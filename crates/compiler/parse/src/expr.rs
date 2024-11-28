use std::cell::Cell;

use crate::ast::{
    is_expr_suffixed, AccessShortcut, AssignedField, ClosureShortcut, Collection, CommentOrNewline,
    Defs, Expr, ExtractSpaces, Implements, ImportAlias, ImportAsKeyword, ImportExposingKeyword,
    ImportedModuleName, IngestedFileAnnotation, IngestedFileImport, ModuleImport,
    ModuleImportParams, Pattern, Spaceable, Spaced, Spaces, SpacesBefore, TryTarget,
    TypeAnnotation, TypeDef, TypeHeader, ValueDef, WhenShortcut,
};
use crate::blankspace::{eat_nc, eat_nc_check, eat_nc_loc_c, eat_nc_ok, SpacedBuilder};
use crate::header::{chomp_module_name, ModuleName};
use crate::ident::{
    chomp_access_chain, chomp_integer_part, chomp_lowercase_part, malformed_ident,
    parse_anycase_ident, parse_ident_chain, parse_lowercase_ident, Accessor, BadIdent, Ident,
    Suffix,
};
use crate::number_literal::parse_number_base;
use crate::parser::{
    collection_inner, eat_keyword, EClosure, EExpect, EExpr, EIf, EImport, EImportParams,
    EInParens, EList, EPattern, ERecord, EReturn, EType, EWhen, ParseResult, SpaceProblem,
    SyntaxError,
};
use crate::pattern::parse_closure_param;
use crate::state::State;
use crate::string_literal::{self, rest_of_str_like, StrLikeLiteral};
use crate::type_annotation::{
    self, parse_implements_abilities, parse_type_expr, NO_TYPE_EXPR_FLAGS, STOP_AT_FIRST_IMPL,
    TRAILING_COMMA_VALID,
};
use crate::{header, keyword};
use bumpalo::collections::Vec;
use bumpalo::Bump;
use roc_collections::soa::slice_extend_new;
use roc_error_macros::internal_error;
use roc_module::called_via::{BinOp, CalledVia, UnaryOp};
use roc_region::all::{Loc, Position, Region};

use crate::parser::Progress::{self, *};

pub fn test_parse_expr<'a>(
    arena: &'a bumpalo::Bump,
    state: State<'a>,
) -> Result<Loc<Expr<'a>>, SyntaxError<'a>> {
    let (_, spaces_before, state) = eat_nc_check(EExpr::IndentStart, arena, state, 0, false)
        .map_err(|(_, fail)| SyntaxError::Expr(fail, Position::default()))?;

    let (expr, state) = parse_expr_block(CHECK_FOR_ARROW | ACCEPT_MULTI_BACKPASSING, arena, state)
        .map_err(|(_, fail)| SyntaxError::Expr(fail, Position::default()))?;

    if state.has_reached_end() {
        Ok(expr.spaced_before(arena, spaces_before))
    } else {
        let fail = EExpr::BadExprEnd(state.pos());
        Err(SyntaxError::Expr(fail, Position::default()))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExprParseFlags(u8);

pub const NO_EXPR_PARSE_FLAGS: ExprParseFlags = ExprParseFlags(0);

/// Check for and accept multi-backpassing syntax
/// This is usually true, but false within list/record literals
/// because the comma separating backpassing arguments conflicts
/// with the comma separating literal elements
pub const ACCEPT_MULTI_BACKPASSING: ExprParseFlags = ExprParseFlags(1);

/// Check for the `->` token, and raise an error if found
/// This is usually true, but false in if-guards
///
/// > Just foo if foo == 2 -> ...
pub const CHECK_FOR_ARROW: ExprParseFlags = ExprParseFlags(1 << 1);

impl ExprParseFlags {
    pub const fn is_set(&self, flag: Self) -> bool {
        (self.0 & flag.0) != 0
    }

    #[must_use]
    pub const fn unset(&self, flag: Self) -> Self {
        Self(self.0 & !flag.0)
    }
}

impl std::ops::BitOr for ExprParseFlags {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

fn rest_of_expr_in_parens_etc<'a>(
    start: Position,
    arena: &'a Bump,
    state: State<'a>,
) -> ParseResult<'a, Loc<Expr<'a>>, EExpr<'a>> {
    let elem_p = move |a: &'a Bump, state: State<'a>| {
        let pos = state.pos();
        parse_expr_block(CHECK_FOR_ARROW, a, state)
            .map_err(|(p, fail)| (p, EInParens::Expr(a.alloc(fail), pos)))
    };
    let (elems, state) = collection_inner(arena, state, elem_p, Expr::SpaceBefore)
        .map_err(|(_, fail)| (MadeProgress, EExpr::InParens(fail, start)))?;

    if state.bytes().first() != Some(&b')') {
        let fail = EInParens::End(state.pos());
        return Err((MadeProgress, EExpr::InParens(fail, start)));
    }
    let state = state.inc();

    if elems.is_empty() {
        let fail = EInParens::Empty(state.pos());
        return Err((NoProgress, EExpr::InParens(fail, start)));
    }

    let mut loc_elems = if elems.len() > 1 {
        state.loc(start, Expr::Tuple(elems.ptrify_items(arena)))
    } else {
        // TODO: don't discard comments before/after (stored in the Collection)
        Loc::at(
            elems.items[0].region,
            Expr::ParensAround(&elems.items[0].value),
        )
    };

    let (suffixes, state) = parse_field_task_result_suffixes(arena, state)?;

    // if there are field accesses, include the parentheses in the region
    // otherwise, don't include the parentheses
    if !suffixes.is_empty() {
        let elems = apply_access_chain(arena, loc_elems.value, suffixes);
        loc_elems = state.loc(start, elems)
    };

    Ok((loc_elems, state))
}

/// It parses suffixes `.`, `!`, `?` and as it is called after the initial term it always returns MadeProgress for the Err
fn parse_field_task_result_suffixes<'a>(
    arena: &'a Bump,
    mut state: State<'a>,
) -> ParseResult<'a, Vec<'a, Suffix<'a>>, EExpr<'a>> {
    let mut fields = Vec::with_capacity_in(1, arena);
    loop {
        let prev_state = state.clone();
        let (field, next_state) = match state.bytes().first() {
            Some(b) => match b {
                b'.' => {
                    let state = state.inc();
                    let ident_pos = state.pos();
                    match parse_lowercase_ident(state.clone()) {
                        Ok((name, state)) => (Suffix::Accessor(Accessor::RecordField(name)), state),
                        Err(NoProgress) => {
                            // This is a tuple accessor, e.g. "1" in `.1`
                            match chomp_integer_part(state.bytes()) {
                                Ok(name) => (
                                    Suffix::Accessor(Accessor::TupleIndex(name)),
                                    state.leap_len(name),
                                ),
                                Err(_) => return Err((MadeProgress, EExpr::Access(ident_pos))),
                            }
                        }
                        Err(_) => return Err((MadeProgress, EExpr::Access(ident_pos))),
                    }
                }
                b'!' => (Suffix::TrySuffix(TryTarget::Task), state.inc()),
                b'?' => (Suffix::TrySuffix(TryTarget::Result), state.inc()),
                _ => return Ok((fields, prev_state)),
            },
            _ => return Ok((fields, prev_state)),
        };

        fields.push(field);
        state = next_state;
    }
}

fn parse_negative_number<'a>(
    start: Position,
    flags: ExprParseFlags,
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
) -> ParseResult<'a, Loc<Expr<'a>>, EExpr<'a>> {
    // unary minus should not be followed by whitespace or comment
    if !state
        .bytes()
        .get(1)
        .map(|b| b.is_ascii_whitespace() || *b == b'#')
        .unwrap_or(false)
    {
        let prev = state.clone();
        let state = state.inc();
        let loc_op = Region::new(start, state.pos());

        match parse_term(PARSE_DEFAULT, flags, arena, state, min_indent) {
            Ok((expr, state)) => Ok((numeric_negate_expr(arena, &prev, loc_op, expr, &[]), state)),
            Err((_, fail)) => Err((MadeProgress, fail)),
        }
    } else {
        // drop the minus and parse '0b', '0o', '0x', etc.
        match parse_number_base(true, &state.bytes()[1..], state) {
            Ok((literal, state)) => Ok((state.loc(start, literal_to_expr(literal)), state)),
            Err((MadeProgress, fail)) => Err((MadeProgress, EExpr::Number(fail, start))),
            Err(_) => {
                // it may be the case with split arrow `- >` or similar,
                // so it should not considered as bad number, let's keep parsing until we find the closest error.
                Err((NoProgress, EExpr::Start(start)))
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ParseTermOpts(u8);

impl ParseTermOpts {
    pub const fn is_set(&self, opt: Self) -> bool {
        (self.0 & opt.0) != 0
    }
}

impl std::ops::BitOr for ParseTermOpts {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

pub const PARSE_DEFAULT: ParseTermOpts = ParseTermOpts(0);

pub const PARSE_UNDERSCORE: ParseTermOpts = ParseTermOpts(0b1);
pub const PARSE_NEGATIVE: ParseTermOpts = ParseTermOpts(0b10);
pub const PARSE_IF_WHEN: ParseTermOpts = ParseTermOpts(0b100);
pub const PARSE_ALL: ParseTermOpts = ParseTermOpts(0b111);

pub const PARSE_NO_CLOSURE: ParseTermOpts = ParseTermOpts(0b1000);

fn parse_term<'a>(
    opts: ParseTermOpts,
    flags: ExprParseFlags,
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
) -> ParseResult<'a, Loc<Expr<'a>>, EExpr<'a>> {
    let start = state.pos();
    if let Some(b) = state.bytes().first() {
        match b {
            b'\\' => {
                if !opts.is_set(PARSE_NO_CLOSURE) {
                    match rest_of_closure(flags, arena, state.inc()) {
                        Ok((expr, state)) => Ok((state.loc(start, expr), state)),
                        Err((p, fail)) => Err((p, EExpr::Closure(fail, start))),
                    }
                } else {
                    Err((NoProgress, EExpr::Start(start)))
                }
            }
            b'_' => {
                if opts.is_set(PARSE_UNDERSCORE) {
                    let state = state.inc();
                    match chomp_lowercase_part(state.bytes()) {
                        Ok((name, _)) => {
                            let state = state.leap(name.len());
                            Ok((state.loc(start, Expr::Underscore(name)), state))
                        }
                        Err(NoProgress) => Ok((state.loc(start, Expr::Underscore("")), state)),
                        Err(_) => Err((MadeProgress, EExpr::End(start))),
                    }
                } else {
                    Err((NoProgress, EExpr::Start(start)))
                }
            }
            b'-' => {
                if opts.is_set(PARSE_NEGATIVE) {
                    parse_negative_number(start, flags, arena, state, min_indent)
                } else {
                    Err((NoProgress, EExpr::Start(start)))
                }
            }
            b'!' => {
                if opts.is_set(PARSE_NEGATIVE) {
                    rest_of_logical_not(start, flags, arena, state.inc(), min_indent)
                } else {
                    Err((NoProgress, EExpr::Start(start)))
                }
            }
            b'(' => rest_of_expr_in_parens_etc(start, arena, state.inc()),
            b'{' => rest_of_record_expr(start, arena, state.inc()),
            b'[' => rest_of_list_expr(start, arena, state.inc()),
            b'"' | b'\'' => {
                let column = state.column();
                match rest_of_str_like(*b == b'\'', column, arena, state.inc()) {
                    Ok((literal, state)) => {
                        let str_literal = match literal {
                            StrLikeLiteral::Str(s) => Expr::Str(s),
                            StrLikeLiteral::SingleQuote(s) => Expr::SingleQuote(s.to_str_in(arena)),
                        };
                        Ok((state.loc(start, str_literal), state))
                    }
                    Err((p, fail)) => Err((p, EExpr::Str(fail, start))),
                }
            }
            b'0'..=b'9' => match parse_number_base(false, state.bytes(), state) {
                Ok((literal, state)) => Ok((state.loc(start, literal_to_expr(literal)), state)),
                Err((p, fail)) => Err((p, EExpr::Number(fail, start))),
            },
            _ => {
                if opts.is_set(PARSE_IF_WHEN) {
                    let n = eat_keyword(keyword::IF, &state);
                    if n > 0 {
                        return match rest_of_if_expr(flags, arena, state.leap(n), min_indent) {
                            Ok((expr, state)) => Ok((state.loc(start, expr), state)),
                            Err((p, err)) => Err((p, EExpr::If(err, start))),
                        };
                    }

                    let n = eat_keyword(keyword::WHEN, &state);
                    if n > 0 {
                        return match when::rest_of_when_expr(None, flags, arena, state.leap(n), 0) {
                            Ok((expr, state)) => Ok((state.loc(start, expr), state)),
                            Err((p, err)) => Err((p, EExpr::When(err, start))),
                        };
                    }
                }

                let n = eat_keyword(keyword::CRASH, &state);
                if n > 0 {
                    let state = state.leap(n);
                    return Ok((state.loc(start, Expr::Crash), state));
                }

                let n = eat_keyword(keyword::DBG, &state);
                if n > 0 {
                    let state = state.leap(n);
                    return Ok((state.loc(start, Expr::Dbg), state));
                }

                // todo: @later "try" is not included into KEYWORDS in keyword.rs because there still functions with the such name
                let n = eat_keyword("try", &state);
                if n > 0 {
                    let state = state.leap(n);
                    return Ok((state.loc(start, Expr::Try), state));
                }

                let (ident, state) = parse_ident_chain(arena, state)?;

                let ident_end = state.pos();
                let (suffixes, state) = parse_field_task_result_suffixes(arena, state)?;

                let mut ident = ident_to_expr(arena, ident, None);
                if !suffixes.is_empty() {
                    ident = apply_access_chain(arena, ident, suffixes);
                }
                Ok((Loc::pos(start, ident_end, ident), state))
            }
        }
    } else {
        Err((NoProgress, EExpr::Start(start)))
    }
}

/// Entry point for parsing an expression.
pub(crate) fn parse_expr_start<'a>(
    flags: ExprParseFlags,
    start_state_and_term: Option<(State<'a>, Loc<Expr<'a>>)>,
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
) -> ParseResult<'a, Loc<Expr<'a>>, EExpr<'a>> {
    let (start_state, term, state) = match start_state_and_term {
        None => {
            let (term, news) = parse_term(PARSE_ALL, flags, arena, state.clone(), min_indent)?;
            (state, term, news)
        }
        Some((start_state, term)) => (start_state, term, state),
    };

    let start = start_state.pos();
    let inc_indent = start_state.line_indent() + 1;

    // Parse a chain of expressions separated by operators. Also handles function application.
    let mut prev_state = state.clone();
    let (_, spaces_before_op, state) =
        match eat_nc_check(EExpr::IndentEnd, arena, state.clone(), min_indent, false) {
            Ok(ok) => ok,
            Err(_) => return Ok((state.loc(start, term.value), state)),
        };

    let mut expr_state = ExprState {
        operators: Vec::new_in(arena),
        arguments: Vec::new_in(arena),
        expr: term,
        spaces_after: spaces_before_op,
        end: prev_state.pos(),
    };

    let mut state = state;
    loop {
        let term_res = if state.column() >= inc_indent {
            parse_term(PARSE_UNDERSCORE, flags, arena, state.clone(), inc_indent)
        } else {
            Err((NoProgress, EExpr::Start(state.pos())))
        };

        match term_res {
            Ok((mut arg, new_state)) => {
                state = new_state;
                prev_state = state.clone();

                if !expr_state.spaces_after.is_empty() {
                    arg = arg.spaced_before(arena, expr_state.spaces_after);
                    expr_state.spaces_after = &[];
                }
                expr_state.arguments.push(arena.alloc(arg));
                expr_state.end = state.pos();

                match eat_nc_check(EExpr::IndentEnd, arena, state.clone(), min_indent, false) {
                    Ok((_, new_spaces, new_state)) => {
                        expr_state.spaces_after = new_spaces;
                        state = new_state;
                    }
                    Err(_) => {
                        expr_state.spaces_after = &[];
                        let expr = finalize_expr(expr_state, arena);
                        return Ok((state.loc(start, expr), state));
                    }
                }

                continue;
            }
            Err((MadeProgress, f)) => return Err((MadeProgress, f)),
            Err((NoProgress, _)) => {
                let before_op = state.clone();
                // We're part way thru parsing an expression, e.g. `bar foo `.
                // We just tried parsing an argument and determined we couldn't -
                // so we're going to try parsing an operator.
                let op_res = match parse_bin_op(state.clone()) {
                    // roll back space parsing
                    Err((NoProgress, _)) => Ok((finalize_expr(expr_state, arena), prev_state)),
                    Err(err) => Err(err),
                    Ok((op, state)) => {
                        let op_start = before_op.pos();
                        let op_end = state.pos();

                        expr_state.consume_spaces(arena);

                        if let BinOp::When = op {
                            let when_pos = state.pos();
                            let cond = Some((expr_state.expr, WhenShortcut::BinOp));
                            match when::rest_of_when_expr(cond, flags, arena, state, min_indent) {
                                Ok(ok) => Ok(ok),
                                Err((p, fail)) => Err((p, EExpr::When(fail, when_pos))),
                            }
                        } else {
                            let (_, spaces_after_op, state) =
                                eat_nc_check(EExpr::IndentEnd, arena, state, min_indent, false)?;

                            match op {
                                BinOp::Minus
                                    if expr_state.end != op_start && op_end == state.pos() =>
                                {
                                    let op_at = Region::new(op_start, op_end);
                                    parse_negative_term(
                                        start, arena, state, min_indent, inc_indent, expr_state,
                                        flags, before_op, op_at,
                                    )
                                }
                                _ => parse_after_binop(
                                    start,
                                    arena,
                                    state,
                                    min_indent,
                                    inc_indent,
                                    flags,
                                    spaces_after_op,
                                    expr_state,
                                    Loc::pos(op_start, op_end, op),
                                ),
                            }
                        }
                    }
                };
                return op_res.map(|(expr, state)| (state.loc(start, expr), state));
            }
        }
    }
}

#[allow(clippy::type_complexity)]
pub fn parse_repl_defs_and_optional_expr<'a>(
    arena: &'a Bump,
    state: State<'a>,
) -> Result<(Defs<'a>, Option<Loc<Expr<'a>>>), (Progress, EExpr<'a>)> {
    let start = state.pos();
    let (spaces_before, state) = match eat_nc(arena, state.clone(), false) {
        Ok((_, (sp, _), state)) => (state.loc(start, sp), state),
        Err((NoProgress, _)) => return Ok((Defs::default(), None)),
        Err(err) => return Err(err),
    };

    let (stmts, state) = parse_stmt_seq(
        arena,
        state,
        |e, _| e.clone(),
        CHECK_FOR_ARROW | ACCEPT_MULTI_BACKPASSING,
        0,
        spaces_before,
        EExpr::IndentEnd,
    )?;

    let state = match eat_nc(arena, state.clone(), false) {
        Ok((_, _, state)) => state,
        Err((NoProgress, _)) => state,
        Err(err) => return Err(err),
    };

    if !state.has_reached_end() {
        return Err((MadeProgress, EExpr::End(state.pos())));
    }

    let defs =
        stmts_to_defs(&stmts, Defs::default(), false, arena).map_err(|err| (MadeProgress, err))?;
    Ok(defs)
}

fn parse_stmt<'a>(
    flags: ExprParseFlags,
    comment_region: Region,
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
) -> ParseResult<'a, Loc<Stmt<'a>>, EExpr<'a>> {
    let start = state.pos();
    match state.bytes().first() {
        Some(b) => match b {
            b'\\' => match rest_of_closure(flags, arena, state.inc()) {
                Ok((expr, state)) => Ok((state.loc(start, Stmt::Expr(expr)), state)),
                Err((p, fail)) => Err((p, EExpr::Closure(fail, start))),
            },
            b'i' => match eat_keyword(keyword::IF, &state) {
                0 => match eat_keyword(keyword::IMPORT, &state) {
                    0 => parse_stmt_operator_chain(flags, arena, state, min_indent),
                    n => rest_of_import(start, arena, state.leap(n), min_indent),
                },
                n => match rest_of_if_expr(flags, arena, state.leap(n), min_indent) {
                    Ok((expr, state)) => Ok((state.loc(start, Stmt::Expr(expr)), state)),
                    Err((p, fail)) => Err((p, EExpr::If(fail, start))),
                },
            },
            b'e' => match eat_keyword(keyword::EXPECT, &state) {
                0 => parse_stmt_operator_chain(flags, arena, state, min_indent),
                n => rest_of_expect_stmt(start, flags, comment_region, arena, state.leap(n)),
            },
            b'd' => match eat_keyword(keyword::DBG, &state) {
                0 => parse_stmt_operator_chain(flags, arena, state, min_indent),
                n => rest_of_dbg_stmt(start, flags, comment_region, arena, state.leap(n)),
            },
            b'r' => match eat_keyword(keyword::RETURN, &state) {
                0 => parse_stmt_operator_chain(flags, arena, state, min_indent),
                n => rest_of_return_stmt(start, flags, arena, state.leap(n)),
            },
            b'w' => match eat_keyword(keyword::WHEN, &state) {
                0 => parse_stmt_operator_chain(flags, arena, state, min_indent),
                n => match when::rest_of_when_expr(None, flags, arena, state.leap(n), 0) {
                    Ok((expr, state)) => Ok((state.loc(start, Stmt::Expr(expr)), state)),
                    Err((p, err)) => Err((p, EExpr::When(err, start))),
                },
            },
            _ => parse_stmt_operator_chain(flags, arena, state, min_indent),
        },
        None => Err((NoProgress, EExpr::Start(start))),
    }
}

fn parse_stmt_operator_chain<'a>(
    flags: ExprParseFlags,
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
) -> ParseResult<'a, Loc<Stmt<'a>>, EExpr<'a>> {
    let start = state.pos();
    let line_indent = state.line_indent();

    let opts = PARSE_NO_CLOSURE | PARSE_UNDERSCORE | PARSE_NEGATIVE;
    let (expr, state) = parse_term(opts, flags, arena, state, min_indent)?;

    let mut prev_state = state.clone();
    let end = state.pos();

    let (_, spaces_before_op, state) =
        match eat_nc_check(EExpr::IndentEnd, arena, state.clone(), min_indent, false) {
            Ok(ok) => ok,
            Err(_) => {
                return Ok((state.loc(start, Stmt::Expr(expr.value)), state));
            }
        };

    let mut expr_state = ExprState {
        operators: Vec::new_in(arena),
        arguments: Vec::new_in(arena),
        expr,
        spaces_after: spaces_before_op,
        end,
    };

    let inc_indent = line_indent + 1;
    let mut state = state;
    loop {
        let term_res = if state.column() >= inc_indent {
            parse_term(PARSE_UNDERSCORE, flags, arena, state.clone(), inc_indent)
        } else {
            Err((NoProgress, EExpr::Start(state.pos())))
        };

        match term_res {
            Err((MadeProgress, f)) => return Err((MadeProgress, f)),
            Ok((
                implements @ Loc {
                    value:
                        Expr::Var {
                            module_name: "",
                            ident: keyword::IMPLEMENTS,
                            ..
                        },
                    ..
                },
                state,
            )) if matches!(expr_state.expr.value, Expr::Tag(..)) => {
                return match parse_ability_def(expr_state, state, arena, implements, inc_indent) {
                    Ok((td, state)) => Ok((state.loc(start, Stmt::TypeDef(td)), state)),
                    Err((NoProgress, _)) => Err((NoProgress, EExpr::Start(start))),
                    Err(err) => Err(err),
                };
            }
            Err((NoProgress, _)) => {
                // We're part way thru parsing an expression, e.g. `bar foo `.
                // We just tried parsing an argument and determined we couldn't -
                // so we're going to try parsing an operator.
                //
                // This is very similar to the logic in `expr_operator_chain`, except
                // we handle the additional case of backpassing, which is valid
                // at the statement level but not at the expression level.
                let before_op = state.clone();
                let op_res = match parse_op(state.clone()) {
                    Err((MadeProgress, f)) => Err((MadeProgress, f)),
                    Ok((op, state)) => {
                        // adds the spaces before operator to the preceding expression term
                        expr_state.consume_spaces(arena);

                        if let OperatorOrDef::BinOp(BinOp::When) = op {
                            // the `~` when operator is handled here to handle the spaces specific to the when branches
                            // instead of generic space handling in `parse_stmt_operator`
                            let when_pos = state.pos();
                            let cond = Some((expr_state.expr, WhenShortcut::BinOp));
                            match when::rest_of_when_expr(cond, flags, arena, state, min_indent) {
                                Ok((expr, state)) => Ok((Stmt::Expr(expr), state)),
                                Err((p, fail)) => Err((p, EExpr::When(fail, when_pos))),
                            }
                        } else {
                            let loc_op = state.loc(before_op.pos(), op);
                            parse_stmt_operator(
                                start, arena, state, min_indent, inc_indent, flags, expr_state,
                                loc_op, before_op,
                            )
                        }
                    }
                    Err((NoProgress, _)) => {
                        if flags.is_set(ACCEPT_MULTI_BACKPASSING) && state.bytes().starts_with(b",")
                        {
                            state = state.inc();
                            parse_stmt_multi_backpassing(
                                expr_state, flags, arena, state, min_indent,
                            )
                        } else if flags.is_set(CHECK_FOR_ARROW) && state.bytes().starts_with(b"->")
                        {
                            Err((MadeProgress, EExpr::BadOperator("->", state.pos())))
                        } else {
                            // roll back space parsing
                            let expr = finalize_expr(expr_state, arena);
                            Ok((Stmt::Expr(expr), prev_state))
                        }
                    }
                };
                return match op_res {
                    Ok((stmt, state)) => Ok((state.loc(start, stmt), state)),
                    Err((NoProgress, _)) => Err((NoProgress, EExpr::Start(start))),
                    Err(err) => Err(err),
                };
            }
            Ok((mut arg, new_state)) => {
                state = new_state;
                prev_state = state.clone();

                if !expr_state.spaces_after.is_empty() {
                    arg = arg.spaced_before(arena, expr_state.spaces_after);
                    expr_state.spaces_after = &[];
                }
                expr_state.arguments.push(arena.alloc(arg));
                expr_state.end = state.pos();

                match eat_nc_check(EExpr::IndentEnd, arena, state.clone(), min_indent, false) {
                    Ok((_, new_spaces, new_state)) => {
                        expr_state.spaces_after = new_spaces;
                        state = new_state;
                    }
                    Err(_) => {
                        expr_state.spaces_after = &[];
                        let expr = finalize_expr(expr_state, arena);
                        return Ok((state.loc(start, Stmt::Expr(expr)), state));
                    }
                }

                continue;
            }
        }
    }
}

#[derive(Debug)]
struct ExprState<'a> {
    operators: Vec<'a, (Loc<Expr<'a>>, Loc<BinOp>)>,
    arguments: Vec<'a, &'a Loc<Expr<'a>>>,
    expr: Loc<Expr<'a>>,
    spaces_after: &'a [CommentOrNewline<'a>],
    end: Position,
}

impl<'a> ExprState<'a> {
    fn consume_spaces(&mut self, arena: &'a Bump) {
        if !self.spaces_after.is_empty() {
            if let Some(last) = self.arguments.pop() {
                let new = last.value.with_spaces_after(self.spaces_after, last.region);

                self.arguments.push(arena.alloc(new));
            } else {
                let region = self.expr.region;

                let mut value = Expr::Num("");
                std::mem::swap(&mut self.expr.value, &mut value);

                self.expr = arena
                    .alloc(value)
                    .with_spaces_after(self.spaces_after, region);
            };

            self.spaces_after = &[];
        }
    }

    fn validate_assignment_or_backpassing<F>(
        mut self,
        arena: &'a Bump,
        loc_op: Loc<OperatorOrDef>,
        argument_error: F,
    ) -> Result<Loc<Expr<'a>>, EExpr<'a>>
    where
        F: Fn(Region, Position) -> EExpr<'a>,
    {
        if !self.operators.is_empty() {
            // this `=` or `<-` likely occurred inline; treat it as an invalid operator
            let opchar = match loc_op.value {
                OperatorOrDef::Assignment => "=",
                OperatorOrDef::Backpassing => "<-",
                _ => unreachable!(),
            };

            let fail = EExpr::BadOperator(opchar, loc_op.region.start());

            Err(fail)
        } else if !matches!(self.expr.value, Expr::Tag(_) | Expr::OpaqueRef(_))
            && !self.arguments.is_empty()
            && !is_expr_suffixed(&self.expr.value)
        {
            let region = Region::across_all(self.arguments.iter().map(|v| &v.region));
            Err(argument_error(region, loc_op.region.start()))
        } else {
            self.consume_spaces(arena);
            if !self.arguments.is_empty() {
                Ok(to_call(arena, self.arguments, self.expr))
            } else {
                Ok(self.expr)
            }
        }
    }

    fn validate_is_type_def(
        mut self,
        arena: &'a Bump,
        kind: Loc<AliasOrOpaque>,
    ) -> Result<(Loc<Expr<'a>>, Vec<'a, &'a Loc<Expr<'a>>>), EExpr<'a>> {
        if !self.operators.is_empty() {
            // this `:`/`:=` likely occurred inline; treat it as an invalid operator
            let op = match kind.value {
                AliasOrOpaque::Alias => ":",
                AliasOrOpaque::Opaque => ":=",
            };
            let fail = EExpr::BadOperator(op, kind.region.start());

            Err(fail)
        } else {
            self.consume_spaces(arena);
            Ok((self.expr, self.arguments))
        }
    }
}

fn finalize_expr<'a>(expr_state: ExprState<'a>, arena: &'a Bump) -> Expr<'a> {
    let right_arg = if !expr_state.arguments.is_empty() {
        to_call(arena, expr_state.arguments, expr_state.expr)
    } else {
        expr_state.expr
    };
    if expr_state.operators.is_empty() {
        right_arg.value
    } else {
        Expr::BinOps(
            expr_state.operators.into_bump_slice(),
            arena.alloc(right_arg),
        )
    }
}

fn to_call<'a>(
    arena: &'a Bump,
    mut args: Vec<'a, &'a Loc<Expr<'a>>>,
    loc_expr: Loc<Expr<'a>>,
) -> Loc<Expr<'a>> {
    debug_assert!(!args.is_empty());
    let last = args.last().map(|x| x.region).unwrap_or_default();
    let region = Region::span_across(&loc_expr.region, &last);

    let spaces = if let Some(last) = args.last_mut() {
        let spaces = last.value.extract_spaces();
        if spaces.after.is_empty() {
            &[]
        } else {
            let inner = spaces.item.spaced_before(arena, spaces.before);
            *last = arena.alloc(Loc::at(last.region, inner));
            spaces.after
        }
    } else {
        &[]
    };

    let mut apply = Expr::Apply(
        arena.alloc(loc_expr),
        args.into_bump_slice(),
        CalledVia::Space,
    );

    apply = apply.spaced_after(arena, spaces);
    Loc::at(region, apply)
}

fn numeric_negate_expr<'a>(
    arena: &'a Bump,
    state: &State<'a>,
    loc_op: Region,
    expr: Loc<Expr<'a>>,
    spaces: &'a [CommentOrNewline<'a>],
) -> Loc<Expr<'a>> {
    debug_assert_eq!(state.bytes().first(), Some(&b'-'));
    // for overflow reasons, we must make the unary minus part of the number literal.
    let start = state.pos();
    let region = Region::new(start, expr.region.end());

    let new_expr = match expr.value {
        Expr::Num(string) => {
            let s = unsafe { std::str::from_utf8_unchecked(&state.bytes()[..string.len() + 1]) };
            Expr::Num(s)
        }
        Expr::Float(string) => {
            let s = unsafe { std::str::from_utf8_unchecked(&state.bytes()[..string.len() + 1]) };
            Expr::Float(s)
        }
        Expr::NonBase10Int {
            string,
            base,
            is_negative,
        } => {
            // don't include the minus sign here; it will not be parsed right
            Expr::NonBase10Int {
                is_negative: !is_negative,
                string,
                base,
            }
        }
        _ => Expr::UnaryOp(arena.alloc(expr), Loc::at(loc_op, UnaryOp::Negate)),
    };

    Loc::at(region, new_expr).spaced_before(arena, spaces)
}

fn parse_import_params<'a>(
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
) -> ParseResult<'a, ModuleImportParams<'a>, EImportParams<'a>> {
    let (_, before, state) = eat_nc_check(EImportParams::Indent, arena, state, min_indent, false)
        .map_err(|(_, fail)| (NoProgress, fail))?;

    let record_pos = state.pos();
    if state.bytes().first() != Some(&b'{') {
        let fail = EImportParams::Record(ERecord::Open(record_pos), record_pos);
        return Err((NoProgress, fail));
    }

    let (record, state) = rest_of_record(arena, state.inc())
        .map_err(|(p, fail)| (p, EImportParams::Record(fail, record_pos)))?;

    let record_at = Region::new(record_pos, state.pos());

    if let Some(prefix) = record.prefix {
        let fail = match prefix {
            (update, RecordHelpPrefix::Update) => EImportParams::RecordUpdateFound(update.region),
            (mapper, RecordHelpPrefix::Mapper) => EImportParams::RecordBuilderFound(mapper.region),
        };
        return Err((MadeProgress, fail));
    }

    let params = record.fields.map_items_result(arena, |loc_field| {
        match loc_field.value.to_assigned_field(arena) {
            AssignedField::IgnoredValue(_, _, _) => Err((
                MadeProgress,
                EImportParams::RecordIgnoredFieldFound(loc_field.region),
            )),
            field => Ok(Loc::at(loc_field.region, field)),
        }
    })?;

    let params = Loc::at(record_at, params);
    Ok((ModuleImportParams { before, params }, state))
}

fn parse_imported_module_name(
    state: State<'_>,
) -> ParseResult<'_, ImportedModuleName<'_>, EImport<'_>> {
    let package_pos = state.pos();
    let (package, state) = match parse_lowercase_ident(state.clone()) {
        Ok((name, state)) => match state.bytes().first() {
            Some(&b'.') => (Some(name), state.inc()),
            _ => return Err((MadeProgress, EImport::PackageShorthandDot(package_pos))),
        },
        Err(NoProgress) => (None, state),
        Err(_) => return Err((MadeProgress, EImport::PackageShorthand(package_pos))),
    };

    let name_pos = state.pos();
    let (name, state) = match chomp_module_name(state.bytes()) {
        Ok(name) => (ModuleName::new(name), state.leap_len(name)),
        Err(p) => return Err((p, EImport::ModuleName(name_pos))),
    };

    Ok((ImportedModuleName { package, name }, state))
}

fn import_as<'a>(
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
) -> ParseResult<'a, header::KeywordItem<'a, ImportAsKeyword, Loc<ImportAlias<'a>>>, EImport<'a>> {
    let (keyword, state) = header::spaces_around_keyword(
        arena,
        state,
        min_indent,
        ImportAsKeyword,
        EImport::As,
        EImport::IndentAs,
        EImport::IndentAlias,
    )?;

    let ident_pos = state.pos();
    let (item, state) = match parse_anycase_ident(state) {
        Ok((ident, state)) => {
            let ident_at = Region::new(ident_pos, state.pos());
            match ident.chars().next() {
                Some(first) if first.is_uppercase() => {
                    let ident = Loc::at(ident_at, ImportAlias::new(ident));
                    (ident, state)
                }
                Some(_) => return Err((MadeProgress, EImport::LowercaseAlias(ident_at))),
                None => return Err((MadeProgress, EImport::Alias(state.pos()))),
            }
        }
        Err(p) => return Err((p, EImport::Alias(ident_pos))),
    };

    Ok((header::KeywordItem { keyword, item }, state))
}

#[allow(clippy::type_complexity)]
fn import_exposing<'a>(
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
) -> ParseResult<
    'a,
    header::KeywordItem<
        'a,
        ImportExposingKeyword,
        Collection<'a, Loc<Spaced<'a, header::ExposedName<'a>>>>,
    >,
    EImport<'a>,
> {
    let (keyword, state) = header::spaces_around_keyword(
        arena,
        state,
        min_indent,
        ImportExposingKeyword,
        EImport::Exposing,
        EImport::IndentExposing,
        EImport::ExposingListStart,
    )?;

    if state.bytes().first() != Some(&b'[') {
        return Err((NoProgress, EImport::ExposingListStart(state.pos())));
    }
    let state = state.inc();

    let elem_p = move |_: &'a Bump, state: State<'a>| {
        let pos = state.pos();
        match parse_anycase_ident(state) {
            Ok((ident, state)) => {
                let ident = Spaced::Item(crate::header::ExposedName::new(ident));
                Ok((state.loc(pos, ident), state))
            }
            Err(p) => Err((p, EImport::ExposedName(pos))),
        }
    };
    let (item, state) = collection_inner(arena, state, elem_p, Spaced::SpaceBefore)?;

    if state.bytes().first() != Some(&b']') {
        return Err((MadeProgress, EImport::ExposingListEnd(state.pos())));
    }
    let state = state.inc();

    Ok((header::KeywordItem { keyword, item }, state))
}

fn import_ingested_file_as<'a>(
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
) -> ParseResult<'a, header::KeywordItem<'a, ImportAsKeyword, Loc<&'a str>>, EImport<'a>> {
    let (keyword, state) = header::spaces_around_keyword(
        arena,
        state,
        min_indent,
        ImportAsKeyword,
        EImport::As,
        EImport::IndentAs,
        EImport::IndentIngestedName,
    )?;

    let item_pos = state.pos();
    let (item, state) = parse_lowercase_ident(state)
        .map_err(|_| (MadeProgress, EImport::IngestedName(item_pos)))?;

    let item = state.loc(item_pos, item);

    let keyword_item = header::KeywordItem { keyword, item };
    Ok((keyword_item, state))
}

fn parse_import_ingested_file_ann<'a>(
    arena: &'a bumpalo::Bump,
    state: State<'a>,
    min_indent: u32,
) -> ParseResult<'a, IngestedFileAnnotation<'a>, EImport<'a>> {
    let (_, before_colon, state) =
        match eat_nc_check(EImport::IndentColon, arena, state, min_indent, false) {
            Ok(ok) => ok,
            Err((_, fail)) => return Err((NoProgress, fail)),
        };

    if state.bytes().first() != Some(&b':') {
        return Err((NoProgress, EImport::Colon(state.pos())));
    }
    let state = state.inc();

    let ann_pos = state.pos();
    let (annotation, state) =
        type_annotation::parse_type_expr(NO_TYPE_EXPR_FLAGS, arena, state, min_indent)
            .map_err(|(p, fail)| (p, EImport::Annotation(fail, ann_pos)))?;

    let ann = IngestedFileAnnotation {
        before_colon,
        annotation,
    };
    Ok((ann, state))
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum AliasOrOpaque {
    Alias,  // ':'
    Opaque, // ':='
}

fn extract_tag_and_spaces<'a>(arena: &'a Bump, expr: Expr<'a>) -> Option<Spaces<'a, &'a str>> {
    let mut expr = expr.extract_spaces();

    loop {
        match &expr.item {
            Expr::ParensAround(inner_expr) => {
                let inner_expr = inner_expr.extract_spaces();
                expr.item = inner_expr.item;
                expr.before = merge_spaces(arena, expr.before, inner_expr.before);
                expr.after = merge_spaces(arena, inner_expr.after, expr.after);
            }
            Expr::Tag(tag) => {
                return Some(Spaces {
                    before: expr.before,
                    item: tag,
                    after: expr.after,
                });
            }
            _ => return None,
        }
    }
}

/// We just saw a ':' or ':=', and we're trying to parse an alias or opaque type definition.
fn parse_stmt_alias_or_opaque<'a>(
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
    expr_state: ExprState<'a>,
    kind: Loc<AliasOrOpaque>,
    spaces_after_operator: &'a [CommentOrNewline<'a>],
) -> ParseResult<'a, Stmt<'a>, EExpr<'a>> {
    let inc_indent = min_indent + 1;

    let expr_region = expr_state.expr.region;
    let (expr, arguments) = expr_state
        .validate_is_type_def(arena, kind)
        .map_err(|fail| (MadeProgress, fail))?;

    let (res, state) = if let Some(tag) = extract_tag_and_spaces(arena, expr.value) {
        let name = tag.item;
        let mut type_arguments = Vec::with_capacity_in(arguments.len(), arena);

        for argument in arguments {
            match expr_to_pattern(arena, &argument.value) {
                Ok(good) => {
                    type_arguments.push(Loc::at(argument.region, good));
                }
                Err(()) => {
                    let pos = state.pos();
                    let fail = EExpr::Pattern(arena.alloc(EPattern::NotAPattern(pos)), pos);
                    return Err((MadeProgress, fail));
                }
            }
        }

        match kind.value {
            AliasOrOpaque::Alias => {
                // TODO @check later that here we skip `spaces_after_operator`
                let ann_pos = state.pos();
                let (ann, state) = parse_type_expr(NO_TYPE_EXPR_FLAGS, arena, state, inc_indent)
                    .map_err(|(p, fail)| (p, EExpr::Type(fail, ann_pos)))?;

                let header = TypeHeader {
                    name: Loc::at(expr.region, name),
                    vars: type_arguments.into_bump_slice(),
                };

                let def = TypeDef::Alias { header, ann };
                (Stmt::TypeDef(def), state)
            }

            AliasOrOpaque::Opaque => {
                // TODO @check later that here we skip `spaces_after_operator`
                let ann_pos = state.pos();
                let (ann, state) = parse_type_expr(
                    TRAILING_COMMA_VALID | STOP_AT_FIRST_IMPL,
                    arena,
                    state,
                    inc_indent,
                )
                .map_err(|(p, fail)| (p, EExpr::Type(fail, ann_pos)))?;

                let prev = state.clone();
                let (derived, state) =
                    match eat_nc_check(EType::TIndentStart, arena, state, inc_indent, false) {
                        Err(_) => (None, prev),
                        Ok((_, sp, state)) => {
                            match parse_implements_abilities(arena, state, inc_indent) {
                                Err(_) => (None, prev),
                                Ok((abilities, state)) => {
                                    (Some(abilities.spaced_before(arena, sp)), state)
                                }
                            }
                        }
                    };

                let header = TypeHeader {
                    name: Loc::at(expr.region, name),
                    vars: type_arguments.into_bump_slice(),
                };

                let def = TypeDef::Opaque {
                    header,
                    typ: ann,
                    derived,
                };
                (Stmt::TypeDef(def), state)
            }
        }
    } else {
        let call = if !arguments.is_empty() {
            to_call(arena, arguments, expr)
        } else {
            expr
        };

        match expr_to_pattern(arena, &call.value) {
            Ok(pat) => {
                let ann_pos = state.pos();
                let (type_ann, state) =
                    parse_type_expr(NO_TYPE_EXPR_FLAGS, arena, state, inc_indent)
                        .map_err(|(_, fail)| (MadeProgress, EExpr::Type(fail, ann_pos)))?;

                // put the spaces from after the operator in front of the call
                let type_ann = type_ann.spaced_before(arena, spaces_after_operator);
                let value_def = ValueDef::Annotation(Loc::at(expr_region, pat), type_ann);
                (Stmt::ValueDef(value_def), state)
            }
            Err(_) => {
                // this `:`/`:=` likely occurred inline; treat it as an invalid operator
                let op = match kind.value {
                    AliasOrOpaque::Alias => ":",
                    AliasOrOpaque::Opaque => ":=",
                };
                let fail = EExpr::BadOperator(op, kind.region.start());
                return Err((MadeProgress, fail));
            }
        }
    };

    Ok((res, state))
}

mod ability {
    use super::*;
    use crate::{
        ast::{AbilityMember, Spaced},
        parser::EAbility,
    };

    pub enum IndentLevel {
        PendingMin,
        Exact,
    }

    /// Parses an ability demand like `hash : a -> U64 where a implements Hash`, in the context of a larger
    /// ability definition.
    /// This is basically the same as parsing a free-floating annotation, but with stricter rules.
    pub fn parse_demand<'a>(
        indent_type: IndentLevel,
        indent: u32,
        arena: &'a Bump,
        state: State<'a>,
    ) -> ParseResult<'a, (u32, AbilityMember<'a>), EAbility<'a>> {
        // Put no restrictions on the indent after the spaces; we'll check it manually.
        let (spaces_before, state) = match eat_nc(arena, state, false) {
            Ok((_, (sp, _), state)) => (sp, state),
            Err((_, fail)) => return Err((NoProgress, fail)),
        };

        match indent_type {
            IndentLevel::PendingMin if state.column() < indent => {
                let indent_delta = state.column() as i32 - indent as i32;
                let fail = EAbility::DemandAlignment(indent_delta, state.pos());
                Err((MadeProgress, fail))
            }
            IndentLevel::Exact if state.column() < indent => {
                // This demand is not indented correctly
                let indent_delta = state.column() as i32 - indent as i32;
                // Rollback because the deindent may be because there is a next
                // expression
                let fail = EAbility::DemandAlignment(indent_delta, state.pos());
                Err((NoProgress, fail))
            }
            IndentLevel::Exact if state.column() > indent => {
                // This demand is not indented correctly
                let indent_delta = state.column() as i32 - indent as i32;

                // We might be trying to parse at EOF, at which case the indent level
                // will be off, but there is actually nothing left.
                let fail = EAbility::DemandAlignment(indent_delta, state.pos());
                Err((Progress::when(!state.has_reached_end()), fail))
            }
            _ => {
                let indent_column = state.column();

                let start = state.pos();
                let (name, state) = parse_lowercase_ident(state)
                    .map_err(|_| (MadeProgress, EAbility::DemandName(start)))?;

                let name = state.loc(start, Spaced::Item(name));
                let name = name.spaced_before(arena, spaces_before);

                let inc_indent = indent_column + 1;

                // TODO: do we get anything from picking up spaces here?
                let (_, _, state) =
                    eat_nc_check(EAbility::DemandName, arena, state, inc_indent, true)?;

                if state.bytes().first() != Some(&b':') {
                    return Err((MadeProgress, EAbility::DemandColon(state.pos())));
                }
                let state = state.inc();

                let type_pos = state.pos();
                let (typ, state) = parse_type_expr(TRAILING_COMMA_VALID, arena, state, inc_indent)
                    .map_err(|(p, fail)| (p, EAbility::Type(fail, type_pos)))?;

                let demand = AbilityMember { name, typ };
                Ok(((indent_column, demand), state))
            }
        }
    }
}

/// Parse the series of "demands" (e.g. similar to methods in a rust trait), for an ability definition.
fn finish_parsing_ability_def<'a>(
    inc_indent: u32,
    name: Loc<&'a str>,
    args: &'a [Loc<Pattern<'a>>],
    loc_implements: Loc<Implements<'a>>,
    arena: &'a Bump,
    state: State<'a>,
) -> ParseResult<'a, TypeDef<'a>, EExpr<'a>> {
    let mut demands = Vec::with_capacity_in(2, arena);

    // Parse the first demand. This will determine the indentation level all the
    // other demands must observe.
    let start = state.pos();
    let ((demand_indent_level, first_demand), mut state) =
        ability::parse_demand(ability::IndentLevel::PendingMin, inc_indent, arena, state)
            .map_err(|(p, fail)| (p, EExpr::Ability(fail, start)))?;
    demands.push(first_demand);

    loop {
        match ability::parse_demand(
            ability::IndentLevel::Exact,
            demand_indent_level,
            arena,
            state.clone(),
        ) {
            Ok(((_indent, demand), next_state)) => {
                state = next_state;
                demands.push(demand);
            }
            Err((MadeProgress, problem)) => {
                return Err((MadeProgress, EExpr::Ability(problem, state.pos())));
            }
            Err((NoProgress, _)) => {
                break;
            }
        }
    }

    let type_def = TypeDef::Ability {
        header: TypeHeader { name, vars: args },
        loc_implements,
        members: demands.into_bump_slice(),
    };

    Ok((type_def, state))
}

/// A Stmt is an intermediate representation used only during parsing.
/// It consists of a fragment of code that hasn't been fully stitched together yet.
/// For example, each of the following lines is a Stmt:
/// - `foo bar` (Expr)
/// - `foo, bar <- baz` (Backpassing)
/// - `Foo : [A, B, C]` (TypeDef)
/// - `foo = \x -> x + 1` (ValueDef)
///
/// Note in particular that the Backpassing Stmt doesn't make any sense on its own;
/// we need to link it up with the following stmts to make a complete expression.
#[derive(Debug, Clone, Copy)]
pub enum Stmt<'a> {
    Expr(Expr<'a>),
    Backpassing(&'a [Loc<Pattern<'a>>], &'a Loc<Expr<'a>>),
    TypeDef(TypeDef<'a>),
    ValueDef(ValueDef<'a>),
}

/// Having just parsed an operator, we need to dispatch to the appropriate
/// parsing function based on the operator.
///
/// Note, this function is very similar to `parse_expr_operator`, but it
/// handles additional cases to allow assignments / type annotations / etc.
#[allow(clippy::too_many_arguments)]
fn parse_stmt_operator<'a>(
    start: Position,
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
    inc_indent: u32,
    flags: ExprParseFlags,
    expr_state: ExprState<'a>,
    loc_op: Loc<OperatorOrDef>,
    initial: State<'a>,
) -> ParseResult<'a, Stmt<'a>, EExpr<'a>> {
    let (spaces_after_op, state) = eat_nc_loc_c(EExpr::IndentEnd, arena, state, min_indent, false)?;

    let op = loc_op.value;
    let op_start = loc_op.region.start();
    let op_end = loc_op.region.end();
    let new_start = state.pos();

    match op {
        OperatorOrDef::BinOp(BinOp::When) => unreachable!("the case handled by the caller"),
        OperatorOrDef::BinOp(BinOp::Minus) if expr_state.end != op_start && op_end == new_start => {
            parse_negative_term(
                start,
                arena,
                state,
                min_indent,
                inc_indent,
                expr_state,
                flags,
                initial,
                loc_op.region,
            )
            .map(|(expr, state)| (Stmt::Expr(expr), state))
        }
        OperatorOrDef::BinOp(op) => parse_after_binop(
            start,
            arena,
            state,
            min_indent,
            inc_indent,
            flags,
            spaces_after_op.value,
            expr_state,
            loc_op.with_value(op),
        )
        .map(|(expr, state)| (Stmt::Expr(expr), state)),
        OperatorOrDef::Assignment => {
            // We just saw the '=' operator of an assignment stmt. Continue parsing from there.
            let call = expr_state
                .validate_assignment_or_backpassing(arena, loc_op, EExpr::ElmStyleFunction)
                .map_err(|fail| (MadeProgress, fail))?;
            let loc = call.region;

            let (value_def, state) = {
                match expr_to_pattern(arena, &call.value) {
                    Ok(pattern) => {
                        let (body, state) = parse_block(
                            flags,
                            arena,
                            state,
                            inc_indent,
                            EExpr::IndentEnd,
                            |a, _| a.clone(),
                            Some(spaces_after_op),
                        )?;

                        let alias =
                            ValueDef::Body(arena.alloc(Loc::at(loc, pattern)), arena.alloc(body));
                        (alias, state)
                    }
                    Err(_) => {
                        // this `=` likely occurred inline; treat it as an invalid operator
                        let fail = EExpr::BadOperator(arena.alloc("="), op_start);
                        return Err((MadeProgress, fail));
                    }
                }
            };

            Ok((Stmt::ValueDef(value_def), state))
        }
        OperatorOrDef::Backpassing => {
            // Parse the rest of a backpassing statement, after the <- operator
            let expr_region = expr_state.expr.region;
            let call = expr_state
                .validate_assignment_or_backpassing(arena, loc_op, |_, pos| {
                    EExpr::BadOperator("<-", pos)
                })
                .map_err(|fail| (MadeProgress, fail))?;

            let (loc_pattern, loc_body, state) = {
                match expr_to_pattern(arena, &call.value) {
                    Ok(pat) => {
                        let (type_ann, state) =
                            parse_expr_start(flags, None, arena, state, inc_indent)?;

                        // put the spaces from after the operator in front of the call
                        let type_ann = type_ann.spaced_before(arena, spaces_after_op.value);
                        (Loc::at(expr_region, pat), type_ann, state)
                    }
                    Err(_) => {
                        // this `=` likely occurred inline; treat it as an invalid operator
                        let fail = EExpr::BadOperator("=", op_start);
                        return Err((MadeProgress, fail));
                    }
                }
            };

            let stmt = Stmt::Backpassing(arena.alloc([loc_pattern]), arena.alloc(loc_body));
            Ok((stmt, state))
        }
        OperatorOrDef::AliasOrOpaque(kind) => parse_stmt_alias_or_opaque(
            arena,
            state,
            inc_indent,
            expr_state,
            loc_op.with_value(kind),
            spaces_after_op.value,
        ),
    }
}

/// Continue parsing terms after we just parsed a binary operator
#[allow(clippy::too_many_arguments)]
fn parse_after_binop<'a>(
    start: Position,
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
    inc_indent: u32,
    flags: ExprParseFlags,
    spaces_after_op: &'a [CommentOrNewline],
    mut expr_state: ExprState<'a>,
    loc_op: Loc<BinOp>,
) -> ParseResult<'a, Expr<'a>, EExpr<'a>> {
    let (right_expr, state) = match parse_term(PARSE_ALL, flags, arena, state.clone(), min_indent) {
        Ok(ok) => ok,
        Err((NoProgress, _)) => return Err((MadeProgress, EExpr::TrailingOperator(state.pos()))),
        Err(err) => return Err(err),
    };

    // put the spaces from after the operator in front of the new_expr
    let right_expr = right_expr.spaced_before(arena, spaces_after_op);

    let call_or_left = if !expr_state.arguments.is_empty() {
        let args = std::mem::replace(&mut expr_state.arguments, Vec::new_in(arena));
        to_call(arena, args, expr_state.expr)
    } else {
        expr_state.expr
    };
    expr_state.operators.push((call_or_left, loc_op));
    expr_state.expr = right_expr;
    expr_state.end = state.pos();

    let prev = state.clone();
    match eat_nc_check(EExpr::IndentEnd, arena, state, min_indent, false) {
        Ok((_, spaces_after, state)) => {
            expr_state.spaces_after = spaces_after;
            parse_expr_end(
                start, arena, state, min_indent, inc_indent, flags, expr_state, prev,
            )
        }
        Err(_) => {
            expr_state.spaces_after = &[];
            Ok((finalize_expr(expr_state, arena), prev))
        }
    }
}

/// We just saw a `,` that we think is part of a backpassing statement.
/// Parse the rest of the statement.
fn parse_stmt_multi_backpassing<'a>(
    mut expr_state: ExprState<'a>,
    flags: ExprParseFlags,
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
) -> ParseResult<'a, Stmt<'a>, EExpr<'a>> {
    // called after parsing the first , in `a, b <- c` (e.g.)

    let parser = move |arena: &'a Bump, state: State<'a>, min_indent: u32| {
        let (s_pr, sp_before, state) =
            eat_nc_check(EPattern::Start, arena, state, min_indent, false)?;

        let (pat, state) = match crate::pattern::parse_pattern(arena, state, min_indent) {
            Ok(ok) => ok,
            Err((p, fail)) => return Err((p.or(s_pr), fail)),
        };

        let (_, sp_after, state) =
            eat_nc_check(EPattern::IndentEnd, arena, state, min_indent, true)?;

        let pat = pat.spaced_around(arena, sp_before, sp_after);
        Ok((pat, state))
    };

    let start = state.pos();
    let original_state = state.clone();
    let start_bytes_len = state.bytes().len();

    let (mut patterns, state) = match parser(arena, state, min_indent) {
        Ok((first_pat, next_state)) => {
            let mut state = next_state;
            let mut pats = Vec::with_capacity_in(1, arena);
            pats.push(first_pat);

            let result = loop {
                if state.bytes().first() != Some(&b',') {
                    break (pats, state);
                }
                let next_state = state.inc();

                // If the delimiter passed, check the element parser.
                match parser(arena, next_state.clone(), min_indent) {
                    Ok((next_pat, next_state)) => {
                        state = next_state;
                        pats.push(next_pat);
                    }
                    Err((_, fail)) => {
                        // If the delimiter parsed, but the following
                        // element did not, that's a fatal error.
                        let err_pr = Progress::when(start_bytes_len > next_state.bytes().len());
                        let fail = if let EPattern::IndentEnd(_) = fail {
                            EExpr::UnexpectedComma(start.prev())
                        } else {
                            EExpr::Pattern(arena.alloc(fail), start)
                        };
                        return Err((err_pr, fail));
                    }
                }
            };
            result
        }
        Err((NoProgress, _)) => (Vec::new_in(arena), original_state),
        Err((p, fail)) => {
            let fail = if let EPattern::IndentEnd(_) = fail {
                EExpr::UnexpectedComma(start.prev())
            } else {
                EExpr::Pattern(arena.alloc(fail), start)
            };
            return Err((p, fail));
        }
    };

    expr_state.consume_spaces(arena);

    let call = if !expr_state.arguments.is_empty() {
        to_call(arena, expr_state.arguments, expr_state.expr)
    } else {
        expr_state.expr
    };

    let pos = state.pos();
    let pattern = expr_to_pattern(arena, &call.value).map_err(|()| {
        (
            MadeProgress,
            EExpr::Pattern(arena.alloc(EPattern::NotAPattern(pos)), pos),
        )
    })?;

    let loc_pattern = Loc::at(call.region, pattern);

    patterns.insert(0, loc_pattern);

    let line_indent = state.line_indent();

    if !state.bytes().starts_with(b"<-") {
        return Err((MadeProgress, EExpr::BackpassArrow(state.pos())));
    }
    let state = state.leap(2);

    let min_indent = line_indent + 1;
    let (sp_pr, spaces_before, state) =
        eat_nc_check(EExpr::IndentEnd, arena, state, min_indent, false)?;

    let (loc_body, state) = match parse_expr_start(flags, None, arena, state, min_indent) {
        Ok(ok) => ok,
        Err((pe, fail)) => return Err((sp_pr.or(pe), fail)),
    };

    let loc_body = loc_body.spaced_before(arena, spaces_before);
    let ret = Stmt::Backpassing(patterns.into_bump_slice(), arena.alloc(loc_body));
    Ok((ret, state))
}

/// We just saw a unary negation operator, and now we need to parse the expression.
/// A `-` is unary if it is preceded by a space and not followed by a space
#[allow(clippy::too_many_arguments)]
fn parse_negative_term<'a>(
    start: Position,
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
    inc_indent: u32,
    mut expr_state: ExprState<'a>,
    flags: ExprParseFlags,
    initial: State<'a>,
    op_at: Region,
) -> ParseResult<'a, Expr<'a>, EExpr<'a>> {
    let (negated_expr, state) = parse_term(PARSE_DEFAULT, flags, arena, state, min_indent)?;

    let spaces = expr_state.spaces_after;
    let arg = numeric_negate_expr(arena, &initial, op_at, negated_expr, spaces);
    expr_state.arguments.push(arena.alloc(arg));
    expr_state.end = state.pos();

    let initial = state.clone();
    let (spaces, state) = eat_nc_ok(EExpr::IndentEnd, arena, state, min_indent);
    expr_state.spaces_after = spaces;

    // TODO: this should probably be handled in the caller, not here
    parse_expr_end(
        start, arena, state, min_indent, inc_indent, flags, expr_state, initial,
    )
}

/// Parse an expression, not allowing `if`/`when`/etc.
/// TODO: this should probably be subsumed into `expr_operator_chain`
#[allow(clippy::too_many_arguments)]
fn parse_expr_end<'a>(
    start: Position,
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
    inc_indent: u32,
    flags: ExprParseFlags,
    mut expr_state: ExprState<'a>,
    initial: State<'a>,
) -> ParseResult<'a, Expr<'a>, EExpr<'a>> {
    let term_res = if state.column() >= inc_indent {
        parse_term(PARSE_UNDERSCORE, flags, arena, state.clone(), inc_indent)
    } else {
        Err((NoProgress, EExpr::Start(state.pos())))
    };

    match term_res {
        Err((MadeProgress, f)) => Err((MadeProgress, f)),
        Ok((mut arg, state)) => {
            // now that we have `function arg1 ... <spaces> argn`, attach the spaces to the `argn`
            if !expr_state.spaces_after.is_empty() {
                arg = arg.spaced_before(arena, expr_state.spaces_after);
                expr_state.spaces_after = &[];
            }
            expr_state.arguments.push(arena.alloc(arg));
            expr_state.end = state.pos();

            let initial_state = state.clone();
            match eat_nc_check(EExpr::IndentEnd, arena, state.clone(), min_indent, false) {
                Err(_) => {
                    expr_state.spaces_after = &[];
                    let expr = finalize_expr(expr_state, arena);
                    Ok((expr, state))
                }
                Ok((_, spaces_after, state)) => {
                    expr_state.spaces_after = spaces_after;
                    parse_expr_end(
                        start,
                        arena,
                        state,
                        min_indent,
                        inc_indent,
                        flags,
                        expr_state,
                        initial_state,
                    )
                }
            }
        }
        Err((NoProgress, _)) => {
            // We're part way thru parsing an expression, e.g. `bar foo `.
            // We just tried parsing an argument and determined we couldn't -
            // so we're going to try parsing an operator.
            let before_op = state.clone();
            match parse_bin_op(state) {
                Err((MadeProgress, f)) => Err((MadeProgress, f)),
                Ok((op, state)) => {
                    let op_start = before_op.pos();
                    let op_end = state.pos();

                    expr_state.consume_spaces(arena);

                    if let BinOp::When = op {
                        // the chain of operators finishes at the when statement,
                        // so their value will be the condition/value for the when pattern matching
                        let ops_val = finalize_expr(expr_state, arena);
                        let ops_val = state.loc(start, ops_val);

                        let when_pos = state.pos();
                        let cond = Some((ops_val, WhenShortcut::BinOp));
                        match when::rest_of_when_expr(cond, flags, arena, state, min_indent) {
                            Ok(ok) => Ok(ok),
                            Err((p, fail)) => Err((p, EExpr::When(fail, when_pos))),
                        }
                    } else {
                        let (_, spaces_after_op, state) =
                            eat_nc_check(EExpr::IndentEnd, arena, state, min_indent, false)?;

                        match op {
                            BinOp::Minus if expr_state.end != op_start && op_end == state.pos() => {
                                let op_at = Region::new(op_start, op_end);
                                parse_negative_term(
                                    start, arena, state, min_indent, inc_indent, expr_state, flags,
                                    before_op, op_at,
                                )
                            }
                            _ => parse_after_binop(
                                start,
                                arena,
                                state,
                                min_indent,
                                inc_indent,
                                flags,
                                spaces_after_op,
                                expr_state,
                                Loc::pos(op_start, op_end, op),
                            ),
                        }
                    }
                }
                // roll back space parsing
                Err((NoProgress, _)) => Ok((finalize_expr(expr_state, arena), initial)),
            }
        }
    }
}

/// This is an ability definition, `Ability arg1 ... implements ...`.
fn parse_ability_def<'a>(
    expr_state: ExprState<'a>,
    state: State<'a>,
    arena: &'a Bump,
    implements: Loc<Expr<'a>>,
    inc_indent: u32,
) -> ParseResult<'a, TypeDef<'a>, EExpr<'a>> {
    let name = expr_state.expr.map_owned(|e| match e {
        Expr::Tag(name) => name,
        _ => unreachable!(),
    });

    let mut args = Vec::with_capacity_in(expr_state.arguments.len(), arena);
    for arg in expr_state.arguments {
        match expr_to_pattern(arena, &arg.value) {
            Ok(pat) => {
                args.push(Loc::at(arg.region, pat));
            }
            Err(_) => {
                let start = arg.region.start();
                let fail = &*arena.alloc(EPattern::Start(start));
                return Err((MadeProgress, EExpr::Pattern(fail, arg.region.start())));
            }
        }
    }

    // Attach any spaces to the `implements` keyword
    let implements = Loc::at(implements.region, Implements::Implements)
        .spaced_before(arena, expr_state.spaces_after);

    let args = args.into_bump_slice();
    let (type_def, state) =
        finish_parsing_ability_def(inc_indent, name, args, implements, arena, state)?;

    Ok((type_def, state))
}

pub fn parse_expr_block<'a>(
    flags: ExprParseFlags,
    arena: &'a Bump,
    state: State<'a>,
) -> ParseResult<'a, Loc<Expr<'a>>, EExpr<'a>> {
    let start = state.pos();
    let (stmts, state) = parse_stmt_seq(
        arena,
        state,
        |fail, _| fail.clone(),
        flags,
        0,
        Loc::pos(start, start, &[]),
        EExpr::IndentStart,
    )?;

    if stmts.is_empty() {
        let fail = arena.alloc(EExpr::Start(state.pos())).clone();
        return Err((NoProgress, fail));
    }

    let expr = stmts_to_expr(&stmts, arena).map_err(|e| (MadeProgress, arena.alloc(e).clone()))?;

    let (_, spaces_after, state) = eat_nc_check(EExpr::IndentEnd, arena, state, 0, true)?;
    let expr = expr.spaced_after(arena, spaces_after);

    Ok((expr, state))
}

pub fn merge_spaces<'a>(
    arena: &'a Bump,
    a: &'a [CommentOrNewline<'a>],
    b: &'a [CommentOrNewline<'a>],
) -> &'a [CommentOrNewline<'a>] {
    if a.is_empty() {
        b
    } else if b.is_empty() {
        a
    } else {
        let mut merged = Vec::with_capacity_in(a.len() + b.len(), arena);
        merged.extend_from_slice(a);
        merged.extend_from_slice(b);
        merged.into_bump_slice()
    }
}

/// If the given Expr would parse the same way as a valid Pattern, convert it.
/// Example: (foo) could be either an Expr::Var("foo") or Pattern::Identifier("foo")
fn expr_to_pattern<'a>(arena: &'a Bump, expr: &Expr<'a>) -> Result<Pattern<'a>, ()> {
    let mut expr = expr.extract_spaces();

    while let Expr::ParensAround(loc_expr) = &expr.item {
        let expr_inner = loc_expr.extract_spaces();

        expr.before = merge_spaces(arena, expr.before, expr_inner.before);
        expr.after = merge_spaces(arena, expr_inner.after, expr.after);
        expr.item = expr_inner.item;
    }

    let mut pat = match expr.item {
        Expr::Var {
            module_name, ident, ..
        } => {
            if module_name.is_empty() {
                Pattern::Identifier { ident }
            } else {
                Pattern::QualifiedIdentifier { module_name, ident }
            }
        }
        Expr::Underscore(opt_name) => Pattern::Underscore(opt_name),
        Expr::Tag(value) => Pattern::Tag(value),
        Expr::OpaqueRef(value) => Pattern::OpaqueRef(value),
        Expr::Apply(loc_val, loc_args, _) => {
            let region = loc_val.region;
            let value = expr_to_pattern(arena, &loc_val.value)?;
            let val_pattern = arena.alloc(Loc { region, value });

            let mut arg_patterns = Vec::with_capacity_in(loc_args.len(), arena);

            for loc_arg in loc_args.iter() {
                let region = loc_arg.region;
                let value = expr_to_pattern(arena, &loc_arg.value)?;
                arg_patterns.push(Loc { region, value });
            }

            Pattern::Apply(val_pattern, arg_patterns.into_bump_slice())
        }

        Expr::Try => Pattern::Identifier { ident: "try" },

        Expr::SpaceBefore(..) | Expr::SpaceAfter(..) | Expr::ParensAround(..) => unreachable!(),

        Expr::Record(fields) => {
            let patterns = fields.map_items_result(arena, |loc_assigned_field| {
                let region = loc_assigned_field.region;
                let value = assigned_expr_field_to_pattern_help(arena, &loc_assigned_field.value)?;
                Ok(Loc { region, value })
            })?;

            Pattern::RecordDestructure(patterns)
        }

        Expr::Tuple(fields) => Pattern::Tuple(fields.map_items_result(arena, |loc_expr| {
            let value = expr_to_pattern(arena, &loc_expr.value)?;
            Ok(Loc::at(loc_expr.region, value))
        })?),

        Expr::Float(string) => Pattern::FloatLiteral(string),
        Expr::Num(string) => Pattern::NumLiteral(string),
        Expr::NonBase10Int {
            string,
            base,
            is_negative,
        } => Pattern::NonBase10Literal {
            string,
            base,
            is_negative,
        },
        // These would not have parsed as patterns
        Expr::AccessorFunction(_)
        | Expr::RecordAccess(_, _, _)
        | Expr::TupleAccess(_, _, _)
        | Expr::List { .. }
        | Expr::Closure(_, _, _)
        | Expr::Backpassing(_, _, _)
        | Expr::BinOps { .. }
        | Expr::Defs(_, _)
        | Expr::If { .. }
        | Expr::When(..)
        | Expr::Dbg
        | Expr::DbgStmt(_, _)
        | Expr::LowLevelDbg(_, _, _)
        | Expr::Return(_, _)
        | Expr::MalformedSuffixed(..)
        | Expr::PrecedenceConflict { .. }
        | Expr::EmptyRecordBuilder(_)
        | Expr::SingleFieldRecordBuilder(_)
        | Expr::OptionalFieldInRecordBuilder(_, _)
        | Expr::RecordUpdate { .. }
        | Expr::RecordUpdater(_)
        | Expr::UnaryOp(_, _)
        | Expr::TrySuffix { .. }
        | Expr::Crash
        | Expr::RecordBuilder { .. } => return Err(()),

        Expr::Str(string) => Pattern::StrLiteral(string),
        Expr::SingleQuote(string) => Pattern::SingleQuote(string),
        Expr::MalformedIdent(string, problem) => Pattern::MalformedIdent(string, problem),
    };

    // Now we re-add the spaces

    if !expr.before.is_empty() {
        pat = Pattern::SpaceBefore(arena.alloc(pat), expr.before);
    }
    if !expr.after.is_empty() {
        pat = Pattern::SpaceAfter(arena.alloc(pat), expr.after);
    }

    Ok(pat)
}

fn assigned_expr_field_to_pattern_help<'a>(
    arena: &'a Bump,
    assigned_field: &AssignedField<'a, Expr<'a>>,
) -> Result<Pattern<'a>, ()> {
    // the assigned fields always store spaces, but this slice is often empty
    Ok(match assigned_field {
        AssignedField::RequiredValue(name, spaces, value) => {
            let pattern = expr_to_pattern(arena, &value.value)?;
            let result = arena.alloc(Loc::at(value.region, pattern));
            if spaces.is_empty() {
                Pattern::RequiredField(name.value, result)
            } else {
                Pattern::SpaceAfter(
                    arena.alloc(Pattern::RequiredField(name.value, result)),
                    spaces,
                )
            }
        }
        AssignedField::OptionalValue(name, spaces, value) => {
            let result = arena.alloc(Loc::at(value.region, value.value));
            if spaces.is_empty() {
                Pattern::OptionalField(name.value, result)
            } else {
                Pattern::SpaceAfter(
                    arena.alloc(Pattern::OptionalField(name.value, result)),
                    spaces,
                )
            }
        }
        AssignedField::LabelOnly(name) => Pattern::Identifier { ident: name.value },
        AssignedField::SpaceBefore(nested, spaces) => Pattern::SpaceBefore(
            arena.alloc(assigned_expr_field_to_pattern_help(arena, nested)?),
            spaces,
        ),
        AssignedField::SpaceAfter(nested, spaces) => Pattern::SpaceAfter(
            arena.alloc(assigned_expr_field_to_pattern_help(arena, nested)?),
            spaces,
        ),
        AssignedField::IgnoredValue(_, _, _) => return Err(()),
    })
}

pub fn parse_top_level_defs<'a>(
    arena: &'a bumpalo::Bump,
    state: State<'a>,
    defs: Defs<'a>,
) -> ParseResult<'a, Defs<'a>, EExpr<'a>> {
    let (_, (first_spaces, sp_at), state) = eat_nc(arena, state, false)?;

    let (stmts, state) = parse_stmt_seq(
        arena,
        state,
        |e, _| e.clone(),
        CHECK_FOR_ARROW | ACCEPT_MULTI_BACKPASSING,
        0,
        Loc::at(sp_at, first_spaces),
        EExpr::IndentEnd,
    )?;

    let (_, (last_spaces, _), state) = eat_nc(arena, state, false)?;

    let existing_len = defs.tags.len();

    let (mut defs, last_expr) =
        stmts_to_defs(&stmts, defs, false, arena).map_err(|e| (MadeProgress, e))?;

    if let Some(expr) = last_expr {
        let fail = EExpr::UnexpectedTopLevelExpr(expr.region.start());
        return Err((MadeProgress, fail));
    }

    if defs.tags.len() > existing_len {
        let after = slice_extend_new(&mut defs.spaces, last_spaces.iter().copied());
        let last = defs.tags.len() - 1;
        debug_assert!(defs.space_after[last].is_empty() || after.is_empty());
        defs.space_after[last] = after;
    }

    Ok((defs, state))
}

thread_local! {
    // we use a thread_local here so that tests consistently give the same pattern
    static SUFFIXED_ANSWER_COUNTER: Cell<usize> = const { Cell::new(0) };
}

// Took this approach from the `next_unique_suffixed_ident`.
fn next_unique_closure_shortcut_arg(arena: &'_ Bump) -> &str {
    SUFFIXED_ANSWER_COUNTER.with(|counter| {
        let count = counter.get();
        counter.set(count + 1);
        arena.alloc(format!("nu{}", count))
    })
}

pub(crate) fn reset_unique_closure_shortcut_arg_generator() {
    SUFFIXED_ANSWER_COUNTER.with(|counter| {
        counter.set(0);
    });
}

// todo: @ask is this convention is too smart, get feedback from the real usage
// For the space guided format of the closure shortcut, we use a nice short name for the argument,
// it is no need to be unique and expected to be modified by the User
pub const FMT_EXPAND_CLOSURE_SHORTCUT_ARG: &str = "x";

fn rest_of_closure<'a>(
    flags: ExprParseFlags,
    arena: &'a Bump,
    mut state: State<'a>,
) -> ParseResult<'a, Expr<'a>, EClosure<'a>> {
    // After the first token, all other tokens must be indented past the start of the line
    let slash_indent = state.line_indent();
    if slash_indent > state.column() {
        return Err((NoProgress, EClosure::Start(state.pos())));
    }

    let after_slash = state.pos();

    // @feat entry point for parsing the closure-shortcut
    // Expand the shortcut into the full code guided by presence of space after slash (only if actual shortcut follows)
    // e.g. this one with th space after slash `\ .foo.bar` will expand to `\x -> x.foo.bar`, but this one `\.foo.bar` will stay as-is in the formatted
    let mut body_pos = after_slash;
    let fmt_expand = state.bytes().first() == Some(&b' ');
    if fmt_expand {
        state.inc_mut();
        body_pos = state.pos();
    };

    let first_ch = state.bytes().first();
    let is_negate_op = first_ch == Some(&b'-');
    let is_not_op = first_ch == Some(&b'!');
    if is_negate_op | is_not_op {
        state.inc_mut();
    }

    // Parses `\.foo.bar + 1` into `\p -> p.foo.bar + 1`
    if state.bytes().first() == Some(&b'.') {
        let ident = if fmt_expand {
            FMT_EXPAND_CLOSURE_SHORTCUT_ARG
        } else {
            next_unique_closure_shortcut_arg(arena)
        };

        let param = Loc::at(Region::point(after_slash), Pattern::Identifier { ident });
        let mut params = Vec::with_capacity_in(1, arena);
        params.push(param);

        let mut parts = Vec::with_capacity_in(2, arena);
        parts.push(Accessor::RecordField(ident));

        let ident_state = state.clone();
        let bytes = state.bytes();
        let pos = state.pos();
        let (ident, state) = match chomp_access_chain(bytes, &mut parts) {
            Ok(width) => {
                let parts = parts.into_bump_slice();
                let ident = Ident::Access {
                    module_name: "",
                    parts,
                };
                (ident, state.leap(width))
            }
            // Handling the identity function `\.`, where the `.` was found but nothing after it, therefore the width is 1.
            Err(1) => (Ident::Plain(ident), state.inc()),
            Err(width) => {
                let fail = BadIdent::WeirdDotAccess(pos.bump_offset(width));
                malformed_ident(bytes, fail, state.leap(width))
            }
        };

        let ident_end = state.pos();
        let (suffixes, state) = parse_field_task_result_suffixes(arena, state)
            .map_err(|(_, fail)| (MadeProgress, EClosure::Body(arena.alloc(fail), ident_end)))?;

        let mut closure_shortcut = None;
        if !fmt_expand {
            closure_shortcut = Some(AccessShortcut::Closure);
        }
        let mut ident = ident_to_expr(arena, ident, closure_shortcut);
        if !suffixes.is_empty() {
            ident = apply_access_chain(arena, ident, suffixes);
        }

        let ident = if is_negate_op | is_not_op {
            let unary_op = if is_negate_op {
                UnaryOp::Negate
            } else {
                UnaryOp::Not
            };
            let not_neg_op = Loc::pos(body_pos, body_pos.next(), unary_op);
            let not_neg_ident = Loc::pos(body_pos.next(), ident_end, ident);
            let not_neg_ident = Expr::UnaryOp(arena.alloc(not_neg_ident), not_neg_op);
            Loc::pos(body_pos, ident_end, not_neg_ident)
        } else {
            Loc::pos(body_pos, ident_end, ident)
        };

        let err_pos = state.pos();
        let inc_indent: u32 = slash_indent + 1;
        let (body, state) =
            match parse_expr_start(flags, Some((ident_state, ident)), arena, state, inc_indent) {
                Ok(ok) => ok,
                Err((_, fail)) => {
                    return Err((MadeProgress, EClosure::Body(arena.alloc(fail), err_pos)))
                }
            };

        let mut shortcut = None;
        if !fmt_expand {
            shortcut = Some(ClosureShortcut::Access)
        }
        let closure = Expr::Closure(params.into_bump_slice(), arena.alloc(body), shortcut);
        return Ok((closure, state));
    }

    // Either pipe shortcut `\|> f` into `\x -> x |> f`, or the rest of BinOp's, e.g. `\+ 1` into `\x -> x + 1`,
    // Excluding the operators for which the shortcut does not make sense, assignment '=', Type Alias ':', ':=', etc.

    let (binop_shortcut, binop, state) = if is_negate_op {
        (true, BinOp::Minus, state)
    } else if let Ok((binop, state)) = parse_bin_op(state.clone()) {
        (true, binop, state)
    } else {
        // here Minus does not matter
        (false, BinOp::Minus, state)
    };

    if binop_shortcut {
        let ident = if fmt_expand {
            FMT_EXPAND_CLOSURE_SHORTCUT_ARG
        } else {
            next_unique_closure_shortcut_arg(arena)
        };

        let after_binop = state.pos();
        let param = Pattern::Identifier { ident };
        let param = Loc::pos(after_slash, after_binop, param);
        let mut params: Vec<'_, Loc<Pattern<'_>>> = Vec::with_capacity_in(1, arena);
        params.push(param);

        let inc_indent = slash_indent + 1;

        // a single closure parameter is the left value of the binary operator
        let left_var = Expr::new_var("", ident);
        let left_var = Loc::pos(body_pos, after_binop, left_var);

        // special handling of the `~` when operator
        let (body, state, what) = if binop == BinOp::When {
            let what = if fmt_expand {
                WhenShortcut::BinOp
            } else {
                WhenShortcut::Closure
            };
            let cond = Some((left_var, what));
            match when::rest_of_when_expr(cond, flags, arena, state, inc_indent) {
                Ok((expr, state)) => (expr, state, ClosureShortcut::WhenBinOp),
                Err((_, fail)) => {
                    let fail = EExpr::When(fail, after_binop);
                    return Err((MadeProgress, EClosure::Body(arena.alloc(fail), after_binop)));
                }
            }
        } else {
            // "normal" handling of the rest of the binary operators
            let expr_state = ExprState {
                operators: Vec::new_in(arena),
                arguments: Vec::new_in(arena),
                expr: left_var,
                spaces_after: &[],
                end: body_pos,
            };

            let loc_op = Loc::pos(body_pos, after_binop, binop);
            let (_, spaces_after_op, state) =
                match eat_nc_check(EExpr::IndentEnd, arena, state, inc_indent, false) {
                    Ok(ok) => ok,
                    Err((_, fail)) => {
                        return Err((MadeProgress, EClosure::Body(arena.alloc(fail), after_binop)))
                    }
                };

            match parse_after_binop(
                body_pos,
                arena,
                state,
                inc_indent,
                inc_indent,
                flags,
                spaces_after_op,
                expr_state,
                loc_op,
            ) {
                Ok((expr, state)) => (expr, state, ClosureShortcut::BinOp),
                Err((_, fail)) => {
                    return Err((MadeProgress, EClosure::Body(arena.alloc(fail), after_binop)))
                }
            }
        };

        let body = state.loc(after_binop, body);

        let shortcut = if fmt_expand { None } else { Some(what) };
        let closure = Expr::Closure(params.into_bump_slice(), arena.alloc(body), shortcut);
        return Ok((closure, state));
    }

    // Parse the params, params are comma-separated
    let inc_indent: u32 = slash_indent + 1;
    let param_pos = state.pos();
    let (_, spaces_before, state) =
        match eat_nc_check(EClosure::IndentArg, arena, state, inc_indent, false) {
            Ok(ok) => ok,
            Err((NoProgress, _)) => return Err((MadeProgress, EClosure::Arg(param_pos))),
            Err(err) => return Err(err),
        };

    let param_ident_pos = state.pos();
    let (param, state) = match parse_closure_param(arena, state, inc_indent) {
        Ok(ok) => ok,
        Err((NoProgress, _)) => return Err((MadeProgress, EClosure::Arg(param_pos))),
        Err((_, fail)) => return Err((MadeProgress, EClosure::Pattern(fail, param_ident_pos))),
    };

    let (_, spaces_after, state) =
        match eat_nc_check(EClosure::IndentArrow, arena, state, inc_indent, false) {
            Ok(ok) => ok,
            Err((NoProgress, _)) => return Err((MadeProgress, EClosure::Arg(param_pos))),
            Err(err) => return Err(err),
        };

    let first_param = param.spaced_around(arena, spaces_before, spaces_after);
    let mut params = Vec::with_capacity_in(1, arena);
    params.push(first_param);

    let mut state = state;
    loop {
        if state.bytes().first() != Some(&b',') {
            break;
        }
        state.inc_mut();

        // After delimiter found, parse the parameter
        let param_pos = state.pos();
        let (_, spaces_before, next_state) =
            match eat_nc_check(EClosure::IndentArg, arena, state, inc_indent, false) {
                Ok(ok) => ok,
                Err((NoProgress, _)) => return Err((MadeProgress, EClosure::Arg(param_pos))),
                Err(err) => return Err(err),
            };

        let param_ident_pos = next_state.pos();
        let (param, next_state) = match parse_closure_param(arena, next_state, inc_indent) {
            Ok(ok) => ok,
            Err((NoProgress, _)) => return Err((MadeProgress, EClosure::Arg(param_pos))),
            Err((_, fail)) => return Err((MadeProgress, EClosure::Pattern(fail, param_ident_pos))),
        };

        let (_, spaces_after, next_state) =
            match eat_nc_check(EClosure::IndentArrow, arena, next_state, inc_indent, false) {
                Ok(ok) => ok,
                Err((NoProgress, _)) => return Err((MadeProgress, EClosure::Arg(param_pos))),
                Err(err) => return Err(err),
            };

        let next_param = param.spaced_around(arena, spaces_before, spaces_after);
        params.push(next_param);
        state = next_state;
    }

    // Parse the arrow which separates params from body, only then parse the body
    if !state.bytes().starts_with(b"->") {
        return Err((MadeProgress, EClosure::Arrow(state.pos())));
    }
    state.leap_mut(2);

    let body_indent = state.line_indent() + 1;
    let (first_nl, state) = eat_nc_loc_c(EClosure::IndentBody, arena, state, body_indent, true)?;

    let (body, state) = if first_nl.value.is_empty() {
        let err_pos = state.pos();
        match parse_expr_start(flags, None, arena, state, inc_indent) {
            Ok(ok) => ok,
            Err((_, fail)) => {
                return Err((MadeProgress, EClosure::Body(arena.alloc(fail), err_pos)))
            }
        }
    } else {
        let (stmts, state) = parse_stmt_seq(
            arena,
            state,
            EClosure::Body,
            flags,
            inc_indent,
            Loc::at(first_nl.region, &[]),
            EClosure::IndentBody,
        )?;

        let err_pos = state.pos();
        if stmts.is_empty() {
            let fail = EClosure::Body(arena.alloc(EExpr::Start(err_pos)), err_pos);
            return Err((MadeProgress, fail));
        }

        match stmts_to_expr(&stmts, arena) {
            Ok(out) => (out.spaced_before(arena, first_nl.value), state),
            Err(fail) => return Err((MadeProgress, EClosure::Body(arena.alloc(fail), err_pos))),
        }
    };

    let closure = Expr::Closure(params.into_bump_slice(), arena.alloc(body), None);
    Ok((closure, state))
}

mod when {
    use super::*;
    use crate::{
        ast::{WhenBranch, WhenShortcut},
        blankspace::eat_nc,
    };

    pub fn rest_of_when_expr<'a>(
        cond: Option<(Loc<Expr<'a>>, WhenShortcut)>,
        flags: ExprParseFlags,
        arena: &'a Bump,
        state: State<'a>,
        mut min_indent: u32,
    ) -> ParseResult<'a, Expr<'a>, EWhen<'a>> {
        if min_indent == 0 {
            min_indent = state.line_indent();
        }

        let (shortcut, cond, state) = if let Some((cond, what)) = cond {
            (Some(what), cond, state)
        } else {
            let (_, spaces_before, state) =
                eat_nc_check(EWhen::IndentCondition, arena, state, min_indent, true)?;

            let at_cond = state.pos();
            let (cond, state) = match parse_expr_start(flags, None, arena, state, min_indent) {
                Ok(ok) => ok,
                Err((_, fail)) => {
                    return Err((MadeProgress, EWhen::Condition(arena.alloc(fail), at_cond)))
                }
            };

            let (_, (spaces_after, _), state) = eat_nc(arena, state, true)?;
            let cond = cond.spaced_around(arena, spaces_before, spaces_after);

            let n = eat_keyword(keyword::IS, &state);
            if n == 0 {
                return Err((MadeProgress, EWhen::Is(state.pos())));
            }
            (None, cond, state.leap(n))
        };

        // Note that we allow the `is` to be at any indent level, since this doesn't introduce any
        // ambiguity. The formatter will fix it up.
        // We require that branches are indented relative to the line containing the `is`.
        let branch_indent = state.line_indent() + 1;

        // 1. Parse the first branch and get its indentation level (it must be >= branch_indent).
        // 2. Parse the other branches. Their indentation levels must be == the first branch's.
        let (((pattern_indent, first_patterns), guard), state) =
            match parse_branch_alternatives(flags, None, arena, state, branch_indent) {
                Ok(ok) => ok,
                Err((_, fail)) => return Err((MadeProgress, fail)),
            };

        // Parse the first "->" and the expression after it.
        let (value, mut state) = parse_branch_result(arena, state)?;

        // Record this as the first branch, then optionally parse additional branches.
        let mut branches: Vec<'a, &'a WhenBranch<'a>> = Vec::with_capacity_in(2, arena);
        branches.push(arena.alloc(WhenBranch {
            patterns: first_patterns.into_bump_slice(),
            value,
            guard,
        }));

        while !state.bytes().is_empty() {
            match parse_branch_alternatives(
                flags,
                Some(pattern_indent),
                arena,
                state.clone(),
                branch_indent,
            ) {
                Ok((((indent_column, patterns), guard), guard_state)) => {
                    if pattern_indent == indent_column {
                        let (value, next_state) = parse_branch_result(arena, guard_state)?;

                        let branch = WhenBranch {
                            patterns: patterns.into_bump_slice(),
                            value,
                            guard,
                        };
                        branches.push(arena.alloc(branch));
                        state = next_state;
                    } else {
                        let indent = pattern_indent - indent_column;
                        let fail = EWhen::PatternAlignment(indent, guard_state.pos());
                        return Err((MadeProgress, fail));
                    }
                }
                Err((NoProgress, _)) => break,
                Err(err) => return Err(err),
            }
        }

        let when = Expr::When(arena.alloc(cond), branches.into_bump_slice(), shortcut);
        Ok((when, state))
    }

    #[allow(clippy::type_complexity)]
    fn parse_branch_alternatives<'a>(
        flags: ExprParseFlags,
        pattern_indent: Option<u32>,
        arena: &'a Bump,
        state: State<'a>,
        min_indent: u32,
    ) -> ParseResult<'a, ((u32, Vec<'a, Loc<Pattern<'a>>>), Option<Loc<Expr<'a>>>), EWhen<'a>> {
        let flags = flags.unset(CHECK_FOR_ARROW);

        // put no restrictions on the indent after the spaces; we'll check it manually
        let (_, (indent_spaces, _), state) = eat_nc(arena, state, false)?;

        // the region is not reliable for the indent column in the case of
        // parentheses around patterns
        let pattern_column = state.column();

        if let Some(wanted) = pattern_indent {
            if pattern_column > wanted {
                let err_progress = if state.bytes().starts_with(b"->") {
                    MadeProgress
                } else {
                    NoProgress
                };
                return Err((err_progress, EWhen::IndentPattern(state.pos())));
            }
            if pattern_column < wanted {
                let indent = wanted - pattern_column;
                return Err((NoProgress, EWhen::PatternAlignment(indent, state.pos())));
            }
        }

        let pat_indent = min_indent.max(pattern_indent.unwrap_or(min_indent));

        let (sp, spaces_before, state) =
            match eat_nc_check(EWhen::IndentPattern, arena, state, pat_indent, false) {
                Ok(ok) => ok,
                Err((_, fail)) => return Err((NoProgress, fail)),
            };

        let pattern_pos = state.pos();
        let (pattern, state) = match crate::pattern::parse_pattern(arena, state, pat_indent) {
            Ok(ok) => ok,
            Err((ep, fail)) => return Err((ep.or(sp), EWhen::Pattern(fail, pattern_pos))),
        };

        let (_, spaces_after, mut state) =
            eat_nc_check(EWhen::IndentPattern, arena, state, pat_indent, true)?;

        let first_pattern = pattern.spaced_around(arena, spaces_before, spaces_after);
        let mut patterns = Vec::with_capacity_in(1, arena);
        patterns.push(first_pattern);

        loop {
            let prev_state = state.clone();
            if state.bytes().first() == Some(&b'|') {
                state.inc_mut();

                let (_, spaces_before, next_state) =
                    eat_nc_check(EWhen::IndentPattern, arena, state, pat_indent, true)?;

                let pattern_pos = next_state.pos();
                let (pat, next_state) =
                    match crate::pattern::parse_pattern(arena, next_state, pat_indent) {
                        Ok(ok) => ok,
                        Err((_, fail)) => {
                            return Err((MadeProgress, EWhen::Pattern(fail, pattern_pos)))
                        }
                    };

                let (_, spaces_after, next_state) =
                    eat_nc_check(EWhen::IndentPattern, arena, next_state, pat_indent, true)?;

                let pattern = pat.spaced_around(arena, spaces_before, spaces_after);
                patterns.push(pattern);
                state = next_state;
            } else {
                state = prev_state;
                break;
            }
        }

        // tag spaces onto the first parsed pattern
        if let Some(first) = patterns.get_mut(0) {
            *first = (*first).spaced_before(arena, indent_spaces);
        }

        let column_patterns = (pattern_column, patterns);
        let original_state = state.clone();

        let n = eat_keyword(keyword::IF, &state);
        if n == 0 {
            return Ok(((column_patterns, None), original_state));
        }
        state.leap_mut(n);

        // TODO we should require space before the expression but not after
        let (_, spaces_before, state) =
            eat_nc_check(EWhen::IndentIfGuard, arena, state, min_indent, true)?;

        let guard_pos = state.pos();
        let (guard, state) = parse_expr_start(flags, None, arena, state, min_indent + 1)
            .map_err(|(_, fail)| (MadeProgress, EWhen::IfGuard(arena.alloc(fail), guard_pos)))?;

        let (_, spaces_after, state) =
            eat_nc_check(EWhen::IndentArrow, arena, state, min_indent, true)?;

        let guard = guard.spaced_around(arena, spaces_before, spaces_after);
        Ok(((column_patterns, Some(guard)), state))
    }

    /// Parsing the righthandside of a branch in a when conditional.
    fn parse_branch_result<'a>(
        arena: &'a Bump,
        state: State<'a>,
    ) -> ParseResult<'a, Loc<Expr<'a>>, EWhen<'a>> {
        if !state.bytes().starts_with(b"->") {
            return Err((MadeProgress, EWhen::Arrow(state.pos())));
        }
        let state = state.leap(2);

        let inc_indent = state.line_indent() + 1;
        match parse_block(
            CHECK_FOR_ARROW | ACCEPT_MULTI_BACKPASSING,
            arena,
            state,
            inc_indent,
            EWhen::IndentBranch,
            EWhen::Branch,
            None,
        ) {
            Ok(ok) => Ok(ok),
            Err((_, fail)) => Err((MadeProgress, fail)),
        }
    }
}

fn rest_of_expect_stmt<'a>(
    start: Position,
    flags: ExprParseFlags,
    preceding_comment: Region,
    arena: &'a Bump,
    state: State<'a>,
) -> ParseResult<'a, Loc<Stmt<'a>>, EExpr<'a>> {
    let inc_indent = state.line_indent() + 1;
    match parse_block(
        flags,
        arena,
        state,
        inc_indent,
        EExpect::IndentCondition,
        EExpect::Condition,
        None,
    ) {
        Ok((condition, state)) => {
            let vd = ValueDef::Expect {
                condition: arena.alloc(condition),
                preceding_comment,
            };
            Ok((state.loc(start, Stmt::ValueDef(vd)), state))
        }
        Err((_, fail)) => Err((MadeProgress, EExpr::Expect(fail, start))),
    }
}

fn rest_of_return_stmt<'a>(
    start: Position,
    flags: ExprParseFlags,
    arena: &'a Bump,
    state: State<'a>,
) -> ParseResult<'a, Loc<Stmt<'a>>, EExpr<'a>> {
    let inc_indent = state.line_indent() + 1;
    match parse_block(
        flags,
        arena,
        state,
        inc_indent,
        EReturn::IndentReturnValue,
        EReturn::ReturnValue,
        None,
    ) {
        Ok((expr, state)) => {
            let expr = Loc::pos(start, expr.region.end(), expr.value);
            let stmt = Stmt::Expr(Expr::Return(arena.alloc(expr), None));
            Ok((state.loc(start, stmt), state))
        }
        Err((_, fail)) => Err((MadeProgress, EExpr::Return(fail, start))),
    }
}

fn rest_of_dbg_stmt<'a>(
    start: Position,
    flags: ExprParseFlags,
    preceding_comment: Region,
    arena: &'a Bump,
    state: State<'a>,
) -> ParseResult<'a, Loc<Stmt<'a>>, EExpr<'a>> {
    let inc_indent = state.line_indent() + 1;
    match parse_block(
        flags,
        arena,
        state,
        inc_indent,
        EExpect::IndentCondition,
        EExpect::Condition,
        None,
    ) {
        Ok((condition, state)) => {
            let vd = ValueDef::Dbg {
                condition: arena.alloc(condition),
                preceding_comment,
            };
            Ok((state.loc(start, Stmt::ValueDef(vd)), state))
        }
        Err((_, fail)) => Err((MadeProgress, EExpr::Dbg(fail, start))),
    }
}

fn parse_module_import<'a>(
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
) -> ParseResult<'a, ModuleImport<'a>, EImport<'a>> {
    let (_, before_name, state) =
        eat_nc_check(EImport::IndentStart, arena, state, min_indent, false)?;

    let name_pos = state.pos();
    let (name, state) = parse_imported_module_name(state)?;
    let name = state.loc(name_pos, name);

    let params_pos = state.pos();
    let (params, state) = match parse_import_params(arena, state.clone(), min_indent) {
        Ok((out, state)) => (Some(out), state),
        Err((NoProgress, _)) => (None, state),
        Err((_, fail)) => return Err((MadeProgress, EImport::Params(fail, params_pos))),
    };

    let (alias, state) = match import_as(arena, state.clone(), min_indent) {
        Ok((out, state)) => (Some(out), state),
        Err((NoProgress, _)) => (None, state),
        Err(err) => return Err(err),
    };

    let (exposed, state) = match import_exposing(arena, state.clone(), min_indent) {
        Ok((out, state)) => (Some(out), state),
        Err((NoProgress, _)) => (None, state),
        Err(err) => return Err(err),
    };

    let import = ModuleImport {
        before_name,
        name,
        params,
        alias,
        exposed,
    };
    Ok((import, state))
}

fn rest_of_import<'a>(
    start: Position,
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
) -> ParseResult<'a, Loc<Stmt<'a>>, EExpr<'a>> {
    let inc_indent = min_indent + 1;
    let (vd, state) = match parse_module_import(arena, state.clone(), inc_indent) {
        Ok((module_import, state)) => (ValueDef::ModuleImport(module_import), state),
        Err((MadeProgress, fail)) => return Err((MadeProgress, EExpr::Import(fail, start))),
        Err(_) => {
            let (_, before_path, state) =
                eat_nc_check(EImport::IndentStart, arena, state, inc_indent, false)
                    .map_err(|(_, fail)| (MadeProgress, EExpr::Import(fail, start)))?;

            let path_pos = state.pos();
            let (_, path, state) =
                string_literal::parse_str_literal(arena, state).map_err(|_| {
                    let fail = EExpr::Import(EImport::IngestedPath(path_pos), start);
                    (MadeProgress, fail)
                })?;

            let path = state.loc(path_pos, path);

            let (name, state) = import_ingested_file_as(arena, state, inc_indent)
                .map_err(|(_, fail)| (MadeProgress, EExpr::Import(fail, start)))?;

            let (annotation, state) =
                match parse_import_ingested_file_ann(arena, state.clone(), inc_indent) {
                    Ok((out, state)) => (Some(out), state),
                    Err((NoProgress, _)) => (None, state),
                    Err((_, fail)) => return Err((MadeProgress, EExpr::Import(fail, start))),
                };

            let import = IngestedFileImport {
                before_path,
                path,
                name,
                annotation,
            };
            (ValueDef::IngestedFileImport(import), state)
        }
    };

    let has_reached_new_line_or_eof = state.has_reached_end();
    let (_, spaces_after, _) =
        match eat_nc_check(EImport::EndNewline, arena, state.clone(), min_indent, false) {
            Ok(ok) => ok,
            Err((_, fail)) => return Err((MadeProgress, EExpr::Import(fail, start))),
        };

    if !has_reached_new_line_or_eof && spaces_after.is_empty() {
        let fail = EImport::EndNewline(state.pos());
        return Err((MadeProgress, EExpr::Import(fail, start)));
    }

    Ok((state.loc(start, Stmt::ValueDef(vd)), state))
}

fn rest_of_if_expr<'a>(
    flags: ExprParseFlags,
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
) -> ParseResult<'a, Expr<'a>, EIf<'a>> {
    let if_indent = state.line_indent();

    let mut branches = Vec::with_capacity_in(1, arena);

    let mut loop_state = state;
    let at_final_else = loop {
        let (_, spaces_before_cond, state) = eat_nc_check(
            EIf::IndentCondition,
            arena,
            loop_state.clone(),
            min_indent,
            false,
        )?;

        let cond_pos = state.pos();
        let (cond, state) = parse_expr_start(
            CHECK_FOR_ARROW | ACCEPT_MULTI_BACKPASSING,
            None,
            arena,
            state,
            min_indent,
        )
        .map_err(|(p, fail)| (p, EIf::Condition(arena.alloc(fail), cond_pos)))?;

        let (_, spaces_after_cond, state) =
            eat_nc_check(EIf::IndentThenToken, arena, state.clone(), min_indent, true)?;

        let n = eat_keyword(keyword::THEN, &state);
        if n == 0 {
            return Err((MadeProgress, EIf::Then(state.pos())));
        }
        let state = state.leap(n);

        let cond = cond.spaced_around(arena, spaces_before_cond, spaces_after_cond);

        let (then_expr, state) = parse_block(
            CHECK_FOR_ARROW | ACCEPT_MULTI_BACKPASSING,
            arena,
            state,
            0,
            EIf::IndentThenBranch,
            EIf::ThenBranch,
            None,
        )
        .map_err(|(_, fail)| (MadeProgress, fail))?;

        let (_, spaces_after_then, state) =
            eat_nc_check(EIf::IndentElseToken, arena, state, min_indent, true)?;

        let then_expr = if spaces_after_then.is_empty() {
            then_expr
        } else {
            let expr = if let Expr::SpaceBefore(x, before) = then_expr.value {
                Expr::SpaceBefore(arena.alloc(Expr::SpaceAfter(x, spaces_after_then)), before)
            } else {
                Expr::SpaceAfter(arena.alloc(then_expr.value), spaces_after_then)
            };
            Loc::at(then_expr.region, expr)
        };

        let n = eat_keyword(keyword::ELSE, &state);
        if n == 0 {
            return Err((MadeProgress, EIf::Else(state.pos())));
        }
        let state = state.leap(n);

        branches.push((cond, then_expr));

        // try to parse another `if`
        // NOTE this drops spaces between the `else` and the `if`
        if let Ok((_, _, state)) =
            eat_nc_check(EIf::IndentIf, arena, state.clone(), min_indent, false)
        {
            let n = eat_keyword(keyword::IF, &state);
            if n > 0 {
                loop_state = state.leap(n);
                continue;
            }
        }
        break state;
    };

    let else_indent = at_final_else.line_indent();
    let indented_else = else_indent > if_indent;

    let min_indent = if !indented_else {
        else_indent + 1
    } else {
        if_indent
    };

    let (else_branch, state) = parse_block(
        flags,
        arena,
        at_final_else,
        min_indent,
        EIf::IndentElseBranch,
        EIf::ElseBranch,
        None,
    )?;

    let expr = Expr::If {
        if_thens: branches.into_bump_slice(),
        final_else: arena.alloc(else_branch),
        indented_else,
    };

    Ok((expr, state))
}

/// Parse a block of statements.
/// For example, the then and else branches of an `if` expression are both blocks.
/// There are two cases here:
/// 1. If there is a preceding newline, then the block must be indented and is allowed to have definitions.
/// 2. If there is no preceding newline, then the block must consist of a single expression (no definitions).
/// 3. If you pass `first_spaces: None` this function will parse the spaces itself
#[allow(clippy::too_many_arguments)]
fn parse_block<'a, E>(
    flags: ExprParseFlags,
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
    indent_problem: fn(Position) -> E,
    wrap_error: fn(&'a EExpr<'a>, Position) -> E,
    first_spaces: Option<Loc<&'a [CommentOrNewline<'a>]>>,
) -> ParseResult<'a, Loc<Expr<'a>>, E>
where
    E: 'a + SpaceProblem,
{
    let (first_spaces, state) = if let Some(first_spaces) = first_spaces {
        (first_spaces, state)
    } else {
        // if no spaces are provided, parse them here
        eat_nc_loc_c(indent_problem, arena, state, min_indent, false)?
    };

    if !first_spaces.value.is_empty() {
        let (stmts, state) = parse_stmt_seq(
            arena,
            state,
            wrap_error,
            flags,
            min_indent,
            Loc::at(first_spaces.region, &[]),
            indent_problem,
        )?;

        let last_pos = state.pos();
        if stmts.is_empty() {
            let fail = wrap_error(arena.alloc(EExpr::Start(last_pos)), last_pos);
            return Err((NoProgress, fail));
        }

        match stmts_to_expr(&stmts, arena) {
            Ok(expr) => Ok((expr.spaced_before(arena, first_spaces.value), state)),
            Err(fail) => Err((MadeProgress, wrap_error(arena.alloc(fail), last_pos))),
        }
    } else {
        let prev_pos = state.pos();
        match parse_expr_start(flags, None, arena, state, min_indent) {
            Ok((expr, state)) => Ok((expr.spaced_before(arena, first_spaces.value), state)),
            Err((_, fail)) => Err((MadeProgress, wrap_error(arena.alloc(fail), prev_pos))),
        }
    }
}

/// Parse a sequence of statements, which we'll later process into an expression.
/// Statements can include:
/// - assignments
/// - type annotations
/// - expressions
/// - [multi]backpassing
///
/// This function doesn't care about whether the order of those statements makes any sense.
/// e.g. it will happily parse two expressions in a row, or backpassing with nothing following it.
fn parse_stmt_seq<'a, E: SpaceProblem + 'a>(
    arena: &'a Bump,
    mut state: State<'a>,
    wrap_error: fn(&'a EExpr<'a>, Position) -> E,
    flags: ExprParseFlags,
    min_indent: u32,
    mut last_space: Loc<&'a [CommentOrNewline<'a>]>,
    indent_problem: fn(Position) -> E,
) -> ParseResult<'a, Vec<'a, SpacesBefore<'a, Loc<Stmt<'a>>>>, E> {
    let mut stmts = Vec::new_in(arena);
    let mut prev = state.clone();
    loop {
        if at_terminator(&state) {
            state = prev;
            break;
        }
        let start = state.pos();
        let stmt = match parse_stmt(flags, last_space.region, arena, state.clone(), min_indent) {
            Ok((stmt, next)) => {
                prev = next.clone();
                state = next;
                stmt
            }
            Err((NoProgress, _)) => {
                if stmts.is_empty() {
                    let fail = wrap_error(arena.alloc(EExpr::Start(start)), start);
                    return Err((NoProgress, fail));
                }
                state = prev;
                break;
            }
            Err((_, fail)) => {
                return Err((MadeProgress, wrap_error(arena.alloc(fail), start)));
            }
        };

        stmts.push(SpacesBefore {
            before: last_space.value,
            item: stmt,
        });

        match eat_nc_loc_c(indent_problem, arena, state.clone(), min_indent, false) {
            Ok((space, new_state)) => {
                if space.value.is_empty() {
                    // require a newline or a terminator after the statement
                    if at_terminator(&new_state) {
                        state = prev;
                        break;
                    }
                    let last_pos = state.pos();
                    let fail = wrap_error(arena.alloc(EExpr::BadExprEnd(last_pos)), last_pos);
                    return Err((MadeProgress, fail));
                }
                last_space = space;
                state = new_state;
            }
            Err(_) => {
                break;
            }
        };
    }
    Ok((stmts, state))
}

/// Check if the current byte is a terminator for a sequence of statements
fn at_terminator(state: &State<'_>) -> bool {
    matches!(
        state.bytes().first(),
        None | Some(b']' | b'}' | b')' | b',')
    )
}

/// Convert a sequence of statements into a `Expr::Defs` expression
/// (which is itself a Defs struct and final expr)
fn stmts_to_expr<'a>(
    stmts: &[SpacesBefore<'a, Loc<Stmt<'a>>>],
    arena: &'a Bump,
) -> Result<Loc<Expr<'a>>, EExpr<'a>> {
    if stmts.len() > 1 {
        let first_pos = stmts.first().unwrap().item.region.start();
        let last_pos = stmts.last().unwrap().item.region.end();

        let (defs, last_expr) = stmts_to_defs(stmts, Defs::default(), true, arena)?;

        let final_expr = match last_expr {
            Some(e) => e,
            None => return Err(EExpr::DefMissingFinalExpr(last_pos)),
        };

        if defs.is_empty() {
            Ok(final_expr)
        } else {
            let defs = Expr::Defs(arena.alloc(defs), arena.alloc(final_expr));
            Ok(Loc::pos(first_pos, last_pos, defs))
        }
    } else {
        let SpacesBefore {
            before: space,
            item: Loc {
                region: stmt_at,
                value: stmt,
            },
        } = *stmts.last().unwrap();
        let expr = match stmt {
            Stmt::Expr(e) => e.spaced_before(arena, space),
            Stmt::ValueDef(ValueDef::Dbg { condition, .. }) => {
                // If we parse a `dbg` as the last thing in a series of statements then it's
                // actually an expression.
                let dbg = Loc::at(stmt_at, Expr::Dbg);
                Expr::Apply(arena.alloc(dbg), arena.alloc([condition]), CalledVia::Space)
            }
            Stmt::ValueDef(ValueDef::Expect { .. }) => {
                let end = stmt_at.end();
                let fail = EExpect::Continuation(arena.alloc(EExpr::IndentEnd(end)), end);
                return Err(EExpr::Expect(fail, stmt_at.start()));
            }
            Stmt::Backpassing(..) | Stmt::TypeDef(_) | Stmt::ValueDef(_) => {
                return Err(EExpr::IndentEnd(stmt_at.end()))
            }
        };

        Ok(Loc::at(stmt_at, expr))
    }
}

/// Convert a sequence of `Stmt` into a Defs and an optional final expression.
/// todo: @perf Future refactoring opportunity: push this logic directly into where we're
/// parsing the statements.
fn stmts_to_defs<'a>(
    stmts: &[SpacesBefore<'a, Loc<Stmt<'a>>>],
    mut defs: Defs<'a>,
    exprify_dbg: bool,
    arena: &'a Bump,
) -> Result<(Defs<'a>, Option<Loc<Expr<'a>>>), EExpr<'a>> {
    let mut last_expr = None;
    let mut i = 0;
    while i < stmts.len() {
        let SpacesBefore {
            item: Loc { region, value },
            before,
        } = stmts[i];
        match value {
            Stmt::Expr(Expr::Return(return_value, _after_return)) => {
                if i == stmts.len() - 1 {
                    last_expr = Some(Loc::at_zero(Expr::Return(return_value, None)));
                } else {
                    let rest = stmts_to_expr(&stmts[i + 1..], arena)?;
                    last_expr = Some(Loc::at_zero(Expr::Return(
                        return_value,
                        Some(arena.alloc(rest)),
                    )));
                }

                // don't re-process the rest of the statements, they got consumed by the early return
                break;
            }
            Stmt::Expr(e) => {
                if i + 1 < stmts.len() {
                    let def = ValueDef::Stmt(arena.alloc(Loc::at(region, e)));
                    defs.push_value_def_before(def, region, before);
                } else {
                    let e = e.spaced_before(arena, before);
                    last_expr = Some(Loc::at(region, e));
                }
            }
            Stmt::Backpassing(pats, call) => {
                if i + 1 >= stmts.len() {
                    return Err(EExpr::BackpassContinue(region.end()));
                }

                let rest = stmts_to_expr(&stmts[i + 1..], arena)?;

                let e = Expr::Backpassing(arena.alloc(pats), arena.alloc(call), arena.alloc(rest));

                let e = e.spaced_before(arena, before);
                last_expr = Some(Loc::pos(region.start(), rest.region.end(), e));

                // don't re-process the rest of the statements; they got consumed by the backpassing
                break;
            }

            Stmt::TypeDef(td) => {
                if let (
                    TypeDef::Alias {
                        header,
                        ann: ann_type,
                    },
                    Some((
                        spaces_middle,
                        Stmt::ValueDef(ValueDef::Body(loc_pattern, loc_def_expr)),
                    )),
                ) = (td, stmts.get(i + 1).map(|s| (s.before, s.item.value)))
                {
                    if spaces_middle.len() <= 1
                        || header
                            .vars
                            .first()
                            .map(|var| var.value.equivalent(&loc_pattern.value))
                            .unwrap_or(false)
                    {
                        // This is a case like
                        //   UserId x : [UserId Int]
                        //   UserId x = UserId 42
                        // We optimistically parsed the first line as an alias; we now turn it
                        // into an annotation.

                        let region = Region::span_across(&loc_pattern.region, &loc_def_expr.region);

                        let value_def = join_alias_to_body(
                            arena,
                            header,
                            ann_type,
                            spaces_middle,
                            loc_pattern,
                            loc_def_expr,
                        );

                        let region = Region::span_across(&header.name.region, &region);
                        defs.push_value_def(value_def, region, before, &[]);

                        i += 1;
                    } else {
                        defs.push_type_def(td, region, before, &[])
                    }
                } else {
                    defs.push_type_def(td, region, before, &[])
                }
            }
            Stmt::ValueDef(vd) => {
                // NOTE: it shouldn't be necessary to convert ValueDef::Dbg into an expr, but
                // it turns out that ValueDef::Dbg exposes some bugs in the rest of the compiler.
                // In particular, it seems that the solver thinks the dbg expr must be a bool.
                if let ValueDef::Dbg {
                    condition,
                    preceding_comment: _,
                } = vd
                {
                    if exprify_dbg {
                        let e = if i + 1 < stmts.len() {
                            let rest = stmts_to_expr(&stmts[i + 1..], arena)?;
                            Expr::DbgStmt(arena.alloc(condition), arena.alloc(rest))
                        } else {
                            Expr::Apply(
                                arena.alloc(Loc::at(region, Expr::Dbg)),
                                arena.alloc([condition]),
                                CalledVia::Space,
                            )
                        };

                        let e = e.spaced_before(arena, before);
                        last_expr = Some(Loc::at(region, e));

                        // don't re-process the rest of the statements; they got consumed by the dbg expr
                        break;
                    }
                }

                if let (
                    ValueDef::Annotation(ann_pattern, ann_type),
                    Some((
                        spaces_middle,
                        Stmt::ValueDef(ValueDef::Body(loc_pattern, loc_def_expr)),
                    )),
                ) = (vd, stmts.get(i + 1).map(|s| (s.before, s.item.value)))
                {
                    if spaces_middle.len() <= 1 || ann_pattern.value.equivalent(&loc_pattern.value)
                    {
                        let region = Region::span_across(&loc_pattern.region, &loc_def_expr.region);

                        let value_def = ValueDef::AnnotatedBody {
                            ann_pattern: arena.alloc(ann_pattern),
                            ann_type: arena.alloc(ann_type),
                            lines_between: spaces_middle,
                            body_pattern: loc_pattern,
                            body_expr: loc_def_expr,
                        };

                        let region =
                            roc_region::all::Region::span_across(&ann_pattern.region, &region);
                        defs.push_value_def(value_def, region, before, &[]);
                        i += 1;
                    } else {
                        defs.push_value_def(vd, region, before, &[])
                    }
                } else {
                    defs.push_value_def(vd, region, before, &[])
                }
            }
        }

        i += 1;
    }
    Ok((defs, last_expr))
}

/// Given a type alias and a value definition, join them into a AnnotatedBody
pub fn join_alias_to_body<'a>(
    arena: &'a Bump,
    header: TypeHeader<'a>,
    ann_type: Loc<TypeAnnotation<'a>>,
    spaces_middle: &'a [CommentOrNewline<'a>],
    body_pattern: &'a Loc<Pattern<'a>>,
    body_expr: &'a Loc<Expr<'a>>,
) -> ValueDef<'a> {
    let loc_name = arena.alloc(header.name.map(|x| Pattern::Tag(x)));
    let ann_pattern = Pattern::Apply(loc_name, header.vars);

    let vars_region = Region::across_all(header.vars.iter().map(|v| &v.region));
    let region_ann_pattern = Region::span_across(&loc_name.region, &vars_region);
    let loc_ann_pattern = Loc::at(region_ann_pattern, ann_pattern);

    ValueDef::AnnotatedBody {
        ann_pattern: arena.alloc(loc_ann_pattern),
        ann_type: arena.alloc(ann_type),
        lines_between: spaces_middle,
        body_pattern,
        body_expr,
    }
}

fn ident_to_expr<'a>(
    arena: &'a Bump,
    src: Ident<'a>,
    shortcut: Option<AccessShortcut>,
) -> Expr<'a> {
    match src {
        Ident::Plain(ident) => Expr::new_var_shortcut("", ident, shortcut),
        Ident::Tag(string) => Expr::Tag(string),
        Ident::OpaqueRef(string) => Expr::OpaqueRef(string),
        Ident::Access { module_name, parts } => {
            // The first value in the iterator is the variable name,
            // e.g. `foo` in `foo.bar.baz`
            let mut iter = parts.iter();
            let mut answer = match iter.next() {
                Some(Accessor::RecordField(ident)) => {
                    Expr::new_var_shortcut(module_name, ident, shortcut)
                }
                Some(Accessor::TupleIndex(_)) => {
                    // TODO: make this state impossible to represent in Ident::Access,
                    // by splitting out parts[0] into a separate field with a type of `&'a str`,
                    // rather than a `&'a [Accessor<'a>]`.
                    internal_error!("Parsed an Ident::Access with a first part of a tuple index");
                }
                None => {
                    internal_error!("Parsed an Ident::Access with no parts");
                }
            };

            // The remaining items in the iterator are record field accesses,
            // e.g. `bar` in `foo.bar.baz`, followed by `baz`
            let mut first = true;
            for field in iter {
                let shortcut = if first { shortcut } else { None };
                first = false;
                // Wrap the previous answer in the new one, so we end up
                // with a nested Expr. That way, `foo.bar.baz` gets represented
                // in the AST as if it had been written (foo.bar).baz all along.
                match field {
                    Accessor::RecordField(field) => {
                        answer = Expr::RecordAccess(arena.alloc(answer), field, shortcut);
                    }
                    Accessor::TupleIndex(index) => {
                        answer = Expr::TupleAccess(arena.alloc(answer), index, shortcut);
                    }
                }
            }
            answer
        }
        Ident::AccessorFunction(string) => Expr::AccessorFunction(string),
        Ident::RecordUpdaterFunction(string) => Expr::RecordUpdater(string),
        Ident::Malformed(string, problem) => Expr::MalformedIdent(string, problem),
    }
}

fn rest_of_list_expr<'a>(
    start: Position,
    arena: &'a Bump,
    state: State<'a>,
) -> ParseResult<'a, Loc<Expr<'a>>, EExpr<'a>> {
    let elem_p = move |a, state: State<'a>| {
        let expr_pos = state.pos();
        parse_expr_start(CHECK_FOR_ARROW, None, a, state, 0)
            .map_err(|(p, fail)| (p, EList::Expr(a.alloc(fail), expr_pos)))
    };

    let (elems, state) = collection_inner(arena, state, elem_p, Expr::SpaceBefore)
        .map_err(|(_, fail)| (MadeProgress, EExpr::List(fail, start)))?;

    if state.bytes().first() != Some(&b']') {
        let fail = EList::End(state.pos());
        return Err((MadeProgress, EExpr::List(fail, start)));
    }
    let state = state.inc();

    let elems = elems.ptrify_items(arena);
    Ok((state.loc(start, Expr::List(elems)), state))
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum RecordField<'a> {
    RequiredValue(Loc<&'a str>, &'a [CommentOrNewline<'a>], &'a Loc<Expr<'a>>),
    OptionalValue(Loc<&'a str>, &'a [CommentOrNewline<'a>], &'a Loc<Expr<'a>>),
    IgnoredValue(Loc<&'a str>, &'a [CommentOrNewline<'a>], &'a Loc<Expr<'a>>),
    LabelOnly(Loc<&'a str>),
    SpaceBefore(&'a RecordField<'a>, &'a [CommentOrNewline<'a>]),
    SpaceAfter(&'a RecordField<'a>, &'a [CommentOrNewline<'a>]),
}

#[derive(Debug)]
pub struct FoundApplyValue;

impl<'a> RecordField<'a> {
    fn is_ignored_value(&self) -> bool {
        let mut current = self;

        loop {
            match current {
                RecordField::IgnoredValue(_, _, _) => break true,
                RecordField::SpaceBefore(field, _) | RecordField::SpaceAfter(field, _) => {
                    current = *field;
                }
                _ => break false,
            }
        }
    }

    pub fn to_assigned_field(self, arena: &'a Bump) -> AssignedField<'a, Expr<'a>> {
        use AssignedField::*;

        match self {
            RecordField::RequiredValue(loc_label, spaces, loc_expr) => {
                RequiredValue(loc_label, spaces, loc_expr)
            }

            RecordField::OptionalValue(loc_label, spaces, loc_expr) => {
                OptionalValue(loc_label, spaces, loc_expr)
            }

            RecordField::IgnoredValue(loc_label, spaces, loc_expr) => {
                IgnoredValue(loc_label, spaces, loc_expr)
            }

            RecordField::LabelOnly(loc_label) => LabelOnly(loc_label),

            RecordField::SpaceBefore(field, spaces) => {
                let assigned_field = field.to_assigned_field(arena);

                SpaceBefore(arena.alloc(assigned_field), spaces)
            }

            RecordField::SpaceAfter(field, spaces) => {
                let assigned_field = field.to_assigned_field(arena);

                SpaceAfter(arena.alloc(assigned_field), spaces)
            }
        }
    }
}

impl<'a> Spaceable<'a> for RecordField<'a> {
    fn before(&'a self, spaces: &'a [CommentOrNewline<'a>]) -> Self {
        RecordField::SpaceBefore(self, spaces)
    }
    fn after(&'a self, spaces: &'a [CommentOrNewline<'a>]) -> Self {
        RecordField::SpaceAfter(self, spaces)
    }
}

pub fn parse_record_field<'a>(
    arena: &'a Bump,
    state: State<'a>,
) -> ParseResult<'a, RecordField<'a>, ERecord<'a>> {
    use RecordField::*;

    let start = state.pos();
    match parse_lowercase_ident(state.clone()) {
        Err(NoProgress) => { /* goto below :) */ }
        Err(_) => return Err((MadeProgress, ERecord::Field(start))),
        Ok((label, state)) => {
            let field_label = state.loc(start, label);

            let (_, (label_spaces, _), state) = eat_nc(arena, state, true)?;

            let olds = state.clone();
            match state.bytes().first() {
                Some(b @ (&b':' | &b'?')) => {
                    let (_, (spaces, _), state) = eat_nc(arena, state.inc(), true)?;

                    let val_pos = state.pos();
                    let (val_expr, state) =
                        parse_expr_start(CHECK_FOR_ARROW, None, arena, state, 0).map_err(
                            |(_, fail)| (MadeProgress, ERecord::Expr(arena.alloc(fail), val_pos)),
                        )?;

                    let val_expr = val_expr.spaced_before(arena, spaces);

                    let field = if *b == b':' {
                        RequiredValue(field_label, label_spaces, arena.alloc(val_expr))
                    } else {
                        OptionalValue(field_label, label_spaces, arena.alloc(val_expr))
                    };
                    return Ok((field, state));
                }
                _ => {
                    let field = LabelOnly(field_label).spaced_after(arena, label_spaces);
                    return Ok((field, olds));
                }
            };
        }
    }

    match state.bytes().first() {
        Some(&b'_') => {
            let state = state.inc();
            let name_pos = state.pos();
            let (opt_field_label, state) = match chomp_lowercase_part(state.bytes()) {
                Ok((name, _)) => (name, state.leap_len(name)),
                Err(NoProgress) => ("", state),
                Err(_) => return Err((MadeProgress, ERecord::Field(name_pos))),
            };

            let opt_field_label = state.loc(start, opt_field_label);

            let (_, (label_spaces, _), state) = eat_nc(arena, state, true)?;

            match state.bytes().first() {
                Some(&b':') => {
                    let (_, (colon_spaces, _), state) = eat_nc(arena, state.inc(), true)?;

                    let val_pos = state.pos();
                    let (field_val, state) =
                        parse_expr_start(CHECK_FOR_ARROW, None, arena, state, 0).map_err(
                            |(_, fail)| (MadeProgress, ERecord::Expr(arena.alloc(fail), val_pos)),
                        )?;

                    let field_val = field_val.spaced_before(arena, colon_spaces);
                    let field = IgnoredValue(opt_field_label, label_spaces, arena.alloc(field_val));
                    Ok((field, state))
                }
                _ => Err((MadeProgress, ERecord::Colon(start))),
            }
        }
        _ => Err((NoProgress, ERecord::UnderscoreField(start))),
    }
}

enum RecordHelpPrefix {
    Update,
    Mapper,
}

struct RecordHelp<'a> {
    prefix: Option<(Loc<Expr<'a>>, RecordHelpPrefix)>,
    fields: Collection<'a, Loc<RecordField<'a>>>,
}

fn rest_of_record<'a>(
    arena: &'a Bump,
    state: State<'a>,
) -> ParseResult<'a, RecordHelp<'a>, ERecord<'a>> {
    // You can optionally have an identifier followed by an '&' to
    // make this a record update, e.g. { Foo.user & username: "blah" }.

    // We wrap the ident in an Expr here,
    // so that we have a Spaceable value to work with,
    // and then in canonicalization verify that it's an Expr::Var
    // (and not e.g. an `Expr::Access`) and extract its string.
    let prev = state.clone();
    let (prefix, state) = match eat_nc::<'_, ERecord<'_>>(arena, state, false) {
        Err(_) => (None, prev),
        Ok((_, (spaces_before, _), state)) => {
            let ident_at = state.pos();
            match parse_ident_chain(arena, state) {
                Err(_) => (None, prev),
                Ok((ident, state)) => {
                    let ident = state.loc(ident_at, ident_to_expr(arena, ident, None));
                    match eat_nc::<'_, ERecord<'_>>(arena, state, false) {
                        Err(_) => (None, prev),
                        Ok((_, (spaces_after, _), state)) => {
                            let ident = ident.spaced_around(arena, spaces_before, spaces_after);

                            if state.bytes().first() == Some(&b'&') {
                                (Some((ident, RecordHelpPrefix::Update)), state.inc())
                            } else if state.bytes().starts_with(b"<-") {
                                (Some((ident, RecordHelpPrefix::Mapper)), state.leap(2))
                            } else {
                                (None, prev)
                            }
                        }
                    }
                }
            }
        }
    };

    let elem_p = move |arena: &'a Bump, state: State<'a>| {
        let field_pos = state.pos();
        match parse_record_field(arena, state) {
            Ok((out, state)) => Ok((state.loc(field_pos, out), state)),
            Err(err) => Err(err),
        }
    };
    let (fields, state) = collection_inner(arena, state, elem_p, RecordField::SpaceBefore)?;

    if state.bytes().first() != Some(&b'}') {
        return Err((MadeProgress, ERecord::End(state.pos())));
    }
    let state = state.inc();

    let record = RecordHelp { prefix, fields };
    Ok((record, state))
}

fn rest_of_record_expr<'a>(
    start: Position,
    arena: &'a Bump,
    state: State<'a>,
) -> ParseResult<'a, Loc<Expr<'a>>, EExpr<'a>> {
    let (record, state) =
        rest_of_record(arena, state).map_err(|(p, fail)| (p, EExpr::Record(fail, start)))?;

    // there can be field access, e.g. `{ x : 4 }.x`
    let (suffixes, state) = parse_field_task_result_suffixes(arena, state)?;

    let expr_result = match record.prefix {
        Some((update, RecordHelpPrefix::Update)) => {
            let result = record.fields.map_items_result(arena, |loc_field| {
                match loc_field.value.to_assigned_field(arena) {
                    AssignedField::IgnoredValue(_, _, _) => {
                        Err(EExpr::RecordUpdateIgnoredField(loc_field.region))
                    }
                    builder_field => Ok(Loc {
                        region: loc_field.region,
                        value: builder_field,
                    }),
                }
            });

            let update = &*arena.alloc(update);
            result.map(|fields| Expr::RecordUpdate { update, fields })
        }
        Some((mapper, RecordHelpPrefix::Mapper)) => {
            let result = record.fields.map_items_result(arena, |loc_field| {
                let region = loc_field.region;
                let value = loc_field.value.to_assigned_field(arena);
                Ok(Loc { region, value })
            });

            let mapper = &*arena.alloc(mapper);
            result.map(|fields| Expr::RecordBuilder { mapper, fields })
        }
        None => {
            let special_field_found = record.fields.iter().find_map(|field| {
                if field.value.is_ignored_value() {
                    Some(Err(EExpr::RecordUpdateIgnoredField(field.region)))
                } else {
                    None
                }
            });

            special_field_found.unwrap_or_else(|| {
                let fields = record.fields.map_items(arena, |loc_field| {
                    loc_field.map(|field| field.to_assigned_field(arena))
                });
                Ok(Expr::Record(fields))
            })
        }
    };

    match expr_result {
        Ok(expr) => Ok((
            state.loc(start, apply_access_chain(arena, expr, suffixes)),
            state,
        )),
        Err(fail) => Err((MadeProgress, fail)),
    }
}

fn apply_access_chain<'a>(
    arena: &'a Bump,
    value: Expr<'a>,
    suffixes: Vec<'a, Suffix<'a>>,
) -> Expr<'a> {
    suffixes
        .into_iter()
        .fold(value, |value, suffix| match suffix {
            Suffix::Accessor(Accessor::RecordField(field)) => {
                Expr::RecordAccess(arena.alloc(value), field, None)
            }
            Suffix::Accessor(Accessor::TupleIndex(field)) => {
                Expr::TupleAccess(arena.alloc(value), field, None)
            }
            Suffix::TrySuffix(target) => Expr::TrySuffix {
                target,
                expr: arena.alloc(value),
            },
        })
}

fn literal_to_expr(literal: crate::number_literal::NumLiteral<'_>) -> Expr<'_> {
    use crate::number_literal::NumLiteral::*;
    match literal {
        Num(s) => Expr::Num(s),
        Float(s) => Expr::Float(s),
        NonBase10Int {
            string,
            base,
            is_negative,
        } => Expr::NonBase10Int {
            string,
            base,
            is_negative,
        },
    }
}

fn rest_of_logical_not<'a>(
    start: Position,
    flags: ExprParseFlags,
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
) -> ParseResult<'a, Loc<Expr<'a>>, EExpr<'a>> {
    let after_op = state.pos();
    let (_, spaces_before, state) =
        eat_nc_check(EExpr::IndentStart, arena, state, min_indent, true)?;

    match parse_term(PARSE_DEFAULT, flags, arena, state, min_indent) {
        Ok((val, state)) => {
            let val = val.spaced_before(arena, spaces_before);
            let op = Loc::pos(start, after_op, UnaryOp::Not);
            Ok((state.loc(start, Expr::UnaryOp(arena.alloc(val), op)), state))
        }
        Err((_, fail)) => Err((MadeProgress, fail)),
    }
}

const BINOP_CHAR_SET: &[u8] = b"+-/*=.<>:&|^?%!~";

const BINOP_CHAR_MASK: u128 = {
    let mut result = 0u128;
    let mut i = 0;
    while i < BINOP_CHAR_SET.len() {
        let index = BINOP_CHAR_SET[i] as usize;
        result |= 1 << index;
        i += 1;
    }
    result
};

#[inline(always)]
fn is_binop_char(ch: &u8) -> bool {
    *ch < 127 && (BINOP_CHAR_MASK & (1 << *ch) != 0)
}

const SPECIAL_CHAR_SET: &[u8] = b" #\n\r\t,()[]{}\"'/\\+*%^&|<>=!~`;:?.";

const SPECIAL_CHAR_MASK: u128 = {
    let mut result = 0u128;
    let mut i = 0;
    while i < SPECIAL_CHAR_SET.len() {
        let index = SPECIAL_CHAR_SET[i] as usize;
        result |= 1 << index;
        i += 1;
    }
    result
};

#[inline(always)]
pub(crate) fn is_special_char(ch: &u8) -> bool {
    *ch < 127 && (SPECIAL_CHAR_MASK & (1 << *ch) != 0)
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum OperatorOrDef {
    BinOp(BinOp),
    Assignment,
    AliasOrOpaque(AliasOrOpaque),
    Backpassing,
}

fn parse_bin_op(state: State<'_>) -> ParseResult<BinOp, EExpr<'_>> {
    let bytes: &[u8] = state.bytes();

    let mut chomped = 0;
    for ch in bytes.iter() {
        if !is_binop_char(ch) {
            break;
        }
        chomped += 1;
    }

    if chomped == 0 {
        return Err((NoProgress, EExpr::Start(state.pos())));
    }

    // Safe because BINOP_CHAR_SET only contains ascii chars
    let op = unsafe { std::str::from_utf8_unchecked(&bytes[..chomped]) };
    match op {
        "+" => Ok((BinOp::Plus, state.inc())),
        "-" => Ok((BinOp::Minus, state.inc())),
        "*" => Ok((BinOp::Star, state.inc())),
        "/" => Ok((BinOp::Slash, state.inc())),
        "%" => Ok((BinOp::Percent, state.inc())),
        "^" => Ok((BinOp::Caret, state.inc())),
        ">" => Ok((BinOp::GreaterThan, state.inc())),
        "<" => Ok((BinOp::LessThan, state.inc())),
        "~" => Ok((BinOp::When, state.inc())),
        "|>" => Ok((BinOp::Pizza, state.leap(2))),
        "==" => Ok((BinOp::Equals, state.leap(2))),
        "!=" => Ok((BinOp::NotEquals, state.leap(2))),
        ">=" => Ok((BinOp::GreaterThanOrEq, state.leap(2))),
        "<=" => Ok((BinOp::LessThanOrEq, state.leap(2))),
        "&&" => Ok((BinOp::And, state.leap(2))),
        "||" => Ok((BinOp::Or, state.leap(2))),
        "//" => Ok((BinOp::DoubleSlash, state.leap(2))),

        // a `.` makes no progress, so it does not interfere with `.foo` access(or)
        "." => Err((NoProgress, EExpr::BadOperator(".", state.pos()))),
        "!" => Err((NoProgress, EExpr::BadOperator("!", state.pos()))),
        // makes no progress, so it does not interfere with `_ if isGood -> ...`
        "->" => Err((NoProgress, EExpr::BadOperator("->", state.pos()))),

        _ => Err((MadeProgress, EExpr::BadOperator(op, state.pos()))),
    }
}

fn parse_op(state: State<'_>) -> ParseResult<OperatorOrDef, EExpr<'_>> {
    match parse_bin_op(state.clone()) {
        Ok((op, state)) => Ok((OperatorOrDef::BinOp(op), state)),
        Err((MadeProgress, EExpr::BadOperator(op, pos))) => match op {
            "=" => Ok((OperatorOrDef::Assignment, state.inc())),
            ":" => Ok((
                OperatorOrDef::AliasOrOpaque(AliasOrOpaque::Alias),
                state.inc(),
            )),
            ":=" => Ok((
                OperatorOrDef::AliasOrOpaque(AliasOrOpaque::Opaque),
                state.leap(2),
            )),
            "<-" => Ok((OperatorOrDef::Backpassing, state.leap(2))),
            _ => Err((MadeProgress, EExpr::BadOperator(op, pos))),
        },
        Err(err) => Err(err),
    }
}
