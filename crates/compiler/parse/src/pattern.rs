use crate::ast::{Collection, Pattern, PatternAs};
use crate::blankspace::{eat_nc, eat_nc_check, SpacedBuilder};
use crate::expr::{parse_expr_start, CHECK_FOR_ARROW};
use crate::ident::{chomp_lowercase_part, parse_ident_chain, parse_lowercase_ident, Ident};
use crate::keyword;
use crate::number_literal::parse_number_base;
use crate::parser::{
    at_keyword,
    Progress::{self, *},
};
use crate::parser::{collection_inner, EPattern, PInParens, PList, PRecord, ParseResult, Parser};
use crate::state::State;
use crate::string_literal::{rest_of_str_like, StrLikeLiteral};
use bumpalo::collections::string::String;
use bumpalo::collections::Vec;
use bumpalo::Bump;
use roc_region::all::{Loc, Position, Region};

/// Different patterns are supported in different circumstances.
/// For example, when branches can pattern match on number literals, but
/// assignments and function args can't. Underscore is supported in function
/// arg patterns and in when branch patterns, but not in assignments.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PatternType {
    TopLevelDef,
    DefExpr,
    FunctionArg,
    WhenBranch,
    ModuleParams,
}

pub fn parse_closure_param<'a>(
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
) -> Result<(Loc<Pattern<'a>>, State<'a>), (Progress, EPattern<'a>)> {
    if let Some(b) = state.bytes().first() {
        let start = state.pos();
        match b {
            // Underscore is also common, e.g. \_ -> ...
            b'_' => rest_of_underscore_pattern(start, state.inc()),
            // You can destructure records in params, e.g. \{ x, y } -> ...
            b'{' => rest_of_record_pattern(start, arena, state.inc()),
            // If you wrap it in parens, you can match any arbitrary pattern at all. But what about the list pattern?
            // e.g. \(User.UserId userId) -> ...
            b'(' => rest_of_pattern_in_parens(start, arena, state.inc()),
            // todo: @ask why not parse the list pattern here?
            b'[' => Err((NoProgress, EPattern::Start(state.pos()))),
            _ => parse_ident_pattern(start, true, arena, state, min_indent),
        }
    } else {
        Err((NoProgress, EPattern::Start(state.pos())))
    }
}

pub fn parse_pattern<'a>(
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
) -> Result<(Loc<Pattern<'a>>, State<'a>), (Progress, EPattern<'a>)> {
    let (pattern, state) = parse_loc_pattern_etc(true, arena, state, min_indent)?;

    let pattern_state = state.clone();
    let (_, pattern_spaces, state) =
        match eat_nc_check(EPattern::AsKeyword, arena, state, min_indent, false) {
            Ok(ok) => ok,
            Err(_) => return Ok((pattern, pattern_state)),
        };

    match parse_pattern_as(arena, state, min_indent) {
        Err((MadeProgress, e)) => Err((MadeProgress, e)),
        Err(_) => Ok((pattern, pattern_state)),
        Ok((pattern_as, state)) => {
            let region = Region::span_across(&pattern.region, &pattern_as.identifier.region);

            let pattern = pattern.spaced_after(arena, pattern_spaces);
            let as_pattern = Pattern::As(arena.alloc(pattern), pattern_as);

            Ok((Loc::at(region, as_pattern), state))
        }
    }
}

fn parse_loc_pattern_etc<'a>(
    can_have_arguments: bool,
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
) -> Result<(Loc<Pattern<'a>>, State<'a>), (Progress, EPattern<'a>)> {
    if let Some(b) = state.bytes().first() {
        let start = state.pos();
        match b {
            b'_' => rest_of_underscore_pattern(start, state.inc()),
            b'{' => rest_of_record_pattern(start, arena, state.inc()),
            b'(' => rest_of_pattern_in_parens(start, arena, state.inc()),
            b'[' => rest_of_list_pattern(start, arena, state.inc()),
            b'"' | b'\'' => {
                let column = state.column();
                match rest_of_str_like(*b == b'\'', column, arena, state.inc(), min_indent) {
                    Ok((_, literal, state)) => {
                        let literal = match literal {
                            StrLikeLiteral::Str(s) => Pattern::StrLiteral(s),
                            StrLikeLiteral::SingleQuote(s) => {
                                // TODO: preserve the original escaping
                                Pattern::SingleQuote(s.to_str_in(arena))
                            }
                        };
                        Ok((state.loc(start, literal), state))
                    }
                    Err((p, _)) => Err((p, EPattern::Start(start))),
                }
            }
            b'0'..=b'9' => match parse_number_base(false, state.bytes(), state) {
                Ok((_, literal, state)) => {
                    Ok((state.loc(start, literal_to_pattern(literal)), state))
                }
                Err((p, fail)) => Err((p, EPattern::NumLiteral(fail, start))),
            },
            b'-' => match parse_number_base(true, &state.bytes()[1..], state) {
                Ok((_, literal, state)) => {
                    Ok((state.loc(start, literal_to_pattern(literal)), state))
                }
                Err((NoProgress, _)) => Err((NoProgress, EPattern::Start(start))),
                Err((p, fail)) => Err((p, EPattern::NumLiteral(fail, start))),
            },
            _ => parse_ident_pattern(start, can_have_arguments, arena, state, min_indent),
        }
    } else {
        Err((NoProgress, EPattern::Start(state.pos())))
    }
}

fn parse_pattern_as<'a>(
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
) -> Result<(PatternAs<'a>, State<'a>), (Progress, EPattern<'a>)> {
    if !at_keyword(keyword::AS, &state) {
        return Err((NoProgress, EPattern::AsKeyword(state.pos())));
    }
    let state = state.inc_len(keyword::AS);

    let (_, spaces_before, state) =
        eat_nc_check(EPattern::AsIdentifier, arena, state, min_indent, false)?;

    let pos = state.pos();
    match parse_lowercase_ident(state) {
        Ok((ident, state)) => {
            let pattern = PatternAs {
                spaces_before,
                identifier: state.loc(pos, ident),
            };
            Ok((pattern, state))
        }
        Err(_) => Err((MadeProgress, EPattern::AsIdentifier(pos))),
    }
}

// Don't parse operators, because they have a higher precedence than function application.
// If we encounter one, we're done parsing function args!
fn type_tag_or_def_tag_pattern_args<'a>(
    stop_on_has_kw: bool,
    arena: &'a Bump,
    mut state: State<'a>,
    min_indent: u32,
) -> ParseResult<'a, Vec<'a, Loc<Pattern<'a>>>, EPattern<'a>> {
    let mut patterns = Vec::with_capacity_in(1, arena);
    loop {
        let prev = state.clone();

        let (_, spaces, next) =
            match eat_nc_check(EPattern::IndentStart, arena, state, min_indent, false) {
                Ok(ok) => ok,
                Err(_) => break Ok((Progress::when(!patterns.is_empty()), patterns, prev)),
            };

        // Cannot have arguments here, pass `false` to make sure `Foo Bar 1` is parsed as `Foo (Bar) 1`, and not `Foo (Bar 1)`
        let (Loc { region, mut value }, next) =
            match parse_loc_pattern_etc(false, arena, next, min_indent) {
                Ok(ok) => ok,
                Err((NoProgress, _)) => {
                    break Ok((Progress::when(!patterns.is_empty()), patterns, prev))
                }
                Err(err) => break Err(err),
            };

        if stop_on_has_kw
            && matches!(
                value,
                Pattern::Identifier {
                    ident: crate::keyword::IMPLEMENTS,
                    ..
                }
            )
        {
            break Ok((Progress::when(!patterns.is_empty()), patterns, prev));
        }

        if !spaces.is_empty() {
            value = Pattern::SpaceBefore(arena.alloc(value), spaces);
        }
        state = next;
        patterns.push(Loc::at(region, value));
    }
}

fn rest_of_pattern_in_parens<'a>(
    start: Position,
    arena: &'a Bump,
    state: State<'a>,
) -> Result<(Loc<Pattern<'a>>, State<'a>), (Progress, EPattern<'a>)> {
    let elem_p = move |a: &'a Bump, state: State<'a>, min_indent: u32| {
        let pos = state.pos();
        match parse_pattern(a, state, min_indent) {
            Ok((out, state)) => Ok((MadeProgress, out, state)),
            Err((p, fail)) => Err((p, PInParens::Pattern(a.alloc(fail), pos))),
        }
    };

    let (_, pats, state) =
        match collection_inner(elem_p, Pattern::SpaceBefore).parse(arena, state, 0) {
            Ok(ok) => ok,
            Err((_, fail)) => return Err((MadeProgress, EPattern::PInParens(fail, start))),
        };

    if state.bytes().first() != Some(&b')') {
        let fail = PInParens::End(state.pos());
        return Err((MadeProgress, EPattern::PInParens(fail, start)));
    }
    let state = state.inc();

    if pats.is_empty() {
        let fail = PInParens::Empty(state.pos());
        return Err((NoProgress, EPattern::PInParens(fail, start)));
    }

    let pats = if pats.len() > 1 {
        state.loc(start, Pattern::Tuple(pats))
    } else {
        // TODO: don't discard comments before/after (stored in the Collection)
        // TODO: add Pattern::ParensAround to faithfully represent the input, see the `parse_expr_in_parens_etc`
        pats.items[0]
    };
    Ok((pats, state))
}

fn literal_to_pattern(literal: crate::number_literal::NumLiteral<'_>) -> Pattern<'_> {
    use crate::number_literal::NumLiteral::*;
    match literal {
        Num(s) => Pattern::NumLiteral(s),
        Float(s) => Pattern::FloatLiteral(s),
        NonBase10Int {
            string,
            base,
            is_negative,
        } => Pattern::NonBase10Literal {
            string,
            base,
            is_negative,
        },
    }
}

fn rest_of_list_pattern<'a>(
    start: Position,
    arena: &'a Bump,
    state: State<'a>,
) -> Result<(Loc<Pattern<'a>>, State<'a>), (Progress, EPattern<'a>)> {
    let (_, elems, state) =
        match collection_inner(list_element_pattern, Pattern::SpaceBefore).parse(arena, state, 0) {
            Ok(ok) => ok,
            Err((_, fail)) => return Err((MadeProgress, EPattern::List(fail, start))),
        };

    if state.bytes().first() != Some(&b']') {
        let fail = PList::End(state.pos());
        return Err((MadeProgress, EPattern::List(fail, start)));
    }
    let state = state.inc();
    Ok((state.loc(start, Pattern::List(elems)), state))
}

fn list_element_pattern<'a>(
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
) -> ParseResult<'a, Loc<Pattern<'a>>, PList<'a>> {
    let start = state.pos();
    if state.bytes().starts_with(b"...") {
        return Err((MadeProgress, PList::Rest(start)));
    }

    match parse_list_rest_pattern(start, arena, state.clone(), min_indent) {
        Err((NoProgress, _)) => {}
        res => return res,
    }

    match parse_pattern(arena, state, min_indent) {
        Ok((out, state)) => Ok((MadeProgress, out, state)),
        Err((p, fail)) => Err((p, PList::Pattern(arena.alloc(fail), start))),
    }
}

fn parse_list_rest_pattern<'a>(
    start: Position,
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
) -> ParseResult<'a, Loc<Pattern<'a>>, PList<'a>> {
    if !state.bytes().starts_with(b"..") {
        return Err((NoProgress, PList::Open(start)));
    }
    let state = state.advance(2);
    let dots_at = Region::new(start, state.pos());

    let no_as = Loc::at(dots_at, Pattern::ListRest(None));

    let pattern_state = state.clone();
    let (pattern_spaces, state) =
        match eat_nc_check(EPattern::AsKeyword, arena, state, min_indent, false) {
            Ok((_, pattern_spaces, state)) => (pattern_spaces, state),
            Err(_) => return Ok((MadeProgress, no_as, pattern_state)),
        };

    let position = state.pos();
    match parse_pattern_as(arena, state, min_indent) {
        Err((MadeProgress, e)) => Err((MadeProgress, PList::Pattern(arena.alloc(e), position))),
        Err(_) => Ok((MadeProgress, no_as, pattern_state)),
        Ok((pattern_as, state)) => {
            let region = Region::span_across(&dots_at, &pattern_as.identifier.region);

            let as_pattern = Pattern::ListRest(Some((pattern_spaces, pattern_as)));
            Ok((MadeProgress, Loc::at(region, as_pattern), state))
        }
    }
}

fn parse_ident_pattern<'a>(
    start: Position,
    can_have_arguments: bool,
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
) -> Result<(Loc<Pattern<'a>>, State<'a>), (Progress, EPattern<'a>)> {
    let (ident, state) = match parse_ident_chain(arena, state) {
        Ok(ok) => ok,
        Err((p, _)) => return Err((p, EPattern::Start(start))),
    };

    let ident_loc = Region::new(start, state.pos());
    match ident {
        Ident::Tag(tag) => {
            let loc_tag = Loc::at(ident_loc, Pattern::Tag(tag));

            // Make sure `Foo Bar 1` is parsed as `Foo (Bar) 1`, and not `Foo (Bar 1)`
            if can_have_arguments {
                let (_, loc_args, state) =
                    type_tag_or_def_tag_pattern_args(true, arena, state, min_indent)?;

                if loc_args.is_empty() {
                    Ok((loc_tag, state))
                } else {
                    let region = Region::across_all(
                        std::iter::once(&ident_loc)
                            .chain(loc_args.iter().map(|loc_arg| &loc_arg.region)),
                    );
                    let value = Pattern::Apply(&*arena.alloc(loc_tag), loc_args.into_bump_slice());
                    Ok((Loc { region, value }, state))
                }
            } else {
                Ok((loc_tag, state))
            }
        }
        Ident::OpaqueRef(name) => {
            let loc_pat = Loc::at(ident_loc, Pattern::OpaqueRef(name));

            // Make sure `@Foo Bar 1` is parsed as `@Foo (Bar) 1`, and not `@Foo (Bar 1)`
            if can_have_arguments {
                let (_, loc_args, state) =
                    type_tag_or_def_tag_pattern_args(false, arena, state, min_indent)?;

                if loc_args.is_empty() {
                    Ok((loc_pat, state))
                } else {
                    let region = Region::across_all(
                        std::iter::once(&ident_loc)
                            .chain(loc_args.iter().map(|loc_arg| &loc_arg.region)),
                    );
                    let value = Pattern::Apply(&*arena.alloc(loc_pat), loc_args.into_bump_slice());
                    Ok((Loc { region, value }, state))
                }
            } else {
                Ok((loc_pat, state))
            }
        }
        Ident::Plain(ident) => {
            let ident = Loc::at(ident_loc, Pattern::Identifier { ident });
            Ok((ident, state))
        }
        Ident::Access { module_name, parts } => {
            // Plain identifiers (e.g. `foo`) are allowed in patterns, but
            // more complex ones (e.g. `Foo.bar` or `foo.bar.baz`) are not.
            let mut malformed_str = String::new_in(arena);
            if !module_name.is_empty() {
                malformed_str.push_str(module_name);
            };
            for part in parts {
                if !malformed_str.is_empty() {
                    malformed_str.push('.');
                }
                malformed_str.push_str(part.as_inner());
            }

            let bad_ident = Loc::at(ident_loc, Pattern::Malformed(malformed_str.into_bump_str()));
            Ok((bad_ident, state))
        }
        Ident::AccessorFunction(_) => Err((MadeProgress, EPattern::AccessorFunction(start))),
        Ident::RecordUpdaterFunction(_) => {
            Err((MadeProgress, EPattern::RecordUpdaterFunction(start)))
        }
        Ident::Malformed(malformed, problem) => {
            debug_assert!(!malformed.is_empty());
            let loc = Loc::at(ident_loc, Pattern::MalformedIdent(malformed, problem));
            Ok((loc, state))
        }
    }
}

fn rest_of_underscore_pattern(
    start: Position,
    state: State<'_>,
) -> Result<(Loc<Pattern<'_>>, State<'_>), (Progress, EPattern<'_>)> {
    let (name, state) = match chomp_lowercase_part(state.bytes()) {
        Ok((name, _)) => (name, state.advance(name.len())),
        Err(NoProgress) => ("", state),
        Err(_) => return Err((MadeProgress, EPattern::End(state.pos()))),
    };
    let pattern = state.loc(start, Pattern::Underscore(name));
    Ok((pattern, state))
}

fn rest_of_record_pattern<'a>(
    start: Position,
    arena: &'a Bump,
    state: State<'a>,
) -> Result<(Loc<Pattern<'a>>, State<'a>), (Progress, EPattern<'a>)> {
    let (_, fields, state) =
        match collection_inner(parse_record_pattern_field, Pattern::SpaceBefore)
            .parse(arena, state, 0)
        {
            Ok(ok) => ok,
            Err((_, fail)) => return Err((MadeProgress, EPattern::Record(fail, start))),
        };

    if state.bytes().first() != Some(&b'}') {
        let fail = PRecord::End(state.pos());
        return Err((MadeProgress, EPattern::Record(fail, start)));
    }
    let state = state.inc();

    let pattern = Pattern::RecordDestructure(fields);
    Ok((state.loc(start, pattern), state))
}

pub fn parse_record_pattern_fields<'a>(
    arena: &'a Bump,
    state: State<'a>,
) -> ParseResult<'a, Collection<'a, Loc<Pattern<'a>>>, PRecord<'a>> {
    if state.bytes().first() != Some(&b'{') {
        return Err((NoProgress, PRecord::Open(state.pos())));
    }
    let state = state.inc();

    let (_, out, state) = match collection_inner(parse_record_pattern_field, Pattern::SpaceBefore)
        .parse(arena, state, 0)
    {
        Ok(ok) => ok,
        Err((_, fail)) => return Err((MadeProgress, fail)),
    };

    if state.bytes().first() != Some(&b'}') {
        return Err((MadeProgress, PRecord::End(state.pos())));
    }

    Ok((MadeProgress, out, state.inc()))
}

fn parse_record_pattern_field<'a>(
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
) -> ParseResult<'a, Loc<Pattern<'a>>, PRecord<'a>> {
    // You must have a field name, e.g. "email"
    // using the initial pos is important for error reporting
    let start = state.pos();
    let (label, state) = parse_lowercase_ident(state).map_err(|p| (p, PRecord::Field(start)))?;
    let label_at = Region::new(start, state.pos());

    let (_, (label_spaces, _), state) = eat_nc(arena, state, true)?;

    // Having a value is optional; both `{ email }` and `{ email: blah }` work.
    // (This is true in both literals and types.)
    if state.bytes().first() == Some(&b':') {
        let state = state.inc();

        let (_, (colon_spaces, _), state) = eat_nc(arena, state, true)?;

        let pattern_pos = state.pos();
        let (pattern_val, state) = match parse_pattern(arena, state, min_indent) {
            Ok(ok) => ok,
            Err((_, fail)) => {
                let fail = PRecord::Pattern(arena.alloc(fail), pattern_pos);
                return Err((MadeProgress, fail));
            }
        };

        let pattern_val = pattern_val.spaced_before(arena, colon_spaces);
        let region = Region::span_across(&label_at, &pattern_val.region);

        // TODO spaces are dropped here
        // arena.alloc(arena.alloc(value).spaced_before(spaces, region)),
        let req_field = Pattern::RequiredField(label, arena.alloc(pattern_val));
        return Ok((MadeProgress, Loc::at(region, req_field), state));
    }

    if state.bytes().first() == Some(&b'?') {
        let state = state.inc();

        let (_, (question_spaces, _), state) = eat_nc(arena, state, true)?;

        let optional_val_pos = state.pos();
        let (optional_val, state) =
            match parse_expr_start(CHECK_FOR_ARROW, None, arena, state, min_indent) {
                Ok(ok) => ok,
                Err((_, fail)) => {
                    let fail = PRecord::Expr(arena.alloc(fail), optional_val_pos);
                    return Err((MadeProgress, fail));
                }
            };

        let optional_val = optional_val.spaced_before(arena, question_spaces);
        let region = Region::span_across(&label_at, &optional_val.region);

        // TODO spaces are dropped
        // arena.alloc(arena.alloc(value).spaced_before(spaces, region)),
        let opt_field = Pattern::OptionalField(label, arena.alloc(optional_val));
        return Ok((MadeProgress, Loc::at(region, opt_field), state));
    }

    let value = if !label_spaces.is_empty() {
        Pattern::SpaceAfter(
            arena.alloc(Pattern::Identifier { ident: label }),
            label_spaces,
        )
    } else {
        Pattern::Identifier { ident: label }
    };

    Ok((MadeProgress, Loc::at(label_at, value), state))
}
