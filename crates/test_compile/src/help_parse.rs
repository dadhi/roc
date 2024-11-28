use bumpalo::Bump;
use roc_parse::{
    ast,
    blankspace::{eat_nc_check, eat_nc_or_empty, SpacedBuilder},
    expr::{parse_expr_block, ACCEPT_MULTI_BACKPASSING, CHECK_FOR_ARROW},
    parser::{EExpr, SourceError, SyntaxError},
    state::State,
};
use roc_region::all::{Loc, Position};

use crate::deindent::trim_and_deindent;

pub struct ParseExpr {
    arena: Bump,
}

impl Default for ParseExpr {
    fn default() -> Self {
        Self {
            arena: Bump::with_capacity(4096),
        }
    }
}

impl ParseExpr {
    pub fn parse_expr<'a>(&'a self, input: &'a str) -> Result<ast::Expr<'a>, SyntaxError<'a>> {
        self.parse_loc_expr(input)
            .map(|loc_expr| loc_expr.value)
            .map_err(|e| e.problem)
    }

    pub fn parse_loc_expr<'a>(
        &'a self,
        input: &'a str,
    ) -> Result<Loc<ast::Expr<'a>>, SourceError<'a, SyntaxError<'a>>> {
        let original_bytes = trim_and_deindent(&self.arena, input).as_bytes();
        let state = State::new(original_bytes);

        let arena = &self.arena;
        let out = match eat_nc_check(EExpr::IndentStart, arena, state, 0, false) {
            Err((_, fail)) => Err(fail),
            Ok((_, spaces_before, state)) => {
                match parse_expr_block(CHECK_FOR_ARROW | ACCEPT_MULTI_BACKPASSING, arena, state) {
                    Err((_, fail)) => Err(fail),
                    Ok((expr, state)) => {
                        let (spaces_after, _) = eat_nc_or_empty(arena, state, 0);
                        let expr = expr.spaced_around(arena, spaces_before, spaces_after);
                        Ok(expr)
                    }
                }
            }
        };

        out.map_err(|fail| SourceError {
            problem: SyntaxError::Expr(fail, Position::default()),
            bytes: original_bytes,
        })
    }

    pub fn into_arena(self) -> Bump {
        self.arena
    }

    pub fn arena(&self) -> &Bump {
        &self.arena
    }
}
