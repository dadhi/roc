use crate::ast::CommentOrNewline;
use crate::ast::Spaceable;
use crate::parser::ParseResult;
use crate::parser::Progress;
use crate::parser::SpaceProblem;
use crate::parser::{BadInputError, Parser, Progress::*};
use crate::state::State;
use bumpalo::collections::vec::Vec;
use bumpalo::Bump;
use roc_region::all::Loc;
use roc_region::all::Position;
use roc_region::all::Region;

pub trait SpacedBuilder<'a, T: 'a + Spaceable<'a>> {
    fn spaced_before(self, arena: &'a Bump, spaces: &'a [CommentOrNewline]) -> Self;

    fn spaced_after(self, arena: &'a Bump, spaces: &'a [CommentOrNewline]) -> Self;

    #[inline(always)]
    fn spaced_around(
        self,
        arena: &'a Bump,
        spaces_before: &'a [CommentOrNewline<'a>],
        spaces_after: &'a [CommentOrNewline<'a>],
    ) -> Self
    where
        Self: Sized,
    {
        self.spaced_after(arena, spaces_after)
            .spaced_before(arena, spaces_before)
    }
}

impl<'a, T> SpacedBuilder<'a, T> for Loc<T>
where
    T: 'a + Spaceable<'a>,
{
    #[inline(always)]
    fn spaced_before(self, arena: &'a Bump, spaces: &'a [CommentOrNewline]) -> Self {
        if spaces.is_empty() {
            self
        } else {
            Loc {
                region: self.region,
                value: arena.alloc(self.value).before(spaces),
            }
        }
    }

    #[inline(always)]
    fn spaced_after(self, arena: &'a Bump, spaces: &'a [CommentOrNewline]) -> Self {
        if spaces.is_empty() {
            self
        } else {
            Loc {
                region: self.region,
                value: arena.alloc(self.value).after(spaces),
            }
        }
    }
}

pub fn simple_eat_whitespace(bytes: &[u8]) -> usize {
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b' ' => i += 1,
            _ => break,
        }
    }
    i
}

pub fn fast_eat_whitespace(bytes: &[u8]) -> usize {
    // Load 8 bytes at a time, keeping in mind that the initial offset may not be aligned
    let mut i = 0;
    while i + 8 <= bytes.len() {
        let chunk = unsafe {
            // Safe because we know the pointer is in bounds
            (bytes.as_ptr().add(i) as *const u64)
                .read_unaligned()
                .to_le()
        };

        // Space character is 0x20, which has a single bit set
        // We can check for any space character by checking if any other bit is set
        let spaces = 0x2020_2020_2020_2020;

        // First, generate a mask where each byte is 0xff if the byte is a space,
        // and some other bit sequence otherwise
        let mask = !(chunk ^ spaces);

        // Now mask off the high bit, so there's some place to carry into without
        // overflowing into the next byte.
        let mask = mask & !0x8080_8080_8080_8080;

        // Now add 0x0101_0101_0101_0101 to each byte, which will carry into the high bit
        // if and only if the byte is a space.
        let mask = mask + 0x0101_0101_0101_0101;

        // Now mask off areas where the original bytes had the high bit set, so that
        // 0x80|0x20 = 0xa0 will not be considered a space.
        let mask = mask & !(chunk & 0x8080_8080_8080_8080);

        // Make sure all the _other_ bits aside from the high bit are set,
        // and count the number of trailing one bits, dividing by 8 to get the number of
        // bytes that are spaces.
        let count = ((mask | !0x8080_8080_8080_8080).trailing_ones() as usize) / 8;

        if count == 8 {
            i += 8;
        } else {
            return i + count;
        }
    }

    // Check the remaining bytes
    simple_eat_whitespace(&bytes[i..]) + i
}

pub fn simple_eat_until_control_character(bytes: &[u8]) -> usize {
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] < b' ' {
            break;
        } else {
            i += 1;
        }
    }
    i
}

pub fn fast_eat_until_control_character(bytes: &[u8]) -> usize {
    // Load 8 bytes at a time, keeping in mind that the initial offset may not be aligned
    let mut i = 0;
    while i + 8 <= bytes.len() {
        let chunk = unsafe {
            // Safe because we know the pointer is in bounds
            (bytes.as_ptr().add(i) as *const u64)
                .read_unaligned()
                .to_le()
        };

        // Control characters are 0x00-0x1F, and don't have any high bits set.
        // They only have bits set that fall under the 0x1F mask.
        let control = 0x1F1F_1F1F_1F1F_1F1F;

        // First we set up a value where, if a given byte is a control character,
        // it'll have a all the non-control bits set to 1. All control bits are set to zero.
        let mask = !(chunk & !control) & !control;

        // Now, down shift by one bit. This will leave room for the following add to
        // carry, without impacting the next byte.
        let mask = mask >> 1;

        // Add one (shifted by the right amount), causing all the one bits in the control
        // characters to cascade, and put a one in the high bit.
        let mask = mask.wrapping_add(0x1010_1010_1010_1010);

        // Now, we can count the number of trailing zero bits, dividing by 8 to get the
        // number of bytes before the first control character.
        let count = (mask & 0x8080_8080_8080_8080).trailing_zeros() as usize / 8;

        if count == 8 {
            i += 8;
        } else {
            return i + count;
        }
    }

    // Check the remaining bytes
    simple_eat_until_control_character(&bytes[i..]) + i
}

/// Eat NewLines and Comments with ident check
pub fn eat_nc_check<'a, E>(
    indent_problem: fn(Position) -> E,
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
    err_made_progress: bool,
) -> ParseResult<'a, &'a [CommentOrNewline<'a>], E>
where
    E: 'a + SpaceProblem,
{
    let start = state.pos();
    let (ok_pr, (sp, _), state) = eat_nc(arena, state, err_made_progress)?;
    if !sp.is_empty() && state.column() < min_indent {
        return Err((ok_pr, indent_problem(start)));
    }
    Ok((ok_pr, sp, state))
}

pub fn space0_e<'a, E>(
    indent_problem: fn(Position) -> E,
) -> impl Parser<'a, &'a [CommentOrNewline<'a>], E>
where
    E: 'a + SpaceProblem,
{
    move |arena, state: State<'a>, min_indent: u32| {
        eat_nc_check(indent_problem, arena, state, min_indent, false)
    }
}

pub fn eat_nc_loc_c<'a, E>(
    indent_problem: fn(Position) -> E,
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
    err_made_progress: bool,
) -> Result<(Loc<&'a [CommentOrNewline<'a>]>, State<'a>), (Progress, E)>
where
    E: 'a + SpaceProblem,
{
    let start = state.pos();
    let (ok_pr, (sp, comments_at), state) = eat_nc(arena, state, err_made_progress)?;
    if !sp.is_empty() && state.column() < min_indent {
        return Err((ok_pr, indent_problem(start)));
    }
    Ok((Loc::at(comments_at, sp), state))
}

fn begins_with_crlf(bytes: &[u8]) -> bool {
    bytes.len() >= 2 && bytes[0] == b'\r' && bytes[1] == b'\n'
}

// note: @dup of the eat_nc_locs
#[allow(clippy::type_complexity)]
pub fn eat_nc<'a, E>(
    arena: &'a Bump,
    mut state: State<'a>,
    err_made_progress: bool,
) -> Result<(Progress, (&'a [CommentOrNewline<'a>], Region), State<'a>), (Progress, E)>
where
    E: 'a + SpaceProblem,
{
    let mut nc = Vec::new_in(arena);
    let mut p = NoProgress;
    let mut found_newline = state.is_at_start_of_file();
    let mut comments_at = None;
    loop {
        let whitespace = fast_eat_whitespace(state.bytes());
        if whitespace > 0 {
            state.advance_mut(whitespace);
            p = MadeProgress;
        }

        let start = state.pos();
        match state.bytes().first() {
            Some(b'#') => {
                state.inc_mut();

                let is_doc_comment =
                    state.bytes().first() == Some(&b'#') && state.bytes().get(1) != Some(&b'#');

                if is_doc_comment {
                    state.inc_mut();
                    if state.bytes().first() == Some(&b' ') {
                        state.inc_mut();
                    }
                }

                let len = fast_eat_until_control_character(state.bytes());

                // We already checked that the string is valid UTF-8
                debug_assert!(std::str::from_utf8(&state.bytes()[..len]).is_ok());
                let text = unsafe { std::str::from_utf8_unchecked(&state.bytes()[..len]) };

                let comment = if is_doc_comment {
                    CommentOrNewline::DocComment(text)
                } else {
                    CommentOrNewline::LineComment(text)
                };
                state.advance_mut(len);
                nc.push(comment);
                found_newline = true;

                comments_at = match comments_at {
                    None => Some(Region::new(start, state.pos())),
                    Some(r) => Some(Region::new(r.start(), state.pos())),
                };

                if begins_with_crlf(state.bytes()) {
                    state = state.advance_newline(2);
                } else if state.bytes().first() == Some(&b'\n') {
                    state = state.advance_newline(1);
                }

                p = MadeProgress;
            }
            Some(b'\r') => {
                if state.bytes().get(1) != Some(&b'\n') {
                    return Err((
                        if err_made_progress { MadeProgress } else { p },
                        E::space_problem(BadInputError::HasMisplacedCarriageReturn, state.pos()),
                    ));
                }
                state = state.advance_newline(2);
                nc.push(CommentOrNewline::Newline);
                found_newline = true;
                p = MadeProgress;
            }
            Some(b'\n') => {
                state = state.advance_newline(1);
                nc.push(CommentOrNewline::Newline);
                found_newline = true;
                p = MadeProgress;
            }
            Some(b'\t') => {
                return Err((
                    if err_made_progress { MadeProgress } else { p },
                    E::space_problem(BadInputError::HasTab, state.pos()),
                ));
            }
            Some(x) if *x < b' ' => {
                return Err((
                    if err_made_progress { MadeProgress } else { p },
                    E::space_problem(BadInputError::HasAsciiControl, state.pos()),
                ));
            }
            _ => {
                if found_newline {
                    state = state.mark_current_indent();
                }
                break;
            }
        }
    }

    let comments_at = comments_at.unwrap_or(Region::point(state.pos()));
    Ok((p, (nc.into_bump_slice(), comments_at), state))
}

#[inline(always)]
pub fn eat_nc_ok<'a, E>(
    indent_problem: fn(Position) -> E,
    arena: &'a Bump,
    state: State<'a>,
    min_indent: u32,
) -> (&'a [CommentOrNewline<'a>], State<'a>)
where
    E: 'a + SpaceProblem,
{
    match eat_nc_check(indent_problem, arena, state.clone(), min_indent, false) {
        Ok((_, out, state)) => (out, state),
        Err(_) => (&[] as &[_], state),
    }
}

// note: @dup similar to `eat_nc` but without errors and progress
pub fn eat_nc_locs<'a>(
    arena: &'a Bump,
    mut state: State<'a>,
) -> Option<(&'a [Loc<CommentOrNewline<'a>>], State<'a>)> {
    let mut nc = Vec::new_in(arena);
    let mut found_newline = state.is_at_start_of_file();
    loop {
        let whitespace = fast_eat_whitespace(state.bytes());
        if whitespace > 0 {
            state.advance_mut(whitespace);
        }

        let start = state.pos();
        match state.bytes().first() {
            Some(b'#') => {
                state.advance_mut(1);

                let is_doc_comment =
                    state.bytes().first() == Some(&b'#') && state.bytes().get(1) != Some(&b'#');

                if is_doc_comment {
                    state.advance_mut(1);
                    if state.bytes().first() == Some(&b' ') {
                        state.advance_mut(1);
                    }
                }

                let len = fast_eat_until_control_character(state.bytes());

                // We already checked that the string is valid UTF-8
                debug_assert!(std::str::from_utf8(&state.bytes()[..len]).is_ok());
                let text = unsafe { std::str::from_utf8_unchecked(&state.bytes()[..len]) };

                let comment = if is_doc_comment {
                    CommentOrNewline::DocComment(text)
                } else {
                    CommentOrNewline::LineComment(text)
                };
                state.advance_mut(len);
                nc.push(Loc::pos(start, state.pos(), comment));
                found_newline = true;

                if begins_with_crlf(state.bytes()) {
                    state = state.advance_newline(2);
                } else if state.bytes().first() == Some(&b'\n') {
                    state = state.advance_newline(1);
                }
            }
            Some(b'\r') => {
                if state.bytes().get(1) != Some(&b'\n') {
                    return None;
                }
                state = state.advance_newline(2);
                nc.push(Loc::pos(start, state.pos(), CommentOrNewline::Newline));
                found_newline = true;
            }
            Some(b'\n') => {
                state = state.advance_newline(1);
                nc.push(Loc::pos(start, state.pos(), CommentOrNewline::Newline));
                found_newline = true;
            }
            Some(b'\t') => {
                return None;
            }
            Some(x) if *x < b' ' => {
                return None;
            }
            _ => {
                if found_newline {
                    state = state.mark_current_indent();
                }
                break;
            }
        }
    }

    Some((nc.into_bump_slice(), state))
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn test_eat_whitespace_simple() {
        let bytes = &[0, 0, 0, 0, 0, 0, 0, 0];
        assert_eq!(simple_eat_whitespace(bytes), fast_eat_whitespace(bytes));
    }

    proptest! {
        #[test]
        fn test_eat_whitespace(bytes in proptest::collection::vec(any::<u8>(), 0..100)) {
            prop_assert_eq!(simple_eat_whitespace(&bytes), fast_eat_whitespace(&bytes));
        }
    }

    #[test]
    fn test_eat_until_control_character_simple() {
        let bytes = &[32, 0, 0, 0, 0, 0, 0, 0];
        assert_eq!(
            simple_eat_until_control_character(bytes),
            fast_eat_until_control_character(bytes)
        );
    }

    proptest! {
        #[test]
        fn test_eat_until_control_character(bytes in proptest::collection::vec(any::<u8>(), 0..100)) {
            prop_assert_eq!(
                simple_eat_until_control_character(&bytes),
                fast_eat_until_control_character(&bytes));
        }
    }
}
