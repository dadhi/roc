use roc_region::all::{Position, Region};
use std::fmt;

use crate::parser::Progress;

pub const CLOSURE_PIPE_SUGAR: &[u8] = b"\\>";
pub const CLOSURE_PIPE_SUGAR_LEN: usize = CLOSURE_PIPE_SUGAR.len();
pub const CLOSURE_PIPE_DESUGAR: &[u8] = b"\\0__ -> o__ |>";
pub const CLOSURE_PIPE_DESUGAR_LEN: usize = CLOSURE_PIPE_DESUGAR.len();

/// A position in a source file.
// NB: [Copy] is explicitly NOT derived to reduce the chance of bugs due to accidentally re-using
// parser state.
#[derive(Clone)]
pub struct State<'a> {
    /// The raw input bytes from the file.
    /// Beware: original_bytes[0] always points at the start of the file.
    /// Use bytes()[0] to access the current byte the parser is inspecting
    original_bytes: &'a [u8],

    /// Offset in original_bytes that the parser is currently inspecting
    offset: usize,

    /// Position of the start of the current line
    pub(crate) line_start: Position,

    /// Position of the first non-whitespace character on the current line
    pub(crate) line_start_after_whitespace: Position,

    // TODO @wip
    /// The bytes desugared from the shorthand syntax in the original bytes, e.g. `\>` to `\x -> x |>`
    closure_pipe_desugar_active: bool,

    /// The offset inside the desugared bytes,
    /// so the logical current offset will be `offset + closure_pipe_desugar_offset`
    closure_pipe_desugar_offset: usize,
}

impl<'a> State<'a> {
    pub fn new(bytes: &'a [u8]) -> State<'a> {
        State {
            original_bytes: bytes,
            offset: 0,
            line_start: Position::zero(),

            // Technically not correct.
            // We don't know the position of the first non-whitespace character yet.
            line_start_after_whitespace: Position::zero(),

            closure_pipe_desugar_active: false,
            closure_pipe_desugar_offset: 0,
        }
    }

    pub fn original_bytes(&self) -> &'a [u8] {
        self.original_bytes
    }

    pub fn original_bytes_at_offset(&self) -> &'a [u8] {
        // dbg!(self.offset);
        // dbg!(String::from_utf8(self.original_bytes[self.offset..].to_vec()).unwrap());
        &self.original_bytes[self.offset..]
    }

    pub(crate) fn bytes(&self) -> &'a [u8] {
        if self.closure_pipe_desugar_active {
            if self.closure_pipe_desugar_offset >= CLOSURE_PIPE_DESUGAR_LEN {
                let original_offset =
                    self.offset + CLOSURE_PIPE_SUGAR_LEN + self.closure_pipe_desugar_offset
                        - CLOSURE_PIPE_DESUGAR_LEN;
                &self.original_bytes[original_offset..]
            } else {
                &CLOSURE_PIPE_DESUGAR[self.closure_pipe_desugar_offset..]
            }
        } else {
            &self.original_bytes[self.offset..]
        }
    }

    pub fn column(&self) -> u32 {
        self.pos().offset - self.line_start.offset
    }

    pub fn line_indent(&self) -> u32 {
        self.line_start_after_whitespace.offset - self.line_start.offset
    }

    /// Check that the indent is at least `indent` spaces.
    /// Return a new indent if the current indent is greater than `indent`.
    pub fn check_indent<E>(
        &self,
        indent: u32,
        e: impl Fn(Position) -> E,
    ) -> Result<u32, (Progress, E)> {
        if self.column() < indent {
            Err((Progress::NoProgress, e(self.pos())))
        } else {
            Ok(std::cmp::max(indent, self.line_indent()))
        }
    }

    #[must_use]
    #[inline(always)]
    pub(crate) fn activate_closure_pipe_desugar(mut self) -> State<'a> {
        debug_assert!(
            !self.closure_pipe_desugar_active,
            "closure_pipe_desugar should be inactive"
        );
        self.closure_pipe_desugar_active = true;
        self.closure_pipe_desugar_offset = 0;
        self
    }

    /// Mutably advance the state by a given offset
    pub(crate) fn advance_mut(&mut self, offset: usize) {
        if self.closure_pipe_desugar_active {
            let new_offset = self.closure_pipe_desugar_offset + offset;
            if new_offset >= CLOSURE_PIPE_DESUGAR_LEN {
                self.offset += CLOSURE_PIPE_SUGAR_LEN + new_offset - CLOSURE_PIPE_DESUGAR_LEN;
                self.closure_pipe_desugar_active = false;
            } else {
                self.closure_pipe_desugar_offset = new_offset;
            }
        } else {
            self.offset += offset;
        }
    }

    /// If the next `text.len()` bytes of the input match the provided `text`,
    /// mutably advance the state by that much.
    #[inline(always)]
    pub(crate) fn consume_mut(&mut self, text: &str) -> bool {
        let found = self.bytes().starts_with(text.as_bytes());

        if found {
            self.advance_mut(text.len());
        }

        found
    }

    #[must_use]
    #[inline(always)]
    pub(crate) const fn advance(mut self, offset: usize) -> State<'a> {
        if self.closure_pipe_desugar_active {
            let new_offset = self.closure_pipe_desugar_offset + offset;
            if new_offset >= CLOSURE_PIPE_DESUGAR_LEN {
                self.offset += CLOSURE_PIPE_SUGAR_LEN + new_offset - CLOSURE_PIPE_DESUGAR_LEN;
                self.closure_pipe_desugar_active = false;
            } else {
                self.closure_pipe_desugar_offset = new_offset;
            }
        } else {
            self.offset += offset;
        }
        self
    }

    #[must_use]
    #[inline(always)]
    pub(crate) const fn advance_original_bytes(mut self, offset: usize) -> State<'a> {
        self.offset += offset;
        self
    }

    #[must_use]
    #[inline(always)]
    pub(crate) const fn advance_newline(mut self) -> State<'a> {
        self.offset += 1;
        self.line_start = self.pos();

        // WARNING! COULD CAUSE BUGS IF WE FORGET TO CALL mark_current_indent LATER!
        // We really need to be stricter about this.
        self.line_start_after_whitespace = self.line_start;

        self
    }

    #[must_use]
    #[inline(always)]
    pub(crate) const fn mark_current_indent(mut self) -> State<'a> {
        self.line_start_after_whitespace = self.pos();
        self
    }

    /// Returns the current position
    pub const fn pos(&self) -> Position {
        Position::new(self.offset as u32)
    }

    pub const fn closure_pipe_desugared(&self) -> bool {
        self.closure_pipe_desugar_active
    }

    /// Returns whether the parser has reached the end of the input
    pub const fn has_reached_end(&self) -> bool {
        self.offset == self.original_bytes.len()
    }

    /// Returns a Region corresponding to the current state, but
    /// with the the end column advanced by the given amount. This is
    /// useful when parsing something "manually" (using input.chars())
    /// and thus wanting a Region while not having access to loc().
    pub fn len_region(&self, length: u32) -> Region {
        Region::new(self.pos(), self.pos().bump_column(length))
    }
}

impl<'a> fmt::Debug for State<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "State {{")?;

        match std::str::from_utf8(self.bytes()) {
            Ok(string) => write!(f, "\n\tbytes: [utf8] {string:?}")?,
            Err(_) => write!(f, "\n\tbytes: [invalid utf8] {:?}", self.bytes())?,
        }

        write!(f, "\n\t(offset): {:?},", self.pos())?;
        write!(f, "\n}}")
    }
}

#[test]
fn state_size() {
    // State should always be under 8 machine words, so it fits in a typical
    // cache line.
    let state_size = std::mem::size_of::<State>();
    let maximum = std::mem::size_of::<usize>() * 8;
    assert!(state_size <= maximum, "{state_size:?} <= {maximum:?}");
}
