use crate::ast::Base;
use crate::parser::{ENumber, Progress};
use crate::state::State;

pub enum NumLiteral<'a> {
    Float(&'a str),
    Num(&'a str),
    NonBase10Int {
        string: &'a str,
        base: Base,
        is_negative: bool,
    },
}

pub fn parse_number_base<'a>(
    is_negated: bool,
    bytes: &'a [u8],
    state: State<'a>,
) -> Result<(NumLiteral<'a>, State<'a>), (Progress, ENumber)> {
    match bytes.get(0..2) {
        Some(b"0b") => chomp_number_base(Base::Binary, is_negated, &bytes[2..], state),
        Some(b"0o") => chomp_number_base(Base::Octal, is_negated, &bytes[2..], state),
        Some(b"0x") => chomp_number_base(Base::Hex, is_negated, &bytes[2..], state),
        _ => chomp_number_dec(is_negated, bytes, state),
    }
}

fn chomp_number_base<'a>(
    base: Base,
    is_negative: bool,
    bytes: &'a [u8],
    state: State<'a>,
) -> Result<(NumLiteral<'a>, State<'a>), (Progress, ENumber)> {
    let (_, chomped) = chomp_number(bytes);

    let string = unsafe { std::str::from_utf8_unchecked(&bytes[..chomped]) };

    let state = state.advance(chomped + 2 + is_negative as usize);
    let literal = NumLiteral::NonBase10Int {
        is_negative,
        string,
        base,
    };
    Ok((literal, state))
}

fn chomp_number_dec<'a>(
    is_negative: bool,
    bytes: &'a [u8],
    state: State<'a>,
) -> Result<(NumLiteral<'a>, State<'a>), (Progress, ENumber)> {
    let (is_float, chomped) = chomp_number(bytes);

    if is_negative && chomped == 0 {
        // we're probably actually looking at unary negation here
        return Err((Progress::NoProgress, ENumber::End));
    }

    if !bytes.first().copied().unwrap_or_default().is_ascii_digit() {
        // we're probably actually looking at unary negation here
        return Err((Progress::NoProgress, ENumber::End));
    }

    let string =
        unsafe { std::str::from_utf8_unchecked(&state.bytes()[0..chomped + is_negative as usize]) };

    let state = state.advance(chomped + is_negative as usize);

    let literal = if is_float {
        NumLiteral::Float(string)
    } else {
        NumLiteral::Num(string)
    };
    Ok((literal, state))
}

fn chomp_number(mut bytes: &[u8]) -> (bool, usize) {
    let start_bytes_len = bytes.len();
    let mut is_float = false;

    while let Some(byte) = bytes.first() {
        match byte {
            b'.' => {
                // skip, fix multiple `.`s in canonicalization
                is_float = true;
                bytes = &bytes[1..];
            }
            b'e' => {
                // maybe scientific notation?
                match bytes.get(1) {
                    Some(b'-') => {
                        is_float = true;
                        bytes = &bytes[2..];
                    }
                    Some(c) if (*c as char).is_ascii_digit() => {
                        is_float = true;
                        bytes = &bytes[2..];
                    }
                    _ => {
                        bytes = &bytes[1..];
                    }
                }
            }
            b'_' => {
                // skip
                bytes = &bytes[1..];
            }
            _ if byte.is_ascii_digit() || byte.is_ascii_alphabetic() => {
                // valid digits (alphabetic in hex digits, and the `e` in `12e26` scientific notation
                bytes = &bytes[1..];
            }
            _ => {
                // not a valid digit; we're done
                return (is_float, start_bytes_len - bytes.len());
            }
        }
    }

    // if the above loop exits, we must be dealing with an empty slice
    // therefore we parsed all of the bytes in the input
    (is_float, start_bytes_len)
}
