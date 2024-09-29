// These keywords are valid in expressions
pub const IF: &str = "if";
pub const THEN: &str = "then";
pub const ELSE: &str = "else";
pub const WHEN: &str = "when";
pub const AS: &str = "as";
pub const IS: &str = "is";
pub const DBG: &str = "dbg";
pub const IMPORT: &str = "import";
pub const EXPECT: &str = "expect";
pub const EXPECT_FX: &str = "expect-fx";
pub const CRASH: &str = "crash";

// These keywords are valid in imports
pub const EXPOSING: &str = "exposing";

// These keywords are valid in types
pub const IMPLEMENTS: &str = "implements";
pub const WHERE: &str = "where";

// These keywords are valid in headers
pub const PLATFORM: &str = "platform";

pub const KEYWORDS: [&str; 11] = [
    IF, THEN, ELSE, WHEN, AS, IS, DBG, IMPORT, EXPECT, EXPECT_FX, CRASH,
];

// todo: @wip create a fast lookup for the keyword, returning its index (or enum?).
// Utilize it when checking that identifier is not a keyword and when checking the state against keywords in a sequence, e.g. in `parse_stmt_start`
// Implement it via the fixed `match` layers starting from the first character or from the length of the input string,
// see http://0x80.pl/notesen/2023-04-30-lookup-in-strings.html
// and http://0x80.pl/notesen/2022-01-29-http-verb-parse.html

pub fn match_keyword(s: &str) -> Option<&str> {
    match s {
        IF => Some(IF),
        THEN => Some(THEN),
        ELSE => Some(ELSE),
        WHEN => Some(WHEN),
        AS => Some(AS),
        IS => Some(IS),
        DBG => Some(DBG),
        IMPORT => Some(IMPORT),
        EXPECT => Some(EXPECT),
        EXPECT_FX => Some(EXPECT_FX),
        CRASH => Some(CRASH),
        _ => None,
    }
}

pub fn smart_match_keyword2(s: &str) -> Option<&str> {
    let len = s.len();
    if len < 2 || len > 9 {
        return None;
    }
    let bytes: &[u8] = s.as_bytes();
    match bytes[0] {
        b'a' => match bytes[1] {
            b's' => match len {
                2 => Some(AS),
                _ => None,
            },
            _ => None,
        },
        b'c' => match bytes[1] {
            b'r' => match s {
                CRASH => Some(CRASH),
                _ => None,
            },
            _ => None,
        },
        b'd' => match bytes[1] {
            b'b' => match s {
                DBG => Some(DBG),
                _ => None,
            },
            _ => None,
        },
        b'e' => match bytes[1] {
            b'l' => match s {
                ELSE => Some(ELSE),
                _ => None,
            },
            b'x' => match s {
                EXPECT => Some(EXPECT),
                EXPECT_FX => Some(EXPECT_FX),
                _ => None,
            },
            _ => None,
        },
        b'i' => match bytes[1] {
            b'f' => match len {
                2 => Some(IF),
                _ => None,
            },
            b'm' => match s {
                IMPORT => Some(IMPORT),
                _ => None,
            },
            b's' => match len {
                2 => Some(IS),
                _ => None,
            },
            _ => None,
        },
        b't' => match bytes[1] {
            b'h' => match s {
                THEN => Some(THEN),
                _ => None,
            },
            _ => None,
        },
        b'w' => match bytes[1] {
            b'h' => match s {
                WHEN => Some(WHEN),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

pub fn smart_match_keyword(s: &str) -> Option<&str> {
    let bytes = s.as_bytes();
    match bytes.len() {
        2 => match bytes[0] {
            b'a' => match bytes[1] {
                b's' => Some(AS),
                _ => None,
            },
            b'i' => match bytes[1] {
                b'f' => Some(IF),
                b's' => Some(IS),
                _ => None,
            },
            _ => None,
        },
        3 => match bytes[0] {
            b'd' => match s {
                DBG => Some(DBG),
                _ => None,
            },
            _ => None,
        },
        4 => match bytes[0] {
            b'e' => match s {
                ELSE => Some(ELSE),
                _ => None,
            },
            b't' => match s {
                THEN => Some(THEN),
                _ => None,
            },
            b'w' => match s {
                WHEN => Some(WHEN),
                _ => None,
            },
            _ => None,
        },
        5 => match bytes[0] {
            b'c' => match s {
                CRASH => Some(CRASH),
                _ => None,
            },
            _ => None,
        },
        6 => match bytes[0] {
            b'i' => match s {
                IMPORT => Some(IMPORT),
                _ => None,
            },
            b'e' => match s {
                EXPECT => Some(EXPECT),
                _ => None,
            },
            _ => None,
        },
        9 => match bytes[0] {
            b'e' => match s {
                EXPECT_FX => Some(EXPECT_FX),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}
