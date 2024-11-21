use crate::{
    ast::Collection,
    blankspace::{eat_nc, SpacedBuilder},
    expr::is_special_char,
    state::State,
};
use bumpalo::collections::vec::Vec;
use bumpalo::Bump;
use roc_region::all::{Loc, Position, Region};
use Progress::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Either<First, Second> {
    First(First),
    Second(Second),
}

impl<F: Copy, S: Copy> Copy for Either<F, S> {}

pub type ParseResult<'a, Output, Error> = Result<(Progress, Output, State<'a>), (Progress, Error)>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Progress {
    MadeProgress,
    NoProgress,
}

impl Progress {
    #[inline(always)]
    pub fn when(made_progress: bool) -> Self {
        if made_progress {
            Progress::MadeProgress
        } else {
            Progress::NoProgress
        }
    }

    pub fn or(&self, other: Self) -> Self {
        if (*self == MadeProgress) || (other == MadeProgress) {
            MadeProgress
        } else {
            NoProgress
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SyntaxError<'a> {
    Unexpected(Region),
    OutdentedTooFar,
    Eof(Region),
    InvalidPattern,
    BadUtf8,
    ReservedKeyword(Region),
    ArgumentsBeforeEquals(Region),
    NotYetImplemented(String),
    Todo,
    Type(EType<'a>),
    Pattern(EPattern<'a>),
    Expr(EExpr<'a>, Position),
    Header(EHeader<'a>),
    Space(BadInputError),
    NotEndOfFile(Position),
}
pub trait SpaceProblem: std::fmt::Debug {
    fn space_problem(e: BadInputError, pos: Position) -> Self;
}

macro_rules! impl_space_problem {
    ($($name:ident $(< $lt:tt >)?),*) => {
        $(
            impl $(< $lt >)? SpaceProblem for $name $(< $lt >)? {
                fn space_problem(e: BadInputError, pos: Position) -> Self {
                    Self::Space(e, pos)
                }
            }
        )*
    };
}

impl_space_problem! {
    EExpect<'a>,
    EExposes,
    EExpr<'a>,
    EHeader<'a>,
    EIf<'a>,
    EImport<'a>,
    EParams<'a>,
    EImports,
    EImportParams<'a>,
    EInParens<'a>,
    EClosure<'a>,
    EList<'a>,
    EPackageEntry<'a>,
    EPackages<'a>,
    EPattern<'a>,
    EProvides<'a>,
    ERecord<'a>,
    EReturn<'a>,
    ERequires<'a>,
    EString<'a>,
    EType<'a>,
    ETypeInParens<'a>,
    ETypeRecord<'a>,
    ETypeTagUnion<'a>,
    ETypedIdent<'a>,
    ETypeAbilityImpl<'a>,
    EWhen<'a>,
    EAbility<'a>,
    PInParens<'a>,
    PRecord<'a>,
    PList<'a>
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EHeader<'a> {
    Provides(EProvides<'a>, Position),
    Params(EParams<'a>, Position),
    Exposes(EExposes, Position),
    Imports(EImports, Position),
    Requires(ERequires<'a>, Position),
    Packages(EPackages<'a>, Position),

    Space(BadInputError, Position),
    Start(Position),
    ModuleName(Position),
    AppName(EString<'a>, Position),
    PackageName(EPackageName<'a>, Position),
    PlatformName(EPackageName<'a>, Position),
    IndentStart(Position),

    InconsistentModuleName(Region),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EProvides<'a> {
    Provides(Position),
    Open(Position),
    To(Position),
    IndentProvides(Position),
    IndentTo(Position),
    IndentListStart(Position),
    IndentPackage(Position),
    ListStart(Position),
    ListEnd(Position),
    Identifier(Position),
    Package(EPackageName<'a>, Position),
    Space(BadInputError, Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EParams<'a> {
    Pattern(PRecord<'a>, Position),
    BeforeArrow(Position),
    Arrow(Position),
    AfterArrow(Position),
    Space(BadInputError, Position),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EExposes {
    Exposes(Position),
    IndentExposes(Position),
    IndentListStart(Position),
    ListStart(Position),
    ListEnd(Position),
    Identifier(Position),
    Space(BadInputError, Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ERequires<'a> {
    Requires(Position),
    Open(Position),
    IndentRequires(Position),
    IndentListStart(Position),
    ListStart(Position),
    ListEnd(Position),
    TypedIdent(ETypedIdent<'a>, Position),
    Rigid(Position),
    Space(BadInputError, Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ETypedIdent<'a> {
    Space(BadInputError, Position),
    HasType(Position),
    IndentHasType(Position),
    Name(Position),
    Type(EType<'a>, Position),
    IndentType(Position),
    Identifier(Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EPackages<'a> {
    Open(Position),
    Space(BadInputError, Position),
    Packages(Position),
    IndentPackages(Position),
    ListStart(Position),
    ListEnd(Position),
    IndentListStart(Position),
    IndentListEnd(Position),
    PackageEntry(EPackageEntry<'a>, Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EPackageName<'a> {
    BadPath(EString<'a>, Position),
    Escapes(Position),
    Multiline(Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EPackageEntry<'a> {
    BadPackage(EPackageName<'a>, Position),
    Shorthand(Position),
    Colon(Position),
    IndentPackage(Position),
    IndentPlatform(Position),
    Space(BadInputError, Position),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EImports {
    Imports(Position),
    IndentImports(Position),
    IndentListStart(Position),
    ListStart(Position),
    ListEnd(Position),
    Identifier(Position),
    ModuleName(Position),
    Space(BadInputError, Position),
    SetStart(Position),
    SetEnd(Position),
    TypedIdent(Position),
    AsKeyword(Position),
    StrLiteral(Position),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BadInputError {
    HasTab,
    HasMisplacedCarriageReturn,
    HasAsciiControl,
    BadUtf8,
}

impl<'a, T> SourceError<'a, T> {
    pub fn new(problem: T, state: &State<'a>) -> Self {
        Self {
            problem,
            bytes: state.original_bytes(),
        }
    }

    pub fn map_problem<E>(self, f: impl FnOnce(T) -> E) -> SourceError<'a, E> {
        SourceError {
            problem: f(self.problem),
            bytes: self.bytes,
        }
    }

    pub fn into_file_error(self, filename: std::path::PathBuf) -> FileError<'a, T> {
        FileError {
            problem: self,
            filename,
        }
    }
}

impl<'a> SyntaxError<'a> {
    pub fn into_source_error(self, state: &State<'a>) -> SourceError<'a, SyntaxError<'a>> {
        SourceError {
            problem: self,
            bytes: state.original_bytes(),
        }
    }

    pub fn into_file_error(
        self,
        filename: std::path::PathBuf,
        state: &State<'a>,
    ) -> FileError<'a, SyntaxError<'a>> {
        self.into_source_error(state).into_file_error(filename)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EExpr<'a> {
    TrailingOperator(Position),

    Start(Position),
    End(Position),
    BadExprEnd(Position),
    Space(BadInputError, Position),

    Dot(Position),
    Access(Position),
    BadOperator(&'a str, Position),

    DefMissingFinalExpr(Position),
    DefMissingFinalExpr2(&'a EExpr<'a>, Position),
    Type(EType<'a>, Position),
    Pattern(&'a EPattern<'a>, Position),
    Ability(EAbility<'a>, Position),
    IndentDefBody(Position),
    IndentEquals(Position),
    IndentAnnotation(Position),
    Equals(Position),
    Colon(Position),
    DoubleColon(Position),
    Ident(Position),
    ElmStyleFunction(Region, Position),
    MalformedPattern(Position),
    QualifiedTag(Position),
    BackpassComma(Position),
    BackpassArrow(Position),
    BackpassContinue(Position),
    DbgContinue(Position),

    When(EWhen<'a>, Position),
    If(EIf<'a>, Position),

    Expect(EExpect<'a>, Position),
    Dbg(EExpect<'a>, Position),
    Import(EImport<'a>, Position),
    Return(EReturn<'a>, Position),

    Closure(EClosure<'a>, Position),

    InParens(EInParens<'a>, Position),
    Record(ERecord<'a>, Position),
    RecordUpdateOldBuilderField(Region),
    RecordUpdateIgnoredField(Region),
    RecordBuilderOldBuilderField(Region),

    // SingleQuote errors are folded into the EString
    Str(EString<'a>, Position),

    Number(ENumber, Position),
    List(EList<'a>, Position),

    IndentStart(Position),
    IndentEnd(Position),

    UnexpectedComma(Position),
    UnexpectedTopLevelExpr(Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ENumber {
    End,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EString<'a> {
    Open(Position),

    CodePtOpen(Position),
    CodePtEnd(Position),

    InvalidSingleQuote(ESingleQuote, Position),

    Space(BadInputError, Position),
    EndlessSingleLine(Position),
    EndlessMultiLine(Position),
    EndlessSingleQuote(Position),
    UnknownEscape(Position),
    Format(&'a EExpr<'a>, Position),
    FormatEnd(Position),
    MultilineInsufficientIndent(Position),
    ExpectedDoubleQuoteGotSingleQuote(Position),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ESingleQuote {
    Empty,
    TooLong,
    InterpolationNotAllowed,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ERecord<'a> {
    End(Position),
    Open(Position),

    Field(Position),
    UnderscoreField(Position),
    Colon(Position),

    // TODO remove
    Expr(&'a EExpr<'a>, Position),

    Space(BadInputError, Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EInParens<'a> {
    End(Position),
    Open(Position),

    /// Empty parens, e.g. () is not allowed
    Empty(Position),

    ///
    Expr(&'a EExpr<'a>, Position),

    ///
    Space(BadInputError, Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EClosure<'a> {
    Space(BadInputError, Position),
    Start(Position),
    Arrow(Position),
    Arg(Position),
    // TODO make EEXpr
    Pattern(EPattern<'a>, Position),
    Body(&'a EExpr<'a>, Position),
    IndentArrow(Position),
    IndentBody(Position),
    IndentArg(Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EList<'a> {
    Open(Position),
    End(Position),
    Space(BadInputError, Position),

    Expr(&'a EExpr<'a>, Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EWhen<'a> {
    Space(BadInputError, Position),
    When(Position),
    Is(Position),
    Pattern(EPattern<'a>, Position),
    Arrow(Position),

    IfGuard(&'a EExpr<'a>, Position),

    Condition(&'a EExpr<'a>, Position),
    Branch(&'a EExpr<'a>, Position),

    IndentCondition(Position),
    IndentPattern(Position),
    IndentArrow(Position),
    IndentBranch(Position),
    IndentIfGuard(Position),
    PatternAlignment(u32, Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EAbility<'a> {
    Space(BadInputError, Position),
    Type(EType<'a>, Position),

    DemandAlignment(i32, Position),
    DemandName(Position),
    DemandColon(Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EIf<'a> {
    Space(BadInputError, Position),
    If(Position),
    Then(Position),
    Else(Position),
    // TODO make EEXpr
    Condition(&'a EExpr<'a>, Position),
    ThenBranch(&'a EExpr<'a>, Position),
    ElseBranch(&'a EExpr<'a>, Position),

    IndentCondition(Position),
    IndentIf(Position),
    IndentThenToken(Position),
    IndentElseToken(Position),
    IndentThenBranch(Position),
    IndentElseBranch(Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EExpect<'a> {
    Space(BadInputError, Position),
    Condition(&'a EExpr<'a>, Position),
    Continuation(&'a EExpr<'a>, Position),
    IndentCondition(Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EReturn<'a> {
    Space(BadInputError, Position),
    Return(Position),
    ReturnValue(&'a EExpr<'a>, Position),
    IndentReturnValue(Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EImport<'a> {
    IndentStart(Position),
    PackageShorthand(Position),
    PackageShorthandDot(Position),
    ModuleName(Position),
    Params(EImportParams<'a>, Position),
    IndentAs(Position),
    As(Position),
    IndentAlias(Position),
    Alias(Position),
    LowercaseAlias(Region),
    IndentExposing(Position),
    Exposing(Position),
    ExposingListStart(Position),
    ExposedName(Position),
    ExposingListEnd(Position),
    IndentIngestedPath(Position),
    IngestedPath(Position),
    IndentIngestedName(Position),
    IngestedName(Position),
    IndentColon(Position),
    Colon(Position),
    IndentAnnotation(Position),
    Annotation(EType<'a>, Position),
    Space(BadInputError, Position),
    EndNewline(Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EImportParams<'a> {
    Indent(Position),
    Record(ERecord<'a>, Position),
    RecordUpdateFound(Region),
    RecordBuilderFound(Region),
    RecordIgnoredFieldFound(Region),
    Space(BadInputError, Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EPattern<'a> {
    Record(PRecord<'a>, Position),
    List(PList<'a>, Position),
    AsKeyword(Position),
    AsIdentifier(Position),
    Underscore(Position),
    NotAPattern(Position),

    Start(Position),
    End(Position),
    Space(BadInputError, Position),

    PInParens(PInParens<'a>, Position),
    NumLiteral(ENumber, Position),

    IndentStart(Position),
    IndentEnd(Position),
    AsIndentStart(Position),

    AccessorFunction(Position),
    RecordUpdaterFunction(Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PRecord<'a> {
    End(Position),
    Open(Position),

    Field(Position),

    Pattern(&'a EPattern<'a>, Position),
    Expr(&'a EExpr<'a>, Position),

    Space(BadInputError, Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PList<'a> {
    End(Position),
    Open(Position),

    Rest(Position),
    Pattern(&'a EPattern<'a>, Position),

    Space(BadInputError, Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PInParens<'a> {
    Empty(Position),
    End(Position),
    Pattern(&'a EPattern<'a>, Position),

    Space(BadInputError, Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EType<'a> {
    Space(BadInputError, Position),

    TRecord(ETypeRecord<'a>, Position),
    TTagUnion(ETypeTagUnion<'a>, Position),
    TInParens(ETypeInParens<'a>, Position),
    TApply(ETypeApply, Position),
    TInlineAlias(ETypeInlineAlias, Position),
    TBadTypeVariable(Position),
    ///
    TStart(Position),
    TEnd(Position),
    TFunctionArgument(Position),
    TImplementsClause(Position),
    ///
    TIndentStart(Position),
    TIndentEnd(Position),
    TAsIndentStart(Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ETypeRecord<'a> {
    End(Position),

    Field(Position),
    Type(&'a EType<'a>, Position),

    Space(BadInputError, Position),

    IndentColon(Position),
    IndentOptional(Position),
    IndentEnd(Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ETypeTagUnion<'a> {
    End(Position),

    Type(&'a EType<'a>, Position),

    Space(BadInputError, Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ETypeInParens<'a> {
    /// e.g. (), which isn't a valid type
    Empty(Position),

    End(Position),
    ///
    Type(&'a EType<'a>, Position),

    /// note: Do not delete it, because we have a macro implementation that uses it
    Space(BadInputError, Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ETypeApply {
    End(Position),
    Space(BadInputError, Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ETypeInlineAlias {
    NotAnAlias(Position),
    Qualified(Position),
    ArgumentNotLowercase(Position),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ETypeAbilityImpl<'a> {
    End(Position),
    Open(Position),

    Field(Position),
    UnderscoreField(Position),
    Colon(Position),
    Type(&'a EType<'a>, Position),

    Space(BadInputError, Position),

    QuestionMark(Position),
    Expr(&'a EExpr<'a>, Position),
    IndentBar(Position),
    IndentAmpersand(Position),
}

impl<'a> From<ERecord<'a>> for ETypeAbilityImpl<'a> {
    fn from(e: ERecord<'a>) -> Self {
        match e {
            ERecord::End(p) => ETypeAbilityImpl::End(p),
            ERecord::Open(p) => ETypeAbilityImpl::Open(p),
            ERecord::Field(p) => ETypeAbilityImpl::Field(p),
            ERecord::UnderscoreField(p) => ETypeAbilityImpl::UnderscoreField(p),
            ERecord::Colon(p) => ETypeAbilityImpl::Colon(p),
            ERecord::Space(s, p) => ETypeAbilityImpl::Space(s, p),
            ERecord::Expr(e, p) => ETypeAbilityImpl::Expr(e, p),
        }
    }
}

#[derive(Debug)]
pub struct SourceError<'a, T> {
    pub problem: T,
    pub bytes: &'a [u8],
}

#[derive(Debug)]
pub struct FileError<'a, T> {
    pub problem: SourceError<'a, T>,
    pub filename: std::path::PathBuf,
}

pub trait Parser<'a, Output, Error> {
    fn parse(
        &self,
        arena: &'a Bump,
        state: State<'a>,
        min_indent: u32,
    ) -> ParseResult<'a, Output, Error>;

    #[cfg(not(feature = "parse_debug_trace"))]
    #[inline(always)]
    fn trace(self, _message: &'static str) -> Self
    where
        Self: Sized,
        Output: std::fmt::Debug,
        Error: std::fmt::Debug,
    {
        self
    }

    #[cfg(feature = "parse_debug_trace")]
    fn trace(self, message: &'static str) -> Traced<'a, Output, Error, Self>
    where
        Self: Sized,
        Output: std::fmt::Debug,
        Error: std::fmt::Debug,
    {
        Traced {
            parser: self,
            message,
            _phantom: Default::default(),
        }
    }
}

impl<'a, F, Output, Error> Parser<'a, Output, Error> for F
where
    Error: 'a,
    F: Fn(&'a Bump, State<'a>, u32) -> ParseResult<'a, Output, Error>,
{
    fn parse(
        &self,
        arena: &'a Bump,
        state: State<'a>,
        min_indent: u32,
    ) -> ParseResult<'a, Output, Error> {
        self(arena, state, min_indent)
    }
}

#[cfg(feature = "parse_debug_trace")]
pub struct Traced<'a, O, E, P: Parser<'a, O, E>> {
    parser: P,
    message: &'static str,
    _phantom: std::marker::PhantomData<&'a (O, E)>,
}

#[cfg(feature = "parse_debug_trace")]
impl<'a, O: std::fmt::Debug, E: std::fmt::Debug, P: Parser<'a, O, E>> Parser<'a, O, E>
    for Traced<'a, O, E, P>
where
    E: 'a,
{
    fn parse(&self, arena: &'a Bump, state: State<'a>, min_indent: u32) -> ParseResult<'a, O, E> {
        use std::cell::RefCell;

        thread_local! {
            pub static INDENT: RefCell<usize> = RefCell::new(0);
        }

        // This should be enough for anyone. Right? RIGHT?
        let indent_text = "| ; : ! ".repeat(20);

        let cur_indent = INDENT.with(|i| *i.borrow());

        println!(
            "{:<5?}:{:<2} {}{:<50}",
            state.pos(),
            min_indent,
            &indent_text[..cur_indent * 2],
            self.message
        );

        let previous_state = state.clone();
        INDENT.with(|i| *i.borrow_mut() += 1);
        let res = self.parser.parse(arena, state, min_indent);
        INDENT.with(|i| *i.borrow_mut() = cur_indent);

        let (progress, value, state) = match &res {
            Ok((progress, result, state)) => (progress, Ok(result), state),
            Err((progress, error)) => (progress, Err(error), &previous_state),
        };

        println!(
            "{:<5?}:{:<2} {}{:<50} {:<15} {:?}",
            state.pos(),
            min_indent,
            &indent_text[..cur_indent * 2],
            self.message,
            format!("{:?}", progress),
            value
        );

        res
    }
}

/// Start the check from the next character after keyword,
/// that should not be an identifier character
/// to prevent treating `whence` or `iffy` as keywords
pub fn at_keyword(kw: &'static str, state: &State<'_>) -> bool {
    let bytes = state.bytes();
    match bytes.get(kw.len()) {
        Some(b) => is_special_char(b) && bytes.starts_with(kw.as_bytes()),
        None => bytes.starts_with(kw.as_bytes()),
    }
}

// MACRO COMBINATORS
//
// Using some combinators together results in combinatorial type explosion,
// this takes forever to compile. Using macros instead avoids this!

/// Wraps the output of the given parser in a [`Loc`](../roc_region/all/struct.Loc.html) struct,
/// to provide location information.
///
/// # Examples
/// ```
/// # #![forbid(unused_imports)]
/// # use roc_parse::state::State;
/// # use crate::roc_parse::parser::{Parser, Progress, word, loc};
/// # use roc_region::all::{Loc, Position};
/// # use bumpalo::Bump;
/// # #[derive(Debug, PartialEq)]
/// # enum Problem {
/// #     NotFound(Position),
/// # }
/// # let arena = Bump::new();
/// # fn foo<'a>(arena: &'a Bump) {
/// let parser = loc(word("hello", Problem::NotFound));
///
/// let (progress, output, state) = parser.parse(&arena, State::new("hello, world".as_bytes()), 0).unwrap();
/// assert_eq!(progress, Progress::MadeProgress);
/// assert_eq!(output, Loc::new(0, 5, ()));
/// assert_eq!(state.pos().offset, 5);
/// # }
/// # foo(&arena);
/// ```
pub fn loc<'a, Output, E: 'a>(
    parser: impl Parser<'a, Output, E>,
) -> impl Parser<'a, Loc<Output>, E> {
    move |arena: &'a Bump, state: crate::state::State<'a>, min_indent: u32| {
        let start = state.pos();
        match parser.parse(arena, state, min_indent) {
            Ok((progress, value, state)) => {
                Ok((progress, Loc::pos(start, state.pos(), value), state))
            }
            Err(err) => Err(err),
        }
    }
}

pub fn skip_second<'a, P1, First, P2, Second, E>(p1: P1, p2: P2) -> impl Parser<'a, First, E>
where
    E: 'a,
    P1: Parser<'a, First, E>,
    P2: Parser<'a, Second, E>,
{
    move |arena, state: crate::state::State<'a>, min_indent: u32| match p1
        .parse(arena, state, min_indent)
    {
        Ok((p1, out1, state)) => match p2.parse(arena, state, min_indent) {
            Ok((p2, _, state)) => Ok((p1.or(p2), out1, state)),
            Err((p2, fail)) => Err((p1.or(p2), fail)),
        },
        Err((progress, fail)) => Err((progress, fail)),
    }
}

// It is always returns Err with MadeProgress, because it the inner parser between the opening and closing symbols.
pub fn collection_inner<'a, Elem: 'a + crate::ast::Spaceable<'a> + Clone, E: 'a + SpaceProblem>(
    arena: &'a Bump,
    state: State<'a>,
    elem_p: impl Fn(&'a Bump, State<'a>) -> Result<(Loc<Elem>, State<'a>), (Progress, E)> + 'a,
    space_before: impl Fn(&'a Elem, &'a [crate::ast::CommentOrNewline<'a>]) -> Elem,
) -> Result<(crate::ast::Collection<'a, Loc<Elem>>, State<'a>), (Progress, E)> {
    let (_, (first_spaces, _), state) = eat_nc(arena, state, true)?;

    let (first_item, state) = match elem_p(arena, state.clone()) {
        Ok(ok) => ok,
        Err((NoProgress, _)) => {
            let empty = Collection::with_items_and_comments(arena, &[], first_spaces);
            return Ok((empty, state));
        }
        Err(err) => return Err(err),
    };

    let (_, (spaces_after, _), state) = eat_nc(arena, state, true)?;
    let mut first_item = first_item.spaced_after(arena, spaces_after);

    if !first_spaces.is_empty() {
        let spaced_val = space_before(arena.alloc(first_item.value), first_spaces);
        first_item = Loc::at(first_item.region, spaced_val);
    }

    let mut items = Vec::with_capacity_in(1, arena);
    items.push(first_item);

    let mut state = state;
    loop {
        if state.bytes().first() != Some(&b',') {
            break;
        }
        state.inc_mut();
        match eat_nc::<'a, E>(arena, state.clone(), false) {
            Ok((_, (spb, _), news)) => {
                let (elem, news) = match elem_p(arena, news) {
                    Ok(ok) => ok,
                    Err(_) => break,
                };
                let (item, news) = match eat_nc::<'a, E>(arena, news.clone(), false) {
                    Ok((_, (spa, _), news)) => (elem.spaced_around(arena, spb, spa), news),
                    Err(_) => (elem.spaced_before(arena, spb), news),
                };
                items.push(item);
                state = news;
            }
            Err(_) => break,
        }
    }

    let (_, (final_spaces, _), state) = eat_nc(arena, state, true)?;

    let items = Collection::with_items_and_comments(arena, items.into_bump_slice(), final_spaces);
    Ok((items, state))
}

/// Creates a parser that always succeeds with the given argument as output.
///
/// # Examples
/// ```
/// # #![forbid(unused_imports)]
/// # use roc_parse::state::State;
/// # use crate::roc_parse::parser::{Parser, Progress, succeed};
/// # use bumpalo::Bump;
/// # let arena = Bump::new();
/// # fn foo<'a>(arena: &'a Bump) {
/// let parser = succeed("different");
///
/// let (progress, output, state) = Parser::<&'a str,()>::parse(&parser, &arena, State::new("hello, world".as_bytes()), 0).unwrap();
/// assert_eq!(progress, Progress::NoProgress);
/// assert_eq!(output, "different");
/// assert_eq!(state.pos().offset, 0);
/// # }
/// # foo(&arena);
/// ```
pub fn succeed<'a, T: Clone, E: 'a>(value: T) -> impl Parser<'a, T, E> {
    move |_arena: &'a bumpalo::Bump, state: crate::state::State<'a>, _min_indent: u32| {
        Ok((NoProgress, value.clone(), state))
    }
}

/// Take as input something that looks like a struct literal where values are parsers
/// and return a parser that runs each parser and returns a struct literal with the
/// results.
#[macro_export]
macro_rules! record {
    ($name:ident $(:: $name_ext:ident)* { $($field:ident: $parser:expr),* $(,)? }) => {
        move |arena: &'a bumpalo::Bump, state: $crate::state::State<'a>, min_indent: u32| {
            let mut state = state;
            let mut progress = NoProgress;
            $(
                let (new_progress, $field, new_state) = $parser.parse(arena, state, min_indent)?;
                state = new_state;
                progress = progress.or(new_progress);
            )*
            Ok((progress, $name $(:: $name_ext)* { $($field),* }, state))
        }
    };
}

pub fn reset_min_indent<'a, P, T, X: 'a>(parser: P) -> impl Parser<'a, T, X>
where
    P: Parser<'a, T, X>,
{
    move |arena, state, _min_indent| parser.parse(arena, state, 0)
}

/// Transforms a possible error, like `map_err` in Rust.
/// It has no effect if the given parser succeeds.
///
/// # Examples
/// ```
/// # #![forbid(unused_imports)]
/// # use roc_parse::state::State;
/// # use crate::roc_parse::parser::{Parser, Progress, word, specialize_err};
/// # use roc_region::all::Position;
/// # use bumpalo::Bump;
/// # #[derive(Debug, PartialEq)]
/// # enum Problem {
/// #     NotFound(Position),
/// #     Other(Position),
/// # }
/// # let arena = Bump::new();
/// let parser = specialize_err(
///     |_prev_err, pos| Problem::Other(pos),
///     word("bye", Problem::NotFound)
/// );
///
/// let (progress, err) = parser.parse(&arena, State::new("hello, world".as_bytes()), 0).unwrap_err();
/// assert_eq!(progress, Progress::NoProgress);
/// assert_eq!(err, Problem::Other(Position::new(0)));
/// ```
pub fn specialize_err<'a, F, P, T, X, Y>(map_error: F, parser: P) -> impl Parser<'a, T, Y>
where
    F: Fn(X, Position) -> Y,
    P: Parser<'a, T, X>,
    Y: 'a,
{
    move |a, state: State<'a>, min_indent| {
        let original_pos = state.pos();
        match parser.parse(a, state, min_indent) {
            Ok(t) => Ok(t),
            Err((p, error)) => Err((p, map_error(error, original_pos))),
        }
    }
}

pub fn word<'a, ToError, E>(word: &'static str, to_error: ToError) -> impl Parser<'a, (), E>
where
    ToError: Fn(Position) -> E,
    E: 'a,
{
    debug_assert!(!word.contains('\n'));
    move |_arena: &'a Bump, state: State<'a>, _min_indent: u32| {
        if state.bytes().starts_with(word.as_bytes()) {
            Ok((MadeProgress, (), state.advance(word.len())))
        } else {
            Err((NoProgress, to_error(state.pos())))
        }
    }
}

/// Matches a single `u8` and moves the state's position forward if it succeeds.
///
/// # Example
///
/// ```
/// # #![forbid(unused_imports)]
/// # use roc_parse::state::State;
/// # use crate::roc_parse::parser::{Parser, Progress, byte};
/// # use roc_region::all::Position;
/// # use bumpalo::Bump;
/// # #[derive(Debug, PartialEq)]
/// # enum Problem {
/// #     NotFound(Position),
/// # }
/// # let arena = Bump::new();
/// let parser = byte(b'h', Problem::NotFound);
///
/// // Success case
/// let (progress, output, state) = parser.parse(&arena, State::new("hello, world".as_bytes()), 0).unwrap();
/// assert_eq!(progress, Progress::MadeProgress);
/// assert_eq!(output, ());
/// assert_eq!(state.pos(), Position::new(1));
///
/// // Error case
/// let (progress, problem) = parser.parse(&arena, State::new("bye, world".as_bytes()), 0).unwrap_err();
/// assert_eq!(progress, Progress::NoProgress);
/// assert_eq!(problem, Problem::NotFound(Position::zero()));
/// ```
pub fn byte<'a, ToError, E>(byte_to_match: u8, to_error: ToError) -> impl Parser<'a, (), E>
where
    ToError: Fn(Position) -> E,
    E: 'a,
{
    debug_assert_ne!(byte_to_match, b'\n');

    move |_arena: &'a Bump, state: State<'a>, _min_indent: u32| match state.bytes().first() {
        Some(x) if *x == byte_to_match => Ok((MadeProgress, (), state.inc())),
        _ => Err((NoProgress, to_error(state.pos()))),
    }
}
