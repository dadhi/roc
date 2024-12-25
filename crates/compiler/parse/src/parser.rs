use crate::{
    ast::Collection,
    blankspace::{eat_nc, SpacedBuilder},
    expr::is_special_char,
    keyword::EXPECT,
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

pub type ParseResult<'a, Output, Error> = Result<(Output, State<'a>), (Progress, Error)>;

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
impl<'a> SyntaxError<'a> {
    pub fn get_region(&self) -> Option<Region> {
        match self {
            SyntaxError::Unexpected(r) => Some(*r),
            SyntaxError::Eof(r) => Some(*r),
            SyntaxError::ReservedKeyword(r) => Some(*r),
            SyntaxError::ArgumentsBeforeEquals(r) => Some(*r),
            SyntaxError::Type(e_type) => Some(e_type.get_region()),
            SyntaxError::Pattern(e_pattern) => Some(e_pattern.get_region()),
            SyntaxError::NotEndOfFile(pos) => Some(Region::from_pos(*pos)),
            SyntaxError::Expr(e_expr, _) => Some(e_expr.get_region()),
            SyntaxError::Header(e_header) => Some(e_header.get_region()),
            SyntaxError::NotYetImplemented(_) => None,
            SyntaxError::OutdentedTooFar => None,
            SyntaxError::Todo => None,
            SyntaxError::InvalidPattern => None,
            SyntaxError::BadUtf8 => None,
            SyntaxError::Space(_bad_input) => None,
        }
    }
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

impl<'a> EHeader<'a> {
    pub fn get_region(&self) -> Region {
        match self {
            EHeader::Provides(provides, _pos) => provides.get_region(),
            EHeader::Params(params, _pos) => params.get_region(),
            EHeader::Exposes(_, pos) => Region::from_pos(*pos),
            EHeader::Imports(_, pos) => Region::from_pos(*pos),
            EHeader::Requires(requires, _pos) => requires.get_region(),
            EHeader::Packages(packages, _pos) => packages.get_region(),
            EHeader::Space(_, pos) => Region::from_pos(*pos),
            EHeader::Start(pos) => Region::from_pos(*pos),
            EHeader::ModuleName(pos) => Region::from_pos(*pos),
            EHeader::AppName(app_name, _pos) => app_name.get_region(),
            EHeader::PackageName(package_name, _pos) => package_name.get_region(),
            EHeader::PlatformName(platform_name, _pos) => platform_name.get_region(),
            EHeader::IndentStart(pos) => Region::from_pos(*pos),
            EHeader::InconsistentModuleName(region) => *region,
        }
    }
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

impl<'a> EProvides<'a> {
    pub fn get_region(&self) -> Region {
        let pos = match self {
            EProvides::Provides(p)
            | EProvides::Open(p)
            | EProvides::To(p)
            | EProvides::IndentProvides(p)
            | EProvides::IndentTo(p)
            | EProvides::IndentListStart(p)
            | EProvides::IndentPackage(p)
            | EProvides::ListStart(p)
            | EProvides::ListEnd(p)
            | EProvides::Identifier(p)
            | EProvides::Package(_, p)
            | EProvides::Space(_, p) => p,
        };
        Region::from_pos(*pos)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EParams<'a> {
    Pattern(PRecord<'a>, Position),
    BeforeArrow(Position),
    Arrow(Position),
    AfterArrow(Position),
    Space(BadInputError, Position),
}

impl<'a> EParams<'a> {
    pub fn get_region(&self) -> Region {
        let pos = match self {
            EParams::Pattern(_, p)
            | EParams::BeforeArrow(p)
            | EParams::Arrow(p)
            | EParams::AfterArrow(p)
            | EParams::Space(_, p) => p,
        };
        Region::from_pos(*pos)
    }
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

impl EExposes {
    pub fn get_region(&self) -> Region {
        let pos = match self {
            EExposes::Exposes(p)
            | EExposes::IndentExposes(p)
            | EExposes::IndentListStart(p)
            | EExposes::ListStart(p)
            | EExposes::ListEnd(p)
            | EExposes::Identifier(p)
            | EExposes::Space(_, p) => p,
        };
        Region::from_pos(*pos)
    }
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

impl<'a> ERequires<'a> {
    pub fn get_region(&self) -> Region {
        let pos = match self {
            ERequires::Requires(p)
            | ERequires::Open(p)
            | ERequires::IndentRequires(p)
            | ERequires::IndentListStart(p)
            | ERequires::ListStart(p)
            | ERequires::ListEnd(p)
            | ERequires::TypedIdent(_, p)
            | ERequires::Rigid(p)
            | ERequires::Space(_, p) => p,
        };
        Region::from_pos(*pos)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ETypedIdent<'a> {
    Space(BadInputError, Position),
    HasType(Position),
    Name(Position),
    Type(EType<'a>, Position),
    Identifier(Position),
}

impl<'a> ETypedIdent<'a> {
    pub fn get_region(&self) -> Region {
        let pos = match self {
            ETypedIdent::Space(_, p)
            | ETypedIdent::HasType(p)
            | ETypedIdent::Name(p)
            | ETypedIdent::Type(_, p)
            | ETypedIdent::Identifier(p) => p,
        };
        Region::from_pos(*pos)
    }
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

impl<'a> EPackages<'a> {
    pub fn get_region(&self) -> Region {
        let pos = match self {
            EPackages::Open(p)
            | EPackages::Space(_, p)
            | EPackages::Packages(p)
            | EPackages::IndentPackages(p)
            | EPackages::ListStart(p)
            | EPackages::ListEnd(p)
            | EPackages::IndentListStart(p)
            | EPackages::IndentListEnd(p)
            | EPackages::PackageEntry(_, p) => p,
        };
        Region::from_pos(*pos)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EPackageName<'a> {
    BadPath(EString<'a>, Position),
    Escapes(Position),
    Multiline(Position),
}

impl<'a> EPackageName<'a> {
    pub fn get_region(&self) -> Region {
        let pos = match self {
            EPackageName::BadPath(_, p) | EPackageName::Escapes(p) | EPackageName::Multiline(p) => {
                p
            }
        };
        Region::from_pos(*pos)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EPackageEntry<'a> {
    BadPackage(EPackageName<'a>, Position),
    Shorthand(Position),
    Colon(Position),
    IndentPlatform(Position),
    Space(BadInputError, Position),
}

impl<'a> EPackageEntry<'a> {
    pub fn get_region(&self) -> Region {
        let pos = match self {
            EPackageEntry::BadPackage(_, p)
            | EPackageEntry::Shorthand(p)
            | EPackageEntry::Colon(p)
            | EPackageEntry::IndentPlatform(p)
            | EPackageEntry::Space(_, p) => p,
        };
        Region::from_pos(*pos)
    }
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

impl EImports {
    pub fn get_region(&self) -> Region {
        let pos = match self {
            EImports::Imports(p)
            | EImports::IndentImports(p)
            | EImports::IndentListStart(p)
            | EImports::ListStart(p)
            | EImports::ListEnd(p)
            | EImports::Identifier(p)
            | EImports::ModuleName(p)
            | EImports::Space(_, p)
            | EImports::SetStart(p)
            | EImports::SetEnd(p)
            | EImports::TypedIdent(p)
            | EImports::AsKeyword(p)
            | EImports::StrLiteral(p) => p,
        };
        Region::from_pos(*pos)
    }
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

impl<'a> EExpr<'a> {
    pub fn get_region(&self) -> Region {
        match self {
            // Cases with child nodes that have get_region()
            EExpr::Type(e_type, _) => e_type.get_region(),
            EExpr::Pattern(e_pattern, _) => e_pattern.get_region(),
            EExpr::Ability(e_ability, _) => e_ability.get_region(),
            EExpr::When(e_when, _) => e_when.get_region(),
            EExpr::If(e_if, _) => e_if.get_region(),
            EExpr::Expect(e_expect, _) => e_expect.get_region(),
            EExpr::Dbg(e_expect, _) => e_expect.get_region(),
            EExpr::Import(e_import, _) => e_import.get_region(),
            EExpr::Return(e_return, _) => e_return.get_region(),
            EExpr::Closure(e_closure, _) => e_closure.get_region(),
            EExpr::InParens(e_in_parens, _) => e_in_parens.get_region(),
            EExpr::Record(e_record, _) => e_record.get_region(),
            EExpr::Str(e_string, _) => e_string.get_region(),
            EExpr::List(e_list, _) => e_list.get_region(),

            // Cases with direct Region values
            EExpr::RecordUpdateOldBuilderField(r)
            | EExpr::RecordUpdateIgnoredField(r)
            | EExpr::RecordBuilderOldBuilderField(r) => *r,

            // Cases with Position values
            EExpr::TrailingOperator(p)
            | EExpr::Start(p)
            | EExpr::End(p)
            | EExpr::BadExprEnd(p)
            | EExpr::Space(_, p)
            | EExpr::Dot(p)
            | EExpr::Access(p)
            | EExpr::BadOperator(_, p)
            | EExpr::DefMissingFinalExpr(p)
            | EExpr::DefMissingFinalExpr2(_, p)
            | EExpr::IndentDefBody(p)
            | EExpr::IndentEquals(p)
            | EExpr::IndentAnnotation(p)
            | EExpr::Equals(p)
            | EExpr::Colon(p)
            | EExpr::DoubleColon(p)
            | EExpr::Ident(p)
            | EExpr::ElmStyleFunction(_, p)
            | EExpr::MalformedPattern(p)
            | EExpr::QualifiedTag(p)
            | EExpr::BackpassComma(p)
            | EExpr::BackpassArrow(p)
            | EExpr::BackpassContinue(p)
            | EExpr::DbgContinue(p)
            | EExpr::Number(_, p)
            | EExpr::IndentStart(p)
            | EExpr::IndentEnd(p)
            | EExpr::UnexpectedComma(p)
            | EExpr::UnexpectedTopLevelExpr(p) => Region::from_pos(*p),
        }
    }
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

impl<'a> EString<'a> {
    pub fn get_region(&self) -> Region {
        match self {
            // Case with child node that has get_region()
            EString::Format(expr, _) => expr.get_region(),

            // Cases with Position values
            EString::Open(p)
            | EString::CodePtOpen(p)
            | EString::CodePtEnd(p)
            | EString::InvalidSingleQuote(_, p)
            | EString::Space(_, p)
            | EString::EndlessSingleLine(p)
            | EString::EndlessMultiLine(p)
            | EString::EndlessSingleQuote(p)
            | EString::UnknownEscape(p)
            | EString::FormatEnd(p)
            | EString::MultilineInsufficientIndent(p)
            | EString::ExpectedDoubleQuoteGotSingleQuote(p) => Region::from_pos(*p),
        }
    }
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

impl<'a> ERecord<'a> {
    pub fn get_region(&self) -> Region {
        match self {
            // Cases with child node that has get_region()
            ERecord::Expr(expr, _) => expr.get_region(),

            // Cases with Position values
            ERecord::End(p)
            | ERecord::Open(p)
            | ERecord::Field(p)
            | ERecord::UnderscoreField(p)
            | ERecord::Colon(p)
            | ERecord::Space(_, p) => Region::from_pos(*p),
        }
    }
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

impl<'a> EInParens<'a> {
    pub fn get_region(&self) -> Region {
        match self {
            // Cases with child node that has get_region()
            EInParens::Expr(expr, _) => expr.get_region(),

            // Cases with Position values
            EInParens::End(p)
            | EInParens::Open(p)
            | EInParens::Empty(p)
            | EInParens::Space(_, p) => Region::from_pos(*p),
        }
    }
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

impl<'a> EClosure<'a> {
    pub fn get_region(&self) -> Region {
        match self {
            // Cases with child nodes that have get_region()
            EClosure::Pattern(pattern, _) => pattern.get_region(),
            EClosure::Body(expr, _) => expr.get_region(),

            // Cases with Position values
            EClosure::Space(_, p)
            | EClosure::Start(p)
            | EClosure::Arrow(p)
            | EClosure::Arg(p)
            | EClosure::IndentArrow(p)
            | EClosure::IndentBody(p)
            | EClosure::IndentArg(p) => Region::from_pos(*p),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EList<'a> {
    Open(Position),
    End(Position),
    Space(BadInputError, Position),

    Expr(&'a EExpr<'a>, Position),
}

impl<'a> EList<'a> {
    pub fn get_region(&self) -> Region {
        match self {
            // Case with child node that has get_region()
            EList::Expr(expr, _) => expr.get_region(),

            // Cases with Position values
            EList::Open(p) | EList::End(p) | EList::Space(_, p) => Region::from_pos(*p),
        }
    }
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

impl<'a> EWhen<'a> {
    pub fn get_region(&self) -> Region {
        match self {
            // Cases with child nodes that have get_region()
            EWhen::Pattern(pattern, _) => pattern.get_region(),
            EWhen::IfGuard(expr, _) => expr.get_region(),
            EWhen::Condition(expr, _) => expr.get_region(),
            EWhen::Branch(expr, _) => expr.get_region(),

            // Cases with Position values
            EWhen::Space(_, p)
            | EWhen::When(p)
            | EWhen::Is(p)
            | EWhen::Arrow(p)
            | EWhen::IndentCondition(p)
            | EWhen::IndentPattern(p)
            | EWhen::IndentArrow(p)
            | EWhen::IndentBranch(p)
            | EWhen::IndentIfGuard(p)
            | EWhen::PatternAlignment(_, p) => Region::from_pos(*p),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EAbility<'a> {
    Space(BadInputError, Position),
    Type(EType<'a>, Position),

    DemandAlignment(i32, Position),
    DemandName(Position),
    DemandColon(Position),
}

impl<'a> EAbility<'a> {
    pub fn get_region(&self) -> Region {
        match self {
            // Case with child node that has get_region()
            EAbility::Type(e_type, _) => e_type.get_region(),

            // Cases with Position values
            EAbility::Space(_, p)
            | EAbility::DemandAlignment(_, p)
            | EAbility::DemandName(p)
            | EAbility::DemandColon(p) => Region::from_pos(*p),
        }
    }
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

impl<'a> EIf<'a> {
    pub fn get_region(&self) -> Region {
        match self {
            EIf::Condition(expr, _) | EIf::ThenBranch(expr, _) | EIf::ElseBranch(expr, _) => {
                expr.get_region()
            }
            EIf::Space(_, p)
            | EIf::If(p)
            | EIf::Then(p)
            | EIf::Else(p)
            | EIf::IndentCondition(p)
            | EIf::IndentIf(p)
            | EIf::IndentThenToken(p)
            | EIf::IndentElseToken(p)
            | EIf::IndentThenBranch(p)
            | EIf::IndentElseBranch(p) => Region::from_pos(*p),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EExpect<'a> {
    Space(BadInputError, Position),
    Condition(&'a EExpr<'a>, Position),
    Continuation(&'a EExpr<'a>, Position),
    IndentCondition(Position),
}

impl<'a> EExpect<'a> {
    pub fn get_region(&self) -> Region {
        match self {
            EExpect::Condition(expr, _) | EExpect::Continuation(expr, _) => expr.get_region(),
            EExpect::Space(_, p) | EExpect::IndentCondition(p) => Region::from_pos(*p),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EReturn<'a> {
    Space(BadInputError, Position),
    Return(Position),
    ReturnValue(&'a EExpr<'a>, Position),
    IndentReturnValue(Position),
}
impl<'a> EReturn<'a> {
    pub fn get_region(&self) -> Region {
        match self {
            EReturn::ReturnValue(expr, _) => expr.get_region(),
            EReturn::Space(_, p) | EReturn::Return(p) | EReturn::IndentReturnValue(p) => {
                Region::from_pos(*p)
            }
        }
    }
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

impl<'a> EImport<'a> {
    pub fn get_region(&self) -> Region {
        match self {
            // Cases with child nodes that have get_region()
            EImport::Params(params, _) => params.get_region(),
            EImport::Annotation(e_type, _) => e_type.get_region(),

            // Case with direct Region value
            EImport::LowercaseAlias(r) => *r,

            // Cases with Position values
            EImport::IndentStart(p)
            | EImport::PackageShorthand(p)
            | EImport::PackageShorthandDot(p)
            | EImport::ModuleName(p)
            | EImport::IndentAs(p)
            | EImport::As(p)
            | EImport::IndentAlias(p)
            | EImport::Alias(p)
            | EImport::IndentExposing(p)
            | EImport::Exposing(p)
            | EImport::ExposingListStart(p)
            | EImport::ExposedName(p)
            | EImport::ExposingListEnd(p)
            | EImport::IndentIngestedPath(p)
            | EImport::IngestedPath(p)
            | EImport::IndentIngestedName(p)
            | EImport::IngestedName(p)
            | EImport::IndentColon(p)
            | EImport::Colon(p)
            | EImport::IndentAnnotation(p)
            | EImport::Space(_, p)
            | EImport::EndNewline(p) => Region::from_pos(*p),
        }
    }
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

impl<'a> EImportParams<'a> {
    pub fn get_region(&self) -> Region {
        match self {
            EImportParams::Indent(p) | EImportParams::Record(_, p) | EImportParams::Space(_, p) => {
                Region::from_pos(*p)
            }
            EImportParams::RecordUpdateFound(r)
            | EImportParams::RecordBuilderFound(r)
            | EImportParams::RecordIgnoredFieldFound(r) => *r,
        }
    }
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

impl<'a> EPattern<'a> {
    pub fn get_region(&self) -> Region {
        match self {
            // Cases with child nodes that have get_region()
            EPattern::Record(expr, _) => expr.get_region(),
            EPattern::List(expr, _) => expr.get_region(),
            EPattern::PInParens(expr, _) => expr.get_region(),

            // Cases with Position values
            EPattern::AsKeyword(position)
            | EPattern::AsIdentifier(position)
            | EPattern::Underscore(position)
            | EPattern::NotAPattern(position)
            | EPattern::Start(position)
            | EPattern::End(position)
            | EPattern::Space(_, position)
            | EPattern::NumLiteral(_, position)
            | EPattern::IndentStart(position)
            | EPattern::IndentEnd(position)
            | EPattern::AsIndentStart(position)
            | EPattern::AccessorFunction(position)
            | EPattern::RecordUpdaterFunction(position) => Region::from_pos(*position),
        }
    }
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

impl<'a> PRecord<'a> {
    pub fn get_region(&self) -> Region {
        match self {
            // Cases with child nodes that have get_region()
            PRecord::Pattern(pattern, _) => pattern.get_region(),
            PRecord::Expr(expr, _) => expr.get_region(),

            // Cases with Position values
            PRecord::End(p) | PRecord::Open(p) | PRecord::Field(p) | PRecord::Space(_, p) => {
                Region::from_pos(*p)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PList<'a> {
    End(Position),
    Open(Position),

    Rest(Position),
    Pattern(&'a EPattern<'a>, Position),

    Space(BadInputError, Position),
}

impl<'a> PList<'a> {
    pub fn get_region(&self) -> Region {
        match self {
            // Case with child node that has get_region()
            PList::Pattern(pattern, _) => pattern.get_region(),

            // Cases with Position values
            PList::End(p) | PList::Open(p) | PList::Rest(p) | PList::Space(_, p) => {
                Region::from_pos(*p)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PInParens<'a> {
    Empty(Position),
    End(Position),
    Pattern(&'a EPattern<'a>, Position),

    Space(BadInputError, Position),
}

impl<'a> PInParens<'a> {
    pub fn get_region(&self) -> Region {
        match self {
            // Case with child node that has get_region()
            PInParens::Pattern(pattern, _) => pattern.get_region(),

            // Cases with Position values
            PInParens::Empty(p) | PInParens::End(p) | PInParens::Space(_, p) => {
                Region::from_pos(*p)
            }
        }
    }
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
impl<'a> EType<'a> {
    pub fn get_region(&self) -> Region {
        match self {
            // Cases with child nodes that have get_region()
            EType::TRecord(expr, _) => expr.get_region(),
            EType::TTagUnion(expr, _) => expr.get_region(),
            EType::TInParens(expr, _) => expr.get_region(),
            EType::TApply(eapply, _) => eapply.get_region(),
            EType::TInlineAlias(einline, _) => einline.get_region(),

            // Cases with Position values
            EType::Space(_, p)
            | EType::TBadTypeVariable(p)
            | EType::TStart(p)
            | EType::TEnd(p)
            | EType::TFunctionArgument(p)
            | EType::TImplementsClause(p)
            | EType::TIndentStart(p)
            | EType::TIndentEnd(p)
            | EType::TAsIndentStart(p) => Region::from_pos(*p),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ETypeRecord<'a> {
    End(Position),

    Field(Position),
    Type(&'a EType<'a>, Position),

    Space(BadInputError, Position),
}

impl<'a> ETypeRecord<'a> {
    pub fn get_region(&self) -> Region {
        match self {
            // Case with child node that has get_region()
            ETypeRecord::Type(type_expr, _) => type_expr.get_region(),

            // Cases with Position values
            ETypeRecord::End(p) | ETypeRecord::Field(p) | ETypeRecord::Space(_, p) => {
                Region::from_pos(*p)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ETypeTagUnion<'a> {
    End(Position),

    Type(&'a EType<'a>, Position),

    Space(BadInputError, Position),
}

impl<'a> ETypeTagUnion<'a> {
    pub fn get_region(&self) -> Region {
        match self {
            // Case with child node that has get_region()
            ETypeTagUnion::Type(type_expr, _) => type_expr.get_region(),

            // Cases with Position values
            ETypeTagUnion::End(p) | ETypeTagUnion::Space(_, p) => Region::from_pos(*p),
        }
    }
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

impl<'a> ETypeInParens<'a> {
    pub fn get_region(&self) -> Region {
        match self {
            // Cases with child nodes that have get_region()
            ETypeInParens::Type(type_expr, _) => type_expr.get_region(),

            // Cases with Position values
            ETypeInParens::Empty(p) | ETypeInParens::End(p) | ETypeInParens::Space(_, p) => {
                Region::from_pos(*p)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ETypeApply {
    End(Position),
    Space(BadInputError, Position),
}

impl ETypeApply {
    pub fn get_region(&self) -> Region {
        let pos = match self {
            ETypeApply::End(p) | ETypeApply::Space(_, p) => p,
        };
        Region::from_pos(*pos)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ETypeInlineAlias {
    NotAnAlias(Position),
    Qualified(Position),
    ArgumentNotLowercase(Position),
}

impl ETypeInlineAlias {
    pub fn get_region(&self) -> Region {
        let pos = match self {
            ETypeInlineAlias::NotAnAlias(p)
            | ETypeInlineAlias::Qualified(p)
            | ETypeInlineAlias::ArgumentNotLowercase(p) => p,
        };
        Region::from_pos(*pos)
    }
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
impl<'a> ETypeAbilityImpl<'a> {
    pub fn get_region(&self) -> Region {
        match self {
            // Case with child node that has get_region()
            ETypeAbilityImpl::Type(type_expr, _) => type_expr.get_region(),
            ETypeAbilityImpl::Expr(expr, _) => expr.get_region(),
            // Cases with Position values
            ETypeAbilityImpl::End(p)
            | ETypeAbilityImpl::Open(p)
            | ETypeAbilityImpl::Field(p)
            | ETypeAbilityImpl::UnderscoreField(p)
            | ETypeAbilityImpl::Colon(p)
            | ETypeAbilityImpl::Space(_, p)
            | ETypeAbilityImpl::QuestionMark(p)
            | ETypeAbilityImpl::IndentBar(p)
            | ETypeAbilityImpl::IndentAmpersand(p) => Region::from_pos(*p),
        }
    }
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

/// Start the check from the next character after keyword,
/// that should not be an identifier character
/// to prevent treating `whence` or `iffy` as keywords
pub fn eat_keyword<'a>(kw: &'static str, state: &State<'a>) -> usize {
    let bytes = state.bytes();
    let kw_len = kw.len();
    let found = match bytes.get(kw_len) {
        Some(b'-') if kw != EXPECT => bytes.starts_with(kw.as_bytes()),
        Some(b) => is_special_char(b) && bytes.starts_with(kw.as_bytes()),
        None => bytes.starts_with(kw.as_bytes()),
    };
    if found {
        kw_len
    } else {
        0
    }
}

// It is always returns Err with MadeProgress, because it the inner parser between the opening and closing symbols.
pub fn collection_inner<'a, Elem: 'a + crate::ast::Spaceable<'a> + Clone, E: 'a + SpaceProblem>(
    arena: &'a Bump,
    state: State<'a>,
    elem_p: impl Fn(&'a Bump, State<'a>) -> ParseResult<'a, Loc<Elem>, E> + 'a,
    space_before: impl Fn(&'a Elem, &'a [crate::ast::CommentOrNewline<'a>]) -> Elem,
) -> ParseResult<'a, crate::ast::Collection<'a, Loc<Elem>>, E> {
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

        let (_, (spaces_before, _), next) = match eat_nc::<'a, E>(arena, state.clone(), false) {
            Ok(ok) => ok,
            Err(_) => break,
        };

        let (item, next) = match elem_p(arena, next) {
            Ok(ok) => ok,
            Err(_) => break,
        };

        let (item, next) = match eat_nc::<'a, E>(arena, next.clone(), false) {
            Ok((_, (spaces_after, _), next)) => {
                (item.spaced_around(arena, spaces_before, spaces_after), next)
            }
            Err(_) => (item.spaced_before(arena, spaces_before), next),
        };

        items.push(item);
        state = next;
    }

    let (_, (final_spaces, _), state) = eat_nc(arena, state, true)?;

    let items = Collection::with_items_and_comments(arena, items.into_bump_slice(), final_spaces);
    Ok((items, state))
}
