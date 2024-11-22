use std::fmt::Debug;

use crate::ast::{
    Collection, CommentOrNewline, Defs, Header, Malformed, Pattern, Spaced, Spaces, SpacesBefore,
    StrLiteral, TypeAnnotation,
};
use crate::blankspace::{eat_nc_check, SpacedBuilder};
use crate::expr::merge_spaces;
use crate::ident::{self, parse_anycase_ident, parse_lowercase_ident, UppercaseIdent};
use crate::parser::Progress::{self, *};
use crate::parser::{
    at_keyword, collection_inner, EExposes, EHeader, EImports, EPackageEntry, EPackageName,
    EPackages, EParams, EProvides, ERequires, ETypedIdent, ParseResult, Parser, SourceError,
    SpaceProblem, SyntaxError,
};
use crate::pattern::parse_record_pattern_fields;
use crate::state::State;
use crate::string_literal::{self, parse_str_literal};
use crate::type_annotation::{parse_type_expr, SKIP_PARSING_SPACES_BEFORE, TRAILING_COMMA_VALID};
use roc_module::ident::IdentSuffix;
use roc_module::symbol::ModuleId;
use roc_region::all::{Loc, Position, Region};

pub fn parse_module_defs<'a>(
    arena: &'a bumpalo::Bump,
    state: State<'a>,
    defs: Defs<'a>,
) -> Result<Defs<'a>, SyntaxError<'a>> {
    match crate::expr::parse_top_level_defs(arena, state.clone(), defs) {
        Ok((defs, state)) => {
            if state.has_reached_end() {
                Ok(defs)
            } else {
                Err(SyntaxError::NotEndOfFile(state.pos()))
            }
        }
        Err((_, fail)) => Err(SyntaxError::Expr(fail, state.pos())),
    }
}

pub fn parse_header<'a>(
    arena: &'a bumpalo::Bump,
    state: State<'a>,
) -> Result<(SpacesBefore<'a, Header<'a>>, State<'a>), SourceError<'a, EHeader<'a>>> {
    match header(arena, state.clone()) {
        Ok((module, state)) => Ok((module, state)),
        Err((_, fail)) => Err(SourceError::new(fail, &state)),
    }
}

pub fn header<'a>(
    arena: &'a bumpalo::Bump,
    state: State<'a>,
) -> Result<(SpacesBefore<'a, Header<'a>>, State<'a>), (Progress, EHeader<'a>)> {
    let (_, before, state) = eat_nc_check(EHeader::IndentStart, arena, state, 0, false)?;

    let inc_indent = 1;
    if at_keyword("module", &state) {
        let state = state.inc_len("module");
        let (item, state) = parse_module_header(arena, state, inc_indent)?;
        let item = Header::Module(item);
        return Ok((SpacesBefore { before, item }, state));
    }

    if at_keyword("interface", &state) {
        let state = state.inc_len("interface");
        let (_, out, state) = interface_header().parse(arena, state, inc_indent)?;
        let item = Header::Module(out);
        return Ok((SpacesBefore { before, item }, state));
    }

    if at_keyword("app", &state) {
        let state = state.inc_len("app");
        let (out, state) = match app_header(arena, state.clone(), inc_indent) {
            Ok(ok) => ok,
            Err((MadeProgress, fail)) => return Err((MadeProgress, fail)),
            Err((NoProgress, _)) => old_app_header(arena, state, inc_indent)?,
        };
        let item = Header::App(out);
        return Ok((SpacesBefore { before, item }, state));
    }

    if at_keyword("package", &state) {
        let state = state.inc_len("package");
        let (out, state) = match package_header(arena, state.clone(), inc_indent) {
            Ok(ok) => ok,
            Err((MadeProgress, fail)) => return Err((MadeProgress, fail)),
            Err((NoProgress, _)) => old_package_header(arena, state, inc_indent)?,
        };
        let item = Header::Package(out);
        return Ok((SpacesBefore { before, item }, state));
    }

    if at_keyword("platform", &state) {
        let state = state.inc_len("platform");
        let (_, out, state) = platform_header().parse(arena, state, inc_indent)?;
        let item = Header::Platform(out);
        return Ok((SpacesBefore { before, item }, state));
    }

    if at_keyword("hosted", &state) {
        let state = state.inc_len("hosted");
        let (header, state) = hosted_header(arena, state, inc_indent)?;
        let item = Header::Hosted(header);
        return Ok((SpacesBefore { before, item }, state));
    }

    Err((NoProgress, EHeader::Start(state.pos())))
}

fn parse_module_header<'a>(
    arena: &'a bumpalo::Bump,
    state: State<'a>,
    min_indent: u32,
) -> Result<(ModuleHeader<'a>, State<'a>), (Progress, EHeader<'a>)> {
    let (_, after_keyword, state) =
        eat_nc_check(EHeader::IndentStart, arena, state, min_indent, false)?;

    let pos = state.pos();
    let (params, state) = match parse_module_params(arena, state.clone(), min_indent) {
        Ok((_, out, state)) => (Some(out), state),
        Err((NoProgress, _)) => (None, state),
        Err((p, fail)) => return Err((p, EHeader::Params(fail, pos))),
    };

    let pos = state.pos();
    let (_, exposes, state) = exposes_list()
        .parse(arena, state, min_indent)
        .map_err(|(p, fail)| (p, EHeader::Exposes(fail, pos)))?;

    let header = ModuleHeader {
        after_keyword,
        params,
        exposes,
        interface_imports: None,
    };
    Ok((header, state))
}

fn parse_module_params<'a>(
    arena: &'a bumpalo::Bump,
    state: State<'a>,
    min_indent: u32,
) -> ParseResult<'a, ModuleParams<'a>, EParams<'a>> {
    let start = state.pos();

    let (pattern, state) = match parse_record_pattern_fields(arena, state) {
        Ok((_, fields, state)) => (state.loc(start, fields), state),
        Err((p, fail)) => {
            return Err((p, EParams::Pattern(fail, start)));
        }
    };

    let (_, before_arrow, state) =
        eat_nc_check(EParams::BeforeArrow, arena, state, min_indent, false)?;

    if !state.bytes().starts_with(b"->") {
        return Err((MadeProgress, EParams::Arrow(state.pos())));
    }
    let state = state.advance(2);

    let (_, after_arrow, state) =
        eat_nc_check(EParams::AfterArrow, arena, state, min_indent, false)?;

    let params = ModuleParams {
        pattern,
        before_arrow,
        after_arrow,
    };
    Ok((MadeProgress, params, state))
}

// TODO does this need to be a macro?
macro_rules! merge_n_spaces {
    ($arena:expr, $($slice:expr),*) => {
        {
            let mut merged = bumpalo::collections::Vec::with_capacity_in(0 $(+ $slice.len())*, $arena);
            $(merged.extend_from_slice($slice);)*
            merged.into_bump_slice()
        }
    };
}

/// Parse old interface headers so we can format them into module headers
fn interface_header<'a>() -> impl Parser<'a, ModuleHeader<'a>, EHeader<'a>> {
    let after_keyword_p = |arena, state: State<'a>, min_indent: u32| {
        let (sp_err, before_name, state) =
            eat_nc_check(EHeader::IndentStart, arena, state, min_indent, false)?;

        let name_pos = state.pos();
        let state = match parse_module_name(state) {
            Ok((_, state)) => state,
            Err(p) => return Err((p.or(sp_err), EHeader::ModuleName(name_pos))),
        };

        let kw_pos = state.pos();
        let (_, kw, state) = exposes_kw()
            .parse(arena, state, min_indent)
            .map_err(|(p, fail)| (p, EHeader::Exposes(fail, kw_pos)))?;

        let out = merge_n_spaces!(arena, before_name, kw.before, kw.after);
        Ok((MadeProgress, out, state))
    };

    move |arena: &'a bumpalo::Bump, state: State<'a>, min_indent: u32| {
        let (_, after_keyword, state) = after_keyword_p(arena, state, min_indent)?;

        let exposes_pos = state.pos();
        let (_, exposes, state) = exposes_list()
            .parse(arena, state, min_indent)
            .map_err(|(p, fail)| (p, EHeader::Exposes(fail, exposes_pos)))?;

        let start = state.pos();
        let (interface_imports, state) = match imports().parse(arena, state, min_indent) {
            Ok((_, out, state)) => (if out.item.is_empty() { None } else { Some(out) }, state),
            Err((p, fail)) => return Err((p, EHeader::Imports(fail, start))),
        };

        let header = ModuleHeader {
            after_keyword,
            params: None,
            exposes,
            interface_imports,
        };
        Ok((MadeProgress, header, state))
    }
}

fn hosted_header<'a>(
    arena: &'a bumpalo::Bump,
    state: State<'a>,
    min_indent: u32,
) -> Result<(HostedHeader<'a>, State<'a>), (Progress, EHeader<'a>)> {
    let (_, before_name, state) =
        eat_nc_check(EHeader::IndentStart, arena, state, min_indent, false)?;

    let name_pos = state.pos();
    let (name, state) = match parse_module_name(state) {
        Ok(ok) => ok,
        Err(p) => return Err((p, EHeader::ModuleName(name_pos))),
    };
    let name = Loc::pos(name_pos, state.pos(), name);

    let exposes_pos = state.pos();
    let (_, keyword, state) = exposes_kw()
        .parse(arena, state, min_indent)
        .map_err(|(p, fail)| (p, EHeader::Exposes(fail, exposes_pos)))?;

    let (_, item, state) = exposes_list()
        .parse(arena, state, min_indent)
        .map_err(|(p, fail)| (p, EHeader::Exposes(fail, exposes_pos)))?;

    let exposes = KeywordItem { keyword, item };

    let imports_pos = state.pos();
    let (_, imports, state) = match imports().parse(arena, state, min_indent) {
        Ok(ok) => ok,
        Err((p, fail)) => return Err((p, EHeader::Imports(fail, imports_pos))),
    };

    let header = HostedHeader {
        before_name,
        name,
        exposes,
        imports,
    };
    Ok((header, state))
}

pub(crate) fn chomp_module_name(buffer: &[u8]) -> Result<&str, Progress> {
    use encode_unicode::CharExt;
    match char::from_utf8_slice_start(buffer) {
        Ok((ch, mut chomped)) if ch.is_uppercase() => {
            while let Ok((ch, width)) = char::from_utf8_slice_start(&buffer[chomped..]) {
                // After the first character, only these are allowed:
                //
                // * Unicode alphabetic chars - you might include `鹏` if that's clear to your readers
                // * ASCII digits - e.g. `1` but not `¾`, both of which pass .is_numeric()
                // * A '.' separating module parts
                if ch.is_alphabetic() || ch.is_ascii_digit() {
                    chomped += width;
                } else if ch == '.' {
                    chomped += width;

                    if let Ok((next, width)) = char::from_utf8_slice_start(&buffer[chomped..]) {
                        if next.is_uppercase() {
                            chomped += width;
                        } else if next == '{' {
                            // the .{ starting a `Foo.{ bar, baz }` importing clauses
                            chomped -= width;
                            break;
                        } else {
                            return Err(Progress::MadeProgress);
                        }
                    }
                } else {
                    // we're done
                    break;
                }
            }
            let name = unsafe { std::str::from_utf8_unchecked(&buffer[..chomped]) };
            Ok(name)
        }
        _ => Err(Progress::NoProgress),
    }
}

#[inline(always)]
pub(crate) fn parse_module_name(state: State<'_>) -> Result<(ModuleName<'_>, State<'_>), Progress> {
    match chomp_module_name(state.bytes()) {
        Ok(name) => Ok((ModuleName::new(name), state.inc_len(name))),
        Err(p) => Err(p),
    }
}

fn app_header<'a>(
    arena: &'a bumpalo::Bump,
    state: State<'a>,
    min_indent: u32,
) -> Result<(AppHeader<'a>, State<'a>), (Progress, EHeader<'a>)> {
    let (_, before_provides, state) =
        eat_nc_check(EHeader::IndentStart, arena, state, min_indent, false)?;

    let pos = state.pos();
    let (_, provides, state) = exposes_list()
        .parse(arena, state, min_indent)
        .map_err(|(p, fail)| (p, EHeader::Exposes(fail, pos)))?;

    let (_, before_packages, state) =
        eat_nc_check(EHeader::IndentStart, arena, state, min_indent, false)?;

    let pos = state.pos();
    let (_, packages, state) = packages_collection()
        .parse(arena, state, min_indent)
        .map_err(|(p, fail)| (p, EHeader::Packages(fail, pos)))?;
    let packages = state.loc(pos, packages);

    let header = AppHeader {
        before_provides,
        provides,
        before_packages,
        packages,
        old_imports: None,
        old_provides_to_new_package: None,
    };
    Ok((header, state))
}

struct OldAppHeader<'a> {
    pub before_name: &'a [CommentOrNewline<'a>],
    pub packages: Option<Loc<OldAppPackages<'a>>>,
    pub imports: Option<KeywordItem<'a, ImportsKeyword, ImportsCollection<'a>>>,
    pub provides: ProvidesTo<'a>,
}

type OldAppPackages<'a> =
    KeywordItem<'a, PackagesKeyword, Collection<'a, Loc<Spaced<'a, PackageEntry<'a>>>>>;

fn old_app_header<'a>(
    arena: &'a bumpalo::Bump,
    state: State<'a>,
    min_indent: u32,
) -> Result<(AppHeader<'a>, State<'a>), (Progress, EHeader<'a>)> {
    let old = record!(OldAppHeader {
        before_name: move |arena: &'a bumpalo::Bump, state: State<'a>, min_indent: u32| {
            let (_, before_name, state) =
                eat_nc_check(EHeader::IndentStart, arena, state, min_indent, false)?;

            let pos = state.pos();
            let (_, _, state) = string_literal::parse_str_literal()
                .parse(arena, state, min_indent)
                .map_err(|(p, fail)| (p, EHeader::AppName(fail, pos)))?;

            Ok((MadeProgress, before_name, state))
        },
        packages: move |arena: &'a bumpalo::Bump, state: State<'a>, min_indent: u32| {
            let olds = state.clone();
            match packages().parse(arena, state, min_indent) {
                Ok((p, out, state)) => Ok((p, Some(Loc::pos(olds.pos(), state.pos(), out)), state)),
                Err((NoProgress, _)) => Ok((NoProgress, None, olds)),
                Err((_, fail)) => Err((MadeProgress, EHeader::Packages(fail, olds.pos()))),
            }
        },
        imports: move |arena: &'a bumpalo::Bump, state: State<'a>, min_indent: u32| {
            let olds = state.clone();
            match imports().parse(arena, state, min_indent) {
                Ok((p, out, state)) => Ok((p, Some(out), state)),
                Err((NoProgress, _)) => Ok((NoProgress, None, olds)),
                Err((_, fail)) => Err((MadeProgress, EHeader::Imports(fail, olds.pos()))),
            }
        },
        provides: move |arena: &'a bumpalo::Bump, state: State<'a>, min_indent: u32| {
            let pos = state.pos();
            provides_to()
                .parse(arena, state, min_indent)
                .map_err(|(p, fail)| (p, EHeader::Provides(fail, pos)))
        }
    });

    match old.parse(arena, state, min_indent) {
        Ok((_, old, state)) => {
            let mut before_packages: &'a [CommentOrNewline] = &[];

            let packages = match old.packages {
                Some(packages) => {
                    before_packages = merge_spaces(
                        arena,
                        packages.value.keyword.before,
                        packages.value.keyword.after,
                    );

                    if let To::ExistingPackage(platform_shorthand) = old.provides.to.value {
                        packages.map(|coll| {
                            coll.item.map_items(arena, |loc_spaced_pkg| {
                                if loc_spaced_pkg.value.item().shorthand == platform_shorthand {
                                    loc_spaced_pkg.map(|spaced_pkg| {
                                        spaced_pkg.map(arena, |pkg| {
                                            let mut new_pkg = *pkg;
                                            new_pkg.platform_marker = Some(merge_spaces(
                                                arena,
                                                old.provides.to_keyword.before,
                                                old.provides.to_keyword.after,
                                            ));
                                            new_pkg
                                        })
                                    })
                                } else {
                                    *loc_spaced_pkg
                                }
                            })
                        })
                    } else {
                        packages.map(|kw| kw.item)
                    }
                }
                None => Loc {
                    region: Region::zero(),
                    value: Collection::empty(),
                },
            };

            let provides = match old.provides.types {
                Some(types) => {
                    let mut combined_items = bumpalo::collections::Vec::with_capacity_in(
                        old.provides.entries.items.len() + types.items.len(),
                        arena,
                    );

                    combined_items.extend_from_slice(old.provides.entries.items);

                    for loc_spaced_type_ident in types.items {
                        combined_items.push(loc_spaced_type_ident.map(|spaced_type_ident| {
                            spaced_type_ident.map(arena, |type_ident| {
                                ExposedName::new(From::from(*type_ident))
                            })
                        }));
                    }

                    let value_comments = old.provides.entries.final_comments();
                    let type_comments = types.final_comments();

                    let mut combined_comments = bumpalo::collections::Vec::with_capacity_in(
                        value_comments.len() + type_comments.len(),
                        arena,
                    );
                    combined_comments.extend_from_slice(value_comments);
                    combined_comments.extend_from_slice(type_comments);

                    Collection::with_items_and_comments(
                        arena,
                        combined_items.into_bump_slice(),
                        combined_comments.into_bump_slice(),
                    )
                }
                None => old.provides.entries,
            };

            let out = AppHeader {
                before_provides: merge_spaces(
                    arena,
                    old.before_name,
                    old.provides.provides_keyword.before,
                ),
                provides,
                before_packages: merge_spaces(
                    arena,
                    before_packages,
                    old.provides.provides_keyword.after,
                ),
                packages,
                old_imports: old
                    .imports
                    .and_then(|x| if x.item.is_empty() { None } else { Some(x) }),
                old_provides_to_new_package: match old.provides.to.value {
                    To::NewPackage(new_pkg) => Some(new_pkg),
                    To::ExistingPackage(_) => None,
                },
            };

            Ok((out, state))
        }
        Err(err) => Err(err),
    }
}

fn package_header<'a>(
    arena: &'a bumpalo::Bump,
    state: State<'a>,
    min_indent: u32,
) -> Result<(PackageHeader<'a>, State<'a>), (Progress, EHeader<'a>)> {
    let (_, before_exposes, state) =
        eat_nc_check(EHeader::IndentStart, arena, state, min_indent, false)?;

    let pos = state.pos();
    let (_, exposes, state) = exposes_module_collection()
        .parse(arena, state, min_indent)
        .map_err(|(p, fail)| (p, EHeader::Exposes(fail, pos)))?;

    let (_, before_packages, state) =
        eat_nc_check(EHeader::IndentStart, arena, state, min_indent, false)?;

    let pos = state.pos();
    let (_, packages, state) = packages_collection()
        .parse(arena, state, min_indent)
        .map_err(|(p, fail)| (p, EHeader::Packages(fail, pos)))?;
    let packages = state.loc(pos, packages);

    let header = PackageHeader {
        before_exposes,
        exposes,
        before_packages,
        packages,
    };
    Ok((header, state))
}

#[derive(Debug, Clone, PartialEq)]
struct OldPackageHeader<'a> {
    before_name: &'a [CommentOrNewline<'a>],
    exposes: KeywordItem<'a, ExposesKeyword, Collection<'a, Loc<Spaced<'a, ModuleName<'a>>>>>,
    packages:
        Loc<KeywordItem<'a, PackagesKeyword, Collection<'a, Loc<Spaced<'a, PackageEntry<'a>>>>>>,
}

fn old_package_header<'a>(
    arena: &'a bumpalo::Bump,
    state: State<'a>,
    min_indent: u32,
) -> Result<(PackageHeader<'a>, State<'a>), (Progress, EHeader<'a>)> {
    let (sp_err, before_name, state) =
        eat_nc_check(EHeader::IndentStart, arena, state, min_indent, false)?;

    let pos = state.pos();
    let (_, _, state) = package_name()
        .parse(arena, state, min_indent)
        .map_err(|(p, fail)| (p.or(sp_err), EHeader::PackageName(fail, pos)))?;

    let pos = state.pos();
    let (_, exposes, state) = exposes_modules()
        .parse(arena, state, min_indent)
        .map_err(|(p, fail)| (p.or(sp_err), EHeader::Exposes(fail, pos)))?;

    let pos = state.pos();
    let (_, packages, state) = packages()
        .parse(arena, state, min_indent)
        .map_err(|(p, fail)| (p.or(sp_err), EHeader::Packages(fail, pos)))?;
    let packages = state.loc(pos, packages);

    let old = OldPackageHeader {
        before_name,
        exposes,
        packages,
    };

    let before_exposes = merge_n_spaces!(
        arena,
        old.before_name,
        old.exposes.keyword.before,
        old.exposes.keyword.after
    );

    let before_packages = merge_spaces(
        arena,
        old.packages.value.keyword.before,
        old.packages.value.keyword.after,
    );

    let old = PackageHeader {
        before_exposes,
        exposes: old.exposes.item,
        before_packages,
        packages: old.packages.map(|kw| kw.item),
    };

    Ok((old, state))
}

fn platform_header<'a>() -> impl Parser<'a, PlatformHeader<'a>, EHeader<'a>> {
    move |arena: &'a bumpalo::Bump, state: State<'a>, min_indent: u32| {
        let (_, before_name, state) =
            eat_nc_check(EHeader::IndentStart, arena, state, min_indent, false)?;

        let pos = state.pos();
        let (_, name, state) = package_name()
            .parse(arena, state, min_indent)
            .map_err(|(p, fail)| (p, EHeader::PlatformName(fail, pos)))?;
        let name = state.loc(pos, name);

        let pos = state.pos();
        let (_, requires, state) = requires()
            .parse(arena, state, min_indent)
            .map_err(|(p, fail)| (p, EHeader::Requires(fail, pos)))?;

        let pos = state.pos();
        let (_, exposes, state) = exposes_modules()
            .parse(arena, state, min_indent)
            .map_err(|(p, fail)| (p, EHeader::Exposes(fail, pos)))?;

        let pos = state.pos();
        let (_, packages, state) = packages()
            .parse(arena, state, min_indent)
            .map_err(|(p, fail)| (p, EHeader::Packages(fail, pos)))?;

        let pos = state.pos();
        let (_, imports, state) = imports()
            .parse(arena, state, min_indent)
            .map_err(|(p, fail)| (p, EHeader::Imports(fail, pos)))?;

        let pos = state.pos();
        let (_, provides, state) = provides_exposed()
            .parse(arena, state, min_indent)
            .map_err(|(p, fail)| (p, EHeader::Provides(fail, pos)))?;

        let header = PlatformHeader {
            before_name,
            name,
            requires,
            exposes,
            packages,
            imports,
            provides,
        };
        Ok((MadeProgress, header, state))
    }
}

fn provides_to_package<'a>(
    arena: &'a bumpalo::Bump,
    state: State<'a>,
    min_indent: u32,
) -> Result<(To<'a>, State<'a>), (Progress, EProvides<'a>)> {
    let pos = state.pos();
    match parse_lowercase_ident(state.clone()) {
        Ok((out, state)) => Ok((To::ExistingPackage(out), state)),
        Err(MadeProgress) => Err((MadeProgress, EProvides::Identifier(pos))),
        Err(_) => match package_name().parse(arena, state, min_indent) {
            Ok((_, out, state)) => Ok((To::NewPackage(out), state)),
            Err((p, fail)) => Err((p, EProvides::Package(fail, pos))),
        },
    }
}

fn provides_to<'a>() -> impl Parser<'a, ProvidesTo<'a>, EProvides<'a>> {
    (move |arena: &'a bumpalo::Bump, state: State<'a>, min_indent: u32| {
        let (_, provides_keyword, state) = spaces_around_keyword(
            ProvidesKeyword,
            EProvides::Provides,
            EProvides::IndentProvides,
            EProvides::IndentListStart,
        )
        .parse(arena, state, min_indent)?;

        if state.bytes().first() != Some(&b'[') {
            return Err((NoProgress, EProvides::ListStart(state.pos())));
        }
        let state = state.inc();
        let (entries, state) = collection_inner(arena, state, provides_ident, Spaced::SpaceBefore)?;

        if state.bytes().first() != Some(&b']') {
            return Err((MadeProgress, EProvides::ListEnd(state.pos())));
        }
        let state = state.inc();

        let (types, state) = match provides_types().parse(arena, state.clone(), min_indent) {
            Ok((_, out, state)) => (Some(out), state),
            _ => (None, state),
        };

        let (_, to_keyword, state) = spaces_around_keyword(
            ToKeyword,
            EProvides::To,
            EProvides::IndentTo,
            EProvides::IndentListStart,
        )
        .parse(arena, state, min_indent)?;

        let to_pos = state.pos();
        let (to, state) = provides_to_package(arena, state, min_indent)?;
        let to = state.loc(to_pos, to);

        let provides_to = ProvidesTo {
            provides_keyword,
            entries,
            types,
            to_keyword,
            to,
        };
        Ok((MadeProgress, provides_to, state))
    })
    .trace("provides_to")
}

fn provides_exposed<'a>() -> impl Parser<
    'a,
    KeywordItem<'a, ProvidesKeyword, Collection<'a, Loc<Spaced<'a, ExposedName<'a>>>>>,
    EProvides<'a>,
> {
    move |arena: &'a bumpalo::Bump, state: State<'a>, min_indent: u32| {
        let (_, keyword, state) = spaces_around_keyword(
            ProvidesKeyword,
            EProvides::Provides,
            EProvides::IndentProvides,
            EProvides::IndentListStart,
        )
        .parse(arena, state, min_indent)?;

        if state.bytes().first() != Some(&b'[') {
            return Err((NoProgress, EProvides::ListStart(state.pos())));
        }
        let state = state.inc();
        let (item, state) = collection_inner(arena, state, provides_ident, Spaced::SpaceBefore)?;

        if state.bytes().first() != Some(&b']') {
            return Err((MadeProgress, EProvides::ListEnd(state.pos())));
        }
        let state = state.inc();

        let keyword_item = KeywordItem { keyword, item };
        Ok((MadeProgress, keyword_item, state))
    }
}

fn provides_types<'a>(
) -> impl Parser<'a, Collection<'a, Loc<Spaced<'a, UppercaseIdent<'a>>>>, EProvides<'a>> {
    move |arena: &'a bumpalo::Bump, mut state: State<'a>, _: u32| {
        // We only support spaces here, not newlines, because this is not intended
        // to be the design forever. Someday it will hopefully work like Elm,
        // where platform authors can provide functions like Browser.sandbox which
        // present an API based on ordinary-looking type variables.
        let mut p = NoProgress;
        while state.bytes().first() == Some(&b' ') {
            state.inc_mut();
            p = MadeProgress;
        }

        if state.bytes().first() != Some(&b'{') {
            return Err((p, EProvides::ListStart(state.pos())));
        }
        state.inc_mut();

        let elem_p = move |_, state: State<'a>| {
            let start = state.pos();
            ident::uppercase(state).map_err(|p| (p, EProvides::Identifier(start)))
        };
        let (idents, state) = collection_inner(arena, state, elem_p, Spaced::SpaceBefore)?;

        if state.bytes().first() != Some(&b'}') {
            return Err((MadeProgress, EProvides::ListEnd(state.pos())));
        }
        Ok((MadeProgress, idents, state.inc()))
    }
}

fn provides_ident<'a>(
    _: &'a bumpalo::Bump,
    state: State<'a>,
) -> Result<(Loc<Spaced<'a, ExposedName<'a>>>, State<'a>), (Progress, EProvides<'a>)> {
    let ident_pos = state.pos();
    match parse_anycase_ident(state) {
        Ok((ident, state)) => {
            let ident = Spaced::Item(ExposedName::new(ident));
            Ok((state.loc(ident_pos, ident), state))
        }
        Err(p) => Err((p, EProvides::Identifier(ident_pos))),
    }
}

fn exposes_ident<'a>(
    _: &'a bumpalo::Bump,
    state: State<'a>,
) -> Result<(Loc<Spaced<'a, ExposedName<'a>>>, State<'a>), (Progress, EExposes)> {
    let ident_pos = state.pos();
    match parse_anycase_ident(state) {
        Ok((ident, state)) => {
            let ident = Spaced::Item(ExposedName::new(ident));
            Ok((state.loc(ident_pos, ident), state))
        }
        Err(p) => Err((p, EExposes::Identifier(ident_pos))),
    }
}

fn imports_ident<'a>(
    _: &'a bumpalo::Bump,
    state: State<'a>,
) -> Result<(Loc<Spaced<'a, ExposedName<'a>>>, State<'a>), (Progress, EImports)> {
    let ident_pos = state.pos();
    match parse_anycase_ident(state) {
        Ok((ident, state)) => {
            let ident = Spaced::Item(ExposedName::new(ident));
            Ok((state.loc(ident_pos, ident), state))
        }
        Err(p) => Err((p, EImports::Identifier(ident_pos))),
    }
}

fn requires<'a>(
) -> impl Parser<'a, KeywordItem<'a, RequiresKeyword, PlatformRequires<'a>>, ERequires<'a>> {
    move |arena: &'a bumpalo::Bump, state: State<'a>, min_indent: u32| {
        let (_, keyword, state) = spaces_around_keyword(
            RequiresKeyword,
            ERequires::Requires,
            ERequires::IndentRequires,
            ERequires::IndentListStart,
        )
        .parse(arena, state, min_indent)?;

        if state.bytes().first() != Some(&b'{') {
            return Err((NoProgress, ERequires::ListStart(state.pos())));
        }
        let state = state.inc();

        let elem_p = move |_, state: State<'a>| {
            let start = state.pos();
            ident::uppercase(state).map_err(|p| (p, ERequires::Rigid(start)))
        };
        let (rigids, state) = collection_inner(arena, state, elem_p, Spaced::SpaceBefore)?;

        if state.bytes().first() != Some(&b'}') {
            return Err((MadeProgress, ERequires::ListEnd(state.pos())));
        }
        let state = state.inc();

        let (_, _, state) = eat_nc_check(ERequires::ListStart, arena, state, min_indent, true)?;

        if state.bytes().first() != Some(&b'{') {
            return Err((NoProgress, ERequires::ListStart(state.pos())));
        }
        let state = state.inc();

        let elem_p = move |arena: &'a bumpalo::Bump, state: State<'a>| {
            let start = state.pos();
            match parse_typed_ident(start, arena, state) {
                Ok((ident, state)) => Ok((state.loc(start, ident), state)),
                Err((p, fail)) => Err((p, ERequires::TypedIdent(fail, start))),
            }
        };
        let (signatures, state) = collection_inner(arena, state, elem_p, Spaced::SpaceBefore)?;

        if state.bytes().first() != Some(&b'}') {
            return Err((MadeProgress, ERequires::ListEnd(state.pos())));
        }
        let state = state.inc();

        let item = PlatformRequires { rigids, signatures };
        let keyword_item = KeywordItem { keyword, item };
        Ok((MadeProgress, keyword_item, state))
    }
}

#[inline(always)]
fn exposes_kw<'a>() -> impl Parser<'a, Spaces<'a, ExposesKeyword>, EExposes> {
    spaces_around_keyword(
        ExposesKeyword,
        EExposes::Exposes,
        EExposes::IndentExposes,
        EExposes::IndentListStart,
    )
}

fn exposes_list<'a>() -> impl Parser<'a, Collection<'a, Loc<Spaced<'a, ExposedName<'a>>>>, EExposes>
{
    move |arena: &'a bumpalo::Bump, state: State<'a>, _: u32| {
        if state.bytes().first() != Some(&b'[') {
            return Err((NoProgress, EExposes::ListStart(state.pos())));
        }
        let state = state.inc();
        let (entries, state) = collection_inner(arena, state, exposes_ident, Spaced::SpaceBefore)?;

        if state.bytes().first() != Some(&b']') {
            return Err((MadeProgress, EExposes::ListEnd(state.pos())));
        }
        Ok((MadeProgress, entries, state.inc()))
    }
}

pub fn spaces_around_keyword<'a, K: Keyword, E>(
    item: K,
    expectation: fn(Position) -> E,
    indent_problem1: fn(Position) -> E,
    indent_problem2: fn(Position) -> E,
) -> impl Parser<'a, Spaces<'a, K>, E>
where
    E: 'a + SpaceProblem,
{
    move |arena: &'a bumpalo::Bump, state: State<'a>, min_indent: u32| {
        let (_, before, state) =
            match eat_nc_check(indent_problem1, arena, state, min_indent, false) {
                Ok(ok) => ok,
                Err((_, fail)) => return Err((NoProgress, fail)),
            };

        if !at_keyword(K::KEYWORD, &state) {
            return Err((NoProgress, expectation(state.pos())));
        }
        let state = state.inc_len(K::KEYWORD);

        let (_, after, state) = eat_nc_check(indent_problem2, arena, state, min_indent, false)?;

        let spaced_keyword = Spaces {
            before,
            item,
            after,
        };
        Ok((MadeProgress, spaced_keyword, state))
    }
}

#[inline(always)]
fn exposes_modules<'a>() -> impl Parser<
    'a,
    KeywordItem<'a, ExposesKeyword, Collection<'a, Loc<Spaced<'a, ModuleName<'a>>>>>,
    EExposes,
> {
    record!(KeywordItem {
        keyword: spaces_around_keyword(
            ExposesKeyword,
            EExposes::Exposes,
            EExposes::IndentExposes,
            EExposes::IndentListStart
        ),
        item: exposes_module_collection(),
    })
}

fn exposes_module_collection<'a>(
) -> impl Parser<'a, Collection<'a, Loc<Spaced<'a, ModuleName<'a>>>>, EExposes> {
    move |arena: &'a bumpalo::Bump, state: State<'a>, _: u32| {
        if state.bytes().first() != Some(&b'[') {
            return Err((NoProgress, EExposes::ListStart(state.pos())));
        }
        let state = state.inc();

        let elem_p = move |_: &'a bumpalo::Bump, state: State<'a>| {
            let start = state.pos();
            match chomp_module_name(state.bytes()) {
                Ok(name) => {
                    let state = state.inc_len(name);
                    let name = state.loc(start, Spaced::Item(ModuleName::new(name)));
                    Ok((name, state))
                }
                Err(p) => Err((p, EExposes::Identifier(start))),
            }
        };
        let (items, state) = collection_inner(arena, state, elem_p, Spaced::SpaceBefore)?;

        if state.bytes().first() != Some(&b']') {
            return Err((MadeProgress, EExposes::ListEnd(state.pos())));
        }
        Ok((MadeProgress, items, state.inc()))
    }
}

#[inline(always)]
fn packages<'a>() -> impl Parser<
    'a,
    KeywordItem<'a, PackagesKeyword, Collection<'a, Loc<Spaced<'a, PackageEntry<'a>>>>>,
    EPackages<'a>,
> {
    record!(KeywordItem {
        keyword: packages_kw(),
        item: packages_collection()
    })
}

#[inline(always)]
fn packages_kw<'a>() -> impl Parser<'a, Spaces<'a, PackagesKeyword>, EPackages<'a>> {
    spaces_around_keyword(
        PackagesKeyword,
        EPackages::Packages,
        EPackages::IndentPackages,
        EPackages::IndentListStart,
    )
}

#[inline(always)]
fn packages_collection<'a>(
) -> impl Parser<'a, Collection<'a, Loc<Spaced<'a, PackageEntry<'a>>>>, EPackages<'a>> {
    move |arena: &'a bumpalo::Bump, state: State<'a>, _: u32| {
        if state.bytes().first() != Some(&b'{') {
            return Err((NoProgress, EPackages::ListStart(state.pos())));
        }
        let state = state.inc();

        let elem_p = move |arena: &'a bumpalo::Bump, state: State<'a>| {
            let start = state.pos();
            match parse_package_entry(arena, state) {
                Ok((out, state)) => Ok((state.loc(start, out), state)),
                Err((p, fail)) => Err((p, EPackages::PackageEntry(fail, start))),
            }
        };
        let (entries, state) = collection_inner(arena, state, elem_p, Spaced::SpaceBefore)?;

        if state.bytes().first() != Some(&b'}') {
            return Err((MadeProgress, EPackages::ListEnd(state.pos())));
        }
        Ok((MadeProgress, entries, state.inc()))
    }
}

#[inline(always)]
fn imports<'a>() -> impl Parser<
    'a,
    KeywordItem<'a, ImportsKeyword, Collection<'a, Loc<Spaced<'a, ImportsEntry<'a>>>>>,
    EImports,
> {
    move |arena: &'a bumpalo::Bump, state: State<'a>, min_indent: u32| {
        let (_, keyword, state) = spaces_around_keyword(
            ImportsKeyword,
            EImports::Imports,
            EImports::IndentImports,
            EImports::IndentListStart,
        )
        .parse(arena, state, min_indent)?;

        if state.bytes().first() != Some(&b'[') {
            return Err((NoProgress, EImports::ListStart(state.pos())));
        }
        let state = state.inc();
        let (item, state) = collection_inner(arena, state, imports_entry, Spaced::SpaceBefore)?;

        if state.bytes().first() != Some(&b']') {
            return Err((MadeProgress, EImports::ListEnd(state.pos())));
        }
        let state = state.inc();

        let keyword_item = KeywordItem { keyword, item };
        Ok((MadeProgress, keyword_item, state))
    }
}

/// e.g. printLine : Str -> Effect {}
pub fn parse_typed_ident<'a>(
    start: Position,
    arena: &'a bumpalo::Bump,
    state: State<'a>,
) -> Result<(Spaced<'a, TypedIdent<'a>>, State<'a>), (Progress, ETypedIdent<'a>)> {
    let (ident, state) =
        parse_lowercase_ident(state).map_err(|p| (p, ETypedIdent::Identifier(start)))?;
    let ident = state.loc(start, ident);

    let (_, spaces_before_colon, state) =
        eat_nc_check(ETypedIdent::IndentHasType, arena, state, 0, true)?;

    if state.bytes().first() != Some(&b':') {
        return Err((MadeProgress, ETypedIdent::HasType(state.pos())));
    }
    let state = state.inc();

    let (_, spaces_after_colon, state) =
        eat_nc_check(ETypedIdent::IndentType, arena, state, 0, true)?;

    let ann_pos = state.pos();
    match parse_type_expr(
        TRAILING_COMMA_VALID | SKIP_PARSING_SPACES_BEFORE,
        arena,
        state,
        0,
    ) {
        Ok((ann, state)) => {
            let typed_ident = Spaced::Item(TypedIdent {
                ident,
                spaces_before_colon,
                ann: ann.spaced_before(arena, spaces_after_colon),
            });
            Ok((typed_ident, state))
        }
        Err((_, fail)) => Err((MadeProgress, ETypedIdent::Type(fail, ann_pos))),
    }
}

fn imports_entry<'a>(
    arena: &'a bumpalo::Bump,
    state: State<'a>,
) -> Result<(Loc<Spaced<'a, ImportsEntry<'a>>>, State<'a>), (Progress, EImports)> {
    let start = state.pos();
    let p_name_module_name = move |state: State<'a>| {
        let (name, state) = match parse_lowercase_ident(state.clone()) {
            Ok((name, state)) => {
                if state.bytes().first() == Some(&b'.') {
                    (Some(name), state.inc())
                } else {
                    (None, state)
                }
            }
            Err(_) => (None, state),
        };

        let pos = state.pos();
        match parse_module_name(state) {
            Ok((module_name, state)) => Ok((MadeProgress, (name, module_name), state)),
            Err(p) => Err((p, EImports::ModuleName(pos))),
        }
    };

    // e.g. `.{ Task, after}`
    let p_opt_values = move |arena: &'a bumpalo::Bump, state: State<'a>| {
        if state.bytes().first() != Some(&b'.') {
            return Ok((NoProgress, Collection::empty(), state));
        }
        let state = state.inc();

        if state.bytes().first() != Some(&b'{') {
            return Err((MadeProgress, EImports::SetStart(state.pos())));
        }
        let state = state.inc();
        let (opt_values, state) =
            collection_inner(arena, state, imports_ident, Spaced::SpaceBefore)?;

        if state.bytes().first() != Some(&b'}') {
            return Err((MadeProgress, EImports::SetEnd(state.pos())));
        }
        Ok((MadeProgress, opt_values, state.inc()))
    };

    match p_name_module_name(state.clone()) {
        Err((NoProgress, _)) => { /*goto below */ }
        Err(err) => return Err(err),
        Ok((_, (opt_shortname, module_name), state)) => match p_opt_values(arena, state) {
            Err((_, fail)) => return Err((MadeProgress, fail)),
            Ok((_, opt_values, state)) => {
                let entry = match opt_shortname {
                    Some(shortname) => ImportsEntry::Package(shortname, module_name, opt_values),
                    None => ImportsEntry::Module(module_name, opt_values),
                };
                return Ok((state.loc(start, Spaced::Item(entry)), state));
            }
        },
    };

    // e.g. "filename"
    // TODO: str literal allows for multiline strings. We probably don't want that for file names.
    let file_name_pos = state.pos();
    let (_, file_name, state) = match parse_str_literal().parse(arena, state, 0) {
        Ok(ok) => ok,
        Err((p, _)) => return Err((p, EImports::StrLiteral(file_name_pos))),
    };

    let (.., state) = eat_nc_check(EImports::AsKeyword, arena, state, 0, true)?;
    if !state.bytes().starts_with(b"as") {
        return Err((MadeProgress, EImports::AsKeyword(state.pos())));
    }
    let state = state.advance(2);
    let (.., state) = eat_nc_check(EImports::AsKeyword, arena, state, 0, true)?;

    // e.g. file : Str
    let ident_pos = state.pos();
    let (typed_ident, state) = parse_typed_ident(ident_pos, arena, state)
        .map_err(|(p, _)| (p, EImports::TypedIdent(ident_pos)))?;

    // TODO: look at blacking block strings during parsing.
    let entry = Spaced::Item(ImportsEntry::IngestedFile(file_name, typed_ident));
    Ok((state.loc(start, entry), state))
}

impl<'a> HeaderType<'a> {
    pub fn exposed_or_provided_values(&'a self) -> &'a [Loc<ExposedName<'a>>] {
        match self {
            HeaderType::App {
                provides: exposes, ..
            }
            | HeaderType::Hosted { exposes, .. }
            | HeaderType::Builtin { exposes, .. }
            | HeaderType::Module { exposes, .. } => exposes,
            HeaderType::Platform { .. } | HeaderType::Package { .. } => &[],
        }
    }
    pub fn to_string(&'a self) -> &str {
        match self {
            HeaderType::App { .. } => "app",
            HeaderType::Hosted { .. } => "hosted",
            HeaderType::Builtin { .. } => "builtin",
            HeaderType::Package { .. } => "package",
            HeaderType::Platform { .. } => "platform",
            HeaderType::Module { .. } => "module",
        }
    }
}

#[derive(Debug)]
pub enum HeaderType<'a> {
    App {
        provides: &'a [Loc<ExposedName<'a>>],
        to_platform: To<'a>,
    },
    Hosted {
        name: ModuleName<'a>,
        exposes: &'a [Loc<ExposedName<'a>>],
    },
    /// Only created during canonicalization, never actually parsed from source
    Builtin {
        name: ModuleName<'a>,
        exposes: &'a [Loc<ExposedName<'a>>],
        opt_params: Option<ModuleParams<'a>>,
    },
    Package {
        /// usually something other than `pf`
        config_shorthand: &'a str,
        exposes: &'a [Loc<ModuleName<'a>>],
        exposes_ids: &'a [ModuleId],
    },
    Platform {
        opt_app_module_id: Option<ModuleId>,
        /// the name and type scheme of the main function (required by the platform)
        /// (type scheme is currently unused)
        provides: &'a [Loc<ExposedName<'a>>],
        requires: &'a [Loc<TypedIdent<'a>>],
        requires_types: &'a [Loc<UppercaseIdent<'a>>],
        exposes: &'a [Loc<ModuleName<'a>>],
        exposes_ids: &'a [ModuleId],

        /// usually `pf`
        config_shorthand: &'a str,
    },
    Module {
        name: ModuleName<'a>,
        exposes: &'a [Loc<ExposedName<'a>>],
        opt_params: Option<ModuleParams<'a>>,
    },
}

impl<'a> HeaderType<'a> {
    pub fn get_name(self) -> Option<&'a str> {
        match self {
            Self::Module { name, .. } | Self::Builtin { name, .. } | Self::Hosted { name, .. } => {
                Some(name.into())
            }
            Self::Platform {
                config_shorthand: name,
                ..
            }
            | Self::Package {
                config_shorthand: name,
                ..
            } => Some(name),
            Self::App { .. } => {
                //TODO:Eli This can be removed once module params is implemented and app names are no longer strings
                None
            }
        }
    }

    pub fn get_params(&self) -> &Option<ModuleParams<'a>> {
        match self {
            Self::Module {
                opt_params,
                name: _,
                exposes: _,
            }
            | Self::Builtin {
                opt_params,
                name: _,
                exposes: _,
            } => opt_params,
            Self::App {
                provides: _,
                to_platform: _,
            }
            | Self::Package {
                config_shorthand: _,
                exposes: _,
                exposes_ids: _,
            }
            | Self::Hosted {
                name: _,
                exposes: _,
            }
            | Self::Platform {
                opt_app_module_id: _,
                provides: _,
                requires: _,
                requires_types: _,
                exposes: _,
                exposes_ids: _,
                config_shorthand: _,
            } => &None,
        }
    }

    pub fn to_maybe_builtin(self, module_id: ModuleId) -> Self {
        match self {
            HeaderType::Module {
                name,
                exposes,
                opt_params,
            } if module_id.is_builtin() => HeaderType::Builtin {
                name,
                exposes,
                opt_params,
            },
            _ => self,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub enum Version<'a> {
    Exact(&'a str),
    Range {
        min: &'a str,
        min_comparison: VersionComparison,
        max: &'a str,
        max_comparison: VersionComparison,
    },
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub enum VersionComparison {
    AllowsEqual,
    DisallowsEqual,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct PackageName<'a>(&'a str);

impl<'a> PackageName<'a> {
    pub fn to_str(self) -> &'a str {
        self.0
    }

    pub fn as_str(&self) -> &'a str {
        self.0
    }
}

impl<'a> From<PackageName<'a>> for &'a str {
    fn from(name: PackageName<'a>) -> &'a str {
        name.0
    }
}

impl<'a> From<&'a str> for PackageName<'a> {
    fn from(string: &'a str) -> Self {
        Self(string)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub struct ModuleName<'a>(&'a str);

impl<'a> From<ModuleName<'a>> for &'a str {
    fn from(name: ModuleName<'a>) -> Self {
        name.0
    }
}

impl<'a> From<ModuleName<'a>> for roc_module::ident::ModuleName {
    fn from(name: ModuleName<'a>) -> Self {
        name.0.into()
    }
}

impl<'a> ModuleName<'a> {
    const MODULE_SEPARATOR: char = '.';

    pub const fn new(name: &'a str) -> Self {
        ModuleName(name)
    }

    pub const fn as_str(&self) -> &'a str {
        self.0
    }

    pub fn parts(&'a self) -> impl DoubleEndedIterator<Item = &'a str> {
        self.0.split(Self::MODULE_SEPARATOR)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub struct ExposedName<'a>(&'a str);

impl<'a> From<ExposedName<'a>> for &'a str {
    fn from(name: ExposedName<'a>) -> Self {
        name.0
    }
}

impl<'a> ExposedName<'a> {
    pub const fn new(name: &'a str) -> Self {
        ExposedName(name)
    }

    pub fn as_str(&'a self) -> &'a str {
        self.0
    }

    pub fn is_effectful_fn(&self) -> bool {
        IdentSuffix::from_name(self.0).is_bang()
    }
}

pub trait Keyword: Copy + Clone + Debug {
    const KEYWORD: &'static str;
}

macro_rules! keywords {
    ($($name:ident => $string:expr),* $(,)?) => {
        $(
            #[derive(Copy, Clone, PartialEq, Eq, Debug)]
            pub struct $name;

            impl Keyword for $name {
                const KEYWORD: &'static str = $string;
            }
        )*
    }
}

keywords! {
    ExposesKeyword => "exposes",
    PackageKeyword => "package",
    PackagesKeyword => "packages",
    RequiresKeyword => "requires",
    ProvidesKeyword => "provides",
    ToKeyword => "to",
    PlatformKeyword => "platform",
    // Deprecated
    ImportsKeyword => "imports",
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct KeywordItem<'a, K, V> {
    pub keyword: Spaces<'a, K>,
    pub item: V,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ModuleHeader<'a> {
    pub after_keyword: &'a [CommentOrNewline<'a>],
    pub params: Option<ModuleParams<'a>>,
    pub exposes: Collection<'a, Loc<Spaced<'a, ExposedName<'a>>>>,

    // Keeping this so we can format old interface header into module headers
    pub interface_imports: Option<KeywordItem<'a, ImportsKeyword, ImportsCollection<'a>>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ModuleParams<'a> {
    pub pattern: Loc<Collection<'a, Loc<Pattern<'a>>>>,
    pub before_arrow: &'a [CommentOrNewline<'a>],
    pub after_arrow: &'a [CommentOrNewline<'a>],
}

pub type ImportsKeywordItem<'a> = KeywordItem<'a, ImportsKeyword, ImportsCollection<'a>>;
pub type ImportsCollection<'a> = Collection<'a, Loc<Spaced<'a, ImportsEntry<'a>>>>;

#[derive(Clone, Debug, PartialEq)]
pub struct HostedHeader<'a> {
    pub before_name: &'a [CommentOrNewline<'a>],
    pub name: Loc<ModuleName<'a>>,
    pub exposes: KeywordItem<'a, ExposesKeyword, Collection<'a, Loc<Spaced<'a, ExposedName<'a>>>>>,

    pub imports: KeywordItem<'a, ImportsKeyword, Collection<'a, Loc<Spaced<'a, ImportsEntry<'a>>>>>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum To<'a> {
    ExistingPackage(&'a str),
    NewPackage(PackageName<'a>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct AppHeader<'a> {
    pub before_provides: &'a [CommentOrNewline<'a>],
    pub provides: Collection<'a, Loc<Spaced<'a, ExposedName<'a>>>>,
    pub before_packages: &'a [CommentOrNewline<'a>],
    pub packages: Loc<Collection<'a, Loc<Spaced<'a, PackageEntry<'a>>>>>,
    // Old header pieces
    pub old_imports: Option<KeywordItem<'a, ImportsKeyword, ImportsCollection<'a>>>,
    pub old_provides_to_new_package: Option<PackageName<'a>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ProvidesTo<'a> {
    pub provides_keyword: Spaces<'a, ProvidesKeyword>,
    pub entries: Collection<'a, Loc<Spaced<'a, ExposedName<'a>>>>,
    pub types: Option<Collection<'a, Loc<Spaced<'a, UppercaseIdent<'a>>>>>,

    pub to_keyword: Spaces<'a, ToKeyword>,
    pub to: Loc<To<'a>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct PackageHeader<'a> {
    pub before_exposes: &'a [CommentOrNewline<'a>],
    pub exposes: Collection<'a, Loc<Spaced<'a, ModuleName<'a>>>>,
    pub before_packages: &'a [CommentOrNewline<'a>],
    pub packages: Loc<Collection<'a, Loc<Spaced<'a, PackageEntry<'a>>>>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct PlatformRequires<'a> {
    pub rigids: Collection<'a, Loc<Spaced<'a, UppercaseIdent<'a>>>>,
    pub signatures: Collection<'a, Loc<Spaced<'a, TypedIdent<'a>>>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct PlatformHeader<'a> {
    pub before_name: &'a [CommentOrNewline<'a>],
    pub name: Loc<PackageName<'a>>,

    pub requires: KeywordItem<'a, RequiresKeyword, PlatformRequires<'a>>,
    pub exposes: KeywordItem<'a, ExposesKeyword, Collection<'a, Loc<Spaced<'a, ModuleName<'a>>>>>,
    pub packages:
        KeywordItem<'a, PackagesKeyword, Collection<'a, Loc<Spaced<'a, PackageEntry<'a>>>>>,
    pub imports: KeywordItem<'a, ImportsKeyword, Collection<'a, Loc<Spaced<'a, ImportsEntry<'a>>>>>,
    pub provides:
        KeywordItem<'a, ProvidesKeyword, Collection<'a, Loc<Spaced<'a, ExposedName<'a>>>>>,
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum ImportsEntry<'a> {
    /// e.g. `Hello` or `Hello exposing [hello]` see roc-lang.org/examples/MultipleRocFiles/README.html
    Module(
        ModuleName<'a>,
        Collection<'a, Loc<Spaced<'a, ExposedName<'a>>>>,
    ),

    /// e.g. `pf.Stdout` or `pf.Stdout exposing [line]`
    Package(
        &'a str,
        ModuleName<'a>,
        Collection<'a, Loc<Spaced<'a, ExposedName<'a>>>>,
    ),

    /// e.g "path/to/my/file.txt" as myFile : Str
    IngestedFile(StrLiteral<'a>, Spaced<'a, TypedIdent<'a>>),
}

/// e.g.
///
/// printLine : Str -> Result {} *
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct TypedIdent<'a> {
    pub ident: Loc<&'a str>,
    pub spaces_before_colon: &'a [CommentOrNewline<'a>],
    pub ann: Loc<TypeAnnotation<'a>>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct PackageEntry<'a> {
    pub shorthand: &'a str,
    pub spaces_after_shorthand: &'a [CommentOrNewline<'a>],
    pub platform_marker: Option<&'a [CommentOrNewline<'a>]>,
    pub package_name: Loc<PackageName<'a>>,
}

pub fn parse_package_entry<'a>(
    arena: &'a bumpalo::Bump,
    state: State<'a>,
) -> Result<(Spaced<'a, PackageEntry<'a>>, State<'a>), (Progress, EPackageEntry<'a>)> {
    let shorthand_p = move |arena: &'a bumpalo::Bump, state: State<'a>| {
        let ident_pos = state.pos();
        let (ident, state) = match parse_lowercase_ident(state.clone()) {
            Ok(ok) => ok,
            Err(NoProgress) => return Ok((NoProgress, None, state)),
            Err(_) => return Err((MadeProgress, EPackageEntry::Shorthand(ident_pos))),
        };

        let (_, spaces_before_colon, state) =
            eat_nc_check(EPackageEntry::IndentPackage, arena, state, 0, true)?;

        if state.bytes().first() != Some(&b':') {
            return Err((MadeProgress, EPackageEntry::Colon(state.pos())));
        }
        let state = state.inc();

        let (_, spaces_after_colon, state) =
            eat_nc_check(EPackageEntry::IndentPackage, arena, state, 0, true)?;

        let out = ((ident, spaces_before_colon), spaces_after_colon);
        Ok((MadeProgress, Some(out), state))
    };

    let plat_parser = move |arena: &'a bumpalo::Bump, state: State<'a>| {
        let olds = state.clone();
        let (p, sp, state) = if at_keyword(crate::keyword::PLATFORM, &state) {
            let state = state.inc_len(crate::keyword::PLATFORM);
            let (_, sp, state) = eat_nc_check(EPackageEntry::IndentPackage, arena, state, 0, true)?;
            (MadeProgress, Some(sp), state)
        } else {
            (NoProgress, None, olds)
        };

        let name_pos = state.pos();
        match package_name().parse(arena, state, 0) {
            Ok((_, name, state)) => Ok(((sp, state.loc(name_pos, name)), state)),
            Err((p2, fail)) => Err((p2.or(p), EPackageEntry::BadPackage(fail, name_pos))),
        }
    };

    let (p, opt_shorthand, state) = shorthand_p(arena, state)?;

    let ((platform_marker, package_or_path), state) = match plat_parser(arena, state) {
        Ok(ok) => ok,
        Err((p2, fail)) => return Err((p2.or(p), fail)),
    };

    let entry = match opt_shorthand {
        Some(((shorthand, spaces_before_colon), spaces_after_colon)) => PackageEntry {
            shorthand,
            spaces_after_shorthand: merge_spaces(arena, spaces_before_colon, spaces_after_colon),
            platform_marker,
            package_name: package_or_path,
        },
        None => PackageEntry {
            shorthand: "",
            spaces_after_shorthand: &[],
            platform_marker,
            package_name: package_or_path,
        },
    };

    Ok((Spaced::Item(entry), state))
}

pub fn package_name<'a>() -> impl Parser<'a, PackageName<'a>, EPackageName<'a>> {
    move |arena: &'a bumpalo::Bump, state: State<'a>, min_indent: u32| {
        let pos = state.pos();
        match string_literal::parse_str_literal().parse(arena, state, min_indent) {
            Ok((p, name, state)) => match name {
                StrLiteral::PlainLine(text) => Ok((p, PackageName(text), state)),
                StrLiteral::Line(_) => Err((p, EPackageName::Escapes(pos))),
                StrLiteral::Block(_) => Err((p, EPackageName::Multiline(pos))),
            },
            Err((p, fail)) => Err((p, EPackageName::BadPath(fail, pos))),
        }
    }
}

impl<'a, K, V> Malformed for KeywordItem<'a, K, V>
where
    K: Malformed,
    V: Malformed,
{
    fn is_malformed(&self) -> bool {
        self.keyword.is_malformed() || self.item.is_malformed()
    }
}

impl<'a> Malformed for ModuleHeader<'a> {
    fn is_malformed(&self) -> bool {
        false
    }
}

impl<'a> Malformed for HostedHeader<'a> {
    fn is_malformed(&self) -> bool {
        false
    }
}

impl<'a> Malformed for AppHeader<'a> {
    fn is_malformed(&self) -> bool {
        false
    }
}

impl<'a> Malformed for PackageHeader<'a> {
    fn is_malformed(&self) -> bool {
        false
    }
}

impl<'a> Malformed for PlatformRequires<'a> {
    fn is_malformed(&self) -> bool {
        self.signatures.items.iter().any(|x| x.is_malformed())
    }
}

impl<'a> Malformed for PlatformHeader<'a> {
    fn is_malformed(&self) -> bool {
        false
    }
}

impl<'a> Malformed for TypedIdent<'a> {
    fn is_malformed(&self) -> bool {
        self.ann.is_malformed()
    }
}
