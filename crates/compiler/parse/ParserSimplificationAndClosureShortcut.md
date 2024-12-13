# Simplify Parser and add closure shortcut features

## Initial intent

I wanted to add a fun feature, a syntax sugar for the closure of single argument with pipe, 
where this code `\|> Num.add 2` means `\x -> x |> Num.add 2`.

To identify the place where I can add the feature, I have started from the parser.
My debugging experience with Roc parser was miserable. TL;DR; too many nested calls, closures, and macros.
So I've started to unwind the Parser from the original `closure_help` function and ended up with this PR :-)

## Goals

### Done

- [x] Simplify Parser for performance, debug-ability and addition of the new features
- [x] Implement closure shortcut for all Binary operators
- [x] Implement reformat to full closure form guided by the space after slash `\ -`
- [x] Implement closure shortcut for the field and tuple access, e.g. `\.foo`, `\.foo.bar` or `\.0.buzz`. Note: consider how this functionality adds-up to the current RecordAccessor `.foo { foo: 3 }` and RecordUpdater `&foo { foo: 1 } 42 ` functions.
- [x] Implement shortcut for identity function `i -> i`, via `\.`
- [x] Implement `x ~ ...` binary operator for the pattern matching `when x is ...` 
- [x] Implement closure shortcut for the `when` pattern matching using the `~` operator via `\~`
- [x] Generate unique names for the parameter in closure shortcut, because Roc does not support shadowing yet
- [x] Implement shortcut for Unary Negate and Not operators in a form of `\-.` and `\!.` This syntax should be composable with the record/tuple field access, e.g. `\!.foo.bar`, `\-.a + y.b`, etc.
- [x] Fix all @fixme
- [x] Complete or convert all @wip

### Further

- [x] Replace and remove the remaining Parser combinators and their tracing code
- [ ] Think how to optimize the Parser further. Do the low-hanging things. Mark potential places with `todo: @perf`
- [ ] Implement one liner for the `when` pattern matching `x ~ (Some "abc" -> 42, None -> 0)` 


## PR does not

It is not a serious optimization of the parser. 

I was refactoring and moving existing parts around, removing what become redundant in the process. 

Mmm, OK. I did a small optimization/non-pessimization (TM) using the opportunities emerging from the inlining and replacing the combinators with the direct function calls. For example, `parse_term` checks the first character before calling the appropriate parsing function for the rest of the input.

## PR does

- Features. See in the corresponding section below. Features implementation is localized in the Parser and for the small bits in the Formatter. This simplifies **removing or splitting them from this PR**.
- Simplifies Parser by removing closures, macros, deep call chains, unused code, wrapping and unwrapping the results between abstraction layers. For me personally, it  simplified the debugging and code understanding.
- Speeds up compiler compilation because of simpler code and less LOC. I am inlining things and less LOC seems counterintuitive, right? 
- After inlining the leaky abstractions are gone! 
- After inlining, I have found that some errors states were never produced, so the handling of them is unreachable and may be safely removed, e.g. `EClosure::Comma`, `EWhen::Bar`, `EWhen::IfToken`, and many more.
- Removes unnecessary and double checks, a prominent one being mutiple checks if identifier is not a keyword.
- Opens room for the further optimizations, because you colocate things and now see the whole picture (locality of behavior ftw).
- After inlining, the names were adapted from the abstract and general to more concrete and contextual.
- In its current state, the Parser style is not consistent - in one place it is declarative/combinatorial in others it is imperative or mixed (where combinators become complex). This PR removes the most of combinators (and the cost of them), moving toward the pure imperative style, using just functions and calls with minimum macro use.
-  After looking at the inlined invocation I have found repeated **small chunks of infra code**, so I wrapped them in the sugar functions. For example, I have added `spaced_before`, `spaced_around` abstracting the repetition of the same code in many places.

## Parser Benchmarks

`cd ./crates/compiler/parse && cargo bench`  

main branch:

![image](https://github.com/user-attachments/assets/f83ce579-514c-49d8-a565-9df9260f856c)

PR branch:

![image](https://github.com/user-attachments/assets/2e237bd1-a1f1-4706-a9bc-4e1f4cd4bd17)


## New debug experience

Comparing the call-stacks when debugging the test from the test_syntax:
```rust
    #[test]
    fn single_line_string_literal_in_pattern() {
        expr_formats_same(indoc!(
            r#"
            when foo is
                "abc" -> ""
            "#
        ));
    }
```

Breakpoint is on the construction of the AST node for the `WhenBranch`.  

In the main branch (barely fitting on my laptop screen with the smallish font):

![image](https://github.com/user-attachments/assets/39be7546-75da-4320-8449-429846b46610)

In this PR branch:

![image](https://github.com/user-attachments/assets/2dc13990-027a-46fe-9467-404e028f0f32)


## Features

### Closure shortcut for the binary and unary operators, record field and tuple accessors, identity function

It is working for all binary and unary operators, including the Pizza pipe operator `|>` and the new `~` operator for the pattern matching, the record field, tuple accessors and the identity function. 
Plus, those shortcuts are naturally combining, e.g. unary negate with identity and access, then further with the binary operator chain.

Tests for illustration:

```rust
    #[test]
    fn func_call_trailing_lambda_pizza_shortcut() {
        expr_formats_same(indoc!(
            r"
                list = List.map [1, 2, 3] \|> Num.add 1
                list
            "
        ));
    }

    #[test]
    fn func_call_trailing_lambda_plus_shortcut() {
        expr_formats_same(indoc!(
            r"
                list = List.map [1, 2, 3] \+ 1
                list
            "
        ));
    }
    
    #[test]
    fn closure_shortcut_for_when_binop() {
        expr_formats_same(indoc!(
            r#"
            \~
                "abc" -> ""
                _ -> "abc"
            "#
        ));
    }

    #[test]
    fn closure_shortcut_for_tuple_index_access() {
        expr_formats_same(indoc!(
            r"
            \.0
            "
        ));
        expr_formats_same(indoc!(
            r"
            \-.0
            "
        ));
        expr_formats_same(indoc!(
            r"
            \!.0
            "
        ));
    }

    
    #[test]
    fn closure_shortcut_for_field_tuple_index_access() {
        expr_formats_same(indoc!(
            r"
            \.bru.0
            "
        ));
    }

    #[test]
    fn closure_shortcut_for_field_as_part_of_bin_op() {
        expr_formats_same(indoc!(
            r"
            \.foo.bar + 1
            "
        ));
        expr_formats_same(indoc!(
            r"
            \-.foo.bar + 1
            "
        ));
    }

    #[test]
    fn closure_shortcut_for_identity_function() {
        expr_formats_same(indoc!(
            r"
            \.
            "
        ));
    }
    
    #[test]
    fn closure_shortcut_unary_access_with_binop_chain() {
        expr_formats_same(indoc!(
            r#"
            \-.foo.bar + 5 ~
                42 -> ""
                _ -> "42"
            "#
        ));
    }
```

Current implementation changes the Parser to create the same AST for shortcut `\|> bar` as for the normal `\x -> x |> bar`. 
I am still saving the information that the closure is in fact a shortcut via the additional field in `Expr::Closure`.
When the flag is set, the Roc format is adjusted to output the AST in the short form

### User-guided shortcut expansion

By inserting the whitespace after `\` in the closure shortcut, the User indicates the expansion into the full form on the `roc format`:

Say you've typed `\|>` shortcut, then you can put space between opening `\` and `|>` in `\ |> foo` and it will expand into `\x -> x |> foo` on format (automatically with format-on-save and auto-save enabled in the editor). 

- First, it provides a uniform way to understand the shortcut meaning, you may see for yourself by typing space, then removing space to go back to the shortcut form or keep the expanded form.
- Second, the feature may work as a kind of 'editor shortcut' feature. Shortcuts are expanded into the full form while you're typing. Interesting part, that it is supported by the language itself without need for special editor plugins or tooling. IMHO, **it matches the Roc philosophy about tooling in a language**, and personally it is just a fun feature I did not see anywhere else.

Example:
```rust
    #[test]
    fn closure_shortcut_for_tuple_index_access_fmt_expand() {
        expr_formats_to(
            indoc!(
                r"
            \ .0
            "
            ),
            indoc!(
                r"
            \x -> x.0
            "
            ),
        );
        expr_formats_to(
            indoc!(
                r"
            \ -.0
            "
            ),
            indoc!(
                r"
            \x -> -x.0
            "
            ),
        );
        expr_formats_to(
            indoc!(
                r"
            \ !.0
            "
            ),
            indoc!(
                r"
            \x -> !x.0
            "
            ),
        );
    }

   #[test]
    fn closure_shortcut_for_identity_function_format() {
        expr_formats_to(
            indoc!(
                r"
            \ .
            "
            ),
            indoc!(
                r"
            \x -> x
            "
            ),
        );
    }
```

### Binary operator for the when pattern matching

Implemented as `~` symbol, which is not yet used by the other features.
The difference from the `|>` is that it should be the last in the chain of the binary operators.

```rust
    #[test]
    fn basic_pattern_binop() {
        expr_formats_same(indoc!(
            r#"
            foo ~
                "abc" -> ""
                _ -> "abc"
            "#
        ));
    }

    #[test]
    fn pattern_binop_with_operator_chain_equivalents() {
        expr_formats_same(indoc!(
            r#"
            a + b + c ~
                42 -> ""
                _ -> "42"
            "#
        ));
        expr_formats_same(indoc!(
            r#"
            (a + b + c)~
                42 -> ""
                _ -> "42"
            "#
        ));
    }
```
