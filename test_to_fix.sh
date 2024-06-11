#!/usr/bin/bash

# 
cargo test -p roc_load --test test_reporting

# run a single test
cargo test -p repl_test --lib tests::issue_2818 -- --show-output
cargo test --release -p repl_test --lib tests::issue_2818 -- --show-output
