use criterion::{criterion_group, criterion_main, Criterion};
use rand::{distributions::Alphanumeric, Rng};
use roc_parse::keyword::{match_keyword, smart_match_keyword, smart_match_keyword2, KEYWORDS};
use std::collections::HashMap;

fn generate_random_names(count: usize, min_len: usize, max_len: usize) -> Vec<String> {
    let rng = rand::thread_rng();
    (0..count)
        .map(|_| {
            let len = rng.clone().gen_range(min_len..=max_len);
            rng.clone()
                .sample_iter(&Alphanumeric)
                .take(len)
                .map(char::from)
                .collect()
        })
        .collect()
}

fn bench_keyword_lookup(c: &mut Criterion) {
    let hashmap: HashMap<&str, &str> = KEYWORDS.iter().map(|&kw| (kw, kw)).collect();

    let random_names = generate_random_names(100, 1, 16);
    for n in random_names.iter() {
        assert!(KEYWORDS.iter().all(|&kw| kw != *n));
    }

    let inputs: Vec<&str> = KEYWORDS
        .iter()
        .cloned()
        .chain(random_names.iter().map(|s| s.as_str()))
        .collect();

    let mut group = c.benchmark_group("keyword_lookup");

    group.bench_function("iter_any", |b| {
        b.iter(|| {
            let mut kw_count = 0;
            let mut non_kw_count = 0;
            for i in inputs.iter() {
                if KEYWORDS.iter().any(|&kw| *i == kw) {
                    kw_count += 1;
                } else {
                    non_kw_count += 1;
                }
            }
            assert_eq!((kw_count, non_kw_count), (11, 100))
        })
    });

    group.bench_function("direct_match", |b| {
        b.iter(|| {
            let mut kw_count = 0;
            let mut non_kw_count = 0;
            for i in inputs.iter() {
                if match_keyword(*i).is_some() {
                    kw_count += 1;
                } else {
                    non_kw_count += 1;
                }
            }
            assert_eq!((kw_count, non_kw_count), (11, 100))
        })
    });

    group.bench_function("smart_match", |b| {
        b.iter(|| {
            let mut kw_count = 0;
            let mut non_kw_count = 0;
            for i in inputs.iter() {
                if smart_match_keyword2(*i).is_some() {
                    kw_count += 1;
                } else {
                    non_kw_count += 1;
                }
            }
            assert_eq!((kw_count, non_kw_count), (11, 100))
        })
    });

    group.bench_function("std_hashmap", |b| {
        b.iter(|| {
            let mut kw_count = 0;
            let mut non_kw_count = 0;
            for i in inputs.iter() {
                if hashmap.get(*i).is_some() {
                    kw_count += 1;
                } else {
                    non_kw_count += 1;
                }
            }
            assert_eq!((kw_count, non_kw_count), (11, 100))
        })
    });

    group.finish();
}

criterion_group!(benches, bench_keyword_lookup);
criterion_main!(benches);
