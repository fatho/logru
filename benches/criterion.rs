use criterion::{criterion_group, criterion_main, Criterion};
use logru::textual::TextualUniverse;

macro_rules! sanity_check {
    ($computation:expr,$result:expr) => {{
        let r = $computation;
        assert_eq!(r, $result);
        r
    }};
}

fn prepare_zebra(reverse: bool) -> TextualUniverse {
    let mut u = TextualUniverse::new();

    if reverse {
        u.load_str(include_str!("../testfiles/zebra-reverse.lru"))
            .unwrap();
    } else {
        u.load_str(include_str!("../testfiles/zebra.lru")).unwrap();
    }

    u
}

fn zebra(u: &mut TextualUniverse) -> usize {
    let solutions = u.query_dfs("puzzle(X).").unwrap();
    sanity_check!(solutions.count(), 1)
}

fn prepare_arithmetic() -> TextualUniverse {
    let mut u = TextualUniverse::new();

    u.load_str(include_str!("../testfiles/arithmetic.lru"))
        .unwrap();
    u
}

fn arithmetic_add(u: &mut TextualUniverse) -> usize {
    let solutions = u.query_dfs("add(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))),s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))),X).").unwrap();
    sanity_check!(solutions.count(), 1)
}

fn arithmetic_add_reverse(u: &mut TextualUniverse) -> usize {
    let solutions = u.query_dfs("add(X,Y,s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))))))))))))))))))))).").unwrap();
    sanity_check!(solutions.count(), 35)
}

fn arithmetic_sub(u: &mut TextualUniverse) -> usize {
    let solutions = u.query_dfs("add(X,s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))),s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))))))))))))))))))))).").unwrap();
    sanity_check!(solutions.count(), 1)
}

fn arithmetic_mul(u: &mut TextualUniverse) -> usize {
    let solutions = u.query_dfs("mul(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))),s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))),X).").unwrap();
    sanity_check!(solutions.count(), 1)
}

fn arithmetic_squares(u: &mut TextualUniverse) -> usize {
    let solutions = u.query_dfs("mul(X,X,Y).").unwrap();
    sanity_check!(solutions.take(40).count(), 40)
}

fn criterion_benchmark(c: &mut Criterion) {
    let mut zebra_universe = prepare_zebra(false);
    let mut reverse_zebra_universe = prepare_zebra(true);
    let mut arithmetic_universe = prepare_arithmetic();

    // For the Zebra puzzle, the execution order makes a huge difference.
    // The Zebra puzzle with inverted puzzle clauses is many times slower.
    // These benchmarks therefore ensure our execution order is left alone.
    c.bench_function("zebra", |b| b.iter(|| zebra(&mut zebra_universe)));
    c.bench_function("zebra reverse", |b| {
        b.iter(|| zebra(&mut reverse_zebra_universe))
    });
    c.bench_function("add", |b| {
        b.iter(|| arithmetic_add(&mut arithmetic_universe))
    });
    c.bench_function("add reverse", |b| {
        b.iter(|| arithmetic_add_reverse(&mut arithmetic_universe))
    });
    c.bench_function("sub", |b| {
        b.iter(|| arithmetic_sub(&mut arithmetic_universe))
    });
    c.bench_function("mul", |b| {
        b.iter(|| arithmetic_mul(&mut arithmetic_universe))
    });
    c.bench_function("squares", |b| {
        b.iter(|| arithmetic_squares(&mut arithmetic_universe))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
