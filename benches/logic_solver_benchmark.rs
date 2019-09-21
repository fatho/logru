#[macro_use]
extern crate criterion;

extern crate logru;

use criterion::Criterion;

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("zebra puzzle", |b| {
        let rules = logru::zebra::puzzle_rules();
        b.iter(|| {
            let mut q = rules.query(vec![logru::zebra::puzzle(logru::zebra::var(0))]);
            let _ = q.next();
        })
    });
}

criterion_group!{
    name = benches;
    config = Criterion::default().sample_size(4);
    targets = criterion_benchmark
}
criterion_main!(benches);


/*

#[derive(Clone, Copy, PartialEq, Eq)]
enum House {
H1, H2, H3, H4, H5,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Color {
    Yellow, Blue, Red, Ivory, Green,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Nationality {
    Norwegian, Ukrainian, Englishman, Spaniard, Japanese,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Drink {
    Water, Tea, Milk, OrangeJuice, Coffee,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Smoke {
    Kools, Chesterfield, OldGOld, LuckyStrike, Parliaments,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Pet {
    Fox, Horse, Snails, Dog, Zebra
}


*/
