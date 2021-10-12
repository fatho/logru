use criterion::{criterion_group, criterion_main, Criterion};
use logru::{named::NamedUniverse, solver::Solver};

macro_rules! sanity_check {
    ($computation:expr,$result:expr) => {{
        let r = $computation;
        assert_eq!(r, $result);
        r
    }};
}

fn prepare_zebra() -> NamedUniverse {
    let mut u = NamedUniverse::new();

    u.fact("exists($0,list($0,$1,$2,$3,$4))").unwrap();
    u.fact("exists($1,list($0,$1,$2,$3,$4))").unwrap();
    u.fact("exists($2,list($0,$1,$2,$3,$4))").unwrap();
    u.fact("exists($3,list($0,$1,$2,$3,$4))").unwrap();
    u.fact("exists($4,list($0,$1,$2,$3,$4))").unwrap();

    u.fact("rightOf($1,$0,list($0,$1,$2,$3,$4))").unwrap();
    u.fact("rightOf($2,$1,list($0,$1,$2,$3,$4))").unwrap();
    u.fact("rightOf($3,$2,list($0,$1,$2,$3,$4))").unwrap();
    u.fact("rightOf($4,$3,list($0,$1,$2,$3,$4))").unwrap();

    u.fact("middle($2,list($0,$1,$2,$3,$4))").unwrap();

    u.fact("first($0,list($0,$1,$2,$3,$4))").unwrap();

    u.fact("nextTo($1,$0,list($0,$1,$2,$3,$4))").unwrap();
    u.fact("nextTo($2,$1,list($0,$1,$2,$3,$4))").unwrap();
    u.fact("nextTo($3,$2,list($0,$1,$2,$3,$4))").unwrap();
    u.fact("nextTo($4,$3,list($0,$1,$2,$3,$4))").unwrap();
    u.fact("nextTo($0,$1,list($0,$1,$2,$3,$4))").unwrap();
    u.fact("nextTo($1,$2,list($0,$1,$2,$3,$4))").unwrap();
    u.fact("nextTo($2,$3,list($0,$1,$2,$3,$4))").unwrap();
    u.fact("nextTo($3,$4,list($0,$1,$2,$3,$4))").unwrap();

    u.rule(
        "puzzle($0)",
        &[
            "exists(house(red,england,$1,$2,$3),$0)",
            "exists(house($4,spain,$5,$6,dog),$0)",
            "exists(house($7,japan,$8,painter,$9),$0)",
            "exists(house($10,italy,tea,$11,$12),$0)",
            "first(house($13,norway,$14,$15,$16),$0)",
            "rightOf(house(green,$17,$18,$19,$20),house(white,$21,$22,$23,$24),$0)",
            "exists(house($25,$26,$27,photographer,snails),$0)",
            "exists(house(yellow,$28,$29,diplomat,$30),$0)",
            "middle(house($31,$32,milk,$33,$34),$0)",
            "exists(house(green,$35,coffee,$36,$37),$0)",
            "nextTo(house($13,norway,$14,$15,$16),house(blue,$38,$39,$40,$41),$0)",
            "exists(house($42,$43,juice,violinist,$44),$0)",
            "nextTo(house($45,$46,$47,physician,$48),house($49,$50,$51,$52,fox),$0)",
            "nextTo(house($53,$54,$55,diplomat,$56),house($57,$58,$59,$60,horse),$0)",
            "exists(house($61,$62,water,$63,$64),$0)",
            "exists(house($65,$66,$67,$68,zebra),$0)",
        ],
    )
    .unwrap();
    u
}

fn zebra(u: &mut NamedUniverse) -> usize {
    let query = u.parse_query(&["puzzle($0)"]).unwrap();
    let solver = Solver::new(u.inner());
    let solutions = solver.query(&query);
    sanity_check!(solutions.count(), 1)
}

fn prepare_arithmetic() -> NamedUniverse {
    let mut u = NamedUniverse::new();

    u.fact("is_natural(z)").unwrap();
    u.rule("is_natural(s($0))", &["is_natural($0)"]).unwrap();

    u.rule("add($0,z,$0)", &["is_natural($0)"]).unwrap();
    u.rule("add($0,s($1),s($2))", &["add($0,$1,$2)"]).unwrap();

    u.rule("mul($0,z,z)", &["is_natural($0)"]).unwrap();
    u.rule("mul($0,s($1),$2)", &["add($0,$3,$2)", "mul($0,$1,$3)"])
        .unwrap();

    u
}

fn arithmetic_add(u: &mut NamedUniverse) -> usize {
    let query = u.parse_query(&["add(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))),s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))),$0)"]).unwrap();
    let solver = Solver::new(u.inner());
    let solutions = solver.query(&query);
    sanity_check!(solutions.count(), 1)
}

fn arithmetic_add_reverse(u: &mut NamedUniverse) -> usize {
    let query = u.parse_query(&["add($0,$1,s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z)))))))))))))))))))))))))))))))))))"]).unwrap();
    let solver = Solver::new(u.inner());
    let solutions = solver.query(&query);
    sanity_check!(solutions.count(), 35)
}

fn arithmetic_sub(u: &mut NamedUniverse) -> usize {
    let query = u.parse_query(&["add($0,s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))),s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z)))))))))))))))))))))))))))))))))))"]).unwrap();
    let solver = Solver::new(u.inner());
    let solutions = solver.query(&query);
    sanity_check!(solutions.count(), 1)
}

fn arithmetic_mul(u: &mut NamedUniverse) -> usize {
    let query = u.parse_query(&["mul(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))),s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))),$0)"]).unwrap();
    let solver = Solver::new(u.inner());
    let solutions = solver.query(&query);
    sanity_check!(solutions.count(), 1)
}

fn arithmetic_squares(u: &mut NamedUniverse) -> usize {
    let query = u.parse_query(&["mul($0,$0,$1)"]).unwrap();
    let solver = Solver::new(u.inner());
    let solutions = solver.query(&query);
    sanity_check!(solutions.take(40).count(), 40)
}

fn criterion_benchmark(c: &mut Criterion) {
    let mut zebra_universe = prepare_zebra();
    let mut arithmetic_universe = prepare_arithmetic();

    c.bench_function("zebra", |b| b.iter(|| zebra(&mut zebra_universe)));
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
