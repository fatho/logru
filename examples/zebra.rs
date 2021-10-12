use std::time::Instant;

use logru::solver::DfsSolver;

//use logru::zebra;

fn main() {
    let mut u = logru::named::NamedUniverse::new();

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

    let query = u.parse_query(&["puzzle($0)"]).unwrap();
    let solver = DfsSolver::new(u.inner());
    let mut solutions = solver.query(&query);
    let before = Instant::now();
    let solution = solutions.next().unwrap();
    let duration = before.elapsed();

    for var in solution {
        if let Some(term) = var {
            println!("{}", u.term_to_string(&term));
        } else {
            println!("<bug: no solution>");
        }
    }
    println!("Took {:.3}s", duration.as_secs_f64());
}
