// use unification::{Term, VarId};
// use logic::RuleSet;

// /// The basic terms of the Zebra puzzle
// #[derive(Debug, Clone, Copy, PartialEq, Eq)]
// pub enum Zebra {
//     // --------- predicates ----------

//     Puzzle, Exists, RightOf, NextTo, First, Middle,

//     // --------- solution terms ----------

//     House, Houses,

//     // ---------- atoms -----------

//     Yellow, Blue, Red, Ivory, Green,
//     Norwegian, Ukrainian, Englishman, Spaniard, Japanese,
//     Water, Tea, Milk, OrangeJuice, Coffee,
//     Kools, Chesterfield, OldGOld, LuckyStrike, Parliaments,
//     Fox, Horse, Snails, Dog, Zebra
// }

// pub fn house(color: Term<Zebra>, nationality: Term<Zebra>, drink: Term<Zebra>, smoke: Term<Zebra>, pet: Term<Zebra>) -> Term<Zebra> {
//     Term::App(Zebra::House, vec![color, nationality, drink, smoke, pet])
// }

// pub fn houses(h1: Term<Zebra>, h2: Term<Zebra>, h3: Term<Zebra>, h4: Term<Zebra>, h5: Term<Zebra>) -> Term<Zebra> {
//     Term::App(Zebra::Houses, vec![h1, h2, h3, h4, h5])
// }

// pub fn next_to(house1: Term<Zebra>, house2: Term<Zebra>, houses: Term<Zebra>) -> Term<Zebra> {
//     Term::App(Zebra::NextTo, vec![house1, house2, houses])
// }

// pub fn right_of(house1: Term<Zebra>, house2: Term<Zebra>, houses: Term<Zebra>) -> Term<Zebra> {
//     Term::App(Zebra::RightOf, vec![house1, house2, houses])
// }

// pub fn middle(house: Term<Zebra>, houses: Term<Zebra>) -> Term<Zebra> {
//     Term::App(Zebra::Middle, vec![house, houses])
// }

// pub fn first(house: Term<Zebra>, houses: Term<Zebra>) -> Term<Zebra> {
//     Term::App(Zebra::First, vec![house, houses])
// }

// pub fn exists(house: Term<Zebra>, houses: Term<Zebra>) -> Term<Zebra> {
//     Term::App(Zebra::Exists, vec![house, houses])
// }

// pub fn puzzle(houses: Term<Zebra>) -> Term<Zebra> {
//     Term::App(Zebra::Puzzle, vec![houses])
// }

// pub fn atom(a: Zebra) -> Term<Zebra> {
//     Term::App(a, vec![])
// }

// pub fn var(v: usize) -> Term<Zebra> {
//     Term::Var(VarId(v))
// }

// pub fn puzzle_rules() -> RuleSet<Zebra> {
//     let mut rules = RuleSet::new();

//     let mut wild = 100;
//     let mut _w = || {
//         wild += 1;
//         var(wild)
//     };

//     // relationships
//     rules.add_rule(exists(var(0), houses(var(0), var(1), var(2), var(3), var(4))), vec![]);
//     rules.add_rule(exists(var(1), houses(var(0), var(1), var(2), var(3), var(4))), vec![]);
//     rules.add_rule(exists(var(2), houses(var(0), var(1), var(2), var(3), var(4))), vec![]);
//     rules.add_rule(exists(var(3), houses(var(0), var(1), var(2), var(3), var(4))), vec![]);
//     rules.add_rule(exists(var(4), houses(var(0), var(1), var(2), var(3), var(4))), vec![]);

//     rules.add_rule(next_to(var(0), var(1), houses(var(0), var(1), var(2), var(3), var(4))), vec![]);
//     rules.add_rule(next_to(var(1), var(0), houses(var(0), var(1), var(2), var(3), var(4))), vec![]);
//     rules.add_rule(next_to(var(1), var(2), houses(var(0), var(1), var(2), var(3), var(4))), vec![]);
//     rules.add_rule(next_to(var(2), var(1), houses(var(0), var(1), var(2), var(3), var(4))), vec![]);
//     rules.add_rule(next_to(var(2), var(3), houses(var(0), var(1), var(2), var(3), var(4))), vec![]);
//     rules.add_rule(next_to(var(3), var(2), houses(var(0), var(1), var(2), var(3), var(4))), vec![]);
//     rules.add_rule(next_to(var(3), var(4), houses(var(0), var(1), var(2), var(3), var(4))), vec![]);
//     rules.add_rule(next_to(var(4), var(3), houses(var(0), var(1), var(2), var(3), var(4))), vec![]);

//     rules.add_rule(middle(var(2), houses(var(0), var(1), var(2), var(3), var(4))), vec![]);

//     rules.add_rule(first(var(0), houses(var(0), var(1), var(2), var(3), var(4))), vec![]);

//     rules.add_rule(right_of(var(1), var(0), houses(var(0), var(1), var(2), var(3), var(4))), vec![]);
//     rules.add_rule(right_of(var(2), var(1), houses(var(0), var(1), var(2), var(3), var(4))), vec![]);
//     rules.add_rule(right_of(var(3), var(2), houses(var(0), var(1), var(2), var(3), var(4))), vec![]);
//     rules.add_rule(right_of(var(4), var(3), houses(var(0), var(1), var(2), var(3), var(4))), vec![]);

//     rules.add_rule(puzzle(var(0)), vec![
//         // There are five houses.
//         //   (by definition)

//         // The Englishman lives in the red house.
//         exists(house(atom(Zebra::Red), atom(Zebra::Englishman), _w(), _w(), _w()), var(0)),

//         // The Spaniard owns the dog.
//         exists(house(_w(), atom(Zebra::Spaniard), _w(), _w(), atom(Zebra::Dog)), var(0)),

//         // Coffee is drunk in the green house.
//         exists(house(atom(Zebra::Green), _w(), atom(Zebra::Coffee), _w(), _w()), var(0)),

//         // The Ukrainian drinks tea.
//         exists(house(_w(), atom(Zebra::Ukrainian), atom(Zebra::Tea), _w(), _w()), var(0)),

//         // The green house is immediately to the right of the ivory house.
//         right_of(house(atom(Zebra::Green), _w(), _w(), _w(), _w()), house(atom(Zebra::Ivory), _w(), _w(), _w(), _w()), var(0)),

//         // The Old Gold smoker owns snails.
//         exists(house(_w(), _w(), _w(), atom(Zebra::OldGOld), atom(Zebra::Snails)), var(0)),

//         // Kools are smoked in the yellow house.
//         exists(house(atom(Zebra::Yellow), _w(), _w(), atom(Zebra::Kools), _w()), var(0)),

//         // Milk is drunk in the middle house.
//         middle(house(_w(), _w(), atom(Zebra::Milk), _w(), _w()), var(0)),

//         // The Norwegian lives in the first house.
//         first(house(_w(), atom(Zebra::Norwegian), _w(), _w(), _w()), var(0)),

//         // The man who smokes Chesterfields lives in the house next to the man with the fox.
//         next_to(house(_w(), _w(), _w(), atom(Zebra::Chesterfield), _w()), house(_w(), _w(), _w(), _w(), atom(Zebra::Fox)), var(0)),

//         // Kools are smoked in the house next to the house where the horse is kept.
//         next_to(house(_w(), _w(), _w(), atom(Zebra::Kools), _w()), house(_w(), _w(), _w(), _w(), atom(Zebra::Horse)), var(0)),

//         // The Lucky Strike smoker drinks orange juice.
//         exists(house(_w(), _w(), atom(Zebra::OrangeJuice), atom(Zebra::LuckyStrike), _w()), var(0)),

//         // The Japanese smokes Parliaments.
//         exists(house(_w(), atom(Zebra::Japanese), _w(), atom(Zebra::Parliaments), _w()), var(0)),

//         // The Norwegian lives next to the blue house.
//         next_to(house(_w(), atom(Zebra::Norwegian), _w(), _w(), _w()), house(atom(Zebra::Blue), _w(), _w(), _w(), _w()), var(0)),

//         // Someone drinks water.
//         exists(house(_w(), _w(), atom(Zebra::Water), _w(), _w()), var(0)),

//         // Someone has a zebra.
//         exists(house(_w(), _w(), _w(), _w(), atom(Zebra::Zebra)), var(0)),
//     ]);

//     rules
// }

// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn solve() {
//         let rules = puzzle_rules();
//         let mut q = rules.query(vec![puzzle(var(0))]);
//         assert!(q.next().is_some());
//     }
// }
