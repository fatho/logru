use crate::{
    ast::*,
    term_arena::{self, TermArena},
};

/// The Universe is a collection of symbols, facts and rules. A solver can be used for running
/// queries against the universe.
#[derive(Debug)]
pub struct Universe {
    /// next unallocated symbol ID
    fresh_symbol: usize,
    rules: Vec<Rule>,
    compiled_rules: CompiledRuleDb,
}

impl Universe {
    /// Create a new empty universe.
    pub fn new() -> Self {
        Self {
            fresh_symbol: 0,
            rules: vec![],
            compiled_rules: CompiledRuleDb::new(),
        }
    }

    /// Generate a fresh symbol ID in this universe.
    pub fn alloc_symbol(&mut self) -> Sym {
        let sym = Sym::from_ord(self.fresh_symbol);
        self.fresh_symbol += 1;
        sym
    }

    /// Generate a range of fresh symbol IDs in this universe.
    pub fn alloc_symbols(&mut self, count: usize) -> impl Iterator<Item = Sym> {
        let fresh_start = self.fresh_symbol;
        self.fresh_symbol += count;
        (fresh_start..fresh_start + count).map(Sym::from_ord)
    }

    /// Add a new rule to this universe for deriving facts.
    pub fn add_rule(&mut self, rule: Rule) {
        self.compiled_rules.insert(&rule);
        self.rules.push(rule);
    }

    /// Returns the rules that have been added to this universe.
    pub fn rules(&self) -> &[Rule] {
        &self.rules
    }

    /// Returns the number of symbols that have been allocated in this universe.
    pub fn num_symbols(&self) -> usize {
        self.fresh_symbol
    }

    /// Returns the set of compiled rules that are more efficient for a solver to process.
    pub fn compiled_rules(&self) -> &CompiledRuleDb {
        &self.compiled_rules
    }
}

impl Default for Universe {
    fn default() -> Self {
        Self::new()
    }
}

/// Internal helper structure of the DfsSolver for storing rules in a more efficient way during
/// solving. Having them precomputed as `TermArena`s makes instantiating the rules faster since we
/// can linearly copy the arena contents rather than having to traverse a bunch of pointers.
#[derive(Debug, Clone)]
pub struct CompiledRule {
    /// Arena containing the head terms.
    head_blueprint: TermArena,
    /// ID of the head term in the `head_blueprint` arena.
    head: term_arena::TermId,
    /// Arena containing the tail terms. We use a separate arena for this since we might not always
    /// need to instantiate the rule tail, only when the rule head actually matched.
    tail_blueprint: TermArena,
    /// ID of the tail term in the `tail_blueprint` arena.
    tail: Vec<term_arena::TermId>,
    /// Precomputed number of required variable slots for fast allocation of temporary goal
    /// variables when a rule is instantiated.
    var_slots: usize,
}

impl CompiledRule {
    pub fn new(rule: &Rule) -> CompiledRule {
        let mut scratch = Vec::new();
        let mut head_blueprint = TermArena::new();
        let mut tail_blueprint = TermArena::new();
        let head = head_blueprint.insert_ast_appterm(&mut scratch, &rule.head);
        let tail = rule
            .tail
            .iter()
            .map(|tail| tail_blueprint.insert_ast_appterm(&mut scratch, tail))
            .collect();
        CompiledRule {
            head_blueprint,
            head,
            tail_blueprint,
            tail,
            var_slots: rule.head.count_var_slots().max(
                rule.tail
                    .iter()
                    .map(|tail| tail.count_var_slots())
                    .max()
                    .unwrap_or(0),
            ),
        }
    }

    /// Returns the head term and the arena that contains it.
    #[inline(always)]
    pub fn head(&self) -> (term_arena::TermId, &TermArena) {
        (self.head, &self.head_blueprint)
    }

    /// Returns the tail terms and the arena that contains them.
    #[inline(always)]
    pub fn tail(&self) -> (&[term_arena::TermId], &TermArena) {
        (&self.tail, &self.tail_blueprint)
    }

    /// Returns the number of variable slots that need to be allocated for this rule.
    #[inline(always)]
    pub fn var_slots(&self) -> usize {
        self.var_slots
    }
}

/// Auxilliary data structure for holding a set of `CompiledRule`s in a way that is efficient to use
/// during solving.
#[derive(Debug)]
pub struct CompiledRuleDb {
    /// The set of rules indexed by the symbol ID of the head predicate.
    rules_by_head: Vec<Vec<CompiledRule>>,
}

impl CompiledRuleDb {
    /// Create a new empty rule database.
    pub fn new() -> Self {
        Self {
            rules_by_head: Vec::new(),
        }
    }

    /// Create a new rule database with a given minimum capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            rules_by_head: vec![Vec::new(); capacity],
        }
    }

    /// Compile a rule and insert it into the database.
    pub fn insert(&mut self, rule: &Rule) {
        self.ensure_capacity(rule.head.functor);
        let compiled = CompiledRule::new(rule);
        self.rules_by_head[rule.head.functor.ord()].push(compiled);
    }

    /// Query all the rules that have a matching head.
    #[inline(always)]
    pub fn rules_by_head(&self, head: Sym) -> &[CompiledRule] {
        &self.rules_by_head[head.ord()]
    }

    fn ensure_capacity(&mut self, sym: Sym) {
        if sym.ord() >= self.rules_by_head.len() {
            self.rules_by_head.resize(sym.ord() + 1, Vec::new());
        }
    }
}

impl Default for CompiledRuleDb {
    fn default() -> Self {
        Self::new()
    }
}
