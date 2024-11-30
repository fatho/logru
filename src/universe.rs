//! # Universe
//!
//! The universe consists of two main "databases" that are relevant to the set of facts", "databases" that are relevant to the set of facts"),rules and
//! queries:
//! 1. The [`SymbolStore`] is used for allocating named and unnamed [`Sym`]bols which are used as
//!    identifiers in the low-level representation.

use std::{collections::HashMap, sync::Arc};

use crate::{
    ast::*,
    term_arena::{self, TermArena},
};

/// A modifiable collection of symbols
pub trait SymbolStorage {
    /// Return the symbol associated with the name, or allocate a fresh ID and associate it with the
    /// given name.
    fn get_or_insert_named(&mut self, name: &str) -> Sym;

    /// Given a list of name-value pairs, translate the names into [`Sym`]s and return a mapping
    /// from symbols to values.
    fn build_sym_map<'a, T>(
        &mut self,
        pairs: impl IntoIterator<Item = (&'a str, T)>,
    ) -> HashMap<Sym, T> {
        pairs
            .into_iter()
            .map(|(name, value)| (self.get_or_insert_named(name), value))
            .collect()
    }
}

impl<T> SymbolStorage for &mut T
where
    T: SymbolStorage,
{
    fn get_or_insert_named(&mut self, name: &str) -> Sym {
        let this: &mut T = *self; // Specify the concrete type to call to avoid accidentally recursing back into this method and creating an infinite loop.
        this.get_or_insert_named(name)
    }
}

/// A readable collection of symbols
pub trait Symbols {
    /// Get the name of a symbol, if it has one.
    fn get_symbol_name(&self, sym: Sym) -> Option<&str>;

    /// Returns the number of symbols that have been allocated in this universe.
    fn num_symbols(&self) -> usize;
}

/// The symbol store is responsible for allocating unique [`Sym`]s (unique within the instance,
/// there are no guardrails preventing mixing [`Sym`]s from different [`SymbolStore`]s), and keeps a
/// mapping between [`Sym`]s and friendly names.
///
/// # Example
///
/// ```
/// # use logru::universe::*;
/// let mut store = SymbolStore::new();
/// let foo = store.get_or_insert_named("foo");
/// let bar = store.get_or_insert_named("bar");
/// assert_ne!(foo, bar);
///
/// let foo_again = store.get_or_insert_named("foo");
/// assert_eq!(foo, foo_again);
///
/// let bar_name = store.get_symbol_name(bar);
/// assert_eq!(bar_name, Some("bar"));
///
/// // Creating an unnamed symbol
/// let unknown = store.insert_unnamed();
/// let unknown_name = store.get_symbol_name(unknown);
/// assert_eq!(unknown_name, None);
/// ```
///
/// # Example
///
/// See the [top-level example](crate#example).
#[derive(Debug, Clone)]
pub struct SymbolStore {
    /// Mapping from names to symbols
    sym_by_name: HashMap<Arc<str>, Sym>,
    /// Mapping from symbols to names. The length of this mapping doubles as the next unallocated
    /// symbol ID.
    name_by_sym: Vec<Option<Arc<str>>>,
}

impl SymbolStore {
    /// Create a new empty symbol store.
    pub fn new() -> Self {
        Self {
            sym_by_name: HashMap::new(),
            name_by_sym: Vec::new(),
        }
    }

    /// Generate a fresh unnamed symbol ID in this universe.
    ///
    /// # Notes
    ///
    /// While it is possible to create symbols directly from ordinals using [`Sym::from_ord`], using
    /// those may cause the solver to panic or return invalid results if the ordinal hasn't been
    /// previously obtained by calling [`Sym::ord`] on a symbol allocated in this universe.
    pub fn insert_unnamed(&mut self) -> Sym {
        let sym = Sym::from_ord(self.name_by_sym.len());
        self.name_by_sym.push(None);
        sym
    }
}

impl Symbols for SymbolStore {
    /// Get the name of a symbol, if it has one.
    fn get_symbol_name(&self, sym: Sym) -> Option<&str> {
        self.name_by_sym.get(sym.ord()).and_then(|n| n.as_deref())
    }

    /// Returns the number of symbols that have been allocated in this universe.
    fn num_symbols(&self) -> usize {
        self.name_by_sym.len()
    }
}

impl<'a> SymbolStorage for SymbolStore {
    /// Return the symbol associated with the name, or allocate a fresh ID and associate it with the
    /// given name.
    fn get_or_insert_named(&mut self, name: &str) -> Sym {
        self.sym_by_name.get(name).copied().unwrap_or_else(|| {
            let sym = Sym::from_ord(self.name_by_sym.len());
            let shared_name: Arc<str> = name.into();
            self.name_by_sym.push(Some(shared_name.clone()));
            self.sym_by_name.insert(shared_name, sym);
            sym
        })
    }
}

impl Default for SymbolStore {
    fn default() -> Self {
        Self::new()
    }
}

/// Stores and allocates unique symbols on top of a symbol store, without modifying it.
#[derive(Debug)]
pub struct SymbolOverlay<'a> {
    symbols: &'a SymbolStore,
    // Sym entries stored here start at 0, but get translated on the API boundary to start at symbols.num_symbols().
    overlay: SymbolStore,
}

impl<'a> SymbolOverlay<'a> {
    pub fn new(symbols: &'a SymbolStore) -> Self {
        Self {
            symbols,
            overlay: Default::default(),
        }
    }
}

impl SymbolStorage for SymbolOverlay<'_> {
    /// Return the symbol associated with the name, or allocate a fresh ID and associate it with the
    /// given name.
    fn get_or_insert_named(&mut self, name: &str) -> Sym {
        self.symbols
            .sym_by_name
            .get(name)
            .copied()
            .unwrap_or_else(|| {
                Sym::from_ord(
                    self.symbols.num_symbols() + self.overlay.get_or_insert_named(name).ord(),
                )
            })
    }
}

impl Symbols for SymbolOverlay<'_> {
    /// Get the name of a symbol, if it has one.
    fn get_symbol_name(&self, sym: Sym) -> Option<&str> {
        match sym.ord().checked_sub(self.symbols.num_symbols()) {
            None => self.symbols.get_symbol_name(sym),
            Some(index) => self.overlay.get_symbol_name(Sym::from_ord(index)),
        }
    }

    /// Returns the number of symbols that have been allocated in this universe.
    fn num_symbols(&self) -> usize {
        self.overlay.num_symbols() + self.symbols.num_symbols()
    }
}

/// Data structure holding facts and rules for use in solvers, like the built-in
/// [query_dfs](crate::query_dfs).
///
/// In contrast to the pointer-heavy layout of the regular [Rule] AST, this type contains
/// preallocated [crate::term_arena::TermArena]s that are faster to instantiate.
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
    /// The original rule that was compiled into this
    original: Rule,
}

impl CompiledRule {
    pub fn new(rule: Rule) -> CompiledRule {
        let mut scratch = Vec::new();
        let mut head_blueprint = TermArena::new();
        let mut tail_blueprint = TermArena::new();
        let head = head_blueprint.insert_ast_appterm(&mut scratch, &rule.head);
        let tail = rule
            .tail
            .iter()
            .map(|tail| tail_blueprint.insert_ast_term(&mut scratch, tail))
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
            original: rule,
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

    /// Return the original rule that was compiled into this.
    pub fn original(&self) -> &Rule {
        &self.original
    }
}

/// Auxilliary data structure for efficiently looking up [CompiledRule]s based on their head symbol.
#[derive(Debug)]
pub struct RuleSet {
    /// The set of rules indexed by the symbol ID of the head predicate.
    rules_by_head: Vec<Vec<CompiledRule>>,
}

impl RuleSet {
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
    pub fn insert(&mut self, rule: Rule) {
        let head = rule.head.functor;
        self.ensure_capacity(head);
        let compiled = CompiledRule::new(rule);
        self.rules_by_head[head.ord()].push(compiled);
    }

    /// Query all the rules that have a matching head.
    #[inline(always)]
    pub fn rules_by_head(&self, head: Sym) -> &[CompiledRule] {
        if head.ord() < self.rules_by_head.len() {
            &self.rules_by_head[head.ord()]
        } else {
            &[]
        }
    }

    fn ensure_capacity(&mut self, sym: Sym) {
        if sym.ord() >= self.rules_by_head.len() {
            self.rules_by_head.resize(sym.ord() + 1, Vec::new());
        }
    }
}

impl Default for RuleSet {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod test {
    use crate::{ast::Sym, Symbols};

    use super::{SymbolOverlay, SymbolStorage, SymbolStore};

    #[test]
    fn overlay() {
        let mut plain = SymbolStore::new();
        plain.insert_unnamed();
        plain.insert_unnamed();
        plain.insert_unnamed();
        plain.get_or_insert_named("a");
        let overlay_copy = plain.clone();
        let mut overlaid = SymbolOverlay::new(&overlay_copy);

        assert_eq!(
            plain.get_or_insert_named("b"),
            overlaid.get_or_insert_named("b")
        );

        assert_eq!(
            plain.get_or_insert_named("c"),
            overlaid.get_or_insert_named("c")
        );

        assert_eq!(plain.num_symbols(), overlaid.num_symbols());

        assert_eq!(
            plain.get_symbol_name(Sym::from_ord(3)),
            overlaid.get_symbol_name(Sym::from_ord(3))
        );

        // WARNING: those two checks are overly strict: they check that SymbolOverlay and SymbolStore assign the same numbers to additional symbols. That is not pat of the contract for an Overlay, although it makes debugging and testing easier.
        // If the need arises to relax the constraint, check instead that newly added symbols don't collide with existing ones and that names can be obtained correctly.
        assert_eq!(
            plain.get_symbol_name(Sym::from_ord(5)),
            overlaid.get_symbol_name(Sym::from_ord(5))
        );

        assert_eq!(
            plain.get_symbol_name(Sym::from_ord(99)),
            overlaid.get_symbol_name(Sym::from_ord(99))
        );
    }
}
