use std::convert::{TryFrom, TryInto};
use std::fmt::Debug;
use std::num::NonZero;
use std::ops::{Index, IndexMut};

use thiserror::Error;

#[derive(Debug, Clone)]
pub struct Stack {
    stack: Vec<Word>,
}

impl Stack {
    /// Create a new solver stack.
    pub fn new() -> Self {
        Self {
            // Always occupy address `0` so that we can use the null pointer as "unassigned".
            stack: vec![Word::null_ptr()],
        }
    }

    /// Allocate a new singular value on the stack
    #[inline(always)]
    pub fn alloc(&mut self, value: Word) -> Addr {
        let addr = self.top();
        self.stack.push(value);
        addr
    }

    /// Allocate a range of words of the given length on the stack
    #[inline(always)]
    pub fn alloc_zeroed_range(&mut self, len: usize) -> Addr {
        self.alloc_range(std::iter::repeat_n(Word::null_ptr(), len))
    }

    #[inline(always)]
    pub fn alloc_range(&mut self, values: impl IntoIterator<Item = Word>) -> Addr {
        let ret = self.top();
        self.stack.extend(values);
        ret
    }

    #[inline(always)]
    pub fn copy_range(&mut self, start: Addr, end: Addr) -> Addr {
        let ret = self.top();
        self.stack
            .extend_from_within(start.into_raw() as usize..end.into_raw() as usize);
        ret
    }

    //pub fn alloc_compound(&mut self, head: Word)

    /// Free all allocations at and above the given address.
    ///
    /// This has no effect if `Addr` is greater than or equal to the current length.
    #[inline(always)]
    pub fn free(&mut self, limit: Addr) {
        self.stack.truncate(limit.0.get() as usize);
    }

    /// Address of the top of the stack (one after the topmost allocated slot, or the next address
    /// to be allocated, in other words).
    #[inline(always)]
    pub fn top(&self) -> Addr {
        debug_assert!(!self.stack.is_empty(), "stack invariant violated");
        assert!(self.stack.len() < u32::MAX as usize, "stack overflow");

        let addr = self.stack.len();
        // SAFETY:
        // - `addr` is the length of `stack`
        // - `stack` is initialized with one element (i.e. length 1 > 0)
        // - `stack` can only shrink through `free`, but `free` never frees the last element
        // - `addr` cannot overflow due to assertion
        unsafe { Addr(NonZero::new_unchecked(addr as u32)) }
    }

    pub fn freeze(&mut self) -> FrozenStack<'_> {
        FrozenStack {
            limit: self.top(),
            inner: self,
        }
    }
}

impl Index<Addr> for Stack {
    type Output = Word;

    #[inline(always)]
    fn index(&self, index: Addr) -> &Self::Output {
        &self.stack[index.into_raw() as usize]
    }
}

impl IndexMut<Addr> for Stack {
    #[inline(always)]
    fn index_mut(&mut self, index: Addr) -> &mut Self::Output {
        &mut self.stack[index.into_raw() as usize]
    }
}

impl Default for Stack {
    fn default() -> Self {
        Self::new()
    }
}

/// A stack that can only be modified above a certain limit.
pub struct FrozenStack<'s> {
    inner: &'s mut Stack,
    limit: Addr,
}

impl<'s> FrozenStack<'s> {
    /// Allocate a new singular value on the stack
    #[inline(always)]
    pub fn alloc(&mut self, value: Word) -> Addr {
        self.inner.alloc(value)
    }

    /// Allocate a range of words of the given length on the stack
    #[inline(always)]
    pub fn alloc_zeroed_range(&mut self, len: usize) -> Addr {
        self.inner.alloc_zeroed_range(len)
    }

    #[inline(always)]
    pub fn alloc_range(&mut self, values: impl IntoIterator<Item = Word>) -> Addr {
        self.inner.alloc_range(values)
    }

    #[inline(always)]
    pub fn copy_range(&mut self, start: Addr, end: Addr) -> Addr {
        self.inner.copy_range(start, end)
    }

    /// Free all allocations at and above the given address.
    ///
    /// This has no effect if `Addr` is greater than or equal to the current length.
    #[inline(always)]
    pub fn free(&mut self, limit: Addr) {
        assert!(limit >= self.limit);
        self.inner.free(limit);
    }

    /// Address of the top of the stack (one after the topmost allocated slot, or the next address
    /// to be allocated, in other words).
    #[inline(always)]
    pub fn top(&self) -> Addr {
        self.inner.top()
    }

    /// Move the frozen mark up to the current top of the stack.
    pub fn refreeze(&mut self) {
        self.limit = self.top();
    }

    pub fn debug_decoded<'a>(&'a self) -> DecodedFrozenStack<'a, 's> {
        DecodedFrozenStack(self)
    }
}

impl<'s> Drop for FrozenStack<'s> {
    fn drop(&mut self) {
        self.inner.free(self.limit);
    }
}

impl<'s> Index<Addr> for FrozenStack<'s> {
    type Output = Word;

    #[inline(always)]
    fn index(&self, index: Addr) -> &Self::Output {
        &self.inner[index]
    }
}

impl<'s> IndexMut<Addr> for FrozenStack<'s> {
    #[inline(always)]
    fn index_mut(&mut self, index: Addr) -> &mut Self::Output {
        assert!(index >= self.limit);
        &mut self.inner[index]
    }
}

/// A word stored on the solver stack
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[repr(transparent)]
pub struct Word(u64);

impl Word {
    /// The null-pointer word.
    #[inline(always)]
    pub const fn null_ptr() -> Self {
        Word(0)
    }
}

/// An address into the solver stack.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Addr(NonZero<u32>);

impl Addr {
    #[inline(always)]
    pub const fn new(raw: u32) -> Option<Addr> {
        match NonZero::new(raw) {
            Some(val) => Some(Addr(val)),
            None => None,
        }
    }

    #[inline(always)]
    pub const fn into_raw(self) -> u32 {
        self.0.get()
    }

    #[inline(always)]
    pub fn offset(self, off: u32) -> Self {
        Self(self.0.checked_add(off).expect("no overflow"))
    }

    /// Given a compound term at the current address with the given arity,
    /// provide an iterator over all its arguments.
    #[inline(always)]
    pub fn arg_iter(self, arity: Arity) -> impl DoubleEndedIterator<Item = Addr> {
        (0..arity.into_raw()).map(move |off| self.offset(1 + off as u32))
    }

    /// Iterate the range from the current address to the (exclusive) top address.
    #[inline(always)]
    pub fn range_iter(self, top: Addr) -> impl DoubleEndedIterator<Item = Addr> {
        // SAFETY: `self` is valid, and all addresses will be larger, hence they'll also be valid
        (self.into_raw()..top.into_raw()).map(|addr| unsafe { Addr(NonZero::new_unchecked(addr)) })
    }
}

/// An atom identifier.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Atom(u32);

impl Atom {
    #[inline(always)]
    pub const fn new(raw: u32) -> Atom {
        Self(raw)
    }

    #[inline(always)]
    pub const fn into_raw(self) -> u32 {
        self.0
    }
}

/// The arity of a compound term.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Arity(u16);

impl Arity {
    #[inline(always)]
    pub const fn new(raw: u16) -> Arity {
        Self(raw)
    }

    #[inline(always)]
    pub const fn into_raw(self) -> u16 {
        self.0
    }
}

impl From<Arity> for usize {
    #[inline(always)]
    fn from(value: Arity) -> Self {
        value.0 as usize
    }
}

#[derive(Debug, Error)]
#[error("arity must be smaller than 2^15")]
pub struct ArityOutOfBoundsError;

impl TryFrom<usize> for Arity {
    type Error = ArityOutOfBoundsError;

    #[inline(always)]
    fn try_from(value: usize) -> Result<Self, Self::Error> {
        value
            .try_into()
            .map(Arity)
            .map_err(|_| ArityOutOfBoundsError)
    }
}

/// A word stored on the solver stack
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum DecodedWord {
    /// A redirection to another slot.
    ///
    /// Encoded as `0<31-bit padding><32 bit addr>`
    Ptr(Option<Addr>),
    /// A compound term starting with the given atom, and followed by as many cells as the arity
    /// denotes.
    ///
    /// Encoded as `1<15 bit padding><16-bit arity><32 bit atom>`
    App(Atom, Arity),
}

impl DecodedWord {
    const PAYLOAD_MASK: u64 = (1 << 32) - 1;
    const ARITY_MASK: u64 = (1 << 16) - 1;
    const ARITY_SHIFT: i32 = 32;

    const DISCRIMINATOR_MASK: u64 = 1 << 63;
    const DISCRIMINATOR_PTR: u64 = 0;
    const DISCRIMINATOR_APP: u64 = 1 << 63;
}

impl From<Word> for DecodedWord {
    #[inline(always)]
    fn from(value: Word) -> Self {
        let payload = (value.0 & Self::PAYLOAD_MASK) as u32;
        match value.0 & Self::DISCRIMINATOR_MASK {
            Self::DISCRIMINATOR_PTR => DecodedWord::Ptr(Addr::new(payload)),
            Self::DISCRIMINATOR_APP => {
                let arity = ((value.0 >> Self::ARITY_SHIFT) & Self::ARITY_MASK) as u16;
                DecodedWord::App(Atom(payload), Arity(arity))
            }
            _ => unreachable!("discriminator mask only contais one bit"),
        }
    }
}

impl From<DecodedWord> for Word {
    #[inline(always)]
    fn from(value: DecodedWord) -> Self {
        let encoded = match value {
            DecodedWord::Ptr(addr) => {
                DecodedWord::DISCRIMINATOR_PTR | addr.map_or(0, Addr::into_raw) as u64
            }
            DecodedWord::App(atom, arity) => {
                DecodedWord::DISCRIMINATOR_APP
                    | ((arity.0 as u64) << DecodedWord::ARITY_SHIFT)
                    | atom.0 as u64
            }
        };
        Word(encoded)
    }
}

pub struct DecodedFrozenStack<'a, 's>(&'a FrozenStack<'s>);

impl<'a, 's> Debug for DecodedFrozenStack<'a, 's> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Stack {{")?;
        let width = self.0.inner.stack.len().ilog10() + 1;
        for (i, val) in self.0.inner.stack.iter().enumerate() {
            write!(f, " {i:>w$}: ", w = width as usize)?;
            match DecodedWord::from(*val) {
                DecodedWord::Ptr(addr) => {
                    if let Some(addr) = addr {
                        writeln!(f, "@{}", addr.into_raw())?;
                    } else {
                        writeln!(f, "@null")?;
                    }
                }
                DecodedWord::App(atom, arity) => {
                    writeln!(f, "{}/{}", atom.into_raw(), arity.into_raw())?;
                }
            }
        }
        writeln!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use super::{Addr, Arity, Atom, DecodedWord, Word};

    #[test]
    fn word_roundtrips() {
        let examples = [
            DecodedWord::Ptr(None),
            DecodedWord::Ptr(Some(Addr::new(1).unwrap())),
            DecodedWord::Ptr(Some(Addr::new(u32::MAX).unwrap())),
            DecodedWord::App(Atom::new(0), Arity::new(0)),
            DecodedWord::App(Atom::new(u32::MAX), Arity::new(16)),
            DecodedWord::App(Atom::new(1), Arity::new(u16::MAX)),
        ];

        for ex in examples {
            let trip1 = Word::from(ex);
            let trip2 = DecodedWord::from(trip1);

            assert_eq!(ex, trip2);
        }
    }

    #[test]
    fn zero_is_valid_word() {
        assert_eq!(DecodedWord::from(Word(0)), DecodedWord::Ptr(None));
    }

    #[test]
    fn size_of_word() {
        assert_eq!(std::mem::size_of::<DecodedWord>(), 8);
    }
}
