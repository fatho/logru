use std::convert::{TryFrom, TryInto};
use std::num::NonZero;
use std::ops::{Index, IndexMut};

use thiserror::Error;

pub struct Stack {
    stack: Vec<Word>,
}

impl Stack {
    /// Create a new solver stack.
    pub fn new() -> Self {
        Self {
            // Always occupy address `0` so that we can use the null pointer as "unassigned".
            stack: vec![Word::from(DecodedWord::Ptr(None))],
        }
    }

    /// Allocate a new singular value on the stack
    #[inline(always)]
    pub fn alloc(&mut self, value: Word) -> Addr {
        let addr = self.top();
        self.stack.push(value);
        addr
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

/// Decoded representation of [`Word`]s stored on the search stack.
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
