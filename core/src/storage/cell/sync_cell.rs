// Copyright 2018-2019 Parity Technologies (UK) Ltd.
// This file is part of pDSL.
//
// pDSL is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// pDSL is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with pDSL.  If not, see <http://www.gnu.org/licenses/>.

use crate::{
    env,
    memory::{
        boxed::Box,
        format,
    },
    storage::{
        alloc::{
            Allocate,
            AllocateUsing,
        },
        cell::TypedCell,
        Flush,
    },
};

use core::cell::RefCell;

/// A synchronized cell.
///
/// Provides interpreted, read-optimized and inplace-mutable
/// access to the associated constract storage slot.
///
/// # Guarantees
///
/// - `Owned`, `Typed`, `Avoid Reads`, `Mutable`
///
/// Read more about kinds of guarantees and their effect [here](../index.html#guarantees).
#[derive(Debug)]
pub struct SyncCell<T> {
    /// The underlying typed cell.
    cell: TypedCell<T>,
    /// The cache for the synchronized value.
    cache: Cache<T>,
}

/// A synchronized cache entry.
#[derive(Debug)]
pub struct SyncCacheEntry<T> {
    /// If the entry needs to be written back upon a flush.
    ///
    /// This is required as soon as there are potential writes to the
    /// value stored in the associated cell.
    dirty: bool,
    /// The value of the cell.
    ///
    /// Being captured in a `Pin` allows to provide robust references to the outside.
    cell_val: Box<Option<T>>,
}

impl<T> SyncCacheEntry<T> {
    /// Updates the cached value.
    pub fn update(&mut self, new_val: Option<T>) {
        *self.cell_val = new_val;
    }
}

impl<T> SyncCacheEntry<T> {
    /// Initializes this synchronized cache entry with the given value.
    ///
    /// # Note
    ///
    /// The cache will _not_ be marked as dirty after this operation.
    pub fn new(val: Option<T>) -> Self {
        env::println("SyncCacheEntry::new");
        Self {
            dirty: false,
            cell_val: Box::new(val),
        }
    }

    /// Returns `true` if this synchronized cache entry is dirty.
    pub fn is_dirty(&self) -> bool {
        let dirty = self.dirty;
        env::println(&format!("SyncCacheEntry::is_dirty = {:?}", dirty));
        dirty
    }

    /// Marks the cached value as dirty.
    pub fn mark_dirty(&mut self) {
        env::println("SyncCacheEntry::mark_dirty");
        self.dirty = true;
    }

    /// Marks the cached value as clean.
    pub fn mark_clean(&mut self) {
        env::println("SyncCacheEntry::mark_clean");
        self.dirty = false;
    }

    /// Returns an immutable reference to the synchronized cached value.
    pub fn get(&self) -> Option<&T> {
        let ret: Option<&T> = (&*self.cell_val).into();
        env::println(&format!("SyncCacheEntry::get is_some = {:?}", ret.is_some()));
        ret
    }
}

impl<T> SyncCacheEntry<T> {
    /// Returns a mutable reference to the synchronized cached value.
    ///
    /// This also marks the cache entry as being dirty since
    /// the callee could potentially mutate the value.
    pub fn get_mut(&mut self) -> Option<&mut T> {
        self.mark_dirty();
        let ret: Option<&mut T> = self.cell_val.as_mut().into();
        env::println(&format!("SyncCacheEntry::get_mut is_some = {:?}", ret.is_some()));
        ret
    }
}

/// A cache entry storing the value if synchronized.
#[derive(Debug)]
pub enum CacheEntry<T> {
    /// The cache is desychronized with the contract storage.
    Desync,
    /// The cache is in sync with the contract storage.
    Sync(SyncCacheEntry<T>),
}

impl<T> Default for CacheEntry<T> {
    fn default() -> Self {
        env::println("CacheEntry::default()");
        CacheEntry::Desync
    }
}

impl<T> CacheEntry<T> {
    /// Updates the cached value.
    pub fn update(&mut self, new_val: Option<T>) {
        env::println("CacheEntry::update()");
        match self {
            CacheEntry::Desync => {
                env::println("CacheEntry::update() - CacheEntry::Desync 1");
                *self = CacheEntry::Sync(SyncCacheEntry::new(new_val));
                env::println("CacheEntry::update() - CacheEntry::Desync 2");
            }
            CacheEntry::Sync(sync_entry) => {
                env::println("CacheEntry::update() - CacheEntry::Sync(_) 1");
                sync_entry.update(new_val);
                env::println("CacheEntry::update() - CacheEntry::Sync(_) 2");
            }
        }
    }

    /// Returns `true` if the cache is in sync.
    pub fn is_synced(&self) -> bool {
        env::println("CacheEntry::is_synced()");
        match self {
            CacheEntry::Sync(_) => {
                env::println("CacheEntry::is_synced() -> true");
                true
            },
            _ => {
                env::println("CacheEntry::is_synced() -> false");
                false
            },
        }
    }

    /// Returns `true` if the cache is dirty.
    pub fn is_dirty(&self) -> bool {
        env::println("CacheEntry::is_dirty()");
        match self {
            CacheEntry::Desync => {
                env::println("CacheEntry::is_dirty() -> true");
                false
            },
            CacheEntry::Sync(sync_entry) => {
                let dirty = sync_entry.is_dirty();
                env::println(&format!("CacheEntry::is_dirty() -> {:?}", dirty));
                dirty
            },
        }
    }

    /// Marks the cache as dirty.
    pub fn mark_dirty(&mut self) {
        env::println("CacheEntry::mark_dirty()");
        match self {
            CacheEntry::Sync(sync_entry) => {
                env::println("CacheEntry::mark_dirty() - Sync(_)");
                sync_entry.mark_dirty()
            },
            CacheEntry::Desync => {
                env::println("CacheEntry::mark_dirty() - Desync");
                ()
            },
        }
    }

    /// Marks the cache as clean.
    pub fn mark_clean(&mut self) {
        env::println("CacheEntry::mark_clean()");
        match self {
            CacheEntry::Sync(sync_entry) => {
                env::println("CacheEntry::mark_clean() - Sync(_)");
                sync_entry.mark_clean()
            },
            CacheEntry::Desync => {
                env::println("CacheEntry::mark_clean() - Desync");
                ()
            },
        }
    }

    /// Returns an immutable reference to the internal cached entity if any.
    ///
    /// # Panics
    ///
    /// If the cache is in desync state and thus has no cached entity.
    pub fn get(&self) -> Option<&T> {
        env::println("CacheEntry::get()");
        match self {
            CacheEntry::Desync => {
                env::println("CacheEntry::get() Desync -> PANIC");
                panic!(
                    "[pdsl_core::sync_cell::CacheEntry::get] Error: \
                     tried to get the value from a desync cache"
                )
            }
            CacheEntry::Sync(sync_entry) => {
                env::println("CacheEntry::get() Sync(_) -> ok");
                sync_entry.get()
            },
        }
    }

    /// Returns a mutable reference to the internal cached entity if any.
    ///
    /// # Panics
    ///
    /// If the cache is in desync state and thus has no cached entity.
    pub fn get_mut(&mut self) -> Option<&mut T> {
        env::println("CacheEntry::get_mut()");
        match self {
            CacheEntry::Desync => {
                env::println("CacheEntry::get_mut() Desync -> PANIC");
                panic!(
                    "[pdsl_core::sync_cell::CacheEntry::get_mut] Error: \
                     tried to get the value from a desync cache"
                )
            }
            CacheEntry::Sync(sync_entry) => {
                env::println("CacheEntry::get_mut() Sync(_) -> ok");
                sync_entry.get_mut()
            },
        }
    }
}

/// A cache for synchronizing values between memory and storage.
#[derive(Debug)]
pub struct Cache<T> {
    /// The cached value.
    entry: RefCell<CacheEntry<T>>,
}

impl<T> Default for Cache<T> {
    fn default() -> Self {
        env::println("CacheEntry::default()");
        Self {
            entry: Default::default(),
        }
    }
}

impl<T> Cache<T> {
    /// Updates the synchronized value.
    ///
    /// # Note
    ///
    /// - The cache will be in sync after this operation.
    /// - The cache will not be dirty after this operation.
    pub fn update(&self, new_val: Option<T>) {
        env::println("Cache::update() 1");
        self.entry.borrow_mut().update(new_val);
        env::println("Cache::update() 2");
    }

    /// Returns `true` if the cache is in sync.
    pub fn is_synced(&self) -> bool {
        env::println("Cache::is_synced() 1");
        let ret = self.entry.borrow().is_synced();
        env::println("Cache::is_synced() 2");
        ret
    }

    /// Returns `true` if the cache is dirty.
    pub fn is_dirty(&self) -> bool {
        env::println("Cache::is_dirty() 1");
        let dirty = self.entry.borrow().is_dirty();
        env::println("Cache::is_dirty() 2");
        dirty
    }

    /// Marks the cache dirty.
    pub fn mark_dirty(&mut self) {
        env::println("Cache::mark_dirty() 1");
        self.entry.borrow_mut().mark_dirty();
        env::println("Cache::mark_dirty() 2");
    }

    /// Marks the cache clean.
    pub fn mark_clean(&mut self) {
        env::println("Cache::mark_clean() 1");
        self.entry.borrow_mut().mark_clean();
        env::println("Cache::mark_clean() 2");
    }

    /// Returns an immutable reference to the internal cache entry.
    ///
    /// Used to returns references from the inside to the outside.
    fn get_entry(&self) -> &CacheEntry<T> {
        env::println("Cache::get_entry()");
        unsafe { &*self.entry.as_ptr() }
    }

    /// Returns an immutable reference to the internal cache entry.
    ///
    /// Used to returns references from the inside to the outside.
    fn get_entry_mut(&mut self) -> &mut CacheEntry<T> {
        env::println("Cache::get_entry_mut()");
        unsafe { &mut *self.entry.as_ptr() }
    }

    /// Returns an immutable reference to the value if any.
    ///
    /// # Panics
    ///
    /// If the cache is desnyc and thus has no synchronized value.
    pub fn get(&self) -> Option<&T> {
        env::println("Cache::get()");
        self.get_entry().get()
    }

    /// Returns an immutable reference to the value if any.
    ///
    /// # Panics
    ///
    /// If the cache is desnyc and thus has no synchronized value.
    pub fn get_mut(&mut self) -> Option<&mut T> {
        env::println("Cache::get_mut()");
        self.get_entry_mut().get_mut()
    }
}

impl<T> parity_codec::Encode for SyncCell<T> {
    fn encode_to<W: parity_codec::Output>(&self, dest: &mut W) {
        env::println("SyncCell::encode_to() 1");
        self.cell.encode_to(dest);
        env::println("SyncCell::encode_to() 2");
    }
}

impl<T> parity_codec::Decode for SyncCell<T> {
    fn decode<I: parity_codec::Input>(input: &mut I) -> Option<Self> {
        env::println("SyncCell::decode()");
        TypedCell::decode(input).map(|typed_cell| {
            Self {
                cell: typed_cell,
                cache: Cache::default(),
            }
        })
    }
}

impl<T> Flush for SyncCell<T>
where
    T: parity_codec::Encode,
{
    fn flush(&mut self) {
        env::println("SyncCell::flush() 1");
        if self.cache.is_dirty() {
            env::println("SyncCell::flush() is_dirty 1");
            match self.cache.get() {
                Some(val) => {
                    env::println("SyncCell::flush() is_dirty - some 1");
                    self.cell.store(val);
                    env::println("SyncCell::flush() is_dirty - some 2");
                },
                None => {
                    env::println("SyncCell::flush() is_dirty - none 1");
                    self.cell.clear();
                    env::println("SyncCell::flush() is_dirty - none 2");
                },
            }
            env::println("SyncCell::flush() is_dirty 2");
            self.cache.mark_clean();
            env::println("SyncCell::flush() is_dirty 3");
        }
        env::println("SyncCell::flush() 2");
    }
}

impl<T> AllocateUsing for SyncCell<T> {
    unsafe fn allocate_using<A>(alloc: &mut A) -> Self
    where
        A: Allocate,
    {
        env::println("SyncCell::allocate_using() 1");
        Self {
            cell: TypedCell::allocate_using(alloc),
            cache: Default::default(),
        }
    }
}

impl<T> SyncCell<T> {
    /// Removes the value from the cell.
    pub fn clear(&mut self) {
        env::println("SyncCell::clear() 1");
        self.cache.update(None);
        env::println("SyncCell::clear() 2");
        self.cache.mark_dirty();
        env::println("SyncCell::clear() 3");
    }
}

impl<T> SyncCell<T>
where
    T: parity_codec::Decode,
{
    /// Returns an immutable reference to the value of the cell.
    pub fn get(&self) -> Option<&T> {
        env::println("SyncCell::get() 1");
        if !self.cache.is_synced() {
            env::println("SyncCell::get() is_synced 1");
            let loaded = self.cell.load();
            env::println("SyncCell::get() is_synced 2");
            self.cache.update(loaded);
            env::println("SyncCell::get() is_synced 3");
        }
        env::println("SyncCell::get() 2");
        let ret = self.cache.get();
        env::println("SyncCell::get() 3");
        ret
    }
}

impl<T> SyncCell<T>
where
    T: parity_codec::Encode,
{
    /// Sets the value of the cell.
    pub fn set(&mut self, val: T) {
        env::println("SyncCell::set() 1");
        self.cache.update(Some(val));
        env::println("SyncCell::set() 2");
        self.cache.mark_dirty();
        env::println("SyncCell::set() 3");
    }
}

impl<T> SyncCell<T>
where
    T: parity_codec::Codec,
{
    /// Returns a mutable reference to the value of the cell.
    pub fn get_mut(&mut self) -> Option<&mut T> {
        env::println("SyncCell::get_mut() 1");
        if !self.cache.is_synced() {
            env::println("SyncCell::get_mut() is_synced 1");
            let loaded = self.cell.load();
            env::println("SyncCell::get_mut() is_synced 2");
            self.cache.update(loaded);
            env::println("SyncCell::get_mut() is_synced 3");
        }
        env::println("SyncCell::get_mut() 2");
        self.cache.mark_dirty();
        env::println("SyncCell::get_mut() 3");
        let ret = self.cache.get_mut();
        env::println("SyncCell::get_mut() 4");
        ret
    }

    /// Mutates the value stored in the cell.
    ///
    /// Returns an immutable reference to the result if
    /// a mutation happened, otherwise `None` is returned.
    pub fn mutate_with<F>(&mut self, f: F) -> Option<&T>
    where
        F: FnOnce(&mut T),
    {
        env::println("SyncCell::mutate_with() 1");
        if let Some(value) = self.get_mut() {
            env::println("SyncCell::mutate_with() - Some(_) 1");
            f(value);
            env::println("SyncCell::mutate_with() - Some(_) 2");
            return Some(&*value)
        }
        env::println("SyncCell::mutate_with() 2");
        None
    }
}

#[cfg(all(test, feature = "test-env"))]
mod tests {
    use super::*;
    use crate::env;

    use crate::{
        storage::{
            alloc::BumpAlloc,
            Key,
        },
        test_utils::run_test,
    };

    fn dummy_cell() -> SyncCell<i32> {
        unsafe {
            let mut alloc = BumpAlloc::from_raw_parts(Key([0x0; 32]));
            SyncCell::allocate_using(&mut alloc)
        }
    }

    #[test]
    fn simple() {
        run_test(|| {
            let mut cell = dummy_cell();
            assert_eq!(cell.get(), None);
            cell.set(5);
            assert_eq!(cell.get(), Some(&5));
            assert_eq!(cell.mutate_with(|val| *val += 10), Some(&15));
            assert_eq!(cell.get(), Some(&15));
            cell.clear();
            assert_eq!(cell.get(), None);
        })
    }

    #[test]
    fn count_rw_get() {
        // Repetitions performed.
        const N: u32 = 5;

        let mut cell = dummy_cell();

        // Asserts initial reads and writes are zero.
        assert_eq!(env::test::total_reads(), 0);
        assert_eq!(env::test::total_writes(), 0);

        // Repeated reads on the same cell.
        for _i in 0..N {
            cell.get();
            assert_eq!(env::test::total_reads(), 1);
            assert_eq!(env::test::total_writes(), 0);
        }

        // Flush the cell and assert reads and writes.
        cell.flush();
        assert_eq!(env::test::total_reads(), 1);
        assert_eq!(env::test::total_writes(), 0);
    }

    #[test]
    fn count_rw_get_mut() {
        // Repetitions performed.
        const N: u32 = 5;

        let mut cell = dummy_cell();

        // Asserts initial reads and writes are zero.
        assert_eq!(env::test::total_reads(), 0);
        assert_eq!(env::test::total_writes(), 0);

        // Repeated mutable reads on the same cell.
        for _i in 0..N {
            cell.get_mut();
            assert_eq!(env::test::total_reads(), 1);
            assert_eq!(env::test::total_writes(), 0);
        }

        // Flush the cell and assert reads and writes.
        cell.flush();
        assert_eq!(env::test::total_reads(), 1);
        assert_eq!(env::test::total_writes(), 1);
    }

    #[test]
    fn count_rw_set() {
        // Repetitions performed.
        const N: u32 = 5;

        let mut cell = dummy_cell();

        // Asserts initial reads and writes are zero.
        assert_eq!(env::test::total_reads(), 0);
        assert_eq!(env::test::total_writes(), 0);

        // Repeated writes to the same cell.
        for _i in 0..N {
            cell.set(42);
            assert_eq!(env::test::total_reads(), 0);
            assert_eq!(env::test::total_writes(), 0);
        }

        // Flush the cell and assert reads and writes.
        cell.flush();
        assert_eq!(env::test::total_reads(), 0);
        assert_eq!(env::test::total_writes(), 1);
    }

    #[test]
    fn count_rw_clear() {
        // Repetitions performed.
        const N: u32 = 5;

        let mut cell = dummy_cell();

        // Asserts initial reads and writes are zero.
        assert_eq!(env::test::total_reads(), 0);
        assert_eq!(env::test::total_writes(), 0);

        // Repeated writes to the same cell.
        for _i in 0..N {
            cell.clear();
            assert_eq!(env::test::total_reads(), 0);
            assert_eq!(env::test::total_writes(), 0);
        }

        // Flush the cell and assert reads and writes.
        cell.flush();
        assert_eq!(env::test::total_reads(), 0);
        assert_eq!(env::test::total_writes(), 1);
    }
}
