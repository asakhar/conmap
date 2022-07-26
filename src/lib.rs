use std::{
  cell::UnsafeCell,
  collections::hash_map::RandomState,
  fmt::Debug,
  hash::{BuildHasher, Hash, Hasher},
  marker::PhantomData,
  sync::{
    atomic::{AtomicUsize, Ordering},
    RwLock, RwLockReadGuard,
  },
};

const HASH_STEP: usize = 1337;

#[allow(non_snake_case)]
mod CellState {
  #[allow(non_upper_case_globals)]
  pub const Empty: usize = 0;
  #[allow(non_upper_case_globals)]
  pub const Removed: usize = 1;
  #[allow(non_upper_case_globals)]
  pub const Uninit: usize = 2;

  #[macro_export(local_inner_macros)]
  macro_rules! Valid {
    ($n:expr) => {
      (CellState::Uninit + 1 + $n)
    };
  }
}

type ContainerItem<K, V> = (UnsafeCell<Option<K>>, UnsafeCell<Option<V>>, AtomicUsize);
type Container<K, V> = Vec<ContainerItem<K, V>>;

#[derive(Debug)]
pub struct OccupiedEntry<'map, K, V> {
  idx: usize,
  data: RwLockReadGuard<'map, Container<K, V>>,
}

impl<'map, K, V> OccupiedEntry<'map, K, V> {
  fn get(&self) -> &ContainerItem<K, V> {
    unsafe { self.data.get_unchecked(self.idx) }
  }
  fn get_value(&self) -> &V {
    unsafe { &*self.get().1.get() }.as_ref().unwrap()
  }
  fn get_key(&self) -> &K {
    unsafe { &*self.get().0.get() }.as_ref().unwrap()
  }
}

#[derive(Debug)]
pub struct VacantEntry<'map, K, V, S> {
  key: Option<K>,
  map: &'map ConMap<K, V, S>,
}

#[derive(Debug)]
pub enum Entry<'map, K, V, S> {
  Vacant(VacantEntry<'map, K, V, S>),
  Occupied(OccupiedEntry<'map, K, V>),
}

impl<'map, K, V, S> Drop for Entry<'map, K, V, S> {
  fn drop(&mut self) {
    if let Entry::Occupied(entry) = self {
      unsafe { entry.data.get_unchecked(entry.idx) }
        .2
        .fetch_sub(1, Ordering::Relaxed);
    }
  }
}
impl<'map, K, V, S> Entry<'map, K, V, S> {
  const fn as_occupied_unchecked(&self) -> &OccupiedEntry<'map, K, V> {
    match self {
      Entry::Vacant(_) => panic!("Called as_occupied on vacant entry"),
      Entry::Occupied(entry) => entry,
    }
  }
  #[allow(dead_code)]
  const fn as_vacant_unchecked(&self) -> &VacantEntry<'map, K, V, S> {
    match self {
      Entry::Occupied(_) => panic!("Called as_vacant on occupied entry"),
      Entry::Vacant(entry) => entry,
    }
  }
  const fn as_occupied(&self) -> Option<&OccupiedEntry<'map, K, V>> {
    match self {
      Entry::Vacant(_) => None,
      Entry::Occupied(entry) => Some(entry),
    }
  }
  #[allow(dead_code)]
  const fn as_vacant(&self) -> Option<&VacantEntry<'map, K, V, S>> {
    match self {
      Entry::Occupied(_) => None,
      Entry::Vacant(entry) => Some(entry),
    }
  }
  pub fn value_unchecked(&self) -> &V {
    self.as_occupied_unchecked().get_value()
  }
  pub fn value(&self) -> Option<&V> {
    Some(self.as_occupied()?.get_value())
  }
  pub fn key(&self) -> &K {
    match self {
      Entry::Vacant(entry) => entry.key.as_ref().unwrap(),
      Entry::Occupied(entry) => entry.get_key(),
    }
  }
}

impl<'map, K: Hash + PartialEq, V, S: BuildHasher> Entry<'map, K, V, S> {
  pub fn or_insert<'this>(&'this mut self, value: V) -> &'this V {
    let (map, key) = match self {
      Entry::Occupied(entry) => return entry.get_value(),
      Entry::Vacant(entry) => (entry.map, entry.key.take().unwrap()),
    };
    *self = match map.insert(key, value) {
      Ok(r) => r,
      Err(r) => r,
    };
    self.value_unchecked()
  }

  pub fn remove(mut self) -> bool {
    match &mut self {
      Entry::Vacant(entry) => {
        let entry = entry.map.entry(entry.key.take().unwrap());
        if entry.as_occupied().is_none() {
          return false;
        }
        entry.remove()
      }
      Entry::Occupied(entry) => {
        let cell = entry.get();
        while cell
          .2
          .compare_exchange_weak(
            Valid!(1),
            CellState::Uninit,
            Ordering::SeqCst,
            Ordering::Relaxed,
          )
          .is_err()
        {}
        unsafe { &mut *cell.0.get() }.take();
        unsafe { &mut *cell.1.get() }.take();
        cell.2.store(CellState::Removed, Ordering::SeqCst);
        true
      }
    }
  }
}

pub type InsertionResult<T> = Result<T, T>;

#[derive(Debug)]
pub struct ConMap<K, V, S = RandomState> {
  data: RwLock<Container<K, V>>,
  build_hasher: S,
}

impl<K, V> Default for ConMap<K, V, RandomState> {
  fn default() -> Self {
    Self {
      data: Default::default(),
      build_hasher: Default::default(),
    }
  }
}

impl<K, V> ConMap<K, V, RandomState> {
  pub fn new() -> Self {
    Default::default()
  }

  pub fn with_capacity(cap: usize) -> Self {
    let mut data = Vec::with_capacity(cap);
    for _ in 0..data.capacity() {
      data.push((
        UnsafeCell::new(None),
        UnsafeCell::new(None),
        AtomicUsize::new(0),
      ));
    }
    Self {
      data: RwLock::new(data),
      build_hasher: Default::default(),
    }
  }
}

impl<K: Hash + PartialEq, V, S: BuildHasher> ConMap<K, V, S> {
  fn realloc(&self) {
    let mut data = self.data.write().unwrap();
    let mut new_cap = data.capacity() << 4;
    if new_cap == 0 {
      new_cap = 50;
    }
    let old_data = data
      .iter_mut()
      .map(|(key, value, state)| {
        let state_load = state.load(Ordering::Relaxed);
        if state_load <= CellState::Uninit {
          key.get_mut().take();
          value.get_mut().take();
        }
        state.store(CellState::Empty, Ordering::Relaxed);
        (key, value, state_load > CellState::Uninit)
      })
      .filter(|(_, _, should_take)| *should_take)
      .map(|(key, value, _)| {
        (
          key.get_mut().take().unwrap(),
          value.get_mut().take().unwrap(),
        )
      })
      .collect::<Vec<_>>();
    let old_len = data.len();
    data.reserve(new_cap - old_len);
    let new_cap = data.capacity();
    let remaining = new_cap - old_len;
    for _ in 0..remaining {
      data.push((
        UnsafeCell::new(None),
        UnsafeCell::new(None),
        AtomicUsize::new(0),
      ));
    }
    for (key, value) in old_data {
      self.insert_unchecked_no_ret(&data, key, value);
    }
  }

  pub fn insert<'map>(
    &'map self,
    mut key: K,
    mut value: V,
  ) -> InsertionResult<Entry<'map, K, V, S>> {
    loop {
      match self.insert_unchecked(key, value) {
        Ok(ins_res) => return ins_res,
        Err(kv) => {
          (key, value) = kv;
        }
      }
      self.realloc();
    }
  }

  pub fn entry(&self, key: K) -> Entry<K, V, S> {
    let data = self.data.read().unwrap();
    let cap = data.capacity();
    if cap == 0 {
      return Entry::Vacant(VacantEntry {
        key: Some(key),
        map: self,
      });
    }
    let mut hasher = self.build_hasher.build_hasher();
    key.hash(&mut hasher);

    let mut hash = hasher.finish() as usize % cap;
    'outer: for _ in 0..cap {
      // SAFETY: hash is always in bounds of data
      let cell = unsafe { data.get_unchecked(hash) };

      loop {
        let current_state = cell.2.load(Ordering::SeqCst);
        if current_state == CellState::Empty {
          break 'outer;
        }
        if current_state == CellState::Removed {
          break;
        }
        if current_state == usize::MAX || current_state == CellState::Uninit {
          continue;
        }
        if cell
          .2
          .compare_exchange(
            current_state,
            current_state + 1,
            Ordering::SeqCst,
            Ordering::Relaxed,
          )
          .is_err()
        {
          continue;
        }
        let key_ref = unsafe { &*cell.0.get() }.as_ref().unwrap();
        if key_ref != &key {
          cell.2.fetch_sub(1, Ordering::SeqCst);
          break;
        }
        return Entry::Occupied(OccupiedEntry { idx: hash, data });
      }
      hash = (hash + HASH_STEP) % cap;
    }
    return Entry::Vacant(VacantEntry {
      key: Some(key),
      map: self,
    });
  }

  fn insert_unchecked_no_ret(&self, data: &Container<K, V>, key: K, value: V) {
    let release = |idx| {
      let cell: &ContainerItem<K, V> = unsafe { data.get_unchecked(idx) };
      cell.2.fetch_sub(1, Ordering::Relaxed);
    };
    let _ = self
      .insert_unchecked_internal(data, key, value)
      .map(|res| res.map(release).map_err(release));
  }

  fn insert_unchecked_internal(
    &self,
    data: &Container<K, V>,
    key: K,
    value: V,
  ) -> Result<InsertionResult<usize>, (K, V)> {
    let cap = data.capacity();
    if cap == 0 {
      return Err((key, value));
    }
    let mut hasher = self.build_hasher.build_hasher();
    key.hash(&mut hasher);
    let mut hash = hasher.finish() as usize % cap;

    for _ in 0..cap {
      // SAFETY: hash is always in bounds of data
      let cell = unsafe { data.get_unchecked(hash) };
      loop {
        let state = cell.2.load(Ordering::SeqCst);

        if state < CellState::Uninit {
          if cell
            .2
            .compare_exchange(
              state,
              CellState::Uninit,
              Ordering::SeqCst,
              Ordering::Relaxed,
            )
            .is_ok()
          {
            unsafe { *cell.0.get() = Some(key) };
            unsafe { *cell.1.get() = Some(value) };

            cell.2.store(Valid!(1), Ordering::SeqCst);
            return Ok(Ok(hash));
          }
          continue;
        }

        if state == usize::MAX || state == CellState::Uninit {
          continue;
        }
        if cell
          .2
          .compare_exchange(state, state + 1, Ordering::SeqCst, Ordering::Relaxed)
          .is_err()
        {
          continue;
        }
        let cell_key = unsafe { &*cell.0.get() }.as_ref().unwrap();
        if cell_key != &key {
          cell.2.fetch_sub(1, Ordering::Relaxed);
          break;
        }
        return Ok(Err(hash));
      }
      hash = (hash + HASH_STEP) % cap;
    }
    return Err((key, value));
  }

  fn insert_unchecked<'map>(
    &'map self,
    key: K,
    value: V,
  ) -> Result<InsertionResult<Entry<'map, K, V, S>>, (K, V)> {
    let data = self.data.read().unwrap();
    let acquire_access = |idx| {
      Entry::Occupied(OccupiedEntry {
        idx,
        data: self.data.read().unwrap(),
      })
    };
    self
      .insert_unchecked_internal(&data, key, value)
      .map(|v| v.map(acquire_access).map_err(acquire_access))
  }
}

unsafe impl<K: Send, V: Send, S: Send> Send for ConMap<K, V, S> {}
unsafe impl<K: Sync, V: Sync, S: Sync> Sync for ConMap<K, V, S> {}

impl<K, V, S> ConMap<K, V, S> {
  pub fn iter<'map>(&'map self) -> Iter<'map, K, V, S> {
    Iter {
      idx: 0,
      data: self.data.read().unwrap(),
      rwlock: &self.data,
      _phantom: Default::default(),
    }
  }

  pub fn with_hasher(build_hasher: S) -> Self {
    Self {
      data: Default::default(),
      build_hasher,
    }
  }

  pub fn with_capacity_and_hasher(cap: usize, build_hasher: S) -> Self {
    let mut data = Vec::with_capacity(cap);
    for _ in 0..data.capacity() {
      data.push((
        UnsafeCell::new(None),
        UnsafeCell::new(None),
        AtomicUsize::new(0),
      ))
    }
    Self {
      data: RwLock::new(data),
      build_hasher,
    }
  }
}

pub struct Iter<'map, K, V, S> {
  idx: usize,
  data: RwLockReadGuard<'map, Container<K, V>>,
  rwlock: &'map RwLock<Container<K, V>>,
  _phantom: PhantomData<S>,
}

impl<'map, K: Hash + PartialEq<K> + 'map, V: 'map, S: 'map> Iterator for Iter<'map, K, V, S> {
  type Item = Entry<'map, K, V, S>;

  fn next(&mut self) -> Option<Self::Item> {
    'outer: for i in self.idx..self.data.capacity() {
      let cell = unsafe { self.data.get_unchecked(i) };
      loop {
        let current_state = cell.2.load(Ordering::SeqCst);
        if current_state <= CellState::Removed {
          continue 'outer;
        }
        if current_state == usize::MAX || current_state == CellState::Uninit {
          continue;
        }
        if cell
          .2
          .compare_exchange(
            current_state,
            current_state + 1,
            Ordering::SeqCst,
            Ordering::Relaxed,
          )
          .is_err()
        {
          continue;
        }
        debug_assert!(cell.2.load(Ordering::SeqCst) > Valid!(0));
        self.idx = i + 1;
        return Some(Entry::Occupied(OccupiedEntry {
          idx: i,
          data: self.rwlock.read().unwrap(),
        }));
      }
    }
    None
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn it_works() {
    // std::collections::HashMap
    let map = ConMap::with_capacity(100);
    map.insert("abc", 1).unwrap();
    assert_eq!(*map.entry("abc").or_insert(2), 1);
  }

  #[test]
  fn it_works2() {
    // std::collections::HashMap
    let map = ConMap::with_capacity(1);
    map.insert("abc", 1).unwrap();
    map.insert("abcd", 1).unwrap();
    map.insert("abcde", 1).unwrap();
    assert_eq!(*map.entry("abc").or_insert(2), 1);
  }

  #[test]
  fn drop_check() {
    static ALIVE_COUNT: AtomicUsize = AtomicUsize::new(0);
    #[derive(Debug)]
    struct CountsDrops {}
    impl CountsDrops {
      fn new() -> Self {
        ALIVE_COUNT.fetch_add(1, Ordering::Relaxed);
        Self {}
      }
    }
    impl Drop for CountsDrops {
      fn drop(&mut self) {
        ALIVE_COUNT.fetch_sub(1, Ordering::Relaxed);
      }
    }
    {
      let map = ConMap::with_capacity(1);
      for (i, c) in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
        .chars()
        .enumerate()
      {
        map.insert(c, CountsDrops::new()).unwrap().value().unwrap();
        assert_eq!(ALIVE_COUNT.load(Ordering::Relaxed), i + 1);
      }
    }
    assert_eq!(ALIVE_COUNT.load(Ordering::Relaxed), 0);
  }

  #[test]
  fn remove_items() {
    let map = ConMap::with_capacity(10);
    map.insert("a", "a").unwrap();
    let b = map.insert("b", "b").unwrap();
    map.insert("c", "c").unwrap();
    assert!(b.remove());
    assert_eq!(map.entry("a").value(), Some(&"a"));
    assert_eq!(map.entry("c").value(), Some(&"c"));
    assert_eq!(map.entry("b").value(), None);
  }

  #[test]
  fn lazy_init() {
    let map = ConMap::new();
    map.insert("abc", 1).unwrap();
    map.insert("abcd", 1).unwrap();
    map.insert("abcde", 1).unwrap();
    assert_eq!(*map.entry("abc").or_insert(2), 1);
    // let map = std::collections::HashMap::new();
  }

  #[test]
  fn with_hasher() {
    let build_hasher = RandomState::new();
    let map = ConMap::with_hasher(build_hasher);
    assert_eq!(*map.entry("abc").or_insert(1), 1);
    assert_eq!(*map.entry("def").or_insert(2), 2);
    assert_eq!(*map.entry("abc").or_insert(3), 1);
  }
}
