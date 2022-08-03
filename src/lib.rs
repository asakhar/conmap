use core::{
  fmt::{Debug, Display},
  hash::{BuildHasher, Hash, Hasher},
  marker::PhantomData,
};

#[allow(unused_imports)]
use core::sync::atomic::{AtomicUsize, Ordering};
use std::{collections::hash_map::RandomState, error::Error};

use constack::ConStack;
use rwspin::{RwSpin, RwSpinReadGuard, RwSpinWriteGuard};

const HASH_STEP: usize = 1337;

#[derive(Debug, PartialEq, Eq)]
enum State<K, V> {
  Vacant,
  Occupied((K, V)),
  Removed,
}

impl<K, V> Default for State<K, V> {
  fn default() -> Self {
    State::Vacant
  }
}

impl<K, V> State<K, V> {
  const fn as_occupied(&self) -> Option<&(K, V)> {
    use State::Occupied;
    match self {
      Occupied(ref kv) => Some(kv),
      _ => None,
    }
  }
  const fn as_occupied_unchecked(&self) -> &(K, V) {
    use State::Occupied;
    match self {
      Occupied(ref kv) => kv,
      _ => panic!("State was unoccupied"),
    }
  }
  fn take(&mut self) -> Self {
    core::mem::replace(self, State::Vacant)
  }
  const fn is_occupied(&self) -> bool {
    self.as_occupied().is_some()
  }
  fn to_occupied_unchecked(self) -> (K, V) {
    use State::Occupied;
    match self {
      Occupied(kv) => kv,
      _ => panic!("Assumed occupiedd state"),
    }
  }
}

type ContainerItem<K, V> = RwSpin<State<K, V>>;
type Container<K, V> = Vec<ContainerItem<K, V>>;

#[derive(Debug)]
pub struct OccupiedEntry<'map, K, V> {
  rl: Option<RwSpinReadGuard<'map, State<K, V>>>,
  data: RwSpinReadGuard<'map, Container<K, V>>,
}

impl<'map, K, V> OccupiedEntry<'map, K, V> {
  fn new(data: RwSpinReadGuard<'map, Container<K, V>>, idx: usize) -> Self {
    let mut res = Self { data, rl: None };
    res.rl = Some(
      unsafe {
        (*(&mut res.data as *mut RwSpinReadGuard<'map, Container<K, V>>)).get_unchecked(idx)
      }
      .read(),
    );
    res
  }
}

#[derive(Debug)]
pub struct VacantEntry<'map, K, V, S> {
  key: K,
  map: &'map ConMap<K, V, S>,
}

#[derive(Debug)]
pub enum Entry<'map, K, V, S> {
  Vacant(VacantEntry<'map, K, V, S>),
  Occupied(OccupiedEntry<'map, K, V>),
  Uninit,
}

impl<'map, K, V, S> Entry<'map, K, V, S> {
  const fn as_occupied_unchecked(&self) -> &OccupiedEntry<'map, K, V> {
    match self {
      Entry::Occupied(entry) => entry,
      _ => panic!("Called as_occupied on vacant entry"),
    }
  }
  #[allow(dead_code)]
  const fn as_vacant_unchecked(&self) -> &VacantEntry<'map, K, V, S> {
    match self {
      Entry::Vacant(entry) => entry,
      _ => panic!("Called as_vacant on occupied entry"),
    }
  }

  #[allow(dead_code)]
  fn to_vacant_unchecked(self) -> VacantEntry<'map, K, V, S> {
    match self {
      Entry::Vacant(entry) => entry,
      _ => panic!("Called as_vacant on occupied entry"),
    }
  }
  const fn as_occupied(&self) -> Option<&OccupiedEntry<'map, K, V>> {
    match self {
      Entry::Occupied(entry) => Some(entry),
      _ => None,
    }
  }
  #[allow(dead_code)]
  const fn as_vacant(&self) -> Option<&VacantEntry<'map, K, V, S>> {
    match self {
      Entry::Vacant(entry) => Some(entry),
      _ => None,
    }
  }
  pub fn value_unchecked(&self) -> &V {
    &self
      .as_occupied_unchecked()
      .rl
      .as_ref()
      .unwrap()
      .as_occupied_unchecked()
      .1
  }
  pub fn value(&self) -> Option<&V> {
    Some(&self.as_occupied()?.rl.as_ref().unwrap().as_occupied()?.1)
  }
  pub fn key(&self) -> &K {
    match self {
      Entry::Vacant(ref entry) => &entry.key,
      Entry::Occupied(entry) => &entry.rl.as_ref().unwrap().as_occupied_unchecked().0,
      Entry::Uninit => unreachable!(),
    }
  }
}

#[derive(Debug)]
pub enum TryRemoveError {
  WouldBlock,
  DoesNotExist,
}

pub type TryRemoveResult<K, V> = Result<(K, V), TryRemoveError>;

impl<'map, K: Hash + PartialEq, V, S: BuildHasher> Entry<'map, K, V, S> {
  pub fn or_insert<'this>(&'this mut self, value: V) -> &'this V {
    if self.as_occupied().is_some() {
      return self.value_unchecked();
    }
    let entry = core::mem::replace(self, Entry::Uninit);
    let VacantEntry { map, key } = entry.to_vacant_unchecked();
    *self = match map.insert(key, value) {
      Ok(r) => r,
      Err(InsertionError::AlreadyExists(r)) => r,
      _ => unreachable!(),
    };
    self.value_unchecked()
  }

  pub fn remove(self) -> Option<(K, V)> {
    match self {
      Entry::Vacant(entry) => {
        let entry = entry.map.entry(entry.key);
        if entry.as_occupied().is_none() {
          return None;
        }
        entry.remove()
      }
      Entry::Occupied(entry) => {
        let old = core::mem::replace(&mut *entry.rl.unwrap().into_write(), State::Removed);
        match old {
          State::Occupied(kv) => Some(kv),
          _ => None,
        }
      }
      Entry::Uninit => unreachable!(),
    }
  }

  pub fn try_remove(self) -> TryRemoveResult<K, V> {
    match self {
      Entry::Vacant(entry) => {
        let entry = entry.map.entry(entry.key);
        if entry.as_occupied().is_none() {
          return Err(TryRemoveError::DoesNotExist);
        }
        entry.try_remove()
      }
      Entry::Occupied(entry) => match entry.rl.unwrap().try_into_write() {
        Ok(mut res) => Ok(core::mem::replace(&mut *res, State::Removed).to_occupied_unchecked()),
        Err(_) => Err(TryRemoveError::WouldBlock),
      },
      Entry::Uninit => unreachable!(),
    }
  }
}

#[derive(Debug)]
pub struct ConMap<K, V, S = RandomState> {
  data: RwSpin<Container<K, V>>,
  build_hasher: S,
  help_tasks: ConStack<(usize, usize)>,
  help_count: AtomicUsize,
}

impl<K, V> Default for ConMap<K, V, RandomState> {
  fn default() -> Self {
    Self {
      data: Default::default(),
      build_hasher: Default::default(),
      help_tasks: Default::default(),
      help_count: Default::default(),
    }
  }
}

#[derive(Debug)]
pub enum InsertionError<E> {
  AlreadyExists(E),
  WouldBlock,
}

impl<E> Display for InsertionError<E> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.write_str(match self {
      InsertionError::AlreadyExists(_) => "AlreadyExists",
      InsertionError::WouldBlock => "WouldBlock",
    })
  }
}

impl<E: Debug> Error for InsertionError<E> {}

impl<K, V> ConMap<K, V, RandomState> {
  pub fn new() -> Self {
    Default::default()
  }

  pub fn with_capacity(cap: usize) -> Self {
    let mut data = Vec::with_capacity(cap);
    for _ in 0..data.capacity() {
      data.push(RwSpin::new(State::Vacant));
    }
    Self {
      data: RwSpin::new(data),
      build_hasher: Default::default(),
      help_tasks: Default::default(),
      help_count: Default::default(),
    }
  }
}

pub type InsertionResult<T, E> = Result<T, InsertionError<E>>;

impl<K: Hash + PartialEq, V, S: BuildHasher> ConMap<K, V, S> {
  fn realloc_internal(&self, mut data: RwSpinWriteGuard<Container<K, V>>) {
    let mut new_cap = data.capacity() << 4;
    if new_cap == 0 {
      new_cap = 50;
    }
    let old_data = data
      .iter()
      .map(|spin| spin.write().take())
      .filter(|item| item.is_occupied())
      .map(|item| item.to_occupied_unchecked())
      .collect::<Vec<_>>();
    let old_len = data.len();
    data.reserve(new_cap - old_len);
    let new_cap = data.capacity();
    let remaining = new_cap - old_len;
    data.resize_with(remaining, Default::default);
    for (key, value) in old_data {
      self.insert_unchecked_no_ret(&data, key, value);
    }
  }

  fn try_realloc(&self) -> Option<()> {
    self.realloc_internal(self.data.try_write()?);
    Some(())
  }

  fn realloc(&self) {
    self.realloc_internal(self.data.write());
  }

  pub fn insert<'map>(
    &'map self,
    mut key: K,
    mut value: V,
  ) -> InsertionResult<Entry<'map, K, V, S>, Entry<'map, K, V, S>> {
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

  pub fn try_insert<'map>(
    &'map self,
    mut key: K,
    mut value: V,
  ) -> InsertionResult<Entry<'map, K, V, S>, Entry<'map, K, V, S>> {
    loop {
      match self.try_insert_unchecked(key, value) {
        Ok(ins_res) => return ins_res,
        Err(kv) => {
          (key, value) = kv;
        }
      }
      if self.try_realloc().is_none() {
        return Err(InsertionError::WouldBlock);
      }
    }
  }

  pub fn entry<'map>(&'map self, key: K) -> Entry<'map, K, V, S> {
    use State::*;
    let data = self.data.read();
    let cap = data.capacity();
    if cap == 0 {
      return Entry::Vacant(VacantEntry { key, map: self });
    }
    let mut hasher = self.build_hasher.build_hasher();
    key.hash(&mut hasher);

    let mut hash = hasher.finish() as usize % cap;
    for _ in 0..cap {
      // SAFETY: hash is always in bounds of data
      let cell = unsafe { data.get_unchecked(hash) };

      let cell_read = cell.read();
      match &*cell_read {
        Occupied((k, _)) if k == &key => {
          return Entry::Occupied(OccupiedEntry::new(data.clone(), hash))
        }
        Vacant => break,
        Removed | Occupied(_) => {}
      };
      hash = (hash + HASH_STEP) % cap;
    }
    return Entry::Vacant(VacantEntry { key, map: self });
  }

  fn insert_unchecked_no_ret(&self, data: &Container<K, V>, key: K, value: V) {
    let _ = self.insert_unchecked_internal(data, key, value);
  }

  fn insert_unchecked_internal<'map>(
    &'map self,
    data: &'map Container<K, V>,
    key: K,
    value: V,
  ) -> Result<
    InsertionResult<(usize, RwSpinReadGuard<State<K, V>>), (usize, RwSpinReadGuard<State<K, V>>)>,
    (K, V),
  > {
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
      let cell_read = cell.read();
      if !cell_read.is_occupied() {
        let mut cell_write = cell_read.into_write();
        let _old = core::mem::replace(&mut *cell_write, State::Occupied((key, value)));
        // debug_assert!(_old == Vacant || _old == Removed);
        return Ok(Ok((hash, cell_write.into())));
      }
      let (k, _) = &*cell_read.as_occupied_unchecked();
      if k == &key {
        return Ok(Err(InsertionError::AlreadyExists((hash, cell_read))));
      }
      hash = (hash + HASH_STEP) % cap;
    }
    return Err((key, value));
  }

  fn try_insert_unchecked<'map>(
    &'map self,
    key: K,
    value: V,
  ) -> Result<InsertionResult<Entry<'map, K, V, S>, Entry<'map, K, V, S>>, (K, V)> {
    let data = self.data.try_read();
    if data.is_none() {
      return Ok(Err(InsertionError::WouldBlock));
    }
    let data = data.unwrap();

    let acquire_access = |(idx, rl)| {
      let res = Entry::Occupied(OccupiedEntry::new(data.clone(), idx));
      drop(rl);
      res
    };

    self.insert_unchecked_internal(&data, key, value).map(|v| {
      v.map(acquire_access).map_err(|err| match err {
        InsertionError::AlreadyExists(idx) => InsertionError::AlreadyExists(acquire_access(idx)),
        InsertionError::WouldBlock => InsertionError::WouldBlock,
      })
    })
  }

  fn insert_unchecked<'map>(
    &'map self,
    key: K,
    value: V,
  ) -> Result<InsertionResult<Entry<'map, K, V, S>, Entry<'map, K, V, S>>, (K, V)> {
    let data = self.data.read();
    let acquire_access = |(idx, rl)| {
      let res = Entry::Occupied(OccupiedEntry::new(data.clone(), idx));
      drop(rl);
      res
    };
    self.insert_unchecked_internal(&data, key, value).map(|v| {
      v.map(acquire_access).map_err(|err| match err {
        InsertionError::AlreadyExists(idx) => InsertionError::AlreadyExists(acquire_access(idx)),
        InsertionError::WouldBlock => InsertionError::WouldBlock,
      })
    })
  }
}

unsafe impl<K: Send, V: Send, S: Send> Send for ConMap<K, V, S> {}
unsafe impl<K: Sync, V: Sync, S: Sync> Sync for ConMap<K, V, S> {}

impl<K, V, S> ConMap<K, V, S> {
  pub fn iter<'map>(&'map self) -> Iter<'map, K, V, S> {
    Iter {
      idx: 0,
      data: self.data.read(),
      _phantom: Default::default(),
    }
  }

  pub fn with_hasher(build_hasher: S) -> Self {
    Self {
      data: Default::default(),
      build_hasher,
      help_tasks: Default::default(),
      help_count: Default::default(),
    }
  }

  pub fn with_capacity_and_hasher(cap: usize, build_hasher: S) -> Self {
    let mut data = Vec::with_capacity(cap);
    for _ in 0..data.capacity() {
      data.push(Default::default());
    }
    Self {
      data: RwSpin::new(data),
      build_hasher,
      help_tasks: Default::default(),
      help_count: Default::default(),
    }
  }
}

pub struct Iter<'map, K, V, S> {
  idx: usize,
  data: RwSpinReadGuard<'map, Container<K, V>>,
  _phantom: PhantomData<S>,
}

impl<'map, K: Hash + PartialEq<K> + 'map, V: 'map, S: 'map> Iterator for Iter<'map, K, V, S> {
  type Item = Entry<'map, K, V, S>;

  fn next(&mut self) -> Option<Self::Item> {
    for i in self.idx..self.data.capacity() {
      let cell = unsafe { self.data.get_unchecked(i) }.read();
      if cell.is_occupied() {
        return Some(Entry::Occupied(OccupiedEntry::new(self.data.clone(), i)));
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
    assert!(b.remove() == Some(("b", "b")));
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
