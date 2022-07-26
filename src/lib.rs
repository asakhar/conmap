use std::{
  cell::UnsafeCell,
  collections::hash_map::DefaultHasher,
  fmt::Debug,
  hash::{Hash, Hasher},
  sync::{
    atomic::{AtomicUsize, Ordering},
    RwLock, RwLockReadGuard,
  },
};

const EMPTY: usize = 0;
const REMOVED: usize = 1;
const UNINITIALIZED: usize = 2;

type ContainerItem<K, V> = (UnsafeCell<Option<K>>, UnsafeCell<Option<V>>, AtomicUsize);
type Container<K, V> = Vec<ContainerItem<K, V>>;

#[derive(Debug)]
pub struct OccupiedEntry<'map, K, V> {
  idx: usize,
  data: RwLockReadGuard<'map, Container<K, V>>,
}

impl<'map, K, V> OccupiedEntry<'map, K, V> {
  fn get_value(&self) -> &V {
    unsafe { &*self.data.get_unchecked(self.idx).1.get() }
      .as_ref()
      .unwrap()
  }
  fn get_key(&self) -> &K {
    unsafe { &*self.data.get_unchecked(self.idx).0.get() }
      .as_ref()
      .unwrap()
  }
}

#[derive(Debug)]
pub struct VacantEntry<'map, K, V> {
  key: Option<K>,
  map: &'map ConMap<K, V>,
}

#[derive(Debug)]
pub enum Entry<'map, K, V> {
  Vacant(VacantEntry<'map, K, V>),
  Occupied(OccupiedEntry<'map, K, V>),
}

impl<'map, K, V> Drop for Entry<'map, K, V> {
  fn drop(&mut self) {
    if let Entry::Occupied(entry) = self {
      unsafe { entry.data.get_unchecked(entry.idx) }
        .2
        .fetch_sub(1, Ordering::Relaxed);
    }
  }
}
impl<'map, K, V> Entry<'map, K, V> {
  const fn as_occupied_unchecked(&self) -> &OccupiedEntry<'map, K, V> {
    match self {
      Entry::Vacant(_) => panic!("Called as_occupied on vacant entry"),
      Entry::Occupied(entry) => entry,
    }
  }
  #[allow(dead_code)]
  const fn as_vacant_unchecked(&self) -> &VacantEntry<'map, K, V> {
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
  const fn as_vacant(&self) -> Option<&VacantEntry<'map, K, V>> {
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

impl<'map, K: Hash + PartialEq, V> Entry<'map, K, V> {
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
}

pub type InsertionResult<T> = Result<T, T>;

#[derive(Debug)]
pub struct ConMap<K, V> {
  data: RwLock<Container<K, V>>,
}

impl<K: Hash + PartialEq, V> ConMap<K, V> {
  fn realloc(&self) {
    let mut data = self.data.write().unwrap();
    let new_cap = data.capacity() << 4;
    let old_data = data
      .iter()
      .filter(|(_, _, state)| state.load(Ordering::Relaxed) > UNINITIALIZED)
      .map(|(key, value, _)| unsafe { ((*key.get()).take(), (*value.get()).take()) })
      .collect::<Vec<_>>();
    let old_len = data.len();
    data.reserve(new_cap - old_len);
    for item in data.iter_mut() {
      item.0.get_mut().take();
      item.1.get_mut().take();
      item.2.store(EMPTY, Ordering::Relaxed);
    }
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
      self.insert_unchecked_no_ret(&data, key.unwrap(), value.unwrap());
    }
  }

  pub fn with_capacity(cap: usize) -> Self {
    let mut data = Vec::with_capacity(cap);
    for _ in 0..cap {
      data.push((
        UnsafeCell::new(None),
        UnsafeCell::new(None),
        AtomicUsize::new(0),
      ));
    }
    Self {
      data: RwLock::new(data),
    }
  }
  pub fn insert<'map>(&'map self, mut key: K, mut value: V) -> InsertionResult<Entry<'map, K, V>> {
    loop {
      match self.insert_unchecked(key, value) {
        Ok(ins_res) => return ins_res,
        Err((k, v)) => {
          key = k;
          value = v
        }
      }
      self.realloc();
    }
  }

  pub fn entry(&self, key: K) -> Entry<K, V> {
    let mut hasher = DefaultHasher::new();
    key.hash(&mut hasher);
    let data = self.data.read().unwrap();
    let cap = data.capacity();

    let mut hash = hasher.finish() as usize % cap;
    'outer: for _ in 0..cap {
      // SAFETY: hash is always in bounds of data
      let cell = unsafe { data.get_unchecked(hash) };

      loop {
        let current_state = cell.2.load(Ordering::SeqCst);
        if current_state == EMPTY {
          break 'outer;
        }
        if current_state == REMOVED {
          break;
        }
        if current_state == usize::MAX || current_state == UNINITIALIZED {
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
      hash = (hash + 1337) % cap;
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
    let mut hasher = DefaultHasher::new();
    key.hash(&mut hasher);
    let cap = data.capacity();
    let mut hash = hasher.finish() as usize % cap;

    for _ in 0..cap {
      // SAFETY: hash is always in bounds of data
      let cell = unsafe { data.get_unchecked(hash) };
      loop {
        let state = cell.2.load(Ordering::SeqCst);

        if state < UNINITIALIZED {
          if cell
            .2
            .compare_exchange(state, UNINITIALIZED, Ordering::SeqCst, Ordering::Relaxed)
            .is_ok()
          {
            unsafe { *cell.0.get() = Some(key) };
            unsafe { *cell.1.get() = Some(value) };

            cell.2.store(UNINITIALIZED + 2, Ordering::SeqCst);
            return Ok(Ok(hash));
          }
          continue;
        }

        if state == usize::MAX || state == UNINITIALIZED {
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
      hash = (hash + 1337) % cap;
    }
    return Err((key, value));
  }

  fn insert_unchecked<'map>(
    &'map self,
    key: K,
    value: V,
  ) -> Result<InsertionResult<Entry<'map, K, V>>, (K, V)> {
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

unsafe impl<K: Send, V: Send> Send for ConMap<K, V> {}
unsafe impl<K: Sync, V: Sync> Sync for ConMap<K, V> {}

impl<K, V> ConMap<K, V> {
  pub fn iter<'map>(&'map self) -> Iter<'map, K, V> {
    Iter {
      idx: 0,
      data: self.data.read().unwrap(),
      rwlock: &self.data,
    }
  }
}

pub struct Iter<'map, K, V> {
  idx: usize,
  data: RwLockReadGuard<'map, Container<K, V>>,
  rwlock: &'map RwLock<Container<K, V>>,
}

impl<'map, K: Hash + PartialEq<K>, V> Iterator for Iter<'map, K, V> {
  type Item = Entry<'map, K, V>;

  fn next(&mut self) -> Option<Self::Item> {
    'outer: for i in self.idx..self.data.capacity() {
      let cell = unsafe { self.data.get_unchecked(i) };
      loop {
        let current_state = cell.2.load(Ordering::SeqCst);
        if current_state <= REMOVED {
          continue 'outer;
        }
        if current_state == usize::MAX || current_state == UNINITIALIZED {
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
        assert!(cell.2.load(Ordering::SeqCst) > UNINITIALIZED);
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
}
