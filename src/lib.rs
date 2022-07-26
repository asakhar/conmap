use std::{
  cell::UnsafeCell,
  collections::hash_map::DefaultHasher,
  fmt::Debug,
  hash::{Hash, Hasher},
  marker::PhantomData,
  ptr,
  sync::{
    atomic::{AtomicPtr, AtomicUsize, Ordering},
    RwLock, RwLockReadGuard,
  },
};

const EMPTY: usize = 0;
const REMOVED: usize = 1;
const UNINITIALIZED: usize = 2;

#[derive(Debug)]
pub struct OccupiedEntry<'map, K, V> {
  idx: usize,
  data: RwLockReadGuard<'map, Vec<(AtomicPtr<K>, AtomicPtr<V>, AtomicUsize)>>,
}

impl<'map, K, V> OccupiedEntry<'map, K, V> {
  fn get_value(&self) -> &V {
    unsafe { &*self.data.get_unchecked(self.idx).1.load(Ordering::SeqCst) }
  }
  fn get_key(&self) -> &K {
    unsafe { &*self.data.get_unchecked(self.idx).0.load(Ordering::SeqCst) }
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
  data: RwLock<Vec<(AtomicPtr<K>, AtomicPtr<V>, AtomicUsize)>>,
  _phantom: PhantomData<UnsafeCell<(K, V)>>,
}

impl<K: Hash + PartialEq, V> ConMap<K, V> {
  fn realloc(&self) {
    let mut data = self.data.write().unwrap();
    let new_cap = data.capacity() << 2;
    let old_data = data
      .iter()
      .filter(|(_, _, state)| state.load(Ordering::Relaxed) > UNINITIALIZED)
      .map(|(key, value, _)| (key.load(Ordering::Relaxed), value.load(Ordering::Relaxed)))
      .collect::<Vec<_>>();
    data.clear();
    data.reserve(new_cap);
    let new_cap = data.capacity();
    for _ in 0..new_cap {
      data.push((
        AtomicPtr::new(ptr::null_mut()),
        AtomicPtr::new(ptr::null_mut()),
        AtomicUsize::new(0),
      ));
    }
    for (key, value) in old_data {
      self.insert_unchecked_no_ret(&data, key, value); //("Failed to insert value to reallocated array");
    }
  }

  pub fn with_capacity(cap: usize) -> Self {
    let mut data = Vec::with_capacity(cap);
    for _ in 0..cap {
      data.push((
        AtomicPtr::new(ptr::null_mut()),
        AtomicPtr::new(ptr::null_mut()),
        AtomicUsize::new(0),
      ));
    }
    Self {
      data: RwLock::new(data),
      _phantom: Default::default(),
    }
  }
  pub fn insert<'map>(&'map self, key: K, value: V) -> InsertionResult<Entry<'map, K, V>> {
    let key_raw_ptr = Box::into_raw(Box::new(key));
    let value_raw_ptr = Box::into_raw(Box::new(value));

    loop {
      if let Some(ins_res) = self.insert_unchecked(key_raw_ptr, value_raw_ptr) {
        return ins_res;
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
        let key_raw_ptr = cell.0.load(Ordering::SeqCst);
        let key_ref = unsafe { &*key_raw_ptr };
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

  fn insert_unchecked_no_ret<'map>(
    &'map self,
    data: &Vec<(AtomicPtr<K>, AtomicPtr<V>, AtomicUsize)>,
    key: *mut K,
    value: *mut V,
  ) {
    let release = |idx| {
      let cell: &(AtomicPtr<K>, AtomicPtr<V>, AtomicUsize) = unsafe { data.get_unchecked(idx) };
      cell.2.fetch_sub(1, Ordering::Relaxed);
    };
    let _ = self
      .insert_unchecked_internal(data, key, value)
      .map(|res| res.map(release).map_err(release));
  }

  fn insert_unchecked_internal<'map>(
    &'map self,
    data: &Vec<(AtomicPtr<K>, AtomicPtr<V>, AtomicUsize)>,
    key: *mut K,
    value: *mut V,
  ) -> Option<InsertionResult<usize>> {
    let mut hasher = DefaultHasher::new();
    let key_ref = unsafe { &*key };
    key_ref.hash(&mut hasher);
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
            cell
              .0
              .compare_exchange(ptr::null_mut(), key, Ordering::SeqCst, Ordering::Relaxed)
              .unwrap();

            cell.1.store(value, Ordering::SeqCst);
            cell.2.store(UNINITIALIZED + 2, Ordering::SeqCst);
            return Some(Ok(hash));
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
        let cell_key = unsafe { &*cell.0.load(Ordering::SeqCst) };
        if cell_key != key_ref {
          cell.2.fetch_sub(1, Ordering::Relaxed);
          break;
        }
        return Some(Err(hash));
      }
      hash = (hash + 1337) % cap;
    }
    return None;
  }

  fn insert_unchecked<'map>(
    &'map self,
    key: *mut K,
    value: *mut V,
  ) -> Option<InsertionResult<Entry<'map, K, V>>> {
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
  data: RwLockReadGuard<'map, Vec<(AtomicPtr<K>, AtomicPtr<V>, AtomicUsize)>>,
  rwlock: &'map RwLock<Vec<(AtomicPtr<K>, AtomicPtr<V>, AtomicUsize)>>,
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
}
