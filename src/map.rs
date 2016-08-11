//! A map based on a B-Tree.
use std::mem;
use std::borrow::Borrow;
use core;

pub use core::Iter;

/// A map based on a B-Tree.
///
/// TODO
///
/// It is a logic error for a key to be modified in such a way that
/// the key's ordering relative to any other key,
/// as determined by the `Ord` trait, changes while it is in the map.
/// This is normally only possible through `Cell`, `RefCell`, global state, I/O, or unsafe code.
///
/// # Examples
///
/// TODO
///
/// `SplayMap` implements an [Entry API](#method.entry) which allows for
/// more complex methods of getting, setting, updating and removing keys and their values:
///
/// TODO
#[derive(Debug, Clone)]
pub struct SplayMap<K, V> {
    tree: core::Tree<K, V>,
}
impl<K, V> SplayMap<K, V>
    where K: Ord
{
    /// Makes a new empty `SplayMap`.
    ///
    /// # Examples
    ///
    pub fn new() -> Self {
        SplayMap { tree: core::Tree::new() }
    }
    pub fn clear(&mut self) {
        self.tree = core::Tree::new();
    }
    pub fn get<Q: ?Sized>(&mut self, key: &Q) -> Option<&V>
        where K: Borrow<Q>,
              Q: Ord
    {
        self.get_mut(key).map(|v| &*v)
    }
    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
        where K: Borrow<Q>,
              Q: Ord
    {
        self.tree.get(key)
    }
    pub fn find_lower_bound<Q: ?Sized>(&mut self, key: &Q) -> Option<&K>
        where K: Borrow<Q>,
              Q: Ord
    {
        self.tree.find_lower_bound(key)
    }
    pub fn find_upper_bound<Q: ?Sized>(&mut self, key: &Q) -> Option<&K>
        where K: Borrow<Q>,
              Q: Ord
    {
        self.tree.find_upper_bound(key)
    }
    pub fn contains_key<Q: ?Sized>(&mut self, key: &Q) -> bool
        where K: Borrow<Q>,
              Q: Ord
    {
        self.get(key).is_some()
    }
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.tree.insert(key, value)
    }
    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
        where K: Borrow<Q>,
              Q: Ord
    {
        self.tree.remove(key)
    }
    pub fn entry(&mut self, key: K) -> Entry<K, V> {
        if self.contains_key(&key) {
            Entry::Occupied(OccupiedEntry {
                key: key,
                tree: &mut self.tree,
            })
        } else {
            Entry::Vacant(VacantEntry {
                key: key,
                tree: &mut self.tree,
            })
        }
    }
}
impl<K, V> SplayMap<K, V> {
    pub fn len(&self) -> usize {
        self.tree.len
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub fn iter(&self) -> Iter<K, V> {
        self.tree.iter()
    }
    // TODO: iterator
}
impl<K, V> Default for SplayMap<K, V>
    where K: Ord
{
    fn default() -> Self {
        SplayMap::new()
    }
}

// TODO: move to core
pub enum Entry<'a, K: 'a, V: 'a> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}
impl<'a, K: 'a, V: 'a> Entry<'a, K, V>
    where K: Ord
{
    pub fn key(&self) -> &K {
        match *self {
            Entry::Occupied(ref e) => &e.key,
            Entry::Vacant(ref e) => &e.key,
        }
    }
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(e) => e.into_mut(),
            Entry::Vacant(e) => e.insert(default),
        }
    }
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(e) => e.into_mut(),
            Entry::Vacant(e) => e.insert(default()),
        }
    }
}

pub struct OccupiedEntry<'a, K: 'a, V: 'a> {
    key: K,
    tree: &'a mut core::Tree<K, V>,
}
impl<'a, K: 'a, V: 'a> OccupiedEntry<'a, K, V>
    where K: Ord
{
    pub fn key(&self) -> &K {
        &self.key
    }
    pub fn get(&self) -> &V {
        &self.tree.root.as_ref().unwrap().val
    }
    pub fn get_mut(&mut self) -> &mut V {
        &mut self.tree.root.as_mut().unwrap().val
    }
    pub fn into_mut(self) -> &'a mut V {
        &mut self.tree.root.as_mut().unwrap().val
    }
    pub fn insert(&mut self, value: V) -> V {
        mem::replace(self.tree.get(&self.key).unwrap(), value)
    }
    pub fn remove(self) -> V {
        self.tree.remove(&self.key).unwrap()
    }
}

pub struct VacantEntry<'a, K: 'a, V: 'a> {
    key: K,
    tree: &'a mut core::Tree<K, V>,
}
impl<'a, K: 'a, V: 'a> VacantEntry<'a, K, V>
    where K: Ord
{
    pub fn key(&self) -> &K {
        &self.key
    }
    pub fn insert(self, value: V) -> &'a mut V {
        self.tree.insert(self.key, value);
        &mut self.tree.root.as_mut().unwrap().val
    }
}
