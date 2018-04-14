//! A map based on a splay tree.
use std;
use std::mem;
use std::borrow::Borrow;
use tree_core;
use iter;

/// A map based on a splay tree.
///
/// A splay tree based map is a self-adjusting data structure.
/// It performs insertion, removal and look-up in `O(log n)` amortized time.
///
/// It is a logic error for a key to be modified in such a way that
/// the key's ordering relative to any other key,
/// as determined by the `Ord` trait, changes while it is in the map.
/// This is normally only possible through `Cell`, `RefCell`, global state, I/O, or unsafe code.
///
/// # Examples
/// ```
/// use splay_tree::SplayMap;
///
/// let mut map = SplayMap::new();
///
/// map.insert("foo", 1);
/// map.insert("bar", 2);
/// map.insert("baz", 3);
///
/// assert_eq!(map.get("foo"), Some(&1));
/// assert_eq!(map.remove("foo"), Some(1));
/// assert_eq!(map.get("foo"), None);
///
/// for (k, v) in &map {
///     println!("{}: {}", k, v);
/// }
/// ```
///
/// `SplayMap` implements an [Entry API](#method.entry) which allows for
/// more complex methods of getting, setting, updating and removing keys and their values:
/// ```
/// extern crate rand;
/// extern crate splay_tree;
///
/// use splay_tree::SplayMap;
///
/// # fn main() {
/// let mut count = SplayMap::new();
/// for _ in 0..1000 {
///     let k = rand::random::<u8>();
///     *count.entry(k).or_insert(0) += 1;
/// }
/// for k in 0..0x100 {
///     println!("{}: {}", k, count.get(&k).unwrap_or(&0));
/// }
/// # }
/// ```
#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct SplayMap<K, V> {
    tree: tree_core::Tree<K, V>,
}
impl<K, V> SplayMap<K, V>
where
    K: Ord,
{
    /// Makes a new empty `SplayMap`.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayMap;
    ///
    /// let mut map = SplayMap::new();
    /// map.insert("foo", 1);
    /// assert_eq!(map.len(), 1);
    /// ```
    pub fn new() -> Self {
        SplayMap { tree: tree_core::Tree::new() }
    }

    /// Clears the map, removing all values.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayMap;
    ///
    /// let mut map = SplayMap::new();
    /// map.insert("foo", 1);
    /// map.clear();
    /// assert!(map.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.tree = tree_core::Tree::new();
    }

    /// Returns true if the map contains a value for the specified key.
    ///
    /// The key may be any borrowed form of the map's key type,
    /// but the ordering on the borrowed form _must_ match the ordering on the key type.
    ///
    /// # Notice
    ///
    /// Because `SplayMap` is a self-adjusting amortized data structure,
    /// this function requires the `mut` qualifier for `self`.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayMap;
    ///
    /// let mut map = SplayMap::new();
    /// map.insert("foo", 1);
    /// assert!(map.contains_key("foo"));
    /// assert!(!map.contains_key("bar"));
    /// ```
    pub fn contains_key<Q: ?Sized>(&mut self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.tree.contains_key(key)
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type,
    /// but the ordering on the borrowed form _must_ match the ordering on the key type.
    ///
    /// # Notice
    ///
    /// Because `SplayMap` is a self-adjusting amortized data structure,
    /// this function requires the `mut` qualifier for `self`.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayMap;
    ///
    /// let mut map = SplayMap::new();
    /// map.insert("foo", 1);
    /// assert_eq!(map.get("foo"), Some(&1));
    /// assert_eq!(map.get("bar"), None);
    /// ```
    pub fn get<Q: ?Sized>(&mut self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.get_mut(key).map(|v| &*v)
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type,
    /// but the ordering on the borrowed form _must_ match the ordering on the key type.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayMap;
    ///
    /// let mut map = SplayMap::new();
    /// map.insert("foo", 1);
    /// map.get_mut("foo").map(|v| *v = 2);
    /// assert_eq!(map.get("foo"), Some(&2));
    /// ```
    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.tree.get(key)
    }

    /// Finds a minimum key which satisfies "greater than or equal to `key`" condition in the map.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayMap;
    ///
    /// let mut map = SplayMap::new();
    /// map.insert(1, ());
    /// map.insert(3, ());
    ///
    /// assert_eq!(map.find_lower_bound_key(&0), Some(&1));
    /// assert_eq!(map.find_lower_bound_key(&1), Some(&1));
    /// assert_eq!(map.find_lower_bound_key(&4), None);
    /// ```
    pub fn find_lower_bound_key<Q: ?Sized>(&mut self, key: &Q) -> Option<&K>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.tree.find_lower_bound(key)
    }

    /// Finds a minimum key which satisfies "greater than `key`" condition in the map.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayMap;
    ///
    /// let mut map = SplayMap::new();
    /// map.insert(1, ());
    /// map.insert(3, ());
    ///
    /// assert_eq!(map.find_upper_bound_key(&0), Some(&1));
    /// assert_eq!(map.find_upper_bound_key(&1), Some(&3));
    /// assert_eq!(map.find_upper_bound_key(&4), None);
    /// ```
    pub fn find_upper_bound_key<Q: ?Sized>(&mut self, key: &Q) -> Option<&K>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.tree.find_upper_bound(key)
    }

    /// Gets the entry which have the minimum key in the map.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayMap;
    ///
    /// let mut map = SplayMap::new();
    /// map.insert(1, ());
    /// map.insert(3, ());
    ///
    /// assert_eq!(map.smallest(), Some((&1, &())));
    /// ```
    pub fn smallest(&mut self) -> Option<(&K, &V)> {
        self.tree.get_lftmost()
    }

    /// Takes the entry which have the minimum key in the map.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayMap;
    ///
    /// let mut map = SplayMap::new();
    /// map.insert(1, ());
    /// map.insert(3, ());
    ///
    /// assert_eq!(map.take_smallest(), Some((1, ())));
    /// assert_eq!(map.take_smallest(), Some((3, ())));
    /// assert_eq!(map.take_smallest(), None);
    /// ```
    pub fn take_smallest(&mut self) -> Option<(K, V)> {
        self.tree.take_lftmost()
    }

    /// Gets the entry which have the maximum key in the map.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayMap;
    ///
    /// let mut map = SplayMap::new();
    /// map.insert(1, ());
    /// map.insert(3, ());
    ///
    /// assert_eq!(map.largest(), Some((&3, &())));
    /// ```
    pub fn largest(&mut self) -> Option<(&K, &V)> {
        self.tree.get_rgtmost()
    }

    /// Takes the entry which have the maximum key in the map.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayMap;
    ///
    /// let mut map = SplayMap::new();
    /// map.insert(1, ());
    /// map.insert(3, ());
    ///
    /// assert_eq!(map.take_largest(), Some((3, ())));
    /// assert_eq!(map.take_largest(), Some((1, ())));
    /// assert_eq!(map.take_largest(), None);
    /// ```
    pub fn take_largest(&mut self) -> Option<(K, V)> {
        self.tree.take_rgtmost()
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, `None` is  returned.
    ///
    /// If the map did have this key present, the value is updated,
    /// and the old value is returned.
    /// The key is not updated, though;
    /// this matters for types that can be `==` without being identical.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayMap;
    ///
    /// let mut map = SplayMap::new();
    /// assert_eq!(map.insert("foo", 1), None);
    /// assert_eq!(map.get("foo"), Some(&1));
    /// assert_eq!(map.insert("foo", 2), Some(1));
    /// assert_eq!(map.get("foo"), Some(&2));
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.tree.insert(key, value)
    }

    /// Removes a key from the map,
    /// returning the value at the key if the key was previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type,
    /// but the ordering on the borrowed form _must_ match the ordering on the key type.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayMap;
    ///
    /// let mut map = SplayMap::new();
    /// map.insert("foo", 1);
    /// assert_eq!(map.remove("foo"), Some(1));
    /// assert_eq!(map.remove("foo"), None);
    /// ```
    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.tree.remove(key)
    }

    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayMap;
    ///
    /// let mut count = SplayMap::new();
    ///
    /// // count the number of occurrences of letters in the vec
    /// for x in vec!["a", "b", "a", "c", "a", "b"] {
    ///     *count.entry(x).or_insert(0) += 1;
    /// }
    ///
    /// assert_eq!(count.get("a"), Some(&3));
    /// ```
    pub fn entry(&mut self, key: K) -> Entry<K, V> {
        if self.contains_key(&key) {
            Entry::Occupied(OccupiedEntry { tree: &mut self.tree })
        } else {
            Entry::Vacant(VacantEntry {
                key: key,
                tree: &mut self.tree,
            })
        }
    }
}
impl<K, V> SplayMap<K, V> {
    /// Returns the number of elements in the map.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayMap;
    ///
    /// let mut map = SplayMap::new();
    /// map.insert("foo", 1);
    /// map.insert("bar", 2);
    /// assert_eq!(map.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.tree.len()
    }

    /// Returns true if the map contains no elements.
    ///
    /// #  Examples
    /// ```
    /// use splay_tree::SplayMap;
    ///
    /// let mut map = SplayMap::new();
    /// assert!(map.is_empty());
    ///
    /// map.insert("foo", 1);
    /// assert!(!map.is_empty());
    ///
    /// map.clear();
    /// assert!(map.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Gets an iterator over the entries of the map, sorted by key.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayMap;
    ///
    /// let map: SplayMap<_, _> =
    ///     vec![("foo", 1), ("bar", 2), ("baz", 3)].into_iter().collect();
    /// assert_eq!(vec![(&"bar", &2), (&"baz", &3), (&"foo", &1)],
    ///            map.iter().collect::<Vec<_>>());
    /// ```
    pub fn iter(&self) -> Iter<K, V> {
        Iter::new(&self.tree)
    }

    /// Gets a mutable iterator over the entries of the map, soretd by key.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayMap;
    ///
    /// let mut map: SplayMap<_, _> =
    ///     vec![("foo", 1), ("bar", 2), ("baz", 3)].into_iter().collect();
    /// for (_, v) in map.iter_mut() {
    ///    *v += 10;
    /// }
    /// assert_eq!(map.get("bar"), Some(&12));
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut::new(&mut self.tree)
    }

    /// Gets an iterator over the keys of the map, in sorted order.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayMap;
    ///
    /// let map: SplayMap<_, _> =
    ///     vec![("foo", 1), ("bar", 2), ("baz", 3)].into_iter().collect();
    /// assert_eq!(vec!["bar", "baz", "foo"],
    ///            map.keys().cloned().collect::<Vec<_>>());
    /// ```
    pub fn keys(&self) -> Keys<K, V> {
        Keys::new(&self.tree)
    }

    /// Gets an iterator over the values of the map, in order by key.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayMap;
    ///
    /// let map: SplayMap<_, _> =
    ///     vec![("foo", 1), ("bar", 2), ("baz", 3)].into_iter().collect();
    /// assert_eq!(vec![2, 3, 1],
    ///            map.values().cloned().collect::<Vec<_>>());
    /// ```
    pub fn values(&self) -> Values<K, V> {
        Values::new(&self.tree)
    }

    /// Gets a mutable iterator over the values of the map, in order by key.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayMap;
    ///
    /// let mut map: SplayMap<_, _> =
    ///     vec![("foo", 1), ("bar", 2), ("baz", 3)].into_iter().collect();
    /// for v in map.values_mut() {
    ///     *v += 10;
    /// }
    /// assert_eq!(vec![12, 13, 11],
    ///            map.values().cloned().collect::<Vec<_>>());
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<K, V> {
        ValuesMut::new(&mut self.tree)
    }
}
impl<K, V> Default for SplayMap<K, V>
where
    K: Ord,
{
    fn default() -> Self {
        SplayMap::new()
    }
}
impl<K, V> std::iter::FromIterator<(K, V)> for SplayMap<K, V>
where
    K: Ord,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = (K, V)>,
    {
        let mut map = SplayMap::new();
        for (k, v) in iter {
            map.insert(k, v);
        }
        map
    }
}
impl<'a, K, V> IntoIterator for &'a SplayMap<K, V>
where
    K: 'a,
    V: 'a,
{
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        Iter::new(&self.tree)
    }
}
impl<'a, K, V> IntoIterator for &'a mut SplayMap<K, V>
where
    K: 'a,
    V: 'a,
{
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        IterMut::new(&mut self.tree)
    }
}
impl<K, V> IntoIterator for SplayMap<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self.tree)
    }
}
impl<K, V> Extend<(K, V)> for SplayMap<K, V>
where
    K: Ord,
{
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = (K, V)>,
    {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}
impl<'a, K, V> Extend<(&'a K, &'a V)> for SplayMap<K, V>
where
    K: 'a + Copy + Ord,
    V: 'a + Copy,
{
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = (&'a K, &'a V)>,
    {
        for (k, v) in iter {
            self.insert(*k, *v);
        }
    }
}

/// An iterator over a SplayMap's entries.
pub struct Iter<'a, K: 'a, V: 'a>(iter::Iter<'a, K, V>);
impl<'a, K: 'a, V: 'a> Iter<'a, K, V> {
    fn new(tree: &'a tree_core::Tree<K, V>) -> Self {
        Iter(tree.iter())
    }
}
impl<'a, K: 'a, V: 'a> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

/// A mutable iterator over a SplayMap's entries.
pub struct IterMut<'a, K: 'a, V: 'a>(iter::IterMut<'a, K, V>);
impl<'a, K: 'a, V: 'a> IterMut<'a, K, V> {
    fn new(tree: &'a mut tree_core::Tree<K, V>) -> Self {
        IterMut(tree.iter_mut())
    }
}
impl<'a, K: 'a, V: 'a> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

/// An owning iterator over a SplayMap's entries.
pub struct IntoIter<K, V>(iter::IntoIter<K, V>);
impl<K, V> IntoIter<K, V> {
    fn new(tree: tree_core::Tree<K, V>) -> Self {
        IntoIter(tree.into_iter())
    }
}
impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

/// An iterator over a SplayMap's keys.
pub struct Keys<'a, K: 'a, V: 'a>(Iter<'a, K, V>);
impl<'a, K: 'a, V: 'a> Keys<'a, K, V> {
    fn new(tree: &'a tree_core::Tree<K, V>) -> Self {
        Keys(Iter::new(tree))
    }
}
impl<'a, K: 'a, V: 'a> Iterator for Keys<'a, K, V> {
    type Item = &'a K;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, _)| k)
    }
}

/// An iterator over a SplayMap's values.
pub struct Values<'a, K: 'a, V: 'a>(Iter<'a, K, V>);
impl<'a, K: 'a, V: 'a> Values<'a, K, V> {
    fn new(tree: &'a tree_core::Tree<K, V>) -> Self {
        Values(Iter::new(tree))
    }
}
impl<'a, K: 'a, V: 'a> Iterator for Values<'a, K, V> {
    type Item = &'a V;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(_, v)| v)
    }
}

/// A mutable iterator over a SplayMap's values.
pub struct ValuesMut<'a, K: 'a, V: 'a>(IterMut<'a, K, V>);
impl<'a, K: 'a, V: 'a> ValuesMut<'a, K, V> {
    fn new(tree: &'a mut tree_core::Tree<K, V>) -> Self {
        ValuesMut(IterMut::new(tree))
    }
}
impl<'a, K: 'a, V: 'a> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(_, v)| v)
    }
}

/// A view into a single entry in a map, which may either be vacant or occupied.
pub enum Entry<'a, K: 'a, V: 'a> {
    /// An occupied entry
    Occupied(OccupiedEntry<'a, K, V>),
    /// A vacant entry
    Vacant(VacantEntry<'a, K, V>),
}
impl<'a, K: 'a, V: 'a> Entry<'a, K, V>
where
    K: Ord,
{
    /// Returns a reference to this entry's key.
    pub fn key(&self) -> &K {
        match *self {
            Entry::Occupied(ref e) => e.key(),
            Entry::Vacant(ref e) => e.key(),
        }
    }

    /// Ensures a value is in the entry by inserting the default if empty,
    /// and returns a mutable reference to the value in the entry.
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(e) => e.into_mut(),
            Entry::Vacant(e) => e.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty,
    /// and returns a mutable reference to the value in the entry.
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(e) => e.into_mut(),
            Entry::Vacant(e) => e.insert(default()),
        }
    }
}

/// An occupied Entry.
pub struct OccupiedEntry<'a, K: 'a, V: 'a> {
    tree: &'a mut tree_core::Tree<K, V>,
}
impl<'a, K: 'a, V: 'a> OccupiedEntry<'a, K, V>
where
    K: Ord,
{
    /// Gets a reference to the key in the entry.
    pub fn key(&self) -> &K {
        &self.tree.root_ref().key
    }

    /// Gets a reference to the value in the entry.
    pub fn get(&self) -> &V {
        &self.tree.root_ref().val
    }

    /// Gets a mutable reference to the value in the entry.
    pub fn get_mut(&mut self) -> &mut V {
        &mut self.tree.root_mut().val
    }

    /// Converts the entry into a mutable reference to its value.
    pub fn into_mut(self) -> &'a mut V {
        &mut self.tree.root_mut().val
    }

    /// Sets the value of the entry with the OccupiedEntry's key,
    /// and returns the entry's old value.
    pub fn insert(&mut self, value: V) -> V {
        mem::replace(self.get_mut(), value)
    }

    /// Takes the value of the entry out of the map, and returns it.
    pub fn remove(self) -> V {
        self.tree.pop_root().unwrap().1
    }
}

/// A vacant Entry.
pub struct VacantEntry<'a, K: 'a, V: 'a> {
    key: K,
    tree: &'a mut tree_core::Tree<K, V>,
}
impl<'a, K: 'a, V: 'a> VacantEntry<'a, K, V>
where
    K: Ord,
{
    /// Gets a reference to the key that would be used
    /// when inserting a value through the VacantEntry.
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Sets the value of the entry with the VacantEntry's key,
    /// and returns a mutable reference to it.
    pub fn insert(self, value: V) -> &'a mut V {
        self.tree.insert(self.key, value);
        &mut self.tree.root_mut().val
    }
}
