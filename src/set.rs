//! A set based on splay tree.
use std;
use std::ops;
use std::cmp;
use std::iter::Peekable;
use std::borrow::Borrow;
use core;
use iter;

/// A set based on splay tree.
///
/// A splay tree based set is a self-adjusting data structure.
/// It performs insertion, removal and look-up in `O(log n)` amortized time.
///
/// It is a logic error for a key to be modified in such a way that
/// the key's ordering relative to any other key,
/// as determined by the `Ord` trait, changes while it is in the map.
/// This is normally only possible through `Cell`, `RefCell`, global state, I/O, or unsafe code.
///
/// # Examples
/// ```
/// use splay_tree::SplaySet;
///
/// let mut set = SplaySet::new();
///
/// set.insert("foo");
/// set.insert("bar");
/// set.insert("baz");
/// assert_eq!(set.len(), 3);
///
/// assert!(set.contains("bar"));
/// assert!(set.remove("bar"));
/// assert!(!set.contains("bar"));
/// // TODO
/// // assert_eq!(vec!["baz", "foo"], set.into_iter().collect::<Vec<_>>());
/// ```
#[derive(Debug,Clone,Hash,PartialEq,Eq,PartialOrd,Ord)]
pub struct SplaySet<T> {
    tree: core::Tree<T, ()>,
}
impl<T> SplaySet<T>
    where T: Ord
{
    /// Makes a new SplaySet
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplaySet;
    ///
    /// let set: SplaySet<()> = SplaySet::new();
    /// assert!(set.is_empty());
    /// ```
    pub fn new() -> Self {
        SplaySet { tree: core::Tree::new() }
    }

    /// Clears the set, removing all values.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplaySet;
    ///
    /// let mut set = SplaySet::new();
    /// set.insert("foo");
    /// set.clear();
    /// assert!(set.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.tree = core::Tree::new();
    }

    /// Returns true if the set contains a value.
    ///
    /// The value may be any borrowed form of the set's value type,
    /// but the ordering on the borrowed form _must_ match the ordering on the value type.
    ///
    /// Because `SplaySet` is a self-adjusting amortized data structure,
    /// this function requires the `mut` qualifier for `self`.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplaySet;
    ///
    /// let mut set = SplaySet::new();
    /// set.insert("foo");
    /// assert!(set.contains("foo"));
    /// assert!(!set.contains("bar"));
    /// ```
    pub fn contains<Q: ?Sized>(&mut self, value: &Q) -> bool
        where T: Borrow<Q>,
              Q: Ord
    {
        self.tree.contains_key(value)
    }

    /// Returns a reference to the value in the set, if any, that is equal to the given value.
    ///
    /// The value may be any borrowed form of the set's value type,
    /// but the ordering on the borrowed form _must_ match the ordering on the value type.
    ///
    /// Because `SplaySet` is a self-adjusting amortized data structure,
    /// this function requires the `mut` qualifier for `self`.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplaySet;
    ///
    /// let mut set = SplaySet::new();
    /// set.insert("foo");
    /// assert_eq!(set.get("foo"), Some(&"foo"));
    /// assert_eq!(set.get("bar"), None);
    /// ```
    pub fn get<Q: ?Sized>(&mut self, value: &Q) -> Option<&T>
        where T: Borrow<Q>,
              Q: Ord
    {
        if self.tree.get(value).is_some() {
            self.tree.root.as_ref().map(|n| &n.key)
        } else {
            None
        }
    }

    /// Finds a minimum element which
    /// satisfies "greater than or equal to `value`" condition in the set.
    ///
    /// The value may be any borrowed form of the set's value type,
    /// but the ordering on the borrowed form _must_ match the ordering on the value type.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplaySet;
    ///
    /// let mut set = SplaySet::new();
    /// set.insert(1);
    /// set.insert(3);
    ///
    /// assert_eq!(set.find_lower_bound(&0), Some(&1));
    /// assert_eq!(set.find_lower_bound(&1), Some(&1));
    /// assert_eq!(set.find_lower_bound(&4), None);
    /// ```
    pub fn find_lower_bound<Q: ?Sized>(&mut self, value: &Q) -> Option<&T>
        where T: Borrow<Q>,
              Q: Ord
    {
        self.tree.find_lower_bound(value)
    }

    /// Finds a minimum element which satisfies "greater than `value`" condition in the set.
    ///
    /// The value may be any borrowed form of the set's value type,
    /// but the ordering on the borrowed form _must_ match the ordering on the value type.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplaySet;
    ///
    /// let mut set = SplaySet::new();
    /// set.insert(1);
    /// set.insert(3);
    ///
    /// assert_eq!(set.find_upper_bound(&0), Some(&1));
    /// assert_eq!(set.find_upper_bound(&1), Some(&3));
    /// assert_eq!(set.find_upper_bound(&4), None);
    /// ```
    pub fn find_upper_bound<Q: ?Sized>(&mut self, value: &Q) -> Option<&T>
        where T: Borrow<Q>,
              Q: Ord
    {
        self.tree.find_upper_bound(value)
    }

    /// Adds a value to the set.
    ///
    /// If the set did not have this value present, `true` is returned.
    ///
    /// If the set did have this value present, `false` is returned,
    /// and the entry is not updated.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplaySet;
    ///
    /// let mut set = SplaySet::new();
    /// assert!(set.insert("foo"));
    /// assert!(!set.insert("foo"));
    /// assert_eq!(set.len(), 1);
    /// ```
    pub fn insert(&mut self, value: T) -> bool {
        self.tree.insert(value, ()).is_none()
    }

    /// Adds a value to the set, replacing the existing value, if any,
    /// that is equal to the given one.
    /// Returns the replaced value.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplaySet;
    ///
    /// let mut set = SplaySet::new();
    /// assert_eq!(set.replace("foo"), None);
    /// assert_eq!(set.replace("foo"), Some("foo"));
    /// ```
    pub fn replace(&mut self, value: T) -> Option<T> {
        let old = self.take(&value);
        self.insert(value);
        old
    }

    /// Removes a value from the set. Returns `true` is the value was present in the set.
    ///
    /// The value may be any borrowed form of the set's value type,
    /// but the ordering on the borrowed form _must_ match the ordering on the value type.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplaySet;
    ///
    /// let mut set = SplaySet::new();
    /// set.insert("foo");
    /// assert_eq!(set.remove("foo"), true);
    /// assert_eq!(set.remove("foo"), false);
    /// ```
    pub fn remove<Q: ?Sized>(&mut self, value: &Q) -> bool
        where T: Borrow<Q>,
              Q: Ord
    {
        self.tree.remove(value).is_some()
    }

    /// Removes and returns the value in the set, if any, that is equal to the given one.
    ///
    /// The value may be any borrowed form of the set's value type,
    /// but the ordering on the borrowed form _must_ match the ordering on the value type.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplaySet;
    ///
    /// let mut set = SplaySet::new();
    /// set.insert("foo");
    /// assert_eq!(set.take("foo"), Some("foo"));
    /// assert_eq!(set.take("foo"), None);
    /// ```
    pub fn take<Q: ?Sized>(&mut self, value: &Q) -> Option<T>
        where T: Borrow<Q>,
              Q: Ord
    {
        if self.contains(value) {
            self.tree.pop_root().map(|(e, _)| e)
        } else {
            None
        }
    }

    /// Visits the values representing the difference, in ascending order.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplaySet;
    ///
    /// let a: SplaySet<_> = vec![1, 2, 3].into_iter().collect();
    /// let b: SplaySet<_> = vec![2, 3, 4].into_iter().collect();
    ///
    /// assert_eq!(a.difference(&b).cloned().collect::<Vec<_>>(),
    ///            [1]);
    /// ```
    pub fn difference<'a>(&'a self, other: &'a Self) -> Difference<'a, T> {
        Difference(self.iter().peekable(), other.iter().peekable())
    }

    /// Visits the values representing the symmetric difference, in ascending order.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplaySet;
    ///
    /// let a: SplaySet<_> = vec![1, 2, 3].into_iter().collect();
    /// let b: SplaySet<_> = vec![2, 3, 4].into_iter().collect();
    ///
    /// assert_eq!(a.symmetric_difference(&b).cloned().collect::<Vec<_>>(),
    ///            [1, 4]);
    /// ```
    pub fn symmetric_difference<'a>(&'a self, other: &'a Self) -> SymmetricDifference<'a, T> {
        SymmetricDifference(self.iter().peekable(), other.iter().peekable())
    }

    /// Visits the values representing the intersection, in ascending order.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplaySet;
    ///
    /// let a: SplaySet<_> = vec![1, 2, 3].into_iter().collect();
    /// let b: SplaySet<_> = vec![2, 3, 4].into_iter().collect();
    ///
    /// assert_eq!(a.intersection(&b).cloned().collect::<Vec<_>>(),
    ///            [2, 3]);
    /// ```
    pub fn intersection<'a>(&'a self, other: &'a Self) -> Intersection<'a, T> {
        Intersection(self.iter().peekable(), other.iter().peekable())
    }

    /// Visits the values representing the union, in ascending order.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplaySet;
    ///
    /// let a: SplaySet<_> = vec![1, 2, 3].into_iter().collect();
    /// let b: SplaySet<_> = vec![2, 3, 4].into_iter().collect();
    ///
    /// assert_eq!(a.union(&b).cloned().collect::<Vec<_>>(),
    ///            [1, 2, 3, 4]);
    /// ```
    pub fn union<'a>(&'a self, other: &'a Self) -> Union<'a, T> {
        Union(self.iter().peekable(), other.iter().peekable())
    }

    /// Returns `true` if the set has no elements in common with `other`.
    /// This is equivalent to checking for an empty intersection.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplaySet;
    ///
    /// let a: SplaySet<_> = vec![1, 2, 3].into_iter().collect();
    /// let b: SplaySet<_> = vec![2, 3, 4].into_iter().collect();
    /// let c: SplaySet<_> = vec![4, 5, 6].into_iter().collect();
    ///
    /// assert!(!a.is_disjoint(&b));
    /// assert!(!b.is_disjoint(&c));
    /// assert!(a.is_disjoint(&c));
    /// assert!(c.is_disjoint(&a));
    /// ```
    pub fn is_disjoint(&self, other: &Self) -> bool {
        self.intersection(other).count() == 0
    }

    /// Returns `true` if the set is a subset of another.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplaySet;
    ///
    /// let a: SplaySet<_> = vec![1, 2, 3].into_iter().collect();
    /// let b: SplaySet<_> = vec![2, 3, 4].into_iter().collect();
    /// let c: SplaySet<_> = vec![1, 2, 3, 4].into_iter().collect();
    ///
    /// assert!(!a.is_subset(&b));
    /// assert!(!b.is_subset(&a));
    /// assert!(!c.is_subset(&a));
    /// assert!(a.is_subset(&c));
    /// assert!(b.is_subset(&c));
    /// assert!(c.is_subset(&c));
    /// ```
    pub fn is_subset(&self, other: &Self) -> bool {
        self.difference(other).count() == 0
    }

    /// Returns `true` if the set is a superset of another.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplaySet;
    ///
    /// let a: SplaySet<_> = vec![1, 2, 3].into_iter().collect();
    /// let b: SplaySet<_> = vec![2, 3, 4].into_iter().collect();
    /// let c: SplaySet<_> = vec![1, 2, 3, 4].into_iter().collect();
    ///
    /// assert!(!a.is_superset(&b));
    /// assert!(!b.is_superset(&a));
    /// assert!(!a.is_superset(&c));
    /// assert!(c.is_superset(&a));
    /// assert!(c.is_superset(&b));
    /// assert!(c.is_superset(&c));
    /// ```
    pub fn is_superset(&self, other: &Self) -> bool {
        other.is_subset(self)
    }
}
impl<T> SplaySet<T> {
    /// Returns the number of elements in the set.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplaySet;
    ///
    /// let mut set = SplaySet::new();
    /// set.insert("foo");
    /// set.insert("bar");
    /// assert_eq!(set.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.tree.len
    }

    /// Returns true if the set contains no elements.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplaySet;
    ///
    /// let mut set = SplaySet::new();
    /// assert!(set.is_empty());
    ///
    /// set.insert("foo");
    /// assert!(!set.is_empty());
    ///
    /// set.clear();
    /// assert!(set.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Gets an iterator over the SplaySet's contents, in sorted order.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplaySet;
    ///
    /// let mut set = SplaySet::new();
    /// set.insert("foo");
    /// set.insert("bar");
    /// set.insert("baz");
    ///
    /// assert_eq!(set.iter().collect::<Vec<_>>(), [&"bar", &"baz", &"foo"]);
    /// ```
    pub fn iter(&self) -> Iter<T> {
        Iter::new(self)
    }
}
impl<T> Default for SplaySet<T>
    where T: Ord
{
    fn default() -> Self {
        SplaySet::new()
    }
}
impl<T> std::iter::FromIterator<T> for SplaySet<T>
    where T: Ord
{
    fn from_iter<I>(iter: I) -> Self
        where I: IntoIterator<Item = T>
    {
        let mut set = SplaySet::new();
        for x in iter {
            set.insert(x);
        }
        set
    }
}
impl<T> IntoIterator for SplaySet<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(iter::IntoIter::new(self.tree))
    }
}
impl<'a, T> IntoIterator for &'a SplaySet<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        Iter::new(self)
    }
}
impl<T> Extend<T> for SplaySet<T>
    where T: Ord
{
    fn extend<I>(&mut self, iter: I)
        where I: IntoIterator<Item = T>
    {
        for x in iter {
            self.insert(x);
        }
    }
}
impl<'a, T> Extend<&'a T> for SplaySet<T>
    where T: Copy + 'a + Ord
{
    fn extend<I>(&mut self, iter: I)
        where I: IntoIterator<Item = &'a T>
    {
        for x in iter {
            self.insert(*x);
        }
    }
}
impl<'a, 'b, T> ops::Sub<&'b SplaySet<T>> for &'a SplaySet<T>
    where T: Ord + Clone
{
    type Output = SplaySet<T>;

    /// Returns the difference of `self` and `rhs` as a new `SplaySet<T>`.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplaySet;
    ///
    /// let a: SplaySet<_> = vec![1, 2, 3].into_iter().collect();
    /// let b: SplaySet<_> = vec![3, 4, 5].into_iter().collect();
    ///
    /// assert_eq!((&a - &b).into_iter().collect::<Vec<_>>(),
    ///            [1, 2]);
    /// ```
    fn sub(self, rhs: &SplaySet<T>) -> SplaySet<T> {
        self.difference(rhs).cloned().collect()
    }
}
impl<'a, 'b, T> ops::BitXor<&'b SplaySet<T>> for &'a SplaySet<T>
    where T: Ord + Clone
{
    type Output = SplaySet<T>;

    /// Returns the symmetric difference of `self` and `rhs` as a new `SplaySet<T>`.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplaySet;
    ///
    /// let a: SplaySet<_> = vec![1, 2, 3].into_iter().collect();
    /// let b: SplaySet<_> = vec![3, 4, 5].into_iter().collect();
    ///
    /// assert_eq!((&a ^ &b).into_iter().collect::<Vec<_>>(),
    ///            [1, 2, 4, 5]);
    /// ```
    fn bitxor(self, rhs: &SplaySet<T>) -> SplaySet<T> {
        self.symmetric_difference(rhs).cloned().collect()
    }
}
impl<'a, 'b, T> ops::BitAnd<&'b SplaySet<T>> for &'a SplaySet<T>
    where T: Ord + Clone
{
    type Output = SplaySet<T>;

    /// Returns the intersection of `self` and `rhs` as a new `SplaySet<T>`.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplaySet;
    ///
    /// let a: SplaySet<_> = vec![1, 2, 3].into_iter().collect();
    /// let b: SplaySet<_> = vec![3, 4, 5].into_iter().collect();
    ///
    /// assert_eq!((&a & &b).into_iter().collect::<Vec<_>>(),
    ///            [3]);
    /// ```
    fn bitand(self, rhs: &SplaySet<T>) -> SplaySet<T> {
        self.intersection(rhs).cloned().collect()
    }
}
impl<'a, 'b, T> ops::BitOr<&'b SplaySet<T>> for &'a SplaySet<T>
    where T: Ord + Clone
{
    type Output = SplaySet<T>;

    /// Returns the union of `self` and `rhs` as a new `SplaySet<T>`.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplaySet;
    ///
    /// let a: SplaySet<_> = vec![1, 2, 3].into_iter().collect();
    /// let b: SplaySet<_> = vec![3, 4, 5].into_iter().collect();
    ///
    /// assert_eq!((&a | &b).into_iter().collect::<Vec<_>>(),
    ///            [1, 2, 3, 4, 5]);
    /// ```
    fn bitor(self, rhs: &SplaySet<T>) -> SplaySet<T> {
        self.union(rhs).cloned().collect()
    }
}

/// An Iterator over a SplaySet items.
pub struct Iter<'a, T: 'a>(iter::Iter<'a, T, ()>);
impl<'a, T: 'a> Iter<'a, T> {
    fn new(set: &'a SplaySet<T>) -> Self {
        Iter(iter::Iter::new(&set.tree))
    }
}
impl<'a, T: 'a> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(e, _)| e)
    }
}

/// An owning iterator over a SplaySet's items.
pub struct IntoIter<T>(iter::IntoIter<T, ()>);
impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(e, _)| e)
    }
}

fn item_cmp<T>(a: Option<&T>, b: Option<&T>) -> Option<cmp::Ordering>
    where T: Ord
{
    match (a, b) {
        (None, None) => None,
        (Some(_), None) => Some(cmp::Ordering::Less),
        (None, Some(_)) => Some(cmp::Ordering::Greater),
        (Some(a), Some(b)) => Some(a.cmp(b)),
    }
}

/// A lazy iterator producing elements in the set difference (in-order).
pub struct Difference<'a, T: 'a>(Peekable<Iter<'a, T>>, Peekable<Iter<'a, T>>);
impl<'a, T: 'a> Iterator for Difference<'a, T>
    where T: Ord
{
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match item_cmp(self.0.peek(), self.1.peek()) {
                None => return None,
                Some(cmp::Ordering::Less) => return self.0.next(),
                Some(cmp::Ordering::Greater) => {
                    self.1.next();
                }
                Some(cmp::Ordering::Equal) => {
                    self.0.next();
                    self.1.next();
                }
            }
        }
    }
}

/// A lazy iterator producing elements in the set symmetric difference (in-order).
pub struct SymmetricDifference<'a, T: 'a>(Peekable<Iter<'a, T>>, Peekable<Iter<'a, T>>);
impl<'a, T: 'a> Iterator for SymmetricDifference<'a, T>
    where T: Ord
{
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match item_cmp(self.0.peek(), self.1.peek()) {
                None => return None,
                Some(cmp::Ordering::Less) => return self.0.next(),
                Some(cmp::Ordering::Greater) => return self.1.next(),
                Some(cmp::Ordering::Equal) => {
                    self.0.next();
                    self.1.next();
                }
            }
        }
    }
}

/// A lazy iterator producing elements in the set intersection (in-order).
pub struct Intersection<'a, T: 'a>(Peekable<Iter<'a, T>>, Peekable<Iter<'a, T>>);
impl<'a, T: 'a> Iterator for Intersection<'a, T>
    where T: Ord
{
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match item_cmp(self.0.peek(), self.1.peek()) {
                None => return None,
                Some(cmp::Ordering::Less) => {
                    self.0.next();
                }
                Some(cmp::Ordering::Greater) => {
                    self.1.next();
                }
                Some(cmp::Ordering::Equal) => {
                    self.0.next();
                    return self.1.next();
                }
            }
        }
    }
}

/// A lazy iterator producing elements in the set union (in-order).
pub struct Union<'a, T: 'a>(Peekable<Iter<'a, T>>, Peekable<Iter<'a, T>>);
impl<'a, T: 'a> Iterator for Union<'a, T>
    where T: Ord
{
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match item_cmp(self.0.peek(), self.1.peek()) {
                None => return None,
                Some(cmp::Ordering::Less) => return self.0.next(),
                Some(cmp::Ordering::Greater) => return self.1.next(),
                Some(cmp::Ordering::Equal) => {
                    self.0.next();
                    return self.1.next();
                }
            }
        }
    }
}
