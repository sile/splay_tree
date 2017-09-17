//! A priority queue implemented with a splay tree.
use std;
use std::cmp;
use tree_core;
use iter;

/// `SplayHeap` iterator.
pub struct Iter<'a, T: 'a> {
    iter: iter::Iter<'a, Item<T>, ()>,
}
impl<'a, T: 'a> Iter<'a, T> {
    fn new(tree: &'a tree_core::Tree<Item<T>, ()>) -> Self {
        Iter { iter: tree.iter() }
    }
}
impl<'a, T: 'a> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(i, _)| &i.0)
    }
}

/// An iterator that moves out of a `SplayHeap`.
pub struct IntoIter<T>(iter::IntoIter<Item<T>, ()>);
impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, _)| k.0)
    }
}

#[derive(Debug,Clone,PartialEq,Eq,PartialOrd)]
struct Item<T>(T, u64);
impl<T> Ord for Item<T>
    where T: Ord
{
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        match self.0.cmp(&other.0) {
            cmp::Ordering::Equal => self.1.cmp(&other.1),
            cmp::Ordering::Less => cmp::Ordering::Greater,
            cmp::Ordering::Greater => cmp::Ordering::Less,
        }
    }
}

/// A priority queue implemented with a splay tree.
///
/// This will be a max-heap.
///
/// A splay tree based heap is a self-adjusting data structure.
/// It performs pushing and popping in `O(log n)` amortized time.
///
/// It is a logic error for a key to be modified in such a way that
/// the key's ordering relative to any other key,
/// as determined by the `Ord` trait, changes while it is in the map.
/// This is normally only possible through `Cell`, `RefCell`, global state, I/O, or unsafe code.
///
/// # Examples
/// ```
/// use splay_tree::SplayHeap;
///
/// let mut heap = SplayHeap::new();
///
/// heap.push(0);
/// heap.push(10);
/// heap.push(7);
///
/// assert_eq!(heap.peek(), Some(&10));
/// assert_eq!(heap.pop(), Some(10));
/// assert_eq!(heap.pop(), Some(7));
/// assert_eq!(heap.pop(), Some(0));
/// assert_eq!(heap.pop(), None);
/// ```
#[derive(Debug,Clone)]
pub struct SplayHeap<T> {
    tree: tree_core::Tree<Item<T>, ()>,
    seq: u64,
}
impl<T> SplayHeap<T>
    where T: Ord
{
    /// Creates an empty `SplayHeap` as a max-heap.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayHeap;
    /// let mut heap = SplayHeap::new();
    ///
    /// heap.push(10);
    /// assert_eq!(heap.pop(), Some(10));
    /// ```
    pub fn new() -> Self {
        SplayHeap {
            tree: tree_core::Tree::new(),
            seq: 0,
        }
    }

    /// Returns the greatest item in the heap, or `None` if it is empty.
    ///
    /// # NOTICE
    /// Because `SplayHeap` is a self-adjusting amortized data structure,
    /// this function requires the `mut` qualifier.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayHeap;
    /// let mut heap = SplayHeap::new();
    /// assert_eq!(heap.peek(), None);
    ///
    /// heap.push(1);
    /// heap.push(5);
    /// heap.push(2);
    /// assert_eq!(heap.peek(), Some(&5));
    /// ```
    pub fn peek(&mut self) -> Option<&T> {
        self.tree.get_lftmost().map(|(i, _)| &i.0)
    }

    /// Removes the greatest item from the heap and returns it, or `None` if it is empty.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayHeap;
    /// let mut heap: SplayHeap<_> = vec![1, 3].into_iter().collect();
    ///
    /// assert_eq!(heap.pop(), Some(3));
    /// assert_eq!(heap.pop(), Some(1));
    /// assert_eq!(heap.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        self.tree.take_lftmost().map(|(i, _)| i.0)
    }

    /// Pushes an item onto the heap.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayHeap;
    /// let mut heap = SplayHeap::new();
    /// heap.push(3);
    /// heap.push(5);
    /// heap.push(1);
    ///
    /// assert_eq!(heap.len(), 3);
    /// assert_eq!(heap.peek(), Some(&5));
    /// ```
    pub fn push(&mut self, item: T) {
        let seq = self.seq;
        self.seq = seq.wrapping_add(1);
        self.tree.insert(Item(item, seq), ());
    }

    /// Drops all items from the heap.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayHeap;
    /// let mut heap: SplayHeap<_> = vec![1, 3].into_iter().collect();
    ///
    /// assert!(!heap.is_empty());
    /// heap.clear();
    /// assert!(heap.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.tree = tree_core::Tree::new();
    }
}
impl<T> SplayHeap<T> {
    /// Returns an iterator visiting all items in sorted (descending) order.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayHeap;
    /// let heap: SplayHeap<_> = vec![1, 4, 2, 3].into_iter().collect();
    ///
    /// // Print all values in `heap` in sorted order
    /// for x in heap.iter() {
    ///   println!("{}", x);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<T> {
        Iter::new(&self.tree)
    }

    /// Returns the length of the heap.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayHeap;
    /// let heap: SplayHeap<_> = vec![1, 3].into_iter().collect();
    ///
    /// assert_eq!(heap.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.tree.len()
    }

    /// Checkes if the heap is empty.
    ///
    /// # Examples
    /// ```
    /// use splay_tree::SplayHeap;
    /// let mut heap = SplayHeap::new();
    ///
    /// assert!(heap.is_empty());
    ///
    /// heap.push(1);
    /// assert!(!heap.is_empty());
    ///
    /// heap.pop();
    /// assert!(heap.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}
impl<T> Default for SplayHeap<T>
    where T: Ord
{
    fn default() -> Self {
        SplayHeap::new()
    }
}
impl<T> std::iter::FromIterator<T> for SplayHeap<T>
    where T: Ord
{
    fn from_iter<I>(iter: I) -> Self
        where I: IntoIterator<Item = T>
    {
        let mut heap = SplayHeap::new();
        for x in iter {
            heap.push(x);
        }
        heap
    }
}
impl<T> IntoIterator for SplayHeap<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.tree.into_iter())
    }
}
impl<'a, T> IntoIterator for &'a SplayHeap<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
impl<T> Extend<T> for SplayHeap<T>
    where T: Ord
{
    fn extend<I>(&mut self, iter: I)
        where I: IntoIterator<Item = T>
    {
        for x in iter {
            self.push(x);
        }
    }
}
impl<'a, T> Extend<&'a T> for SplayHeap<T>
    where T: Copy + 'a + Ord
{
    fn extend<I>(&mut self, iter: I)
        where I: IntoIterator<Item = &'a T>
    {
        for x in iter {
            self.push(*x);
        }
    }
}
