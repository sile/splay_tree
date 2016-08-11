//! A priority queue implemented with a splay tree.
//!
//! `SplayHeap` is a self-adjusting heap data structure.
//! It performs pushing and popping in `O(log n)` amortized time.
use std::iter;
use std::cmp;
use core;

/// `SplayHeap` iterator.
pub struct Iter<'a, T: 'a> {
    iter: core::Iter<'a, Item<T>, ()>,
}
impl<'a, T: 'a> Iter<'a, T> {
    fn new(tree: &'a core::Tree<Item<T>, ()>) -> Self {
        Iter { iter: core::Iter::new(tree) }
    }
}
impl<'a, T: 'a> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(i, _)| &i.0)
    }
}

/// An iterator that moves out of a `SplayHeap`.
pub struct IntoIter<T>(SplayHeap<T>);
impl<T> Iterator for IntoIter<T>
    where T: Ord
{
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop()
    }
}

#[derive(Debug,Clone,PartialEq,Eq,PartialOrd)]
struct Item<T>(T);
impl<T> Ord for Item<T>
    where T: Ord
{
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        match self.0.cmp(&other.0) {
            cmp::Ordering::Equal => cmp::Ordering::Greater,
            cmp::Ordering::Less => cmp::Ordering::Greater,
            cmp::Ordering::Greater => cmp::Ordering::Less,
        }
    }
}

/// A priority queue implemented with a splay tree.
///
/// This will be a max-heap.
///
/// ### Examples
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
    tree: core::Tree<Item<T>, ()>,
}
impl<T> SplayHeap<T>
    where T: Ord
{
    /// Creates an empty `SplayHeap` as a max-heap.
    ///
    /// ### Examples
    /// ```
    /// use splay_tree::SplayHeap;
    /// let mut heap = SplayHeap::new();
    ///
    /// heap.push(10);
    /// assert_eq!(heap.pop(), Some(10));
    /// ```
    pub fn new() -> Self {
        SplayHeap { tree: core::Tree::new() }
    }

    /// Returns the greatest item in the heap, or `None` if it is empty.
    ///
    /// ### NOTICE
    /// Because `SplayHeap` is a self-adjusting amortized data structure,
    /// this function requires the `mut` qualifier.
    ///
    /// ### Examples
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
    /// ### Examples
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
    /// ### Examples
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
        self.tree.insert(Item(item), ());
    }

    /// Drops all items from the heap.
    ///
    /// ### Examples
    /// ```
    /// use splay_tree::SplayHeap;
    /// let mut heap: SplayHeap<_> = vec![1, 3].into_iter().collect();
    ///
    /// assert!(!heap.is_empty());
    /// heap.clear();
    /// assert!(heap.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.tree = core::Tree::new();
    }
}
impl<T> SplayHeap<T> {
    /// Returns an iterator visiting all items in sorted (ascending) order.
    ///
    /// ### Examples
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
    /// ### Examples
    /// ```
    /// use splay_tree::SplayHeap;
    /// let heap: SplayHeap<_> = vec![1, 3].into_iter().collect();
    ///
    /// assert_eq!(heap.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.tree.len
    }

    /// Checkes if the heap is empty.
    ///
    /// ### Examples
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
impl<T> iter::FromIterator<T> for SplayHeap<T>
    where T: Ord
{
    fn from_iter<I>(iter: I) -> Self
        where I: iter::IntoIterator<Item = T>
    {
        let mut heap = SplayHeap::new();
        for x in iter {
            heap.push(x);
        }
        heap
    }
}
impl<T> IntoIterator for SplayHeap<T>
    where T: Ord
{
    type Item = T;
    type IntoIter = IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self)
    }
}
impl<'a, T> IntoIterator for &'a SplayHeap<T>
    where T: Ord
{
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
