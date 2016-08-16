//! A vector with set-like lookup.
use std::borrow::Borrow;
use core;
use iter;

#[derive(Debug,Clone,Hash,PartialEq,Eq,PartialOrd,Ord)]
pub struct SplayVecSet<T> {
    tree: core::Tree<T, ()>,
}
impl<T> SplayVecSet<T>
    where T: Ord
{
    pub fn new() -> Self {
        SplayVecSet { tree: core::Tree::new() }
    }

    pub fn clear(&mut self) {
        self.tree = core::Tree::new();
    }

    pub fn push(&mut self, value: T) -> bool {
        self.tree.insert(value, ()).is_none()
    }

    pub fn pop(&mut self) -> Option<T> {
        self.tree.pop_last().map(|(k, _)| k)
    }

    pub fn contains<Q: ?Sized>(&mut self, value: &Q) -> bool
        where T: Borrow<Q>,
              Q: Ord
    {
        self.tree.contains_key(value)
    }

    pub fn find_lower_bound<Q: ?Sized>(&mut self, value: &Q) -> Option<&T>
        where T: Borrow<Q>,
              Q: Ord
    {
        self.tree.find_lower_bound(value)
    }

    pub fn find_upper_bound<Q: ?Sized>(&mut self, value: &Q) -> Option<&T>
        where T: Borrow<Q>,
              Q: Ord
    {
        self.tree.find_upper_bound(value)
    }

    pub fn find_index<Q: ?Sized>(&mut self, value: &Q) -> Option<usize>
        where T: Borrow<Q>,
              Q: Ord
    {
        self.contains(value);
        self.tree.root().map(|i| i as usize)
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        if index < self.len() {
            Some(&self.tree.node_ref(index as core::NodeIndex).key)
        } else {
            None
        }
    }
}
impl<T> SplayVecSet<T> {
    pub fn len(&self) -> usize {
        self.tree.len()
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    // pub fn iter(&self) -> Iter<T> {
    //     Iter::new(self)
    // }
}
