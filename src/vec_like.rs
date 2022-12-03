use std::borrow::Borrow;
use std::slice;
use tree_core;

#[derive(Debug, Clone)]
pub struct VecLike<'a, K: 'a, V: 'a> {
    tree: &'a tree_core::Tree<K, V>,
}
impl<'a, K: 'a, V: 'a> VecLike<'a, K, V> {
    pub fn new(tree: &'a tree_core::Tree<K, V>) -> Self {
        VecLike { tree: tree }
    }
    pub fn len(&self) -> usize {
        self.tree.len()
    }
    pub fn get(&self, index: usize) -> Option<(&'a K, &'a V)> {
        if index < self.tree.len() {
            Some(self.tree.node_ref(index as tree_core::NodeIndex).into())
        } else {
            None
        }
    }
    pub fn first(&self) -> Option<(&'a K, &'a V)> {
        self.get(0)
    }
    pub fn last(&self) -> Option<(&'a K, &'a V)> {
        let last = self.tree.len().wrapping_sub(1);
        self.get(last)
    }
    pub fn iter(&self) -> Iter<'a, K, V> {
        Iter(self.tree.nodes_iter())
    }
}

#[derive(Debug)]
pub struct VecLikeMut<'a, K: 'a, V: 'a> {
    tree: &'a mut tree_core::Tree<K, V>,
}
impl<'a, K: 'a, V: 'a> VecLikeMut<'a, K, V>
where
    K: Ord,
{
    pub fn push(&mut self, key: K, value: V) -> bool {
        if self.tree.contains_key(&key) {
            false
        } else {
            self.tree.insert(key, value);
            true
        }
    }
    pub fn pop(&mut self) -> Option<(K, V)> {
        self.tree.pop_last()
    }
    pub fn find_index<Q: ?Sized>(&mut self, key: &Q) -> Option<usize>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        if self.tree.contains_key(key) {
            self.tree.root().map(|i| i as usize)
        } else {
            None
        }
    }
}
impl<'a, K: 'a, V: 'a> VecLikeMut<'a, K, V> {
    pub fn new(tree: &'a mut tree_core::Tree<K, V>) -> Self {
        VecLikeMut { tree: tree }
    }
    pub fn len(&self) -> usize {
        self.tree.len()
    }
    pub fn get(&self, index: usize) -> Option<(&K, &V)> {
        if index < self.tree.len() {
            Some(self.tree.node_ref(index as tree_core::NodeIndex).into())
        } else {
            None
        }
    }
    #[allow(dead_code)]
    pub fn get_mut(&mut self, index: usize) -> Option<(&K, &mut V)> {
        if index < self.tree.len() {
            Some(self.tree.node_mut(index as tree_core::NodeIndex).into())
        } else {
            None
        }
    }
    pub fn first(&self) -> Option<(&K, &V)> {
        self.get(0)
    }
    #[allow(dead_code)]
    pub fn first_mut(&mut self) -> Option<(&K, &mut V)> {
        self.get_mut(0)
    }
    pub fn last(&self) -> Option<(&K, &V)> {
        let last = self.tree.len().wrapping_sub(1);
        self.get(last)
    }
    #[allow(dead_code)]
    pub fn last_mut(&mut self) -> Option<(&K, &mut V)> {
        let last = self.tree.len().wrapping_sub(1);
        self.get_mut(last)
    }
    pub fn iter(&self) -> Iter<K, V> {
        Iter(self.tree.nodes_iter())
    }
    #[allow(dead_code)]
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut(self.tree.nodes_iter_mut())
    }
}

pub struct Iter<'a, K: 'a, V: 'a>(slice::Iter<'a, tree_core::Node<K, V>>);
impl<'a, K: 'a, V: 'a> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|n| n.into())
    }
}

pub struct IterMut<'a, K: 'a, V: 'a>(slice::IterMut<'a, tree_core::Node<K, V>>);
impl<'a, K: 'a, V: 'a> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|n| n.into())
    }
}
