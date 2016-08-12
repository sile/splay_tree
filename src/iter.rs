//! Iterators for splay tree
use core::Node;
use core::Tree;

enum Visit<E, N> {
    Elem(E),
    Node(N),
}

pub struct Iter<'a, K: 'a, V: 'a> {
    stack: Vec<Visit<(&'a K, &'a V), &'a Node<K, V>>>,
}
impl<'a, K: 'a, V: 'a> Iter<'a, K, V> {
    pub fn new(tree: &'a Tree<K, V>) -> Self {
        if let Some(root) = tree.root.as_ref() {
            Iter { stack: vec![Visit::Node(root)] }
        } else {
            Iter { stack: vec![] }
        }
    }
}
impl<'a, K: 'a, V: 'a> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(v) = self.stack.pop() {
            match v {
                Visit::Node(n) => {
                    n.rgt.as_ref().map(|rgt| self.stack.push(Visit::Node(rgt)));
                    self.stack.push(Visit::Elem((&n.key, &n.val)));
                    n.lft.as_ref().map(|lft| self.stack.push(Visit::Node(lft)));
                }
                Visit::Elem(e) => {
                    return Some(e);
                }
            }
        }
        None
    }
}

pub struct IntoIter<K, V> {
    stack: Vec<Visit<(K, V), Node<K, V>>>,
}
impl<K, V> IntoIter<K, V> {
    pub fn new(tree: Tree<K, V>) -> Self {
        if let Some(root) = tree.root {
            IntoIter { stack: vec![Visit::Node(*root)] }
        } else {
            IntoIter { stack: vec![] }
        }
    }
}
impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(v) = self.stack.pop() {
            match v {
                Visit::Node(mut n) => {
                    n.rgt.take().map(|rgt| self.stack.push(Visit::Node(*rgt)));
                    self.stack.push(Visit::Elem((n.key, n.val)));
                    n.lft.take().map(|lft| self.stack.push(Visit::Node(*lft)));
                }
                Visit::Elem(e) => {
                    return Some(e);
                }
            }
        }
        None
    }
}

pub struct IterMut<'a, K: 'a, V: 'a> {
    stack: Vec<Visit<(&'a K, &'a mut V), &'a mut Node<K, V>>>,
}
impl<'a, K: 'a, V: 'a> IterMut<'a, K, V> {
    pub fn new(tree: &'a mut Tree<K, V>) -> Self {
        if let Some(root) = tree.root.as_mut() {
            IterMut { stack: vec![Visit::Node(root)] }
        } else {
            IterMut { stack: vec![] }
        }
    }
}
impl<'a, K: 'a, V: 'a> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(v) = self.stack.pop() {
            match v {
                Visit::Node(n) => {
                    n.rgt.as_mut().map(|rgt| self.stack.push(Visit::Node(rgt)));
                    self.stack.push(Visit::Elem((&n.key, &mut n.val)));
                    n.lft.as_mut().map(|lft| self.stack.push(Visit::Node(lft)));
                }
                Visit::Elem(e) => {
                    return Some(e);
                }
            }
        }
        None
    }
}
