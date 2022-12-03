//! Iterators for splay tree
use crate::tree_core::Node;
use crate::tree_core::NodeIndex;
use std::mem;
use std::vec::Vec;

pub type MaybeNodeIndex = Option<NodeIndex>;

pub trait Nodes {
    type Entry;
    fn get_node(&mut self, index: NodeIndex) -> (Self::Entry, MaybeNodeIndex, MaybeNodeIndex);
}

enum Visit<E> {
    Elem(E),
    Node(NodeIndex),
}

pub struct InOrderIter<N>
where
    N: Nodes,
{
    nodes: N,
    stack: Vec<Visit<N::Entry>>,
}
impl<N> InOrderIter<N>
where
    N: Nodes,
{
    pub fn new(root: MaybeNodeIndex, nodes: N) -> Self {
        InOrderIter {
            nodes,
            stack: root.map(Visit::Node).into_iter().collect(),
        }
    }
}
impl<N> Iterator for InOrderIter<N>
where
    N: Nodes,
{
    type Item = N::Entry;
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(v) = self.stack.pop() {
            match v {
                Visit::Node(n) => {
                    let (e, lft, rgt) = self.nodes.get_node(n);
                    if let Some(rgt) = rgt {
                        self.stack.push(Visit::Node(rgt))
                    }
                    self.stack.push(Visit::Elem(e));
                    if let Some(lft) = lft {
                        self.stack.push(Visit::Node(lft))
                    }
                }
                Visit::Elem(e) => {
                    return Some(e);
                }
            }
        }
        None
    }
}

pub type Iter<'a, K, V> = InOrderIter<&'a [Node<K, V>]>;
impl<'a, K: 'a, V: 'a> Nodes for &'a [Node<K, V>] {
    type Entry = (&'a K, &'a V);
    fn get_node(&mut self, index: NodeIndex) -> (Self::Entry, MaybeNodeIndex, MaybeNodeIndex) {
        let n = unsafe { self.get_unchecked(index as usize) };
        (n.into(), n.lft(), n.rgt())
    }
}

pub type IterMut<'a, K, V> = InOrderIter<&'a mut [Node<K, V>]>;
impl<'a, K: 'a, V: 'a> Nodes for &'a mut [Node<K, V>] {
    type Entry = (&'a K, &'a mut V);
    fn get_node(&mut self, index: NodeIndex) -> (Self::Entry, MaybeNodeIndex, MaybeNodeIndex) {
        let n = unsafe { self.get_unchecked_mut(index as usize) };
        let (lft, rgt) = (n.lft(), n.rgt());
        let n = unsafe { &mut *(n as *mut _) as &mut Node<_, _> };
        (n.into(), lft, rgt)
    }
}

pub type IntoIter<K, V> = InOrderIter<OwnedNodes<K, V>>;
pub struct OwnedNodes<K, V>(pub(crate) Vec<Option<Node<K, V>>>);
impl<K, V> Nodes for OwnedNodes<K, V> {
    type Entry = (K, V);
    fn get_node(&mut self, index: NodeIndex) -> (Self::Entry, MaybeNodeIndex, MaybeNodeIndex) {
        let n = mem::take(self.0.get_mut(index as usize).expect("bug")).expect("bug");
        let (lft, rgt) = (n.lft(), n.rgt());
        (n.into(), lft, rgt)
    }
}
impl<K, V> Drop for OwnedNodes<K, V> {
    fn drop(&mut self) {
        let is_sentinel = |n: &Node<_, _>| n.lft().is_some() && n.lft() == n.rgt();
        for e in self.0.drain(..).flatten() {
            if is_sentinel(&e) {
                mem::forget(e);
            }
        }
    }
}
