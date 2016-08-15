//! Iterators for splay tree
use core::Node;
use core::NodeIndex;
use core::Tree;

enum Visit<E, N> {
    Elem(E),
    Node(N),
}

pub struct Iter<'a, K: 'a, V: 'a> {
    tree: &'a Tree<K, V>,
    stack: Vec<Visit<(&'a K, &'a V), NodeIndex>>,
}
impl<'a, K: 'a, V: 'a> Iter<'a, K, V> {
    pub fn new(tree: &'a Tree<K, V>) -> Self {
        Iter {
            tree: tree,
            stack: if let Some(root) = tree.root() {
                vec![Visit::Node(root)]
            } else {
                vec![]
            },
        }
    }
}
impl<'a, K: 'a, V: 'a> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(v) = self.stack.pop() {
            match v {
                Visit::Node(n) => {
                    let n = self.tree.node_ref(n);
                    n.rgt().map(|rgt| self.stack.push(Visit::Node(rgt)));
                    self.stack.push(Visit::Elem((&n.key, &n.val)));
                    n.lft().map(|lft| self.stack.push(Visit::Node(lft)));
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
    tree: Tree<K, V>,
}
impl<K, V> IntoIter<K, V> {
    pub fn new(tree: Tree<K, V>) -> Self {
        IntoIter { tree: tree }
    }
}
// TODO: Delete Ord
impl<K, V> Iterator for IntoIter<K, V>
    where K: Ord
{
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        self.tree.take_lftmost()
    }
}

pub struct IterMut<'a, K: 'a, V: 'a> {
    tree: &'a mut Tree<K, V>,
    // stack: Vec<Visit<(&'a K, &'a mut V), NodeIndex>>,
    stack: Vec<Visit<*mut Node<K, V>, NodeIndex>>,
}
impl<'a, K: 'a, V: 'a> IterMut<'a, K, V> {
    pub fn new(tree: &'a mut Tree<K, V>) -> Self {
        let root = tree.root();
        IterMut {
            tree: tree,
            stack: if let Some(root) = root {
                vec![Visit::Node(root)]
            } else {
                vec![]
            },
        }
    }
}
impl<'a, K: 'a, V: 'a> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(v) = self.stack.pop() {
            match v {
                Visit::Node(n) => {
                    let n = self.tree.node_mut(n);
                    if let Some(rgt) = n.rgt() {
                        self.stack.push(Visit::Node(rgt));
                    }
                    self.stack.push(Visit::Elem(n));
                    if let Some(lft) = n.lft() {
                        self.stack.push(Visit::Node(lft));
                    }
                }
                Visit::Elem(e) => {
                    let e = unsafe {
                        let e: &mut _ = &mut *e;
                        (&e.key, &mut e.val)
                    };
                    return Some(e);
                }
            }
        }
        None
    }
}
