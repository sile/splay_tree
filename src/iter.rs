use core::Node;
use core::Tree;

// XXX: name
enum Item<T> {
    Left(T),
    Right(T),
}
pub struct Iter<'a, K: 'a, V: 'a> {
    stack: Vec<Item<&'a Node<K, V>>>,
}
impl<'a, K: 'a, V: 'a> Iter<'a, K, V> {
    pub fn new(tree: &'a Tree<K, V>) -> Self {
        if let Some(root) = tree.root.as_ref() {
            Iter { stack: vec![Item::Left(root)] }
        } else {
            Iter { stack: vec![] }
        }
    }
}
impl<'a, K: 'a, V: 'a> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(e) = self.stack.pop() {
            match e {
                Item::Left(e) => {
                    self.stack.push(Item::Right(e));
                    if let Some(child) = e.lft.as_ref() {
                        self.stack.push(Item::Left(child));
                    }
                }
                Item::Right(e) => {
                    if let Some(child) = e.rgt.as_ref() {
                        self.stack.push(Item::Left(child));
                    }
                    return Some((&e.key, &e.val));
                }
            }
        }
        None
    }
}

pub struct IntoIter<K, V> {
    stack: Vec<Item<Node<K, V>>>,
}
impl<K, V> IntoIter<K, V> {
    pub fn new(mut tree: Tree<K, V>) -> Self {
        if let Some(root) = tree.root.take() {
            IntoIter { stack: vec![Item::Left(*root)] }
        } else {
            IntoIter { stack: vec![] }
        }
    }
}
impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(e) = self.stack.pop() {
            match e {
                Item::Left(mut e) => {
                    let lft = e.lft.take();
                    self.stack.push(Item::Right(e));
                    if let Some(child) = lft {
                        self.stack.push(Item::Left(*child));
                    }
                }
                Item::Right(mut e) => {
                    if let Some(child) = e.rgt.take() {
                        self.stack.push(Item::Left(*child));
                    }
                    return Some((e.key, e.val));
                }
            }
        }
        None
    }
}

enum Item2<K, V, T> {
    Left(T),
    Right((K, V), Option<T>),
}

pub struct IterMut<'a, K: 'a, V: 'a> {
    stack: Vec<Item2<&'a K, &'a mut V, &'a mut Node<K, V>>>,
}
impl<'a, K: 'a, V: 'a> IterMut<'a, K, V> {
    pub fn new(tree: &'a mut Tree<K, V>) -> Self {
        if let Some(root) = tree.root.as_mut() {
            IterMut { stack: vec![Item2::Left(root)] }
        } else {
            IterMut { stack: vec![] }
        }
    }
}
impl<'a, K: 'a, V: 'a> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(e) = self.stack.pop() {
            match e {
                Item2::Left(e) => {
                    use std::borrow::BorrowMut;
                    self.stack
                        .push(Item2::Right((&e.key, &mut e.val),
                                           e.rgt.as_mut().map(|r| r.borrow_mut())));
                    if let Some(child) = e.lft.as_mut() {
                        self.stack.push(Item2::Left(child));
                    }
                }
                Item2::Right(e, rgt) => {
                    if let Some(child) = rgt {
                        self.stack.push(Item2::Left(child));
                    }
                    return Some(e);
                }
            }
        }
        None
    }
}
