use std::mem;
use std::cmp::Ordering;
use std::borrow::Borrow;

pub type BoxNode<K, V> = Box<Node<K, V>>;
pub type MaybeNode<K, V> = Option<BoxNode<K, V>>;

#[derive(Debug, Clone)]
pub struct Node<K, V> {
    pub key: K,
    pub val: V,
    pub lft: MaybeNode<K, V>,
    pub rgt: MaybeNode<K, V>,
}
impl<K, V> Node<K, V> {
    pub fn new(key: K, value: V, lft: MaybeNode<K, V>, rgt: MaybeNode<K, V>) -> Box<Self> {
        Box::new(Node {
            key: key,
            val: value,
            lft: lft,
            rgt: rgt,
        })
    }
    fn lftmost_mut(&mut self) -> &mut Node<K, V> {
        let mut next = self;
        loop {
            let curr = next;
            match curr.lft {
                None => return curr,
                Some(ref mut lft) => next = lft,
            }
        }
    }
    // TODO: splay?
    fn lftmost(&self) -> &Node<K, V> {
        let mut next = self;
        loop {
            let curr = next;
            match curr.lft {
                None => return curr,
                Some(ref lft) => next = lft,
            }
        }
    }
    fn pop(mut self) -> ((K, V), MaybeNode<K, V>) {
        let root = match (self.lft.take(), self.rgt.take()) {
            (None, None) => None,
            (Some(lft), None) => Some(lft),
            (None, Some(rgt)) => Some(rgt),
            (Some(mut lft), Some(mut rgt)) => {
                if let Some(lft_rgt) = lft.rgt.take() {
                    rgt.lftmost_mut().lft = Some(lft_rgt);
                }
                lft.rgt = Some(rgt);
                Some(lft)
            }
        };
        ((self.key, self.val), root)
    }
}

#[derive(Debug, Clone)]
pub struct Tree<K, V> {
    pub root: MaybeNode<K, V>,
    pub len: usize,
}
impl<K, V> Tree<K, V>
    where K: Ord
{
    pub fn new() -> Self {
        Tree {
            root: None,
            len: 0,
        }
    }
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let (new_root, old_value) = if let Some(root) = self.root.take() {
            let (mut root, order) = Tree::splay(&key, root);
            match order {
                Ordering::Equal => {
                    let old = mem::replace(&mut root.val, value);
                    (root, Some(old))
                }
                Ordering::Less => {
                    let lft = root.lft.take();
                    (Node::new(key, value, lft, Some(root)), None)
                }
                Ordering::Greater => {
                    let rgt = root.rgt.take();
                    (Node::new(key, value, Some(root), rgt), None)
                }
            }
        } else {
            (Node::new(key, value, None, None), None)
        };
        self.root = Some(new_root);
        if old_value.is_none() {
            self.len += 1;
        }
        old_value
    }
    pub fn find_lower_bound<Q: ?Sized>(&mut self, key: &Q) -> Option<&K>
        where K: Borrow<Q>,
              Q: Ord
    {
        self.root.take().and_then(move |root| {
            let (root, order) = Tree::splay(key, root);
            self.root = Some(root);
            if let Ordering::Less = order {
                self.root.as_ref().and_then(|n| n.rgt.as_ref().map(|r| &r.lftmost().key))
            } else {
                self.root.as_ref().map(|n| &n.key)
            }
        })
    }
    pub fn find_upper_bound<Q: ?Sized>(&mut self, key: &Q) -> Option<&K>
        where K: Borrow<Q>,
              Q: Ord
    {
        self.root.take().and_then(move |root| {
            let (root, order) = Tree::splay(key, root);
            self.root = Some(root);
            if let Ordering::Greater = order {
                self.root.as_ref().map(|n| &n.key)
            } else {
                self.root.as_ref().and_then(|n| n.rgt.as_ref().map(|r| &r.lftmost().key))
            }
        })
    }
    pub fn get_rgtmost(&mut self) -> Option<(&K, &V)> {
        self.root.take().and_then(move |root| {
            let (root, _) = Tree::splay_by(root, |_| Ordering::Greater);
            self.root = Some(root);
            self.root.as_ref().map(|n| (&n.key, &n.val))
        })
    }
    pub fn take_rgtmost(&mut self) -> Option<(K, V)> {
        self.root.take().and_then(move |root| {
            let (root, _) = Tree::splay_by(root, |_| Ordering::Greater);
            let (e, root) = root.pop();
            self.root = root;
            self.len -= 1;
            Some(e)
        })
    }
    pub fn get_lftmost(&mut self) -> Option<(&K, &V)> {
        self.root.take().and_then(move |root| {
            let (root, _) = Tree::splay_by(root, |_| Ordering::Less);
            self.root = Some(root);
            self.root.as_ref().map(|n| (&n.key, &n.val))
        })
    }
    pub fn take_lftmost(&mut self) -> Option<(K, V)> {
        self.root.take().and_then(move |root| {
            let (root, _) = Tree::splay_by(root, |_| Ordering::Less);
            let (e, root) = root.pop();
            self.root = root;
            self.len -= 1;
            Some(e)
        })
    }
    pub fn get<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
        where K: Borrow<Q>,
              Q: Ord
    {
        self.root.take().and_then(move |root| {
            let (root, order) = Tree::splay(key, root);
            self.root = Some(root);
            if let Ordering::Equal = order {
                self.root.as_mut().map(|n| &mut n.val)
            } else {
                None
            }
        })
    }
    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
        where K: Borrow<Q>,
              Q: Ord
    {
        self.root.take().and_then(|root| {
            let (root, order) = Tree::splay(key, root);
            if let Ordering::Equal = order {
                let ((_, v), root) = root.pop();
                self.root = root;
                self.len -= 1;
                Some(v)
            } else {
                self.root = Some(root);
                None
            }
        })
    }
    fn splay_by<F>(mut node: BoxNode<K, V>, cmp: F) -> (BoxNode<K, V>, Ordering)
        where F: Fn(&K) -> Ordering
    {
        let mut lft_root = None;
        let mut rgt_root = None;
        let mut order = cmp(node.key.borrow());
        {
            let mut lft_rgtmost = &mut lft_root;
            let mut rgt_lftmost = &mut rgt_root;
            loop {
                match order {
                    Ordering::Equal => break,
                    Ordering::Less => {
                        let mut child = if let Some(child) = node.lft.take() {
                            child
                        } else {
                            break;
                        };
                        // zig
                        order = cmp(child.key.borrow());
                        if let Ordering::Less = order {
                            if let Some(grand_child) = child.lft.take() {
                                // zig-zig
                                node.lft = child.rgt.take();
                                child.rgt = Some(node);
                                node = child;
                                child = grand_child;
                                order = cmp(child.key.borrow());
                            }
                        }
                        let node_lft: usize = unsafe { mem::transmute(&mut node.lft) };
                        *rgt_lftmost = Some(node);
                        rgt_lftmost = unsafe { mem::transmute(node_lft) };

                        node = child;
                    }
                    Ordering::Greater => {
                        let mut child = if let Some(child) = node.rgt.take() {
                            child
                        } else {
                            break;
                        };
                        // zag
                        order = cmp(child.key.borrow());
                        if let Ordering::Greater = order {
                            if let Some(grand_child) = child.rgt.take() {
                                // zag-zag
                                node.rgt = child.lft.take();
                                child.lft = Some(node);
                                node = child;
                                child = grand_child;
                                order = cmp(child.key.borrow());
                            }
                        }
                        let node_rgt: usize = unsafe { mem::transmute(&mut node.rgt) };
                        *lft_rgtmost = Some(node);
                        lft_rgtmost = unsafe { mem::transmute(node_rgt) };

                        node = child;
                    }
                }
            }
            *lft_rgtmost = node.lft.take();
            *rgt_lftmost = node.rgt.take();
        }
        node.lft = lft_root;
        node.rgt = rgt_root;
        (node, order)
    }
    fn splay<Q: ?Sized>(key: &Q, node: BoxNode<K, V>) -> (BoxNode<K, V>, Ordering)
        where K: Borrow<Q>,
              Q: Ord
    {
        Tree::splay_by(node, |k| key.cmp(k.borrow()))
    }
}
impl<K, V> Tree<K, V> {
    pub fn iter(&self) -> Iter<K, V> {
        Iter::new(self)
    }
    // pub fn keys(&self) -> Keys<K, V> {
    //     Keys::new(self)
    // }
}

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


// pub struct RevIter<'a, K: 'a, V: 'a> {
//     stack: Vec<Item<&'a Node<K, V>>>,
// }
// impl<'a, K: 'a, V: 'a> RevIter<'a, K, V> {
//     pub fn new(tree: &'a Tree<K, V>) -> Self {
//         if let Some(root) = tree.root.as_ref() {
//             RevIter { stack: vec![Item::Right(root)] }
//         } else {
//             RevIter { stack: vec![] }
//         }
//     }
// }
// impl<'a, K: 'a, V: 'a> Iterator for RevIter<'a, K, V> {
//     type Item = (&'a K, &'a V);
//     fn next(&mut self) -> Option<Self::Item> {
//         while let Some(e) = self.stack.pop() {
//             match e {
//                 Item::Right(e) => {
//                     self.stack.push(Item::Left(e));
//                     if let Some(child) = e.rgt.as_ref() {
//                         self.stack.push(Item::Right(child));
//                     }
//                 }
//                 Item::Left(e) => {
//                     if let Some(child) = e.lft.as_ref() {
//                         self.stack.push(Item::Right(child));
//                     }
//                     return Some((&e.key, &e.val));
//                 }
//             }
//         }
//         None
//     }
// }

// pub struct Keys<'a, K: 'a, V: 'a> {
//     iter: Iter<'a, K, V>,
// }
// impl<'a, K: 'a, V: 'a> Keys<'a, K, V> {
//     fn new(tree: &'a Tree<K, V>) -> Self {
//         Keys { iter: Iter::new(tree) }
//     }
// }
// impl<'a, K: 'a, V: 'a> Iterator for Keys<'a, K, V> {
//     type Item = &'a K;
//     fn next(&mut self) -> Option<Self::Item> {
//         self.iter.next().map(|e| e.0)
//     }
// }
