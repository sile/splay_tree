// http://digital.cs.usu.edu/~allan/DS/Notes/Ch22.pdf

use std::cmp::Ordering;

type BoxNode<K, V> = Box<Node<K, V>>;
type MaybeNode<K, V> = Option<BoxNode<K, V>>;

#[derive(Debug)]
struct Node<K, V> {
    key: K,
    val: V,
    lft: MaybeNode<K, V>,
    rgt: MaybeNode<K, V>,
}
impl<K, V> Node<K, V> {
    fn new(key: K, value: V, lft: MaybeNode<K, V>, rgt: MaybeNode<K, V>) -> Box<Self> {
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
}

pub struct Tree<K, V> {
    root: MaybeNode<K, V>, // TODO: len
}
impl<K, V> Tree<K, V>
    where K: Ord
{
    pub fn new() -> Self {
        Tree { root: None }
    }
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let (new_root, old_value) = if let Some(root) = self.root.take() {
            let (mut root, order) = Tree::splay(&key, root);
            match order {
                Ordering::Equal => {
                    let old = std::mem::replace(&mut root.val, value);
                    (root, Some(old))
                }
                Ordering::Less => (Node::new(key, value, None, Some(root)), None),
                Ordering::Greater => (Node::new(key, value, Some(root), None), None),
            }
        } else {
            (Node::new(key, value, None, None), None)
        };
        self.root = Some(new_root);
        old_value
    }
    pub fn get(&mut self, key: &K) -> Option<&V> {
        self.root.take().and_then(move |root| {
            let (root, order) = Tree::splay(key, root);
            self.root = Some(root);
            if let Ordering::Equal = order {
                self.root.as_ref().map(|n| &n.val)
            } else {
                None
            }
        })
    }
    pub fn remove(&mut self, key: &K) -> Option<V> {
        self.root.take().and_then(|root| {
            let (mut root, order) = Tree::splay(key, root);
            if let Ordering::Equal = order {
                self.root = match (root.lft.take(), root.rgt.take()) {
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
                Some(root.val)
            } else {
                self.root = Some(root);
                None
            }
        })
    }
    fn splay(key: &K, mut node: BoxNode<K, V>) -> (BoxNode<K, V>, Ordering) {
        let mut lft_root = None;
        let mut rgt_root = None;
        let mut order = key.cmp(&node.key);
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
                        order = key.cmp(&child.key);
                        if let Ordering::Less = order {
                            if let Some(grand_child) = child.lft.take() {
                                // zig-zig
                                node.lft = child.rgt.take();
                                child.rgt = Some(node);
                                node = child;
                                child = grand_child;
                                order = key.cmp(&child.key);
                            }
                        }
                        let node_lft: usize = unsafe { std::mem::transmute(&mut node.lft) };
                        *rgt_lftmost = Some(node);
                        rgt_lftmost = unsafe { std::mem::transmute(node_lft) };

                        node = child;
                    }
                    Ordering::Greater => {
                        let mut child = if let Some(child) = node.rgt.take() {
                            child
                        } else {
                            break;
                        };
                        // zag
                        order = key.cmp(&child.key);
                        if let Ordering::Greater = order {
                            if let Some(grand_child) = child.rgt.take() {
                                // zag-zag
                                node.rgt = child.lft.take();
                                child.lft = Some(node);
                                node = child;
                                child = grand_child;
                                order = key.cmp(&child.key);
                            }
                        }
                        let node_rgt: usize = unsafe { std::mem::transmute(&mut node.rgt) };
                        *lft_rgtmost = Some(node);
                        lft_rgtmost = unsafe { std::mem::transmute(node_rgt) };

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
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let mut t = Tree::new();
        assert_eq!(None, t.insert(1, 1));
        assert_eq!(Some(1), t.insert(1, 2));
        assert_eq!(Some(&2), t.get(&1));
        assert_eq!(None, t.insert(2, 2));
        assert_eq!(Some(&2), t.get(&1));
        assert_eq!(Some(&2), t.get(&2));
        assert_eq!(None, t.get(&3));
        assert_eq!(Some(2), t.remove(&1));
        assert_eq!(None, t.get(&1));
    }
}
