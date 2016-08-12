use std::cmp;
use std::mem;
use std::hash;
use std::cmp::Ordering;
use std::borrow::Borrow;
use iter;

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
            if let Ordering::Greater = order {
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
            if let Ordering::Less = order {
                self.root.as_ref().map(|n| &n.key)
            } else {
                self.root.as_ref().and_then(|n| n.rgt.as_ref().map(|r| &r.lftmost().key))
            }
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
    pub fn pop_root(&mut self) -> Option<(K, V)> {
        self.root.take().map(|root| {
            let (e, root) = root.pop();
            self.root = root;
            self.len -= 1;
            e
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
    fn iter(&self) -> iter::Iter<K, V> {
        iter::Iter::new(self)
    }
}
impl<K, V> hash::Hash for Tree<K, V>
    where K: hash::Hash,
          V: hash::Hash
{
    fn hash<H>(&self, state: &mut H)
        where H: hash::Hasher
    {
        for (k, v) in self.iter() {
            k.hash(state);
            v.hash(state);
        }
    }
}
impl<K, V> PartialEq for Tree<K, V>
    where K: PartialEq,
          V: PartialEq
{
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len && self.iter().zip(other.iter()).all(|(a, b)| a.eq(&b))
    }
}
impl<K, V> Eq for Tree<K, V>
    where K: Eq,
          V: Eq
{
}
impl<K, V> PartialOrd for Tree<K, V>
    where K: PartialOrd,
          V: PartialOrd
{
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        let mut i0 = self.iter();
        let mut i1 = other.iter();
        loop {
            match (i0.next(), i1.next()) {
                (None, None) => return Some(cmp::Ordering::Equal),
                (None, _) => return Some(cmp::Ordering::Less),
                (_, None) => return Some(cmp::Ordering::Greater),
                (Some(e0), Some(e1)) => {
                    match e0.partial_cmp(&e1) {
                        Some(cmp::Ordering::Equal) => {}
                        not_equal => return not_equal,
                    }
                }
            }
        }
    }
}
impl<K, V> Ord for Tree<K, V>
    where K: Ord,
          V: Ord
{
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        let mut i0 = self.iter();
        let mut i1 = other.iter();
        loop {
            match (i0.next(), i1.next()) {
                (None, None) => return cmp::Ordering::Equal,
                (None, _) => return cmp::Ordering::Less,
                (_, None) => return cmp::Ordering::Greater,
                (Some(e0), Some(e1)) => {
                    match e0.cmp(&e1) {
                        cmp::Ordering::Equal => {}
                        not_equal => return not_equal,
                    }
                }
            }
        }
    }
}
