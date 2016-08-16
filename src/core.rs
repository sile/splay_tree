use std::u32;
use std::mem;
use std::cmp;
use std::hash;
use std::borrow::Borrow;
use std::cmp::Ordering;
use iter;

pub type NodeIndex = u32;
const NULL_NODE: NodeIndex = u32::MAX;

#[derive(Debug, Clone)]
pub struct Node<K, V> {
    pub lft: NodeIndex,
    pub rgt: NodeIndex,
    pub key: K,
    pub val: V,
}
impl<K, V> Node<K, V> {
    pub fn rgt(&self) -> Option<NodeIndex> {
        if self.rgt == NULL_NODE {
            None
        } else {
            Some(self.rgt)
        }
    }
    pub fn lft(&self) -> Option<NodeIndex> {
        if self.lft == NULL_NODE {
            None
        } else {
            Some(self.lft)
        }
    }
}
impl<K, V> Node<K, V>
    where K: Ord
{
    fn new(key: K, value: V, lft: NodeIndex, rgt: NodeIndex) -> Self {
        Node {
            key: key,
            val: value,
            lft: lft,
            rgt: rgt,
        }
    }
    fn pop(nodes: &mut Vec<Self>, root: NodeIndex) -> ((K, V), NodeIndex) {
        let children = {
            let n = &mut nodes[root as usize];
            (mem::replace(&mut n.lft, NULL_NODE), mem::replace(&mut n.rgt, NULL_NODE))
        };
        let new_root = match children {
            (NULL_NODE, NULL_NODE) => NULL_NODE,
            (lft, NULL_NODE) => lft,
            (NULL_NODE, rgt) => rgt,
            (lft, mut rgt) => {
                let lft_rgt = mem::replace(&mut nodes[lft as usize].rgt, NULL_NODE);
                if lft_rgt != NULL_NODE {
                    rgt = Node::splay_lftmost(nodes, rgt);
                    nodes[rgt as usize].lft = lft_rgt;
                }
                nodes[lft as usize].rgt = rgt;
                lft
            }
        };
        if nodes.len() as NodeIndex - 1 != root {
            let key = &nodes[nodes.len() - 1].key as *const _;
            let _ = Node::splay(nodes, new_root, unsafe { &*key });
            let last = nodes.pop().unwrap();
            let old = mem::replace(&mut nodes[root as usize], last);
            ((old.key, old.val), root)
        } else {
            (nodes.pop().map(|n| (n.key, n.val)).unwrap(), new_root)
        }
    }
    fn splay<Q: ?Sized>(nodes: &mut [Self], root: NodeIndex, key: &Q) -> (NodeIndex, Ordering)
        where K: Borrow<Q>,
              Q: Ord
    {
        Node::splay_by(nodes, root, |k| key.cmp(k.borrow()))
    }
    fn splay_lftmost(nodes: &mut [Self], root: NodeIndex) -> NodeIndex {
        Node::splay_by(nodes, root, |_| Ordering::Less).0
    }
    fn splay_by<F>(nodes: &mut [Self], root: NodeIndex, cmp: F) -> (NodeIndex, Ordering)
        where F: Fn(&K) -> Ordering
    {
        assert!(root != NULL_NODE);
        let mut node = root;
        let mut lft_root = NULL_NODE;
        let mut rgt_root = NULL_NODE;
        let mut order = cmp(nodes[node as usize].key.borrow());
        {
            let mut lft_rgtmost = &mut lft_root;
            let mut rgt_lftmost = &mut rgt_root;
            loop {
                match order {
                    Ordering::Less if nodes[node as usize].lft != NULL_NODE => {
                        // zig
                        let mut child = mem::replace(&mut nodes[node as usize].lft, NULL_NODE);

                        order = cmp(nodes[child as usize].key.borrow());
                        if let Ordering::Less = order {
                            if nodes[child as usize].lft != NULL_NODE {
                                // zig-zig
                                let grand_child = mem::replace(&mut nodes[child as usize].lft,
                                                               NULL_NODE);
                                nodes[node as usize].lft = nodes[child as usize].rgt;
                                nodes[child as usize].rgt = node;
                                node = child;
                                child = grand_child;
                                order = cmp(nodes[child as usize].key.borrow());
                            }
                        }
                        *rgt_lftmost = node;
                        rgt_lftmost = unsafe { &mut *(&mut nodes[node as usize].lft as *mut _) };

                        node = child;
                    }
                    Ordering::Greater if nodes[node as usize].rgt != NULL_NODE => {
                        // zag
                        let mut child = mem::replace(&mut nodes[node as usize].rgt, NULL_NODE);
                        order = cmp(nodes[child as usize].key.borrow());
                        if let Ordering::Greater = order {
                            if nodes[child as usize].rgt != NULL_NODE {
                                // zag-zag
                                let grand_child = mem::replace(&mut nodes[child as usize].rgt,
                                                               NULL_NODE);
                                nodes[node as usize].rgt = nodes[child as usize].lft;
                                nodes[child as usize].lft = node;
                                node = child;
                                child = grand_child;
                                order = cmp(nodes[child as usize].key.borrow());
                            }
                        }
                        *lft_rgtmost = node;
                        lft_rgtmost = unsafe { &mut *(&mut nodes[node as usize].rgt as *mut _) };

                        node = child;
                    }
                    _ => break,
                }
            }
            *lft_rgtmost = mem::replace(&mut nodes[node as usize].lft, NULL_NODE);
            *rgt_lftmost = mem::replace(&mut nodes[node as usize].rgt, NULL_NODE);
        }
        nodes[node as usize].lft = lft_root;
        nodes[node as usize].rgt = rgt_root;

        (node, order)
    }
}

#[derive(Debug, Clone)]
pub struct Tree<K, V> {
    root: NodeIndex,
    nodes: Vec<Node<K, V>>,
}
impl<K, V> Tree<K, V>
    where K: Ord
{
    pub fn new() -> Self {
        Tree {
            root: 0,
            nodes: Vec::new(),
        }
    }
    pub fn contains_key<Q: ?Sized>(&mut self, key: &Q) -> bool
        where K: Borrow<Q>,
              Q: Ord
    {
        if self.nodes.is_empty() {
            false
        } else {
            let (root, order) = Node::splay(&mut self.nodes, self.root, key);
            self.root = root;
            order == Ordering::Equal
        }
    }
    pub fn find_lower_bound<Q: ?Sized>(&mut self, key: &Q) -> Option<&K>
        where K: Borrow<Q>,
              Q: Ord
    {
        if self.nodes.is_empty() {
            None
        } else {
            let (root, order) = Node::splay(&mut self.nodes, self.root, key);
            self.root = root;
            if let Ordering::Greater = order {
                let mut root_rgt = self.nodes[self.root as usize].rgt;
                if root_rgt != NULL_NODE {
                    root_rgt = Node::splay_lftmost(&mut self.nodes, root_rgt);
                    self.nodes[self.root as usize].rgt = root_rgt;
                    Some(&self.nodes[root_rgt as usize].key)
                } else {
                    None
                }
            } else {
                Some(&self.nodes[self.root as usize].key)
            }
        }
    }
    pub fn find_upper_bound<Q: ?Sized>(&mut self, key: &Q) -> Option<&K>
        where K: Borrow<Q>,
              Q: Ord
    {
        if self.nodes.is_empty() {
            None
        } else {
            let (root, order) = Node::splay(&mut self.nodes, self.root, key);
            self.root = root;
            if let Ordering::Less = order {
                Some(&self.nodes[self.root as usize].key)
            } else {
                let mut root_rgt = self.nodes[self.root as usize].rgt;
                if root_rgt != NULL_NODE {
                    root_rgt = Node::splay_lftmost(&mut self.nodes, root_rgt);
                    self.nodes[self.root as usize].rgt = root_rgt;
                    Some(&self.nodes[root_rgt as usize].key)
                } else {
                    None
                }
            }
        }
    }
    pub fn get<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
        where K: Borrow<Q>,
              Q: Ord
    {
        if self.contains_key(key) {
            Some(&mut self.nodes[self.root as usize].val)
        } else {
            None
        }
    }
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let (new_root, old_value) = if self.nodes.is_empty() {
            self.nodes.push(Node::new(key, value, NULL_NODE, NULL_NODE));
            (0, None)
        } else {
            let (root, order) = Node::splay(&mut self.nodes, self.root, &key);
            match order {
                Ordering::Equal => {
                    let old = mem::replace(&mut self.nodes[root as usize].val, value);
                    (root, Some(old))
                }
                Ordering::Less => {
                    let lft = mem::replace(&mut self.nodes[root as usize].lft, NULL_NODE);
                    self.nodes.push(Node::new(key, value, lft, root));
                    (self.nodes.len() as NodeIndex - 1, None)
                }
                Ordering::Greater => {
                    let rgt = mem::replace(&mut self.nodes[root as usize].rgt, NULL_NODE);
                    self.nodes.push(Node::new(key, value, root, rgt));
                    (self.nodes.len() as NodeIndex - 1, None)
                }
            }

        };
        assert!(new_root != NULL_NODE);

        self.root = new_root;
        old_value
    }
    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
        where K: Borrow<Q>,
              Q: Ord
    {
        if self.contains_key(key) {
            self.pop_root().map(|(_, v)| v)
        } else {
            None
        }
    }
    pub fn pop_last(&mut self) -> Option<(K, V)> {
        if self.nodes.is_empty() {
            None
        } else {
            let key = &self.nodes.last().unwrap().key as *const _;
            self.contains_key(unsafe { &*key });
            self.pop_root()
        }
    }
    pub fn pop_root(&mut self) -> Option<(K, V)> {
        if self.nodes.is_empty() {
            None
        } else {
            let (e, root) = Node::pop(&mut self.nodes, self.root);
            self.root = root;
            Some(e)
        }
    }
    pub fn get_lftmost(&mut self) -> Option<(&K, &V)> {
        if self.nodes.is_empty() {
            None
        } else {
            self.root = Node::splay_lftmost(&mut self.nodes, self.root);
            let n = &self.nodes[self.root as usize];
            Some((&n.key, &n.val))
        }
    }
    pub fn take_lftmost(&mut self) -> Option<(K, V)> {
        if self.nodes.is_empty() {
            None
        } else {
            self.root = Node::splay_lftmost(&mut self.nodes, self.root);
            self.pop_root()
        }
    }
}
impl<K, V> Tree<K, V> {
    pub fn iter(&self) -> iter::Iter<K, V> {
        iter::Iter::new(self)
    }
    pub fn root(&self) -> Option<NodeIndex> {
        if self.nodes.is_empty() {
            None
        } else {
            Some(self.root)
        }
    }
    pub fn node_ref(&self, i: NodeIndex) -> &Node<K, V> {
        &self.nodes[i as usize]
    }
    pub fn node_mut(&mut self, i: NodeIndex) -> &mut Node<K, V> {
        &mut self.nodes[i as usize]
    }
    pub fn root_ref(&self) -> Option<&Node<K, V>> {
        if self.nodes.is_empty() {
            None
        } else {
            Some(&self.nodes[self.root as usize])
        }
    }
    pub fn root_mut(&mut self) -> Option<&mut Node<K, V>> {
        if self.nodes.is_empty() {
            None
        } else {
            Some(&mut self.nodes[self.root as usize])
        }
    }
    pub fn len(&self) -> usize {
        self.nodes.len()
    }
    pub fn capacity(&self) -> usize {
        self.nodes.capacity()
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
        self.len() == other.len() && self.iter().zip(other.iter()).all(|(a, b)| a.eq(&b))
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
