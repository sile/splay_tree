//! In-place top-down splay tree implementation
use crate::iter;
use std::borrow::Borrow;
use std::cmp;
use std::cmp::Ordering;
use std::hash;
use std::mem;
use std::slice;
use std::u32;
use std::vec::Vec;

pub type NodeIndex = u32;
const NULL_NODE: NodeIndex = u32::MAX;

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Node<K, V> {
    lft: NodeIndex,
    rgt: NodeIndex,
    pub key: K,
    pub val: V,
}
impl<K, V> Node<K, V> {
    pub fn new(key: K, val: V, lft: NodeIndex, rgt: NodeIndex) -> Self {
        Node { key, val, lft, rgt }
    }
    pub fn rgt(&self) -> Option<NodeIndex> {
        if self.rgt != NULL_NODE {
            Some(self.rgt)
        } else {
            None
        }
    }
    pub fn lft(&self) -> Option<NodeIndex> {
        if self.lft != NULL_NODE {
            Some(self.lft)
        } else {
            None
        }
    }
}
impl<K, V> From<Node<K, V>> for (K, V) {
    fn from(t: Node<K, V>) -> Self {
        (t.key, t.val)
    }
}
impl<'a, K, V> From<&'a Node<K, V>> for (&'a K, &'a V) {
    fn from(t: &'a Node<K, V>) -> Self {
        (&t.key, &t.val)
    }
}
impl<'a, K, V> From<&'a mut Node<K, V>> for (&'a K, &'a mut V) {
    fn from(t: &'a mut Node<K, V>) -> Self {
        (&t.key, &mut t.val)
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Tree<K, V> {
    root: NodeIndex,
    nodes: Vec<Node<K, V>>,
}
impl<K, V> Tree<K, V>
where
    K: Ord,
{
    pub fn new() -> Self {
        Tree {
            root: 0,
            nodes: Vec::new(),
        }
    }
    pub fn contains_key<Q: ?Sized>(&mut self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.root().map_or(false, |root| {
            let (root, order) = self.splay(root, key);
            self.root = root;
            order == Ordering::Equal
        })
    }
    pub fn contains_key_immut<Q: ?Sized>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.get_immut(key).is_some()
    }
    pub fn find_lower_bound<Q: ?Sized>(&mut self, key: &Q) -> Option<&K>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.find_bound(|k| key.cmp(k.borrow()))
    }
    pub fn find_lower_bound_immut<Q: ?Sized>(&self, key: &Q) -> Option<&K>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.find_bound_immut(|k| key.cmp(k.borrow()))
    }
    pub fn find_upper_bound<Q: ?Sized>(&mut self, key: &Q) -> Option<&K>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.find_bound(|k| match key.cmp(k.borrow()) {
            Ordering::Equal => Ordering::Greater,
            other => other,
        })
    }
    pub fn find_upper_bound_immut<Q: ?Sized>(&self, key: &Q) -> Option<&K>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.find_bound_immut(|k| match key.cmp(k.borrow()) {
            Ordering::Equal => Ordering::Greater,
            other => other,
        })
    }
    pub fn get<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        if self.contains_key(key) {
            Some(&mut self.root_mut().val)
        } else {
            None
        }
    }
    pub fn get_immut<Q: ?Sized>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        let mut index = self.root();
        while let Some(node) = index.map(|i| self.node_ref(i)) {
            match key.cmp(node.key.borrow()) {
                Ordering::Equal => return Some((&node.key, &node.val)),
                Ordering::Less => index = node.lft(),
                Ordering::Greater => index = node.rgt(),
            }
        }
        None
    }
    pub fn find_bound_immut<F>(&self, cmp: F) -> Option<&K>
    where
        F: Fn(&K) -> Ordering,
    {
        let mut index = self.root();
        let mut candidate = None;
        while let Some(node) = index.map(|i| self.node_ref(i)) {
            match cmp(&node.key) {
                Ordering::Equal => return Some(&node.key),
                Ordering::Less => {
                    candidate = Some(&node.key);
                    index = node.lft();
                }
                Ordering::Greater => index = node.rgt(),
            }
        }
        candidate
    }
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        if let Some(root) = self.root() {
            let (root, order) = self.splay(root, &key);
            self.root = root;
            match order {
                Ordering::Equal => {
                    let old = mem::replace(&mut self.root_mut().val, value);
                    Some(old)
                }
                Ordering::Less => {
                    let lft = mem::replace(&mut self.root_mut().lft, NULL_NODE);
                    let rgt = self.root;
                    self.push_root(Node::new(key, value, lft, rgt));
                    None
                }
                Ordering::Greater => {
                    let rgt = mem::replace(&mut self.root_mut().rgt, NULL_NODE);
                    let lft = self.root;
                    self.push_root(Node::new(key, value, lft, rgt));
                    None
                }
            }
        } else {
            self.push_root(Node::new(key, value, NULL_NODE, NULL_NODE));
            None
        }
    }
    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        if self.contains_key(key) {
            Some(self.non_empty_pop_root().1)
        } else {
            None
        }
    }
    pub fn pop_last(&mut self) -> Option<(K, V)> {
        self.nodes
            .last()
            .map(|n| unsafe { &*(&n.key as *const _) })
            .map(|key| {
                self.contains_key(key);
                self.non_empty_pop_root()
            })
    }
    pub fn pop_root(&mut self) -> Option<(K, V)> {
        self.root().map(|_| self.non_empty_pop_root())
    }
    pub fn get_lftmost(&mut self) -> Option<(&K, &V)> {
        self.root().map(move |root| {
            self.root = self.splay_lftmost(root);
            self.root_ref().into()
        })
    }
    pub fn get_lftmost_immut(&self) -> Option<(&K, &V)> {
        self.root().map(|i| self.node_ref(i)).map(|mut node| {
            while let Some(next) = node.lft().map(|i| self.node_ref(i)) {
                node = next;
            }
            (&node.key, &node.val)
        })
    }
    pub fn take_lftmost(&mut self) -> Option<(K, V)> {
        self.root().map(|root| {
            self.root = self.splay_lftmost(root);
            self.non_empty_pop_root()
        })
    }
    pub fn get_rgtmost(&mut self) -> Option<(&K, &V)> {
        self.root().map(move |root| {
            self.root = self.splay_rgtmost(root);
            self.root_ref().into()
        })
    }
    pub fn get_rgtmost_immut(&self) -> Option<(&K, &V)> {
        self.root().map(|i| self.node_ref(i)).map(|mut node| {
            while let Some(next) = node.rgt().map(|i| self.node_ref(i)) {
                node = next;
            }
            (&node.key, &node.val)
        })
    }
    pub fn take_rgtmost(&mut self) -> Option<(K, V)> {
        self.root().map(|root| {
            self.root = self.splay_rgtmost(root);
            self.non_empty_pop_root()
        })
    }
    fn push_root(&mut self, node: Node<K, V>) {
        self.nodes.push(node);
        self.root = self.nodes.len() as NodeIndex - 1;
        assert!(self.root != NULL_NODE);
    }
    fn splay<Q: ?Sized>(&mut self, root: NodeIndex, key: &Q) -> (NodeIndex, Ordering)
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        self.splay_by(root, |k| key.cmp(k.borrow()))
    }
    fn splay_lftmost(&mut self, root: NodeIndex) -> NodeIndex {
        self.splay_by(root, |_| Ordering::Less).0
    }
    fn splay_rgtmost(&mut self, root: NodeIndex) -> NodeIndex {
        self.splay_by(root, |_| Ordering::Greater).0
    }
    fn splay_by<F>(&mut self, mut curr_idx: NodeIndex, cmp: F) -> (NodeIndex, Ordering)
    where
        F: Fn(&K) -> Ordering,
    {
        use std::mem::replace;
        let mut lft_root_idx = NULL_NODE;
        let mut rgt_root_idx = NULL_NODE;
        let mut curr_mut = unsafe { self.aliasable_node_mut(curr_idx) };
        let mut order = cmp(curr_mut.key.borrow());
        {
            let mut lft_rgtmost_idx = &mut lft_root_idx;
            let mut rgt_lftmost_idx = &mut rgt_root_idx;
            loop {
                let mut child_idx;
                let mut child_mut;
                match order {
                    Ordering::Less if curr_mut.lft != NULL_NODE => {
                        // zig
                        child_idx = replace(&mut curr_mut.lft, NULL_NODE);
                        child_mut = unsafe { self.aliasable_node_mut(child_idx) };
                        order = cmp(child_mut.key.borrow());
                        if Ordering::Less == order && child_mut.lft != NULL_NODE {
                            // zig-zig
                            let grand_child_idx = replace(&mut child_mut.lft, NULL_NODE);
                            curr_mut.lft = replace(&mut child_mut.rgt, curr_idx);
                            curr_idx = replace(&mut child_idx, grand_child_idx);
                            curr_mut = replace(&mut child_mut, unsafe {
                                self.aliasable_node_mut(grand_child_idx)
                            });
                            order = cmp(child_mut.key.borrow());
                        }
                        *rgt_lftmost_idx = curr_idx;
                        rgt_lftmost_idx = unsafe { &mut *(&mut curr_mut.lft as *mut _) };
                    }
                    Ordering::Greater if curr_mut.rgt != NULL_NODE => {
                        // zag
                        child_idx = replace(&mut curr_mut.rgt, NULL_NODE);
                        child_mut = unsafe { self.aliasable_node_mut(child_idx) };
                        order = cmp(child_mut.key.borrow());
                        if Ordering::Greater == order && child_mut.rgt != NULL_NODE {
                            // zag-zag
                            let grand_child_idx = replace(&mut child_mut.rgt, NULL_NODE);
                            curr_mut.rgt = replace(&mut child_mut.lft, curr_idx);
                            curr_idx = replace(&mut child_idx, grand_child_idx);
                            curr_mut = replace(&mut child_mut, unsafe {
                                self.aliasable_node_mut(grand_child_idx)
                            });
                            order = cmp(child_mut.key.borrow());
                        }
                        *lft_rgtmost_idx = curr_idx;
                        lft_rgtmost_idx = unsafe { &mut *(&mut curr_mut.rgt as *mut _) };
                    }
                    _ => break,
                }
                curr_mut = child_mut;
                curr_idx = child_idx;
            }
            *lft_rgtmost_idx = replace(&mut curr_mut.lft, NULL_NODE);
            *rgt_lftmost_idx = replace(&mut curr_mut.rgt, NULL_NODE);
        }
        curr_mut.lft = lft_root_idx;
        curr_mut.rgt = rgt_root_idx;
        (curr_idx, order)
    }
    fn non_empty_pop_root(&mut self) -> (K, V) {
        let new_root = match *self.root_ref() {
            Node {
                lft: NULL_NODE,
                rgt: NULL_NODE,
                ..
            } => NULL_NODE,
            Node {
                lft,
                rgt: NULL_NODE,
                ..
            } => lft,
            Node {
                lft: NULL_NODE,
                rgt,
                ..
            } => rgt,
            Node { lft, rgt, .. } if self.node_ref(rgt).lft == NULL_NODE => {
                self.node_mut(rgt).lft = lft;
                rgt
            }
            Node { lft, mut rgt, .. } => {
                let lft_rgt = mem::replace(&mut self.node_mut(lft).rgt, NULL_NODE);
                if lft_rgt != NULL_NODE {
                    rgt = self.splay_lftmost(rgt);
                    self.node_mut(rgt).lft = lft_rgt;
                }
                self.node_mut(lft).rgt = rgt;
                lft
            }
        };
        if self.len() as NodeIndex - 1 != self.root {
            let key = &self.node_ref(self.len() as NodeIndex - 1).key as *const _;
            let _ = self.splay(new_root, unsafe { &*key });
            let last = self.nodes.pop().unwrap();
            mem::replace(self.root_mut(), last).into()
        } else {
            self.root = new_root;
            self.nodes.pop().unwrap().into()
        }
    }
    fn find_bound<F>(&mut self, cmp: F) -> Option<&K>
    where
        F: Fn(&K) -> Ordering,
    {
        self.root().and_then(move |root| {
            let (root, order) = self.splay_by(root, cmp);
            self.root = root;
            if let Ordering::Greater = order {
                let mut root_rgt = self.root_ref().rgt;
                if root_rgt != NULL_NODE {
                    root_rgt = self.splay_lftmost(root_rgt);
                    self.root_mut().rgt = root_rgt;
                    Some(&self.node_ref(root_rgt).key)
                } else {
                    None
                }
            } else {
                Some(&self.root_ref().key)
            }
        })
    }
}
impl<K, V> Tree<K, V> {
    pub fn root(&self) -> Option<NodeIndex> {
        if self.nodes.is_empty() {
            None
        } else {
            Some(self.root)
        }
    }
    pub fn root_ref(&self) -> &Node<K, V> {
        let root = self.root;
        self.node_ref(root)
    }
    pub fn root_mut(&mut self) -> &mut Node<K, V> {
        let root = self.root;
        self.node_mut(root)
    }
    pub fn node_ref(&self, i: NodeIndex) -> &Node<K, V> {
        unsafe { self.nodes.get_unchecked(i as usize) }
    }
    pub fn node_mut(&mut self, i: NodeIndex) -> &mut Node<K, V> {
        unsafe { self.nodes.get_unchecked_mut(i as usize) }
    }
    unsafe fn aliasable_node_mut<'a>(&mut self, i: NodeIndex) -> &'a mut Node<K, V> {
        &mut *(self.node_mut(i) as *mut _)
    }
    pub fn len(&self) -> usize {
        self.nodes.len()
    }
    #[allow(dead_code)]
    pub fn capacity(&self) -> usize {
        self.nodes.capacity()
    }
    pub fn iter(&self) -> iter::Iter<K, V> {
        iter::InOrderIter::new(self.root(), &self.nodes)
    }
    pub fn iter_mut(&mut self) -> iter::IterMut<K, V> {
        iter::InOrderIter::new(self.root(), &mut self.nodes)
    }
    pub fn into_iter(self) -> iter::IntoIter<K, V> {
        iter::InOrderIter::new(
            self.root(),
            iter::OwnedNodes(self.nodes.into_iter().map(Some).collect()),
        )
    }
    pub fn nodes_iter(&self) -> slice::Iter<Node<K, V>> {
        self.nodes.iter()
    }
    pub fn nodes_iter_mut(&mut self) -> slice::IterMut<Node<K, V>> {
        self.nodes.iter_mut()
    }
}
impl<K, V> hash::Hash for Tree<K, V>
where
    K: hash::Hash,
    V: hash::Hash,
{
    fn hash<H>(&self, state: &mut H)
    where
        H: hash::Hasher,
    {
        for e in self.iter() {
            e.hash(state);
        }
    }
}
impl<K, V> PartialEq for Tree<K, V>
where
    K: PartialEq,
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().zip(other.iter()).all(|(a, b)| a.eq(&b))
    }
}
impl<K, V> Eq for Tree<K, V>
where
    K: Eq,
    V: Eq,
{
}
impl<K, V> PartialOrd for Tree<K, V>
where
    K: PartialOrd,
    V: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        let mut i0 = self.iter();
        let mut i1 = other.iter();
        loop {
            match (i0.next(), i1.next()) {
                (None, None) => return Some(cmp::Ordering::Equal),
                (None, _) => return Some(cmp::Ordering::Less),
                (_, None) => return Some(cmp::Ordering::Greater),
                (Some(e0), Some(e1)) => match e0.partial_cmp(&e1) {
                    Some(cmp::Ordering::Equal) => {}
                    not_equal => return not_equal,
                },
            }
        }
    }
}
impl<K, V> Ord for Tree<K, V>
where
    K: Ord,
    V: Ord,
{
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        let mut i0 = self.iter();
        let mut i1 = other.iter();
        loop {
            match (i0.next(), i1.next()) {
                (None, None) => return cmp::Ordering::Equal,
                (None, _) => return cmp::Ordering::Less,
                (_, None) => return cmp::Ordering::Greater,
                (Some(e0), Some(e1)) => match e0.cmp(&e1) {
                    cmp::Ordering::Equal => {}
                    not_equal => return not_equal,
                },
            }
        }
    }
}
