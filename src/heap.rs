use core;

#[derive(Debug,Clone)]
pub struct SplayHeap<T> {
    tree: core::Tree<T, ()>,
}
impl<T> SplayHeap<T>
    where T: Ord
{
    pub fn new() -> Self {
        SplayHeap { tree: core::Tree::new() }
    }
    pub fn peek(&mut self) -> Option<&T> {
        self.tree.get_rgtmost().map(|e| e.0)
    }
    pub fn pop(&mut self) -> Option<T> {
        self.tree.take_rgtmost().map(|e| e.0)
    }
    pub fn push(&mut self, item: T) {
        self.tree.insert(item, ());
    }
    pub fn len(&self) -> usize {
        self.tree.len
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub fn clear(&mut self) {
        self.tree = core::Tree::new();
    }
    // TODO: other functions
}
impl<T> Default for SplayHeap<T>
    where T: Ord
{
    fn default() -> Self {
        SplayHeap::new()
    }
}
