//! Splay tree based data structures
mod core;
mod iter;
pub mod map;
pub mod set;
pub mod heap;

pub use map::SplayMap;
pub use set::SplaySet;
pub use heap::SplayHeap;
