//! Splay tree based data structures
mod core;
mod iter;
pub mod map;
pub mod set;
pub mod heap;

#[doc(inline)]
pub use map::SplayMap;

#[doc(inline)]
pub use set::SplaySet;

#[doc(inline)]
pub use heap::SplayHeap;
