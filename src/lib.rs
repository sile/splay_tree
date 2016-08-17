//! Splay tree based data structures
#![warn(missing_docs)]
mod core;
mod iter;
mod vec_like;
pub mod map;
pub mod set;
pub mod heap;

#[doc(inline)]
pub use map::SplayMap;

#[doc(inline)]
pub use set::SplaySet;

#[doc(inline)]
pub use heap::SplayHeap;
