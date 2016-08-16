//! Splay tree based data structures

// TODO: #![warn(missing_docs)]
mod core;
mod iter;
pub mod map;
pub mod set;
pub mod heap;
pub mod vec_set;

#[doc(inline)]
pub use map::SplayMap;

#[doc(inline)]
pub use set::SplaySet;

#[doc(inline)]
pub use heap::SplayHeap;

#[doc(inline)]
pub use vec_set::SplayVecSet;
