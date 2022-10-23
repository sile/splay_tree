splay_tree
==========

[![](https://img.shields.io/crates/v/splay_tree.svg)](https://crates.io/crates/splay_tree)
[![Documentation](https://docs.rs/splay_tree/badge.svg)](https://docs.rs/splay_tree)
[![Build Status](https://travis-ci.org/sile/splay_tree.svg?branch=master)](https://travis-ci.org/sile/splay_tree)
[![Code Coverage](https://codecov.io/gh/sile/splay_tree/branch/master/graph/badge.svg)](https://codecov.io/gh/sile/splay_tree/branch/master)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)

`splay_tree` provides data structures such as map, set and heap which are based on an in-place top-down splay tree.

> A splay tree is a self-adjusting binary search tree with
> the additional property that recently accessed elements are quick to access again.
> It performs basic operations such as insertion, look-up and removal in O(log n) amortized time. - [Splay tree (Wikipedia)](https://en.wikipedia.org/wiki/Splay_tree)

Documentation
-------------

See [RustDoc Documentation](https://docs.rs/splay_tree/).

The documentation includes some examples.


Installation
------------

Add following lines to your `Cargo.toml`:

```toml
[dependencies]
splay_tree = "0.2"
```


Reference
---------

- https://en.wikipedia.org/wiki/Splay_tree
- http://digital.cs.usu.edu/~allan/DS/Notes/Ch22.pdf


License
-------

This library is released under the MIT License.

See the [LICENSE](LICENSE) file for full license information.
