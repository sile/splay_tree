extern crate splay_tree;
extern crate rand;

mod map {
    use splay_tree::SplayMap;

    #[test]
    fn basic() {
        let mut map = SplayMap::new();
        assert_eq!(0, map.len());
        assert_eq!(None, map.get("foo"));
        assert_eq!(None, map.insert("foo", 1));
        assert_eq!(Some(&1), map.get("foo"));
        assert_eq!(1, map.len());
        assert_eq!(Some(1), map.remove("foo"));
        assert_eq!(None, map.get("foo"));
        assert_eq!(0, map.len());

        map.clear();
        assert_eq!(None, map.get("foo"));

        map.insert("foo", 1);
        map.insert("bar", 2);
        map.insert("baz", 3);
        assert_eq!(vec![("bar", 2), ("baz", 3), ("foo", 1)],
                   map.iter().map(|(k, v)| (*k, *v)).collect::<Vec<_>>());
    }
}

mod heap {
    use splay_tree::SplayHeap;

    #[test]
    fn new() {
        let heap: SplayHeap<()> = SplayHeap::new();
        assert!(heap.is_empty());
    }

    #[test]
    fn default() {
        let heap: SplayHeap<()> = SplayHeap::default();
        assert!(heap.is_empty());
    }

    #[test]
    fn push_and_pop() {
        let mut heap = SplayHeap::new();

        heap.push(10);
        heap.push(1);
        heap.push(30);
        heap.push(7);
        assert_eq!(heap.len(), 4);

        assert_eq!(heap.pop(), Some(30));
        assert_eq!(heap.pop(), Some(10));
        assert_eq!(heap.pop(), Some(7));
        assert_eq!(heap.pop(), Some(1));
        assert!(heap.is_empty());
    }

    #[test]
    fn peek() {
        let mut heap = vec![1, 2, 3].into_iter().collect::<SplayHeap<_>>();
        assert_eq!(heap.peek(), Some(&3));
        assert_eq!(heap.pop(), Some(3));
        heap.clear();

        assert_eq!(heap.peek(), None);
    }

    #[test]
    fn iterator() {
        let heap = vec![1, 2, 3].into_iter().collect::<SplayHeap<_>>();
        assert_eq!(vec![3, 2, 1], heap.iter().cloned().collect::<Vec<_>>());
        assert_eq!(vec![3, 2, 1],
                   (&heap).into_iter().cloned().collect::<Vec<_>>());
        assert_eq!(vec![3, 2, 1], heap.into_iter().collect::<Vec<_>>());
    }

    #[test]
    fn extend() {
        let mut heap = SplayHeap::new();
        heap.extend(vec![1, 2, 3]);
        heap.extend(vec![&3, &4]);
        assert_eq!(vec![4, 3, 3, 2, 1],
                   heap.iter().cloned().collect::<Vec<_>>());
    }

    #[test]
    fn large_heap() {
        use rand::{self, Rng};

        let mut input = (0..1000).into_iter().collect::<Vec<_>>();
        rand::thread_rng().shuffle(&mut input);

        let mut heap = input.into_iter().collect::<SplayHeap<_>>();
        while let Some(n) = heap.pop() {
            assert_eq!(n, heap.len());
        }
    }
}
