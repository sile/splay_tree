extern crate splay_tree;
extern crate rand;

mod map {
    use splay_tree::SplayMap;

    #[test]
    fn new() {
        let map: SplayMap<(), ()> = SplayMap::new();
        assert!(map.is_empty());
    }

    #[test]
    fn default() {
        let map: SplayMap<(), ()> = SplayMap::default();
        assert!(map.is_empty());
    }

    #[test]
    fn insert_and_contains_key() {
        let mut map = SplayMap::new();
        assert!(!map.contains_key("foo"));
        assert_eq!(map.insert("foo", 1), None);
        assert!(map.contains_key("foo"));
        assert_eq!(map.insert("foo", 2), Some(1));
        assert!(map.contains_key("foo"));
    }

    #[test]
    fn clear() {
        let mut map = SplayMap::new();
        map.insert("foo", 1);
        assert!(map.contains_key("foo"));
        map.clear();
        assert!(!map.contains_key("foo"));
    }

    #[test]
    fn get_and_get_mut() {
        let mut map = SplayMap::new();
        assert_eq!(map.get("foo"), None);
        map.insert("foo", 1);
        assert_eq!(map.get("foo"), Some(&1));

        *map.get_mut("foo").unwrap() += 10;
        assert_eq!(map.get("foo"), Some(&11));
    }

    #[test]
    fn iterator() {
        let mut map: SplayMap<_, _> =
            vec![("foo", 1), ("bar", 2), ("baz", 3)].into_iter().collect();
        assert_eq!(vec!["bar", "baz", "foo"],
                   map.keys().cloned().collect::<Vec<_>>());
        assert_eq!(vec![2, 3, 1], map.values().cloned().collect::<Vec<_>>());
        for v in map.values_mut() {
            *v += 10;
        }
        assert_eq!(vec![("bar", 12), ("baz", 13), ("foo", 11)],
                   map.into_iter().collect::<Vec<_>>());
    }

    #[test]
    fn find_lower_or_upper_bound_key() {
        // small map
        let mut map: SplayMap<_, _> =
            vec![("foo", 1), ("bar", 2), ("baz", 3)].into_iter().collect();
        assert_eq!(map.find_lower_bound_key("aaa"), Some(&"bar"));
        assert_eq!(map.find_upper_bound_key("aaa"), Some(&"bar"));
        assert_eq!(map.find_lower_bound_key("baz"), Some(&"baz"));
        assert_eq!(map.find_upper_bound_key("baz"), Some(&"foo"));
        assert_eq!(map.find_lower_bound_key("zzz"), None);
        assert_eq!(map.find_upper_bound_key("zzz"), None);

        // large map
        use rand::{self, Rng};
        let mut input = (0..1000).into_iter().collect::<Vec<_>>();
        rand::thread_rng().shuffle(&mut input);

        let mut map: SplayMap<_, _> = input.into_iter().map(|n| (n, n)).collect();
        assert_eq!(map.find_lower_bound_key(&500), Some(&500));
        assert_eq!(map.find_upper_bound_key(&500), Some(&501));
        assert_eq!(map.find_lower_bound_key(&999), Some(&999));
        assert_eq!(map.find_upper_bound_key(&999), None);
    }

    #[test]
    fn remove() {
        let mut map = SplayMap::new();
        map.insert("foo", 1);
        map.insert("bar", 2);
        map.insert("baz", 3);
        assert_eq!(map.remove("bar"), Some(2));
        assert_eq!(map.remove("bar"), None);
        assert_eq!(map.len(), 2);
    }

    #[test]
    fn enry() {
        let mut count = SplayMap::new();

        for x in vec!["a", "b", "a", "c", "a", "b"] {
            *count.entry(x).or_insert(0) += 1;
        }

        assert_eq!(count.get("a"), Some(&3));
        assert_eq!(count.get("b"), Some(&2));
        assert_eq!(count.get("c"), Some(&1));
    }

    #[test]
    fn extend() {
        let mut map = SplayMap::new();
        map.extend(vec![("foo", 1), ("bar", 2)]);
        map.extend(vec![("bar", 3), ("baz", 4)]);
        assert_eq!(vec![("bar", 3), ("baz", 4), ("foo", 1)],
                   map.into_iter().collect::<Vec<_>>());
    }

    #[test]
    fn hash_eq_ord() {
        let mut a: SplayMap<_, _> = vec![("bar", 2), ("baz", 3)].into_iter().collect();
        let mut b: SplayMap<_, _> = vec![("foo", 1), ("bar", 2)].into_iter().collect();

        assert!(hash(&a) != hash(&b));
        assert!(a != b);
        assert!(a < b);

        b.insert("baz", 3);
        assert!(a < b);

        a.insert("foo", 1);
        assert!(hash(&a) == hash(&b));
        assert!(a == b);
    }

    #[test]
    fn large_map() {
        use rand::{self, Rng};

        let mut input = (0..1000).into_iter().collect::<Vec<_>>();
        rand::thread_rng().shuffle(&mut input);

        let mut map: SplayMap<_, _> = input.into_iter().map(|n| (n, n)).collect();
        for i in 0..1000 {
            assert_eq!(map.remove(&i), Some(i));
        }
        assert!(map.is_empty());
    }

    use std::hash;
    fn hash<T: hash::Hash>(x: &T) -> u64 {
        use std::hash::Hasher;
        let mut hasher = hash::SipHasher::new();
        x.hash(&mut hasher);
        hasher.finish()
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
