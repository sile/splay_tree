use rand::seq::SliceRandom;
use std::collections::hash_map::DefaultHasher;
use std::hash;

fn hash<T: hash::Hash>(x: &T) -> u64 {
    use std::hash::Hasher;
    let mut hasher = DefaultHasher::new();
    x.hash(&mut hasher);
    hasher.finish()
}

mod map {
    use super::*;
    #[cfg(feature = "serde")]
    use serde_json::{from_str, to_string};
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
        let mut map: SplayMap<_, _> = vec![("foo", 1), ("bar", 2), ("baz", 3)]
            .into_iter()
            .collect();
        assert_eq!(
            vec!["bar", "baz", "foo"],
            map.keys().cloned().collect::<Vec<_>>()
        );
        assert_eq!(vec![2, 3, 1], map.values().cloned().collect::<Vec<_>>());
        for v in map.values_mut() {
            *v += 10;
        }
        assert_eq!(
            vec![("bar", 12), ("baz", 13), ("foo", 11)],
            map.into_iter().collect::<Vec<_>>()
        );
    }

    #[test]
    fn find_lower_or_upper_bound_key() {
        // small map
        let mut map: SplayMap<_, _> = vec![("foo", 1), ("bar", 2), ("baz", 3)]
            .into_iter()
            .collect();
        assert_eq!(map.find_lower_bound_key("aaa"), Some(&"bar"));
        assert_eq!(map.find_upper_bound_key("aaa"), Some(&"bar"));
        assert_eq!(map.find_lower_bound_key("baz"), Some(&"baz"));
        assert_eq!(map.find_upper_bound_key("baz"), Some(&"foo"));
        assert_eq!(map.find_lower_bound_key("zzz"), None);
        assert_eq!(map.find_upper_bound_key("zzz"), None);

        // large map
        let mut input = (0..1000).into_iter().collect::<Vec<_>>();
        input.shuffle(&mut rand::rng());

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
        assert_eq!(
            vec![("bar", 3), ("baz", 4), ("foo", 1)],
            map.into_iter().collect::<Vec<_>>()
        );
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
        let mut input = (0..1000).into_iter().collect::<Vec<_>>();
        input.shuffle(&mut rand::rng());

        let mut map: SplayMap<_, _> = input.into_iter().map(|n| (n, n)).collect();
        for i in 0..1000 {
            assert_eq!(map.remove(&i), Some(i));
        }
        assert!(map.is_empty());
    }

    #[cfg(feature = "serde")]
    #[test]
    fn map_serde() {
        let mut input = (0..1000).into_iter().collect::<Vec<_>>();
        input.shuffle(&mut rand::rng());

        let map: SplayMap<_, _> = input.into_iter().map(|n| (n, n)).collect();
        let ser_map: SplayMap<_, _> = from_str(&to_string(&map).unwrap()).unwrap();
        assert_eq!(ser_map, map);
    }
}

mod set {
    use super::*;
    #[cfg(feature = "serde")]
    use serde_json::{from_str, to_string};
    use splay_tree::SplaySet;

    #[test]
    fn new() {
        let set: SplaySet<()> = SplaySet::new();
        assert!(set.is_empty());
    }

    #[test]
    fn default() {
        let set: SplaySet<()> = SplaySet::default();
        assert!(set.is_empty());
    }

    #[test]
    fn insert_and_replace_contains() {
        let mut set = SplaySet::new();

        assert!(!set.contains("foo"));
        assert_eq!(set.insert("foo"), true);
        assert!(set.contains("foo"));
        assert_eq!(set.insert("foo"), false);
        assert!(set.contains("foo"));

        assert_eq!(set.replace("bar"), None);
        assert_eq!(set.replace("bar"), Some("bar"));
        assert!(set.contains("bar"));
    }

    #[test]
    fn clear() {
        let mut set = SplaySet::new();
        set.insert("foo");
        assert!(set.contains("foo"));
        set.clear();
        assert!(!set.contains("foo"));
    }

    #[test]
    fn get() {
        let mut set = SplaySet::new();
        assert_eq!(set.get("foo"), None);
        set.insert("foo");
        assert_eq!(set.get("foo"), Some(&"foo"));
    }

    #[test]
    fn iterator() {
        let set: SplaySet<_> = vec!["foo", "bar", "baz"].into_iter().collect();
        assert_eq!(
            set.iter().cloned().collect::<Vec<_>>(),
            ["bar", "baz", "foo"]
        );
        assert_eq!(
            (&set).into_iter().cloned().collect::<Vec<_>>(),
            ["bar", "baz", "foo"]
        );
        assert_eq!(set.into_iter().collect::<Vec<_>>(), ["bar", "baz", "foo"]);
    }

    #[test]
    fn find_lower_or_upper_bound() {
        // small set
        let mut set: SplaySet<_> = vec!["foo", "bar", "baz"].into_iter().collect();
        assert_eq!(set.find_lower_bound("aaa"), Some(&"bar"));
        assert_eq!(set.find_upper_bound("aaa"), Some(&"bar"));
        assert_eq!(set.find_lower_bound("baz"), Some(&"baz"));
        assert_eq!(set.find_upper_bound("baz"), Some(&"foo"));
        assert_eq!(set.find_lower_bound("zzz"), None);
        assert_eq!(set.find_upper_bound("zzz"), None);

        // large set
        let mut input = (0..1000).into_iter().collect::<Vec<_>>();
        input.shuffle(&mut rand::rng());

        let mut set: SplaySet<_> = input.into_iter().collect();
        assert_eq!(set.find_lower_bound(&500), Some(&500));
        assert_eq!(set.find_upper_bound(&500), Some(&501));
        assert_eq!(set.find_lower_bound(&999), Some(&999));
        assert_eq!(set.find_upper_bound(&999), None);
    }

    #[test]
    fn remove_and_take() {
        let mut set = SplaySet::new();
        set.insert("foo");
        set.insert("bar");
        set.insert("baz");

        assert_eq!(set.remove("bar"), true);
        assert_eq!(set.remove("bar"), false);
        assert_eq!(set.len(), 2);

        assert_eq!(set.take("foo"), Some("foo"));
        assert_eq!(set.take("foo"), None);
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn extend() {
        let mut set = SplaySet::new();
        set.extend(vec!["foo", "bar"]);
        set.extend(vec!["bar", "baz"]);
        assert_eq!(set.into_iter().collect::<Vec<_>>(), ["bar", "baz", "foo"]);
    }

    #[test]
    fn hash_eq_ord() {
        let mut a: SplaySet<_> = vec!["bar", "baz"].into_iter().collect();
        let mut b: SplaySet<_> = vec!["foo", "bar"].into_iter().collect();

        assert!(hash(&a) != hash(&b));
        assert!(a != b);
        assert!(a < b);

        b.insert("baz");
        assert!(a < b);

        a.insert("foo");
        assert!(hash(&a) == hash(&b));
        assert!(a == b);
    }

    #[test]
    fn large_set() {
        let mut input = (0..1000).collect::<Vec<_>>();
        input.shuffle(&mut rand::rng());

        let mut set: SplaySet<_> = input.iter().cloned().collect();
        for i in input {
            assert!(set.remove(&i));
        }
        assert!(set.is_empty());
    }

    #[test]
    fn set_operations() {
        let a: SplaySet<_> = vec![1, 2, 3].into_iter().collect();
        let b: SplaySet<_> = vec![3, 4, 5].into_iter().collect();
        let c: SplaySet<_> = vec![5, 6, 7].into_iter().collect();
        let d: SplaySet<_> = vec![1, 2, 3, 4].into_iter().collect();

        assert_eq!(a.difference(&b).cloned().collect::<Vec<_>>(), [1, 2]);
        assert_eq!((&a - &b).into_iter().collect::<Vec<_>>(), [1, 2]);

        assert_eq!(
            a.symmetric_difference(&b).cloned().collect::<Vec<_>>(),
            [1, 2, 4, 5]
        );
        assert_eq!((&a ^ &b).into_iter().collect::<Vec<_>>(), [1, 2, 4, 5]);

        assert_eq!(a.intersection(&b).cloned().collect::<Vec<_>>(), [3]);
        assert_eq!((&a & &b).into_iter().collect::<Vec<_>>(), [3]);

        assert_eq!(a.union(&b).cloned().collect::<Vec<_>>(), [1, 2, 3, 4, 5]);
        assert_eq!((&a | &b).into_iter().collect::<Vec<_>>(), [1, 2, 3, 4, 5]);

        assert!(!a.is_disjoint(&a));
        assert!(!a.is_disjoint(&b));
        assert!(a.is_disjoint(&c));
        assert!(!a.is_disjoint(&d));

        assert!(a.is_subset(&a));
        assert!(!a.is_subset(&b));
        assert!(!a.is_subset(&c));
        assert!(a.is_subset(&d));

        assert!(a.is_superset(&a));
        assert!(!a.is_superset(&b));
        assert!(!a.is_superset(&c));
        assert!(!a.is_superset(&d));
        assert!(d.is_superset(&a));
        assert!(!d.is_superset(&b));
        assert!(!d.is_superset(&c));
    }

    #[test]
    fn vec_like() {
        let mut set = SplaySet::new();
        {
            let mut vec = set.as_vec_like_mut();
            vec.push(10);
            vec.push(3);
            vec.push(7);
            vec.push(8);
            vec.pop();
            assert_eq!(vec.get(0), Some(&10));
            assert_eq!(vec.get(1), Some(&3));
            assert_eq!(vec.get(2), Some(&7));
            assert_eq!(vec.get(3), None);

            assert_eq!(vec.find_index(&3), Some(1));
            assert_eq!(vec.find_index(&300), None);

            assert_eq!(vec.iter().cloned().collect::<Vec<_>>(), [10, 3, 7]);
        }
        assert_eq!(set.iter().cloned().collect::<Vec<_>>(), [3, 7, 10]);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn set_serde() {
        let mut input = (0..1000).into_iter().collect::<Vec<_>>();
        input.shuffle(&mut rand::rng());

        let set: SplaySet<_> = input.into_iter().collect();
        let ser_set: SplaySet<_> = from_str(&to_string(&set).unwrap()).unwrap();
        assert_eq!(ser_set, set);
    }
}

mod heap {
    use super::*;
    #[cfg(feature = "serde")]
    use serde_json::{from_str, to_string};
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
        assert_eq!(
            vec![3, 2, 1],
            (&heap).into_iter().cloned().collect::<Vec<_>>()
        );
        assert_eq!(vec![3, 2, 1], heap.into_iter().collect::<Vec<_>>());
    }

    #[test]
    fn extend() {
        let mut heap = SplayHeap::new();
        heap.extend(vec![1, 2, 3]);
        heap.extend(vec![&3, &4]);
        assert_eq!(
            vec![4, 3, 3, 2, 1],
            heap.iter().cloned().collect::<Vec<_>>()
        );
    }

    #[test]
    fn large_heap() {
        let mut input = (0..1000).into_iter().collect::<Vec<_>>();
        input.shuffle(&mut rand::rng());

        let mut heap = input.into_iter().collect::<SplayHeap<_>>();
        while let Some(n) = heap.pop() {
            assert_eq!(n, heap.len());
        }
    }

    #[cfg(feature = "serde")]
    #[test]
    fn heap_serde() {
        use std::iter::FromIterator;

        let mut input = (0..1000).into_iter().collect::<Vec<_>>();
        input.shuffle(&mut rand::rng());

        let heap: SplayHeap<_> = input.into_iter().collect();
        let ser_heap: SplayHeap<u64> = from_str(&to_string(&heap).unwrap()).unwrap();
        assert_eq!(Vec::from_iter(ser_heap), Vec::from_iter(heap));
    }
}
