extern crate splay_tree;

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
