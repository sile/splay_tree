fn main() {
    let mut set = splay_tree::SplaySet::new();
    for _ in 0..1_000_000 {
        set.insert(rand::random::<u64>());
    }
}
