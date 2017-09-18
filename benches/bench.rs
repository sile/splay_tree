#![feature(test)]

extern crate splay_tree;
extern crate test;

use splay_tree::SplayMap;

const SMALL: u32 = 10;
const MEDIUM: u32 = 100;
const BIG: u32 = 1000;
const HUGE: u32 = 10_000_000;

fn insert_splay(b: &mut test::Bencher, num: u32) {
    let mut map = SplayMap::new();
    for i in 0..num {
        map.insert(i, i);
    }
    let mut j = num + 1;
    b.iter(|| {
        j += 1;
        map.insert(j, j);
    })
}

fn get_middle_splay(b: &mut test::Bencher, num: u32) {
    let mut map = SplayMap::new();
    for i in 0..num {
        map.insert(i, i);
    }
    let middle = num / 2;
    b.iter(|| {
        test::black_box(map.get(&middle));
    })
}

fn get_none_splay(b: &mut test::Bencher, num: u32) {
    let mut map = SplayMap::new();
    for i in 0..num {
        map.insert(i, i);
    }
    let none = num + 1;
    b.iter(|| {
        test::black_box(map.get(&none));
    })
}

#[bench]
fn bench_insert_splay_small(b: &mut test::Bencher) {
    insert_splay(b, SMALL);
}
#[bench]
fn bench_insert_splay_medium(b: &mut test::Bencher) {
    insert_splay(b, MEDIUM);
}
#[bench]
fn bench_insert_splay_big(b: &mut test::Bencher) {
    insert_splay(b, BIG);
}
#[bench]
fn bench_insert_splay_huge(b: &mut test::Bencher) {
    insert_splay(b, HUGE);
}

#[bench]
fn bench_get_none_splay_small(b: &mut test::Bencher) {
    get_none_splay(b, SMALL);
}
#[bench]
fn bench_get_none_splay_medium(b: &mut test::Bencher) {
    get_none_splay(b, MEDIUM);
}
#[bench]
fn bench_get_none_splay_big(b: &mut test::Bencher) {
    get_none_splay(b, BIG);
}
#[bench]
fn bench_get_none_splay_huge(b: &mut test::Bencher) {
    get_none_splay(b, HUGE);
}
