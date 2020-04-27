//! From https://en.wikipedia.org/wiki/Fowler%E2%80%93Noll%E2%80%93Vo_hash_function

use std::collections::HashMap;

pub struct FNV(u64);

const INIT: u64 = 0xcbf29ce484222325;
const PRIME: u64 = 0x100000001b3;

impl FNV {
    #[inline]
    fn new() -> Self {
        FNV(INIT)
    }
}

impl std::hash::Hasher for FNV {
    fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            // fnv-1a
            self.0 ^= *b as u64;
            self.0 = self.0.wrapping_mul(PRIME);
        }
    }

    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }
}

pub struct FNVBuildHasher;
impl std::hash::BuildHasher for FNVBuildHasher {
    type Hasher = FNV;
    fn build_hasher(&self) -> FNV {
        FNV::new()
    }
}

pub type FnvHashMap<K, V> = std::collections::HashMap<K, V, FNVBuildHasher>;

pub fn new_table<K, V>() -> FnvHashMap<K, V> {
    HashMap::with_hasher(FNVBuildHasher)
}
pub fn new_table_with_cap<K, V>(n: usize) -> FnvHashMap<K, V> {
    HashMap::with_capacity_and_hasher(n, FNVBuildHasher)
}
