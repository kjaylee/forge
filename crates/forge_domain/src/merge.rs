pub mod std {
    pub fn overwrite<T>(base: &mut T, other: T) {
        *base = other;
    }
}
pub mod vec {
    pub use merge::vec::*;
    pub fn unify<T: PartialEq>(base: &mut Vec<T>, other: Vec<T>) {
        for other_item in other {
            if !base.contains(&other_item) {
                base.push(other_item);
            }
        }
    }
}

pub mod bool {
    pub use merge::bool::*;
}
