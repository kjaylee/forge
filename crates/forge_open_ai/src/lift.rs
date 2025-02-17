#![allow(dead_code)]
/// A simple wrapper to lift a value into a newtype so that it's easier to
/// convert between types.
pub struct Lift<A>(A);

impl<A> Lift<A> {
    pub fn new(a: A) -> Self {
        Lift(a)
    }

    pub fn take(self) -> A {
        self.0
    }
}

pub trait LiftUp<A> {
    fn lift(self) -> Lift<A>;
}

impl<A> LiftUp<A> for A {
    fn lift(self) -> Lift<A> {
        Lift::new(self)
    }
}
