use crate::Result;

/// Monoid-like wrapper for composing signals using Vec
#[derive(Default, Debug, Clone)]
pub struct Wrap<A> {
    pub items: Vec<A>,
}

impl<A> Wrap<A> {
    /// Monoid binary operation - combines two wrapped values by concatenation
    pub fn and(mut self, other: impl Into<Wrap<A>>) -> Self {
        self.items.extend(other.into().items);
        self
    }

    /// Wraps a single value
    pub fn new(value: A) -> Self {
        Wrap { items: vec![value] }
    }

    /// Combines multiple Wrap values into a single Wrap
    pub fn all<I>(wraps: I) -> Self
    where
        I: IntoIterator<Item = Wrap<A>>,
    {
        let mut result = Wrap { items: Vec::new() };
        for wrap in wraps {
            result = result.and(wrap);
        }
        result
    }
}

impl<A> Wrap<A> {
    /// Converts to Result (convenience method)
    pub fn ok(self) -> Result<Self> {
        Ok(self)
    }

    /// Returns an iterator over all values in this wrapper
    pub fn iter(&self) -> std::slice::Iter<A> {
        self.items.iter()
    }
}

impl<A> IntoIterator for Wrap<A> {
    type Item = A;
    type IntoIter = std::vec::IntoIter<A>;

    fn into_iter(self) -> Self::IntoIter {
        self.items.into_iter()
    }
}

impl<A> From<A> for Wrap<A> {
    fn from(value: A) -> Self {
        Wrap::new(value)
    }
}

impl<'a, A> IntoIterator for &'a Wrap<A> {
    type Item = &'a A;
    type IntoIter = std::slice::Iter<'a, A>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_wrap_all_empty_iterator() {
        let fixture: Vec<Wrap<i32>> = vec![];
        let actual = Wrap::all(fixture);
        let expected: Wrap<i32> = Wrap { items: vec![] };
        assert_eq!(actual.items, expected.items);
    }

    #[test]
    fn test_wrap_all_single_wrap() {
        let fixture = vec![Wrap::new(42)];
        let actual = Wrap::all(fixture);
        let expected = Wrap { items: vec![42] };
        assert_eq!(actual.items, expected.items);
    }

    #[test]
    fn test_wrap_all_multiple_wraps() {
        let fixture = vec![Wrap::new(1), Wrap::new(2), Wrap::new(3)];
        let actual = Wrap::all(fixture);
        let expected = Wrap { items: vec![1, 2, 3] };
        assert_eq!(actual.items, expected.items);
    }

    #[test]
    fn test_wrap_all_wraps_with_multiple_items() {
        let fixture = vec![
            Wrap { items: vec![1, 2] },
            Wrap { items: vec![3, 4, 5] },
            Wrap { items: vec![6] },
        ];
        let actual = Wrap::all(fixture);
        let expected = Wrap { items: vec![1, 2, 3, 4, 5, 6] };
        assert_eq!(actual.items, expected.items);
    }

    #[test]
    fn test_wrap_all_with_array() {
        let fixture = [Wrap::new("hello"), Wrap::new("world")];
        let actual = Wrap::all(fixture);
        let expected = Wrap { items: vec!["hello", "world"] };
        assert_eq!(actual.items, expected.items);
    }

    #[test]
    fn test_wrap_all_with_results() {
        fn success_wrap(value: i32) -> Result<Wrap<i32>> {
            Ok(Wrap::new(value))
        }

        let fixture = [
            success_wrap(1).unwrap(),
            success_wrap(2).unwrap(),
            success_wrap(3).unwrap(),
        ];
        let actual = Wrap::all(fixture);
        let expected = Wrap { items: vec![1, 2, 3] };
        assert_eq!(actual.items, expected.items);
    }
}
