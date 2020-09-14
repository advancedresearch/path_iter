use crate::*;

use std::ops::Range;

/// Negation.
#[derive(Clone)]
pub struct Neg;

impl<T> HigherIntoIterator<Item<Range<T>>> for Neg
    where T: std::ops::Sub<Output = T> + From<u8>
{
    type Item = T;
    type IntoIter = Range<T>;
    fn hinto_iter(self, arg: Item<Range<T>>) -> Self::IntoIter {
        let arg = arg.inner();
        Range {start: T::from(1) - arg.end, end: T::from(1) - arg.start}
    }
}

impl HigherIntoIterator<Item<i64>> for Neg {
    type Item = i64;
    type IntoIter = Range<i64>;
    fn hinto_iter(self, arg: Item<i64>) -> Self::IntoIter {
        let arg = arg.inner();
        Range {start: -arg, end: 1-arg}
    }
}

/// Addition.
#[derive(Clone)]
pub struct Add;

/// Iterates over numbers that adds up to some range.
pub struct AddRangeIter {
    range: Range<i64>,
    ind: i64,
    add: i64,
}

impl Iterator for AddRangeIter {
    type Item = (i64, i64);
    fn next(&mut self) -> Option<Self::Item> {
        let res = Some((self.ind - self.add, self.add));
        self.ind += 1;
        if self.ind >= self.range.end {
            self.ind = self.range.start;
            if self.add >= 0 {
                self.add += 1;
            }
            self.add = -self.add;
        }
        res
    }
}

impl HigherIntoIterator<Item<Range<i64>>> for Add
{
    type Item = (i64, i64);
    type IntoIter = AddRangeIter;
    fn hinto_iter(self, arg: Item<Range<i64>>) -> Self::IntoIter {
        let arg = arg.inner();
        AddRangeIter {
            ind: arg.start,
            range: arg,
            add: 0,
        }
    }
}

impl HigherIntoIterator<Item<i64>> for Add {
    type Item = (i64, i64);
    type IntoIter = AddRangeIter;
    fn hinto_iter(self, arg: Item<i64>) -> Self::IntoIter {
        let arg = arg.inner();
        Add.hinto_iter(item(arg..arg+1))
    }
}
