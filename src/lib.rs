#![deny(missing_docs)]

//! # Path-Iter
//! A cocategory enumeration library based on path semantics
//!
//! Implementation based on paper [Cocategory Enumeration](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip/cocategory-enumeration.pdf).
//!
//! For an introduction to Path Semantics,
//! see [this paper](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip/introduction-to-path-semantics-for-computer-scientists.pdf).
//!
//! ### Sub-types in Path Semantics
//!
//! In normal Path Semantics, one uses
//! [normal paths](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip/normal-paths.pdf)
//! in theorem proving.
//! Normal paths is a derivation from functions with sub-types.
//!
//! This library focuses on sub-types, not on the more general case of normal paths.
//!
//! A sub-type in Path Semantics is written in this form:
//!
//! ```text
//! x : [f] a
//! ```
//!
//! Where `x` is some input, `f` is a function and `a` is the output of `f`.
//!
//! This library is for enumerating such sub-types efficiently.
//!
//! ### Example: AND
//!
//! The `path!` macro is used to write in the standard notation of Path Semantics.
//! It constructs a type using `Path` that implements `IntoIterator`:
//!
//! ```rust
//! use path_iter::*;
//!
//! fn main() {
//!     for a in path!([And] true) {
//!         // Prints `(true, true)`
//!         println!("{:?}", a);
//!     }
//! }
//! ```
//!
//! It prints `(true, true)` because that is the only input value to `And`
//! which produces `true` as output.
//!
//! ### Example: AND 2
//!
//! You can decide the output value at runtime:
//!
//! ```rust
//! use path_iter::*;
//!
//! fn main() {
//!     for &b in &[false, true] {
//!         for a in path!([And] b) {
//!             println!("{:?}", a);
//!         }
//!         println!("");
//!     }
//! }
//! ```
//!
//! This prints:
//!
//! ```text
//! (false, false)
//! (false, true)
//! (true, false)
//!
//! (true, true)
//! ```
//!
//! ### Example: AND-NOT
//!
//! You can chain path sub-types together:
//!
//! ```rust
//! use path_iter::*;
//!
//! fn main() {
//!     for a in path!([And] [Not] true) {
//!         println!("{:?}", a);
//!     }
//! }
//! ```
//!
//! ### Example: Partial Application
//!
//! Partial application is a technique where
//! a function reduces to another function
//! when calling it with fewer arguments than the signature.
//!
//! For example, `And(true)` reduces to `Idb`.
//!
//! ```rust
//! use path_iter::*;
//!
//! fn main() {
//!    for a in path!([And(true)] true) {
//!         println!("{:?}", a);
//!     }
//! }
//! ```
//!
//! This should not be confused with function currying,
//! which is extensionally equal to partial application,
//! but captures the underlying function in a closure.
//!
//! The `path!` macro expands to partial application automatically, but it is very limited.
//! Outside the macro `path!` or for complex cases, one must use `PApp::papp`.
//!
//! ### Example: AND 3
//!
//! The standard notation for composing paths is not very friendly with Rust macros.
//! Therefore, one can use a single bracket `[]` with functions separated by commas:
//!
//! ```rust
//! use path_iter::*;
//!
//! fn main() {
//!     for a in path!([((And, And), (And, And)), (And, And), And] true) {
//!         println!("{:?}", a);
//!     }
//! }
//! ```

use std::iter::IntoIterator;

pub use boolean::*;
pub use range::*;

/// Syntax sugar for a path sub-type.
///
/// For example:
/// ```rust
/// use path_iter::*;
///
/// fn main() {
///     for a in path!([And] true) {
///         // Prints `(true, true)`
///         println!("{:?}", a);
///     }
/// }
/// ```
#[macro_export]
macro_rules! path(
    ([$x:ident ($y:expr)] $([$($z:tt)*])+ $w:expr) => {
        Path($crate::PApp::papp($x, $y), path!($([$($z)*])+ $w))
    };
    ([$x0:expr , $($x:expr),+ $(,)?] $z:expr) => {
        path($x0, path!([$($x),*] $z))
    };
    ([$x:expr] [$x1:expr] [$x2:expr] [$x3:expr] [$x4:expr] [$x5:expr] [$x6:expr] $z:expr) => {
        path($x, path!([$x1] [$x2] [$x3] [$x4] [$x5] [$x6] $z))
    };
    ([$x:expr] [$x1:expr] [$x2:expr] [$x3:expr] [$x4:expr] [$x5:expr] $z:expr) => {
        path($x, path!([$x1] [$x2] [$x3] [$x4] [$x5] $z))
    };
    ([$x:expr] [$x1:expr] [$x2:expr] [$x3:expr] [$x4:expr] $z:expr) => {
        path($x, path!([$x1] [$x2] [$x3] [$x4] $z))
    };
    ([$x:expr] [$x1:expr] [$x2:expr] [$x3:expr] $z:expr) => {
        path($x, path!([$x1] [$x2] [$x3] $z))
    };
    ([$x:expr] [$x1:expr] [$x2:expr] $z:expr) => {
        path($x, path!([$x1] [$x2] $z))
    };
    ([$x:expr] [$y:expr] $z:expr) => {
        path($x, path!([$y] $z))
    };
    ([$x:ident ($y:expr)] $z:expr) => {
        Path($crate::PApp::papp($x, $y), $crate::item($z))
    };
    ([$x:expr] $y:expr) => {
        Path($x, $crate::item($y))
    };
);

/// Syntax sugar for the type of a path sub-type.
///
/// For example:
/// ```rust
/// use path_iter::*;
///
/// fn main() {
///     for a in imply(false) {
///         // Prints `(true, false)`
///         println!("{:?}", a);
///     }
/// }
///
/// pub fn imply(b: bool) -> path_type!([(Not, Idb)] [Or] bool) {
///     path!([(Not, Idb)] [Or] b)
/// }
/// ```
#[macro_export]
macro_rules! path_type(
    ([$x0:ty , $($x:ty),+ $(,)?] $z:ty) => {
        PathComp<$x0, path_type!([$($x),*] $z)>
    };
    ([$x:ty] [$y:ty] $z:ty) => {
        PathComp<$x, path_type!([$y] $z)>
    };
    ([$x:ty] $y:ty) => {
        PathEnd<$x, $y>
    };
);

/// Stores a path sub-type with either `[T] U` (left) or `[T] [V] ...` (right).
#[derive(Clone)]
pub struct Path<T, U, V>(pub T, pub Either<U, V>);

/// Represents a terminal path `[T] U`.
pub type PathEnd<T, U> = Path<T, U, Empty>;

/// Represents a path composition.
pub type PathComp<T, V> = Path<T, Empty, V>;

mod boolean;
mod range;

/// Implemented for partial application.
///
/// For example, `And::papp(true)` returns `Either::Left(Idb)`.
pub trait PApp {
    /// The argument type.
    type Arg;
    /// The return type of partial application.
    type Ret;
    /// Applies argument to function, using partial application.
    fn papp(self, arg: Self::Arg) -> Self::Ret;
}

/// Iterates over two the sum type of two iterators.
#[derive(Clone)]
pub enum EitherIter<T, U> {
    /// The left iterator.
    Left(T),
    /// The right iterator.
    Right(U)
}

/// Used to lift iterator generators into a sum type.
///
/// This is used in partial application,
/// e.g. `And::papp(true)` returns `Either::Left(Idb)`.
#[derive(Clone)]
pub enum Either<T, U> {
    /// The left iterator generator.
    Left(T),
    /// The right iterator generator.
    Right(U)
}

/// A type that is impossible to construct.
#[derive(Clone)]
pub enum Empty {}

/// Used to make end of path disambiguous from path composition.
pub type Item<T> = Either<T, Empty>;

/// Constructs an item.
pub fn item<T>(a: T) -> Item<T> {Either::Left(a)}

/// Construct a path composition.
pub fn path<T, U>(a: T, b: U) -> PathComp<T, U> {Path(a, Either::Right(b))}

/// Gets the pullback of two maps `f` and `g`.
///
/// For more information about pullbacks, see [wikipedia article](https://en.wikipedia.org/wiki/Pullback_(category_theory)).
pub fn pullback<T, U>(f: T, g: U) -> path_type!([(T, U), Eqb] bool) {
    path!([(f, g), Eqb] true)
}

impl<T> Item<T> {
    /// Gets the inner value.
    pub fn inner(self) -> T {
        if let Either::Left(a) = self {
            a
        } else {
            // This is unreachable because `Empty` can not be constructed.
            unreachable!()
        }
    }
}

impl<T> Either<Empty, T> {
    /// Gets the inner right value.
    pub fn inner_right(self) -> T {
        if let Either::Right(a) = self {
            a
        } else {
            // This is unreachable because `Empty` can not be constructed.
            unreachable!()
        }
    }
}

impl<T> IntoIterator for Item<T> {
    type Item = T;
    type IntoIter = <Option<T> as IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        if let Either::Left(a) = self {
            Some(a).into_iter()
        } else {
            // This is unreachable because `Empty` can not be constructed.
            unreachable!()
        }
    }
}

impl<T, U, V> Iterator for EitherIter<T, U>
    where T: Iterator<Item = V>, U: Iterator<Item = V>
{
    type Item = V;
    fn next(&mut self) -> Option<V> {
        match self {
            EitherIter::Left(a) => a.next(),
            EitherIter::Right(b) => b.next()
        }
    }
}

/// Iterates over a product of two iterator generators.
///
/// For example, `[(And, Or)] (true, false)`
/// iterates over the product of `[And] true` and `[Or] false`.
pub struct ProductIter<T, U, V1, V2> {
    // Left/first iterator.
    inner: T,
    // Right/second iterator.
    outer: U,
    // The object that turns into the second iterator.
    // outer_ty: V,
    // Stores values that are cloned from the first iterator.
    inner_vals: Vec<V1>,
    // Stores values that are cloned from the second iterator.
    outer_vals: Vec<V2>,
    // The index of the cloned value from the first iterator.
    inner_ind: usize,
    // The index of the cloned value from the second iterator.
    outer_ind: usize,
}

#[derive(Debug, PartialEq, Eq)]
enum State {
    Top,
    TopLeft,
    TopRight,
    Middle,
    MiddleRight,
    MiddleBottom,
    MiddleLeft,
    MiddleHorizontal,
    BottomRight,
    BottomLeft,
    Outside,
    OutsideRight,
    OutsideBottom,
}

impl State {
    pub fn new((a, b): (usize, usize), (n, m): (usize, usize)) -> State {
        let origo = (a == 0) && (b == 0);
        let top = a == 0;
        let left = b == 0;
        let right = (b + 1) == m;
        let bottom = (a + 1) == n;
        let bottom_right = right && bottom;
        let top_right = top && right;
        let bottom_left = left && bottom;
        let middle_a = (a > 0) && (a < n);
        let middle_b = (b > 0) && (b < m);
        let middle = middle_a && middle_b;
        let outside_a = a >= n;
        let outside_b = b >= m;
        let outside = outside_a && outside_b;
        if outside {State::Outside}
        else if bottom_right {State::BottomRight}
        else if bottom && middle_b && !top {State::MiddleBottom}
        else if right && middle_a {State::MiddleRight}
        else if top_right && !origo {State::TopRight}
        else if origo {State::TopLeft}
        else if top && middle_b && !bottom {State::Top}
        else if bottom_left {State::BottomLeft}
        else if left && middle_a {State::MiddleLeft}
        else if middle {State::Middle}
        else if outside_a && (middle_b || right || left) {State::OutsideBottom}
        else if outside_b && (middle_a || bottom || top) {State::OutsideRight}
        else {State::MiddleHorizontal}
    }

    pub fn next(&self, (a, b): (usize, usize), (n, m): (usize, usize)) -> (usize, usize) {
        match self {
            State::Outside | State::BottomRight => (n, m),
            State::MiddleRight |
            State::Top |
            State::TopRight |
            State::Middle => (a + 1, b.max(1) - 1),
            State::OutsideBottom |
            State::MiddleBottom |
            State::BottomLeft |
            State::MiddleLeft => {
                let (a, b) = (0, a + b + 1);
                let new_state = State::new((a, b), (n, m));
                if &new_state == self {return (n, m)};
                if new_state == State::TopRight {return (a, b)};
                new_state.next((a, b), (n, m))
            }
            State::OutsideRight => {
                let k = a + b;
                let (a, b) = (k - (m - 1), m - 1);
                let new_state = State::new((a, b), (n, m));
                if &new_state == self {return (n, m)};
                if new_state == State::OutsideBottom {return (n, m)};
                if new_state == State::BottomRight {return (a, b)};
                if new_state == State::MiddleRight {return (a, b)};
                new_state.next((a, b), (n, m))
            }
            State::TopLeft => {
                let new_state = State::new((0, 1), (n, m));
                if new_state == State::OutsideRight {return (1, 0)};
                (0, 1)
            }
            State::MiddleHorizontal => (0, a + b + 1),
        }
    }
}

fn diag_prod((a, b): (usize, usize), (n, m): (usize, usize)) -> (usize, usize) {
    let state = State::new((a, b), (n, m));
    state.next((a, b), (n, m))
}

impl<T, U, W1, W2> Iterator for ProductIter<T, U, W1, W2>
    where T: Iterator<Item = W1>,
          U: Iterator<Item = W2>,
          W1: Clone,
          W2: Clone,
{
    type Item = (W1, W2);
    fn next(&mut self) -> Option<Self::Item> {
        for _ in 0..2 {
            if let Some(u) = self.inner.next() {
                self.inner_vals.push(u);
            }
            if let Some(v) = self.outer.next() {
                self.outer_vals.push(v);
            }
        }

        if self.inner_ind >= self.inner_vals.len() ||
           self.outer_ind >= self.outer_vals.len()
        {
            None
        } else {
            let u = self.inner_vals[self.inner_ind].clone();
            let v = self.outer_vals[self.outer_ind].clone();
            let (a, b) = diag_prod(
                (self.inner_ind, self.outer_ind),
                (self.inner_vals.len(), self.outer_vals.len())
            );
            self.inner_ind = a;
            self.outer_ind = b;
            Some((u, v))
        }
    }
}

/// Implemented by iterator generators.
///
/// A function, e.g. `And` is a iterator generator
/// with respect to the output, e.g. `[And] true`.
/// This iterates over inputs that makes `And` return `true`.
pub trait HigherIntoIterator<T> {
    /// The item type generated by the iterator.
    type Item;
    /// The iterator type.
    type IntoIter;
    /// Construct iterator from an argument.
    fn hinto_iter(self, a: T) -> Self::IntoIter;
}

impl<T1, T2, U1, U2, V1, V2, I1, I2> HigherIntoIterator<Item<(U1, U2)>> for (T1, T2)
    where T1: HigherIntoIterator<Item<U1>, Item = V1, IntoIter = I1>,
          T2: Clone + HigherIntoIterator<Item<U2>, Item = V2, IntoIter = I2>,
          I1: Iterator<Item = V1>,
          U2: Clone
{
    type Item = (V1, V2);
    type IntoIter = ProductIter<I1, I2, V1, V2>;
    fn hinto_iter(self, arg: Item<(U1, U2)>) -> Self::IntoIter {
        let (u1, u2) = arg.inner();
        let (a, b) = self;
        let inner = a.hinto_iter(item(u1));
        let outer = b.hinto_iter(item(u2));
        ProductIter {
            inner,
            outer,
            inner_vals: vec![],
            outer_vals: vec![],
            inner_ind: 0,
            outer_ind: 0,
        }
    }
}

impl<T, U, V, I> HigherIntoIterator<Item<U>> for Item<T>
    where Item<T>: IntoIterator<Item = V, IntoIter = I>,
          I: Iterator<Item = V>
{
    type Item = V;
    type IntoIter = I;
    fn hinto_iter(self, _: Item<U>) -> Self::IntoIter {
        <Self as IntoIterator>::into_iter(self)
    }
}

impl<T, U, V, W, I1, I2> HigherIntoIterator<Item<V>> for Either<T, U>
    where T: HigherIntoIterator<Item<V>, Item = W, IntoIter = I1>,
          U: HigherIntoIterator<Item<V>, Item = W, IntoIter = I2>,
          I1: Iterator<Item = W>,
          I2: Iterator<Item = W>
{
    type Item = W;
    type IntoIter = EitherIter<I1, I2>;
    fn hinto_iter(self, arg: Item<V>) -> Self::IntoIter {
        match self {
            Either::Left(a) => EitherIter::Left(a.hinto_iter(arg)),
            Either::Right(b) => EitherIter::Right(b.hinto_iter(arg))
        }
    }
}

impl<T, U, V, W> IntoIterator for PathEnd<T, U>
    where T: HigherIntoIterator<Item<U>, Item = W, IntoIter = V>,
          V: Iterator<Item = W>
{
    type Item = W;
    type IntoIter = V;
    fn into_iter(self) -> Self::IntoIter {
        self.0.hinto_iter(self.1)
    }
}

impl<T, U, W, I, W2, I2> IntoIterator for PathComp<T, U>
    where U: IntoIterator<Item = W, IntoIter = I>,
          T: Clone + HigherIntoIterator<Item<W>, Item = W2, IntoIter = I2>,
          I: Iterator<Item = W>,
          I2: Iterator<Item = W2>
{
    type Item = W2;
    type IntoIter = PathIter<I2, I, T>;
    fn into_iter(self) -> Self::IntoIter {
        let Path(a, b) = self;
        let in_iter = b.inner_right().into_iter();
        PathIter {
            in_iter,
            out_iter: vec![],
            out_ind: 0,
            arg: a
        }
    }
}

/// Iterates over a path composition, e.g. `[f] [g] a`.
pub struct PathIter<T, U, V> {
    out_iter: Vec<T>,
    in_iter: U,
    out_ind: usize,
    arg: V,
}

impl<T, U, V> Iterator for PathIter<T, U, V>
    where T: Iterator, U: Iterator, V: Clone,
          V: HigherIntoIterator<Item<U::Item>, Item = T::Item, IntoIter = T>
{
    type Item = T::Item;
    fn next(&mut self) -> Option<T::Item> {
        loop {
            while self.out_ind < self.out_iter.len() {
                let v = self.out_iter[self.out_ind].next();
                if v.is_some() {
                    self.out_ind += 1;
                    return v;
                } else {
                    self.out_iter.swap_remove(self.out_ind);
                }
            }

            if let Some(u) = self.in_iter.next() {
                self.out_iter.push(self.arg.clone().hinto_iter(item(u)));
            } else if self.out_iter.len() == 0 {
                return None;
            }

            self.out_ind = 0;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        assert_eq!(item(true).into_iter().next(), Some(true));
        assert_eq!(item(false).into_iter().next(), Some(false));
        assert_eq!(Path(Not, item(true)).into_iter().next(), Some(false));
        assert_eq!(Path(Not, item(false)).into_iter().next(), Some(true));
        assert_eq!(path(Not, Path(Not, item(true))).into_iter().next(), Some(true));
        assert_eq!(path(Not, Path(Not, item(false))).into_iter().next(), Some(false));
    }

    #[test]
    fn test_diag() {
        assert_eq!(diag_prod((0, 0), (0, 0)), (0, 0));
        assert_eq!(diag_prod((1, 1), (0, 0)), (0, 0));

        assert_eq!(diag_prod((0, 0), (1, 1)), (1, 1));
        assert_eq!(diag_prod((1, 0), (1, 1)), (1, 1));
        assert_eq!(diag_prod((0, 1), (1, 1)), (1, 1));

        assert_eq!(diag_prod((0, 0), (2, 2)), (0, 1));
        assert_eq!(diag_prod((0, 1), (2, 2)), (1, 0));
        assert_eq!(diag_prod((1, 0), (2, 2)), (1, 1));
        assert_eq!(diag_prod((1, 1), (2, 2)), (2, 2));

        assert_eq!(diag_prod((0, 0), (3, 3)), (0, 1));
        assert_eq!(diag_prod((0, 1), (3, 3)), (1, 0));
        assert_eq!(diag_prod((1, 0), (3, 3)), (0, 2));
        assert_eq!(diag_prod((0, 2), (3, 3)), (1, 1));
        assert_eq!(diag_prod((1, 1), (3, 3)), (2, 0));
        assert_eq!(diag_prod((2, 0), (3, 3)), (1, 2));
        assert_eq!(diag_prod((1, 2), (3, 3)), (2, 1));
        assert_eq!(diag_prod((2, 1), (3, 3)), (2, 2));
        assert_eq!(diag_prod((2, 2), (3, 3)), (3, 3));

        assert_eq!(diag_prod((3, 2), (4, 4)), (3, 3));

        assert_eq!(diag_prod((0, 0), (3, 1)), (1, 0));
        assert_eq!(diag_prod((0, 0), (1, 3)), (0, 1));
        assert_eq!(diag_prod((0, 1), (1, 6)), (0, 2));
    }

    #[test]
    fn test_product() {
        let mut x = path!([(Add, Add)] (0, 0)).into_iter();
        assert_eq!(x.next(), Some(((0, 0), (0, 0))));
        assert_eq!(x.next(), Some(((0, 0), (1, -1))));
        assert_eq!(x.next(), Some(((1, -1), (0, 0))));
        assert_eq!(x.next(), Some(((1, -1), (1, -1))));
        assert_eq!(x.next(), Some(((-1, 1), (0, 0))));
        assert_eq!(x.next(), Some(((1, -1), (-1, 1))));
        assert_eq!(x.next(), Some(((-1, 1), (1, -1))));

        let mut x = path!([(Add, Id)] (0, 0)).into_iter();
        assert_eq!(x.next(), Some(((0, 0), 0)));
        assert_eq!(x.next(), Some(((1, -1), 0)));
        assert_eq!(x.next(), Some(((-1, 1), 0)));
        assert_eq!(x.next(), Some(((2, -2), 0)));

        let mut x = path!([(Id, Add)] (0, 0)).into_iter();
        assert_eq!(x.next(), Some((0, (0, 0))));
        assert_eq!(x.next(), Some((0, (1, -1))));
        assert_eq!(x.next(), Some((0, (-1, 1))));
    }
}
