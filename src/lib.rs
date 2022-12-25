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
pub struct ProductIter<T, U, V, W> {
    inner: T,
    outer: U,
    outer_ty: V,
    inner_vals: Vec<W>,
    inner_ind: usize,
    over_diagonal: Option<usize>,
}

impl<T, U, V, W1, W2> Iterator for ProductIter<T, U, V, W1>
    where T: Iterator<Item = W1>,
          U: Iterator<Item = W2>,
          V: Clone + IntoIterator<Item = W2, IntoIter = U>,
          W1: Clone
{
    type Item = (W1, W2);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(max_len) = self.over_diagonal {
            if self.inner_vals.len() == 0 {return None};

            if self.inner_ind > 0 {
                let u = self.inner_vals[self.inner_ind - 1].clone();
                if let Some(v) = self.outer.next() {
                    self.inner_ind -= 1;
                    return Some((u.clone(), v));
                } else {
                    return None;
                }
            }

            // Remove one value.
            self.inner_vals.pop();
            self.inner_ind = self.inner_vals.len();
            self.outer = self.outer_ty.clone().into_iter();
            // Skip the first values.
            for _ in self.inner_ind..max_len {
                if self.outer.next().is_none() {return None}
            }
            return self.next();
        }

        if self.inner_ind > 0 {
            let u = self.inner_vals[self.inner_ind - 1].clone();
            if let Some(v) = self.outer.next() {
                self.inner_ind -= 1;
                return Some((u.clone(), v));
            }
        }

        self.outer = self.outer_ty.clone().into_iter();

        if let Some(val) = self.inner.next() {
            self.inner_vals.push(val);
        } else {
            self.over_diagonal = Some(self.inner_vals.len());
            self.inner_vals.reverse();
            self.inner_ind = 0;
            return self.next();
        }
        self.inner_ind = self.inner_vals.len();
        self.next()
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
    type IntoIter = ProductIter<I1, I2, PathEnd<T2, U2>, V1>;
    fn hinto_iter(self, arg: Item<(U1, U2)>) -> Self::IntoIter {
        let (u1, u2) = arg.inner();
        let (a, b) = self;
        let inner = a.hinto_iter(item(u1));
        let outer = b.clone().hinto_iter(item(u2.clone()));
        ProductIter {
            inner, inner_vals: vec![], outer, outer_ty: Path(b, item(u2)), inner_ind: 0,
            over_diagonal: None,
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
}
