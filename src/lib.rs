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
        Path(crate::PApp::papp($x, $y), path!($([$($z)*])+ $w))
    };
    ([$x0:expr , $($x:expr),+ $(,)?] $z:expr) => {
        Path($x0, path!([$($x),*] $z))
    };
    ([$x:expr] [$x1:expr] [$x2:expr] [$x3:expr] [$x4:expr] [$x5:expr] [$x6:expr] $z:expr) => {
        Path($x, path!([$x1] [$x2] [$x3] [$x4] [$x5] [$x6] Item($z)))
    };
    ([$x:expr] [$x1:expr] [$x2:expr] [$x3:expr] [$x4:expr] [$x5:expr] $z:expr) => {
        Path($x, path!([$x1] [$x2] [$x3] [$x4] [$x5] Item($z)))
    };
    ([$x:expr] [$x1:expr] [$x2:expr] [$x3:expr] [$x4:expr] $z:expr) => {
        Path($x, path!([$x1] [$x2] [$x3] [$x4] Item($z)))
    };
    ([$x:expr] [$x1:expr] [$x2:expr] [$x3:expr] $z:expr) => {
        Path($x, path!([$x1] [$x2] [$x3] Item($z)))
    };
    ([$x:expr] [$x1:expr] [$x2:expr] $z:expr) => {
        Path($x, path!([$x1] [$x2] Item($z)))
    };
    ([$x:expr] [$y:expr] $z:expr) => {
        Path($x, path!([$y] $z))
    };
    ([$x:ident ($y:expr)] $z:expr) => {
        Path(crate::PApp::papp($x, $y), Item($z))
    };
    ([$x:expr] $y:expr) => {
        Path($x, Item($y))
    };
);

/// Used to wrap value types to avoid impl collisions.
#[derive(Clone)]
pub struct Item<T>(pub T);

/// Stores a path sub-type `[T] U`.
#[derive(Clone)]
pub struct Path<T, U>(pub T, pub U);

impl<T> From<Item<T>> for Item<Item<T>> {
    fn from(val: Item<T>) -> Self {Item(val)}
}

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
    inner_val: Option<W>,
}

impl<T, U, V, W1, W2> Iterator for ProductIter<T, U, V, W1>
    where T: Iterator<Item = W1>,
          U: Iterator<Item = W2>,
          V: Clone + IntoIterator<Item = W2, IntoIter = U>,
          W1: Clone
{
    type Item = (W1, W2);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(u) = &self.inner_val {
            if let Some(v) = self.outer.next() {
                Some((u.clone(), v))
            } else {
                self.inner_val = self.inner.next();
                self.outer = self.outer_ty.clone().into_iter();
                self.next()
            }
        } else {
            None
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

impl<T, U1, U2> HigherIntoIterator<Item<(U1, U2)>> for T
    where T: HigherIntoIterator<(Item<U1>, Item<U2>)>
{
    type Item = T::Item;
    type IntoIter = T::IntoIter;
    fn hinto_iter(self, Item((a, b)): Item<(U1, U2)>) -> Self::IntoIter {
        self.hinto_iter((Item(a), Item(b)))
    }
}

impl<T1, T2, U1, U2, V1, V2, I1, I2> HigherIntoIterator<(Item<U1>, Item<U2>)> for (T1, T2)
    where T1: HigherIntoIterator<Item<U1>, Item = V1, IntoIter = I1>,
          T2: Clone + HigherIntoIterator<Item<U2>, Item = V2, IntoIter = I2>,
          I1: Iterator<Item = V1>,
          Item<U2>: Clone
{
    type Item = (V1, V2);
    type IntoIter = ProductIter<I1, I2, Path<T2, Item<U2>>, V1>;
    fn hinto_iter(self, (u1, u2): (Item<U1>, Item<U2>)) -> Self::IntoIter {
        let (a, b) = self;
        let mut inner = a.hinto_iter(u1);
        let inner_val = inner.next();
        let outer = b.clone().hinto_iter(u2.clone());
        ProductIter {
            inner, inner_val, outer, outer_ty: Path(b, u2)
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

impl<T, U, V, W> IntoIterator for Path<T, U>
    where T: HigherIntoIterator<U, Item = W, IntoIter = V>,
          V: Iterator<Item = W>
{
    type Item = W;
    type IntoIter = V;
    fn into_iter(self) -> Self::IntoIter {
        self.0.hinto_iter(self.1)
    }
}

/// Function composition.
///
/// For example, `Comp(Not, Not)` is the same as `Idb`.
#[derive(Clone)]
pub struct Comp<T, U>(pub T, pub U);

impl<T, U, V, W, W2, I1, I2> HigherIntoIterator<Item<V>> for Comp<T, U>
    where U: HigherIntoIterator<V, Item = W, IntoIter = I1>,
          T: Clone + HigherIntoIterator<Item<W>, Item = W2, IntoIter = I2>,
          I1: Iterator<Item = W>,
          I2: Iterator<Item = W2>
{
    type Item = W2;
    type IntoIter = PathIter<I2, I1, T>;
    fn hinto_iter(self, Item(arg): Item<V>) -> Self::IntoIter {
        let Comp(a, b) = self;
        let mut in_iter = b.hinto_iter(arg);
        let out_iter = in_iter.next().map(|u| a.clone().hinto_iter(Item(u)));
        PathIter {
            in_iter,
            out_iter,
            arg: a
        }
    }
}

impl<T, U, V, W, I> HigherIntoIterator<Path<U, V>> for T
    where Comp<T, U>: HigherIntoIterator<Item<V>, Item = W, IntoIter = I>
{
    type Item = W;
    type IntoIter = I;
    fn hinto_iter(self, Path(a, b): Path<U, V>) -> Self::IntoIter {
        Comp(self, a).hinto_iter(Item(b))
    }
}

/// Iterates over a path composition, e.g. `[f] [g] a`.
pub struct PathIter<T, U, V> {
    out_iter: Option<T>,
    in_iter: U,
    arg: V,
}

impl<T, U, V> Iterator for PathIter<T, U, V>
    where T: Iterator, U: Iterator, V: Clone,
          Path<V, Item<U::Item>>: IntoIterator<Item = T::Item, IntoIter = T>
{
    type Item = T::Item;
    fn next(&mut self) -> Option<T::Item> {
        loop {
            if let Some(out_iter) = &mut self.out_iter {
                let v = out_iter.next();
                if v.is_some() {
                    return v;
                }
                if let Some(u) = self.in_iter.next() {
                    *out_iter = Path(self.arg.clone(), Item(u)).into_iter();
                } else {
                    return None;
                }
            } else {
                return None;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        assert_eq!(Item(true).into_iter().next(), Some(true));
        assert_eq!(Item(false).into_iter().next(), Some(false));
        assert_eq!(Path(Not, Item(true)).into_iter().next(), Some(false));
        assert_eq!(Path(Not, Item(false)).into_iter().next(), Some(true));
        assert_eq!(Path(Not, Path(Not, Item(true))).into_iter().next(), Some(true));
        assert_eq!(Path(Not, Path(Not, Item(false))).into_iter().next(), Some(false));
    }
}
