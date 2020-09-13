# Path-Iter
A cocategory enumeration library based on path semantics

Implementation based on paper [Cocategory Enumeration](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip/cocategory-enumeration.pdf).

For an introduction to Path Semantics,
see [this paper](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip/introduction-to-path-semantics-for-computer-scientists.pdf).

### Sub-types in Path Semantics

In normal Path Semantics, one uses
[normal paths](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip/normal-paths.pdf)
in theorem proving.
Normal paths is a derivation from functions with sub-types.

This library focuses on sub-types, not on the more general case of normal paths.

A sub-type in Path Semantics is written in this form:

```text
x : [f] a
```

Where `x` is some input, `f` is a function and `a` is the output of `f`.

This library is for enumerating such sub-types efficiently.

### Example: AND

The `path!` macro is used to write in the standard notation of Path Semantics.
It constructs a type using `Path` that implements `IntoIterator`:

```rust
use path_iter::*;

fn main() {
    for a in path!([And] true) {
        // Prints `(true, true)`
        println!("{:?}", a);
    }
}
```

It prints `(true, true)` because that is the only input value to `And`
which produces `true` as output.

### Example: AND 2

You can decide the output value at runtime:

```rust
use path_iter::*;

fn main() {
    for &b in &[false, true] {
        for a in path!([And] b) {
            println!("{:?}", a);
        }
        println!("");
    }
}
```

This prints:

```text
(false, false)
(false, true)
(true, false)

(true, true)
```

### Example: AND-NOT

You can chain path sub-types together:

```rust
use path_iter::*;

fn main() {
    for a in path!([And] [Not] true) {
        println!("{:?}", a);
    }
}
```

### Example: Partial Application

Partial application is a technique where
a function reduces to another function
when calling it with fewer arguments than the signature.

For example, `And(true)` reduces to `Idb`.

```rust
use path_iter::*;

fn main() {
   for a in path!([And(true)] true) {
        println!("{:?}", a);
    }
}
```

This should not be confused with function currying,
which is extensionally equal to partial application,
but captures the underlying function in a closure.

The `path!` macro expands to partial application automatically, but it is very limited.
Outside the macro `path!` or for complex cases, one must use `PApp::papp`.

### Example: AND 3

The standard notation for composing paths is not very friendly with Rust macros.
Therefore, one can use a single bracket `[]` with functions separated by commas:

```rust
use path_iter::*;

fn main() {
    for a in path!([((And, And), (And, And)), (And, And), And] true) {
        println!("{:?}", a);
    }
}
```
