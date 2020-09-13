use crate::*;

/// Logical NOT.
#[derive(Clone)]
pub struct Not;

/// Logical AND.
#[derive(Clone)]
pub struct And;

/// Logical OR.
#[derive(Clone)]
pub struct Or;

/// Logical EQ.
#[derive(Clone)]
pub struct Eqb;

/// Logical XOR.
#[derive(Clone)]
pub struct Xor;

/// A boolean unary function that returns `false`.
#[derive(Clone)]
pub struct False1;

/// A boolean unary function that returns `true`.
#[derive(Clone)]
pub struct True1;

/// Returns the argument of a boolean unary function.
#[derive(Clone)]
pub struct Idb;

/// Returns the first argument of a boolean binary function.
#[derive(Clone)]
pub struct Fstb;

/// Returns the second argument of a boolean binary function.
#[derive(Clone)]
pub struct Sndb;

impl PApp for And {
    type Arg = bool;
    type Ret = Either<Idb, False1>;
    fn papp(self, b: bool) -> Self::Ret {
        if b {Either::Left(Idb)}
        else {Either::Right(False1)}
    }
}

impl PApp for Or {
    type Arg = bool;
    type Ret = Either<True1, Idb>;
    fn papp(self, b: bool) -> Self::Ret {
        if b {Either::Left(True1)}
        else {Either::Right(Idb)}
    }
}

impl PApp for Xor {
    type Arg = bool;
    type Ret = Either<Not, Idb>;
    fn papp(self, b: bool) -> Self::Ret {
        if b {Either::Left(Not)}
        else {Either::Right(Idb)}
    }
}

impl PApp for Eqb {
    type Arg = bool;
    type Ret = Either<Idb, Not>;
    fn papp(self, b: bool) -> Self::Ret {
        if b {Either::Left(Idb)}
        else {Either::Right(Not)}
    }
}

impl PApp for Fstb {
    type Arg = bool;
    type Ret = Item<bool>;
    fn papp(self, b: bool) -> Self::Ret {Item(b)}
}

impl PApp for Sndb {
    type Arg = bool;
    type Ret = Idb;
    fn papp(self, _: bool) -> Self::Ret {Idb}
}

impl IntoIterator for Item<bool> {
    type Item = bool;
    type IntoIter = <Option<bool> as IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        Some(self.0).into_iter()
    }
}

impl HigherIntoIterator<Item<bool>> for False1 {
    type Item = bool;
    type IntoIter = std::vec::IntoIter<bool>;
    fn hinto_iter(self, Item(arg): Item<bool>) -> Self::IntoIter {
        match arg {
            false => vec![false, true].into_iter(),
            true => vec![].into_iter()
        }
    }
}

impl HigherIntoIterator<Item<bool>> for True1 {
    type Item = bool;
    type IntoIter = std::vec::IntoIter<bool>;
    fn hinto_iter(self, Item(arg): Item<bool>) -> Self::IntoIter {
        False1.hinto_iter(Item(!arg))
    }
}

impl HigherIntoIterator<Item<bool>> for Idb {
    type Item = bool;
    type IntoIter = <Option<bool> as IntoIterator>::IntoIter;
    fn hinto_iter(self, arg: Item<bool>) -> Self::IntoIter {
        arg.into_iter()
    }
}

impl HigherIntoIterator<Item<bool>> for Not {
    type Item = bool;
    type IntoIter = <Option<bool> as IntoIterator>::IntoIter;
    fn hinto_iter(self, Item(arg): Item<bool>) -> Self::IntoIter {
        Item(!arg).into_iter()
    }
}

impl HigherIntoIterator<Item<bool>> for And {
    type Item = (bool, bool);
    type IntoIter = std::vec::IntoIter<(bool, bool)>;
    fn hinto_iter(self, Item(arg): Item<bool>) -> Self::IntoIter {
        match arg {
            false => vec![
                (false, false),
                (false, true),
                (true, false)
            ].into_iter(),
            true => vec![
                (true, true)
            ].into_iter()
        }
    }
}

impl HigherIntoIterator<Item<bool>> for Or {
    type Item = (bool, bool);
    type IntoIter = std::vec::IntoIter<(bool, bool)>;
    fn hinto_iter(self, Item(arg): Item<bool>) -> Self::IntoIter {
        match arg {
            false => vec![
                (false, false),
            ].into_iter(),
            true => vec![
                (false, true),
                (true, false),
                (true, true),
            ].into_iter()
        }
    }
}

impl HigherIntoIterator<Item<bool>> for Eqb {
    type Item = (bool, bool);
    type IntoIter = std::vec::IntoIter<(bool, bool)>;
    fn hinto_iter(self, Item(arg): Item<bool>) -> Self::IntoIter {
        match arg {
            false => vec![
                (false, true),
                (true, false)
            ].into_iter(),
            true => vec![
                (false, false),
                (true, true)
            ].into_iter()
        }
    }
}

impl HigherIntoIterator<Item<bool>> for Xor {
    type Item = (bool, bool);
    type IntoIter = std::vec::IntoIter<(bool, bool)>;
    fn hinto_iter(self, Item(arg): Item<bool>) -> Self::IntoIter {
        Eqb.hinto_iter(Item(!arg))
    }
}

impl HigherIntoIterator<Item<bool>> for Fstb {
    type Item = (bool, bool);
    type IntoIter = std::vec::IntoIter<(bool, bool)>;
    fn hinto_iter(self, Item(arg): Item<bool>) -> Self::IntoIter {
        match arg {
            false => vec![
                (false, false),
                (false, true)
            ].into_iter(),
            true => vec![
                (true, false),
                (true, true)
            ].into_iter()
        }
    }
}

impl HigherIntoIterator<Item<bool>> for Sndb {
    type Item = (bool, bool);
    type IntoIter = std::vec::IntoIter<(bool, bool)>;
    fn hinto_iter(self, Item(arg): Item<bool>) -> Self::IntoIter {
        match arg {
            false => vec![
                (false, false),
                (true, false)
            ].into_iter(),
            true => vec![
                (false, true),
                (true, false)
            ].into_iter()
        }
    }
}
