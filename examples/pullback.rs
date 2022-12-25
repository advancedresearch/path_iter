use path_iter::*;

fn main() {
    for a in pullback(And, Or) {
        // Prints:
        /*
        ((false, false), (false, false))
        ((false, true), (false, false))
        ((true, true), (false, true))
        ((true, false), (false, false))
        ((true, true), (true, false))
        ((true, true), (true, true))
        */
        println!("{:?}", a);
    }
}
