use path_iter::*;

fn main() {
    for a in path!([And] true) {
        // Prints `(true, true)`
        println!("{:?}", a);
    }
}
