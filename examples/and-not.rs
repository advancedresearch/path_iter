use path_iter::*;

fn main() {
    for a in path!([And] [Not] true) {
        println!("{:?}", a);
    }
}
