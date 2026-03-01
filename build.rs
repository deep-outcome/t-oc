use std::fs::copy;
use std::path::Path;

fn main() {
    uc();
}

fn uc() {
    _ = std::fs::create_dir("./src/uc");

    let src = "../rust-helpers/src/uc.rs";
    let dst = "./src/uc/mod.rs";

    let src = Path::new(src);
    let dst = Path::new(dst);
    _ = copy(src, dst);
}
