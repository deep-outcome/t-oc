# t-oc
 - trie occurence counter is frequency dictionary that use any `impl Iterator<Item = char>` type as occurrent
 - since its flexibility it allows to count _apples_ with _pears_ without hassle


### basic usage

- only English alphabet letters are supported oob
- since `core::str::Chars` is `impl Iterator<Item = char>` type usage with `str` is oob

```rust
use t_oc::Toc;
use std::panic::catch_unwind;

let mut toc = Toc::new();
let occurrent = "true";

toc.ins(occurrent.chars());
toc.ins(true.to_string().chars());

assert_eq!(2, toc.acq(occurrent.chars()).unwrap());
toc.put(occurrent.chars(), 15);
assert_eq!(15, toc.acq(occurrent.chars()).unwrap());

let catch = catch_unwind(move|| toc.ins("#&%".chars()));
assert!(catch.is_err());
```

### custom alphabet implementation

- to use custom alphabet employ `Toc::new_with`
- provide it with functions for alphabet generation and index conversion
- see also example on `new_with`

```rust
use t_oc::{Toc, Alphabet, ab as ab_fn};

struct UsizeCharIterator {
    c: char,
    x: bool,
}

impl Iterator for UsizeCharIterator {
    type Item = char;

    fn next(&mut self) -> Option<char> {
        if self.x {
            self.x = false;
            Some(self.c)
        } else {
            None
        }
    }
}

impl UsizeCharIterator {
    fn new(n: usize) -> Self {
        let c = n.to_string().chars().next();
        let c = unsafe { c.unwrap_unchecked() };
        UsizeCharIterator { c, x: true }
    }
}

fn ix(c: char) -> usize {
    c.to_digit(10).unwrap() as usize
}

fn ab() -> Alphabet {
    ab_fn(10)
}

#[test]
fn test() {
    let nums = [1, 2, 2, 3, 3, 3, 7, 7, 7, 8, 8, 9];

    let mut toc = Toc::new_with(ix, ab);

    for n in nums {
        toc.ins(UsizeCharIterator::new(n));
    }

    assert_eq!(1, toc.acq(UsizeCharIterator::new(1)).unwrap());
    assert_eq!(2, toc.acq(UsizeCharIterator::new(2)).unwrap());
    assert_eq!(3, toc.acq(UsizeCharIterator::new(3)).unwrap());
    assert_eq!(3, toc.acq(UsizeCharIterator::new(7)).unwrap());
    assert_eq!(2, toc.acq(UsizeCharIterator::new(8)).unwrap());
    assert_eq!(1, toc.acq(UsizeCharIterator::new(9)).unwrap());
}
```
