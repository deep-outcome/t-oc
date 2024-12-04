# t-oc
 - trie occurrence counter is frequency dictionary that uses any `impl Iterator<Item = char>` type as occurrent
 - since its flexibility it allows to count _apples_ with _pears_ without hassle


### basic usage

- only English alphabet letters are supported oob
- since `core::str::Chars` is `impl Iterator<Item = char>` type usage with `str` is oob

```rust
use t_oc::Toc;
use std::panic::catch_unwind;

let mut toc = Toc::new();
let occurrent = "true";

_ = toc.ins(occurrent.chars(), None);
_ = toc.ins(true.to_string().chars(), None);

assert_eq!(2, toc.acq(occurrent.chars()).uproot());
toc.put(occurrent.chars(), 15);
assert_eq!(15, toc.acq(occurrent.chars()).uproot());

let catch = catch_unwind(move|| _ = toc.ins("#&%".chars(), None));
assert!(catch.is_err());
```

### custom alphabet implementation

- to use custom alphabet employ `Toc::new_with`
- provide it with function for index conversion and alphabet relevant length
- see also example on `new_with`

```rust
use t_oc::Toc;

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

#[test]
fn test() {
    let nums = [1, 2, 2, 3, 3, 3, 7, 7, 7, 8, 8, 9];

    let mut toc = Toc::new_with(ix, 10);

    for n in nums {
        _ = toc.ins(UsizeCharIterator::new(n), None);
    }

    assert_eq!(1, toc.acq(UsizeCharIterator::new(1)).uproot());
    assert_eq!(2, toc.acq(UsizeCharIterator::new(2)).uproot());
    assert_eq!(3, toc.acq(UsizeCharIterator::new(3)).uproot());
    assert_eq!(3, toc.acq(UsizeCharIterator::new(7)).uproot());
    assert_eq!(2, toc.acq(UsizeCharIterator::new(8)).uproot());
    assert_eq!(1, toc.acq(UsizeCharIterator::new(9)).uproot());
}
```
