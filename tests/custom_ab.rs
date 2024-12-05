use t_oc::Toc;

struct UsizeCharIterator {
    s: String,
    c: usize,
}

impl Iterator for UsizeCharIterator {
    type Item = char;

    fn next(&mut self) -> Option<char> {
        let c = self.c;

        let opt = self.s.chars().nth(c);

        if opt.is_some() {
            self.c = c + 1;
        }

        opt
    }
}

impl UsizeCharIterator {
    fn new(n: usize) -> Self {
        Self { s: n.to_string(), c: 0 }
    }
}

fn ix(c: char) -> usize {
    c.to_digit(10).unwrap() as usize
}

#[test]
fn test() {
    let nums = [0, 2, 2, 100, 100, 9999];

    let mut toc = Toc::new_with(ix, 10);

    for n in nums {
        _ = toc.ins(UsizeCharIterator::new(n), None);
    }

    assert_eq!(1, toc.acq(UsizeCharIterator::new(0)).uproot());
    assert_eq!(2, toc.acq(UsizeCharIterator::new(2)).uproot());
    assert_eq!(2, toc.acq(UsizeCharIterator::new(100)).uproot());
    assert_eq!(1, toc.acq(UsizeCharIterator::new(9999)).uproot());
}
