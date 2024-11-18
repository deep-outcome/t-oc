//! Trie Occurrence Counter is frequency dictionary that uses any `impl Iterator<Item = char>` type as occurrent.
//!
//! Support for English letters A–Za–z OOB.

use std::vec::Vec;
use crate::english_letters::ALPHABET_LEN;

/// `Letter` is `Alphabet` element, represents tree node.
#[cfg_attr(test, derive(PartialEq))]
pub struct Letter {
    #[cfg(test)]
    val: char,
    ab: Option<Alphabet>,
    ct: Option<usize>,
}

impl Letter {
    fn new() -> Self {
        Letter {
            #[cfg(test)]
            val: '💚',
            ab: None,
            ct: None,
        }
    }

    fn ab(&self) -> bool {
        self.ab.is_some()
    }

    fn ct(&self) -> bool {
        self.ct.is_some()
    }
}

/// Tree node arms. Consists of `Letter`s.
pub type Alphabet = Box<[Letter]>;
/// Index conversion function. Tighten with `Alphabet`.
/// Returns corresponding `usize`d index of `char`.
///
/// For details see `english_letters::ix` implementation.
pub type Ix = fn(char) -> usize;
/// Alphabet function. Constructs alphabet that supports chosen `char`s.
///
/// Not all arms necessarily have to logically exists.
///
/// For details see `english_letters::ab` implementation.
pub type Ab = fn() -> Alphabet;

/// Alphabet function, tree arms generation of length specified.
pub fn ab(len: usize) -> Alphabet {
    let mut ab = Vec::new();
    ab.reserve_exact(len);

    #[cfg(test)]
    #[cfg(feature = "test-ext")]
    let mut c = 'A' as u8;

    for sc in ab.spare_capacity_mut() {
        let mut _letter = sc.write(Letter::new());

        #[cfg(test)]
        #[cfg(feature = "test-ext")]
        {
            _letter.val = c as char;

            if c == 'Z' as u8 {
                c = 'a' as u8;
            } else {
                c = c + 1;
            }
        }
    }

    unsafe { ab.set_len(len) };

    ab.into_boxed_slice()
}

/// Module contains functions for working with English alphabet letters, A-Za-z.
///
/// For details see `Toc::new_with()`.
pub mod english_letters {

    use crate::{ab as ab_fn, Alphabet};

    /// 26
    pub const BASE_ALPHABET_LEN: usize = 26;
    /// 52
    pub const ALPHABET_LEN: usize = BASE_ALPHABET_LEN * 2;

    /// `Alphabet` of English capital and small letters length.
    pub fn ab() -> Alphabet {
        ab_fn(ALPHABET_LEN)
    }

    /// Index conversion function.
    pub const fn ix(c: char) -> usize {
        let code_point = c as usize;

        const A: usize = 'A' as usize;
        #[allow(non_upper_case_globals)]
        const a: usize = 'a' as usize;

        match code_point {
            | c if c > 64 && c < 91 => c - A,
            | c if c > 96 && c < 123 => c - a + BASE_ALPHABET_LEN,
            | _ => panic!("Unsupported char. Cannot convert to index."),
        }
    }
}

///  Insertion result enumeration.
#[derive(Debug)]
#[derive(PartialEq, Eq)]
pub enum InsRes {
    /// Insertion accomplished.
    Ok,
    /// Attempt to insert zero occurrent.
    ZeroLen,
}

/// Versatile result enumeration.
///
/// Used by various methods in versatile way.
#[derive(Debug)]
#[derive(PartialEq, Eq)]
pub enum VerRes {
    /// Operation accomplished.
    Ok(usize),
    /// Zero occurrent usage.
    ZeroLen,
    /// Unknown occurrent usage.
    Unknown,
}

impl VerRes {
    /// Returns `true` for `VerRes::Ok(_)`.
    pub const fn is_ok(&self) -> bool {
        match self {
            | VerRes::Ok(_) => true,
            | _ => false,
        }
    }

    /// Returns `usize` of `VerRes::Ok(usize)` or _panics_ if not that variant.
    pub const fn unwrap(&self) -> usize {
        match self {
            | VerRes::Ok(res) => *res,
            | _ => panic!("Value is not `Ok(usize)` variant."),
        }
    }

    /// Returns `usize` of `VerRes::Ok(usize)` and does not _panic_ if not that variant (UB).
    ///
    /// Check with `std::hint::unreachable_unchecked` for more information.
    pub const unsafe fn unwrap_unchecked(&self) -> usize {
        match self {
            | VerRes::Ok(res) => *res,
            // SAFETY: the safety contract must be upheld by the caller.
            | _ => unsafe { std::hint::unreachable_unchecked() },
        }
    }
}

#[cfg_attr(test, derive(PartialEq, Debug))]
enum TraRes<'a> {
    Ok(&'a Letter),
    OkMut(&'a mut Letter),
    ZeroLen,
    UnknownForNotEntry,
    UnknownForAbsentPath,
}

impl<'a> TraRes<'a> {
    fn ver_res(&self) -> VerRes {
        return match self {
            | TraRes::ZeroLen => VerRes::ZeroLen,
            | TraRes::UnknownForNotEntry | TraRes::UnknownForAbsentPath => VerRes::Unknown,
            | TraRes::Ok(l) => ok(l),
            | TraRes::OkMut(l) => ok(l),
        };

        fn ok(l: &Letter) -> VerRes {
            VerRes::Ok(l.ct.unwrap())
        }
    }
}

/// Trie Occurrence Counter is frequency dictionary that uses any `impl Iterator<Item = char>` type as occurrent.
///
/// OOB English letters A–Za–z support only.
///
/// ```
/// use t_oc::Toc;
/// use std::panic::catch_unwind;
///
/// let mut toc = Toc::new();
/// let occurrent = "true";
///
/// toc.ins(occurrent.chars(), None);
/// toc.ins(true.to_string().chars(), None);
///
/// assert_eq!(2, toc.acq(occurrent.chars()).unwrap());
/// toc.put(occurrent.chars(), 15);
/// assert_eq!(15, toc.acq(occurrent.chars()).unwrap());
///
/// let catch = catch_unwind(move|| toc.ins("#&%".chars(), None));
/// assert!(catch.is_err());
/// ```
///
/// When asymptotic computational complexity is not explicitly specified , it is:
/// - TC: Θ(s) where s is count of `char`s iterated over.
/// - SC: Θ(0)
pub struct Toc {
    // tree root
    rt: Alphabet,
    // index fn
    ix: Ix,
    // alphabet fn
    ab: Ab,
    // backtrace buff
    tr: Vec<*mut Letter>,
}

impl Toc {
    /// Constructs default version of `Toc`, i.e. via
    /// `fn new_with()` with `english_letters::ab` and `english_letters::ix`.
    pub fn new() -> Self {
        Self::new_with(english_letters::ix, english_letters::ab)
    }

    /// Allows to use custom alphabet different from default alphabet.
    ///
    /// ```
    /// use t_oc::{ab as ab_fn, Alphabet, Toc};
    ///
    /// fn ab() -> Alphabet {
    ///     ab_fn(2)
    /// }
    /// fn ix(c: char) -> usize {
    ///     match c {
    ///         '&' => 0,
    ///         '|' => 1,
    ///         _ => panic!(),
    ///     }
    /// }
    ///
    /// let mut toc = Toc::new_with(ix, ab);
    /// let a = "&";
    /// let b = "|";
    /// let aba = "&|&";
    /// toc.ins(a.chars(), None);
    /// toc.ins(a.chars(), None);
    /// toc.ins(b.chars(), None);
    /// toc.ins(aba.chars(), None);
    /// assert_eq!(2, toc.acq(a.chars()).unwrap());
    /// assert_eq!(1, toc.acq(aba.chars()).unwrap());
    pub fn new_with(ix: Ix, ab: Ab) -> Self {
        Self {
            rt: ab(),
            ix,
            ab,
            tr: Vec::new(),
        }
    }

    /// `Toc` uses internal buffer, to avoid excesive allocations and copying, which grows
    /// over time due backtracing in `rem` method which backtraces whole path from entry
    /// node to root node.
    ///
    /// Use this method to shrink or extend it to fit actual program needs. Neither shrinking nor extending
    /// is guaranteed to be exact. See `Vec::with_capacity()` and `Vec::reserve()`. For optimal `rem` performance, set `approx_cap` to, at least, `occurrent.count()`.
    ///
    /// Some high value is sufficient anyway. Since buffer continuous
    /// usage, its capacity will likely expand at some point in time to size sufficient to all occurrents.
    ///
    /// Return value is actual buffer capacity.
    ///
    /// **Note:** While `String` is UTF8 encoded, its byte length does not have to equal its `char` count
    /// which is either equal or lesser.
    /// ```
    /// let sights = "🤩";
    /// assert_eq!(4, sights.len());
    /// assert_eq!(1, sights.chars().count());
    ///
    /// let yes = "sí";
    /// assert_eq!(3, yes.len());
    /// assert_eq!(2, yes.chars().nth(1).unwrap().len_utf8());
    ///
    /// let abc = "abc";
    /// assert_eq!(3, abc.len());
    /// ```
    pub fn put_trace_cap(&mut self, approx_cap: usize) -> usize {
        let tr = &mut self.tr;
        let cp = tr.capacity();

        if cp < approx_cap {
            tr.reserve(approx_cap);
        } else if cp > approx_cap {
            *tr = Vec::with_capacity(approx_cap);
        }

        tr.capacity()
    }

    /// Return value is internal backtracing buffer capacity.
    ///
    /// Check with `fn put_trace_cap` for details.
    pub fn acq_trace_cap(&self) -> usize {
        self.tr.capacity()
    }

    /// Counter is of word size. Add overflow is wrapped using `wrapping_add`.
    ///
    /// Optional `val` parameter can be used to insert exact value.
    ///
    /// Return value is `InsRes::Ok` for non-zero `occurrent`.
    ///
    /// - SC: Θ(q) where q is number of unique nodes, i.e. `char`s in respective branches.
    pub fn ins(&mut self, mut occurrent: impl Iterator<Item = char>, val: Option<usize>) -> InsRes {
        let c = occurrent.next();

        if c.is_none() {
            return InsRes::ZeroLen;
        }

        let c = unsafe { c.unwrap_unchecked() };

        let ix = self.ix;
        let ab = self.ab;

        let mut letter = &mut self.rt[ix(c)];

        while let Some(c) = occurrent.next() {
            let alphabet = letter.ab.get_or_insert_with(|| ab());
            letter = &mut alphabet[ix(c)];
        }

        let ct = letter.ct.get_or_insert(0);

        *ct = if let Some(v) = val { v } else { ct.wrapping_add(1) };

        InsRes::Ok
    }

    /// Used to acquire value for `occurrent`.
    ///
    /// If `VerRes::Ok(usize)`, `usize` is `occurrent` occurrences count.
    pub fn acq(&self, occurrent: impl Iterator<Item = char>) -> VerRes {
        let this = unsafe { self.as_mut() };

        let track_res = this.track(occurrent, false, false);
        if let TraRes::Ok(l) = track_res {
            let ct = l.ct;
            let ct = unsafe { ct.unwrap_unchecked() };
            VerRes::Ok(ct)
        } else {
            track_res.ver_res()
        }
    }

    unsafe fn as_mut(&self) -> &mut Self {
        let ptr: *const Self = self;
        let mut_ptr: *mut Self = core::mem::transmute(ptr);
        mut_ptr.as_mut().unwrap()
    }

    /// Used to put new value for `occurrent` occurrences.
    ///
    /// If `VerRes::Ok(usize)`, `usize` is previous value.    
    pub fn put(&mut self, occurrent: impl Iterator<Item = char>, val: usize) -> VerRes {
        let track_res = self.track(occurrent, false, true);

        if let TraRes::OkMut(l) = track_res {
            let old = l.ct.replace(val);
            let old = unsafe { old.unwrap_unchecked() };
            VerRes::Ok(old)
        } else {
            track_res.ver_res()
        }
    }

    /// Used to remove `occurrent` from tree.
    ///
    /// If `VerRes::Ok(usize)`, `usize` is `occurrent` occurrences count.
    ///
    /// - s is count of `char`s iterated over.
    /// - TC: Ω(s) or ϴ(s) (backtracing buffer capacity dependent complexity)
    /// - SC: ϴ(s)
    ///
    /// Check with `put_trace_cap` for details on backtracing.
    pub fn rem(&mut self, occurrent: impl Iterator<Item = char>) -> VerRes {
        let track_res = self.track(occurrent, true, false);
        let res = if let TraRes::Ok(_) = track_res {
            let ct = Self::rem_actual(&mut self.tr);
            VerRes::Ok(ct)
        } else {
            track_res.ver_res()
        };

        self.tr.clear();
        res
    }

    fn rem_actual(tr: &mut Vec<*mut Letter>) -> usize {
        let mut trace = tr.iter_mut().map(|x| unsafe { x.as_mut() }.unwrap());
        let entry = trace.next_back().unwrap();

        let ct = entry.ct;
        let ct = unsafe { ct.unwrap_unchecked() };
        entry.ct = None;

        if !entry.ab() {
            while let Some(l) = trace.next_back() {
                let alphabet = l.ab.as_ref().unwrap();
                let mut remove_alphab = true;

                for ix in 0..ALPHABET_LEN {
                    let letter = &alphabet[ix];

                    if letter.ab() || letter.ct() {
                        remove_alphab = false;
                        break;
                    }
                }

                if remove_alphab {
                    l.ab = None;
                } else {
                    break;
                }

                if l.ct() {
                    break;
                }
            }
        }

        ct
    }

    // - s is count of `char`s iterated over.
    // - TC: Ω(s) when `tracing = true`, ϴ(s) otherwise
    // - SC: ϴ(s) when `tracing = true`, ϴ(0) otherwise
    fn track(
        &mut self,
        mut occurrent: impl Iterator<Item = char>,
        tracing: bool,
        okmut: bool,
    ) -> TraRes {
        let c = occurrent.next();

        if c.is_none() {
            return TraRes::ZeroLen;
        }

        let c = unsafe { c.unwrap_unchecked() };

        let ix = &self.ix;
        let tr = &mut self.tr;

        let mut letter = &mut self.rt[ix(c)];

        loop {
            if tracing {
                tr.push(letter)
            }

            if let Some(c) = occurrent.next() {
                if let Some(ab) = letter.ab.as_mut() {
                    letter = &mut ab[ix(c)];
                } else {
                    return TraRes::UnknownForAbsentPath;
                }
            } else {
                break;
            }
        }

        if letter.ct() {
            if okmut {
                TraRes::OkMut(letter)
            } else {
                TraRes::Ok(letter)
            }
        } else {
            TraRes::UnknownForNotEntry
        }
    }
}

#[cfg(test)]
mod tests_of_units {

    use crate::Letter;
    use std::fmt::{Debug, Formatter};

    impl Debug for Letter {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            let ab = some_none(self.ab.as_ref());

            return f.write_fmt(format_args!(
                "Letter {{\n  val: {}\n  ab: {}\n  ct: {:?}\n}}",
                self.val, ab, self.ct
            ));

            fn some_none<T>(val: Option<&T>) -> &'static str {
                if val.is_some() {
                    "Some"
                } else {
                    "None"
                }
            }
        }
    }

    mod letter {

        use crate::Letter;
        use crate::english_letters::ab as ab_fn;

        #[test]
        fn new() {
            let letter = Letter::new();

            assert_eq!('💚', letter.val);
            assert!(letter.ab.is_none());
            assert!(letter.ct.is_none());
        }

        #[test]
        fn ab() {
            let mut letter = Letter::new();
            letter.ab = Some(ab_fn());
            assert_eq!(true, letter.ab());
        }

        #[test]
        fn ct() {
            let mut letter = Letter::new();
            letter.ct = Some(0);
            assert_eq!(true, letter.ct());
        }
    }

    mod ab {

        use crate::english_letters::ALPHABET_LEN;
        use crate::ab as ab_fn;

        #[test]
        fn ab() {
            let ab = ab_fn(ALPHABET_LEN);
            assert_eq!(ALPHABET_LEN, ab.len());

            #[cfg(feature = "test-ext")]
            {
                let chain = ('A'..='Z').chain('a'..='z');

                for (ix, c) in chain.enumerate() {
                    let letter = &ab[ix];

                    assert_eq!(c, letter.val);
                    assert!(letter.ab.is_none());
                    assert!(letter.ct.is_none());
                }
            }
        }

        #[test]
        fn zero_len() {
            let ab = ab_fn(0);
            assert_eq!(0, ab.len());
        }
    }

    mod english_letters {
        use crate::english_letters::{ab as ab_fn, ALPHABET_LEN, BASE_ALPHABET_LEN};

        #[test]
        fn consts() {
            assert_eq!(26, BASE_ALPHABET_LEN);
            assert_eq!(52, ALPHABET_LEN);
        }

        #[test]
        fn ab() {
            let ab = ab_fn();
            assert_eq!(ALPHABET_LEN, ab.len());
        }

        mod ix {
            use crate::english_letters::ix;
            use std::panic::catch_unwind;

            #[test]
            fn ixes() {
                assert_eq!(0, ix('A'));
                assert_eq!(25, ix('Z'));
                assert_eq!(26, ix('a'));
                assert_eq!(51, ix('z'));
            }

            #[test]
            fn unsupported_char() {
                let ucs = unsupported_chars();

                for c in ucs {
                    let result = catch_unwind(|| ix(c));
                    assert!(result.is_err());

                    let err = result.err();
                    let err = unsafe { err.unwrap_unchecked() };
                    let downcast = err.downcast_ref::<&str>().unwrap();
                    assert_eq!(&"Unsupported char. Cannot convert to index.", downcast);
                }
            }

            fn unsupported_chars() -> [char; 4] {
                #[rustfmt::skip] let ucs =
                [
                    'A' as u8 -1, 'Z' as u8 +1, // 65–90
                    'a' as u8 -1, 'z' as u8 +1, // 97–122
                ];

                ucs.map(|x| x as char)
            }
        }
    }

    mod ver_res {
        use crate::VerRes;

        #[test]
        fn is_ok() {
            assert_eq!(true, VerRes::Ok(0).is_ok());
            assert_eq!(false, VerRes::Unknown.is_ok());
            assert_eq!(false, VerRes::ZeroLen.is_ok());
        }

        #[test]
        fn unwrap() {
            assert_eq!(33, VerRes::Ok(33).unwrap());
        }

        #[test]
        #[should_panic(expected = "Value is not `Ok(usize)` variant.")]
        fn unwrap_panic() {
            VerRes::ZeroLen.unwrap();
        }

        #[test]
        fn unwrap_unchecked() {
            const VAL: usize = 77;
            let test = unsafe { VerRes::Ok(VAL).unwrap_unchecked() };
            assert_eq!(VAL, test);
        }
    }

    mod track_res {
        use crate::{TraRes, Letter, VerRes};

        #[test]
        fn ver_res() {
            const VAL: usize = 9;

            let mut letter = Letter::new();
            letter.ct = Some(VAL);
            assert_eq!(VerRes::Ok(VAL), TraRes::Ok(&letter).ver_res());
            assert_eq!(VerRes::Ok(VAL), TraRes::OkMut(&mut letter).ver_res());
            assert_eq!(VerRes::ZeroLen, TraRes::ZeroLen.ver_res());
            assert_eq!(VerRes::Unknown, TraRes::UnknownForAbsentPath.ver_res());
            assert_eq!(VerRes::Unknown, TraRes::UnknownForNotEntry.ver_res());
        }
    }

    mod toc {
        use crate::{Toc, Letter};
        use crate::english_letters::{ix, ab};

        #[test]
        fn new() {
            let toc = Toc::new();
            assert_eq!(ab(), toc.rt);
            assert_eq!(ab as usize, toc.ab as usize);
            assert_eq!(ix as usize, toc.ix as usize);
        }

        #[test]
        fn new_with() {
            fn test_ix(_c: char) -> usize {
                0
            }
            fn test_ab() -> Box<[Letter]> {
                let mut ab = Vec::new();
                ab.push(Letter::new());
                ab.into_boxed_slice()
            }

            let toc = Toc::new_with(test_ix, test_ab);

            assert_eq!(test_ab(), toc.rt);
            assert_eq!(test_ab as usize, toc.ab as usize);
            assert_eq!(test_ix as usize, toc.ix as usize);
            assert_eq!(0, toc.tr.capacity());
        }

        mod put_trace_cap {
            use crate::Toc;

            #[test]
            fn extend() {
                const NEW_CAP: usize = 10;

                let mut toc = Toc::new();
                assert!(toc.tr.capacity() < NEW_CAP);

                let size = toc.put_trace_cap(NEW_CAP);
                assert!(size >= NEW_CAP);
                assert!(toc.tr.capacity() >= NEW_CAP);
            }

            #[test]
            fn shrink() {
                const NEW_CAP: usize = 10;
                const OLD_CAP: usize = 50;

                let mut toc = Toc::new();
                toc.tr = Vec::with_capacity(OLD_CAP);

                let size = toc.put_trace_cap(NEW_CAP);
                assert!(size >= NEW_CAP && size < OLD_CAP);
                let cap = toc.tr.capacity();
                assert!(cap >= NEW_CAP && cap < OLD_CAP);
            }

            #[test]
            fn same() {
                let mut toc = Toc::new();
                let cap = toc.tr.capacity();

                let size = toc.put_trace_cap(cap);
                assert_eq!(cap, size);
                assert_eq!(cap, toc.tr.capacity());
            }
        }

        #[test]
        fn acq_trace_cap() {
            const VAL: usize = 10;

            let mut toc = Toc::new();
            let tr = &mut toc.tr;

            assert!(tr.capacity() < VAL);
            tr.reserve_exact(VAL);
            assert_eq!(VAL, toc.acq_trace_cap());
        }

        mod ins {
            use crate::{Toc, InsRes};
            use crate::english_letters::ix;

            #[test]
            fn basic_test() {
                let entry = || "impreciseness".chars();

                let mut toc = Toc::new();
                assert_eq!(InsRes::Ok, toc.ins(entry(), None));

                let chars: Vec<char> = entry().collect();
                let len = chars.len();
                let last_ix = len - 1;

                let mut sup_ab = &toc.rt;
                for c_ix in 0..len {
                    let c = chars[c_ix];
                    let l = &sup_ab[ix(c)];

                    let terminal_it = c_ix == last_ix;

                    let sub_ab = l.ab.as_ref();
                    assert_eq!(terminal_it, sub_ab.is_none(), "{c_ix}, {c}, {terminal_it}",);

                    if terminal_it {
                        let ct = l.ct.as_ref();
                        assert!(ct.is_some());
                        let ct = unsafe { ct.unwrap_unchecked() };
                        assert_eq!(&1, ct);
                    } else {
                        sup_ab = unsafe { sub_ab.unwrap_unchecked() };
                    }
                }
            }

            #[test]
            fn zero_occurrent() {
                let mut toc = Toc::new();
                assert_eq!(InsRes::ZeroLen, toc.ins("".chars(), None));
            }

            #[test]
            fn singular_occurrent() {
                let mut toc = Toc::new();
                assert_eq!(InsRes::Ok, toc.ins("a".chars(), None));
                assert_eq!(Some(1), toc.rt[ix('a')].ct);
            }

            #[test]
            fn double_insert() {
                let entry = || "impreciseness".chars();

                let mut toc = Toc::new();
                assert_eq!(InsRes::Ok, toc.ins(entry(), None));
                assert_eq!(InsRes::Ok, toc.ins(entry(), None));

                let chars: Vec<char> = entry().collect();
                let len = chars.len();
                let last_ix = len - 1;

                let mut sup_ab = &toc.rt;
                for c_ix in 0..len {
                    let c = chars[c_ix];
                    let l = &sup_ab[ix(c)];

                    let terminal_it = c_ix == last_ix;

                    let sub_ab = l.ab.as_ref();
                    assert_eq!(terminal_it, sub_ab.is_none(), "{c_ix}, {c}, {terminal_it}",);

                    if terminal_it {
                        let ct = l.ct.as_ref();
                        assert!(ct.is_some());
                        let ct = unsafe { ct.unwrap_unchecked() };
                        assert_eq!(&2, ct);
                    } else {
                        sup_ab = unsafe { sub_ab.unwrap_unchecked() };
                    }
                }
            }

            #[test]
            fn exact() {
                let entry = || "impreciseness".chars();
                const VAL: usize = 15;

                let mut toc = Toc::new();
                assert_eq!(InsRes::Ok, toc.ins(entry(), Some(VAL)));
                assert_eq!(VerRes::Ok(VAL), toc.acq(entry()));
            }

            #[test]
            fn exact_over() {
                let entry = || "impreciseness".chars();
                const VAL: usize = 15;

                let mut toc = Toc::new();
                _ = toc.ins(entry(), None);

                assert_eq!(InsRes::Ok, toc.ins(entry(), Some(VAL)));
                assert_eq!(VerRes::Ok(VAL), toc.acq(entry()));
            }

            use crate::VerRes;

            #[test]
            #[allow(non_snake_case)]
            #[rustfmt::skip]
            #[cfg(feature = "test-ext")]
            fn load() {

                let strs = [
                    ("zzbb", 44_441), ("zzaa", 88_999),
                    ("xya", 77_666), ("xyz", 22_333),
                    ("abc", 33_222), ("abd", 74_332),
                    ("abcd", 11_234), ("abce", 11_234),
                    ("qaa", 16_678), ("qrs", 24_555),
                    ("qrt", 900_001), ("qua", 130_901),
                    ("qwa", 2_006),
                    ("percent", 77_110), ("percentile", 99_888),
                    ("quail", 20_333), ("qualification", 33_111),
                    ("quality", 555_666), ("quantity", 116_777),
                    ("XYAB", 544_555), ("XYABA", 111_900),
                    ("JUI", 30_000), ("JUN", 100_000),
                    ("XYA", 80_000), ("XYQ", 11_111),
                    ("XYZ", 111_333), ("XYABC", 222_000),
                    ("MOMENT", 15_999), ("INSTANT", 34_341),
                    ("JUNCTURE", 789_223),
                    ("ABC", 14_234), ("ABD", 34_123)
                ];

                let mut toc = Toc::new();
                for (s, c) in strs {
                    for _ in 0..c {
                        let res = toc.ins(s.chars(), None);
                        assert_eq!(InsRes::Ok, res);
                    }
                }

                for (s, c) in strs {
                    let res = toc.acq(s.chars());
                    assert_eq!(VerRes::Ok(c), res);                 
                }
            }

            #[test]
            fn overflow_wrap() {
                let mut toc = Toc::new();

                let entry = || "a".chars();

                _ = toc.ins(entry(), None);
                _ = toc.put(entry(), usize::MAX);
                _ = toc.ins(entry(), None);
                assert_eq!(VerRes::Ok(0), toc.acq(entry()));
            }
        }

        mod acq {
            use crate::{Toc, VerRes};

            #[test]
            #[allow(non_upper_case_globals)]
            fn known_unknown() {
                let a = || "a".chars();
                let b = || "b".chars();

                let mut toc = Toc::new();
                _ = toc.ins(a(), None);

                assert_eq!(VerRes::Ok(1), toc.acq(a()));
                assert_eq!(VerRes::Unknown, toc.acq(b()));
            }

            #[test]
            fn zero_occurrent() {
                let toc = Toc::new();
                assert_eq!(VerRes::ZeroLen, toc.acq("".chars()));
            }
        }

        #[test]
        fn as_mut() {
            let toc = Toc::new();
            let toc_ptr = &toc as *const Toc;
            let toc_mut = unsafe { toc.as_mut() };
            assert_eq!(toc_ptr as usize, toc_mut as *mut Toc as usize);
        }

        mod put {
            use crate::{Toc, VerRes};

            #[test]
            #[allow(non_upper_case_globals)]
            fn known_unknown() {
                let a = || "a".chars();
                let b = || "b".chars();

                let mut toc = Toc::new();
                _ = toc.ins(a(), None);

                assert_eq!(VerRes::Ok(1), toc.put(a(), 3));
                assert_eq!(VerRes::Ok(3), toc.acq(a()));
                assert_eq!(VerRes::Unknown, toc.put(b(), 3));
            }

            #[test]
            fn zero_occurrent() {
                let mut toc = Toc::new();
                assert_eq!(VerRes::ZeroLen, toc.put("".chars(), 3));
            }
        }

        mod rem {
            use crate::{Toc, VerRes};

            #[test]
            fn known_unknown() {
                let known = || "VigilantAndVigourous".chars();
                let unknown = || "NeglectfulAndFeeble".chars();

                let mut toc = Toc::new();
                _ = toc.ins(known(), None);

                assert_eq!(VerRes::Ok(1), toc.rem(known()));
                assert_eq!(VerRes::Unknown, toc.acq(known()));
                assert_eq!(0, toc.tr.len());

                assert_eq!(VerRes::Unknown, toc.rem(unknown()));
                assert_eq!(0, toc.tr.len());
            }

            #[test]
            fn zero_occurrent() {
                let mut toc = Toc::new();
                assert_eq!(VerRes::ZeroLen, toc.rem("".chars()));
            }
        }

        mod rem_actual {
            use crate::{Toc, VerRes, TraRes};
            use crate::english_letters::ix;

            #[test]
            fn basic_test() {
                let entry = || "Keyword".chars();
                let mut toc = Toc::new();
                toc.ins(entry(), None);

                _ = toc.track(entry(), true, false);

                assert_eq!(1, Toc::rem_actual(&mut toc.tr));

                #[allow(non_snake_case)]
                let K = &toc.rt[ix('K')];
                assert_eq!(false, K.ab());
            }

            #[test]
            fn inner_entry() {
                let mut toc = Toc::new();

                let outer = || "Keyword".chars();
                toc.ins(outer(), None);

                let inner = || "Key".chars();
                toc.ins(inner(), None);

                _ = toc.track(inner(), true, false);

                assert_eq!(1, Toc::rem_actual(&mut toc.tr));
                assert_eq!(VerRes::Unknown, toc.acq(inner()));
                assert_eq!(VerRes::Ok(1), toc.acq(outer()));
            }

            #[test]
            fn entry_with_peer_entry() {
                let mut toc = Toc::new();

                let peer = || "Keyworder".chars();
                toc.ins(peer(), None);

                let test = || "Keywordee".chars();
                toc.ins(test(), None);

                _ = toc.track(test(), true, false);

                assert_eq!(1, Toc::rem_actual(&mut toc.tr));
                assert_eq!(VerRes::Unknown, toc.acq(test()));
                assert_eq!(VerRes::Ok(1), toc.acq(peer()));
            }

            #[test]
            fn entry_with_peer_with_alphabet() {
                let mut toc = Toc::new();

                let peer = || "Keyworders".chars();
                toc.ins(peer(), None);

                let test = || "Keywordee".chars();
                toc.ins(test(), None);

                _ = toc.track(test(), true, false);

                assert_eq!(1, Toc::rem_actual(&mut toc.tr));
                assert_eq!(VerRes::Unknown, toc.acq(test()));
                assert_eq!(VerRes::Ok(1), toc.acq(peer()));
            }

            #[test]
            fn entry_under_entry() {
                let mut toc = Toc::new();

                let above = || "Keyworder".chars();
                toc.ins(above(), None);

                let under = || "Keyworders".chars();
                toc.ins(under(), None);

                _ = toc.track(under(), true, false);

                assert_eq!(1, Toc::rem_actual(&mut toc.tr));
                assert_eq!(VerRes::Unknown, toc.acq(under()));
                assert_eq!(VerRes::Ok(1), toc.acq(above()));

                let res = toc.track(above(), false, false);
                if let TraRes::Ok(l) = res {
                    #[cfg(feature = "test-ext")]
                    assert_eq!('r', l.val);
                    assert_eq!(false, l.ab());
                } else {
                    panic!("TraRes::Ok(_) was expected, instead {:?}.", res);
                }
            }
        }

        mod track {
            use crate::{Toc, TraRes};

            #[test]
            fn zero_occurrent() {
                let mut toc = Toc::new();
                let res = toc.track("".chars(), false, false);
                assert_eq!(TraRes::ZeroLen, res);
            }

            #[test]
            #[cfg(feature = "test-ext")]
            fn singular_occurrent() {
                let entry = || "A".chars();

                let mut toc = Toc::new();

                _ = toc.ins(entry(), None);
                let res = toc.track(entry(), true, false);

                if let TraRes::Ok(l) = res {
                    let l_val = l.val;
                    let tr = &toc.tr;

                    assert_eq!('A', l_val);
                    assert_eq!(1, tr.len());

                    let l = unsafe { tr[0].as_ref() }.unwrap();
                    assert_eq!('A', l.val)
                } else {
                    panic!("TraRes::Ok(_) was expected, instead {:?}.", res);
                }
            }

            #[test]
            #[cfg(feature = "test-ext")]
            fn tracing() {
                let entry = || "DictionaryLexicon".chars();

                let mut toc = Toc::new();
                toc.ins(entry(), None);
                _ = toc.track(entry(), true, false);

                let proof = entry().collect::<Vec<char>>();
                let tr = &toc.tr;

                assert_eq!(proof.len(), tr.len());

                for (x, &c) in proof.iter().enumerate() {
                    let l = tr[x];
                    let l = unsafe { l.as_mut() }.unwrap();
                    assert_eq!(c, l.val);
                }
            }

            #[test]
            #[cfg(feature = "test-ext")]
            fn ok_variants() {
                let entry = || "Wordbook".chars();
                let last = 'k';

                let mut toc = Toc::new();
                toc.ins(entry(), None);
                let res = toc.track(entry(), false, false);

                match res {
                    | TraRes::Ok(l) => assert_eq!(last, l.val),
                    | _ => panic!("TraRes::Ok(_) was expected, instead {:?}.", res),
                }

                let res = toc.track(entry(), false, true);
                match res {
                    | TraRes::OkMut(l) => assert_eq!(last, l.val),
                    | _ => panic!("TraRes::OkMut(_) was expected, instead {:?}.", res),
                }
            }

            #[test]
            fn unknown_not_path() {
                let key = || "Wordbook".chars();
                let bad_key = || "Wordbooks".chars();

                let mut toc = Toc::new();
                toc.ins(key(), None);
                let res = toc.track(bad_key(), false, false);
                assert_eq!(TraRes::UnknownForAbsentPath, res);
            }

            #[test]
            fn unknown_not_entry() {
                let key = || "Wordbooks".chars();
                let bad_key = || "Wordbook".chars();

                let mut toc = Toc::new();
                toc.ins(key(), None);
                let res = toc.track(bad_key(), false, false);
                assert_eq!(TraRes::UnknownForNotEntry, res);
            }
        }
    }
}

// cargo test --features test-ext --release
