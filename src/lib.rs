//! Trie Occurrence Counter is frequency dictionary that uses any `impl Iterator<Item = char>` type as occurrent.
//!
//! Support for English letters A–Za–z OOB.

use std::vec::Vec;

/// `Letter` is `Alphabet` element, represents tree node.
#[cfg_attr(test, derive(PartialEq))]
struct Letter {
    #[cfg(test)]
    val: char,
    ab: Option<Alphabet>,
    ct: Option<usize>,
}

impl Letter {
    const fn new() -> Self {
        Letter {
            #[cfg(test)]
            val: '💚',
            ab: None,
            ct: None,
        }
    }

    const fn ab(&self) -> bool {
        self.ab.is_some()
    }

    const fn ct(&self) -> bool {
        self.ct.is_some()
    }
}

/// Tree node arms. Consists of `Letter`s.
type Alphabet = Box<[Letter]>;
/// Index conversion function. Tighten with alphabet used.
/// Returns corresponding `usize`d index of `char`.
///
/// For details see `english_letters::ix` implementation.
pub type Ix = fn(char) -> usize;

/// Reversal index conversion function. Symmetrically mirrors `Ix` function.
///
/// For details see `english_letters::re` implementation.
pub type Re = fn(usize) -> char;

/// Alphabet function, tree arms generation of length specified.
fn ab(len: usize) -> Alphabet {
    let mut ab = Vec::new();
    ab.reserve_exact(len);

    #[cfg(test)]
    #[cfg(feature = "test-ext")]
    let mut c = 'A' as u8;

    let sc = ab.spare_capacity_mut();
    for ix in 0..len {
        let mut _letter = sc[ix].write(Letter::new());

        #[cfg(test)]
        #[cfg(feature = "test-ext")]
        {
            _letter.val = c as char;

            const Z: u8 = 'Z' as u8;
            c = if c == Z { 'a' as u8 } else { c + 1 }
        }
    }

    unsafe { ab.set_len(len) };

    ab.into_boxed_slice()
}

/// Module for working with English alphabet letters, A-Za-z.
///
/// For details see `Toc::new_with()`.
pub mod english_letters {

    /// 26
    pub const BASE_ALPHABET_LEN: usize = 26;
    /// 52
    pub const ALPHABET_LEN: usize = BASE_ALPHABET_LEN * 2;

    const A: usize = 'A' as usize;
    #[allow(non_upper_case_globals)]
    const a: usize = 'a' as usize;

    /// Index conversion function.
    pub fn ix(c: char) -> usize {
        let code_point = c as usize;

        match code_point {
            | c if c > 64 && c < 91 => c - A,
            | c if c > 96 && c < 123 => c - a + BASE_ALPHABET_LEN,
            | _ => {
                panic!("Index conversion failed because code point `{code_point}` is unsupported.")
            },
        }
    }

    /// Index reversal conversion function.
    pub fn re(i: usize) -> char {
        let code_point = match i {
            | i if i < 26 => i + A,
            | i if i > 25 && i < 52 => i + a - BASE_ALPHABET_LEN,
            | _ => {
                panic!("Char conversion failed because index `{i}` conversion is not supported.")
            },
        };

        code_point as u8 as char
    }
}

///  Addition result enumeration.
#[derive(Debug)]
#[derive(PartialEq, Eq)]
pub enum AddRes {
    /// Addition accomplished. Optionally carries previous value, based on its existence.
    Ok(Option<usize>),
    /// Attempt to add zero occurrent.
    ZeroLen,
}

impl AddRes {
    /// Returns `true` only for `AddRes::Ok(_)`.
    pub const fn is_ok(&self) -> bool {
        match self {
            | AddRes::Ok(_) => true,
            | _ => false,
        }
    }

    /// Returns `true` only for `AddRes::Ok(Some(_))`.
    pub const fn is_ok_some(&self) -> bool {
        if let AddRes::Ok(opt) = self {
            if let Some(_) = opt {
                return true;
            }
        }

        false
    }

    /// Returns `usize` of `AddRes::Ok(Some(usize))` or _panics_ if:
    /// - not that variant
    /// - `Option<usize>` is `None`
    pub const fn uproot_ok_some(&self) -> usize {
        if let AddRes::Ok(opt) = self {
            if let Some(n) = opt {
                return *n;
            }
        }

        panic!("Not AddRes::Ok(Some(_)) variant.")
    }

    /// Returns `usize` of `AddRes::Ok(Some(usize))` and does not _panic_ (UB) if:
    /// - not that variant
    /// - `Option<usize>` is `None`
    ///
    /// Check with `std::hint::unreachable_unchecked` for more information.
    pub const unsafe fn uproot_ok_some_unchecked(&self) -> usize {
        if let AddRes::Ok(opt) = self {
            if let Some(n) = opt {
                return *n;
            }
        }
        // SAFETY: the safety contract must be upheld by the caller.
        unsafe { std::hint::unreachable_unchecked() }
    }
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
    /// Returns `true` only for `VerRes::Ok(_)`.
    pub const fn is_ok(&self) -> bool {
        match self {
            | VerRes::Ok(_) => true,
            | _ => false,
        }
    }

    /// Returns `usize` of `VerRes::Ok(usize)` or _panics_ if not that variant.
    pub const fn uproot(&self) -> usize {
        match self {
            | VerRes::Ok(res) => *res,
            | _ => panic!("Value is not `Ok(usize)` variant."),
        }
    }

    /// Returns `usize` of `VerRes::Ok(usize)` and does not _panic_ if not that variant (UB).
    ///
    /// Check with `std::hint::unreachable_unchecked` for more information.
    pub const unsafe fn uproot_unchecked(&self) -> usize {
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

// TC: Ω(n ⋅ alphabet size) ⇒ Ω(n), n = nodes count
// SC: Θ(s + n) ⇒ Θ(s), n = nodes count, s = key lengths sum
// to lower estimation add unpredictible count of string clonings
// and buffer (capacity-) reallocations
fn ext(ab: &Alphabet, buff: &mut String, re: Re, o: &mut Vec<(String, usize)>) {
    for ix in 0..ab.len() {
        buff.push(re(ix));

        let letter = &ab[ix];

        if let Some(ct) = letter.ct {
            let key = buff.clone();
            o.push((key, ct));
        }

        if let Some(ab) = letter.ab.as_ref() {
            ext(ab, buff, re, o);
        }

        _ = buff.pop();
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
/// _ = toc.add(occurrent.chars(), None);
/// _ = toc.add(true.to_string().chars(), None);
///
/// assert_eq!(2, toc.acq(occurrent.chars()).uproot());
/// toc.put(occurrent.chars(), 15);
/// assert_eq!(15, toc.acq(occurrent.chars()).uproot());
///
/// let catch = catch_unwind(move|| _ = toc.add("#&%".chars(), None));
/// assert!(catch.is_err());
/// ```
///
/// When asymptotic computational complexity is not explicitly specified , it is:
/// - TC: Θ(c) where c is count of `char`s iterated over.
/// - SC: Θ(0).
pub struct Toc {
    // tree root
    rt: Alphabet,
    // index fn
    ix: Ix,
    // rev index fn
    re: Option<Re>,
    // alphabet len
    al: usize,
    // backtrace buff
    tr: Vec<*mut Letter>,
}

impl Toc {
    /// Constructs default version of `Toc`, i.e. via
    /// `fn new_with()` with `english_letters::{ix, re, ALPHABET_LEN}`.
    pub fn new() -> Self {
        Self::new_with(
            english_letters::ix,
            Some(english_letters::re),
            english_letters::ALPHABET_LEN,
        )
    }

    /// Allows to use custom alphabet different from default alphabet.
    ///
    /// ```
    /// use t_oc::Toc;
    ///
    /// fn ix(c: char) -> usize {
    ///     match c {
    ///         '&' => 0,
    ///         '|' => 1,
    ///         _ => panic!(),
    ///     }
    /// }
    ///
    /// // if `fn Toc::ext` will not be used, pass `None` for `re`
    /// fn re(i: usize) -> char {
    ///     match i {
    ///         0 => '&',
    ///         1 => '|',
    ///         _ => panic!(),
    ///     }
    /// }    
    ///
    /// let ab_len = 2;
    ///
    /// let mut toc = Toc::new_with(ix, Some(re), ab_len);
    /// let a = "&";
    /// let b = "|";
    /// let aba = "&|&";
    /// _ = toc.add(a.chars(), None);
    /// _ = toc.add(a.chars(), None);
    /// _ = toc.add(b.chars(), None);
    /// _ = toc.add(aba.chars(), None);
    /// assert_eq!(2, toc.acq(a.chars()).uproot());
    /// assert_eq!(1, toc.acq(aba.chars()).uproot());
    pub fn new_with(ix: Ix, re: Option<Re>, ab_len: usize) -> Self {
        Self {
            rt: ab(ab_len),
            ix,
            re,
            al: ab_len,
            tr: Vec::new(),
        }
    }

    /// Used to set internal backtracing buffer capacity.
    ///
    /// `Toc` uses internal buffer, to avoid excessive allocations and copying, which grows
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

    /// Used to obtain internal backtracing buffer capacity.
    ///
    /// Check with `fn put_trace_cap` for details.
    pub fn acq_trace_cap(&self) -> usize {
        self.tr.capacity()
    }

    /// Used to add occurence to tree.
    ///
    /// Counter is of word size. Add overflow is wrapped using `wrapping_add`.
    ///
    /// Optional `val` parameter can be used to insert exact value.
    ///
    /// Return value is `AddRes::Ok(Option<usize>)` for non-zero `occurrent` and holds previous value, if there was some.
    ///
    /// - SC: Θ(q) where q is number of unique nodes, i.e. `char`s in respective branches.
    pub fn add(&mut self, mut occurrent: impl Iterator<Item = char>, val: Option<usize>) -> AddRes {
        let c = occurrent.next();

        if c.is_none() {
            return AddRes::ZeroLen;
        }

        let c = unsafe { c.unwrap_unchecked() };

        let ix = self.ix;
        let al = self.al;

        let mut letter = &mut self.rt[ix(c)];

        while let Some(c) = occurrent.next() {
            let alphabet = letter.ab.get_or_insert_with(|| ab(al));
            letter = &mut alphabet[ix(c)];
        }

        let ct = letter.ct;
        letter.ct = Some(if let Some(v) = val {
            v
        } else {
            if let Some(c) = ct {
                c.wrapping_add(1)
            } else {
                1
            }
        });

        AddRes::Ok(ct)
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
    /// - _c_ is count of `char`s iterated over.
    /// - TC: Ω(c) or ϴ(c) (backtracing buffer capacity dependent complexity).
    /// - SC: ϴ(c).
    ///
    /// Check with `put_trace_cap` for details on backtracing.
    pub fn rem(&mut self, occurrent: impl Iterator<Item = char>) -> VerRes {
        let track_res = self.track(occurrent, true, false);
        let res = if let TraRes::Ok(_) = track_res {
            let ct = Self::rem_actual(self);
            VerRes::Ok(ct)
        } else {
            track_res.ver_res()
        };

        self.tr.clear();
        res
    }

    fn rem_actual(&mut self) -> usize {
        let mut trace = self.tr.iter_mut().map(|x| unsafe { x.as_mut() }.unwrap());
        let entry = trace.next_back().unwrap();

        let ct = entry.ct.take();

        if !entry.ab() {
            while let Some(l) = trace.next_back() {
                let alphabet = l.ab.as_ref().unwrap();
                let mut remove_alphab = true;

                for ix in 0..self.al {
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

        unsafe { ct.unwrap_unchecked() }
    }

    // - s is count of `char`s iterated over
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

    /// Used to extract occurences from tree.
    ///
    /// Does not clear tree. Check with `fn clr` for this.
    ///
    /// - TC: Ω(n) where n is node count.
    /// - SC: Θ(s) where s is occurrent lengths summation.
    pub fn ext(&self) -> Vec<(String, usize)> {
        if let Some(re) = self.re {
            // capacity is prebuffered to 1000
            let mut buff = String::with_capacity(1000);

            // capacity is prebuffered to 1000
            let mut res = Vec::with_capacity(1000);

            ext(&self.rt, &mut buff, re, &mut res);
            res.shrink_to_fit();
            res
        } else {
            panic!("This method is unsupported when `new_with` `re` parameter is provided with `None`.");
        }
    }

    /// Used to clear tree.
    pub fn clr(&mut self) {
        self.rt = ab(self.al);
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

        use crate::{Letter, ab as ab_fn};

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
            assert_eq!(false, letter.ab());

            letter.ab = Some(ab_fn(0));
            assert_eq!(true, letter.ab());
        }

        #[test]
        fn ct() {
            let mut letter = Letter::new();
            assert_eq!(false, letter.ct());

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

        use crate::english_letters::{ALPHABET_LEN, BASE_ALPHABET_LEN};

        #[test]
        fn consts() {
            assert_eq!(26, BASE_ALPHABET_LEN);
            assert_eq!(52, ALPHABET_LEN);
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

                for (c, cp) in ucs.map(|x| (x as char, x)) {
                    let result = catch_unwind(|| ix(c));
                    assert!(result.is_err());

                    let err = unsafe { result.unwrap_err_unchecked() };
                    let downcast = err.downcast_ref::<String>().unwrap();
                    let proof = format!(
                        "Index conversion failed because code point `{cp}` is unsupported."
                    );
                    assert_eq!(&proof, downcast);
                }
            }

            fn unsupported_chars() -> [u8; 4] {
                #[rustfmt::skip] let ucs =
                [
                    'A' as u8 -1, 'Z' as u8 +1, // 65–90
                    'a' as u8 -1, 'z' as u8 +1, // 97–122
                ];
                ucs
            }
        }

        mod re {
            use crate::english_letters::re;

            #[test]
            fn ixes() {
                assert_eq!('A', re(0));
                assert_eq!('Z', re(25));
                assert_eq!('a', re(26));
                assert_eq!('z', re(51));
            }

            #[test]
            #[should_panic(
                expected = "Char conversion failed because index `52` conversion is not supported."
            )]
            fn unsupported_ix() {
                _ = re(52)
            }
        }
    }

    mod add_res {
        use crate::AddRes;

        #[test]
        fn is_ok() {
            assert_eq!(true, AddRes::Ok(None).is_ok());
            assert_eq!(false, AddRes::ZeroLen.is_ok());
        }

        #[test]
        fn is_ok_some_some() {
            assert_eq!(true, AddRes::Ok(Some(3)).is_ok_some());
        }

        #[test]
        fn is_ok_some_none() {
            assert_eq!(false, AddRes::Ok(None).is_ok_some());
        }

        #[test]
        fn is_ok_some_not_ok() {
            assert_eq!(false, AddRes::ZeroLen.is_ok_some());
        }

        #[test]
        fn uproot_ok_some_some() {
            let val = 3;
            assert_eq!(val, AddRes::Ok(Some(val)).uproot_ok_some());
        }

        #[test]
        #[should_panic(expected = "Not AddRes::Ok(Some(_)) variant.")]
        fn uproot_ok_some_none() {
            _ = AddRes::Ok(None).uproot_ok_some()
        }

        #[test]
        #[should_panic(expected = "Not AddRes::Ok(Some(_)) variant.")]
        fn uproot_ok_some_not_ok() {
            _ = AddRes::ZeroLen.uproot_ok_some()
        }

        #[test]
        fn uproot_ok_some_unchecked() {
            let val = 3;
            let uproot = unsafe { AddRes::Ok(Some(val)).uproot_ok_some_unchecked() };
            assert_eq!(val, uproot);
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
        fn uproot() {
            assert_eq!(33, VerRes::Ok(33).uproot());
        }

        #[test]
        #[should_panic(expected = "Value is not `Ok(usize)` variant.")]
        fn uproot_panic() {
            VerRes::ZeroLen.uproot();
        }

        #[test]
        fn uproot_unchecked() {
            const VAL: usize = 77;
            let test = unsafe { VerRes::Ok(VAL).uproot_unchecked() };
            assert_eq!(VAL, test);
        }
    }

    mod ext {

        type Nest = (char, usize);

        use crate::{ab as ab_ctor, ext, Alphabet};
        use crate::english_letters::{ALPHABET_LEN, ix, re};

        fn ab_fn() -> Alphabet {
            ab_ctor(ALPHABET_LEN)
        }

        #[test]
        fn basic_test() {
            let mut ab = ab_fn();

            ab[ix('A')].ct = Some(1);
            ab[ix('z')].ct = Some(2);

            let mut buff = String::new();
            let mut test = Vec::new();

            ext(&ab, &mut buff, re, &mut test);

            let proof = vec![(String::from("A"), 1), (String::from("z"), 2)];
            assert_eq!(proof, test);
        }

        #[test]
        fn nesting() {
            let mut root = ab_fn();

            let nesting = [
                (('A', 3), ('z', 5)),
                (('B', 5), ('y', 8)),
                (('y', 10), ('B', 12)),
                (('z', 99), ('A', 103)),
            ];

            for n in nesting {
                prep(&mut root, n);
            }

            let mut buff = String::new();
            let mut test = Vec::new();

            ext(&root, &mut buff, re, &mut test);

            let proof = vec![
                (String::from("A"), 3),
                (String::from("Az"), 5),
                (String::from("B"), 5),
                (String::from("By"), 8),
                (String::from("y"), 10),
                (String::from("yB"), 12),
                (String::from("z"), 99),
                (String::from("zA"), 103),
            ];

            assert_eq!(proof, test);

            fn prep(ab: &mut Alphabet, n: (Nest, Nest)) {
                let ultra = n.0;
                let infra = n.1;

                let u_l = &mut ab[ix(ultra.0)];
                let mut ul_ab = ab_fn();

                let i_l = &mut ul_ab[ix(infra.0)];
                i_l.ct = Some(infra.1);

                u_l.ab = Some(ul_ab);
                u_l.ct = Some(ultra.1);
            }
        }

        #[test]
        fn in_depth_recursion() {
            let mut root = ab_fn();

            let paths = [
                ("AA", 13),
                ("AzBq", 11),
                ("By", 329),
                ("ZaZazAzAzAbYyb", 55),
                ("yBC", 7),
                ("ybXr", 53),
                ("ybXrQUTmop", 33),
                ("ybXrQUTmopFVB", 99),
                ("ybXrQUTmopRFG", 80),
                ("zAzAZaZaZaByYB", 44),
            ];

            for p in paths {
                let mut chars = p.0.chars();
                let mut le = &mut root[ix(chars.next().unwrap())];

                while let Some(c) = chars.next() {
                    let ab = le.ab.get_or_insert_with(|| ab_fn());
                    le = &mut ab[ix(c)];
                }

                le.ct = Some(p.1)
            }

            let mut buff = String::new();
            let mut test = Vec::new();

            ext(&root, &mut buff, re, &mut test);

            let proof = vec![
                (String::from("AA"), 13),
                (String::from("AzBq"), 11),
                (String::from("By"), 329),
                (String::from("ZaZazAzAzAbYyb"), 55),
                (String::from("yBC"), 7),
                (String::from("ybXr"), 53),
                (String::from("ybXrQUTmop"), 33),
                (String::from("ybXrQUTmopFVB"), 99),
                (String::from("ybXrQUTmopRFG"), 80),
                (String::from("zAzAZaZaZaByYB"), 44),
            ];

            assert_eq!(proof, test);
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
        use crate::{Toc, ab};
        use crate::english_letters::{ix, re, ALPHABET_LEN};

        #[test]
        fn new() {
            let toc = Toc::new();
            assert_eq!(ALPHABET_LEN, toc.al);
            assert_eq!(ix as usize, toc.ix as usize);
            assert_eq!(re as usize, toc.re.unwrap() as usize);
        }

        #[test]
        fn new_with() {
            fn test_ix(_c: char) -> usize {
                0
            }

            fn test_re(_i: usize) -> char {
                '\0'
            }

            let ab_len = 10;
            let toc = Toc::new_with(test_ix, Some(test_re), ab_len);

            assert_eq!(ab(ab_len), toc.rt);
            assert_eq!(ab_len, toc.al);
            assert_eq!(test_ix as usize, toc.ix as usize);
            assert_eq!(test_re as usize, toc.re.unwrap() as usize);
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

        mod add {
            use crate::{Toc, AddRes};
            use crate::english_letters::ix;

            #[test]
            fn basic_test() {
                let entry = || "impreciseness".chars();

                let mut toc = Toc::new();
                assert_eq!(AddRes::Ok(None), toc.add(entry(), None));

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
                assert_eq!(AddRes::ZeroLen, toc.add("".chars(), None));
            }

            #[test]
            fn singular_occurrent() {
                let mut toc = Toc::new();
                assert_eq!(AddRes::Ok(None), toc.add("a".chars(), None));
                assert_eq!(Some(1), toc.rt[ix('a')].ct);
            }

            #[test]
            fn double_add() {
                let entry = || "impreciseness".chars();

                let mut toc = Toc::new();
                assert_eq!(AddRes::Ok(None), toc.add(entry(), None));
                assert_eq!(AddRes::Ok(Some(1)), toc.add(entry(), None));

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
                assert_eq!(AddRes::Ok(None), toc.add(entry(), Some(VAL)));
                assert_eq!(VerRes::Ok(VAL), toc.acq(entry()));
            }

            #[test]
            fn exact_over() {
                let entry = || "impreciseness".chars();
                const VAL: usize = 15;

                let mut toc = Toc::new();
                _ = toc.add(entry(), None);

                assert_eq!(AddRes::Ok(Some(1)), toc.add(entry(), Some(VAL)));
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
                    for i in 0..c {
                        let res = toc.add(s.chars(), None);
                        let prev = if i > 0 {
                            Some(i)
                        } else {
                            None
                        };        
                        assert_eq!(AddRes::Ok(prev), res);
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

                _ = toc.add(entry(), None);
                _ = toc.put(entry(), usize::MAX);
                _ = toc.add(entry(), None);
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
                _ = toc.add(a(), None);

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
                _ = toc.add(a(), None);

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
                _ = toc.add(known(), None);

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
                let entry = || "ABCxyz".chars();
                let mut toc = Toc::new();
                _ = toc.add(entry(), None);

                _ = toc.track(entry(), true, false);

                assert_eq!(1, Toc::rem_actual(&mut toc));

                #[allow(non_snake_case)]
                let K = &toc.rt[ix('A')];
                assert_eq!(false, K.ab());
            }

            #[test]
            fn ab_len_test() {
                let ix = |c| match c {
                    | 'a' => 0,
                    | 'z' => 99,
                    | _ => panic!(),
                };

                let key_1 = || "aaa".chars();
                let key_2 = || "aaz".chars();

                let key_1_val = 50;
                let key_2_val = 60;

                let mut toc = Toc::new_with(ix, None, 100);
                _ = toc.add(key_1(), Some(key_1_val));
                _ = toc.add(key_2(), Some(key_2_val));

                _ = toc.track(key_1(), true, false);

                assert_eq!(key_1_val, Toc::rem_actual(&mut toc));
                assert!(toc.acq(key_2()).is_ok());
            }

            #[test]
            fn inner_entry() {
                let mut toc = Toc::new();

                let outer = || "Keyword".chars();
                _ = toc.add(outer(), None);

                let inner = || "Key".chars();
                _ = toc.add(inner(), None);

                _ = toc.track(inner(), true, false);

                assert_eq!(1, Toc::rem_actual(&mut toc));
                assert_eq!(VerRes::Unknown, toc.acq(inner()));
                assert_eq!(VerRes::Ok(1), toc.acq(outer()));
            }

            #[test]
            fn entry_with_peer_entry() {
                let mut toc = Toc::new();

                let peer = || "Keyworder".chars();
                _ = toc.add(peer(), None);

                let test = || "Keywordee".chars();
                _ = toc.add(test(), None);

                _ = toc.track(test(), true, false);

                assert_eq!(1, Toc::rem_actual(&mut toc));
                assert_eq!(VerRes::Unknown, toc.acq(test()));
                assert_eq!(VerRes::Ok(1), toc.acq(peer()));
            }

            #[test]
            fn entry_with_peer_with_alphabet() {
                let mut toc = Toc::new();

                let peer = || "Keyworders".chars();
                _ = toc.add(peer(), None);

                let test = || "Keywordee".chars();
                _ = toc.add(test(), None);

                _ = toc.track(test(), true, false);

                assert_eq!(1, Toc::rem_actual(&mut toc));
                assert_eq!(VerRes::Unknown, toc.acq(test()));
                assert_eq!(VerRes::Ok(1), toc.acq(peer()));
            }

            #[test]
            fn entry_under_entry() {
                let mut toc = Toc::new();

                let above = || "Keyworder".chars();
                _ = toc.add(above(), None);

                let under = || "Keyworders".chars();
                _ = toc.add(under(), None);

                _ = toc.track(under(), true, false);

                assert_eq!(1, Toc::rem_actual(&mut toc));
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

                _ = toc.add(entry(), None);
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
                _ = toc.add(entry(), None);
                _ = toc.track(entry(), true, false);

                let proof = entry().collect::<Vec<char>>();
                let tr = &toc.tr;

                assert_eq!(proof.len(), tr.len());

                for (x, &c) in proof.iter().enumerate() {
                    let l = tr[x];
                    let l = unsafe { l.as_ref() }.unwrap();
                    assert_eq!(c, l.val);
                }
            }

            #[test]
            #[cfg(feature = "test-ext")]
            fn ok_variants() {
                let entry = || "Wordbook".chars();
                let last = 'k';

                let mut toc = Toc::new();
                _ = toc.add(entry(), None);
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
                _ = toc.add(key(), None);
                let res = toc.track(bad_key(), false, false);
                assert_eq!(TraRes::UnknownForAbsentPath, res);
            }

            #[test]
            fn unknown_not_entry() {
                let key = || "Wordbooks".chars();
                let bad_key = || "Wordbook".chars();

                let mut toc = Toc::new();
                _ = toc.add(key(), None);
                let res = toc.track(bad_key(), false, false);
                assert_eq!(TraRes::UnknownForNotEntry, res);
            }
        }

        mod ext {
            use crate::{Toc, VerRes};
            use crate::english_letters::ix;

            #[test]
            fn basic_test() {
                let test = vec![
                    (String::from("AA"), 13),
                    (String::from("AzBq"), 11),
                    (String::from("By"), 329),
                    (String::from("ZaZazAzAzAbYyb"), 55),
                    (String::from("yBC"), 7),
                    (String::from("ybXr"), 53),
                    (String::from("ybXrQUTmop"), 33),
                    (String::from("ybXrQUTmopFVB"), 99),
                    (String::from("ybXrQUTmopRFG"), 80),
                    (String::from("zAzAZaZaZaByYB"), 44),
                ];

                let mut toc = Toc::new();
                for t in test.iter() {
                    _ = toc.add(t.0.chars(), Some(t.1));
                }

                let ext = toc.ext();
                assert_eq!(test, ext);
                assert!(ext.capacity() < 1000);

                for t in test.iter() {
                    assert_eq!(VerRes::Ok(t.1), toc.acq(t.0.chars()));
                }
            }

            #[test]
            #[should_panic(
                expected = "This method is unsupported when `new_with` `re` parameter is provided with `None`."
            )]
            fn re_not_provided() {
                _ = Toc::new_with(ix, None, 0).ext()
            }
        }

        use crate::VerRes;

        #[test]
        fn clr() {
            let key = || "abc".chars();

            let mut toc = Toc::new();
            _ = toc.add(key(), None);
            toc.clr();

            assert_eq!(VerRes::Unknown, toc.acq(key()));
            assert_eq!(ab(ALPHABET_LEN), toc.rt);
        }
    }
}

// cargo test --features test-ext --release
