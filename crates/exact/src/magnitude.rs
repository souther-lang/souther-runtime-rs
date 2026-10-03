//! A whole number without a sign, of whatever width: what a `Decimal`'s digits write and what the
//! parts of a `Rational` are.
//!
//! Held in a `u128` wherever it fits, and as a `BigUint` only past that, one form for each value:
//! the wide form never holds what a `u128` holds. Nearly every amount a model computes with —
//! money, a rate, a quantity — has fewer than 39 digits, and on those every operation here is
//! machine arithmetic with no allocation; `num_bigint` is asked only where a value, or a result on
//! the way to one, leaves the `u128`. What an operation answers does not depend on which form did
//! the work, and a test holds every operation's `u128` path to the `BigUint` answer for the same
//! operands, across the edge where one form gives way to the other.
//!
//! That a value a `u128` holds costs no `BigUint` is a property of every path and not only of the
//! answers, so a `BigUint` is only ever made through [`wide`], which counts them in the tests: a
//! test holds the count to nought for every operation whose operands and answer are a `u128`'s.
//!
//! Which form a value is in is this module's alone. A caller sees a [`Magnitude`] and the `u128`
//! it is where it is one, and never a type of `num_bigint`, so how a wide number is worked out can
//! change without any caller's code or answers moving.
//!
//! Nothing here knows a scale, a sign or a rounding mode.

use alloc::string::{String, ToString};
use core::cmp::Ordering;
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{ToPrimitive, Zero};

/// Five to the twenty-seventh, the most a `u64` holds of them: what a wide value is divided by
/// while it is a multiple of it.
const FIVE_TO_27: u128 = 7_450_580_596_923_828_125;

/// A value here takes a greatest common divisor every time one is made, so this is on the way of
/// every operation. Where both fit in 64 bits it divides in them, which is one instruction; past
/// that it shifts and subtracts and never divides, because a division of `u128`s is a routine of
/// many steps, and on WebAssembly, which has no multiply wider than 64 bits, a slow one.
fn u128_gcd(one: u128, two: u128) -> u128 {
    if let (Ok(mut one), Ok(mut two)) = (u64::try_from(one), u64::try_from(two)) {
        while two != 0 {
            (one, two) = (two, one % two);
        }
        return u128::from(one);
    }
    if one == 0 || two == 0 {
        return one | two;
    }
    let shared = (one | two).trailing_zeros();
    let (mut one, mut two) = (one >> one.trailing_zeros(), two >> two.trailing_zeros());
    // Both odd from here on, so their difference is even and nought only where they are equal.
    while one != two {
        if one > two {
            (one, two) = (two, one);
        }
        two -= one;
        two >>= two.trailing_zeros();
    }
    one << shared
}

/// Divided with what is left over, in 64 bits where both fit in them: one instruction where a
/// division of `u128`s is a routine, and nearly every value here fits.
fn u128_div_rem(one: u128, two: u128) -> (u128, u128) {
    match (u64::try_from(one), u64::try_from(two)) {
        (Ok(one), Ok(two)) => (u128::from(one / two), u128::from(one % two)),
        _ => (one / two, one % two),
    }
}

/// Ten to each power a `u128` holds, from nought to 38.
pub const TENS: [u128; 39] = {
    let mut tens = [1u128; 39];
    let mut at = 1;
    while at < tens.len() {
        tens[at] = tens[at - 1] * 10;
        at += 1;
    }
    tens
};

/// A whole number without a sign, in the narrower of the two forms that holds it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Magnitude(Form);

#[derive(Clone, Debug, PartialEq, Eq)]
enum Form {
    Small(u128),
    Wide(BigUint),
}

use Form::{Small, Wide};

/// Where a `BigUint` is made: nowhere else does, so that how many were made is a count the tests
/// can ask, and a value a `u128` holds is held to costing none.
mod wide {
    use num_bigint::BigUint;

    #[cfg(test)]
    std::thread_local! {
        /// How many `BigUint`s this thread has made.
        pub(super) static MADE: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    }

    fn made(big: BigUint) -> BigUint {
        #[cfg(test)]
        MADE.with(|it| it.set(it.get() + 1));
        big
    }

    pub(super) fn of_u128(n: u128) -> BigUint {
        made(BigUint::from(n))
    }

    pub(super) fn of_le_bytes(bytes: &[u8]) -> BigUint {
        made(BigUint::from_bytes_le(bytes))
    }

    pub(super) fn of_digits(digits: &[u8]) -> BigUint {
        made(BigUint::parse_bytes(digits, 10).expect("the digits read are ASCII digits"))
    }

    pub(super) fn five_to(n: u32) -> BigUint {
        made(BigUint::from(5u8).pow(n))
    }

    /// Ten to `n`, for an `n` the caller has already held to a width a value may have.
    pub(super) fn ten_to(n: u64) -> BigUint {
        let n =
            u32::try_from(n).expect("a power of ten built here is one a value may be as wide as");
        made(BigUint::from(10u8).pow(n))
    }
}

impl Magnitude {
    pub const ZERO: Magnitude = Magnitude(Small(0));
    pub const ONE: Magnitude = Magnitude(Small(1));

    /// The magnitude a `u128` is.
    pub const fn of_u128(small: u128) -> Magnitude {
        Magnitude(Small(small))
    }

    /// The `u128` this is, where one holds it.
    pub fn as_u128(&self) -> Option<u128> {
        match &self.0 {
            Small(small) => Some(*small),
            Wide(_) => None,
        }
    }

    /// The magnitude a `BigUint` is, in the narrower form.
    fn of_big(big: BigUint) -> Magnitude {
        match big.to_u128() {
            Some(small) => Magnitude(Small(small)),
            None => Magnitude(Wide(big)),
        }
    }

    /// The same number as a `BigUint`, for the operations only that form answers.
    fn big(&self) -> BigUint {
        match &self.0 {
            Small(small) => wide::of_u128(*small),
            Wide(big) => big.clone(),
        }
    }

    /// The magnitude these bytes write, little end first.
    pub fn of_le_bytes(bytes: &[u8]) -> Magnitude {
        if bytes.len() <= 16 {
            let mut word = [0u8; 16];
            word[..bytes.len()].copy_from_slice(bytes);
            return Magnitude(Small(u128::from_le_bytes(word)));
        }
        Magnitude::of_big(wide::of_le_bytes(bytes))
    }

    /// The magnitude as bytes, little end first and with no zero byte at the top, none at all for
    /// nought, handed to `with` for as long as it runs: a `u128`'s are on the stack.
    pub fn with_le_bytes<T>(&self, with: impl FnOnce(&[u8]) -> T) -> T {
        match &self.0 {
            Small(small) => {
                let bytes = small.to_le_bytes();
                let used = 16 - (small.leading_zeros() / 8) as usize;
                with(&bytes[..used])
            }
            Wide(big) => with(&big.to_bytes_le()),
        }
    }

    /// The whole number these ASCII digits write in decimal, leading zeros and all.
    pub fn of_digits(digits: &[u8]) -> Magnitude {
        // A `u128` holds 39 digits and some 39-digit numbers, so the digits are read as a `u128`
        // for as long as they stay in one, and as a `BigUint` from the digit that leaves it.
        let small = digits.iter().try_fold(0u128, |so_far, digit| {
            so_far
                .checked_mul(10)?
                .checked_add(u128::from(digit - b'0'))
        });
        match small {
            Some(small) => Magnitude(Small(small)),
            None => Magnitude::of_big(wide::of_digits(digits)),
        }
    }

    /// The digits it is written in, in decimal, with no leading zero.
    pub fn digits(&self) -> String {
        match &self.0 {
            Small(small) => small.to_string(),
            Wide(big) => big.to_str_radix(10),
        }
    }

    pub fn is_zero(&self) -> bool {
        matches!(self.0, Small(0))
    }

    pub fn is_odd(&self) -> bool {
        match &self.0 {
            Small(small) => small & 1 == 1,
            Wide(big) => big.is_odd(),
        }
    }

    /// How many bits it is wide.
    pub fn bits(&self) -> u64 {
        match &self.0 {
            Small(small) => u64::from(128 - small.leading_zeros()),
            Wide(big) => big.bits(),
        }
    }

    /// How many decimal digits it has; one for nought, as the JVM counts it.
    ///
    /// A `u128`'s by the powers of ten below it. A wider one's read off how many bits it has,
    /// which gives it to within one, and settled against a power of ten no wider than itself.
    pub fn precision(&self) -> u64 {
        match &self.0 {
            Small(small) => TENS.partition_point(|&ten| ten <= *small).max(1) as u64,
            Wide(big) => {
                let mut digits = ((big.bits() - 1) as f64 * core::f64::consts::LOG10_2) as u64 + 1;
                while digits > 1 && *big < wide::ten_to(digits - 1) {
                    digits -= 1;
                }
                while *big >= wide::ten_to(digits) {
                    digits += 1;
                }
                digits
            }
        }
    }

    pub fn add(&self, other: &Magnitude) -> Magnitude {
        if let (Small(one), Small(two)) = (&self.0, &other.0)
            && let Some(sum) = one.checked_add(*two)
        {
            return Magnitude(Small(sum));
        }
        Magnitude::of_big(self.big() + other.big())
    }

    /// `self` less `other`, which is no greater than it.
    pub fn sub(&self, other: &Magnitude) -> Magnitude {
        match (&self.0, &other.0) {
            (Small(one), Small(two)) => Magnitude(Small(one - two)),
            _ => Magnitude::of_big(self.big() - other.big()),
        }
    }

    pub fn mul(&self, other: &Magnitude) -> Magnitude {
        if let (Small(one), Small(two)) = (&self.0, &other.0)
            && let Some(product) = one.checked_mul(*two)
        {
            return Magnitude(Small(product));
        }
        Magnitude::of_big(self.big() * other.big())
    }

    /// One more.
    pub fn increment(&self) -> Magnitude {
        self.add(&Magnitude::ONE)
    }

    /// Times ten to `by`, for a `by` the caller has already held to a width a value may have.
    pub fn times_ten_to(&self, by: u64) -> Magnitude {
        if self.is_zero() || by == 0 {
            return self.clone();
        }
        if let Small(small) = &self.0
            && let Some(ten) = TENS.get(by as usize)
            && let Some(raised) = small.checked_mul(*ten)
        {
            return Magnitude(Small(raised));
        }
        Magnitude::of_big(self.big() * wide::ten_to(by))
    }

    /// The quotient and the remainder of `self` over `divisor`, which is not nought.
    pub fn div_rem(&self, divisor: &Magnitude) -> (Magnitude, Magnitude) {
        match (&self.0, &divisor.0) {
            (Small(one), Small(two)) => {
                let (quotient, remainder) = u128_div_rem(*one, *two);
                (Magnitude(Small(quotient)), Magnitude(Small(remainder)))
            }
            // A dividend a `u128` holds over one it does not is nought, all of it left over.
            (Small(_), Wide(_)) => (Magnitude::ZERO, self.clone()),
            (Wide(dividend), Small(small)) => {
                let (quotient, remainder) = dividend.div_rem(&wide::of_u128(*small));
                (Magnitude::of_big(quotient), Magnitude::of_big(remainder))
            }
            (Wide(dividend), Wide(divisor)) => {
                let (quotient, remainder) = dividend.div_rem(divisor);
                (Magnitude::of_big(quotient), Magnitude::of_big(remainder))
            }
        }
    }

    /// The greatest whole number dividing both.
    ///
    /// The `BigUint`'s own algorithm subtracts the wider number once for each bit it has, so a pair
    /// of very different widths is a wait of minutes at a few million bits, and the pair nearly
    /// every value here is made of has a denominator of one. So the wider number is first taken
    /// down by division for as long as it is more than a word wider than the other, which is the
    /// whole of the work where the narrower is small; the two that are left of a width are what
    /// the `BigUint`'s algorithm is fast at.
    pub fn gcd(&self, other: &Magnitude) -> Magnitude {
        let (mut wider, mut narrower) = if self >= other {
            (self.clone(), other.clone())
        } else {
            (other.clone(), self.clone())
        };
        loop {
            if narrower.is_zero() {
                return wider;
            }
            if let (Small(one), Small(two)) = (&wider.0, &narrower.0) {
                return Magnitude(Small(u128_gcd(*one, *two)));
            }
            if wider.bits() <= narrower.bits() + 64 {
                return Magnitude::of_big(wider.big().gcd(&narrower.big()));
            }
            let (_, left) = wider.div_rem(&narrower);
            wider = narrower;
            narrower = left;
        }
    }

    /// The magnitude with every factor of five taken off, and how many there were. Twenty-seven
    /// at a time while the value is wide and they are there, then one at a time, for the reason
    /// [`Magnitude::without_trailing_zeros`] takes nineteen.
    pub fn without_fives(&self) -> (Magnitude, u64) {
        if self.is_zero() {
            return (self.clone(), 0);
        }
        let mut magnitude = self.clone();
        let mut dropped = 0u64;
        if matches!(magnitude.0, Wide(_)) {
            let chunk = wide::of_u128(FIVE_TO_27);
            while let Wide(big) = &magnitude.0 {
                let (quotient, remainder) = big.div_rem(&chunk);
                if !remainder.is_zero() {
                    break;
                }
                magnitude = Magnitude::of_big(quotient);
                dropped += 27;
            }
        }
        let five = Magnitude(Small(5));
        loop {
            let (quotient, remainder) = magnitude.div_rem(&five);
            if !remainder.is_zero() {
                break;
            }
            magnitude = quotient;
            dropped += 1;
        }
        (magnitude, dropped)
    }

    /// How many two's it is a multiple of, nought for nought.
    pub fn twos(&self) -> u64 {
        match &self.0 {
            Small(0) => 0,
            Small(small) => u64::from(small.trailing_zeros()),
            Wide(big) => big.trailing_zeros().unwrap_or(0),
        }
    }

    /// Divided by two to `by`, rounded down.
    pub fn shifted_down(&self, by: u64) -> Magnitude {
        match &self.0 {
            Small(_) if by >= 128 => Magnitude::ZERO,
            Small(small) => Magnitude(Small(small >> by)),
            Wide(big) => Magnitude::of_big(big >> by),
        }
    }

    /// Times two to `by`, for a `by` the caller has already held to a width a value may have.
    pub fn times_two_to(&self, by: u64) -> Magnitude {
        if self.is_zero() || by == 0 {
            return self.clone();
        }
        if let Small(small) = &self.0
            && by < 128
            && small.leading_zeros() as u64 >= by
        {
            return Magnitude(Small(small << by));
        }
        Magnitude::of_big(self.big() << by)
    }

    /// Times five to `by`, for a `by` the caller has already held to a width a value may have.
    pub fn times_five_to(&self, by: u64) -> Magnitude {
        if self.is_zero() || by == 0 {
            return self.clone();
        }
        let by = u32::try_from(by).expect("a power built here is one a value may be as wide as");
        Magnitude::of_big(self.big() * wide::five_to(by))
    }

    /// Ten to `n`, for an `n` the caller has already held to a width a value may have.
    pub fn ten_to(n: u64) -> Magnitude {
        match TENS.get(n as usize) {
            Some(small) => Magnitude(Small(*small)),
            None => Magnitude::of_big(wide::ten_to(n)),
        }
    }

    /// The magnitude with as many of its trailing zero digits dropped as there are and `most`
    /// allows, and how many were.
    pub fn without_trailing_zeros(&self, most: u64) -> (Magnitude, u64) {
        if self.is_zero() {
            return (self.clone(), 0);
        }
        let mut magnitude = self.clone();
        let mut dropped = 0u64;
        // Nineteen at a time while the value is wide and they are there, then one at a time, which
        // a value a `u128` holds does as machine division. The nineteen's divisor is made only for
        // a value that is wide.
        if matches!(magnitude.0, Wide(_)) {
            let chunk = wide::of_u128(10_000_000_000_000_000_000);
            while let Wide(big) = &magnitude.0
                && dropped + 19 <= most
            {
                let (quotient, remainder) = big.div_rem(&chunk);
                if !remainder.is_zero() {
                    break;
                }
                magnitude = Magnitude::of_big(quotient);
                dropped += 19;
            }
        }
        let ten = Magnitude(Small(10));
        while dropped < most {
            let (quotient, remainder) = magnitude.div_rem(&ten);
            if !remainder.is_zero() {
                break;
            }
            magnitude = quotient;
            dropped += 1;
        }
        (magnitude, dropped)
    }
}

impl PartialOrd for Magnitude {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Magnitude {
    /// A wide one is past every `u128`, since it is only ever what a `u128` does not hold.
    fn cmp(&self, other: &Self) -> Ordering {
        match (&self.0, &other.0) {
            (Small(one), Small(two)) => one.cmp(two),
            (Small(_), Wide(_)) => Ordering::Less,
            (Wide(_), Small(_)) => Ordering::Greater,
            (Wide(one), Wide(two)) => one.cmp(two),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::vec;
    use std::vec::Vec;

    /// Operands either side of every edge a `u128` path could get wrong: nought, the ends of a
    /// word and of a `u128`, powers of ten at and past the table, and values well past it.
    fn operands() -> Vec<BigUint> {
        let two = BigUint::from(2u8);
        let mut every = vec![
            BigUint::zero(),
            BigUint::from(1u8),
            BigUint::from(9u8),
            BigUint::from(10u8),
            BigUint::from(12_345u32),
            BigUint::from(u64::MAX),
            BigUint::from(u64::MAX) + 1u8,
            BigUint::from(u128::MAX / 10),
            BigUint::from(u128::MAX) - 1u8,
            BigUint::from(u128::MAX),
            BigUint::from(u128::MAX) + 1u8,
            BigUint::from(u128::MAX) * 3u8,
            two.pow(200),
            two.pow(200) - 1u8,
        ];
        for power in [18, 19, 37, 38, 39, 40, 77] {
            let ten = wide::ten_to(power);
            every.push(ten.clone() - 1u8);
            every.push(ten.clone());
            every.push(ten + 7u8);
        }
        every
    }

    /// One form for each value: a `u128`'s is the small one, and only a wider one is wide.
    fn normal(magnitude: &Magnitude) -> bool {
        match &magnitude.0 {
            Small(_) => true,
            Wide(big) => big.to_u128().is_none(),
        }
    }

    fn of(big: &BigUint) -> Magnitude {
        Magnitude::of_big(big.clone())
    }

    fn small(n: u128) -> Magnitude {
        Magnitude::of_u128(n)
    }

    /// Every operation answers what the same operation over `BigUint`s answers, whichever form
    /// its operands and its answer are in, and answers it in the narrower form.
    #[test]
    fn every_operation_answers_what_the_big_integer_answers() {
        let every = operands();
        for one in &every {
            let it = of(one);
            assert!(normal(&it), "{one}");
            assert_eq!(it.big(), *one);
            assert_eq!(it.as_u128(), one.to_u128(), "{one}");
            assert_eq!(it.is_zero(), one.is_zero(), "{one}");
            assert_eq!(it.is_odd(), one.is_odd(), "{one}");
            assert_eq!(it.bits(), one.bits(), "{one}");
            assert_eq!(it.digits(), one.to_str_radix(10), "{one}");
            let digits = if one.is_zero() {
                1
            } else {
                one.to_str_radix(10).len() as u64
            };
            assert_eq!(it.precision(), digits, "{one}");
            assert_eq!(
                Magnitude::of_digits(one.to_str_radix(10).as_bytes()),
                it,
                "{one}"
            );
            let bytes = if one.is_zero() {
                Vec::new()
            } else {
                one.to_bytes_le()
            };
            assert_eq!(it.with_le_bytes(<[u8]>::to_vec), bytes, "{one}");
            assert_eq!(Magnitude::of_le_bytes(&bytes), it, "{one}");
            let increment = it.increment();
            assert!(normal(&increment));
            assert_eq!(increment.big(), one + 1u8, "{one}");
            for by in [0, 1, 2, 19, 38, 39, 60] {
                let raised = it.times_ten_to(by);
                assert!(normal(&raised));
                assert_eq!(raised.big(), one * wide::ten_to(by), "{one} · 10^{by}");
            }
            let (stripped, dropped) = it.without_trailing_zeros(u64::MAX);
            assert!(normal(&stripped));
            let mut expected = (one.clone(), 0u64);
            while !expected.0.is_zero() && (&expected.0 % 10u8).is_zero() {
                expected = (&expected.0 / 10u8, expected.1 + 1);
            }
            assert_eq!((stripped.big(), dropped), expected, "{one}");
            let (limited, dropped) = it.without_trailing_zeros(1);
            assert!(dropped <= 1);
            assert_eq!(limited.big() * wide::ten_to(dropped), *one, "{one}");
            for two in &every {
                let other = of(two);
                assert_eq!(it.cmp(&other), one.cmp(two), "{one} {two}");
                let sum = it.add(&other);
                assert!(normal(&sum));
                assert_eq!(sum.big(), one + two, "{one} + {two}");
                let product = it.mul(&other);
                assert!(normal(&product));
                assert_eq!(product.big(), one * two, "{one} · {two}");
                if one >= two {
                    let difference = it.sub(&other);
                    assert!(normal(&difference));
                    assert_eq!(difference.big(), one - two, "{one} - {two}");
                }
                if !two.is_zero() {
                    let (quotient, remainder) = it.div_rem(&other);
                    assert!(normal(&quotient) && normal(&remainder));
                    assert_eq!(
                        (quotient.big(), remainder.big()),
                        one.div_rem(two),
                        "{one} / {two}"
                    );
                }
            }
        }
        for power in 0..80 {
            assert_eq!(
                Magnitude::ten_to(power).big(),
                wide::ten_to(power),
                "{power}"
            );
            assert!(normal(&Magnitude::ten_to(power)));
        }
    }

    /// A `BigUint`s made while `run` ran, and what it answered.
    fn counted<T>(run: impl FnOnce() -> T) -> (T, usize) {
        let before = wide::MADE.with(std::cell::Cell::get);
        let answered = run();
        (answered, wide::MADE.with(std::cell::Cell::get) - before)
    }

    /// A value a `u128` holds costs no `BigUint`: every operation whose operands and answer a `u128`
    /// holds makes none, on any path through it, and not only the answers are the narrow ones. A
    /// `BigUint` made on the way to a narrow answer is the allocation the two forms exist to avoid,
    /// and no answer shows it.
    #[test]
    fn a_value_a_u128_holds_costs_no_big_integer() {
        let smalls: Vec<BigUint> = operands()
            .into_iter()
            .filter(|it| it.to_u128().is_some())
            .collect();
        assert!(smalls.len() > 10);
        // `Some` where the answer is narrow, which is where none may be made.
        let clean = |what: &str, made: (bool, usize)| {
            if made.0 {
                assert_eq!(
                    made.1, 0,
                    "{what} made {} BigUint(s) for a u128's worth",
                    made.1
                );
            }
        };
        for one in &smalls {
            let it = of(one);
            let text = one.to_str_radix(10);
            let bytes = if one.is_zero() {
                Vec::new()
            } else {
                one.to_bytes_le()
            };
            clean(
                "of_digits",
                narrow(counted(|| Magnitude::of_digits(text.as_bytes()))),
            );
            clean(
                "of_le_bytes",
                narrow(counted(|| Magnitude::of_le_bytes(&bytes))),
            );
            clean("increment", narrow(counted(|| it.increment())));
            for by in [0, 1, 19, 38, 39] {
                clean("times_ten_to", narrow(counted(|| it.times_ten_to(by))));
            }
            clean(
                "without_trailing_zeros",
                narrow(counted(|| it.without_trailing_zeros(u64::MAX).0)),
            );
            clean(
                "without_trailing_zeros(3)",
                narrow(counted(|| it.without_trailing_zeros(3).0)),
            );
            for read in [
                counted(|| it.digits()).1,
                counted(|| it.precision()).1,
                counted(|| it.bits()).1,
                counted(|| it.is_odd()).1,
                counted(|| it.is_zero()).1,
                counted(|| it.with_le_bytes(<[u8]>::len)).1,
            ] {
                assert_eq!(read, 0, "{one}");
            }
            for two in &smalls {
                let other = of(two);
                assert_eq!(counted(|| it.cmp(&other)).1, 0, "{one} {two}");
                clean("add", narrow(counted(|| it.add(&other))));
                clean("mul", narrow(counted(|| it.mul(&other))));
                if one >= two {
                    clean("sub", narrow(counted(|| it.sub(&other))));
                }
                if !two.is_zero() {
                    clean("div_rem", narrow(counted(|| it.div_rem(&other).0)));
                }
            }
        }
        for power in 0..=38 {
            clean("ten_to", narrow(counted(|| Magnitude::ten_to(power))));
        }
    }

    fn narrow((magnitude, made): (Magnitude, usize)) -> (bool, usize) {
        (matches!(magnitude.0, Small(_)), made)
    }

    /// A wide number beside a narrow one is worked out from the narrow one's remainder, and is
    /// the same answer the `BigUint` gives, across the edge where a `u128` gives way. A number of
    /// millions of bits beside one is not a wait, which the `BigUint`'s own gcd would make it.
    #[test]
    fn a_gcd_of_a_wide_number_beside_a_narrow_one_is_the_big_integers() {
        for one in operands() {
            for two in operands() {
                let (a, b) = (of(&one), of(&two));
                assert_eq!(a.gcd(&b), of(&one.gcd(&two)), "{one} and {two}");
            }
        }
        let wide = small(1).times_two_to(4_000_000).sub(&small(1));
        assert_eq!(wide.gcd(&small(1)), small(1));
        assert_eq!(small(1).gcd(&wide), small(1));
        assert_eq!(wide.gcd(&small(0)), wide);
        // 2^4000000 - 1 is a multiple of 2^2 - 1 and of 2^5 - 1 (four million is one of five).
        assert_eq!(wide.gcd(&small(15)), small(15));
    }

    /// The factors of five come off a wide number in chunks and a narrow one singly, and each is
    /// counted once whichever way it went.
    #[test]
    fn every_factor_of_five_comes_off_and_is_counted() {
        let seven = small(7);
        for fives in [0u64, 1, 26, 27, 28, 54, 100, 1000] {
            let made = seven.times_five_to(fives);
            assert_eq!(made.without_fives(), (seven.clone(), fives), "{fives}");
        }
        let wide = small(3).times_two_to(300).times_five_to(200);
        let (rest, by) = wide.without_fives();
        assert_eq!((rest, by), (small(3).times_two_to(300), 200));
        assert_eq!(Magnitude::ZERO.without_fives(), (Magnitude::ZERO, 0));
    }
}
