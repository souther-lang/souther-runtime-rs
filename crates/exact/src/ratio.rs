//! An exact rational, and what each operation on one answers (spec §stdlib-rational).
//!
//! The value is `numerator × 2^twos × 5^fives / denominator`, in the one form that has each value
//! once: the numerator and the denominator are coprime and neither is a multiple of two or of
//! five, the denominator is above nought, and nought is `0 / 1` with no exponents. A `Decimal`
//! enters by its scale being negated into the two exponents and nothing being built from it, so a
//! decimal at a scale of a billion is as small here as it is there, and equal values have equal
//! parts.
//!
//! Two limits are kept apart, because confusing them answers a value wrongly. What a value may be
//! is a limit of the carrier: an exponent past sixty-four bits, or a numerator or a denominator
//! wider than [`WIDEST`]. It is asked of the parts an answer is made of, once they are in their one
//! form, and never of what was worked with on the way to them: the sum of two numbers of the widest
//! width is one bit wider than any number may be and is an ordinary value once its factor of two is
//! an exponent. What an operation has room for is the run's: a comparison or a rounding of values
//! that stand a billion exponents from one another is answered without building either, by knowing
//! each as well as the answer needs ([`Enclosure`]), and it is only where that has to be known to
//! more bits than the run can hold that the run is out of room. A [`Failure`] says which of the two
//! it was, so that neither can be taken for the other, and how each ends a run is the runtime's.
//!
//! Nothing here knows where a value is kept. A runtime stores the parts [`Ratio::parts`] answers in
//! whatever layout it has, and reads them back with [`Ratio::from_stored`].

use crate::WIDEST;
use crate::enclosure::Enclosure;
use crate::magnitude::Magnitude;
use crate::rounding::{Dropped, Rounding, dropped, rounded};
use core::cmp::Ordering;

/// `log2(5)` to sixteen places, below and above it, for how many bits a power of five is wide
/// without a floating-point number: an exponent is sixty-four bits, and a `f64` is not exact past
/// fifty-three.
const LOG2_5_BELOW: i128 = 23_219_280_948_873_623;
const LOG2_5_ABOVE: i128 = 23_219_280_948_873_624;
const PLACES: i128 = 10_000_000_000_000_000;

/// How many bits an order or a rounding may know a value to before the run is out of room for it.
/// A near tie needs as many bits as the two values are close to one another, and no pair of
/// values a program makes is anywhere near as close as this asks.
const MOST_PRECISION: u64 = 1 << 24;

/// The bits of working room a comparison or a rounding builds in, beyond what the parts it works
/// from are wide, before it knows its values instead: a value at ordinary exponents is built and
/// compared exactly, which is cheaper than knowing it, and one at exponents past this is not
/// built at all.
const WORKING_ROOM: i128 = 1 << 16;

/// Why an operation answered nothing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Failure {
    /// The answer has no place: a form the carrier does not hold. The run ends for it, as an
    /// `Int` that overflows does.
    NoPlace,
    /// The run has no room for what the answer needed, which is a fact about the run and none
    /// about the value.
    NoRoom,
}

/// What an operation answers, or why it did not.
pub type Exact<T> = Result<T, Failure>;

/// A decimal as its parts: a sign, the whole number its digits write, and how many of them are
/// after the point. Nought has no sign.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Scaled {
    pub negative: bool,
    pub magnitude: Magnitude,
    pub scale: i32,
}

/// An exact rational, in the form that has each value once.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ratio {
    negative: bool,
    numerator: Magnitude,
    denominator: Magnitude,
    twos: i64,
    fives: i64,
}

/// The number, where it is no wider than `limit` bits.
fn held(magnitude: Magnitude, limit: u64) -> Exact<Magnitude> {
    if magnitude.bits() > limit {
        Err(Failure::NoPlace)
    } else {
        Ok(magnitude)
    }
}

/// `left · right`, where that is no wider than `limit` bits. Refused before it is built where it
/// could not be: the product is at least as wide as its factors' widths less one.
fn product(left: &Magnitude, right: &Magnitude, limit: u64) -> Exact<Magnitude> {
    if left.is_zero() || right.is_zero() {
        return Ok(Magnitude::ZERO);
    }
    if left.bits() + right.bits() - 1 > limit {
        return Err(Failure::NoPlace);
    }
    held(left.mul(right), limit)
}

/// `left / right`, for a `right` that divides it.
fn over(left: &Magnitude, right: &Magnitude) -> Magnitude {
    left.div_rem(right).0
}

/// Between which two counts of bits five to `fives`, which is not below nought, is wide.
fn power_bits(fives: i128) -> (i128, i128) {
    (
        fives * LOG2_5_BELOW / PLACES + 1,
        fives * LOG2_5_ABOVE / PLACES + 1,
    )
}

/// The bits `whole × 2^twos × 5^fives` is at most wide, without building it.
fn working_bits(whole: &Magnitude, twos: i128, fives: i128) -> i128 {
    whole.bits() as i128 + twos + power_bits(fives).1
}

/// `whole × 2^twos × 5^fives`, both exponents being at least nought, where that is no wider than
/// `limit` bits: exactly where it is not, and not by a count that is nearly it.
///
/// A number's width is the width of what it is made of, to within a bit, and a power of five is
/// `floor(fives · log2 5) + 1` bits, which is known to within a bit from a `log2 5` known to sixteen
/// places. So a number that is surely too wide is refused before it is built, one that is surely
/// not is built, and the few in between are built and asked: what is built is never more than
/// `limit` bits and the few the estimate could not tell apart, since nothing that is not too wide
/// by the estimate is built.
fn written(whole: &Magnitude, twos: i128, fives: i128, limit: u64) -> Exact<Magnitude> {
    assert!(
        twos >= 0 && fives >= 0,
        "only a power above nought is written out"
    );
    if whole.is_zero() {
        return Ok(Magnitude::ZERO);
    }
    let base = whole.bits() as i128 + twos;
    if base + power_bits(fives).0 - 1 > i128::from(limit) {
        return Err(Failure::NoPlace);
    }
    held(built(whole, twos, fives), limit)
}

/// `whole × 2^twos × 5^fives`, built, for a caller that has settled that it is a width the run has
/// room for.
fn built(whole: &Magnitude, twos: i128, fives: i128) -> Magnitude {
    whole
        .times_two_to(u64::try_from(twos).expect("a width the run has room for"))
        .times_five_to(u64::try_from(fives).expect("a width the run has room for"))
}

/// A sign and a magnitude that are the sum of two of them.
fn signed_sum(left: (bool, &Magnitude), right: (bool, &Magnitude)) -> (bool, Magnitude) {
    if left.0 == right.0 {
        return (left.0, left.1.add(right.1));
    }
    match left.1.cmp(right.1) {
        Ordering::Equal => (false, Magnitude::ZERO),
        Ordering::Greater => (left.0, left.1.sub(right.1)),
        Ordering::Less => (right.0, right.1.sub(left.1)),
    }
}

/// Between which two powers of two `numerator / denominator × 2^twos × 5^fives` stands: its base-2
/// logarithm is above the first and below the second, whatever the exponents are.
fn log_bounds(
    numerator: &Magnitude,
    denominator: &Magnitude,
    twos: i128,
    fives: i128,
) -> (i128, i128) {
    let across = numerator.bits() as i128 - denominator.bits() as i128 + twos;
    let (low, high) = if fives >= 0 {
        (
            fives * LOG2_5_BELOW / PLACES,
            fives * LOG2_5_ABOVE / PLACES + 1,
        )
    } else {
        (
            fives * LOG2_5_ABOVE / PLACES - 1,
            fives * LOG2_5_BELOW / PLACES,
        )
    };
    (across - 1 + low, across + 1 + high)
}

impl Ratio {
    pub const ZERO: Ratio = Ratio {
        negative: false,
        numerator: Magnitude::ZERO,
        denominator: Magnitude::ONE,
        twos: 0,
        fives: 0,
    };

    /// The one form of `numerator × 2^twos × 5^fives / denominator`, which is not over nought.
    ///
    /// The limit is asked of what comes out and not of what went in: a numerator of a width `limit`
    /// bits and no more, doubled, is a bit wider than that and has a factor of two in it, and its
    /// answer is the numerator and one more power of two.
    fn canonical(
        negative: bool,
        numerator: Magnitude,
        denominator: Magnitude,
        mut twos: i128,
        mut fives: i128,
        limit: u64,
    ) -> Exact<Ratio> {
        assert!(!denominator.is_zero(), "a rational is not over nought");
        if numerator.is_zero() {
            return Ok(Ratio::ZERO);
        }
        let common = numerator.gcd(&denominator);
        let (mut numerator, mut denominator) = if common == Magnitude::ONE {
            (numerator, denominator)
        } else {
            (over(&numerator, &common), over(&denominator, &common))
        };
        // The two are coprime by now, so a factor of two or of five is on one of them alone.
        let by = numerator.twos();
        if by > 0 {
            numerator = numerator.shifted_down(by);
            twos += i128::from(by);
        }
        let by = denominator.twos();
        if by > 0 {
            denominator = denominator.shifted_down(by);
            twos -= i128::from(by);
        }
        let (stripped, by) = numerator.without_fives();
        numerator = stripped;
        fives += i128::from(by);
        let (stripped, by) = denominator.without_fives();
        denominator = stripped;
        fives -= i128::from(by);
        Ok(Ratio {
            negative,
            numerator: held(numerator, limit)?,
            denominator: held(denominator, limit)?,
            twos: i64::try_from(twos).map_err(|_| Failure::NoPlace)?,
            fives: i64::try_from(fives).map_err(|_| Failure::NoPlace)?,
        })
    }

    /// `Rational.fromInt`.
    pub fn of_int(value: i64) -> Ratio {
        Ratio::canonical(
            value < 0,
            Magnitude::of_u128(u128::from(value.unsigned_abs())),
            Magnitude::ONE,
            0,
            0,
            WIDEST,
        )
        .expect("every Int has a rational")
    }

    /// `Rational.fromDecimal`: the scale is negated into both exponents and nothing is built from
    /// it.
    ///
    /// # Panics
    ///
    /// Where the decimal's whole number is wider than [`WIDEST`], which no `Decimal` is.
    pub fn of_decimal(decimal: Scaled) -> Ratio {
        let exponent = -i128::from(decimal.scale);
        Ratio::canonical(
            decimal.negative,
            decimal.magnitude,
            Magnitude::ONE,
            exponent,
            exponent,
            WIDEST,
        )
        .expect("every Decimal has a rational")
    }

    /// The value a runtime stored the [`Ratio::parts`] of.
    ///
    /// Taken as they are, since they were a value's own: putting parts back in their one form is
    /// the work every operation has already done, and reading a stored value is not an operation.
    /// Parts that are not one value's own make a value no operation here answers for.
    pub fn from_stored(
        negative: bool,
        numerator: Magnitude,
        denominator: Magnitude,
        twos: i64,
        fives: i64,
    ) -> Ratio {
        debug_assert!(
            Ratio::canonical(
                negative,
                numerator.clone(),
                denominator.clone(),
                i128::from(twos),
                i128::from(fives),
                u64::MAX,
            )
            .is_ok_and(|it| it
                == Ratio {
                    negative,
                    numerator: numerator.clone(),
                    denominator: denominator.clone(),
                    twos,
                    fives,
                }),
            "stored parts are one value's own"
        );
        Ratio {
            negative,
            numerator,
            denominator,
            twos,
            fives,
        }
    }

    /// The parts this value is: whether it is below nought, the numerator, the denominator, and
    /// the powers of two and of five. Equal values have equal parts.
    pub fn parts(&self) -> (bool, &Magnitude, &Magnitude, i64, i64) {
        (
            self.negative,
            &self.numerator,
            &self.denominator,
            self.twos,
            self.fives,
        )
    }

    pub fn is_zero(&self) -> bool {
        self.numerator.is_zero()
    }

    fn signum(&self) -> i8 {
        if self.is_zero() {
            0
        } else if self.negative {
            -1
        } else {
            1
        }
    }

    /// Whether this is a whole number.
    pub fn is_whole(&self) -> bool {
        self.denominator == Magnitude::ONE && self.twos >= 0 && self.fives >= 0
    }

    /// Whether this has a finite decimal spelling: a denominator with no factor left that ten is
    /// not made of.
    pub fn has_finite_decimal(&self) -> bool {
        self.denominator == Magnitude::ONE
    }

    pub fn negated(&self) -> Ratio {
        Ratio {
            negative: !self.negative && !self.is_zero(),
            ..self.clone()
        }
    }

    fn multiply_within(&self, other: &Ratio, limit: u64) -> Exact<Ratio> {
        if self.is_zero() || other.is_zero() {
            return Ok(Ratio::ZERO);
        }
        let across_one = self.numerator.gcd(&other.denominator);
        let across_two = other.numerator.gcd(&self.denominator);
        Ratio::canonical(
            self.negative != other.negative,
            product(
                &over(&self.numerator, &across_one),
                &over(&other.numerator, &across_two),
                limit,
            )?,
            product(
                &over(&self.denominator, &across_two),
                &over(&other.denominator, &across_one),
                limit,
            )?,
            i128::from(self.twos) + i128::from(other.twos),
            i128::from(self.fives) + i128::from(other.fives),
            limit,
        )
    }

    /// `*`.
    pub fn multiply(&self, other: &Ratio) -> Exact<Ratio> {
        self.multiply_within(other, WIDEST)
    }

    fn divide_within(&self, divisor: &Ratio, limit: u64) -> Exact<Ratio> {
        assert!(
            !divisor.is_zero(),
            "a zero divisor is answered as an abort and never divided by"
        );
        if self.is_zero() {
            return Ok(Ratio::ZERO);
        }
        let across_one = self.numerator.gcd(&divisor.numerator);
        let across_two = self.denominator.gcd(&divisor.denominator);
        Ratio::canonical(
            self.negative != divisor.negative,
            product(
                &over(&self.numerator, &across_one),
                &over(&divisor.denominator, &across_two),
                limit,
            )?,
            product(
                &over(&self.denominator, &across_two),
                &over(&divisor.numerator, &across_one),
                limit,
            )?,
            i128::from(self.twos) - i128::from(divisor.twos),
            i128::from(self.fives) - i128::from(divisor.fives),
            limit,
        )
    }

    /// `/`, over a divisor that is not nought: a zero divisor is the caller's to end the run for,
    /// as the language says the operator does.
    ///
    /// # Panics
    ///
    /// Where the divisor is nought.
    pub fn divide(&self, divisor: &Ratio) -> Exact<Ratio> {
        self.divide_within(divisor, WIDEST)
    }

    fn add_within(&self, other: &Ratio, limit: u64) -> Exact<Ratio> {
        if self.is_zero() {
            return Ok(other.clone());
        }
        if other.is_zero() {
            return Ok(self.clone());
        }
        // The lesser of each pair of exponents is common to both terms and stays an exponent. What
        // is left is the distance between them, and that is built: the exact sum is a number with
        // that many digits in it, which the sum of a `Rational` is defined to write out in full.
        let twos = self.twos.min(other.twos);
        let fives = self.fives.min(other.fives);
        let here = written(
            &self.numerator,
            i128::from(self.twos) - i128::from(twos),
            i128::from(self.fives) - i128::from(fives),
            limit,
        )?;
        let there = written(
            &other.numerator,
            i128::from(other.twos) - i128::from(twos),
            i128::from(other.fives) - i128::from(fives),
            limit,
        )?;
        let shared = self.denominator.gcd(&other.denominator);
        let over_this = over(&self.denominator, &shared);
        let here = product(&here, &over(&other.denominator, &shared), limit)?;
        let there = product(&there, &over_this, limit)?;
        // The sum may be a bit wider than either term, and is not asked for its width until it is
        // in its one form, where a factor of two it has is an exponent.
        let (negative, sum) = signed_sum((self.negative, &here), (other.negative, &there));
        Ratio::canonical(
            negative,
            sum,
            product(&over_this, &other.denominator, limit)?,
            i128::from(twos),
            i128::from(fives),
            limit,
        )
    }

    /// `+`.
    pub fn add(&self, other: &Ratio) -> Exact<Ratio> {
        self.add_within(other, WIDEST)
    }

    /// `-`.
    pub fn subtract(&self, other: &Ratio) -> Exact<Ratio> {
        self.add(&other.negated())
    }

    /// This value's magnitude at exponents other than its own, known to `precision` bits, which is
    /// how it is worked with where it is not built. Nothing where that precision is too little to
    /// have a divisor above nought.
    fn enclosed(&self, twos: i128, fives: i128, precision: u64) -> Option<Enclosure> {
        let mut above = Enclosure::of(&self.numerator, precision);
        let mut below = Enclosure::of(&self.denominator, precision);
        let power = Enclosure::five_to(fives.unsigned_abs(), precision);
        if fives >= 0 {
            above = above.times(&power, precision);
        } else {
            below = below.times(&power, precision);
        }
        Some(above.over(&below, precision)?.times_two_to(twos))
    }

    /// How many bits the parts of the two are, which is what an order of them is a work of at the
    /// least, and so what it may be given room for beyond the room ordinary exponents need.
    fn parts_bits(&self, other: &Ratio) -> i128 {
        (self.numerator.bits()
            + self.denominator.bits()
            + other.numerator.bits()
            + other.denominator.bits()) as i128
    }

    /// Where the magnitude stands against `other`'s, by knowing each of the two to more bits until
    /// that says. Never by building either: this is what answers the pair no exponents the run can
    /// build are close enough to answer, and the pair every other is answered by cheaper.
    fn compare_by_enclosure(&self, other: &Ratio) -> Exact<Ordering> {
        let most = MOST_PRECISION + self.parts_bits(other) as u64;
        let mut precision = 256;
        loop {
            let here = self.enclosed(i128::from(self.twos), i128::from(self.fives), precision);
            let there = other.enclosed(i128::from(other.twos), i128::from(other.fives), precision);
            if let (Some(here), Some(there)) = (here, there)
                && let Some(ordering) = here.against(&there)
            {
                return Ok(ordering);
            }
            precision *= 2;
            if precision > most {
                return Err(Failure::NoRoom);
            }
        }
    }

    /// Where the magnitude stands against `other`'s, by the cross product of the two where that is
    /// a width the pair is worked at as a matter of course, and by [`Ratio::compare_by_enclosure`]
    /// where it is not.
    fn compare_magnitudes(&self, other: &Ratio) -> Exact<Ordering> {
        let (low, high) = log_bounds(
            &self.numerator,
            &self.denominator,
            i128::from(self.twos),
            i128::from(self.fives),
        );
        let (other_low, other_high) = log_bounds(
            &other.numerator,
            &other.denominator,
            i128::from(other.twos),
            i128::from(other.fives),
        );
        if high < other_low {
            return Ok(Ordering::Less);
        }
        if low > other_high {
            return Ok(Ordering::Greater);
        }
        let twos = i128::from(self.twos) - i128::from(other.twos);
        let fives = i128::from(self.fives) - i128::from(other.fives);
        let here = working_bits(&self.numerator, twos.max(0), fives.max(0))
            + other.denominator.bits() as i128;
        let there = working_bits(&other.numerator, (-twos).max(0), (-fives).max(0))
            + self.denominator.bits() as i128;
        let room = WORKING_ROOM + self.parts_bits(other);
        if here > room || there > room {
            return self.compare_by_enclosure(other);
        }
        let left = built(
            &self.numerator.mul(&other.denominator),
            twos.max(0),
            fives.max(0),
        );
        let right = built(
            &other.numerator.mul(&self.denominator),
            (-twos).max(0),
            (-fives).max(0),
        );
        Ok(left.cmp(&right))
    }

    /// Where this stands against `other` by exact value. Only ever [`Failure::NoRoom`]: two values
    /// stand in an order whatever they are, so an order has an answer for every pair, and what it
    /// can want is the room to find it — two values that close, at exponents that far apart.
    pub fn compare(&self, other: &Ratio) -> Exact<Ordering> {
        if self == other {
            return Ok(Ordering::Equal);
        }
        let by_sign = self.signum().cmp(&other.signum());
        if by_sign != Ordering::Equal {
            return Ok(by_sign);
        }
        let by_magnitude = self.compare_magnitudes(other)?;
        Ok(if self.negative {
            by_magnitude.reverse()
        } else {
            by_magnitude
        })
    }

    /// The whole number of the value at exponents `twos` and `fives` rounds to, and what rounding
    /// dropped, from what the two parts of it are built to: the numerator over the denominator,
    /// each with the powers that are not below nought.
    fn rounded_exactly(&self, twos: i128, fives: i128) -> (Magnitude, Dropped) {
        let up = built(&self.numerator, twos.max(0), fives.max(0));
        let down = built(&self.denominator, (-twos).max(0), (-fives).max(0));
        let (quotient, remainder) = up.div_rem(&down);
        let left = dropped(&remainder, &down);
        (quotient, left)
    }

    /// The same, without building the two parts: by knowing the value to more bits until the half
    /// of a whole number it stands in is settled. A value a whole number or a half exactly is
    /// never one this is asked of, since building it is no wider than it is, and the value itself
    /// is not settled by any number of bits.
    fn rounded_by_enclosure(
        &self,
        twos: i128,
        fives: i128,
        answer_bits: u64,
    ) -> Exact<(Magnitude, Dropped)> {
        let most = MOST_PRECISION + answer_bits + self.parts_bits(self) as u64;
        let mut precision = answer_bits + 192;
        loop {
            if let Some(enclosed) = self.enclosed(twos, fives, precision)
                && let Some(halves) = enclosed.halves()
            {
                let dropped = if halves.is_odd() {
                    Dropped::AboveHalf
                } else {
                    Dropped::BelowHalf
                };
                return Ok((halves.shifted_down(1), dropped));
            }
            precision *= 2;
            if precision > most {
                return Err(Failure::NoRoom);
            }
        }
    }

    /// The whole number the magnitude of the value at `scale` rounds to by `mode`, where that is
    /// no wider than `limit` bits. The scale goes to the exponents and nothing is built from it,
    /// so a value far below the unit rounds to nought without the power that would have said so,
    /// and one that stands at exponents nothing can be built at is rounded from what is known of it.
    fn rounded_at(&self, scale: i32, mode: Rounding, limit: u64) -> Exact<Magnitude> {
        if self.is_zero() {
            return Ok(Magnitude::ZERO);
        }
        let twos = i128::from(self.twos) + i128::from(scale);
        let fives = i128::from(self.fives) + i128::from(scale);
        let (low, high) = log_bounds(&self.numerator, &self.denominator, twos, fives);
        // Below an eighth of the unit, which is below half of it.
        if high < -3 {
            return held(
                rounded(Magnitude::ZERO, self.negative, Dropped::BelowHalf, mode),
                limit,
            );
        }
        if low > i128::from(limit) + 1 {
            return Err(Failure::NoPlace);
        }
        // What the answer is wide enough to be, and so what building the two parts may be as wide
        // as before the value is known instead: the answer has to be written out whatever is done.
        let answer = high.max(0);
        let room =
            answer + WORKING_ROOM + (self.numerator.bits() + self.denominator.bits()) as i128;
        let up = working_bits(&self.numerator, twos.max(0), fives.max(0));
        let down = working_bits(&self.denominator, (-twos).max(0), (-fives).max(0));
        let (quotient, left) = if up <= room && down <= room {
            self.rounded_exactly(twos, fives)
        } else {
            self.rounded_by_enclosure(twos, fives, answer as u64)?
        };
        held(rounded(quotient, self.negative, left, mode), limit)
    }

    /// An `Int`, where a magnitude and a sign name one.
    fn as_int(&self, magnitude: &Magnitude) -> Exact<i64> {
        let magnitude = magnitude
            .as_u128()
            .and_then(|small| u64::try_from(small).ok())
            .ok_or(Failure::NoPlace)?;
        if self.negative {
            0i64.checked_sub_unsigned(magnitude)
        } else {
            i64::try_from(magnitude).ok()
        }
        .ok_or(Failure::NoPlace)
    }

    /// `Rational.toWholeNumber` of a whole number: no place where it is past every `Int`.
    ///
    /// # Panics
    ///
    /// Where this is not a whole number, which is the case the language answers and never a value
    /// read as one.
    pub fn to_whole(&self) -> Exact<i64> {
        assert!(
            self.is_whole(),
            "a fraction is answered as a case and never read as whole"
        );
        let (low, _) = log_bounds(
            &self.numerator,
            &self.denominator,
            i128::from(self.twos),
            i128::from(self.fives),
        );
        if low > 65 {
            return Err(Failure::NoPlace);
        }
        let whole = written(
            &self.numerator,
            i128::from(self.twos),
            i128::from(self.fives),
            WIDEST,
        )?;
        self.as_int(&whole)
    }

    /// `Rational.toFiniteDecimal` of a value that has one: at the least scale a `Decimal` holds
    /// that writes it, with what is left of the powers among its digits. No place where no scale
    /// does.
    ///
    /// # Panics
    ///
    /// Where this has no finite decimal, which is the case the language answers and never a value
    /// read as one.
    pub fn to_finite_decimal(&self) -> Exact<Scaled> {
        assert!(
            self.has_finite_decimal(),
            "a repeating fraction is answered as a case and never read as a decimal"
        );
        let tens = i128::from(self.twos.min(self.fives));
        if tens < -i128::from(i32::MAX) {
            return Err(Failure::NoPlace);
        }
        let scale = if tens > i128::from(i32::MAX) + 1 {
            i32::MIN
        } else {
            (-tens) as i32
        };
        let magnitude = written(
            &self.numerator,
            i128::from(self.twos) + i128::from(scale),
            i128::from(self.fives) + i128::from(scale),
            WIDEST,
        )?;
        Ok(Scaled {
            negative: self.negative,
            magnitude,
            scale,
        })
    }

    /// `Rational.toInt`: the whole number the value rounds to by `mode`. No place where that is not
    /// an `Int`.
    pub fn to_int(&self, mode: Rounding) -> Exact<i64> {
        let whole = self.rounded_at(0, mode, 64)?;
        self.as_int(&whole)
    }

    /// `Rational.toDecimal`: the value at `scale` places, rounded by `mode`. No place where the
    /// scale is not one a `Decimal` has or the value at it is wider than [`WIDEST`].
    pub fn to_decimal(&self, scale: i64, mode: Rounding) -> Exact<Scaled> {
        let scale = i32::try_from(scale).map_err(|_| Failure::NoPlace)?;
        let magnitude = self.rounded_at(scale, mode, WIDEST)?;
        Ok(Scaled {
            negative: self.negative && !magnitude.is_zero(),
            magnitude,
            scale,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn whole(n: i64) -> Ratio {
        Ratio::of_int(n)
    }

    fn ratio_of(n: i64, d: i64) -> Ratio {
        whole(n)
            .divide(&whole(d))
            .expect("a small quotient has a place")
    }

    fn small(n: u128) -> Magnitude {
        Magnitude::of_u128(n)
    }

    fn decimal(negative: bool, digits: u128, scale: i32) -> Scaled {
        Scaled {
            negative: negative && digits != 0,
            magnitude: small(digits),
            scale,
        }
    }

    fn of_decimal(negative: bool, digits: u128, scale: i32) -> Ratio {
        Ratio::of_decimal(decimal(negative, digits, scale))
    }

    #[test]
    fn a_value_has_one_form_whatever_it_was_written_as() {
        assert_eq!(ratio_of(6, 4), ratio_of(3, 2));
        assert_eq!(ratio_of(-6, 4), ratio_of(3, -2));
        assert_eq!(ratio_of(0, 7), Ratio::ZERO);
        assert_eq!(ratio_of(4, 2), whole(2));
        // A half is a one and a power of two, with no denominator left.
        let half = ratio_of(1, 2);
        assert_eq!((half.twos, half.fives), (-1, 0));
        assert_eq!(half.denominator, Magnitude::ONE);
        // A decimal and the ratio of the same value are one value: 0.5 is 5 at scale 1.
        assert_eq!(of_decimal(false, 5, 1), half);
        assert_eq!(of_decimal(false, 50, 2), half);
        assert_eq!(of_decimal(false, 0, 9), Ratio::ZERO);
    }

    #[test]
    fn what_is_stored_reads_back_as_what_it_was() {
        for value in [
            Ratio::ZERO,
            ratio_of(1, 3),
            ratio_of(-7, 12),
            whole(i64::MIN),
            of_decimal(true, 9, i32::MIN),
            of_decimal(false, 1, i32::MAX),
        ] {
            let (negative, numerator, denominator, twos, fives) = value.parts();
            let stored = Ratio::from_stored(
                negative,
                numerator.clone(),
                denominator.clone(),
                twos,
                fives,
            );
            assert_eq!(stored, value);
        }
    }

    #[test]
    fn the_four_operations_are_exact() {
        let half = ratio_of(1, 2);
        let third = ratio_of(1, 3);
        assert_eq!(half.add(&third), Ok(ratio_of(5, 6)));
        assert_eq!(half.subtract(&third), Ok(ratio_of(1, 6)));
        assert_eq!(third.subtract(&half), Ok(ratio_of(-1, 6)));
        assert_eq!(third.multiply(&whole(3)), Ok(whole(1)));
        assert_eq!(third.divide(&third), Ok(whole(1)));
        assert_eq!(half.subtract(&half), Ok(Ratio::ZERO));
        assert_eq!(ratio_of(-1, 2).add(&half), Ok(Ratio::ZERO));
        assert_eq!(ratio_of(-2, 3).multiply(&ratio_of(-3, 4)), Ok(half.clone()));
        assert_eq!(half.negated().negated(), half);
        assert_eq!(Ratio::ZERO.negated(), Ratio::ZERO);
        // A tenth and a fifth: the sum has a five in it that comes off.
        assert_eq!(
            of_decimal(false, 1, 1).add(&of_decimal(false, 2, 1)),
            Ok(of_decimal(false, 3, 1))
        );
    }

    #[test]
    fn an_order_is_by_exact_value() {
        assert_eq!(ratio_of(1, 3).compare(&ratio_of(1, 2)), Ok(Ordering::Less));
        assert_eq!(
            ratio_of(-1, 2).compare(&ratio_of(-1, 3)),
            Ok(Ordering::Less)
        );
        assert_eq!(ratio_of(-1, 2).compare(&ratio_of(1, 3)), Ok(Ordering::Less));
        assert_eq!(ratio_of(2, 4).compare(&ratio_of(1, 2)), Ok(Ordering::Equal));
        assert_eq!(Ratio::ZERO.compare(&ratio_of(-1, 9)), Ok(Ordering::Greater));
        // Close enough that no logarithm settles it.
        let near = whole(i64::MAX).divide(&whole(i64::MAX - 1)).unwrap();
        assert_eq!(near.compare(&whole(1)), Ok(Ordering::Greater));
        assert_eq!(whole(1).compare(&near), Ok(Ordering::Less));
    }

    #[test]
    fn a_scale_at_the_end_of_its_range_is_an_exponent_and_nothing_is_built() {
        let least = of_decimal(false, 1, i32::MAX);
        assert_eq!(
            (least.twos, least.fives),
            (-i64::from(i32::MAX), -i64::from(i32::MAX))
        );
        let most = of_decimal(false, 1, i32::MIN);
        assert_eq!((most.twos, most.fives), (1 << 31, 1 << 31));
        assert_eq!(least.compare(&whole(1)), Ok(Ordering::Less));
        assert_eq!(most.compare(&whole(1)), Ok(Ordering::Greater));
        assert_eq!(most.negated().compare(&least), Ok(Ordering::Less));
        // A scale's negation reaches one further than its own end, so this is ten and not one.
        assert_eq!(least.multiply(&most), Ok(whole(10)));
        assert_eq!(least.divide(&least), Ok(whole(1)));
        // The sum is a number with two billion digits in it, which no `Decimal` holds.
        assert_eq!(whole(1).add(&least), Err(Failure::NoPlace));
    }

    #[test]
    fn an_exponent_past_sixty_four_bits_has_no_place() {
        let mut power = of_decimal(false, 1, i32::MIN);
        // Squaring doubles the exponent: 2^31, 2^32, ... 2^63 is past a signed exponent.
        let mut refused = false;
        for _ in 0..40 {
            match power.multiply(&power) {
                Ok(next) => power = next,
                Err(failure) => {
                    assert_eq!(failure, Failure::NoPlace);
                    refused = true;
                    break;
                }
            }
        }
        assert!(refused);
    }

    #[test]
    fn what_is_whole_and_what_has_a_finite_decimal() {
        assert!(ratio_of(4, 2).is_whole());
        assert!(!ratio_of(3, 2).is_whole());
        assert!(!ratio_of(1, 3).is_whole());
        assert!(ratio_of(1, 2).has_finite_decimal());
        assert!(ratio_of(1, 5).has_finite_decimal());
        assert!(!ratio_of(1, 3).has_finite_decimal());
        assert!(!ratio_of(1, 6).has_finite_decimal());
        assert!(of_decimal(false, 1, 5).has_finite_decimal());
        assert!(!of_decimal(false, 1, 5).is_whole());
        assert!(of_decimal(false, 1, -5).is_whole());
    }

    #[test]
    fn a_whole_number_is_an_int_where_an_int_holds_it() {
        assert_eq!(whole(0).to_whole(), Ok(0));
        assert_eq!(whole(i64::MIN).to_whole(), Ok(i64::MIN));
        assert_eq!(whole(i64::MAX).to_whole(), Ok(i64::MAX));
        assert_eq!(
            whole(i64::MAX).add(&whole(1)).unwrap().to_whole(),
            Err(Failure::NoPlace)
        );
        assert_eq!(
            whole(i64::MIN).subtract(&whole(1)).unwrap().to_whole(),
            Err(Failure::NoPlace)
        );
        assert_eq!(of_decimal(true, 7, -3).to_whole(), Ok(-7000));
        assert_eq!(
            of_decimal(false, 1, i32::MIN).to_whole(),
            Err(Failure::NoPlace)
        );
    }

    #[test]
    fn a_finite_decimal_is_written_at_the_least_scale_that_writes_it() {
        assert_eq!(ratio_of(1, 2).to_finite_decimal(), Ok(decimal(false, 5, 1)));
        assert_eq!(
            ratio_of(-1, 4).to_finite_decimal(),
            Ok(decimal(true, 25, 2))
        );
        assert_eq!(whole(3).to_finite_decimal(), Ok(decimal(false, 3, 0)));
        assert_eq!(Ratio::ZERO.to_finite_decimal(), Ok(decimal(false, 0, 0)));
        // 3000 is 3 at scale -3: the least scale that writes it.
        assert_eq!(whole(3000).to_finite_decimal(), Ok(decimal(false, 3, -3)));
        assert_eq!(
            of_decimal(false, 12, 40).to_finite_decimal(),
            Ok(decimal(false, 12, 40))
        );
        // A scale at the end of the range is a scale a `Decimal` has.
        assert_eq!(
            of_decimal(false, 1, i32::MAX).to_finite_decimal(),
            Ok(decimal(false, 1, i32::MAX))
        );
    }

    #[test]
    fn a_value_with_a_fraction_is_rounded_by_the_mode_it_is_told() {
        let five_halves = ratio_of(5, 2);
        assert_eq!(five_halves.to_int(Rounding::HalfEven), Ok(2));
        assert_eq!(five_halves.to_int(Rounding::HalfUp), Ok(3));
        assert_eq!(five_halves.to_int(Rounding::HalfDown), Ok(2));
        assert_eq!(five_halves.to_int(Rounding::Down), Ok(2));
        assert_eq!(five_halves.to_int(Rounding::Up), Ok(3));
        assert_eq!(ratio_of(-5, 2).to_int(Rounding::HalfUp), Ok(-3));
        assert_eq!(ratio_of(-5, 2).to_int(Rounding::Ceiling), Ok(-2));
        assert_eq!(ratio_of(-5, 2).to_int(Rounding::Floor), Ok(-3));
        assert_eq!(ratio_of(-1, 3).to_int(Rounding::Ceiling), Ok(0));
        assert_eq!(whole(7).to_int(Rounding::Up), Ok(7));
        assert_eq!(
            whole(i64::MAX).add(&whole(1)).unwrap().to_int(Rounding::Up),
            Err(Failure::NoPlace)
        );

        assert_eq!(
            ratio_of(1, 3).to_decimal(2, Rounding::HalfUp),
            Ok(decimal(false, 33, 2))
        );
        assert_eq!(
            ratio_of(2, 3).to_decimal(2, Rounding::HalfUp),
            Ok(decimal(false, 67, 2))
        );
        assert_eq!(
            ratio_of(2, 3).to_decimal(0, Rounding::Down),
            Ok(decimal(false, 0, 0))
        );
        assert_eq!(
            ratio_of(-1, 3).to_decimal(2, Rounding::Down),
            Ok(decimal(true, 33, 2))
        );
        // Rounded to nought, it has no sign.
        assert_eq!(
            ratio_of(-1, 3).to_decimal(0, Rounding::Down),
            Ok(decimal(false, 0, 0))
        );
        assert_eq!(
            ratio_of(1, 8).to_decimal(2, Rounding::HalfEven),
            Ok(decimal(false, 12, 2))
        );
        assert_eq!(
            ratio_of(1, 8).to_decimal(2, Rounding::HalfUp),
            Ok(decimal(false, 13, 2))
        );
        // A negative scale is a grid of tens.
        assert_eq!(
            whole(1234).to_decimal(-2, Rounding::HalfUp),
            Ok(decimal(false, 12, -2))
        );
        assert_eq!(
            ratio_of(1, 3).to_decimal(i64::from(i32::MAX) + 1, Rounding::Down),
            Err(Failure::NoPlace)
        );
    }

    #[test]
    fn a_value_far_below_the_unit_rounds_without_the_power_that_says_so() {
        let tiny = of_decimal(false, 1, i32::MAX);
        assert_eq!(tiny.to_int(Rounding::Down), Ok(0));
        assert_eq!(tiny.to_int(Rounding::HalfUp), Ok(0));
        assert_eq!(tiny.to_int(Rounding::Up), Ok(1));
        assert_eq!(tiny.negated().to_int(Rounding::Floor), Ok(-1));
        assert_eq!(tiny.negated().to_int(Rounding::Down), Ok(0));
        assert_eq!(tiny.to_decimal(0, Rounding::Up), Ok(decimal(false, 1, 0)));
        // At its own scale it is what it was.
        assert_eq!(
            tiny.to_decimal(i64::from(i32::MAX), Rounding::Down),
            Ok(decimal(false, 1, i32::MAX))
        );
    }

    #[test]
    fn a_value_past_what_a_decimal_holds_has_no_place_at_a_scale() {
        let huge = of_decimal(false, 1, i32::MIN);
        assert_eq!(huge.to_decimal(0, Rounding::Down), Err(Failure::NoPlace));
        assert_eq!(huge.to_int(Rounding::Down), Err(Failure::NoPlace));
    }

    /// The digits as a decimal at `scale`.
    fn digits_at(digits: &str, scale: i32) -> Scaled {
        Scaled {
            negative: false,
            magnitude: Magnitude::of_digits(digits.as_bytes()),
            scale,
        }
    }

    /// `2^2147483648 / 5^924870866`, which is 1.06569530465881019317…: a value whose parts are one
    /// and one and whose two powers no run can write down. It is a value with a place, and is
    /// ordered and rounded as one, from what is known of it.
    #[test]
    fn a_value_at_exponents_nothing_is_built_at_is_ordered_and_rounded_by_what_is_known_of_it() {
        let close = Ratio::canonical(
            false,
            Magnitude::ONE,
            Magnitude::ONE,
            2_147_483_648,
            -924_870_866,
            WIDEST,
        )
        .expect("a value whose parts are one and one and whose exponents are Ints");
        assert_eq!(close.compare(&whole(1)), Ok(Ordering::Greater));
        assert_eq!(whole(1).compare(&close), Ok(Ordering::Less));
        assert_eq!(close.compare(&whole(2)), Ok(Ordering::Less));
        assert_eq!(close.negated().compare(&whole(-1)), Ok(Ordering::Less));
        assert_eq!(
            close.compare(&close.multiply(&whole(1)).unwrap()),
            Ok(Ordering::Equal)
        );
        assert_eq!(close.to_int(Rounding::HalfEven), Ok(1));
        assert_eq!(close.to_int(Rounding::Up), Ok(2));
        assert_eq!(close.to_int(Rounding::Down), Ok(1));
        assert_eq!(close.negated().to_int(Rounding::Floor), Ok(-2));
        assert_eq!(
            close.to_decimal(10, Rounding::HalfEven),
            Ok(digits_at("10656953047", 10))
        );
        assert_eq!(
            close.to_decimal(20, Rounding::HalfEven),
            Ok(digits_at("106569530465881019317", 20))
        );
        // Ordered against a decimal that is close to it too: 1.0656953046588101931 is below, and
        // 1.0656953046588101932 above.
        let below = Ratio::of_decimal(digits_at("10656953046588101931", 19));
        let above = Ratio::of_decimal(digits_at("10656953046588101932", 19));
        assert_eq!(close.compare(&below), Ok(Ordering::Greater));
        assert_eq!(close.compare(&above), Ok(Ordering::Less));
    }

    /// The sum of two numbers as wide as a number may be is a bit wider than any may be and an
    /// ordinary value once its factor of two is an exponent: the limit is asked of the answer, and
    /// not of what was worked with.
    #[test]
    fn a_sum_a_bit_wider_than_a_part_may_be_is_a_value_where_a_factor_of_two_is_an_exponent() {
        let limit = 64;
        let widest = small(u128::from(u64::MAX) - 2);
        let made = |numerator: Magnitude| {
            Ratio::canonical(false, numerator, Magnitude::ONE, 0, 0, limit).expect("in its limit")
        };
        let odd = made(widest.clone());
        let doubled = odd
            .add_within(&odd, limit)
            .expect("twice a number is a number");
        assert_eq!(
            (doubled.numerator.clone(), doubled.twos),
            (widest.clone(), 1)
        );
        // 2^64 - 3 and 2^64 - 5 come to 8 × (2^62 - 1).
        let other = made(small(u128::from(u64::MAX) - 4));
        let summed = odd
            .add_within(&other, limit)
            .expect("its parts are in the limit");
        assert_eq!((summed.numerator, summed.twos), (small((1 << 62) - 1), 3));
        // An odd sum of that width has no factor of two to give, and no place.
        let four = made(small(4)).add_within(&odd, limit);
        assert_eq!(four, Err(Failure::NoPlace));
        // And a product a bit wider does not.
        assert_eq!(odd.multiply_within(&odd, limit), Err(Failure::NoPlace));
    }

    /// What a power is written out as is refused exactly where it is too wide, and not by a count
    /// that is nearly the width.
    #[test]
    fn a_power_is_written_out_where_it_is_no_wider_than_the_limit() {
        for whole in [1u128, 3, 1000] {
            for twos in [0i128, 1, 7, 70] {
                for fives in 0..130i128 {
                    let made = built(&small(whole), twos, fives);
                    for limit in made.bits().saturating_sub(3)..made.bits() + 3 {
                        let written = written(&small(whole), twos, fives, limit);
                        assert_eq!(
                            written.is_ok(),
                            made.bits() <= limit,
                            "{whole} × 2^{twos} × 5^{fives} at {limit}"
                        );
                    }
                }
            }
        }
    }

    /// A small deterministic source of numbers, which is all a differential test needs.
    struct Lcg(u64);

    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            self.0 >> 11
        }

        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }

        fn ratio(&mut self, bits: u32) -> Ratio {
            let numerator = 1 + self.below((1u64 << bits) - 1);
            let denominator = 1 + self.below((1u64 << bits) - 1);
            Ratio::canonical(
                self.below(2) == 1,
                small(u128::from(numerator)),
                small(u128::from(denominator)),
                i128::from(self.below(161)) - 80,
                i128::from(self.below(161)) - 80,
                WIDEST,
            )
            .expect("small parts and exponents")
        }
    }

    /// The order of two magnitudes by building both, which is what the enclosures are held to.
    fn built_order(one: &Ratio, other: &Ratio) -> Ordering {
        let twos = i128::from(one.twos) - i128::from(other.twos);
        let fives = i128::from(one.fives) - i128::from(other.fives);
        let left = built(
            &one.numerator.mul(&other.denominator),
            twos.max(0),
            fives.max(0),
        );
        let right = built(
            &other.numerator.mul(&one.denominator),
            (-twos).max(0),
            (-fives).max(0),
        );
        left.cmp(&right)
    }

    /// An order by what is known of two values is the order of the values, which building them
    /// answers: over pairs at random and over pairs that are a part apart, and across the sizes
    /// at which the enclosures need one precision and the next.
    #[test]
    fn an_order_by_enclosure_is_the_order_by_building() {
        let mut random = Lcg(7);
        for round in 0..1500 {
            let one = random.ratio(if round % 3 == 0 { 62 } else { 12 });
            let other = if round % 2 == 0 {
                random.ratio(12)
            } else {
                // The same value with one part a step off, which no coarse bound tells apart.
                let step = small(1 + u128::from(random.below(3)));
                Ratio::canonical(
                    one.negative,
                    one.numerator.add(&step),
                    one.denominator.clone(),
                    i128::from(one.twos),
                    i128::from(one.fives),
                    WIDEST,
                )
                .expect("a part a step off")
            };
            if one.negative != other.negative || one == other {
                continue;
            }
            assert_eq!(
                one.compare_by_enclosure(&other),
                Ok(built_order(&one, &other)),
                "{one:?} against {other:?}"
            );
            assert_eq!(
                one.compare_magnitudes(&other),
                Ok(built_order(&one, &other)),
                "{one:?} against {other:?}"
            );
        }
    }

    /// A rounding from what is known of the value is the rounding of building it, for every value
    /// that is not a whole number or a half exactly, which is never asked of it.
    #[test]
    fn a_rounding_by_enclosure_is_the_rounding_by_building() {
        let mut random = Lcg(11);
        for round in 0..1500 {
            let value = random.ratio(if round % 3 == 0 { 62 } else { 12 });
            let scale = random.below(9) as i128 - 4;
            let twos = i128::from(value.twos) + scale;
            let fives = i128::from(value.fives) + scale;
            let (quotient, left) = value.rounded_exactly(twos, fives);
            if matches!(left, Dropped::Nothing | Dropped::Half) {
                continue;
            }
            let (_, high) = log_bounds(&value.numerator, &value.denominator, twos, fives);
            let answer = high.max(0) as u64;
            assert_eq!(
                value.rounded_by_enclosure(twos, fives, answer),
                Ok((quotient, left)),
                "{value:?} at {scale}"
            );
        }
    }
}
