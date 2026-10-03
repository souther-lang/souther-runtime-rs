//! A positive value known to lie between two multiples of a power of two, and no more than that.
//!
//! What an order or a rounding of a `Rational` asks is where one value stands against another or
//! against a whole number, and a value whose exponents are billions apart is not answered by
//! building it: `2^2147483648 / 5^924870866` is a little over one, and neither of its two powers
//! can be written down in the room a `Decimal` gets. It is answered by knowing the value well
//! enough to say which side it is on, and knowing it better only where that has not said.
//!
//! An enclosure is `[low, high] × 2^exp`, and every operation on one answers an enclosure of what
//! the operation would have answered exactly: a product's low end is the product of the low ends,
//! rounded down, and its high end the product of the high ends, rounded up, so what is known of a
//! value is never more than what is true of it. A mantissa is held to `precision` bits, which is
//! how much of the value is known, and asking again at a greater precision is how a question the
//! enclosure could not settle is asked once more.
//!
//! Nothing here knows a sign, a scale or a limit of any carrier: it is arithmetic on magnitudes,
//! and what a value may be is the caller's.

use crate::magnitude::Magnitude;
use core::cmp::Ordering;

/// A value between `low × 2^exp` and `high × 2^exp`.
#[derive(Clone, Debug)]
pub(crate) struct Enclosure {
    low: Magnitude,
    high: Magnitude,
    exp: i128,
}

impl Enclosure {
    /// The whole number itself, known to `precision` bits. Nothing is known of nought, which is
    /// the one value no enclosure is asked for.
    pub(crate) fn of(whole: &Magnitude, precision: u64) -> Enclosure {
        assert!(!whole.is_zero(), "nought is not enclosed");
        Enclosure {
            low: whole.clone(),
            high: whole.clone(),
            exp: 0,
        }
        .narrowed(precision)
    }

    /// Five to `power`, known to `precision` bits, by squaring: what is kept of each square is its
    /// leading bits, so a power of five as large as no number holds costs the bits asked for and
    /// not the bits it has.
    pub(crate) fn five_to(power: u128, precision: u64) -> Enclosure {
        let mut result = Enclosure::of(&Magnitude::ONE, precision);
        let mut base = Enclosure::of(&Magnitude::of_u128(5), precision);
        let mut left = power;
        while left > 0 {
            if left & 1 == 1 {
                result = result.times(&base, precision);
            }
            left >>= 1;
            if left > 0 {
                base = base.times(&base, precision);
            }
        }
        result
    }

    /// The same value times two to `by`, which knows no more or less of it.
    pub(crate) fn times_two_to(mut self, by: i128) -> Enclosure {
        self.exp += by;
        self
    }

    /// The product, known to `precision` bits.
    pub(crate) fn times(&self, other: &Enclosure, precision: u64) -> Enclosure {
        Enclosure {
            low: self.low.mul(&other.low),
            high: self.high.mul(&other.high),
            exp: self.exp + other.exp,
        }
        .narrowed(precision)
    }

    /// The quotient, known to `precision` bits. Nothing where the divisor is not known to be above
    /// nought, which a greater precision may change.
    pub(crate) fn over(&self, divisor: &Enclosure, precision: u64) -> Option<Enclosure> {
        if divisor.low.is_zero() {
            return None;
        }
        // Enough bits ahead of the dividend that the quotient has `precision` of its own.
        let lift = (precision + divisor.high.bits() + 2).saturating_sub(self.low.bits());
        let (low, _) = self.low.times_two_to(lift).div_rem(&divisor.high);
        let (high, remainder) = self.high.times_two_to(lift).div_rem(&divisor.low);
        let high = if remainder.is_zero() {
            high
        } else {
            high.increment()
        };
        Some(
            Enclosure {
                low,
                high,
                exp: self.exp - divisor.exp - i128::from(lift),
            }
            .narrowed(precision),
        )
    }

    /// Where the value stands against another, where the two are known well enough to say: below
    /// or above it, and nothing where their enclosures overlap.
    pub(crate) fn against(&self, other: &Enclosure) -> Option<Ordering> {
        if self.high_below(other) {
            Some(Ordering::Less)
        } else if other.high_below(self) {
            Some(Ordering::Greater)
        } else {
            None
        }
    }

    /// Whether the value is known to be below `other`'s.
    ///
    /// Two values that stand at different powers of two are ordered by them, which is nearly every
    /// pair; two at the same are brought to one exponent, which is a shift of at most the bits the
    /// mantissas have.
    fn high_below(&self, other: &Enclosure) -> bool {
        if other.low.is_zero() {
            return false;
        }
        let here = self.high.bits() as i128 + self.exp;
        let there = other.low.bits() as i128 + other.exp;
        if here != there {
            return here < there;
        }
        let by = self.exp - other.exp;
        if by >= 0 {
            self.high.times_two_to(by as u64) < other.low
        } else {
            self.high < other.low.times_two_to((-by) as u64)
        }
    }

    /// The largest whole number of halves the value is known to be at least and known to be short
    /// of the next of: `k` where it is above `k/2` and below `(k+1)/2`, as strictly as the
    /// enclosure knows it. Nothing where the two ends stand in different halves, or where the low
    /// end is one exactly, which the value may be too.
    pub(crate) fn halves(&self) -> Option<Magnitude> {
        let (low, low_exact) = doubled(&self.low, self.exp);
        let (high, _) = doubled(&self.high, self.exp);
        (low == high && !low_exact).then_some(low)
    }

    /// The same enclosure with its mantissas kept to `precision` bits: the low end rounded down
    /// and the high end rounded up, which is what keeps it true.
    fn narrowed(mut self, precision: u64) -> Enclosure {
        let bits = self.high.bits();
        if bits <= precision {
            return self;
        }
        let by = bits - precision;
        let exact = self.high.twos() >= by;
        self.low = self.low.shifted_down(by);
        self.high = self.high.shifted_down(by);
        if !exact {
            self.high = self.high.increment();
        }
        self.exp += i128::from(by);
        self
    }
}

/// `mantissa × 2^exp` doubled and rounded down to a whole number, and whether it was one already.
fn doubled(mantissa: &Magnitude, exp: i128) -> (Magnitude, bool) {
    let exp = exp + 1;
    if exp >= 0 {
        return (mantissa.times_two_to(exp as u64), true);
    }
    let by = (-exp) as u64;
    if by > mantissa.bits() {
        return (Magnitude::ZERO, mantissa.is_zero());
    }
    (mantissa.shifted_down(by), mantissa.twos() >= by)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn small(n: u128) -> Magnitude {
        Magnitude::of_u128(n)
    }

    /// What an enclosure says of a value is never more than what is true of it: a power of five
    /// whose exact value is known stands neither above nor below its own enclosure, at any
    /// precision, and stands where it should against what is a little either side of it.
    #[test]
    fn a_power_of_five_is_enclosed_at_every_precision() {
        for power in [0u128, 1, 2, 3, 27, 100, 1000] {
            let exact = Enclosure::of(&small(1).times_five_to(power as u64), u64::MAX);
            let two = Enclosure::of(&small(2), 64);
            let half = exact.over(&two, 64).expect("two is above nought");
            let double = exact.times(&two, 64);
            for precision in [8u64, 64, 200, 4000] {
                let enclosed = Enclosure::five_to(power, precision);
                assert_eq!(enclosed.against(&exact), None, "5^{power} at {precision}");
                // Eight bits are too few to tell a power of five from half of it or twice it once
                // there have been ten squarings, and enough to know nothing of it that is false.
                if precision >= 64 {
                    assert_eq!(enclosed.against(&half), Some(Ordering::Greater), "{power}");
                    assert_eq!(enclosed.against(&double), Some(Ordering::Less), "{power}");
                }
            }
        }
    }

    /// A power of five with an exponent no number is built at is known to as many bits as asked
    /// for, and stands where it should against a neighbour.
    #[test]
    fn a_power_of_five_a_billion_places_up_is_never_built() {
        let five = Enclosure::five_to(1_000_000_000, 256);
        assert!(five.high.bits() <= 257);
        assert!(five.exp > 2_000_000_000);
        // log2(5^1e9) = 2321928094.887..., so 2^2321928095 is just above it, and 2^2321928094 below.
        let above = Enclosure::of(&small(1), 256).times_two_to(2_321_928_095);
        let below = Enclosure::of(&small(1), 256).times_two_to(2_321_928_094);
        assert_eq!(five.against(&above), Some(Ordering::Less));
        assert_eq!(five.against(&below), Some(Ordering::Greater));
    }

    #[test]
    fn halves_are_told_apart_and_ties_are_left_alone() {
        let seven_halves = Enclosure::of(&small(7), 64).times_two_to(-1);
        // 7/2 is exactly a half, which no enclosure of it can say it is above.
        assert_eq!(seven_halves.halves(), None);
        let above = Enclosure {
            low: small(701),
            high: small(702),
            exp: -8,
        };
        // 701/256 .. 702/256 is above two and three quarters and below two and four fifths.
        assert_eq!(above.halves(), Some(small(5)));
        let straddling = Enclosure {
            low: small(639),
            high: small(641),
            exp: -8,
        };
        assert_eq!(straddling.halves(), None);
    }
}
