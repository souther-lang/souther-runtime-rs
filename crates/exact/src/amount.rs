//! What a `Decimal` is, and what each operation on one answers (spec §primitives,
//! §stdlib-decimal).
//!
//! A `Decimal` is an integer and a scale: the amount is the integer over ten to the scale, and the
//! scale is kept as it was written, so `1.0` and `1.00` are one amount and two values. Equality and
//! order read the amount; the text a value is written as reads the scale too. Every operation here
//! answers what the language states for it, which is what the JVM's `DecimalMath` answers, and says
//! where it answers nothing so that a runtime can end the run for the reason its contract names.
//!
//! The integer is a [`Magnitude`], which does integer arithmetic and nothing else: in a `u128`
//! where the value fits, which is nearly every amount, and as a wide number only past that. Which
//! scale a result has, what a value is written as and where an operation refuses are all written
//! here; which neighbour a mode rounds to is [`rounded`]'s, which a `Rational` rounds by too. So
//! how the integer is worked out could change without a single answer moving, and nothing that
//! reads an [`Amount`] — a runtime's cell, generated code, a host — sees how it is held.
//!
//! No operation here builds a power of ten from a scale it was handed. A scale is a 32-bit number,
//! and `10^2147483647` is a number no memory holds, so an operation whose answer is small but whose
//! operands differ wildly in scale — rounding `1E-2000000000` to a whole number — decides that
//! answer from how many digits there are, and one whose answer is itself that wide refuses before
//! building it ([`WIDEST`]).

use crate::{Dropped, Magnitude, Rounding, Scaled, TENS, WIDEST, dropped, rounded};
use alloc::string::String;
use alloc::vec::Vec;
use core::cmp::Ordering;

/// How many digits the text an amount is written as at a boundary may spell an exponent out into
/// (spec §primitives): `1E+1000` is written with its thousand zeros and `1E+1001` as it stands.
const SPELT_OUT: i64 = 1000;

/// A `Decimal`: a sign, the digits as a whole number, and a scale.
///
/// Nought has no sign, so there is one way to hold each value: `-0.0` is read as `0.0`, as the JVM
/// reads it. The whole number is never wider than [`WIDEST`]. That is held by how one is made, and
/// not by who makes it: every way of making one from what it is handed answers nothing where the
/// whole number would be wider, and the one that does not check, [`Amount::from_trusted_parts`],
/// takes only what [`Amount::with_parts`] gave, and says so in its name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Amount {
    negative: bool,
    magnitude: Magnitude,
    scale: i32,
}

/// The pieces written one after another into one allocation. Not `format!`, whose machinery a
/// runtime would carry and run for what is only copying.
fn joined(pieces: &[&str]) -> String {
    let mut text = String::with_capacity(pieces.iter().map(|piece| piece.len()).sum());
    for piece in pieces {
        text.push_str(piece);
    }
    text
}

/// That many zeros written after the text.
fn zeros(text: &mut String, many: usize) {
    text.extend(core::iter::repeat_n('0', many));
}

/// `log2(10)`, for how many bits a power of ten is wide.
const LOG2_10: f64 = core::f64::consts::LOG2_10;

/// The magnitude, where it is no wider than a `Decimal` holds.
fn held(magnitude: Magnitude) -> Option<Magnitude> {
    (magnitude.bits() <= WIDEST).then_some(magnitude)
}

/// How many digits these runs write one after another once the zeros in front are left off.
fn significant(runs: &[&[u8]]) -> u64 {
    let total: usize = runs.iter().map(|run| run.len()).sum();
    let leading = runs
        .iter()
        .flat_map(|run| run.iter())
        .take_while(|&&digit| digit == b'0')
        .count();
    (total - leading) as u64
}

/// Whether a whole number written in `significant` digits, the first of them not nought, is surely
/// wider than `widest` bits, which is known from the count alone and before any of it is read.
///
/// Its least value is ten to `significant - 1`, which is more than `(significant - 1) · log2 10`
/// bits wide; where that is `widest` or more, no value of that many digits is held. The margin is
/// for the product's rounding, so the answer is never yes for a count some value of which fits.
/// A count it answers no for may still be too wide, and is settled by the width of the value read.
fn surely_wider(significant: u64, widest: u64) -> bool {
    significant > 0 && (significant - 1) as f64 * LOG2_10 >= widest as f64 + 1e-6
}

/// The magnitude times ten to `by`, where that is no wider than a `Decimal` holds. Refused before
/// it is built where it could not be: the product is at least as wide as its factors' widths less
/// one, and a power of ten is `by · log2 10` bits wide.
fn scaled_up(magnitude: &Magnitude, by: u64) -> Option<Magnitude> {
    if magnitude.is_zero() || by == 0 {
        return Some(magnitude.clone());
    }
    // Ten to `by` is narrower than four bits a power, so a product that wide is surely held, and
    // is built without the estimate or the width asked of it: nearly every raise is a place or two.
    if magnitude.bits() + 4 * by <= WIDEST {
        return Some(magnitude.times_ten_to(by));
    }
    let narrowest = (magnitude.bits() - 1) as f64 + (by as f64) * LOG2_10 - 1.0;
    if narrowest > WIDEST as f64 {
        return None;
    }
    held(magnitude.times_ten_to(by))
}

impl Amount {
    fn new(negative: bool, magnitude: Magnitude, scale: i32) -> Amount {
        Amount {
            negative: negative && !magnitude.is_zero(),
            magnitude,
            scale,
        }
    }

    /// A value of this sign, magnitude and scale, where the magnitude is no wider than a `Decimal`
    /// holds.
    pub fn of_magnitude(negative: bool, magnitude: Magnitude, scale: i32) -> Option<Amount> {
        Some(Amount::new(negative, held(magnitude)?, scale))
    }

    /// The value a `Rational` narrowed to a scale is, where its whole number is no wider than a
    /// `Decimal` holds.
    pub(crate) fn of_scaled(parts: Scaled) -> Option<Amount> {
        Amount::of_magnitude(parts.negative, parts.magnitude, parts.scale)
    }

    /// The sign, the magnitude and the scale.
    pub fn split(&self) -> (bool, &Magnitude, i32) {
        (self.negative, &self.magnitude, self.scale)
    }

    /// The value a runtime stored the parts of, read back from where it stored them: a sign, the
    /// magnitude as little-endian bytes, and the scale.
    ///
    /// Trusted and not checked, which is what the name says, as [`crate::Ratio::from_trusted_parts`]
    /// is: only what [`Amount::with_parts`] gave is a value here, and one wider than [`WIDEST`] is
    /// one no operation answers for. A debug build checks it; a release build does not, since
    /// reading a stored value is not an operation and is done on every read.
    pub fn from_trusted_parts(negative: bool, magnitude: &[u8], scale: i32) -> Amount {
        let magnitude = Magnitude::of_le_bytes(magnitude);
        debug_assert!(
            magnitude.bits() <= WIDEST,
            "stored parts are a Decimal's, whose whole number is held"
        );
        Amount::new(negative, magnitude, scale)
    }

    /// The parts [`Amount::from_trusted_parts`] takes, handed to `with` for as long as it runs:
    /// the magnitude as little-endian bytes, with no zero byte at the top and none at all for
    /// nought.
    pub fn with_parts<T>(&self, with: impl FnOnce(bool, &[u8], i32) -> T) -> T {
        self.magnitude
            .with_le_bytes(|bytes| with(self.negative, bytes, self.scale))
    }

    /// `Decimal.fromInt`: the same number, at scale nought. Every `Int` is one exactly.
    pub fn of_int(value: i64) -> Amount {
        Amount::new(
            value < 0,
            Magnitude::of_u128(u128::from(value.unsigned_abs())),
            0,
        )
    }

    /// The whole number these ASCII digits write in decimal, at `scale`: what a runtime reads out
    /// of text once it has decided where the digits are and what scale they come to. Nothing where
    /// the whole number is wider than a `Decimal` holds, which is refused from how many digits
    /// there are before any is read where the count alone says so: a document's number is as long
    /// as the document, and no string bound holds it.
    pub fn of_digits(negative: bool, digits: &[u8], scale: i32) -> Option<Amount> {
        if surely_wider(significant(&[digits]), WIDEST) {
            return None;
        }
        Amount::of_magnitude(negative, Magnitude::of_digits(digits), scale)
    }

    /// The value a JSON number writes, at the scale its spelling gives it: as many places as its
    /// fraction has, less its exponent, which is how the JVM reads one (`new BigDecimal(text)`).
    /// Nothing where that scale is not one a `Decimal` has, or the whole number its digits write is
    /// wider than one holds.
    ///
    /// `written` is a number as RFC 8259 writes one, which the document's reader has held it to.
    pub fn of_json_number(written: &[u8]) -> Option<Amount> {
        let (negative, unsigned) = match written.split_first() {
            Some((b'-', rest)) => (true, rest),
            _ => (false, written),
        };
        let (mantissa, exponent) = match unsigned.iter().position(|&it| it == b'e' || it == b'E') {
            Some(at) => (&unsigned[..at], Some(&unsigned[at + 1..])),
            None => (unsigned, None),
        };
        let (whole, fraction) = match mantissa.iter().position(|&it| it == b'.') {
            Some(at) => (&mantissa[..at], &mantissa[at + 1..]),
            None => (mantissa, &[][..]),
        };
        let exponent = match exponent {
            None => 0,
            Some(spelt) => {
                let (below, digits) = match spelt.split_first() {
                    Some((b'-', rest)) => (true, rest),
                    Some((b'+', rest)) => (false, rest),
                    _ => (false, spelt),
                };
                // An exponent wider than sixty-four bits gives a scale no `Decimal` has, and
                // one within them is settled by the scale below.
                let mut value: i64 = 0;
                for &digit in digits {
                    value = value
                        .checked_mul(10)?
                        .checked_add(i64::from(digit - b'0'))?;
                }
                if below { -value } else { value }
            }
        };
        let fraction_digits = i64::try_from(fraction.len()).ok()?;
        let scale = i32::try_from(fraction_digits.checked_sub(exponent)?).ok()?;
        // Refused before the digits are copied where their count alone says so.
        if surely_wider(significant(&[whole, fraction]), WIDEST) {
            return None;
        }
        let mut digits = Vec::with_capacity(whole.len() + fraction.len());
        digits.extend_from_slice(whole);
        digits.extend_from_slice(fraction);
        Amount::of_digits(negative, &digits, scale)
    }

    /// The scale, as the value carries it.
    pub fn scale(&self) -> i32 {
        self.scale
    }

    /// The integer, in decimal: a `-` where it is below nought, and no leading zero.
    pub fn unscaled_text(&self) -> String {
        let digits = self.magnitude.digits();
        if self.negative {
            joined(&["-", &digits])
        } else {
            digits
        }
    }

    /// Whether the amount is nought, at whatever scale.
    pub fn is_zero(&self) -> bool {
        self.magnitude.is_zero()
    }

    /// Whether the amount is below nought. Nought is not.
    pub fn is_negative(&self) -> bool {
        self.negative
    }

    /// The same amount on the other side of nought, at the same scale. Total.
    pub fn negated(&self) -> Amount {
        Amount::new(!self.negative, self.magnitude.clone(), self.scale)
    }

    /// Two values by amount, whatever their scales (`Decimal.compare`, `==` and `<`). Total.
    ///
    /// By sign first. Two values at one scale are then their magnitudes compared, and two whose
    /// magnitudes a `u128` holds are brought to one scale in one: those are nearly every pair a
    /// sort or a comparison of amounts is handed, and neither needs a digit counted. Past them, by
    /// where each value's leading digit stands; only two values whose leading digits stand at one
    /// place are brought to one scale, and then the one with the larger scale is no wider than the
    /// other already is.
    pub fn compare(&self, other: &Amount) -> Ordering {
        let sign = |it: &Amount| match (it.is_zero(), it.negative) {
            (true, _) => 0,
            (false, true) => -1,
            (false, false) => 1,
        };
        let by_sign = sign(self).cmp(&sign(other));
        if by_sign != Ordering::Equal || self.is_zero() {
            return by_sign;
        }
        let by_magnitude = if self.scale == other.scale {
            self.magnitude.cmp(&other.magnitude)
        } else if let (Some(mine), Some(theirs)) =
            (self.magnitude.as_u128(), other.magnitude.as_u128())
        {
            // The one at the smaller scale raised to the other's. Neither is nought here, so one
            // raised past what a `u128` holds is the greater.
            let apart = i64::from(self.scale) - i64::from(other.scale);
            let raised = |magnitude: u128, by: i64| {
                TENS.get(by as usize)
                    .and_then(|ten| magnitude.checked_mul(*ten))
            };
            if apart < 0 {
                raised(mine, -apart).map_or(Ordering::Greater, |it| it.cmp(&theirs))
            } else {
                raised(theirs, apart).map_or(Ordering::Less, |it| mine.cmp(&it))
            }
        } else {
            self.compare_wide(other)
        };
        if self.negative {
            by_magnitude.reverse()
        } else {
            by_magnitude
        }
    }

    /// The magnitudes of two values of one sign compared by amount, where either is wider than a
    /// `u128`: by where each value's leading digit stands, and brought to one scale only where
    /// those stand at one place.
    fn compare_wide(&self, other: &Amount) -> Ordering {
        let leading = |it: &Amount| it.magnitude.precision() as i64 - i64::from(it.scale);
        match leading(self).cmp(&leading(other)) {
            Ordering::Equal => {
                let apart = i64::from(self.scale) - i64::from(other.scale);
                let raised = |magnitude: &Magnitude, by: i64| magnitude.times_ten_to(by as u64);
                match apart.cmp(&0) {
                    Ordering::Less => raised(&self.magnitude, -apart).cmp(&other.magnitude),
                    Ordering::Equal => self.magnitude.cmp(&other.magnitude),
                    Ordering::Greater => self.magnitude.cmp(&raised(&other.magnitude, apart)),
                }
            }
            unequal => unequal,
        }
    }

    /// `+` and `Decimal.add`: at the larger of the two scales. Nothing where the sum is wider than
    /// a `Decimal` holds.
    pub fn add(&self, other: &Amount) -> Option<Amount> {
        let scale = self.scale.max(other.scale);
        let raised = |it: &Amount| {
            scaled_up(
                &it.magnitude,
                (i64::from(scale) - i64::from(it.scale)) as u64,
            )
        };
        let (mine, theirs) = (raised(self)?, raised(other)?);
        let (negative, magnitude) = if self.negative == other.negative {
            (self.negative, mine.add(&theirs))
        } else if mine >= theirs {
            (self.negative, mine.sub(&theirs))
        } else {
            (other.negative, theirs.sub(&mine))
        };
        Some(Amount::new(negative, held(magnitude)?, scale))
    }

    /// `-` and `Decimal.subtract`, as [`Amount::add`] of the negation.
    pub fn subtract(&self, other: &Amount) -> Option<Amount> {
        self.add(&other.negated())
    }

    /// `*` and `Decimal.multiply`: at the sum of the two scales. Nothing where that sum is not a
    /// scale, or the product is wider than a `Decimal` holds.
    pub fn multiply(&self, other: &Amount) -> Option<Amount> {
        let scale = i32::try_from(i64::from(self.scale) + i64::from(other.scale)).ok()?;
        if self.magnitude.bits() + other.magnitude.bits() > WIDEST + 1 {
            return None;
        }
        let magnitude = held(self.magnitude.mul(&other.magnitude))?;
        Some(Amount::new(
            self.negative != other.negative,
            magnitude,
            scale,
        ))
    }

    /// The value at `scale`, rounded by `mode` where places are dropped (`Decimal.round`, and
    /// `Decimal.toInt` at scale nought). Nothing where the scale is not one a `Decimal` has, or the
    /// value at it is wider than a `Decimal` holds.
    pub fn round(&self, scale: i64, mode: Rounding) -> Option<Amount> {
        let scale = i32::try_from(scale).ok()?;
        if scale >= self.scale {
            let by = (i64::from(scale) - i64::from(self.scale)) as u64;
            return Some(Amount::new(
                self.negative,
                scaled_up(&self.magnitude, by)?,
                scale,
            ));
        }
        let dropping = (i64::from(self.scale) - i64::from(scale)) as u64;
        let (quotient, dropped) = self.dropping(dropping);
        let magnitude = held(rounded(quotient, self.negative, dropped, mode))?;
        Some(Amount::new(self.negative, magnitude, scale))
    }

    /// The magnitude with its last `places` digits dropped, and what was dropped.
    ///
    /// A magnitude with fewer digits than `places` less one is below a tenth of the unit it is
    /// rounded to, so the answer is nought and what was dropped is below half, without the power
    /// of ten the division would have wanted.
    fn dropping(&self, places: u64) -> (Magnitude, Dropped) {
        if self.magnitude.is_zero() {
            return (Magnitude::ZERO, Dropped::Nothing);
        }
        if places > self.magnitude.precision() {
            return (Magnitude::ZERO, Dropped::BelowHalf);
        }
        let unit = Magnitude::ten_to(places);
        let (quotient, remainder) = self.magnitude.div_rem(&unit);
        let dropped = dropped(&remainder, &unit);
        (quotient, dropped)
    }

    /// `Decimal.toInt`: the whole number the value rounds to by `mode`. Nothing where that is not
    /// an `Int`.
    pub fn to_int(&self, mode: Rounding) -> Option<i64> {
        if self.magnitude.is_zero() {
            return Some(0);
        }
        let whole = if self.scale <= 0 {
            // A whole number already, and one with more than nineteen digits is past every `Int`.
            let by = -i64::from(self.scale) as u64;
            if self.magnitude.precision() + by > 19 {
                return None;
            }
            self.magnitude.times_ten_to(by)
        } else {
            let (quotient, dropped) = self.dropping(self.scale as u64);
            rounded(quotient, self.negative, dropped, mode)
        };
        let magnitude = u64::try_from(whole.as_u128()?).ok()?;
        if self.negative {
            0i64.checked_sub_unsigned(magnitude)
        } else {
            i64::try_from(magnitude).ok()
        }
    }

    /// `Decimal.divide`: the quotient at `scale`, rounded by `mode`. Nothing where the scale is
    /// not one a `Decimal` has, or the quotient at it is wider than a `Decimal` holds.
    ///
    /// # Panics
    ///
    /// Where the divisor is nought, which is answered as a case before any division is asked for
    /// (spec §a-division-that-does-not-run-needs-no-scale).
    pub fn divide(&self, divisor: &Amount, scale: i64, mode: Rounding) -> Option<Amount> {
        assert!(
            !divisor.is_zero(),
            "a zero divisor is answered as a case and never divided by"
        );
        let scale = i32::try_from(scale).ok()?;
        let negative = self.negative != divisor.negative;
        if self.is_zero() {
            return Some(Amount::new(false, Magnitude::ZERO, scale));
        }
        // The quotient at `scale` is `self · 10^raise / divisor`, the power of ten on whichever
        // side keeps it whole.
        let raise = i64::from(scale) - i64::from(self.scale) + i64::from(divisor.scale);
        let (quotient, dropped) = if raise >= 0 {
            // As wide as the quotient and the divisor together, and refused where the quotient
            // alone would be wider than a `Decimal` holds.
            let narrowest = (self.magnitude.bits() - 1) as f64 + raise as f64 * LOG2_10
                - divisor.magnitude.bits() as f64
                - 1.0;
            if narrowest > WIDEST as f64 {
                return None;
            }
            let dividend = self.magnitude.times_ten_to(raise as u64);
            let (quotient, remainder) = dividend.div_rem(&divisor.magnitude);
            (quotient, dropped(&remainder, &divisor.magnitude))
        } else {
            let lowered = (-raise) as u64;
            // Below a tenth where the divisor, raised, has two more digits than the dividend.
            let apart = self.magnitude.precision() as i64 - divisor.magnitude.precision() as i64;
            if lowered as i64 >= apart + 2 {
                (Magnitude::ZERO, Dropped::BelowHalf)
            } else {
                let by = divisor.magnitude.times_ten_to(lowered);
                let (quotient, remainder) = self.magnitude.div_rem(&by);
                (quotient, dropped(&remainder, &by))
            }
        };
        let magnitude = held(rounded(quotient, negative, dropped, mode))?;
        Some(Amount::new(negative, magnitude, scale))
    }

    /// How many characters [`Amount::plain_text`] is, worked out without writing it: a sign, the
    /// digits, and either the whole zeros a negative scale stands for or a point and the leading
    /// fractional zeros a scale above the digits asks for. Nought is `0` at every scale up to
    /// nought.
    fn plain_length(&self) -> i64 {
        let sign = i64::from(self.negative);
        let precision = self.magnitude.precision() as i64;
        let scale = i64::from(self.scale);
        if scale <= 0 {
            if self.is_zero() {
                1
            } else {
                sign + precision - scale
            }
        } else if precision > scale {
            sign + precision + 1
        } else {
            sign + 2 + scale
        }
    }

    /// `String.fromDecimal`: the value in plain notation, never with an exponent, at the scale it
    /// carries (spec §stdlib-string). Nothing where that text is longer than `longest` characters,
    /// which is what a string holds and is decided before any of it is written: the text of a
    /// value near either end of the scale range is a couple of billion characters.
    pub fn plain_text(&self, longest: i64) -> Option<String> {
        if self.plain_length() > longest {
            return None;
        }
        let digits = self.magnitude.digits();
        let sign = if self.negative { "-" } else { "" };
        let scale = i64::from(self.scale);
        Some(if scale <= 0 {
            if self.is_zero() {
                String::from("0")
            } else {
                let mut text = joined(&[sign, &digits]);
                zeros(&mut text, (-scale) as usize);
                text
            }
        } else if digits.len() as i64 > scale {
            let point = digits.len() - scale as usize;
            joined(&[sign, &digits[..point], ".", &digits[point..]])
        } else {
            let mut text = joined(&[sign, "0."]);
            zeros(&mut text, scale as usize - digits.len());
            text.push_str(&digits);
            text
        })
    }

    /// The amount with as many of its trailing zeros dropped as the scale lets it drop: one form
    /// for every value the language calls equal (spec §primitives), as the JVM's `leastDigits`
    /// answers it. The scale stops at its smallest, and fixing the scale fixes the digits.
    pub fn least_digits(&self) -> Amount {
        if self.is_zero() {
            return Amount::new(false, Magnitude::ZERO, 0);
        }
        let room = (i64::from(self.scale) - i64::from(i32::MIN)) as u64;
        let (magnitude, dropped) = self.magnitude.without_trailing_zeros(room);
        let scale = (i64::from(self.scale) - dropped as i64) as i32;
        Amount::new(self.negative, magnitude, scale)
    }

    /// The text the value is written as at a boundary: its amount, and not the scale it was read
    /// or worked out at (spec §primitives, the JVM's `Representations.canonicalNumber`).
    ///
    /// The fewest digits the amount is written with, spelt out into its whole zeros where that is
    /// at most [`SPELT_OUT`] digits and left with its exponent where it is more; and then written as
    /// a JSON number the way the JVM's `BigDecimal.toString` writes one, which is how the JVM's
    /// boundary writes it.
    pub fn external_text(&self) -> String {
        let least = self.least_digits();
        let spelt = if least.scale < 0
            && least.magnitude.precision() as i64 - i64::from(least.scale) <= SPELT_OUT
        {
            let by = (-i64::from(least.scale)) as u64;
            Amount::new(least.negative, least.magnitude.times_ten_to(by), 0)
        } else {
            least
        };
        spelt.scientific_text()
    }

    /// The value at the scale it carries, as the JVM's `BigDecimal.toString` writes it: what an
    /// issue's metadata says a `Decimal` is, since Raoh's metadata holds the `BigDecimal` itself and
    /// its scale with it, where a boundary writes the amount alone ([`Amount::external_text`]).
    pub fn scaled_text(&self) -> String {
        self.scientific_text()
    }

    /// The value as the JVM's `BigDecimal.toString` writes it: plain where the scale is not below
    /// nought and the leading digit stands no more than six places after the point, and otherwise
    /// one digit, the rest after a point, and the exponent.
    fn scientific_text(&self) -> String {
        let digits = self.magnitude.digits();
        let sign = if self.negative { "-" } else { "" };
        if self.scale == 0 {
            return joined(&[sign, &digits]);
        }
        let scale = i64::from(self.scale);
        let adjusted = -scale + (digits.len() as i64 - 1);
        if scale >= 0 && adjusted >= -6 {
            let point = digits.len() as i64 - scale;
            return if point > 0 {
                let point = point as usize;
                joined(&[sign, &digits[..point], ".", &digits[point..]])
            } else {
                let mut text = joined(&[sign, "0."]);
                zeros(&mut text, (-point) as usize);
                text.push_str(&digits);
                text
            };
        }
        let (first, rest) = digits.split_at(1);
        let mut written = joined(&[sign, first]);
        if !rest.is_empty() {
            written.push('.');
            written.push_str(rest);
        }
        if adjusted != 0 {
            written.push_str(if adjusted > 0 { "E+" } else { "E-" });
            written.push_str(&Magnitude::of_u128(u128::from(adjusted.unsigned_abs())).digits());
        }
        written
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Ratio;

    /// A value as the JVM's `new BigDecimal(text)` reads decimal text or a JSON number.
    fn d(text: &str) -> Amount {
        Amount::of_json_number(text.as_bytes()).expect("a value the tests write")
    }

    fn shown(amount: &Amount) -> (String, i32) {
        (amount.unscaled_text(), amount.scale())
    }

    /// What a string holds, in characters (spec §what-a-string-holds).
    const STRING_HOLDS: i64 = 268_435_455;

    const EVERY: [Rounding; 7] = [
        Rounding::Up,
        Rounding::Down,
        Rounding::Ceiling,
        Rounding::Floor,
        Rounding::HalfUp,
        Rounding::HalfDown,
        Rounding::HalfEven,
    ];

    /// A value's integer and scale are what its spelling gives it, `-0` is nought, and an
    /// exponent moves the scale.
    #[test]
    fn a_json_number_is_read_at_the_scale_its_spelling_gives_it() {
        for (text, unscaled, scale) in [
            ("0", "0", 0),
            ("-0", "0", 0),
            ("-0.00", "0", 2),
            ("1.50", "150", 2),
            ("-12.345", "-12345", 3),
            ("1e2", "1", -2),
            ("1.5E+3", "15", -2),
            ("25e-3", "25", 3),
            (
                "123456789012345678901234567890",
                "123456789012345678901234567890",
                0,
            ),
        ] {
            assert_eq!(shown(&d(text)), (unscaled.to_string(), scale), "{text}");
        }
        assert!(Amount::of_json_number(b"1e2147483648").is_some());
        assert!(Amount::of_json_number(b"1e2147483649").is_none());
        assert!(Amount::of_json_number(b"1e-2147483647").is_some());
        assert!(Amount::of_json_number(b"1e-2147483648").is_none());
        assert!(Amount::of_json_number(b"1e99999999999999999999").is_none());
    }

    /// Scale is carried and not compared: `1.0` and `1.00` are one amount.
    #[test]
    fn values_are_compared_by_amount_whatever_their_scales() {
        for (one, other, order) in [
            ("1.0", "1.00", Ordering::Equal),
            ("0", "0.000", Ordering::Equal),
            ("-0.0", "0", Ordering::Equal),
            ("1", "1.01", Ordering::Less),
            ("-1", "-1.01", Ordering::Greater),
            ("-1", "1", Ordering::Less),
            ("1e2", "99.99", Ordering::Greater),
            ("1e-2000000000", "0", Ordering::Greater),
            ("1e2000000000", "1e1999999999", Ordering::Greater),
            ("12.30", "1.23e1", Ordering::Equal),
            ("1.50", "1.49", Ordering::Greater),
            (
                "1",
                "1.00000000000000000000000000000000000000",
                Ordering::Equal,
            ),
            (
                "1",
                "1.000000000000000000000000000000000000001",
                Ordering::Less,
            ),
            (
                "2",
                "1.999999999999999999999999999999999999999",
                Ordering::Greater,
            ),
            (
                "340282366920938463463374607431768211455",
                "3.4e38",
                Ordering::Greater,
            ),
            (
                "340282366920938463463374607431768211456",
                "340282366920938463463374607431768211455.9",
                Ordering::Greater,
            ),
            (
                "-7e40",
                "-70000000000000000000000000000000000000000.0",
                Ordering::Equal,
            ),
        ] {
            assert_eq!(d(one).compare(&d(other)), order, "{one} {other}");
            assert_eq!(d(other).compare(&d(one)), order.reverse(), "{other} {one}");
        }
    }

    /// A sum and a difference are at the larger scale, a product at the sum of the two; negation
    /// keeps the scale.
    #[test]
    fn arithmetic_answers_the_scale_the_language_states() {
        let sum = d("1.5").add(&d("2.25")).unwrap();
        assert_eq!(shown(&sum), ("375".to_string(), 2));
        let difference = d("1").subtract(&d("0.001")).unwrap();
        assert_eq!(shown(&difference), ("999".to_string(), 3));
        let product = d("0.10").multiply(&d("100.0")).unwrap();
        assert_eq!(shown(&product), ("10000".to_string(), 3));
        assert_eq!(shown(&d("1.50").negated()), ("-150".to_string(), 2));
        assert_eq!(shown(&d("0.00").negated()), ("0".to_string(), 2));
        let across = d("-5").add(&d("3.5")).unwrap();
        assert_eq!(shown(&across), ("-15".to_string(), 1));
        let nothing = d("2.5").subtract(&d("2.50")).unwrap();
        assert_eq!(shown(&nothing), ("0".to_string(), 2));
    }

    /// A product whose scale is past the range aborts, and so does a sum that would have to be
    /// spelt out past what a `Decimal` holds; nought raised to any scale is still nought.
    #[test]
    fn an_answer_with_no_place_is_nothing() {
        assert!(d("1e-2147483647").multiply(&d("1e-1")).is_none());
        assert!(d("1e2147483647").multiply(&d("1e2")).is_none());
        let floor = d("1e2147483647").multiply(&d("1e1")).unwrap();
        assert_eq!(floor.scale(), i32::MIN);
        assert!(d("0e-2147483647").multiply(&d("1e-1")).is_none());
        assert!(d("1e-2147483647").add(&d("1e2147483647")).is_none());
        let nought = d("0e2147483647").add(&d("1e-2147483647")).unwrap();
        assert_eq!(shown(&nought), ("1".to_string(), 2147483647));
    }

    /// Every operation that widens a whole number past [`WIDEST`] refuses before building it:
    /// rounding and dividing to a larger scale, and a sum across far apart scales. Each would
    /// otherwise build a number of some two billion bits, which is what makes this test slow if
    /// one of them stops refusing first.
    #[test]
    fn a_whole_number_past_the_widest_is_refused_before_it_is_built() {
        // 10^n is about n · log2 10 bits wide, so this scale is past the edge.
        let past = (WIDEST as f64 / LOG2_10) as i64 + 1_000;
        let one = d("1");
        for mode in EVERY {
            assert_eq!(one.round(past, mode), None, "{mode:?}");
            assert_eq!(one.divide(&d("1"), past, mode), None, "{mode:?}");
        }
        assert_eq!(
            one.add(&Amount::from_trusted_parts(false, &[1], past as i32)),
            None
        );
        assert_eq!(
            one.subtract(&Amount::from_trusted_parts(false, &[1], past as i32)),
            None
        );
    }

    /// A count of digits is refused as surely too wide only where every whole number written in
    /// that many is too wide, and is where the least of them is wider by more than a bit: held to
    /// what a `u128` says of each power of ten, at every width a `u128` reaches.
    #[test]
    fn a_count_of_digits_is_refused_exactly_where_none_of_its_values_is_held() {
        for widest in 1..=120u64 {
            for count in 1..=38u64 {
                let least_bits = u64::from(128 - TENS[(count - 1) as usize].leading_zeros());
                if surely_wider(count, widest) {
                    assert!(least_bits > widest, "{count} digits in {widest} bits");
                }
                if least_bits > widest + 1 {
                    assert!(
                        surely_wider(count, widest),
                        "{count} digits in {widest} bits"
                    );
                }
            }
        }
        // At the widest a `Decimal` holds: the least whole number of 646456994 digits is wider
        // than it, and some of 646456993 digits are not.
        assert!(surely_wider(646_456_994, WIDEST));
        assert!(!surely_wider(646_456_993, WIDEST));
        assert!(!surely_wider(0, 0));
    }

    /// Digits are counted without the zeros in front of them, across the runs they are read from.
    #[test]
    fn digits_are_counted_from_the_first_that_is_not_nought() {
        assert_eq!(significant(&[b"0012", b"30"]), 4);
        assert_eq!(significant(&[b"000", b"0012"]), 2);
        assert_eq!(significant(&[b"000", b"000"]), 0);
        assert_eq!(significant(&[b"", b"5"]), 1);
    }

    /// A whole number read from digits is held to the widest a `Decimal` holds like any other, and
    /// not left to who wrote the digits: a document's number is as long as the document.
    #[test]
    fn digits_read_are_held_to_the_widest() {
        assert_eq!(
            Amount::of_digits(false, b"00123", 2).map(|it| shown(&it)),
            Some(("123".to_string(), 2))
        );
        assert_eq!(
            Amount::of_digits(false, b"000", 2).map(|it| it.is_zero()),
            Some(true)
        );
    }

    /// Every mode against the rows `java.math.RoundingMode`'s own documentation tabulates.
    #[test]
    fn every_mode_rounds_as_the_jvm_tabulates() {
        use Rounding::*;
        let table: [(&str, [i64; 7]); 10] = [
            ("5.5", [6, 5, 6, 5, 6, 5, 6]),
            ("2.5", [3, 2, 3, 2, 3, 2, 2]),
            ("1.6", [2, 1, 2, 1, 2, 2, 2]),
            ("1.1", [2, 1, 2, 1, 1, 1, 1]),
            ("1.0", [1, 1, 1, 1, 1, 1, 1]),
            ("-1.0", [-1, -1, -1, -1, -1, -1, -1]),
            ("-1.1", [-2, -1, -1, -2, -1, -1, -1]),
            ("-1.6", [-2, -1, -1, -2, -2, -2, -2]),
            ("-2.5", [-3, -2, -2, -3, -3, -2, -2]),
            ("-5.5", [-6, -5, -5, -6, -6, -5, -6]),
        ];
        for (value, answers) in table {
            for (mode, answer) in [Up, Down, Ceiling, Floor, HalfUp, HalfDown, HalfEven]
                .into_iter()
                .zip(answers)
            {
                assert_eq!(d(value).to_int(mode), Some(answer), "{value} {mode:?}");
                let at_nought = d(value).round(0, mode).unwrap();
                assert_eq!(
                    shown(&at_nought),
                    (answer.to_string(), 0),
                    "{value} {mode:?}"
                );
            }
        }
    }

    /// A value far below the unit it is rounded to is decided by its sign and the mode, without the
    /// power of ten its scale names.
    #[test]
    fn a_value_far_below_the_unit_is_rounded_without_building_its_scale() {
        for mode in EVERY {
            let away = matches!(mode, Rounding::Up | Rounding::Ceiling);
            assert_eq!(d("1e-2000000000").to_int(mode), Some(i64::from(away)));
            let below = matches!(mode, Rounding::Up | Rounding::Floor);
            assert_eq!(d("-1e-2000000000").to_int(mode), Some(-i64::from(below)));
            let rounded = d("7e-2147483647").round(-2147483648, mode).unwrap();
            assert_eq!(rounded.scale(), i32::MIN);
        }
    }

    #[test]
    fn a_whole_number_past_an_int_is_nothing() {
        assert_eq!(
            d("9223372036854775807").to_int(Rounding::Down),
            Some(i64::MAX)
        );
        assert_eq!(
            d("-9223372036854775808").to_int(Rounding::Down),
            Some(i64::MIN)
        );
        assert_eq!(
            d("9223372036854775807.5").to_int(Rounding::Down),
            Some(i64::MAX)
        );
        assert_eq!(d("9223372036854775807.5").to_int(Rounding::Up), None);
        assert_eq!(d("-9223372036854775808.5").to_int(Rounding::Up), None);
        assert_eq!(d("1e19").to_int(Rounding::Down), None);
        assert_eq!(
            d("9e18").to_int(Rounding::Down),
            Some(9_000_000_000_000_000_000)
        );
        assert_eq!(d("1e2000000000").to_int(Rounding::Down), None);
    }

    #[test]
    fn a_scale_outside_the_range_is_nothing() {
        assert!(d("1").round(2147483648, Rounding::Up).is_none());
        assert!(d("1").round(-2147483649, Rounding::Up).is_none());
        assert!(d("1").divide(&d("3"), 2147483648, Rounding::Up).is_none());
        assert!(d("1").round(2147483647, Rounding::Up).is_none());
        let far = d("0").round(2147483647, Rounding::Up).unwrap();
        assert_eq!(far.scale(), i32::MAX);
    }

    /// `Decimal.divide` at the rows `CompileDecimalMathTest` and the specification hold the JVM
    /// to.
    #[test]
    fn a_quotient_is_rounded_at_the_scale_asked() {
        use Rounding::*;
        for (dividend, divisor, scale, mode, unscaled, answered_scale) in [
            ("10", "3", 2, HalfUp, "333", 2),
            ("2", "3", 2, HalfUp, "67", 2),
            ("2", "3", 2, Down, "66", 2),
            ("-2", "3", 2, Floor, "-67", 2),
            ("1", "8", 2, HalfEven, "12", 2),
            ("3", "8", 2, HalfEven, "38", 2),
            ("1", "8", 2, HalfDown, "12", 2),
            ("1", "8", 2, HalfUp, "13", 2),
            ("100", "0.5", 0, HalfUp, "200", 0),
            ("1.00", "4", 1, HalfUp, "3", 1),
            ("12345", "1", -2, HalfUp, "123", -2),
            ("0", "7", 3, HalfUp, "0", 3),
            ("1", "1e10", 2, Up, "1", 2),
            ("1", "1e10", 2, Down, "0", 2),
            ("-1", "1e10", 2, Up, "-1", 2),
            ("1e-5", "1e-2147483647", -2147483642, Down, "1", -2147483642),
        ] {
            let answered = d(dividend)
                .divide(&d(divisor), scale, mode)
                .unwrap_or_else(|| panic!("{dividend} / {divisor}"));
            assert_eq!(
                shown(&answered),
                (unscaled.to_string(), answered_scale),
                "{dividend} / {divisor} at {scale} {mode:?}"
            );
        }
        assert!(d("1").divide(&d("1e-2147483647"), 0, Up).is_none());
    }

    /// Plain notation keeps the scale: trailing zeros after the point, and the whole zeros a
    /// negative scale stands for, never an exponent.
    #[test]
    fn plain_text_is_the_value_at_its_scale() {
        for (value, text) in [
            ("1000.00", "1000.00"),
            ("0.001", "0.001"),
            ("-0.5", "-0.5"),
            ("12e2", "1200"),
            ("0e3", "0"),
            ("0.000", "0.000"),
            ("1e-7", "0.0000001"),
            ("-123", "-123"),
        ] {
            assert_eq!(
                d(value).plain_text(STRING_HOLDS).as_deref(),
                Some(text),
                "{value}"
            );
        }
        assert_eq!(d("1e-2147483647").plain_text(STRING_HOLDS), None);
        assert_eq!(d("1e2147483647").plain_text(STRING_HOLDS), None);
        let longest = Amount::from_trusted_parts(false, &[1], (STRING_HOLDS - 2) as i32);
        assert_eq!(longest.plain_length(), STRING_HOLDS);
        let past = Amount::from_trusted_parts(false, &[1], (STRING_HOLDS - 1) as i32);
        assert_eq!(past.plain_length(), STRING_HOLDS + 1);
        assert_eq!(past.plain_text(STRING_HOLDS), None);
    }

    /// Two values of one amount are written one way at a boundary, an exponent is spelt out into a
    /// thousand digits and no more, and the JVM's `toString` decides where a point goes.
    #[test]
    fn a_value_is_written_at_a_boundary_as_its_amount() {
        for (value, written) in [
            ("1.50", "1.5"),
            ("1.5", "1.5"),
            ("100.00", "100"),
            ("1e2", "100"),
            ("0.000", "0"),
            ("-0.0", "0"),
            ("-2.500", "-2.5"),
            ("0.0000001", "1E-7"),
            ("0.000001", "0.000001"),
            ("1.2300e-10", "1.23E-10"),
            ("1e999", &format!("1{}", "0".repeat(999))),
            ("1e1000", "1E+1000"),
            ("10e998", &format!("1{}", "0".repeat(999))),
            ("1e1000000", "1E+1000000"),
            ("123456789e992", "1.23456789E+1000"),
            ("12345678e992", &format!("12345678{}", "0".repeat(992))),
        ] {
            assert_eq!(d(value).external_text(), written, "{value}");
        }
        // The scale stops at its smallest, and the digits it could not drop stay.
        let floor = Amount::from_trusted_parts(false, &[10], i32::MIN);
        assert_eq!(floor.least_digits(), floor);
        let above = Amount::from_trusted_parts(false, &[100], i32::MIN + 1);
        assert_eq!(above.least_digits(), floor);
    }

    #[test]
    fn parts_are_read_back_as_the_value_they_were_taken_from() {
        for value in [
            "0",
            "-0.00",
            "1",
            "-1",
            "255",
            "256",
            "-123456789012345678901.5",
        ] {
            d(value).with_parts(|negative, magnitude, scale| {
                assert_eq!(
                    Amount::from_trusted_parts(negative, magnitude, scale),
                    d(value),
                    "{value}"
                );
                assert_ne!(magnitude.last(), Some(&0), "{value}");
            });
        }
        assert_eq!(shown(&Amount::of_int(i64::MIN)), (i64::MIN.to_string(), 0));
    }

    /// A value read into a `Rational` and narrowed back at its own scale is the value it was.
    #[test]
    fn a_value_is_the_value_its_rational_narrows_back_to() {
        for value in [
            "0",
            "-0.00",
            "1.50",
            "-12.345",
            "1e2",
            "123456789012345678901234567890.1",
        ] {
            let read = d(value);
            let back = Ratio::of_decimal(&read)
                .to_decimal(i64::from(read.scale()), Rounding::Down)
                .expect("a value at its own scale");
            assert_eq!(back, read, "{value}");
        }
    }
}
