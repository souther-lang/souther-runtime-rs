//! Which of the two whole numbers either side of a value a rounding answers.
//!
//! A `Decimal` rounded to a scale and a `Rational` rounded to a scale or to an `Int` are both a
//! quotient and what the division dropped, and a mode that says what to do with what was dropped.
//! That decision is one, whoever divided.

use crate::magnitude::Magnitude;
use core::cmp::Ordering;

/// A rounding mode, as `RoundingMode` declares its cases (spec §stdlib-decimal). Each says which of
/// the two whole numbers of the scale's grid either side of a value it answers.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Rounding {
    HalfUp,
    HalfEven,
    HalfDown,
    Up,
    Down,
    Ceiling,
    Floor,
}

/// What rounding dropped, measured against half of the unit it rounded to.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Dropped {
    Nothing,
    BelowHalf,
    Half,
    AboveHalf,
}

impl Rounding {
    /// Whether a magnitude rounded towards nought is taken one further from nought instead: the
    /// whole of what this mode decides, given whether the value is below nought, whether the
    /// magnitude kept is odd, and what was dropped.
    ///
    /// A runtime that holds its digits in a representation of its own works those three out of
    /// it and asks this, so that what a mode means is said here and nowhere else. [`rounded`] is
    /// this over a [`Magnitude`].
    pub fn rounds_away(self, negative: bool, odd: bool, dropped: Dropped) -> bool {
        if dropped == Dropped::Nothing {
            return false;
        }
        match self {
            Rounding::Up => true,
            Rounding::Down => false,
            Rounding::Ceiling => !negative,
            Rounding::Floor => negative,
            Rounding::HalfUp => dropped >= Dropped::Half,
            Rounding::HalfDown => dropped == Dropped::AboveHalf,
            Rounding::HalfEven => {
                dropped == Dropped::AboveHalf || (dropped == Dropped::Half && odd)
            }
        }
    }
}

/// What a remainder is, against half the divisor it was left by: twice the remainder against the
/// divisor is the remainder against what the divisor leaves above it.
pub fn dropped(remainder: &Magnitude, divisor: &Magnitude) -> Dropped {
    if remainder.is_zero() {
        return Dropped::Nothing;
    }
    match remainder.cmp(&divisor.sub(remainder)) {
        Ordering::Less => Dropped::BelowHalf,
        Ordering::Equal => Dropped::Half,
        Ordering::Greater => Dropped::AboveHalf,
    }
}

/// The quotient, rounded by `mode` from what the division dropped.
pub fn rounded(quotient: Magnitude, negative: bool, dropped: Dropped, mode: Rounding) -> Magnitude {
    if mode.rounds_away(negative, quotient.is_odd(), dropped) {
        quotient.increment()
    } else {
        quotient
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The table `java.math.RoundingMode` documents each mode with, which is what the JVM backend
    /// rounds by: 5.5, 2.5, 1.6, 1.1, 1.0 and their opposites, each as the magnitude kept, its
    /// sign and what was dropped, against the whole number each mode answers.
    #[test]
    fn every_mode_answers_what_the_jvm_documents_it_to() {
        let values = [
            (5, false, Dropped::Half),
            (2, false, Dropped::Half),
            (1, false, Dropped::AboveHalf),
            (1, false, Dropped::BelowHalf),
            (1, false, Dropped::Nothing),
            (1, true, Dropped::Nothing),
            (1, true, Dropped::BelowHalf),
            (1, true, Dropped::AboveHalf),
            (2, true, Dropped::Half),
            (5, true, Dropped::Half),
        ];
        let table = [
            (Rounding::Up, [6, 3, 2, 2, 1, -1, -2, -2, -3, -6]),
            (Rounding::Down, [5, 2, 1, 1, 1, -1, -1, -1, -2, -5]),
            (Rounding::Ceiling, [6, 3, 2, 2, 1, -1, -1, -1, -2, -5]),
            (Rounding::Floor, [5, 2, 1, 1, 1, -1, -2, -2, -3, -6]),
            (Rounding::HalfUp, [6, 3, 2, 1, 1, -1, -1, -2, -3, -6]),
            (Rounding::HalfDown, [5, 2, 2, 1, 1, -1, -1, -2, -2, -5]),
            (Rounding::HalfEven, [6, 2, 2, 1, 1, -1, -1, -2, -2, -6]),
        ];
        for (mode, answers) in table {
            for ((kept, negative, dropped), answer) in values.into_iter().zip(answers) {
                let away = mode.rounds_away(negative, kept % 2 == 1, dropped);
                let magnitude = kept + i64::from(away);
                let got = if negative { -magnitude } else { magnitude };
                assert_eq!(
                    got, answer,
                    "{mode:?} of {kept} {dropped:?}, negative {negative}"
                );
                let through = rounded(Magnitude::of_u128(kept as u128), negative, dropped, mode);
                assert_eq!(through.as_u128(), Some(magnitude as u128));
            }
        }
    }
}
