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
    /// Whether a magnitude rounded towards nought is taken one further from nought instead.
    fn away(self, negative: bool, odd: bool, dropped: Dropped) -> bool {
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
    if mode.away(negative, quotient.is_odd(), dropped) {
        quotient.increment()
    } else {
        quotient
    }
}
