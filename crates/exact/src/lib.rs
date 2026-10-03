//! Exact arithmetic as the language states it: the whole numbers a `Decimal` is worked out with,
//! the rounding a mode names, and the `Rational` the `/` operator answers (spec §primitives,
//! §stdlib-decimal, §stdlib-rational).
//!
//! What a value is and what an operation on it answers is a question about numbers, and every
//! runtime that answers it has to answer it the same way. So it is answered here once, over values
//! and nothing else: no arena, no address of either runtime's width, no layout, no way of ending a
//! run. A runtime keeps a value's parts where it keeps things, reads them back into these types,
//! and decides what a [`Failure`] ends the run as. `no_std`, because the WebAssembly runtime is.

#![cfg_attr(not(test), no_std)]

extern crate alloc;

mod amount;
mod enclosure;
mod magnitude;
mod ratio;
mod rounding;

pub use amount::Amount;
pub use magnitude::{Magnitude, TENS};
pub use ratio::{Exact, Failure, Ratio, Scaled};
pub use rounding::{Dropped, Rounding, dropped, rounded};

/// How many bits a whole number held here may be at most: the integer of a `Decimal`, and the
/// numerator or the denominator of a `Rational`.
///
/// The language states the range of a scale and not of the integer, and a representation has to
/// stop somewhere: this is where the JVM's `BigInteger` stops, so that a result one carrier holds is
/// one the other holds too. A result past it has no place, and the operation that would have built
/// it refuses (spec §an-operation-refuses-only-what-its-own-answer-has-no-place-for).
pub const WIDEST: u64 = i32::MAX as u64;
