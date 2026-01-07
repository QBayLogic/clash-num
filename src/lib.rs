// SPDX-FileCopyrightText: 2025 Google LLC
//
// SPDX-License-Identifier: Apache-2.0
//! Clash numeric types ([`BitVec<N>`][btv], [`Index<N>`][idx], [`Unsigned<N>`][uns],
//! [`Signed<N>`][sgn]) mirrored in Rust.
//!
//! # What is this crate for?
//! This crate reimplements the four numeric types commonly used in the [Clash hardware description
//! language](https://clash-lang.org/). The purpose for this is that [`clash-protocols-memmap`][cpm]
//! provides a way to expose memory-mapped peripherals to a CPU, and generally these types are put
//! through an instance of `BitPackC` from [`clash-bitpackc`][cbp]. It seems desirable that
//! programmers should be able to talk about Clash types in Rust without having to refer to their
//! monomorphized translation into Rust.
//!
//! # Type representation
//! These types will choose the most appropriate backing type for their const generic parameter,
//! which will always be one of the following:
//! - `u8`
//! - `u16`
//! - `u32`
//! - `u64`
//! - `u128`
//! - `[u8; N]` (with the smallest possible `N` for the given type)
//!
//! [`BitVec<N>`][btv] will always choose a `[u8; N]`, and the other three will always choose an
//! unsigned primitive. It should be possible to extend [`Unsigned<N>`][uns] and [`Signed<N>`][sgn]
//! to arbitrary sizes as well, though it has not been done at time of writing since it makes little
//! to no sense to have anything larger than an `Unsigned<128>` or `Signed<128>` in hardware.
//!
//! # Compiler features
//!
//! This crate makes use of the following list of nightly features:
//! ```
//! #![cfg_attr(test, feature(bigint_helper_methods))]
//! #![feature(
//!     const_cmp,
//!     const_convert,
//!     const_index,
//!     const_ops,
//!     const_option_ops,
//!     const_trait_impl,
//!     generic_const_exprs,
//!     macro_metavar_expr,
//! )]
//! ```
//! Here's the rationale for each of these:
//! - `bigint_helper_methods`: It was difficult to come up with a way to test
//!   [`Shl`](core::ops::Shl) for [`BitVec<N>`][btv] without just copying the implementation.
//!   The operation `a << b` is the same as `a * 2.pow(b)`, so [`u8::carrying_mul`] is used to
//!   generate expected values in the tests. This feature is not used outside of testing, so it is
//!   gated on that.
//! - `const_cmp`, `const_convert`, `const_index`, `const_ops`, `const_option_ops`,
//!   `const_trait_impl`: The numeric types provided by these crates are supposed to be primitives
//!   of a sort, and it seemed desirable to be able to work with them in a `const` context - whether
//!   for creating `const`s, or in `const fn`s. As such, all operator traits are done as
//!   `impl const`, and it was necessary to enable these features to accomplish this.
//! - `generic_const_exprs`: This feature enables the mechanism for choosing the backing types for
//!   the numeric types. See the next section for how this works.
//! - `macro_metavar_expr`: This crate makes prodigious use of the macros in [`subst_macros`], with
//!   the `macro_metavar_expr` feature enabled on that crate. It's an infectious feature, so it
//!   was necessary to enable it here too.
//!
//! # Choosing backing types
//!
//! Backing types are chosen by a "trait look-up table" (informal name, uncertain that there is an
//! actual term for this). To define a trait LUT, one needs a "backer" trait, a marker type that
//! will be used to provide LUT entries (which generally must expose the input and output of the
//! mapping function for `impl`s), and a type alias that maps an input parameter to the LUT marker
//! type. The LUT entries are provided through `impl`s in terms of the lookup type. For instance,
//! here is how the trait LUT for [`Unsigned<N>`][uns] is defined:
//! ```
//! # #![feature(
//! #     const_cmp,
//! #     const_convert,
//! #     const_index,
//! #     const_ops,
//! #     const_option_ops,
//! #     const_trait_impl,
//! #     generic_const_exprs,
//! #     macro_metavar_expr
//! # )]
//! # #![allow(incomplete_features)]
//! # use clash_num::numeric_size;
//! // The "backer" trait. This must provide all of the primitive operations needed in `impl`s for
//! // the `Unsigned<N>` type, as well as any necessary constants.
//! pub const trait HasUnsignedBacker: Sized {
//!     type Type: Copy + const PartialEq + const Eq;
//!     const MIN: Self::Type;
//!     const MAX: Self::Type;
//!
//!     type Mask: Copy + const PartialEq + const Eq;
//!     const MASK: Self::Mask;
//!     fn apply_mask_to(val: &mut Self::Type);
//!     fn apply_mask(val: Self::Type) -> Self::Type {
//!         let mut val = val;
//!         Self::apply_mask_to(&mut val);
//!         val
//!     }
//!
//!     fn bounds_check(val: &Self::Type) -> bool;
//! }
//!
//! // This is the marker type used to define the LUT entries. The `M` parameter is treated as the
//! // input parameter, and the `N` parameter is treated as the output parameter.
//! pub struct UnsignedLutInner<const M: u8, const N: u8>;
//!
//! // Here's the type that maps the input to the marker type:
//! pub type UnsignedLut<const N: u8> = UnsignedLutInner<N, { numeric_size(N) }>;
//! // And here's a convenience alias to retrieve the backing type for a given `Unsigned<N>`:
//! pub type UnsignedBackerOf<const N: u8> = <UnsignedLut<N> as HasUnsignedBacker>::Type;
//!
//! // Then provide each of the LUT entries as `impl`s ():
//! impl<const N: u8> const HasUnsignedBacker for UnsignedLutInner<N, 1> {
//!     type Type = u8;
//!     // ...
//! #     const MIN: Self::Type = 0;
//! #     const MAX: Self::Type = !(!0 << N);
//! #     type Mask = u8;
//! #     const MASK: Self::Mask = {
//! #         if N == 8 {
//! #             !0
//! #         } else {
//! #             !(!0 << N)
//! #         }
//! #     };
//! #     fn apply_mask_to(val: &mut Self::Type) {
//! #         *val &= Self::MASK;
//! #     }
//! #     fn bounds_check(val: &Self::Type) -> bool {
//! #         Self::MASK.ge(val)
//! #     }
//! }
//!
//! impl<const N: u8> const HasUnsignedBacker for UnsignedLutInner<N, 2> {
//!     type Type = u16;
//!     // ...
//! #     const MIN: Self::Type = 0;
//! #     const MAX: Self::Type = !(!0 << N);
//! #     type Mask = u16;
//! #     const MASK: Self::Mask = {
//! #         if N == 16 {
//! #             !0
//! #         } else {
//! #             !(!0 << N)
//! #         }
//! #     };
//! #     fn apply_mask_to(val: &mut Self::Type) {
//! #         *val &= Self::MASK;
//! #     }
//! #     fn bounds_check(val: &Self::Type) -> bool {
//! #         Self::MASK.ge(val)
//! #     }
//! }
//!
//! impl<const N: u8> const HasUnsignedBacker for UnsignedLutInner<N, 4> {
//!     type Type = u32;
//!     // ...
//! #     const MIN: Self::Type = 0;
//! #     const MAX: Self::Type = !(!0 << N);
//! #     type Mask = u32;
//! #     const MASK: Self::Mask = {
//! #         if N == 32 {
//! #             !0
//! #         } else {
//! #             !(!0 << N)
//! #         }
//! #     };
//! #     fn apply_mask_to(val: &mut Self::Type) {
//! #         *val &= Self::MASK;
//! #     }
//! #     fn bounds_check(val: &Self::Type) -> bool {
//! #         Self::MASK.ge(val)
//! #     }
//! }
//!
//! impl<const N: u8> const HasUnsignedBacker for UnsignedLutInner<N, 8> {
//!     type Type = u64;
//!     // ...
//! #     const MIN: Self::Type = 0;
//! #     const MAX: Self::Type = !(!0 << N);
//! #     type Mask = u64;
//! #     const MASK: Self::Mask = {
//! #         if N == 64 {
//! #             !0
//! #         } else {
//! #             !(!0 << N)
//! #         }
//! #     };
//! #     fn apply_mask_to(val: &mut Self::Type) {
//! #         *val &= Self::MASK;
//! #     }
//! #     fn bounds_check(val: &Self::Type) -> bool {
//! #         Self::MASK.ge(val)
//! #     }
//! }
//!
//! impl<const N: u8> const HasUnsignedBacker for UnsignedLutInner<N, 16> {
//!     type Type = u128;
//!     // ...
//! #     const MIN: Self::Type = 0;
//! #     const MAX: Self::Type = !(!0 << N);
//! #     type Mask = u128;
//! #     const MASK: Self::Mask = {
//! #         if N == 128 {
//! #             !0
//! #         } else {
//! #             !(!0 << N)
//! #         }
//! #     };
//! #     fn apply_mask_to(val: &mut Self::Type) {
//! #         *val &= Self::MASK;
//! #     }
//! #     fn bounds_check(val: &Self::Type) -> bool {
//! #         Self::MASK.ge(val)
//! #     }
//! }
//! ```
//! Both [`Signed<N>`][sgn] and [`Index<N>`][idx] use similar setups in order to provide their
//! backing types, though this is not necessary for [`BitVec<N>`][btv] since it's always backed
//! by a byte array.
//!
//! # Future work
//!
//! If so desired, it should be possible to extend [`Unsigned<N>`][uns] and [`Signed<N>`][sgn] to
//! arbitrary sizes (limited by the size of the const generic parameter). This would first be done
//! by changing `pub struct Unsigned<const N: u8>(...)` into
//! `pub struct Unsigned<const N: u16>(...)`, and then changing the definition of [`numeric_size`]
//! to return a known value that denotes a value should be backed by an array:
//! ```
//! /// Translate the number of bits in a numeric type into a trait LUT entry number
//! pub const fn numeric_size(n: u16) -> u8 {
//!     assert!(n != 0, "Cannot represent 0 bits!");
//!     let nbytes = n.div_ceil(8);
//!     if (nbytes as usize) <= size_of::<u128>() {
//!         // Can be represented as a Rust unsigned integer primitive, give back the number of
//!         // bytes in the primitive
//!         nbytes.next_power_of_two() as u8
//!     } else {
//!         // Backing type should be an array
//!         17
//!     }
//! }
//! ```
//! It would also be necessary to introduce a `Mask` type to the
//! [`HasUnsignedBacker`](unsigned::HasUnsignedBacker) trait, since the type we want to use to mask
//! arrays isn't the same as the `Type` associated type.
//! ```
//! # #![feature(
//! #     const_cmp,
//! #     const_convert,
//! #     const_index,
//! #     const_ops,
//! #     const_option_ops,
//! #     const_trait_impl,
//! #     generic_const_exprs,
//! #     macro_metavar_expr
//! # )]
//! # #![allow(incomplete_features)]
//! # pub const fn numeric_size(n: u16) -> u8 {
//! #     assert!(n != 0, "Cannot represent 0 bits!");
//! #     let nbytes = n.div_ceil(8);
//! #     if (nbytes as usize) <= size_of::<u128>() {
//! #         nbytes.next_power_of_two() as u8
//! #     } else {
//! #         17
//! #     }
//! # }
//! pub const trait HasUnsignedBacker: Sized {
//!     type Type: Copy + const PartialEq + const Eq;
//!     const MIN: Self::Type;
//!     const MAX: Self::Type;
//!
//!     type Mask: Copy + const PartialEq + const Eq;
//!     const MASK: Self::Mask;
//!     fn apply_mask_to(val: &mut Self::Type);
//!
//!     fn apply_mask(val: Self::Type) -> Self::Type {
//!         let mut val = val;
//!         Self::apply_mask_to(&mut val);
//!         val
//!     }
//!
//!     fn bounds_check(val: &Self::Type) -> bool;
//! }
//!
//! pub struct UnsignedLutInner<const M: u16, const N: u8>;
//! pub type UnsignedLut<const N: u16> = UnsignedLutInner<N, { numeric_size(N) }>;
//! ```
//! For all other types `Mask` would just be `Self`, but for arrays it would be `u8`. This is
//! because for array-backed type the only unset bits are in the most significant byte, which is
//! just a `u8`. In order to mask it, then, we just need to do a bitand on the most significant
//! byte, rather than on each byte in the array. The next step is to create a new trait LUT entry
//! for array-backed types. Here's what such an `impl` might look like for [`Unsigned<N>`][uns]:
//! ```
//! # #![feature(
//! #     const_cmp,
//! #     const_convert,
//! #     const_index,
//! #     const_ops,
//! #     const_option_ops,
//! #     const_trait_impl,
//! #     generic_const_exprs,
//! #     macro_metavar_expr
//! # )]
//! # #![allow(incomplete_features)]
//! # pub const trait HasUnsignedBacker: Sized {
//! #     type Type: Copy + const PartialEq + const Eq;
//! #     const MIN: Self::Type;
//! #     const MAX: Self::Type;
//! #     type Mask: Copy + const PartialEq + const Eq;
//! #     const MASK: Self::Mask;
//! #     fn apply_mask_to(val: &mut Self::Type);
//! #     fn apply_mask(val: Self::Type) -> Self::Type {
//! #         let mut val = val;
//! #         Self::apply_mask_to(&mut val);
//! #         val
//! #     }
//! #     fn bounds_check(val: &Self::Type) -> bool;
//! # }
//! # pub struct UnsignedLutInner<const M: u16, const N: u8>;
//! impl<const N: u16> const HasUnsignedBacker for UnsignedLutInner<N, 17>
//! where
//!     [(); N.div_ceil(8) as usize]:,
//! {
//!     type Type = [u8; N.div_ceil(8) as usize];
//!     const MIN: Self::Type = [0; _];
//!     const MAX: Self::Type = {
//!         let mut out = [0; _];
//!         out[const { N.div_ceil(8) as usize - 1 }] = Self::MASK;
//!         out
//!     };
//!     type Mask = u8;
//!     const MASK: Self::Mask = if N.is_multiple_of(8) { !0 } else { !(!0 << (N % 8)) };
//!     fn apply_mask_to(val: &mut Self::Type) {
//!         val[const { N.div_ceil(8) as usize - 1 }] &= Self::MASK;
//!     }
//!     fn bounds_check(val: &Self::Type) -> bool {
//!         val[const { N.div_ceil(8) as usize - 1 }] <= Self::MASK
//!     }
//! }
//! ```
//! Then it would be necessary to create and implement wrapper traits for all of the operations that
//! are desired, since it would no longer be true that all of the backing types implement the
//! primitive operations such as [`Add`](core::ops::Add), [`BitOr`](core::ops::BitOr), and so on.
//! Then the core ops can be implemented in terms of these wrapper traits:
//! ```
//! # #![feature(const_trait_impl, generic_const_exprs)]
//! # #![allow(incomplete_features)]
//! # pub const trait HasUnsignedBacker: Sized {
//! #     type Type;
//! # }
//! # pub struct UnsignedLutInner<const M: u16, const N: u8>;
//! # pub type UnsignedLut<const N: u16> = UnsignedLutInner<N, { N as u8 }>;
//! # pub type UnsignedBackerOf<const N: u16> = <UnsignedLut<N> as HasUnsignedBacker>::Type;
//! # struct Unsigned<const N: u16>(pub(crate) UnsignedBackerOf<N>)
//! # where
//! #     UnsignedLut<N>: HasUnsignedBacker;
//! # pub const fn masked<const N: u16>(val: UnsignedBackerOf<N>) -> UnsignedBackerOf<N>
//! # where
//! #     UnsignedLut<N>: HasUnsignedBacker,
//! # {
//! #     unimplemented!()
//! # }
//! pub const trait UnsignedAdd<Rhs = Self> {
//!     type Output;
//!
//!     fn unsigned_add(self, rhs: Rhs) -> Self::Output;
//! }
//!
//! // `UnsignedAdd` will just be an alias impl for `core::ops::Add` for all unsigned primitives,
//! // but it would be necessary to do...
//!
//! impl<const N: usize> const UnsignedAdd<[u8; N]> for [u8; N] {
//!     type Output = [u8; N];
//!
//!     fn unsigned_add(self, rhs: [u8; N]) -> Self::Output {
//!         // ...
//!         # unimplemented!()
//!     }
//! }
//!
//! impl<'a, const N: usize> const UnsignedAdd<&'a [u8; N]> for [u8; N] {
//!     type Output = [u8; N];
//!
//!     fn unsigned_add(self, rhs: &'a [u8; N]) -> Self::Output {
//!         // ...
//!         # unimplemented!()
//!     }
//! }
//!
//! impl<'a, const N: usize> const UnsignedAdd<[u8; N]> for &'a [u8; N] {
//!     type Output = [u8; N];
//!
//!     fn unsigned_add(self, rhs: [u8; N]) -> Self::Output {
//!         // ...
//!         # unimplemented!()
//!     }
//! }
//!
//! impl<'a, 'b, const N: usize> const UnsignedAdd<&'b [u8; N]> for &'a [u8; N] {
//!     type Output = [u8; N];
//!
//!     fn unsigned_add(self, rhs: &'b [u8; N]) -> Self::Output {
//!         // ...
//!         # unimplemented!()
//!     }
//! }
//!
//! // Now we can implement `core::ops::Add` for `Unsigned<N>`:
//!
//! impl<const N: u16> core::ops::Add<Unsigned<N>> for Unsigned<N>
//! where
//!     UnsignedLut<N>: HasUnsignedBacker,
//!     UnsignedBackerOf<N>: UnsignedAdd<UnsignedBackerOf<N>, Output = UnsignedBackerOf<N>>,
//! {
//!     type Output = Unsigned<N>;
//!
//!     fn add(self, rhs: Unsigned<N>) -> Self::Output {
//!         Unsigned(masked(self.0.unsigned_add(rhs.0)))
//!     }
//! }
//!
//! impl<'a, const N: u16> core::ops::Add<&'a Unsigned<N>> for Unsigned<N>
//! where
//!     UnsignedLut<N>: HasUnsignedBacker,
//!     UnsignedBackerOf<N>: UnsignedAdd<&'a UnsignedBackerOf<N>, Output = UnsignedBackerOf<N>>,
//! {
//!     type Output = Unsigned<N>;
//!
//!     fn add(self, rhs: &'a Unsigned<N>) -> Self::Output {
//!         Unsigned(masked(self.0.unsigned_add(&rhs.0)))
//!     }
//! }
//!
//! impl<'a, const N: u16> core::ops::Add<Unsigned<N>> for &'a Unsigned<N>
//! where
//!     UnsignedLut<N>: HasUnsignedBacker,
//!     &'a UnsignedBackerOf<N>: UnsignedAdd<UnsignedBackerOf<N>, Output = UnsignedBackerOf<N>>,
//! {
//!     type Output = Unsigned<N>;
//!
//!     fn add(self, rhs: Unsigned<N>) -> Self::Output {
//!         Unsigned(masked((&self.0).unsigned_add(rhs.0)))
//!     }
//! }
//!
//! impl<'a, 'b, const N: u16> core::ops::Add<&'b Unsigned<N>> for &'a Unsigned<N>
//! where
//!     UnsignedLut<N>: HasUnsignedBacker,
//!     &'a UnsignedBackerOf<N>: UnsignedAdd<&'b UnsignedBackerOf<N>, Output = UnsignedBackerOf<N>>,
//! {
//!     type Output = Unsigned<N>;
//!
//!     fn add(self, rhs: &'b Unsigned<N>) -> Self::Output {
//!         Unsigned(masked((&self.0).unsigned_add(&rhs.0)))
//!     }
//! }
//! ```
//! If it's useful enough it would be possible to create this, however as stated previously it
//! doesn't really make sense to have `Unsigned<N>` or `Signed<N>` for `N > 128` in hardware, so
//! in order to limit the code complexity in this crate such implementations were not made.
//!
//! [btv]: crate::bitvec::BitVec
//! [idx]: crate::index::Index
//! [uns]: crate::unsigned::Unsigned
//! [sgn]: crate::signed::Signed
//! [cpm]: https://github.com/bittide/bittide-hardware/tree/main/clash-protocols-memmap
//! [cbp]: https://github.com/bittide/bittide-hardware/tree/main/clash-bitpackc

#![cfg_attr(not(test), no_std)]
#![cfg_attr(test, feature(bigint_helper_methods))]
#![feature(
    const_cmp,
    const_convert,
    const_index,
    const_ops,
    const_option_ops,
    const_trait_impl,
    generic_const_exprs,
    macro_metavar_expr,
)]
#![allow(incomplete_features)]
#![deny(missing_docs)]
#![recursion_limit = "340"]

pub mod bitvec;
pub mod index;
pub mod signed;
pub mod traits;
pub mod unsigned;

#[cfg(not(doctest))]
pub(crate) mod macros;
#[cfg(doctest)]
pub mod macros;

/// For a desired numeric type `n` bits wide, produces a `u8` that can be used to perform the lookup
/// in a trait LUT.
///
/// # Panics
///
/// Panics if the input is 0.
// TODO: arbitrary-width support. For this, change `n: u8` to `n: u16`
#[must_use]
pub const fn numeric_size(n: u8) -> u8 {
    assert!(n != 0, "Cannot represent 0 bits!");
    let nbytes = n.div_ceil(8);
    if (nbytes as usize) <= size_of::<u128>() {
        nbytes.next_power_of_two()
    } else {
        const_panic::concat_panic!("Cannot make backer for ", n, " bits");
        // TODO: arbitrary-width support. For this, return `17`.
    }
}

/// For a desired indexable range of `0..n`, produces a `u128` that can be used to perform the lookup
/// in the trait LUT.
///
/// # Panics
///
/// Panics if the input is 0.
#[must_use]
pub const fn index_bit_size(n: u128) -> u8 {
    if n == 0 {
        panic!("Cannot represent `Index<0>`!");
    } else if n <= u8::MAX as u128 + 1 {
        8
    } else if n <= u16::MAX as u128 + 1 {
        16
    } else if n <= u32::MAX as u128 + 1 {
        32
    } else if n <= u64::MAX as u128 + 1 {
        64
    } else {
        128
    }
}

/// Marker struct for use in constraints with `generic_const_exprs`
///
/// These constraints typically take the form of `ConstCheck<{ expr() }>: True` or
/// `ConstCheck<{ expr() }>: False`.
pub struct ConstCheck<const B: bool>;

/// Marks a constraint as `true`
pub trait True {}
impl True for ConstCheck<true> {}
/// Marks a constraint as `false`
pub trait False {}
impl False for ConstCheck<false> {}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    #[should_panic]
    fn test_numeric_size_zero() {
        let _ = numeric_size(0);
    }

    #[test]
    #[should_panic]
    fn test_numeric_size_too_big() {
        let _ = numeric_size(255);
    }

    #[test]
    fn test_numeric_size() {
        let pairs = [
            (1, 1),
            (8, 1),
            (9, 2),
            (16, 2),
            (17, 4),
            (32, 4),
            (33, 8),
            (64, 8),
            (65, 16),
            (128, 16),
        ];
        for (input, expect) in pairs {
            let result = numeric_size(input);
            if result != expect {
                println!("Unexpected numeric size!");
                println!("Input: {input}");
                println!("Expected: {expect}");
                println!("Result: {result}");
                panic!();
            }
        }
    }
}
