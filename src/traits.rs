// SPDX-FileCopyrightText: 2025 Google LLC
//
// SPDX-License-Identifier: Apache-2.0
//! Helper traits for the other modules in this crate

/// Guarantees the presence of `.saturating_add()` as implemented on the numeric types.
pub const trait SaturatingAdd<Rhs = Self> {
    /// Output type from [`saturating_add`](SaturatingAdd::saturating_add)
    type Output;

    /// Wrapper function for `saturating_add`
    fn saturating_add(self, rhs: Rhs) -> Self::Output;
}

/// Guarantees the presence of `.saturating_sub()` as implemented on the numeric types.
pub const trait SaturatingSub<Rhs = Self> {
    /// Output type from [`saturating_sub`](SaturatingSub::saturating_sub)
    type Output;

    /// Wrapper function for `saturating_sub`
    fn saturating_sub(self, rhs: Rhs) -> Self::Output;
}

/// Assigning version of [`SaturatingAdd`]
pub const trait SaturatingAddAssign<Rhs = Self> {
    /// Assigning version of [`saturating_add`](SaturatingAdd::saturating_add)
    fn saturating_add_assign(&mut self, rhs: Rhs);
}

/// Assigning version of [`SaturatingSub`]
pub const trait SaturatingSubAssign<Rhs = Self> {
    /// Assigning version of [`saturating_sub`](SaturatingSub::saturating_sub)
    fn saturating_sub_assign(&mut self, rhs: Rhs);
}

subst_macros::repeat_parallel_subst! {
    groups: [
        [group [sub [TYPE] = [u8]]]
        [group [sub [TYPE] = [u16]]]
        [group [sub [TYPE] = [u32]]]
        [group [sub [TYPE] = [u64]]]
        [group [sub [TYPE] = [u128]]]
        [group [sub [TYPE] = [usize]]]
    ],
    callback: [
        macro: subst_macros::repeat_parallel_subst,
        prefix: [
            @callback
            groups: [
                [group
                    [sub [TRAIT] = [SaturatingAdd]]
                    [sub [TRAITASSIGN] = [SaturatingAddAssign]]
                    [sub [FN] = [saturating_add]]
                    [sub [FNASSIGN] = [saturating_add_assign]]
                ]
                [group
                    [sub [TRAIT] = [SaturatingSub]]
                    [sub [TRAITASSIGN] = [SaturatingSubAssign]]
                    [sub [FN] = [saturating_sub]]
                    [sub [FNASSIGN] = [saturating_sub_assign]]
                ]
            ],
            callback: NONE,
        ],
        suffix: [],
    ],
    in: {
        crate::macros::copyable_op_impl! {
            @noassign
            gen = [],
            Lhs = TYPE,
            Rhs = TYPE,
            where = [],
            TRAIT::FN(self, rhs): {
                TYPE::FN(LDEREF self, RDEREF rhs)
            }
        }

        crate::macros::copyable_op_impl! {
            @assign
            gen = [],
            Lhs = TYPE,
            Rhs = TYPE,
            where = [],
            TRAITASSIGN::FNASSIGN(self, rhs): {
                *self = TYPE::FN(LDEREF self, RDEREF rhs);
            }
        }
    }
}

/// Convenience type to access the inner type of a generic type with one parameter, discarding
/// references
pub const trait InnerTy {
    /// The inner type (without references)
    type Inner;
}

/// Convenience alias to retrieve [`InnerTy::Inner`]
pub type GetInnerTy<T> = <T as InnerTy>::Inner;

impl<const N: u128> InnerTy for crate::index::Index<N>
where
    crate::index::IndexLut<N>: const crate::index::HasIndexBacker,
{
    type Inner = crate::index::IndexBackerOf<N>;
}

impl<'a, const N: u128> InnerTy for &'a crate::index::Index<N>
where
    crate::index::IndexLut<N>: const crate::index::HasIndexBacker,
{
    type Inner = &'a crate::index::IndexBackerOf<N>;
}
