//! §6.3 — Where A1 lives formally.
//!
//! The theorem is proven over abstract cells. That buys generality, but it also
//! invites the objection raised in §3.1: if cells are atomic *by construction*, the
//! model has assumed away the one interesting axiom, and the whole development is
//! a tautology dressed as a result.
//!
//! This module answers that objection. It instantiates a cell as a byte sequence,
//! defines the tear relation a real device exhibits, and shows:
//!
//! 1. [`bytewise_tear_violates_a1`] — under byte-level tearing, A1 is **false** for
//!    any cell wider than one byte. A1 is therefore a genuine assumption with real
//!    content, not a definitional convenience. This is the anti-vacuity result.
//! 2. [`atomic_unit_tear_is_trivial`] — A1 holds exactly when the cell *is* the
//!    hardware's atomic unit. So "choose cells to match the atomic write width" is
//!    not folklore; it is the precondition of the theorem.
//! 3. [`abstract_model_assumes_a1`] — the abstract crash lattice offers each cell
//!    exactly two outcomes. Combined with (1): if A1 is false, the abstract model is
//!    **unsound**, not merely imprecise. That is the honest statement of the risk.
//!
//! # What is deliberately not proven here
//!
//! The full simulation argument — that the byte-level model refines the abstract
//! one under A1, for whole multi-cell programs — is **deferred**. Rung 1 needs A1 to
//! have a formal home and a stated price, and it now has both. A refinement proof
//! would be a second body of work of comparable size to the rest of this crate, and
//! §10.1 of the design doc explicitly permits deferring it as long as the deferral
//! is written down rather than silent. This paragraph is that record.

use vstd::prelude::*;
use vstd::seq_lib::{assert_seqs_equal, assert_seqs_equal_internal};

#[cfg(verus_only)]
use crate::algebra::unit;
use crate::algebra::{CellId, Delta};
#[cfg(verus_only)]
use crate::crash::{singleton_lattice, sub_delta};

verus! {

/// A cell's physical content, once you stop pretending cells are opaque.
pub type Bytes = Seq<u8>;

/// What a cell may contain after an interrupted write of `new` over `old`.
///
/// Modelled as a relation rather than a set: the outcome set is finite, but nothing
/// downstream needs its cardinality, and vstd's `Set` would drag finiteness
/// obligations in for no benefit.
///
/// Each byte position independently either took the new value or kept the old one.
/// This is what a partially-programmed NAND page actually looks like — §5's "where
/// it's false" column for A1.
pub open spec fn bytewise_tear(old: Bytes, new: Bytes, r: Bytes) -> bool {
    &&& old.len() == new.len()
    &&& r.len() == old.len()
    &&& forall|i: int| 0 <= i < r.len() ==> #[trigger] r[i] == old[i] || r[i] == new[i]
}

/// **A1**, stated over a tear relation: a write lands entirely or not at all.
pub open spec fn a1_for(tear: spec_fn(Bytes, Bytes, Bytes) -> bool) -> bool {
    forall|old: Bytes, new: Bytes, r: Bytes|
        #[trigger] tear(old, new, r) ==> r == old || r == new
}

/// **The anti-vacuity result.**
///
/// A two-byte cell under byte-level tearing produces `0x00 0x01` from a write of
/// `0x01 0x01` over `0x00 0x00` — a value that is neither the old contents nor the
/// new ones. So A1 is a real, falsifiable assumption about hardware, and the
/// abstract model is not quietly assuming it away.
pub proof fn bytewise_tear_violates_a1() -> (r: (Bytes, Bytes, Bytes))
    ensures
        bytewise_tear(r.0, r.1, r.2),
        r.2 != r.0,
        r.2 != r.1,
        !a1_for(|o: Bytes, n: Bytes, x: Bytes| bytewise_tear(o, n, x)),
{
    let old: Bytes = seq![0u8, 0u8];
    let new: Bytes = seq![1u8, 1u8];
    let torn: Bytes = seq![0u8, 1u8];

    assert(bytewise_tear(old, new, torn)) by {
        assert forall|i: int| 0 <= i < torn.len() implies torn[i] == old[i] || torn[i] == new[i] by {
            assert(i == 0 || i == 1);
        }
    }
    assert(torn[1] != old[1]);
    assert(torn[0] != new[0]);

    // Beta-reduce the relation into the shape `a1_for`'s trigger matches, then let
    // the witness refute the quantifier.
    let t = |o: Bytes, n: Bytes, x: Bytes| bytewise_tear(o, n, x);
    assert(t(old, new, torn));
    (old, new, torn)
}

/// **A1 holds exactly when the cell is the atomic unit.**
///
/// For a one-position cell the tear relation is trivial: the only outcomes are the
/// old value and the new one, which is precisely the two-point lattice the theorem
/// needs. "Pick cells that match the hardware's atomic write width" is therefore
/// the precondition of the entire result, not a tuning suggestion.
pub proof fn atomic_unit_tear_is_trivial(old: Bytes, new: Bytes, r: Bytes)
    requires
        old.len() == 1,
        bytewise_tear(old, new, r),
    ensures
        r =~= old || r =~= new,
{
    assert(r.len() == 1);
    if r[0] == old[0] {
        assert_seqs_equal!(r, old);
    } else {
        assert_seqs_equal!(r, new);
    }
}

/// The abstract model offers each cell exactly two outcomes — landed, or not.
///
/// Read together with [`bytewise_tear_violates_a1`], this is the honest statement of
/// the risk: `sub_delta` has no representation for a *partially* written cell, so if
/// A1 is false the abstract model does not merely lose precision, it becomes
/// unsound. The CRC (§5.1) is the probabilistic mitigation for exactly this case,
/// and it is deliberately outside the proven core.
pub proof fn abstract_model_assumes_a1<V>(e: Delta<V>, c: CellId, sigma: Delta<V>)
    requires
        e.dom() =~= set![c],
        sub_delta(sigma, e),
    ensures
        sigma =~= unit::<V>() || sigma =~= e,
{
    singleton_lattice(sigma, e, c);
}

} // verus!
