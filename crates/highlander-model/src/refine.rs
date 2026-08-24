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
//! # The refinement itself
//!
//! [`physical_crash_is_an_abstract_crash`] is the simulation argument §6.3 asks for.
//! A physical store holds bytes, a crash tears each written cell byte by byte, and
//! under A1 **every physically reachable outcome is an abstract crash outcome**.
//! The abstract model therefore over-approximates the real device, so every result
//! proven about it — the crash-consistency theorem included — holds of the device.
//!
//! [`without_a1_a_physical_crash_escapes_the_model`] is the other half, and it is
//! the reason A1 is an axiom rather than a lemma. Without atomicity there is a
//! physically reachable store that **no** abstract crash outcome describes. The
//! abstract model is then not conservative, it is wrong.

use vstd::map::{assert_maps_equal, assert_maps_equal_internal};
use vstd::prelude::*;
use vstd::seq_lib::{assert_seqs_equal, assert_seqs_equal_internal};
use vstd::set_lib::{assert_sets_equal, assert_sets_equal_internal};

use crate::algebra::{CellId, Delta, Store};
#[cfg(verus_only)]
use crate::algebra::{override_, unit};
#[cfg(verus_only)]
use crate::crash::{
    crash_at, crash_outcome_intro, epochs, is_crash_outcome, prefix_state, singleton_lattice,
    sub_delta,
};

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

// ---------------------------------------------------------------------------
// §6.3 — the refinement
// ---------------------------------------------------------------------------

/// A store as a device holds it: cells of bytes. This is `V = Seq<u8>`, exactly as
/// §6.3 asks.
pub type PhysStore = Store<Bytes>;

/// A crash while epoch `e` is landing.
///
/// A cell the epoch does not write keeps its contents. A cell the epoch does write
/// tears: each byte position independently takes the old value or the new one. No
/// order is assumed, and no cell is assumed to land as a unit — that assumption is
/// A1, and it is stated separately below.
pub open spec fn phys_crash(s0: PhysStore, e: Delta<Bytes>, s2: PhysStore) -> bool {
    &&& e.dom().subset_of(s0.dom())
    &&& s2.dom() =~= s0.dom()
    &&& forall|c: CellId| #![auto]
        s0.dom().contains(c) && !e.dom().contains(c) ==> s2[c] == s0[c]
    &&& forall|c: CellId| #![auto] e.dom().contains(c) ==> bytewise_tear(s0[c], e[c], s2[c])
}

/// **A1, for the cells this epoch writes.**
///
/// Each cell is one atomic unit. `atomic_unit_tear_is_trivial` is what makes this
/// the right statement: at one position, a tear has only the 2 endpoints.
#[cfg(not(feature = "multi-byte-cells"))]
pub open spec fn cells_are_atomic(s0: PhysStore, e: Delta<Bytes>) -> bool {
    forall|c: CellId| #![auto] e.dom().contains(c) ==> s0[c].len() == 1
}

/// **The seventh falsifiability gate (`--features multi-byte-cells`).**
///
/// Drops A1. A cell may then be wider than the atomic write unit, a crash may leave
/// it holding a mixture, and the abstract model has no state to describe that.
/// `refinement_under_a1` must fail with this feature on.
#[cfg(feature = "multi-byte-cells")]
pub open spec fn cells_are_atomic(s0: PhysStore, e: Delta<Bytes>) -> bool {
    true
}

/// **A cell lands whole, or not at all.** A1, stated for a single cell of a real
/// crash — one line, and the whole of the refinement rests on it.
///
/// The hint is guarded so that it simply does not fire when A1 is absent, which
/// leaves the postcondition as the thing that fails. This is the shape a gate target
/// needs: a failure inside a proof reports without a lemma name.
///
/// This is the target of the `multi-byte-cells` gate.
pub proof fn an_atomic_cell_lands_whole(
    s0: PhysStore,
    e: Delta<Bytes>,
    s2: PhysStore,
    c: CellId,
)
    requires
        phys_crash(s0, e, s2),
        cells_are_atomic(s0, e),
        e.dom().contains(c),
    ensures
        s2[c] == s0[c] || s2[c] == e[c],
{
    if s0[c].len() == 1 {
        atomic_unit_tear_is_trivial(s0[c], e[c], s2[c]);
    }
}

/// **The simulation, for one epoch.**
///
/// Under A1, every physically reachable outcome is `s0 ◁ σ` for some `σ ⊑ e`. That
/// is exactly a point of the abstract crash lattice (§6.2), so the abstract model
/// contains the physical one.
///
/// The witness is the obvious one: `σ` is the epoch restricted to the cells that
/// took their new contents.
pub proof fn refinement_under_a1(s0: PhysStore, e: Delta<Bytes>, s2: PhysStore)
    requires
        phys_crash(s0, e, s2),
        cells_are_atomic(s0, e),
    ensures
        exists|sigma: Delta<Bytes>| sub_delta(sigma, e) && s2 =~= override_(s0, sigma),
{
    let sigma = e.filter_keys(|c: CellId| s2[c] == e[c]);

    assert forall|c: CellId| e.dom().contains(c) implies s2[c] == s0[c] || s2[c] == e[c] by {
        an_atomic_cell_lands_whole(s0, e, s2, c);
    }

    assert(sub_delta(sigma, e));
    assert_maps_equal!(s2, override_(s0, sigma), c => {
        if e.dom().contains(c) && s2[c] != e[c] {
            assert(s2[c] == s0[c]);
        }
    });
    assert(sub_delta(sigma, e) && s2 =~= override_(s0, sigma));
}

/// **The refinement, for a whole program.**
///
/// A crash during epoch `k` of a program, on a real device, produces a store the
/// abstract model already accounts for. Therefore every abstract result transfers —
/// including `theorem::crash_consistency`.
pub proof fn physical_crash_is_an_abstract_crash(
    s0: PhysStore,
    p: crate::crash::Program<Bytes>,
    k: int,
    s2: PhysStore,
)
    requires
        0 <= k < epochs(p).len(),
        phys_crash(prefix_state(s0, p, k), epochs(p)[k], s2),
        cells_are_atomic(prefix_state(s0, p, k), epochs(p)[k]),
    ensures
        is_crash_outcome(s0, p, s2),
{
    let prefix = prefix_state(s0, p, k);
    refinement_under_a1(prefix, epochs(p)[k], s2);
    let sigma = choose|sigma: Delta<Bytes>|
        sub_delta(sigma, epochs(p)[k]) && s2 =~= override_(prefix, sigma);
    crash_outcome_intro(s0, p, k, sigma);
    assert(s2 =~= crash_at(s0, p, k, sigma));
}

/// **Why A1 is an axiom and not a lemma.**
///
/// Without atomicity there is a physically reachable store that no point of the
/// abstract crash lattice describes. A 2-byte cell holding `00 00`, overwritten by
/// `01 01`, can be left holding `00 01` — neither the old contents nor the new ones,
/// and `⊑` has no third option.
///
/// The abstract model is then **not** a conservative over-approximation of the
/// device. It is simply wrong about it, and every theorem above rests on an
/// assumption the hardware has broken.
pub proof fn without_a1_a_physical_crash_escapes_the_model() -> (r: (
    PhysStore,
    Delta<Bytes>,
    PhysStore,
))
    ensures
        phys_crash(r.0, r.1, r.2),
        forall|sigma: Delta<Bytes>| sub_delta(sigma, r.1) ==> r.2 != override_(r.0, sigma),
{
    let old: Bytes = seq![0u8, 0u8];
    let new: Bytes = seq![1u8, 1u8];
    let torn: Bytes = seq![0u8, 1u8];

    let s0: PhysStore = map![0nat => old];
    let e: Delta<Bytes> = map![0nat => new];
    let s2: PhysStore = map![0nat => torn];

    assert(bytewise_tear(old, new, torn)) by {
        assert forall|i: int| 0 <= i < torn.len() implies torn[i] == old[i] || torn[i] == new[i] by {
            assert(i == 0 || i == 1);
        }
    }
    assert(phys_crash(s0, e, s2));

    assert forall|sigma: Delta<Bytes>| sub_delta(sigma, e) implies s2 != override_(s0, sigma) by {
        if sigma.dom().contains(0nat) {
            assert(e.dom().contains(0nat));
            assert(sigma[0nat] == e[0nat]);
            assert(override_(s0, sigma)[0nat] == new);
            // torn and new agree at position 1 and differ at position 0.
            assert(torn[0] != new[0]);
        } else {
            assert(override_(s0, sigma)[0nat] == old);
            // torn and old agree at position 0 and differ at position 1.
            assert(torn[1] != old[1]);
        }
    }
    (s0, e, s2)
}

} // verus!
