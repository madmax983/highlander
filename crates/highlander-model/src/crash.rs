//! §6 — The crash model: programs, epochs, and the crash lattice.
//!
//! A commit is a *program*; a crash is a *landing schedule*.
//!
//! # Why arbitrary subsets
//!
//! [`crash_outcomes`] quantifies over every subset of an epoch's writes, not over
//! prefixes. Real devices reorder freely between barriers, so assuming in-order
//! landing would prove something true of a machine nobody owns. The arbitrary
//! subset is not a nuisance quantifier — it is the whole reason the theorem means
//! anything.
//!
//! # Epoch assembly
//!
//! Writes inside one epoch are assembled with `•` ([`algebra::dunion`]), never with
//! `◁`. That is only legitimate when no two writes in an epoch touch the same cell,
//! which is exactly `•`'s definedness side-condition — and exactly what [`wf`]
//! requires. §4.4 of the design doc calls this out as the first of three
//! appearances of the same condition; this module is that first appearance.

use vstd::map::{assert_maps_equal, assert_maps_equal_internal};
use vstd::prelude::*;
use vstd::set_lib::{assert_sets_equal, assert_sets_equal_internal};

use crate::algebra::{CellId, Delta, Store};
#[cfg(verus_only)]
use crate::algebra::{disjoint, dunion, override_, unit};

verus! {

broadcast use vstd::map_lib::group_map_properties;

/// A single storage operation (§6.1).
pub enum Op<V> {
    Write(CellId, V),
    Barrier,
}

/// A commit is a program.
pub type Program<V> = Seq<Op<V>>;

// ---------------------------------------------------------------------------
// Epoch decomposition
// ---------------------------------------------------------------------------

/// Split a program into epochs, assembling each epoch's writes with `•`.
///
/// The result always has length `(number of barriers) + 1`; see [`epochs_nonempty`].
/// Recursion is front-to-back, so `Op::Barrier` at the head opens a fresh empty
/// epoch ahead of everything that follows, and `Op::Write` at the head joins the
/// epoch its successors already formed.
pub open spec fn epochs<V>(p: Program<V>) -> Seq<Delta<V>>
    decreases p.len(),
{
    if p.len() == 0 {
        seq![unit::<V>()]
    } else {
        let rest = epochs(p.drop_first());
        match p[0] {
            Op::Barrier => seq![unit::<V>()].add(rest),
            Op::Write(c, v) => rest.update(0, dunion(map![c => v], rest[0])),
        }
    }
}

/// Well-formedness (§4.4, §6.1): no two writes within one epoch target the same cell.
///
/// This is **not** a hygiene rule. It is the definedness side-condition of `•`, and
/// it is what licenses modelling within-epoch landing as unordered.
pub open spec fn wf<V>(p: Program<V>) -> bool
    decreases p.len(),
{
    if p.len() == 0 {
        true
    } else {
        match p[0] {
            Op::Barrier => wf(p.drop_first()),
            Op::Write(c, _) => wf(p.drop_first()) && !epochs(p.drop_first())[0].dom().contains(c),
        }
    }
}

pub proof fn epochs_nonempty<V>(p: Program<V>)
    ensures
        epochs(p).len() >= 1,
    decreases p.len(),
{
    if p.len() == 0 {
    } else {
        epochs_nonempty(p.drop_first());
    }
}

// ---------------------------------------------------------------------------
// Denotation
// ---------------------------------------------------------------------------

/// Sequence a list of epochs onto a store with `◁` (§6.1: `p = e₁ ◁ e₂ ◁ … ◁ eₙ`).
pub open spec fn apply<V>(s: Store<V>, es: Seq<Delta<V>>) -> Store<V>
    decreases es.len(),
{
    if es.len() == 0 {
        s
    } else {
        apply(override_(s, es[0]), es.drop_first())
    }
}

/// The store a program produces when nothing goes wrong.
pub open spec fn denote<V>(s0: Store<V>, p: Program<V>) -> Store<V> {
    apply(s0, epochs(p))
}

// ---------------------------------------------------------------------------
// §6.2 — The crash lattice
// ---------------------------------------------------------------------------

/// `σ ⊑ e` — σ is a restriction of e to a subset of its domain.
///
/// vstd's `submap_of` is literally this relation, so we take it rather than
/// re-deriving it.
pub open spec fn sub_delta<V>(sigma: Delta<V>, e: Delta<V>) -> bool {
    sigma.submap_of(e)
}

/// Half of the lattice isomorphism: every sub-delta *is* a restriction.
pub proof fn sub_delta_is_restriction<V>(sigma: Delta<V>, e: Delta<V>)
    requires
        sub_delta(sigma, e),
    ensures
        sigma =~= e.restrict(sigma.dom()),
{
    assert_maps_equal!(sigma, e.restrict(sigma.dom()));
}

/// The other half: every restriction to a sub-domain is a sub-delta, and the
/// round trip recovers the domain you started from.
///
/// Together with [`sub_delta_is_restriction`] this is the honest content of
/// "the sub-deltas of `e` are isomorphic to `𝒫(dom e)`". We prove the bijection
/// rather than the cardinality `2^|dom e|`: counting buys nothing downstream and
/// drags finiteness obligations into every lemma.
pub proof fn restriction_is_sub_delta<V>(e: Delta<V>, d: Set<CellId>)
    requires
        d.subset_of(e.dom()),
    ensures
        sub_delta(e.restrict(d), e),
        e.restrict(d).dom() =~= d,
{
    assert_sets_equal!(e.restrict(d).dom(), d);
}

/// Bottom and top of the lattice.
pub proof fn sub_delta_bottom<V>(e: Delta<V>)
    ensures
        sub_delta(unit::<V>(), e),
{
}

pub proof fn sub_delta_top<V>(e: Delta<V>)
    ensures
        sub_delta(e, e),
{
}

/// **The load-bearing lemma for §7.2.**
///
/// A single-cell epoch has a lattice with exactly two points, `⊥` and `⊤`. That is
/// the entire correctness argument for ping-pong: A1 is precisely the claim that
/// the seal epoch's lattice is 2 and not `2^bytes`, and A4 is what makes the seal
/// epoch single-celled in the first place.
pub proof fn singleton_lattice<V>(sigma: Delta<V>, e: Delta<V>, c: CellId)
    requires
        e.dom() =~= set![c],
        sub_delta(sigma, e),
    ensures
        sigma =~= unit::<V>() || sigma =~= e,
{
    if sigma.dom().contains(c) {
        assert_maps_equal!(sigma, e, k => {
            if sigma.dom().contains(k) {
                assert(e.dom().contains(k));
            }
        });
    } else {
        // sigma.dom() is a subset of {c} that excludes c, hence empty.
        assert_maps_equal!(sigma, unit::<V>(), k => {
            if sigma.dom().contains(k) {
                assert(e.dom().contains(k));
                assert(k == c);
            }
        });
    }
}

// ---------------------------------------------------------------------------
// Crash outcomes
// ---------------------------------------------------------------------------

/// The store after epochs `0..k` have fully landed.
pub open spec fn prefix_state<V>(s0: Store<V>, p: Program<V>, k: int) -> Store<V> {
    apply(s0, epochs(p).take(k))
}

/// The store resulting from a crash during epoch `k` in which exactly `sigma` landed.
pub open spec fn crash_at<V>(s0: Store<V>, p: Program<V>, k: int, sigma: Delta<V>) -> Store<V> {
    override_(prefix_state(s0, p, k), sigma)
}

/// `Crash_k(p) = { e₁ ◁ … ◁ e_{k-1} ◁ σ | σ ⊑ e_k }`, unioned over every epoch `k`.
///
/// Stated as a **predicate**, not a `Set`. vstd's `Set` is finite-only in this
/// release (`Set::new` returns `Option`), and while the crash lattice really is
/// finite, proving it so at every use site buys nothing: every consumer wants
/// "for all crash outcomes …", which is what this gives directly.
///
/// Taking `σ = e_k` at the last epoch yields the uninterrupted run, so the complete
/// execution is itself a crash outcome and needs no separate case.
pub open spec fn is_crash_outcome<V>(s0: Store<V>, p: Program<V>, s2: Store<V>) -> bool {
    exists|k: int, sigma: Delta<V>|
        {
            &&& 0 <= k < epochs(p).len()
            &&& sub_delta(sigma, epochs(p)[k])
            &&& s2 =~= #[trigger] crash_at(s0, p, k, sigma)
        }
}

/// Witness introduction: any `(k, σ)` with `σ ⊑ e_k` really is reachable by a crash.
pub proof fn crash_outcome_intro<V>(s0: Store<V>, p: Program<V>, k: int, sigma: Delta<V>)
    requires
        0 <= k < epochs(p).len(),
        sub_delta(sigma, epochs(p)[k]),
    ensures
        is_crash_outcome(s0, p, crash_at(s0, p, k, sigma)),
{
    assert(crash_at(s0, p, k, sigma) =~= crash_at(s0, p, k, sigma));
}

} // verus!
