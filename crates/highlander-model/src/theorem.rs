//! §7.3 — The crash-consistency theorem.
//!
//! > Crash consistency of the whole machine reduces to two stated hardware
//! > promises, with a probabilistic backstop for when they are broken.
//!
//! # On the statement
//!
//! The design doc writes the result as `|image(recover ∘ Crash(p))| ≤ 2`. What is
//! proven here is the disjunction that cardinality bound is shorthand for: *every*
//! crash outcome recovers either to the old checkpoint or to the new one, and to
//! nothing else. That is the same content in the form every consumer actually
//! wants, and it avoids dragging `Set::len` and finiteness obligations through the
//! whole development.
//!
//! One detail the prose glosses: the new state is `recover(denote(…))`, not
//! `denote(…)`. The store after a successful commit still physically contains the
//! *previous* checkpoint in the other slot — that is what ping-pong means. It is
//! the recovered view that equals the new checkpoint.
//!
//! # Where the two cases come from
//!
//! Exactly the two epochs, and the barrier between them is what keeps them two:
//!
//! * **Crash in the payload epoch** — the seal is absent, so recovery reads only the
//!   live slot. All `2ⁿ` points of that epoch's lattice collapse to a *single*
//!   point, because the payload's footprint is disjoint from the live slot's.
//!   [`seal_absent_recovers_old`] is that collapse.
//! * **Crash in the seal epoch** — A4 makes it one cell and A1 makes that cell
//!   atomic, so its lattice has two points. `crash::singleton_lattice` is that step.

use vstd::map::{assert_maps_equal, assert_maps_equal_internal};
use vstd::prelude::*;
use vstd::set_lib::{assert_sets_equal, assert_sets_equal_internal};

use crate::algebra::{CellId, Delta, Store};
#[cfg(verus_only)]
use crate::algebra::{override_, unit};
#[cfg(verus_only)]
use crate::crash::{
    apply, crash_at, denote, epochs, is_crash_outcome, prefix_state, singleton_lattice, sub_delta,
};
use crate::protocol::{CellVal, Geom, Slot};
#[cfg(verus_only)]
use crate::protocol::{
    clean, footprint, gen_at, is_slot, live, live_footprint, other, recover, slots_wf,
};

verus! {

broadcast use vstd::map_lib::group_map_properties;

// ---------------------------------------------------------------------------
// Unfolding `apply` at the two lengths the protocol uses
// ---------------------------------------------------------------------------

pub proof fn apply_empty<V>(s: Store<V>, es: Seq<Delta<V>>)
    requires
        es.len() == 0,
    ensures
        apply(s, es) =~= s,
{
}

pub proof fn apply_one<V>(s: Store<V>, es: Seq<Delta<V>>)
    requires
        es.len() == 1,
    ensures
        apply(s, es) =~= override_(s, es[0]),
{
    assert(es.drop_first().len() == 0);
    apply_empty(override_(s, es[0]), es.drop_first());
}

pub proof fn apply_two<V>(s: Store<V>, es: Seq<Delta<V>>)
    requires
        es.len() == 2,
    ensures
        apply(s, es) =~= override_(override_(s, es[0]), es[1]),
{
    assert(es.drop_first().len() == 1);
    apply_one(override_(s, es[0]), es.drop_first());
}

// ---------------------------------------------------------------------------
// The shape of a legitimate commit
// ---------------------------------------------------------------------------

/// A commit of generation `n + 1` into `target`, while `other(g, target)` holds the
/// live checkpoint at generation `n`.
///
/// Every clause here is load-bearing; the falsifiability gate in
/// `protocol::commit_program` works by breaking the `epochs(p).len() == 2` clause,
/// which is precisely what the barrier buys.
pub open spec fn commit_shape(
    g: Geom,
    s0: Store<CellVal>,
    p: Seq<crate::crash::Op<CellVal>>,
    target: Slot,
    n: nat,
    crc: u64,
) -> bool {
    &&& slots_wf(g)
    &&& is_slot(g, target)
    &&& clean(g, s0)
    &&& live(g, s0) == Some(other(g, target))
    &&& gen_at(s0, other(g, target).seal) == Some(n)
    // Two epochs — payload, then seal. A2 (the barrier) is what makes this 2 and not 1.
    &&& epochs(p).len() == 2
    // The payload writes land only inside the target slot's own region (§7.5 rule 2).
    &&& epochs(p)[0].dom().subset_of(target.payload)
    // A4: the seal is exactly one cell.
    &&& epochs(p)[1] =~= map![target.seal => CellVal::Seal { generation: (n + 1) as nat, crc }]
}

// ---------------------------------------------------------------------------
// The payload-epoch collapse
// ---------------------------------------------------------------------------

/// **All `2ⁿ` points of the payload epoch's lattice collapse to one.**
///
/// Any set of writes confined to the target slot's payload region leaves the
/// recovered state completely unchanged — regardless of *which* subset landed. The
/// disjointness of the target payload from the live footprint is doing all the
/// work, which is §4.4's condition showing up yet again.
pub proof fn seal_absent_recovers_old(
    g: Geom,
    s0: Store<CellVal>,
    target: Slot,
    n: nat,
    delta: Delta<CellVal>,
)
    requires
        slots_wf(g),
        is_slot(g, target),
        clean(g, s0),
        live(g, s0) == Some(other(g, target)),
        gen_at(s0, other(g, target).seal) == Some(n),
        delta.dom().subset_of(target.payload),
    ensures
        recover(g, override_(s0, delta)) =~= recover(g, s0),
{
    let l = other(g, target);
    let s2 = override_(s0, delta);

    // The payload region touches neither seal, so neither generation moves.
    assert(!delta.dom().contains(l.seal));
    assert(!delta.dom().contains(target.seal));
    assert(gen_at(s2, l.seal) == gen_at(s0, l.seal));
    assert(gen_at(s2, target.seal) == gen_at(s0, target.seal));

    // s0 is clean, so it holds nothing outside the live footprint — in particular
    // the target's seal is absent, which is why recovery cannot be fooled.
    assert(!footprint(l).contains(target.seal));
    assert(gen_at(s0, target.seal) is None);

    assert(live(g, s2) == live(g, s0));
    assert(live_footprint(g, s2) =~= footprint(l));
    assert(live_footprint(g, s0) =~= footprint(l));

    // Nothing that landed is visible through the live slot's footprint.
    assert_maps_equal!(s2.restrict(footprint(l)), s0.restrict(footprint(l)));
}

// ---------------------------------------------------------------------------
// The theorem
// ---------------------------------------------------------------------------

/// One crash point, resolved. Split out so the quantifier in
/// [`crash_consistency`] has something to appeal to.
pub proof fn crash_case(
    g: Geom,
    s0: Store<CellVal>,
    p: Seq<crate::crash::Op<CellVal>>,
    target: Slot,
    n: nat,
    crc: u64,
    k: int,
    sigma: Delta<CellVal>,
)
    requires
        commit_shape(g, s0, p, target, n, crc),
        0 <= k < epochs(p).len(),
        sub_delta(sigma, epochs(p)[k]),
    ensures
        recover(g, crash_at(s0, p, k, sigma)) =~= recover(g, s0) || recover(
            g,
            crash_at(s0, p, k, sigma),
        ) =~= recover(g, denote(s0, p)),
{
    let es = epochs(p);
    let e0 = es[0];
    let e1 = es[1];

    if k == 0 {
        // Crash in the payload epoch: prefix is empty, so the state is s0 ◁ σ.
        assert(es.take(0).len() == 0);
        apply_empty(s0, es.take(0));
        assert(prefix_state(s0, p, 0) =~= s0);
        assert(sigma.dom().subset_of(e0.dom()));
        assert(sigma.dom().subset_of(target.payload));
        seal_absent_recovers_old(g, s0, target, n, sigma);
    } else {
        // Crash in the seal epoch: A4 + A1 give a two-point lattice.
        assert(k == 1);
        assert(es.take(1).len() == 1);
        assert(es.take(1)[0] =~= e0);
        apply_one(s0, es.take(1));
        assert(prefix_state(s0, p, 1) =~= override_(s0, e0));

        singleton_lattice(sigma, e1, target.seal);

        if sigma =~= unit::<CellVal>() {
            // Nothing of the seal landed — indistinguishable from a payload crash
            // in which everything landed.
            assert(crash_at(s0, p, 1, sigma) =~= override_(s0, e0));
            seal_absent_recovers_old(g, s0, target, n, e0);
        } else {
            // The seal landed — this is exactly the completed commit.
            assert(sigma =~= e1);
            apply_two(s0, es);
            assert(crash_at(s0, p, 1, sigma) =~= denote(s0, p));
        }
    }
}

/// **The theorem (§7.3).**
///
/// Every reachable crash outcome recovers to one of exactly two states: the
/// checkpoint at generation `n`, or the checkpoint at generation `n + 1`. Never a
/// blend of the two, never anything else.
///
/// This is the foundational lemma of the whole system. Everything above the
/// checkpoint layer is meaningless if the checkpoint can tear.
pub proof fn crash_consistency(
    g: Geom,
    s0: Store<CellVal>,
    p: Seq<crate::crash::Op<CellVal>>,
    target: Slot,
    n: nat,
    crc: u64,
)
    requires
        commit_shape(g, s0, p, target, n, crc),
    ensures
        forall|s2: Store<CellVal>|
            is_crash_outcome(s0, p, s2) ==> recover(g, s2) =~= recover(g, s0) || recover(g, s2)
                =~= recover(g, denote(s0, p)),
{
    assert forall|s2: Store<CellVal>| is_crash_outcome(s0, p, s2) implies recover(g, s2)
        =~= recover(g, s0) || recover(g, s2) =~= recover(g, denote(s0, p)) by {
        let kw = choose|k: int, sigma: Delta<CellVal>|
            #![trigger crash_at(s0, p, k, sigma)]
            {
                &&& 0 <= k < epochs(p).len()
                &&& sub_delta(sigma, epochs(p)[k])
                &&& s2 =~= crash_at(s0, p, k, sigma)
            };
        crash_case(g, s0, p, target, n, crc, kw.0, kw.1);
    }
}

} // verus!
