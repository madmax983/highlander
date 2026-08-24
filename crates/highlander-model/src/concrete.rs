//! §10.1 acceptance gate 2 — a concrete instantiation.
//!
//! The proof so far checks the model against itself. That is exactly the failure
//! mode this module exists to catch: an algebra can be internally consistent and
//! still describe no machine at all.
//!
//! So here is a machine. Six cells, two slots, two payload cells per slot, one seal
//! each. A commit of generation 8 over a live generation 7. Every point of both
//! crash lattices — all `2² = 4` of the payload epoch, both of the seal epoch — is
//! enumerated by hand and checked to recover to generation 7 or generation 8.
//!
//! ```text
//!   cell:      0        1     2        3        4     5
//!            ┌──────┬─────┬─────┐   ┌──────┬─────┬─────┐
//!   slot A   │ seal │ pay │ pay │   │      │     │     │  slot B
//!            └──────┴─────┴─────┘   └──────┴─────┴─────┘
//!             gen 7   live state       gen 8   being written
//! ```

use vstd::map::{assert_maps_equal, assert_maps_equal_internal};
use vstd::prelude::*;
use vstd::set_lib::{assert_sets_equal, assert_sets_equal_internal};

use crate::algebra::{CellId, Delta, Store};
#[cfg(verus_only)]
use crate::algebra::{override_, unit};
#[cfg(verus_only)]
use crate::commit::{
    commit_establishes_shape, commit_is_crash_consistent, commit_preserves_steady, commit_program,
    distinct_keys, kvs_delta, kvs_keys, seal_val,
};
#[cfg(verus_only)]
use crate::crash::{crash_at, crash_outcome_intro, epochs, is_crash_outcome, sub_delta};
use crate::protocol::{CellVal, Geom, Slot};
#[cfg(verus_only)]
use crate::protocol::{
    clean, clean_implies_steady, footprint, gen_at, is_slot, live, other, recover, slots_wf,
    steady, steady_implies_live,
};
#[cfg(verus_only)]
use crate::sequence::{Step, payloads_wf, run, run_is_crash_consistent};

verus! {

broadcast use vstd::map_lib::group_map_properties;

pub open spec fn slot_a() -> Slot {
    Slot { seal: 0, payload: set![1nat, 2nat] }
}

pub open spec fn slot_b() -> Slot {
    Slot { seal: 3, payload: set![4nat, 5nat] }
}

pub open spec fn geom() -> Geom {
    Geom { a: slot_a(), b: slot_b() }
}

pub open spec fn old_byte() -> CellVal {
    CellVal::Data(seq![0u8])
}

pub open spec fn new_byte() -> CellVal {
    CellVal::Data(seq![1u8])
}

/// A clean store: slot A sealed at generation 7, slot B entirely absent.
pub open spec fn s_initial() -> Store<CellVal> {
    map![
        0nat => CellVal::Seal { generation: 7, crc: 0 },
        1nat => old_byte(),
        2nat => old_byte()
    ]
}

pub open spec fn payload() -> Seq<(CellId, CellVal)> {
    seq![(4nat, new_byte()), (5nat, new_byte())]
}

pub proof fn geometry_is_sane()
    ensures
        slots_wf(geom()),
        is_slot(geom(), slot_b()),
        other(geom(), slot_b()) == slot_a(),
{
    assert(slot_a().payload.disjoint(slot_b().payload));
}

pub proof fn initial_store_is_clean()
    ensures
        clean(geom(), s_initial()),
        live(geom(), s_initial()) == Some(slot_a()),
        gen_at(s_initial(), slot_a().seal) == Some(7nat),
{
    geometry_is_sane();
    let s = s_initial();
    assert(gen_at(s, 0nat) == Some(7nat));
    assert(!s.dom().contains(3nat));
    assert(gen_at(s, 3nat) is None);
    assert(live(geom(), s) == Some(slot_a()));
    assert_sets_equal!(crate::protocol::live_footprint(geom(), s), set![0nat, 1nat, 2nat]);
    assert_maps_equal!(recover(geom(), s), s);
}

pub proof fn payload_is_wellformed()
    ensures
        distinct_keys(payload()),
        kvs_keys(payload()) =~= set![4nat, 5nat],
        kvs_keys(payload()).subset_of(slot_b().payload),
        kvs_delta(payload()) =~= map![4nat => new_byte(), 5nat => new_byte()],
{
    // len 2 needs three unfoldings: 2 -> 1 -> 0.
    reveal_with_fuel(kvs_keys, 3);
    reveal_with_fuel(kvs_delta, 3);
    assert(payload().drop_first().drop_first().len() == 0);
    assert_sets_equal!(kvs_keys(payload()), set![4nat, 5nat]);
    assert_maps_equal!(kvs_delta(payload()), map![4nat => new_byte(), 5nat => new_byte()]);
}

/// **The gate.** Every point of both lattices, checked by hand.
///
/// The payload epoch has `2² = 4` points and every one of them recovers to
/// generation 7 — that is the collapse §7.2 describes, made concrete. The seal
/// epoch has 2 points, one per outcome. Six crash points, two recovered states.
pub proof fn every_lattice_point_recovers_cleanly()
    ensures
        forall|s2: Store<CellVal>|
            is_crash_outcome(s_initial(), commit_program(payload(), slot_b(), 7, 0), s2)
                ==> recover(geom(), s2) =~= recover(geom(), s_initial()) || recover(geom(), s2)
                =~= recover(
                geom(),
                crate::crash::denote(s_initial(), commit_program(payload(), slot_b(), 7, 0)),
            ),
{
    let g = geom();
    let s0 = s_initial();
    let kvs = payload();
    let p = commit_program(kvs, slot_b(), 7, 0);

    geometry_is_sane();
    initial_store_is_clean();
    payload_is_wellformed();

    commit_establishes_shape(g, s0, kvs, slot_b(), 7, 0);

    let e_payload = epochs(p)[0];
    let e_seal = epochs(p)[1];

    // --- the payload epoch: all four points -------------------------------
    assert(e_payload =~= map![4nat => new_byte(), 5nat => new_byte()]);

    let bottom: Delta<CellVal> = unit();
    let only_4: Delta<CellVal> = map![4nat => new_byte()];
    let only_5: Delta<CellVal> = map![5nat => new_byte()];

    assert(sub_delta(bottom, e_payload));
    assert(sub_delta(only_4, e_payload));
    assert(sub_delta(only_5, e_payload));
    assert(sub_delta(e_payload, e_payload));

    crash_outcome_intro(s0, p, 0, bottom);
    crash_outcome_intro(s0, p, 0, only_4);
    crash_outcome_intro(s0, p, 0, only_5);
    crash_outcome_intro(s0, p, 0, e_payload);

    // --- the seal epoch: both points ---------------------------------------
    assert(e_seal =~= map![3nat => seal_val(7, 0)]);
    assert(sub_delta(bottom, e_seal));
    assert(sub_delta(e_seal, e_seal));

    crash_outcome_intro(s0, p, 1, bottom);
    crash_outcome_intro(s0, p, 1, e_seal);

    // --- and the general theorem covers all six ----------------------------
    commit_is_crash_consistent(g, s0, kvs, slot_b(), 7, 0);
}

/// The new checkpoint really is generation 8, and it really is in slot B.
/// Without this, "recovers to one of two states" could be satisfied vacuously by
/// two states that are secretly the same one.
pub proof fn the_two_states_are_distinct()
    ensures
        recover(geom(), crate::crash::denote(s_initial(), commit_program(payload(), slot_b(), 7, 0)))
            != recover(geom(), s_initial()),
{
    let g = geom();
    let s0 = s_initial();
    let kvs = payload();
    let p = commit_program(kvs, slot_b(), 7, 0);

    geometry_is_sane();
    initial_store_is_clean();
    payload_is_wellformed();
    commit_establishes_shape(g, s0, kvs, slot_b(), 7, 0);

    let sN = crate::crash::denote(s0, p);
    crate::theorem::apply_two(s0, epochs(p));
    assert(sN =~= override_(override_(s0, epochs(p)[0]), epochs(p)[1]));

    assert(gen_at(sN, 3nat) == Some(8nat));
    assert(gen_at(sN, 0nat) == Some(7nat));
    assert(live(g, sN) == Some(slot_b()));
    assert(recover(g, sN).dom().contains(3nat));
    assert(!recover(g, s0).dom().contains(3nat));
}


// ---------------------------------------------------------------------------
// Two commits, concretely — the case the single-commit theorem could not express
// ---------------------------------------------------------------------------

/// The payload for the commit that targets slot A.
pub open spec fn payload_a() -> Seq<(CellId, CellVal)> {
    seq![(1nat, new_byte()), (2nat, new_byte())]
}

pub proof fn payload_a_is_wellformed()
    ensures
        distinct_keys(payload_a()),
        kvs_keys(payload_a()).subset_of(slot_a().payload),
{
    reveal_with_fuel(kvs_keys, 3);
    assert(payload_a().drop_first().drop_first().len() == 0);
    assert_sets_equal!(kvs_keys(payload_a()), set![1nat, 2nat]);
}

/// **A second commit, into a slot that still carries an older seal.**
///
/// This is the situation the original `clean` precondition could not describe. After
/// the first commit, slot A still holds its generation-7 seal and its generation-7
/// payload; the store is not clean, and never will be again. Under `steady` the
/// second commit is covered, and recovery still cannot be confused, because
/// generation 7 is strictly below generation 8.
pub proof fn a_second_commit_is_also_safe()
    ensures
        steady(geom(), s_initial(), slot_a(), 7),
{
    let g = geom();
    let s0 = s_initial();

    geometry_is_sane();
    initial_store_is_clean();
    payload_is_wellformed();
    payload_a_is_wellformed();

    clean_implies_steady(g, s0, slot_a(), 7);

    // Commit 1: into slot B, generation 8.
    commit_preserves_steady(g, s0, payload(), slot_b(), 7, 0);
    let s1 = crate::crash::denote(s0, commit_program(payload(), slot_b(), 7, 0));
    assert(steady(g, s1, slot_b(), 8));

    // Slot A is still sealed at generation 7, and its payload is still present, so
    // the store is no longer clean — and never will be again.
    commit_establishes_shape(g, s0, payload(), slot_b(), 7, 0);
    let p1 = commit_program(payload(), slot_b(), 7, 0);
    crate::theorem::apply_two(s0, epochs(p1));
    assert(s1 =~= override_(override_(s0, epochs(p1)[0]), epochs(p1)[1]));
    assert(epochs(p1)[1] =~= map![3nat => seal_val(7, 0)]);
    assert(gen_at(s1, slot_a().seal) == Some(7nat));

    steady_implies_live(g, s1, slot_b(), 8);
    assert(crate::protocol::live_footprint(g, s1) =~= footprint(slot_b()));
    assert(s1.dom().contains(1nat));
    assert(!footprint(slot_b()).contains(1nat));
    assert(!recover(g, s1).dom().contains(1nat));
    assert(!clean(g, s1));

    // Commit 2: into slot A, generation 9 — over the top of the old seal.
    commit_is_crash_consistent(g, s1, payload_a(), slot_a(), 8, 0);
    commit_preserves_steady(g, s1, payload_a(), slot_a(), 8, 0);
    let s2 = crate::crash::denote(s1, commit_program(payload_a(), slot_a(), 8, 0));
    assert(steady(g, s2, slot_a(), 9));
}

/// The same two commits as a `run`, which is the form an unbounded machine takes.
pub proof fn a_two_step_run_is_safe()
    ensures
        run(geom(), s_initial(), slot_a(), 7, two_commits()).1 == slot_a(),
        run(geom(), s_initial(), slot_a(), 7, two_commits()).2 == 9,
{
    let g = geom();
    let s0 = s_initial();
    let cs = two_commits();

    geometry_is_sane();
    initial_store_is_clean();
    payload_is_wellformed();
    payload_a_is_wellformed();
    clean_implies_steady(g, s0, slot_a(), 7);

    reveal_with_fuel(payloads_wf, 3);
    reveal_with_fuel(run, 3);
    assert(cs.drop_first().drop_first().len() == 0);
    assert(payloads_wf(g, slot_a(), cs));

    run_is_crash_consistent(g, s0, slot_a(), 7, cs);
}

/// Slot B first, then slot A. The target alternates; that is ping-pong.
pub open spec fn two_commits() -> Seq<Step> {
    seq![(payload(), 0u64), (payload_a(), 0u64)]
}

} // verus!\n
