//! §7.1 — Building an actual commit program, and discharging the theorem's hypotheses.
//!
//! [`crate::theorem::crash_consistency`] takes the *shape* of a commit as a
//! hypothesis: two epochs, payload then seal. This module supplies a real
//! [`Program`] and proves it has that shape, which is what turns the theorem from a
//! statement about hypothetical programs into a statement about the one the
//! protocol emits.
//!
//! # The falsifiability gate (§7.3)
//!
//! [`barrier_ops`] is the *only* thing the `no-barrier` cargo feature changes: it
//! emits `[Barrier]` normally and the empty sequence under the feature. That single
//! line is the difference between two epochs and one.
//!
//! Under `no-barrier` the payload and the seal merge into a single epoch, whose
//! lattice contains the point *"seal landed, payload didn't"* — a state that
//! recovers to neither `N` nor `N+1`. So [`commit_establishes_shape`] and
//! [`commit_is_crash_consistent`] **must fail to verify** with the feature on. If
//! they still verify, the model is vacuous and nothing built on it means anything.
//!
//! `scripts/gate.sh` checks exactly that, and checks that the failure names
//! `commit_is_crash_consistent` — a negative test that passes because the crate
//! failed to compile is worse than no gate at all.

use vstd::map::{assert_maps_equal, assert_maps_equal_internal};
use vstd::prelude::*;
use vstd::seq_lib::{assert_seqs_equal, assert_seqs_equal_internal};
use vstd::set_lib::{assert_sets_equal, assert_sets_equal_internal};

use crate::algebra::{CellId, Delta, Store};
#[cfg(verus_only)]
use crate::algebra::{disjoint, dunion, override_, unit};
use crate::crash::{Op, Program};
#[cfg(verus_only)]
use crate::crash::{denote, epochs, is_crash_outcome, wf};
use crate::protocol::{CellVal, Geom, Slot};
#[cfg(verus_only)]
use crate::protocol::{
    a_slot_is_sane, clean, distinct_slots_are_disjoint, footprint, gen_at, gen_below, is_live_at,
    is_slot, live, live_footprint, recover, slots_wf, steady, steady_implies_live,
};
#[cfg(verus_only)]
use crate::theorem::{commit_shape, crash_consistency};

verus! {

broadcast use vstd::map_lib::group_map_properties;

// ---------------------------------------------------------------------------
// Payloads as key/value sequences
// ---------------------------------------------------------------------------

/// A payload is an ordered list of writes. Order is irrelevant to the *result*
/// (that is what §4.3 buys us), but a program is a sequence, so something has to
/// impose one.
pub type Payload = Seq<(CellId, CellVal)>;

pub open spec fn write_ops(kvs: Payload) -> Program<CellVal> {
    kvs.map_values(|kv: (CellId, CellVal)| Op::Write(kv.0, kv.1))
}

/// The delta a payload assembles to — built with `•`, never `◁`, which is exactly
/// why [`distinct_keys`] is required everywhere below.
pub open spec fn kvs_delta(kvs: Payload) -> Delta<CellVal>
    decreases kvs.len(),
{
    if kvs.len() == 0 {
        unit()
    } else {
        dunion(map![kvs[0].0 => kvs[0].1], kvs_delta(kvs.drop_first()))
    }
}

pub open spec fn kvs_keys(kvs: Payload) -> Set<CellId>
    decreases kvs.len(),
{
    if kvs.len() == 0 {
        Set::empty()
    } else {
        kvs_keys(kvs.drop_first()).insert(kvs[0].0)
    }
}

/// §4.4's condition, stated where it is actually used: `•` is undefined on
/// overlapping domains, so a payload may not write the same cell twice.
pub open spec fn distinct_keys(kvs: Payload) -> bool {
    forall|i: int, j: int| #![auto] 0 <= i < j < kvs.len() ==> kvs[i].0 != kvs[j].0
}

pub proof fn kvs_keys_contains(kvs: Payload, c: CellId)
    ensures
        kvs_keys(kvs).contains(c) <==> exists|i: int| #![auto] 0 <= i < kvs.len() && kvs[i].0 == c,
    decreases kvs.len(),
{
    if kvs.len() == 0 {
    } else {
        kvs_keys_contains(kvs.drop_first(), c);
        if kvs_keys(kvs).contains(c) {
            if c == kvs[0].0 {
                assert(kvs[0].0 == c);
            } else {
                let i = choose|i: int| #![auto]
                    0 <= i < kvs.drop_first().len() && kvs.drop_first()[i].0 == c;
                assert(kvs[i + 1].0 == c);
            }
        }
        if exists|i: int| #![auto] 0 <= i < kvs.len() && kvs[i].0 == c {
            let i = choose|i: int| #![auto] 0 <= i < kvs.len() && kvs[i].0 == c;
            if i > 0 {
                assert(kvs.drop_first()[i - 1].0 == c);
            }
        }
    }
}

pub proof fn kvs_delta_dom(kvs: Payload)
    ensures
        kvs_delta(kvs).dom() =~= kvs_keys(kvs),
    decreases kvs.len(),
{
    if kvs.len() == 0 {
    } else {
        kvs_delta_dom(kvs.drop_first());
        assert_sets_equal!(kvs_delta(kvs).dom(), kvs_keys(kvs));
    }
}

pub proof fn distinct_head_fresh(kvs: Payload)
    requires
        distinct_keys(kvs),
        kvs.len() > 0,
    ensures
        !kvs_keys(kvs.drop_first()).contains(kvs[0].0),
        distinct_keys(kvs.drop_first()),
{
    kvs_keys_contains(kvs.drop_first(), kvs[0].0);
    if kvs_keys(kvs.drop_first()).contains(kvs[0].0) {
        let i = choose|i: int| #![auto]
            0 <= i < kvs.drop_first().len() && kvs.drop_first()[i].0 == kvs[0].0;
        assert(kvs[i + 1].0 == kvs[0].0);
        assert(0 < i + 1 < kvs.len());
    }
    assert forall|i: int, j: int| #![auto]
        0 <= i < j < kvs.drop_first().len() implies kvs.drop_first()[i].0
        != kvs.drop_first()[j].0 by {
        assert(kvs[i + 1].0 != kvs[j + 1].0);
    }
}

// ---------------------------------------------------------------------------
// Epoch decomposition of a payload prefix
// ---------------------------------------------------------------------------

pub proof fn write_ops_drop_first(kvs: Payload, rest: Program<CellVal>)
    requires
        kvs.len() > 0,
    ensures
        (write_ops(kvs) + rest)[0] == Op::Write(kvs[0].0, kvs[0].1),
        (write_ops(kvs) + rest).drop_first() =~= write_ops(kvs.drop_first()) + rest,
{
    assert_seqs_equal!((write_ops(kvs) + rest).drop_first(), write_ops(kvs.drop_first()) + rest);
}

/// The inductive core: prepending a payload's writes folds its delta into epoch 0
/// of whatever follows, and leaves every later epoch untouched.
pub proof fn epochs_prepend_writes(kvs: Payload, rest: Program<CellVal>)
    requires
        distinct_keys(kvs),
        kvs_keys(kvs).disjoint(epochs(rest)[0].dom()),
    ensures
        epochs(write_ops(kvs) + rest) =~= epochs(rest).update(
            0,
            dunion(kvs_delta(kvs), epochs(rest)[0]),
        ),
    decreases kvs.len(),
{
    crate::crash::epochs_nonempty(rest);
    if kvs.len() == 0 {
        assert_seqs_equal!(write_ops(kvs) + rest, rest);
        assert(kvs_delta(kvs) =~= unit::<CellVal>());
        crate::algebra::dunion_unit_left(epochs(rest)[0]);
        assert_seqs_equal!(
            epochs(rest),
            epochs(rest).update(0, dunion(kvs_delta(kvs), epochs(rest)[0]))
        );
    } else {
        distinct_head_fresh(kvs);
        kvs_keys_contains(kvs, kvs[0].0);
        assert(kvs_keys(kvs.drop_first()).subset_of(kvs_keys(kvs)));
        epochs_prepend_writes(kvs.drop_first(), rest);
        write_ops_drop_first(kvs, rest);

        let tail = epochs(write_ops(kvs.drop_first()) + rest);
        let head = map![kvs[0].0 => kvs[0].1];
        assert(tail[0] =~= dunion(kvs_delta(kvs.drop_first()), epochs(rest)[0]));

        kvs_delta_dom(kvs.drop_first());
        crate::algebra::dunion_dom(kvs_delta(kvs.drop_first()), epochs(rest)[0]);
        crate::algebra::dunion_assoc(head, kvs_delta(kvs.drop_first()), epochs(rest)[0]);

        assert_seqs_equal!(
            epochs(write_ops(kvs) + rest),
            epochs(rest).update(0, dunion(kvs_delta(kvs), epochs(rest)[0]))
        );
    }
}

} // verus!

verus! {

// ---------------------------------------------------------------------------
// §7.1 — The commit program
// ---------------------------------------------------------------------------

pub open spec fn seal_val(n: nat, crc: u64) -> CellVal {
    CellVal::Seal { generation: (n + 1) as nat, crc }
}

/// **The falsifiability gate lives here, and nowhere else.**
///
/// This one function is the entire difference between a correct commit and a
/// broken one. Normally it emits a barrier; under `--features no-barrier` it emits
/// nothing, the payload and seal collapse into a single epoch, and every proof
/// downstream of `commit_shape` must break.
#[cfg(not(feature = "no-barrier"))]
pub open spec fn barrier_ops() -> Program<CellVal> {
    seq![Op::Barrier]
}

#[cfg(feature = "no-barrier")]
pub open spec fn barrier_ops() -> Program<CellVal> {
    Seq::empty()
}

pub open spec fn seal_ops(target: Slot, n: nat, crc: u64) -> Program<CellVal> {
    seq![Op::Write(target.seal, seal_val(n, crc))]
}

pub open spec fn commit_tail(target: Slot, n: nat, crc: u64) -> Program<CellVal> {
    barrier_ops() + seal_ops(target, n, crc)
}

/// Payload writes, then a barrier (A2), then a single-cell seal (A4).
pub open spec fn commit_program(kvs: Payload, target: Slot, n: nat, crc: u64) -> Program<CellVal> {
    write_ops(kvs) + commit_tail(target, n, crc)
}

/// Epoch decomposition of everything after the payload.
///
/// With the barrier this is two epochs — an empty one, then the seal. Without it,
/// one. That difference is the gate.
pub proof fn epochs_commit_tail(target: Slot, n: nat, crc: u64)
    ensures
        epochs(commit_tail(target, n, crc)).len() == 1 + barrier_ops().len(),
        epochs(commit_tail(target, n, crc)).last() =~= map![target.seal => seal_val(n, crc)],
        epochs(commit_tail(target, n, crc))[0].dom().subset_of(
            map![target.seal => seal_val(n, crc)].dom(),
        ),
        // With a barrier the first epoch after the payload is empty. Without one it
        // is the seal itself — which is the whole point of the gate.
        barrier_ops().len() > 0 ==> epochs(commit_tail(target, n, crc))[0] =~= unit::<CellVal>(),
{
    let sv = seal_val(n, crc);
    let sops = seal_ops(target, n, crc);

    // epochs of a lone write: one epoch holding just that write.
    assert(sops.drop_first().len() == 0);
    assert_seqs_equal!(epochs(sops.drop_first()), seq![unit::<CellVal>()]);
    crate::algebra::dunion_unit_right(map![target.seal => sv]);
    assert_seqs_equal!(epochs(sops), seq![map![target.seal => sv]]);

    let tail = commit_tail(target, n, crc);
    if barrier_ops().len() == 0 {
        assert_seqs_equal!(tail, sops);
    } else {
        assert(tail[0] == Op::Barrier::<CellVal>);
        assert_seqs_equal!(tail.drop_first(), sops);
        assert_seqs_equal!(epochs(tail), seq![unit::<CellVal>()].add(epochs(sops)));
    }
}

/// The payload's keys never collide with the seal cell, so the prepend lemma
/// applies in **both** configurations. The gate must fail on the *shape*, not on an
/// undischargeable side-condition — otherwise it would be testing the wrong thing.
pub proof fn payload_avoids_seal(g: Geom, kvs: Payload, target: Slot)
    requires
        slots_wf(g),
        is_slot(g, target),
        kvs_keys(kvs).subset_of(target.payload),
    ensures
        !kvs_keys(kvs).contains(target.seal),
{
    a_slot_is_sane(g, target);
}

/// The commit program really does have the shape [`crash_consistency`] assumes.
///
/// **Must fail under `--features no-barrier`**, because `epochs(p).len() == 2`
/// becomes `1`.
pub proof fn commit_establishes_shape(
    g: Geom,
    s0: Store<CellVal>,
    kvs: Payload,
    target: Slot,
    live_slot: Slot,
    n: nat,
    crc: u64,
)
    requires
        is_slot(g, target),
        live_slot != target,
        steady(g, s0, live_slot, n),
        distinct_keys(kvs),
        kvs_keys(kvs).subset_of(target.payload),
    ensures
        commit_shape(g, s0, commit_program(kvs, target, n, crc), target, live_slot, n, crc),
        // Pin the payload epoch exactly, so callers can enumerate its lattice.
        epochs(commit_program(kvs, target, n, crc))[0] =~= kvs_delta(kvs),
{
    let sv = seal_val(n, crc);
    let tail = commit_tail(target, n, crc);
    let p = commit_program(kvs, target, n, crc);

    epochs_commit_tail(target, n, crc);
    payload_avoids_seal(g, kvs, target);
    assert(kvs_keys(kvs).disjoint(epochs(tail)[0].dom()));

    epochs_prepend_writes(kvs, tail);
    kvs_delta_dom(kvs);
    crate::algebra::dunion_unit_right(kvs_delta(kvs));
    crate::crash::epochs_nonempty(tail);

    assert(epochs(p).len() == epochs(tail).len());
    assert(epochs(p)[0] =~= dunion(kvs_delta(kvs), epochs(tail)[0]));
    assert(epochs(p)[1] =~= epochs(tail)[1]);
}

/// **The end-to-end result.**
///
/// Given a clean store whose live checkpoint is generation `n`, committing a
/// payload into the other slot leaves every possible crash outcome recovering to
/// exactly one of two states: generation `n`, or generation `n + 1`.
///
/// This is the statement `scripts/gate.sh` requires to break when the barrier is
/// removed.
pub proof fn commit_is_crash_consistent(
    g: Geom,
    s0: Store<CellVal>,
    kvs: Payload,
    target: Slot,
    live_slot: Slot,
    n: nat,
    crc: u64,
)
    requires
        is_slot(g, target),
        live_slot != target,
        steady(g, s0, live_slot, n),
        distinct_keys(kvs),
        kvs_keys(kvs).subset_of(target.payload),
    ensures
        forall|s2: Store<CellVal>|
            is_crash_outcome(s0, commit_program(kvs, target, n, crc), s2) ==> recover(g, s2)
                =~= recover(g, s0) || recover(g, s2) =~= recover(
                g,
                denote(s0, commit_program(kvs, target, n, crc)),
            ),
{
    commit_establishes_shape(g, s0, kvs, target, live_slot, n, crc);
    crash_consistency(g, s0, commit_program(kvs, target, n, crc), target, live_slot, n, crc);
}


// ---------------------------------------------------------------------------
// The inductive step: a commit re-establishes its own precondition
// ---------------------------------------------------------------------------

/// **A commit leaves the machine ready for the next commit.**
///
/// This is the step that turns "one commit is safe" into "a machine is safe".
/// `commit_is_crash_consistent` needs a steady store; this lemma shows a successful
/// commit produces one, with the slots exchanged and the generation raised.
///
/// Note the conclusion is about `denote`, the raw store — not about `recover`. The
/// machine does not run recovery after a successful commit; it carries on with both
/// slots populated, which is exactly why `clean` could never have been the
/// invariant here.
pub proof fn commit_preserves_steady(
    g: Geom,
    s0: Store<CellVal>,
    kvs: Payload,
    target: Slot,
    live_slot: Slot,
    n: nat,
    crc: u64,
)
    requires
        is_slot(g, target),
        live_slot != target,
        steady(g, s0, live_slot, n),
        distinct_keys(kvs),
        kvs_keys(kvs).subset_of(target.payload),
    ensures
        steady(g, denote(s0, commit_program(kvs, target, n, crc)), target, (n + 1) as nat),
{
    let p = commit_program(kvs, target, n, crc);
    commit_establishes_shape(g, s0, kvs, target, live_slot, n, crc);
    crate::theorem::apply_two(s0, epochs(p));

    let s_new = denote(s0, p);
    assert(s_new =~= override_(override_(s0, epochs(p)[0]), epochs(p)[1]));

    // The seal write puts generation n + 1 in the target.
    assert(epochs(p)[1].dom() =~= set![target.seal]);
    assert(gen_at(s_new, target.seal) == Some((n + 1) as nat));

    // No other slot's seal is in either epoch, so each still reads whatever it read
    // before — and each of those was already below n, hence below n + 1. A3 is what
    // makes that comparison meaningful.
    assert forall|o: Slot| is_slot(g, o) && o != target implies gen_below(
        gen_at(s_new, o.seal),
        (n + 1) as nat,
    ) by {
        distinct_slots_are_disjoint(g, target, o);
        assert(!epochs(p)[0].dom().contains(o.seal));
        assert(!epochs(p)[1].dom().contains(o.seal));
        assert(gen_at(s_new, o.seal) == gen_at(s0, o.seal));
        if o == live_slot {
            assert(gen_at(s0, o.seal) == Some(n));
        }
    }
}

// ---------------------------------------------------------------------------
// Durability: the committed payload survives
// ---------------------------------------------------------------------------

/// **A commit stores what it was given.**
///
/// Crash consistency is a *safety* property: it says a crash never exposes a torn
/// state. On its own that is satisfied for free by a system which exposes nothing —
/// a `recover` returning the empty store makes both sides of `crash_consistency`'s
/// disjunction equal, and every lemma about crashes still passes.
///
/// This lemma is the other half. After a successful commit, each cell the payload
/// wrote is present in the recovered store holding the value that was written, and
/// the seal reads the new generation. Together with `theorem::crash_consistency` it
/// says the checkpoint neither tears nor forgets.
///
/// `scripts/gate.sh` keeps it honest: under `--features degenerate-recover`,
/// `recover` keeps the seal and discards every payload cell, and this lemma must
/// then fail to verify.
pub proof fn commit_is_durable(
    g: Geom,
    s0: Store<CellVal>,
    kvs: Payload,
    target: Slot,
    live_slot: Slot,
    n: nat,
    crc: u64,
)
    requires
        is_slot(g, target),
        live_slot != target,
        steady(g, s0, live_slot, n),
        distinct_keys(kvs),
        kvs_keys(kvs).subset_of(target.payload),
    ensures
        ({
            let r = recover(g, denote(s0, commit_program(kvs, target, n, crc)));
            // every committed cell survives, holding the value that was committed
            &&& forall|c: CellId| #[trigger]
                kvs_keys(kvs).contains(c) ==> r.dom().contains(c) && r[c] == kvs_delta(kvs)[c]
            // the checkpoint identifies itself as the new generation
            &&& gen_at(r, target.seal) == Some((n + 1) as nat)
            // and holds nothing beyond the slot it was written to
            &&& r.dom().subset_of(footprint(target))
        }),
{
    let p = commit_program(kvs, target, n, crc);
    let s_new = denote(s0, p);

    commit_establishes_shape(g, s0, kvs, target, live_slot, n, crc);
    commit_preserves_steady(g, s0, kvs, target, live_slot, n, crc);
    steady_implies_live(g, s_new, target, (n + 1) as nat);
    crate::theorem::apply_two(s0, epochs(p));
    kvs_delta_dom(kvs);

    assert(s_new =~= override_(override_(s0, epochs(p)[0]), epochs(p)[1]));
    assert(epochs(p)[0] =~= kvs_delta(kvs));
    assert(live_footprint(g, s_new) =~= footprint(target));

    assert forall|c: CellId| kvs_keys(kvs).contains(c) implies {
        &&& recover(g, s_new).dom().contains(c)
        &&& recover(g, s_new)[c] == kvs_delta(kvs)[c]
    } by {
        assert(target.payload.contains(c));
        assert(footprint(target).contains(c));
        assert(c != target.seal);
        assert(epochs(p)[0].dom().contains(c));
    }
}

// ---------------------------------------------------------------------------
// §6.1 well-formedness of the emitted program
// ---------------------------------------------------------------------------

/// The tail is well formed: a barrier constrains nothing, and a lone seal write
/// joins an empty epoch.
pub proof fn wf_commit_tail(target: Slot, n: nat, crc: u64)
    ensures
        wf(commit_tail(target, n, crc)),
{
    let sops = seal_ops(target, n, crc);
    assert(sops.drop_first().len() == 0);
    assert(wf(sops.drop_first()));
    assert_seqs_equal!(epochs(sops.drop_first()), seq![unit::<CellVal>()]);
    assert(!epochs(sops.drop_first())[0].dom().contains(target.seal));
    assert(sops[0] == Op::Write(target.seal, seal_val(n, crc)));
    assert(wf(sops));

    let tail = commit_tail(target, n, crc);
    if barrier_ops().len() == 0 {
        assert_seqs_equal!(tail, sops);
    } else {
        assert(tail[0] == Op::Barrier::<CellVal>);
        assert_seqs_equal!(tail.drop_first(), sops);
    }
}

/// Prepending a payload's writes keeps a program well formed, provided the payload
/// writes distinct cells and none of them already appears in the epoch it joins.
///
/// This is §4.4's condition doing its stated job: `wf` is the definedness
/// side-condition of `•`, and here it is discharged rather than assumed.
pub proof fn wf_prepend_writes(kvs: Payload, rest: Program<CellVal>)
    requires
        distinct_keys(kvs),
        wf(rest),
        kvs_keys(kvs).disjoint(epochs(rest)[0].dom()),
    ensures
        wf(write_ops(kvs) + rest),
    decreases kvs.len(),
{
    crate::crash::epochs_nonempty(rest);
    if kvs.len() == 0 {
        assert_seqs_equal!(write_ops(kvs) + rest, rest);
    } else {
        distinct_head_fresh(kvs);
        kvs_keys_contains(kvs, kvs[0].0);
        assert(kvs_keys(kvs.drop_first()).subset_of(kvs_keys(kvs)));

        wf_prepend_writes(kvs.drop_first(), rest);
        write_ops_drop_first(kvs, rest);

        // The head cell is in neither half of the epoch it would join: not in the
        // rest of the payload (distinct keys), and not in what follows (disjoint).
        epochs_prepend_writes(kvs.drop_first(), rest);
        kvs_delta_dom(kvs.drop_first());
        crate::algebra::dunion_dom(kvs_delta(kvs.drop_first()), epochs(rest)[0]);
        assert(!epochs(write_ops(kvs.drop_first()) + rest)[0].dom().contains(kvs[0].0));
    }
}

/// **The program the protocol emits is well formed (§6.1).**
///
/// Without this, `epochs` would still produce a value for an ill-formed program —
/// `dunion` is total, so two writes to one cell would silently collapse — and every
/// downstream result would be about a denotation that means nothing. §4.4 claims
/// this condition carries the algebra's weight; this lemma is where that claim is
/// discharged for the commit path.
pub proof fn commit_program_is_wf(g: Geom, kvs: Payload, target: Slot, n: nat, crc: u64)
    requires
        slots_wf(g),
        is_slot(g, target),
        distinct_keys(kvs),
        kvs_keys(kvs).subset_of(target.payload),
    ensures
        wf(commit_program(kvs, target, n, crc)),
{
    let tail = commit_tail(target, n, crc);
    wf_commit_tail(target, n, crc);
    epochs_commit_tail(target, n, crc);
    payload_avoids_seal(g, kvs, target);
    assert(kvs_keys(kvs).disjoint(epochs(tail)[0].dom()));
    wf_prepend_writes(kvs, tail);
}

// ---------------------------------------------------------------------------
// What N slots buy: a rollback window
// ---------------------------------------------------------------------------

/// **A commit destroys exactly one checkpoint — the one in the slot it targets.**
///
/// Every other slot comes through untouched: its seal, and every cell of its payload
/// region. Nothing else in the protocol reaches outside the target.
///
/// With 2 slots this says the only other checkpoint dies on the next commit, so a
/// machine that checkpoints its own corruption has exactly one commit in which to
/// notice. With `N` slots it keeps `N - 1` older checkpoints, and the window to
/// notice is `N - 1` commits.
///
/// Note what `steady` does *not* say: it says the store is **consistent**, and
/// consistency says nothing about whether the contents are good. That is why a
/// rollback window is worth having.
pub proof fn a_commit_destroys_only_its_target(
    g: Geom,
    s0: Store<CellVal>,
    kvs: Payload,
    target: Slot,
    live_slot: Slot,
    n: nat,
    crc: u64,
    o: Slot,
)
    requires
        is_slot(g, target),
        live_slot != target,
        steady(g, s0, live_slot, n),
        distinct_keys(kvs),
        kvs_keys(kvs).subset_of(target.payload),
        is_slot(g, o),
        o != target,
    ensures
        denote(s0, commit_program(kvs, target, n, crc)).restrict(footprint(o)) =~= s0.restrict(
            footprint(o),
        ),
{
    let p = commit_program(kvs, target, n, crc);
    let s_new = denote(s0, p);

    commit_establishes_shape(g, s0, kvs, target, live_slot, n, crc);
    crate::theorem::apply_two(s0, epochs(p));
    distinct_slots_are_disjoint(g, target, o);
    a_slot_is_sane(g, target);

    assert(s_new =~= override_(override_(s0, epochs(p)[0]), epochs(p)[1]));
    assert_maps_equal!(s_new.restrict(footprint(o)), s0.restrict(footprint(o)), c => {
        if footprint(o).contains(c) {
            assert(!target.payload.contains(c));
            assert(c != target.seal);
            assert(!epochs(p)[0].dom().contains(c));
            assert(!epochs(p)[1].dom().contains(c));
        }
    });
}

/// An older checkpoint stays readable across a commit that does not target it.
///
/// This is the rollback guarantee in the form a recovery would use: the seal is
/// still there, still naming the same generation, so the slot can still be selected
/// and restored.
pub proof fn an_older_checkpoint_survives_a_commit(
    g: Geom,
    s0: Store<CellVal>,
    kvs: Payload,
    target: Slot,
    live_slot: Slot,
    n: nat,
    crc: u64,
    o: Slot,
)
    requires
        is_slot(g, target),
        live_slot != target,
        steady(g, s0, live_slot, n),
        distinct_keys(kvs),
        kvs_keys(kvs).subset_of(target.payload),
        is_slot(g, o),
        o != target,
    ensures
        gen_at(denote(s0, commit_program(kvs, target, n, crc)), o.seal) == gen_at(s0, o.seal),
{
    let p = commit_program(kvs, target, n, crc);
    let s_new = denote(s0, p);

    commit_establishes_shape(g, s0, kvs, target, live_slot, n, crc);
    crate::theorem::apply_two(s0, epochs(p));
    distinct_slots_are_disjoint(g, target, o);

    assert(s_new =~= override_(override_(s0, epochs(p)[0]), epochs(p)[1]));
    assert(!target.payload.contains(o.seal));
    assert(o.seal != target.seal);
    assert(!epochs(p)[0].dom().contains(o.seal));
    assert(!epochs(p)[1].dom().contains(o.seal));
}

} // verus!
