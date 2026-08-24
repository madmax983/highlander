//! §7 — The commit protocol: ping-pong slots, seals, and recovery.
//!
//! This is where `V` becomes concrete. The algebra (§4) and the crash model (§6)
//! never look inside a cell; `recover` has to, because it must read a generation
//! number out of a seal.
//!
//! # The CRC is deliberately inert
//!
//! [`CellVal::Seal`] carries a `crc`, and **no specification or proof in this crate
//! reads it**. That is not an oversight (§5.1): under A1 + A2 alone, ping-pong is
//! already correct with no checksum, because if the new seal is present then its
//! payload necessarily completed. The CRC exists as defence-in-depth for when A1 or
//! A2 turn out to be false, and its guarantee is *probabilistic* — a torn cell can
//! accidentally validate.
//!
//! If you ever find yourself strengthening a proof by appealing to `crc`, stop. You
//! would be silently converting a proven result into a probabilistic one.
//!
//! # Recovery is state selection, not mutation
//!
//! [`recover`] is a *projection* of the store onto the live checkpoint's footprint.
//! It never writes. That is the formal content of §7.5's non-negotiable rule: power
//! can fail *during* recovery, and there is nothing underneath this layer to catch a
//! recovery that destroyed the only valid checkpoint before deciding.

use vstd::map::{assert_maps_equal, assert_maps_equal_internal};
use vstd::prelude::*;
use vstd::set_lib::{assert_sets_equal, assert_sets_equal_internal};

use crate::algebra::{CellId, Delta, Store};
#[cfg(verus_only)]
use crate::algebra::{disjoint, dunion, override_, unit};
use crate::crash::{Op, Program};
#[cfg(verus_only)]
use crate::crash::{apply, denote, epochs, sub_delta, wf};

verus! {

broadcast use vstd::map_lib::group_map_properties;

/// The concrete cell value. `Data` is opaque bytes; `Seal` is the one cell whose
/// contents recovery interprets.
pub enum CellVal {
    Data(Seq<u8>),
    /// `crc` is carried but never read by any proof — see the module docs.
    Seal { generation: nat, crc: u64 },
}

/// One checkpoint slot: a payload region plus the single cell that seals it.
///
/// A4 lives here: the seal is *one* cell. If it spanned cells, A1 would buy nothing
/// and §7.2's two-point argument would collapse.
pub struct Slot {
    pub seal: CellId,
    pub payload: Set<CellId>,
}

/// The two slots. Ping-pong, not one-slot-with-extra-steps.
pub struct Geom {
    pub a: Slot,
    pub b: Slot,
}

/// The slots must genuinely not overlap. This is §7.5's rule 2 in geometric form —
/// the third appearance of `•`'s definedness condition (§4.4).
pub open spec fn slots_wf(g: Geom) -> bool {
    &&& g.a.seal != g.b.seal
    &&& !g.a.payload.contains(g.a.seal)
    &&& !g.b.payload.contains(g.b.seal)
    &&& !g.a.payload.contains(g.b.seal)
    &&& !g.b.payload.contains(g.a.seal)
    &&& g.a.payload.disjoint(g.b.payload)
}

pub open spec fn is_slot(g: Geom, sl: Slot) -> bool {
    sl == g.a || sl == g.b
}

/// The slot that is not `sl`.
pub open spec fn other(g: Geom, sl: Slot) -> Slot {
    if sl == g.a {
        g.b
    } else {
        g.a
    }
}

/// Everything a slot owns: its payload region plus its seal.
pub open spec fn footprint(sl: Slot) -> Set<CellId> {
    sl.payload.insert(sl.seal)
}

// ---------------------------------------------------------------------------
// Reading seals
// ---------------------------------------------------------------------------

/// The generation recorded at cell `c`, or `None` if the cell is absent or holds
/// something that is not a seal.
///
/// Note what is *not* here: no CRC check. See the module docs.
pub open spec fn gen_at(s: Store<CellVal>, c: CellId) -> Option<nat> {
    if s.dom().contains(c) {
        match s[c] {
            CellVal::Seal { generation, crc: _ } => Some(generation),
            CellVal::Data(_) => None,
        }
    } else {
        None
    }
}

/// Which slot holds the live checkpoint: the one with the greater generation,
/// where absent ranks below present. `None` means neither slot is sealed — an
/// unformatted store.
pub open spec fn live(g: Geom, s: Store<CellVal>) -> Option<Slot> {
    match (gen_at(s, g.a.seal), gen_at(s, g.b.seal)) {
        (None, None) => None,
        (Some(_), None) => Some(g.a),
        (None, Some(_)) => Some(g.b),
        (Some(x), Some(y)) => if x >= y {
            Some(g.a)
        } else {
            Some(g.b)
        },
    }
}

pub open spec fn live_footprint(g: Geom, s: Store<CellVal>) -> Set<CellId> {
    match live(g, s) {
        None => Set::empty(),
        Some(sl) => footprint(sl),
    }
}

/// §7.5 — recovery as a projection onto the live checkpoint. Read-only by
/// construction: the result is a restriction of the input, never an update of it.
#[cfg(not(feature = "degenerate-recover"))]
pub open spec fn recover(g: Geom, s: Store<CellVal>) -> Store<CellVal> {
    s.restrict(live_footprint(g, s))
}

/// **The second falsifiability gate (`--features degenerate-recover`).**
///
/// This version keeps the live seal and discards every payload cell. It is a
/// checkpoint system that forgets all of your data.
///
/// It satisfies `crash_consistency`, `run_is_crash_consistent`, `recover_idempotent`,
/// `recover_lands_clean`, `live_stable` and `seal_absent_recovers_old` — because
/// crash consistency is a *safety* property, and a store that holds nothing can
/// never tear. Only `commit::commit_is_durable` rejects it.
///
/// If verification passes with this feature on, durability is not being proven.
#[cfg(feature = "degenerate-recover")]
pub open spec fn recover(g: Geom, s: Store<CellVal>) -> Store<CellVal> {
    s.restrict(
        match live(g, s) {
            None => Set::empty(),
            Some(sl) => set![sl.seal],
        },
    )
}

/// The fixed points of [`recover`].
pub open spec fn clean(g: Geom, s: Store<CellVal>) -> bool {
    recover(g, s) =~= s
}

// ---------------------------------------------------------------------------
// The steady state of a running machine
// ---------------------------------------------------------------------------

/// `x < n`, where an absent generation ranks below every present one.
pub open spec fn gen_below(x: Option<nat>, n: nat) -> bool {
    match x {
        None => true,
        Some(m) => m < n,
    }
}

/// **The invariant a running machine maintains.**
///
/// `clean` describes a *pristine* store — one holding nothing outside the live
/// slot's footprint. That is true of a freshly formatted device and false of every
/// store thereafter, because a successful commit deliberately leaves the previous
/// checkpoint in the other slot. A machine that only ever satisfied `clean` could
/// commit exactly once.
///
/// `steady` is the weaker property that survives commits: the live slot carries
/// generation `n`, and the other slot carries something strictly older, or nothing
/// at all. **This is where A3 starts doing work.** Without "the generation counter
/// never wraps", `gen_below` could be satisfied by a wrapped counter and recovery
/// would select the stale slot.
///
/// Note what is *not* required: that the payload covers the whole slot. A commit may
/// write a subset of its target's payload region, leaving older cells in place. The
/// recovered checkpoint then mixes generations — which is correct for the question
/// this crate answers (can a checkpoint tear?) and is precisely what rung 2's
/// incremental checkpoints will depend on.
pub open spec fn steady(g: Geom, s: Store<CellVal>, l: Slot, n: nat) -> bool {
    &&& slots_wf(g)
    &&& is_slot(g, l)
    &&& gen_at(s, l.seal) == Some(n)
    &&& gen_below(gen_at(s, other(g, l).seal), n)
}

/// There are two slots, and they are different slots.
pub proof fn other_involution(g: Geom, sl: Slot)
    requires
        slots_wf(g),
        is_slot(g, sl),
    ensures
        is_slot(g, other(g, sl)),
        other(g, other(g, sl)) == sl,
        other(g, sl) != sl,
{
    assert(g.a != g.b);
}

/// A steady store recovers to the slot the invariant names.
pub proof fn steady_implies_live(g: Geom, s: Store<CellVal>, l: Slot, n: nat)
    requires
        steady(g, s, l, n),
    ensures
        live(g, s) == Some(l),
{
    other_involution(g, l);
}

/// The old precondition implies the new one, so `steady` is strictly more general.
/// A freshly formatted store is steady; so is every store a commit produces.
pub proof fn clean_implies_steady(g: Geom, s: Store<CellVal>, l: Slot, n: nat)
    requires
        slots_wf(g),
        is_slot(g, l),
        clean(g, s),
        live(g, s) == Some(l),
        gen_at(s, l.seal) == Some(n),
    ensures
        steady(g, s, l, n),
{
    other_involution(g, l);
    // Clean means the store holds nothing outside the live footprint, and the other
    // slot's seal is outside it. So that seal is absent, not merely older.
    assert(live_footprint(g, s) =~= footprint(l));
    assert(!footprint(l).contains(other(g, l).seal));
    assert(!s.dom().contains(other(g, l).seal));
}

// ---------------------------------------------------------------------------
// §7.5 — recovery is a closure operator
// ---------------------------------------------------------------------------

/// Recovery keeps the live slot's seal and drops the other slot's, so re-running it
/// selects the same slot. This is the step that makes idempotence work.
pub proof fn live_stable(g: Geom, s: Store<CellVal>)
    requires
        slots_wf(g),
    ensures
        live(g, recover(g, s)) == live(g, s),
{
    let r = recover(g, s);
    match live(g, s) {
        None => {
            assert(live_footprint(g, s) =~= Set::<CellId>::empty());
            assert_maps_equal!(r, unit::<CellVal>());
            assert(gen_at(r, g.a.seal) is None);
            assert(gen_at(r, g.b.seal) is None);
        },
        Some(sl) => {
            assert(footprint(sl).contains(sl.seal));
            assert(live_footprint(g, s) =~= footprint(sl));
            if sl == g.a {
                assert(gen_at(r, g.a.seal) == gen_at(s, g.a.seal));
                assert(!footprint(g.a).contains(g.b.seal));
                assert(gen_at(r, g.b.seal) is None);
            } else {
                assert(gen_at(r, g.b.seal) == gen_at(s, g.b.seal));
                assert(!footprint(g.b).contains(g.a.seal));
                assert(gen_at(r, g.a.seal) is None);
            }
        },
    }
}

/// `recover ∘ recover = recover`. Its fixed points are the clean stores, so
/// recovery is a retraction `Store ↠ Clean`.
pub proof fn recover_idempotent(g: Geom, s: Store<CellVal>)
    requires
        slots_wf(g),
    ensures
        recover(g, recover(g, s)) =~= recover(g, s),
{
    live_stable(g, s);
    assert_maps_equal!(recover(g, recover(g, s)), recover(g, s));
}

/// §7.5 rule 1, formally: recovery restricted to `Clean` is the identity. This is
/// what "read-only until committed to a slot" means as a statement rather than a
/// comment.
pub proof fn recover_identity_on_clean(g: Geom, s: Store<CellVal>)
    requires
        clean(g, s),
    ensures
        recover(g, s) =~= s,
{
}

/// Every recovered store is clean — recovery lands in its own fixed-point set.
pub proof fn recover_lands_clean(g: Geom, s: Store<CellVal>)
    requires
        slots_wf(g),
    ensures
        clean(g, recover(g, s)),
{
    recover_idempotent(g, s);
}

} // verus!
