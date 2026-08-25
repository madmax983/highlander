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

/// The checkpoint slots. Two is the minimum, and more is useful.
///
/// With two slots a commit destroys the only other checkpoint, so a machine that
/// checkpoints its own corruption has one commit in which to notice before the last
/// good state is gone. With `N` slots it has `N - 1`, and
/// [`crate::commit::a_commit_destroys_only_its_target`] is what makes that true.
pub struct Geom {
    pub slots: Seq<Slot>,
}

pub open spec fn is_slot(g: Geom, sl: Slot) -> bool {
    exists|i: int| 0 <= i < g.slots.len() && #[trigger] g.slots[i] == sl
}

/// The slots must genuinely not overlap. This is §7.5's rule 2 in geometric form —
/// the third appearance of `•`'s definedness condition (§4.4).
pub open spec fn slots_wf(g: Geom) -> bool {
    &&& g.slots.len() >= 2
    &&& forall|i: int| #![trigger g.slots[i]]
        0 <= i < g.slots.len() ==> !g.slots[i].payload.contains(g.slots[i].seal)
    &&& forall|i: int, j: int| #![trigger g.slots[i], g.slots[j]]
        0 <= i < g.slots.len() && 0 <= j < g.slots.len() && i != j ==> {
            &&& g.slots[i].seal != g.slots[j].seal
            &&& !g.slots[i].payload.contains(g.slots[j].seal)
            &&& g.slots[i].payload.disjoint(g.slots[j].payload)
        }
}

/// Distinct slots share nothing. Downstream proofs use this rather than unfolding
/// `slots_wf`, which keeps the index reasoning in one place.
pub proof fn distinct_slots_are_disjoint(g: Geom, x: Slot, y: Slot)
    requires
        slots_wf(g),
        is_slot(g, x),
        is_slot(g, y),
        x != y,
    ensures
        x.seal != y.seal,
        !x.payload.contains(y.seal),
        !y.payload.contains(x.seal),
        x.payload.disjoint(y.payload),
        !x.payload.contains(x.seal),
        !y.payload.contains(y.seal),
{
    let i = choose|i: int| 0 <= i < g.slots.len() && g.slots[i] == x;
    let j = choose|j: int| 0 <= j < g.slots.len() && g.slots[j] == y;
    assert(i != j);
    assert(!g.slots[i].payload.contains(g.slots[i].seal));
    assert(!g.slots[j].payload.contains(g.slots[j].seal));
}

/// A slot shares nothing with itself either — its seal is outside its payload.
pub proof fn a_slot_is_sane(g: Geom, x: Slot)
    requires
        slots_wf(g),
        is_slot(g, x),
    ensures
        !x.payload.contains(x.seal),
{
    let i = choose|i: int| 0 <= i < g.slots.len() && g.slots[i] == x;
    assert(!g.slots[i].payload.contains(g.slots[i].seal));
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

/// `sl` holds generation `n`, and every other slot holds something strictly older
/// or nothing at all.
///
/// This is stated as a property rather than computed by a scan, because what every
/// proof wants is the property. [`at_most_one_live_slot`] shows the property picks
/// out at most one slot — which is Raft's *election safety*, arriving here without
/// an election, because there is one reader and it can see every slot at once.
pub open spec fn is_live_at(g: Geom, s: Store<CellVal>, sl: Slot, n: nat) -> bool {
    &&& is_slot(g, sl)
    &&& gen_at(s, sl.seal) == Some(n)
    &&& forall|o: Slot| #![auto] is_slot(g, o) && o != sl ==> gen_below(gen_at(s, o.seal), n)
}

pub open spec fn is_live(g: Geom, s: Store<CellVal>, sl: Slot) -> bool {
    exists|n: nat| #[trigger] is_live_at(g, s, sl, n)
}

/// Which slot holds the live checkpoint. `None` means no slot dominates: either the
/// store is unformatted, or two slots claim the same generation.
///
/// **A tie yields `None` on purpose.** Two slots at one generation cannot arise from
/// a well-formed run, so a tie means the store is damaged. §2's last row says there
/// is nothing underneath this layer, and a bottom layer that guesses between two
/// equally plausible checkpoints is worse than one that declines to.
pub open spec fn live(g: Geom, s: Store<CellVal>) -> Option<Slot> {
    if exists|sl: Slot| is_live(g, s, sl) {
        Some(choose|sl: Slot| is_live(g, s, sl))
    } else {
        None
    }
}

/// **Election safety.** At most one slot is live.
///
/// Raft needs a protocol for this because its voters cannot see each other. Here
/// there is a single reader and it reads every slot, so the property is a
/// consequence of the generations being totally ordered — A3 again.
pub proof fn at_most_one_live_slot(g: Geom, s: Store<CellVal>, x: Slot, y: Slot)
    requires
        is_live(g, s, x),
        is_live(g, s, y),
    ensures
        x == y,
{
    let nx = choose|n: nat| is_live_at(g, s, x, n);
    let ny = choose|n: nat| is_live_at(g, s, y, n);
    if x != y {
        assert(gen_below(gen_at(s, y.seal), nx));
        assert(gen_below(gen_at(s, x.seal), ny));
    }
}

pub proof fn live_is_the_live_slot(g: Geom, s: Store<CellVal>, sl: Slot)
    requires
        live(g, s) == Some(sl),
    ensures
        is_live(g, s, sl),
{
    let c = choose|x: Slot| is_live(g, s, x);
    assert(is_live(g, s, c));
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
    &&& is_live_at(g, s, l, n)
}

/// A steady store recovers to the slot the invariant names.
pub proof fn steady_implies_live(g: Geom, s: Store<CellVal>, l: Slot, n: nat)
    requires
        steady(g, s, l, n),
    ensures
        live(g, s) == Some(l),
{
    assert(is_live(g, s, l));
    let c = choose|sl: Slot| is_live(g, s, sl);
    at_most_one_live_slot(g, s, c, l);
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
    // Clean means the store holds nothing outside the live footprint, and every
    // other slot's seal is outside it. So those seals are absent, not merely older.
    assert(live_footprint(g, s) =~= footprint(l));
    assert forall|o: Slot| is_slot(g, o) && o != l implies gen_below(gen_at(s, o.seal), n) by {
        distinct_slots_are_disjoint(g, l, o);
        assert(!footprint(l).contains(o.seal));
        assert(!s.dom().contains(o.seal));
    }
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
            assert_maps_equal!(r, Map::<CellId, CellVal>::empty());
            assert forall|sl: Slot| !is_live(g, r, sl) by {
                if is_live(g, r, sl) {
                    let m = choose|m: nat| is_live_at(g, r, sl, m);
                    assert(r.dom().contains(sl.seal));
                }
            }
        },
        Some(sl) => {
            live_is_the_live_slot(g, s, sl);
            let n = choose|n: nat| is_live_at(g, s, sl, n);
            assert(live_footprint(g, s) =~= footprint(sl));
            assert(footprint(sl).contains(sl.seal));
            assert(gen_at(r, sl.seal) == gen_at(s, sl.seal));

            // Recovery keeps only the live slot, so every other seal is gone.
            assert forall|o: Slot| is_slot(g, o) && o != sl implies gen_at(r, o.seal) is None by {
                distinct_slots_are_disjoint(g, sl, o);
                assert(!footprint(sl).contains(o.seal));
            }
            assert(is_live_at(g, r, sl, n));
            assert(is_live(g, r, sl));
            let c = choose|x: Slot| is_live(g, r, x);
            at_most_one_live_slot(g, r, c, sl);
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
