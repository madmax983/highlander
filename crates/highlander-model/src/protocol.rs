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
pub open spec fn recover(g: Geom, s: Store<CellVal>) -> Store<CellVal> {
    s.restrict(live_footprint(g, s))
}

/// The fixed points of [`recover`].
pub open spec fn clean(g: Geom, s: Store<CellVal>) -> bool {
    recover(g, s) =~= s
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
