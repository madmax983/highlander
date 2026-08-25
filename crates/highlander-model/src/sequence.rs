//! An unbounded sequence of commits.
//!
//! `theorem::crash_consistency` covers one commit. A kernel does not do one commit;
//! it does a commit every few milliseconds, forever, alternating between the two
//! slots. This module closes the gap between those two statements.
//!
//! # Why one commit was not enough
//!
//! The single-commit theorem originally required `clean(g, s0)`: the store holds
//! nothing outside the live slot's footprint. That is true of a freshly formatted
//! device and false of every store afterwards, because a successful commit
//! deliberately leaves the previous checkpoint in the other slot. **The theorem's
//! conclusion did not re-establish its own precondition**, so nothing covered the
//! second commit.
//!
//! `protocol::steady` is the weaker property that does survive: the live slot holds
//! generation `n`, and the other slot holds something strictly older, or nothing.
//! `commit::commit_preserves_steady` shows a commit maps a steady state to a steady
//! state with the slots exchanged and the generation raised.
//!
//! # Where A3 finally earns its place
//!
//! A3 — the generation counter never wraps — is stated in §5 of the design doc and
//! then used nowhere in the single-commit proof, because with `clean` the target
//! slot had no seal to compare against. Here the comparison is unavoidable:
//! recovery picks the slot with the greater generation, and across an unbounded run
//! that ordering is the only thing distinguishing the new checkpoint from the one
//! it replaced. A wrapped counter makes `gen_below` true of a *newer* slot, and
//! recovery then selects stale data.

use vstd::prelude::*;

use crate::algebra::Store;
use crate::commit::Payload;
#[cfg(verus_only)]
use crate::commit::{
    commit_is_crash_consistent, commit_preserves_steady, commit_program, distinct_keys, kvs_keys,
};
#[cfg(verus_only)]
use crate::crash::{denote, is_crash_outcome};
use crate::protocol::{CellVal, Geom, Slot};
#[cfg(verus_only)]
use crate::protocol::{is_slot, recover, steady};

verus! {

/// One commit's inputs: its payload, the CRC to stamp into the seal, and the slot
/// it targets.
///
/// With two slots the target was forced — it was the slot that was not live. With
/// `N` it is a choice, so a step has to say. Targeting the oldest slot is what
/// gives a rollback window; the theorem needs only that the target is not live.
pub type Step = (Payload, u64, Slot);

/// Run a sequence of commits from a steady state.
///
/// Returns the final store, the slot that ends up live, and its generation. The
/// target alternates on every step, which is what ping-pong means.
pub open spec fn run(
    g: Geom,
    s: Store<CellVal>,
    l: Slot,
    n: nat,
    cs: Seq<Step>,
) -> (Store<CellVal>, Slot, nat)
    decreases cs.len(),
{
    if cs.len() == 0 {
        (s, l, n)
    } else {
        let target = cs[0].2;
        let p = commit_program(cs[0].0, target, n, cs[0].1);
        run(g, denote(s, p), target, (n + 1) as nat, cs.drop_first())
    }
}

/// Each payload writes distinct cells inside the slot that step targets.
///
/// The target alternates, so this predicate has to walk the sequence rather than
/// state a single condition — a payload legal for one step is illegal for the next.
pub open spec fn payloads_wf(g: Geom, l: Slot, cs: Seq<Step>) -> bool
    decreases cs.len(),
{
    if cs.len() == 0 {
        true
    } else {
        let target = cs[0].2;
        &&& is_slot(g, target)
        &&& target != l
        &&& distinct_keys(cs[0].0)
        &&& kvs_keys(cs[0].0).subset_of(target.payload)
        &&& payloads_wf(g, target, cs.drop_first())
    }
}

/// The invariant survives the whole run, and the generation advances by exactly one
/// per commit.
pub proof fn run_preserves_steady(g: Geom, s: Store<CellVal>, l: Slot, n: nat, cs: Seq<Step>)
    requires
        steady(g, s, l, n),
        payloads_wf(g, l, cs),
    ensures
        steady(g, run(g, s, l, n, cs).0, run(g, s, l, n, cs).1, run(g, s, l, n, cs).2),
        run(g, s, l, n, cs).2 == n + cs.len(),
    decreases cs.len(),
{
    if cs.len() == 0 {
    } else {
        let target = cs[0].2;
        commit_preserves_steady(g, s, cs[0].0, target, l, n, cs[0].1);
        let s1 = denote(s, commit_program(cs[0].0, target, n, cs[0].1));
        run_preserves_steady(g, s1, target, (n + 1) as nat, cs.drop_first());
    }
}

/// **The result for a running machine.**
///
/// From any steady state and any well-formed sequence of commits:
///
/// 1. the run stays steady throughout, so recovery always has a live slot to find;
/// 2. the next commit is crash consistent — every crash during it recovers to
///    generation `n` or generation `n + 1`, and nothing else;
/// 3. **the state after that commit satisfies this lemma's own hypotheses again**,
///    for the rest of the sequence.
///
/// Clause 3 is what makes this cover every commit rather than only the first. The
/// lemma reproduces its own preconditions for the tail, so applying it repeatedly
/// walks the entire run. That is the property the single-commit theorem lacked.
pub proof fn run_is_crash_consistent(g: Geom, s: Store<CellVal>, l: Slot, n: nat, cs: Seq<Step>)
    requires
        steady(g, s, l, n),
        payloads_wf(g, l, cs),
    ensures
        // 1. the invariant holds for the whole run
        steady(g, run(g, s, l, n, cs).0, run(g, s, l, n, cs).1, run(g, s, l, n, cs).2),
        // 2. and 3., for a non-empty sequence
        cs.len() > 0 ==> ({
            let target = cs[0].2;
            let p = commit_program(cs[0].0, target, n, cs[0].1);
            // 2. this commit is crash consistent
            &&& forall|s2: Store<CellVal>|
                is_crash_outcome(s, p, s2) ==> recover(g, s2) =~= recover(g, s) || recover(g, s2)
                    =~= recover(g, denote(s, p))
            // 3. the tail satisfies this lemma's hypotheses again
            &&& steady(g, denote(s, p), target, (n + 1) as nat)
            &&& payloads_wf(g, target, cs.drop_first())
        }),
{
    run_preserves_steady(g, s, l, n, cs);
    if cs.len() > 0 {
        let target = cs[0].2;
        commit_is_crash_consistent(g, s, cs[0].0, target, l, n, cs[0].1);
        commit_preserves_steady(g, s, cs[0].0, target, l, n, cs[0].1);
    }
}

} // verus!
