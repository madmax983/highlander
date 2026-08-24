//! Rung 2 — copy-on-write, so a checkpoint does not stop the world.
//!
//! Rung 1 proves that a commit does not tear and does not forget. It says nothing
//! about *when* the machine may run. As written, a checkpoint is a stop of the whole
//! machine: freeze, write every dirty page, barrier, seal.
//!
//! Copy-on-write removes the stop. At the start of a checkpoint the machine marks
//! each page read-only and then continues to run. A write to a page traps, the
//! machine copies the **old** contents aside, and the write proceeds. A background
//! writer drains the pages to the idle slot at its own speed.
//!
//! # The whole design, in one operator
//!
//! The side table of copied pages is a delta, and the snapshot is
//! [`visible`]`(c) = c.mem ◁ c.saved`.
//!
//! `saved` holds the contents a page had at the start of the checkpoint. `◁` gives
//! the right operand priority (§4.1). Thus a page that has been written reads at its
//! old value through `visible`, and a page that has not been written reads at its
//! current value, which is also its old value. **The non-commutativity of `◁` is the
//! mechanism, and not an obstacle.**
//!
//! # The theorem
//!
//! [`cow_run_preserves_inv`]: for **any** interleaving of writes by the machine and
//! reads by the checkpoint writer, the snapshot does not change. When the writer has
//! visited each page, [`complete_run_equals_mem0`] shows the result is exactly the
//! memory as it was at the start of the checkpoint.
//!
//! # Where "does not stop the world" is stated
//!
//! [`mutate`] is a total function, and [`mutate_preserves_inv`] has no condition
//! about the progress of the checkpoint. From each reachable state, each write is
//! permitted. That is the formal content of "the machine keeps running": the mutator
//! never waits for the writer. [`flush`] is total for the same reason, thus the
//! writer never waits for the mutator either.

use vstd::map::{assert_maps_equal, assert_maps_equal_internal};
use vstd::prelude::*;
use vstd::set_lib::{assert_sets_equal, assert_sets_equal_internal};

use crate::algebra::{CellId, Delta};
#[cfg(verus_only)]
use crate::algebra::{disjoint, override_, unit};

verus! {

broadcast use vstd::map_lib::group_map_properties;

/// A page is a cell. At this level of abstraction there is no difference, and §3.1
/// is deliberate about not fixing a size.
pub type PageId = CellId;

/// The state of a checkpoint that is in progress.
pub struct Cow<V> {
    /// What the machine reads and writes now.
    pub mem: Delta<V>,
    /// Contents copied aside, for pages written since the checkpoint started and
    /// not yet given to the writer.
    pub saved: Delta<V>,
    /// Pages the writer has already taken, at their start-of-checkpoint contents.
    pub out: Delta<V>,
}

/// The snapshot: what the checkpoint writer sees.
///
/// `c.mem ◁ c.saved` — a copied page reads at its old contents, and every other page
/// reads at its current contents.
pub open spec fn visible<V>(c: Cow<V>) -> Delta<V> {
    override_(c.mem, c.saved)
}

/// The state at the instant the checkpoint starts: nothing copied, nothing written.
pub open spec fn cow_start<V>(mem0: Delta<V>) -> Cow<V> {
    Cow { mem: mem0, saved: unit(), out: unit() }
}

/// **The invariant.**
///
/// Each page is in one of two conditions, and each condition records the same fact:
/// the page can still be recovered at its start-of-checkpoint contents.
///
/// * the writer has taken it, and `out` holds those contents; or
/// * the writer has not taken it, and `visible` gives those contents.
pub open spec fn cow_inv<V>(c: Cow<V>, mem0: Delta<V>) -> bool {
    &&& c.mem.dom() =~= mem0.dom()
    &&& c.out.dom().subset_of(mem0.dom())
    &&& c.saved.dom().subset_of(mem0.dom())
    &&& c.saved.dom().disjoint(c.out.dom())
    &&& forall|p: PageId| #![auto] c.out.dom().contains(p) ==> c.out[p] == mem0[p]
    &&& forall|p: PageId| #![auto]
        mem0.dom().contains(p) && !c.out.dom().contains(p) ==> visible(c)[p] == mem0[p]
}

pub proof fn start_satisfies_inv<V>(mem0: Delta<V>)
    ensures
        cow_inv(cow_start(mem0), mem0),
{
    assert_maps_equal!(visible(cow_start(mem0)), mem0);
}

// ---------------------------------------------------------------------------
// The machine writes a page
// ---------------------------------------------------------------------------

/// The machine writes `v` to page `p`.
///
/// If the page has not been copied and the writer has not taken it, copy the old
/// contents aside first. That copy is the whole of copy-on-write.
///
/// This function is **total**. There is no condition about the progress of the
/// checkpoint, thus the machine never waits.
#[cfg(not(feature = "no-cow-copy"))]
pub open spec fn mutate<V>(c: Cow<V>, p: PageId, v: V) -> Cow<V> {
    if c.out.dom().contains(p) || c.saved.dom().contains(p) {
        // Already preserved: the writer has it, or a copy exists.
        Cow { mem: c.mem.insert(p, v), saved: c.saved, out: c.out }
    } else {
        Cow { mem: c.mem.insert(p, v), saved: c.saved.insert(p, c.mem[p]), out: c.out }
    }
}

/// **The third falsifiability gate (`--features no-cow-copy`).**
///
/// Copy-on-write, without the copy. The machine writes the page and nothing keeps
/// the old contents, thus the snapshot follows the machine instead of holding still.
/// A page written after the checkpoint starts, and collected by the writer
/// afterwards, then enters the checkpoint at its **new** contents. The result mixes
/// two instants of the machine, which is exactly the tear that rung 1 works to
/// prevent at the storage layer.
///
/// `cow::mutate_preserves_inv` must fail with this feature on.
#[cfg(feature = "no-cow-copy")]
pub open spec fn mutate<V>(c: Cow<V>, p: PageId, v: V) -> Cow<V> {
    Cow { mem: c.mem.insert(p, v), saved: c.saved, out: c.out }
}

/// **The copy is what holds the snapshot still.**
///
/// A write to a page the writer has not collected does not change what the writer
/// will see. If a copy already exists, the copy stands. If not, `mutate` makes one
/// from the contents the write is about to replace.
///
/// This lemma is the target of the `no-cow-copy` gate. Its postcondition is the
/// whole of copy-on-write in one line, and it becomes false the moment the copy
/// stops happening.
pub proof fn copy_preserves_visible<V>(c: Cow<V>, p: PageId, v: V)
    requires
        !c.out.dom().contains(p),
        c.mem.dom().contains(p),
    ensures
        visible(mutate(c, p, v))[p] == visible(c)[p],
{
}

pub proof fn mutate_preserves_inv<V>(c: Cow<V>, mem0: Delta<V>, p: PageId, v: V)
    requires
        cow_inv(c, mem0),
        mem0.dom().contains(p),
    ensures
        cow_inv(mutate(c, p, v), mem0),
{
    let c2 = mutate(c, p, v);
    assert_sets_equal!(c2.mem.dom(), mem0.dom());

    assert forall|q: PageId| mem0.dom().contains(q) && !c2.out.dom().contains(q) implies visible(
        c2,
    )[q] == mem0[q] by {
        if q == p {
            if c.saved.dom().contains(p) {
                // A copy already exists and does not move, so the old contents stand.
                assert(visible(c2)[p] == c.saved[p]);
                assert(visible(c)[p] == c.saved[p]);
            } else {
                // The copy is made here, from the contents the write is about to
                // replace. Those are exactly the contents `visible` gave before.
                assert(visible(c2)[p] == c.mem[p]);
                assert(visible(c)[p] == c.mem[p]);
            }
        } else {
            // Other pages: neither map changed at q.
            assert(visible(c2)[q] == visible(c)[q]);
        }
    }
}

// ---------------------------------------------------------------------------
// The writer takes a page
// ---------------------------------------------------------------------------

/// The checkpoint writer takes page `p` and records its start-of-checkpoint
/// contents.
///
/// The copy is then no longer needed, thus `saved` releases it. This is what keeps
/// the memory cost of a checkpoint bounded: at most one copy per page, and only
/// until the writer arrives.
///
/// This function is also **total**. A second call for the same page has no effect,
/// which matters because the copy is gone by then and a naive re-read would take the
/// current contents instead of the old contents.
pub open spec fn flush<V>(c: Cow<V>, p: PageId) -> Cow<V> {
    if c.out.dom().contains(p) || !c.mem.dom().contains(p) {
        c
    } else {
        Cow { mem: c.mem, saved: c.saved.remove(p), out: c.out.insert(p, visible(c)[p]) }
    }
}

pub proof fn flush_preserves_inv<V>(c: Cow<V>, mem0: Delta<V>, p: PageId)
    requires
        cow_inv(c, mem0),
    ensures
        cow_inv(flush(c, p), mem0),
{
    let c2 = flush(c, p);
    if c.out.dom().contains(p) || !c.mem.dom().contains(p) {
    } else {
        assert_sets_equal!(c2.mem.dom(), mem0.dom());
        assert forall|q: PageId| mem0.dom().contains(q) && !c2.out.dom().contains(q) implies visible(
            c2,
        )[q] == mem0[q] by {
            assert(q != p);
            assert(visible(c2)[q] == visible(c)[q]);
        }
    }
}

// ---------------------------------------------------------------------------
// Any interleaving at all
// ---------------------------------------------------------------------------

/// One step of either party. A checkpoint is any interleaving of these.
pub enum CowOp<V> {
    /// The machine writes a page.
    Mutate(PageId, V),
    /// The checkpoint writer takes a page.
    Flush(PageId),
}

pub open spec fn cow_step<V>(c: Cow<V>, op: CowOp<V>) -> Cow<V> {
    match op {
        CowOp::Mutate(p, v) => mutate(c, p, v),
        CowOp::Flush(p) => flush(c, p),
    }
}

pub open spec fn cow_run<V>(c: Cow<V>, ops: Seq<CowOp<V>>) -> Cow<V>
    decreases ops.len(),
{
    if ops.len() == 0 {
        c
    } else {
        cow_run(cow_step(c, ops[0]), ops.drop_first())
    }
}

/// Every write targets a real page. Nothing else is required of the schedule.
pub open spec fn ops_in_range<V>(ops: Seq<CowOp<V>>, mem0: Delta<V>) -> bool {
    forall|i: int| #![trigger ops[i]]
        0 <= i < ops.len() ==> match ops[i] {
            CowOp::Mutate(p, _) => mem0.dom().contains(p),
            CowOp::Flush(_) => true,
        }
}

/// **The rung 2 theorem.**
///
/// For *any* interleaving of writes by the machine and reads by the writer, the
/// invariant holds. The machine is free to write any page at any moment, and the
/// snapshot the writer collects does not change.
pub proof fn cow_run_preserves_inv<V>(c: Cow<V>, mem0: Delta<V>, ops: Seq<CowOp<V>>)
    requires
        cow_inv(c, mem0),
        ops_in_range(ops, mem0),
    ensures
        cow_inv(cow_run(c, ops), mem0),
    decreases ops.len(),
{
    if ops.len() == 0 {
    } else {
        match ops[0] {
            CowOp::Mutate(p, v) => {
                assert(mem0.dom().contains(p));
                mutate_preserves_inv(c, mem0, p, v);
            },
            CowOp::Flush(p) => {
                flush_preserves_inv(c, mem0, p);
            },
        }
        assert(ops_in_range(ops.drop_first(), mem0)) by {
            assert forall|i: int| #![trigger ops.drop_first()[i]]
                0 <= i < ops.drop_first().len() implies match ops.drop_first()[i] {
                CowOp::Mutate(p, _) => mem0.dom().contains(p),
                CowOp::Flush(_) => true,
            } by {
                assert(ops.drop_first()[i] == ops[i + 1]);
            }
        }
        cow_run_preserves_inv(cow_step(c, ops[0]), mem0, ops.drop_first());
    }
}

/// When the writer has visited every page, what it collected is exactly the memory
/// as it was at the instant the checkpoint started.
pub proof fn complete_run_equals_mem0<V>(c: Cow<V>, mem0: Delta<V>)
    requires
        cow_inv(c, mem0),
        mem0.dom().subset_of(c.out.dom()),
    ensures
        c.out =~= mem0,
{
    assert_maps_equal!(c.out, mem0);
}

/// The two results together: start a checkpoint, run any schedule that visits every
/// page, and the collected payload is the memory of the machine at the start —
/// however much the machine changed in the meantime.
pub proof fn cow_snapshot_is_exact<V>(mem0: Delta<V>, ops: Seq<CowOp<V>>)
    requires
        ops_in_range(ops, mem0),
        mem0.dom().subset_of(cow_run(cow_start(mem0), ops).out.dom()),
    ensures
        cow_run(cow_start(mem0), ops).out =~= mem0,
{
    start_satisfies_inv(mem0);
    cow_run_preserves_inv(cow_start(mem0), mem0, ops);
    complete_run_equals_mem0(cow_run(cow_start(mem0), ops), mem0);
}

} // verus!
