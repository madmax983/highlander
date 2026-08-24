//! Rung 1 and rung 2, composed.
//!
//! [`crate::cow`] proves that a snapshot taken while the machine runs is exactly the
//! memory as it was at the start of the checkpoint. [`crate::commit`] proves that a
//! commit neither tears nor forgets. This module joins them into the statement the
//! project actually wants:
//!
//! > Start a checkpoint. Let the machine keep running, writing whatever it likes,
//! > in any order. Commit the result. The stored checkpoint is the machine exactly
//! > as it was at the instant the checkpoint began.
//!
//! Neither half gives that on its own. Rung 1 alone stores a payload faithfully but
//! says nothing about where the payload came from, so a stop of the whole machine is
//! required to make the payload meaningful. Rung 2 alone collects a correct snapshot
//! but says nothing about whether a crash during the write destroys it.

use vstd::map::{assert_maps_equal, assert_maps_equal_internal};
use vstd::prelude::*;

use crate::algebra::{CellId, Delta, Store};
use crate::commit::Payload;
#[cfg(verus_only)]
use crate::commit::{commit_is_durable, commit_program, distinct_keys, kvs_delta, kvs_keys};
#[cfg(verus_only)]
use crate::cow::{CowOp, cow_run, cow_snapshot_is_exact, cow_start, ops_in_range};
#[cfg(verus_only)]
use crate::crash::denote;
use crate::machine::{Layout, Machine};
#[cfg(verus_only)]
use crate::machine::{
    capture, capture_dom, capture_restore_roundtrip, image, machine_fits,
    machine_outside_mechanism, restore, restore_ignores_the_mechanism,
};
use crate::protocol::{CellVal, Geom, Slot};
#[cfg(verus_only)]
use crate::protocol::{is_slot, other, recover, steady};

verus! {

/// **The rung 1 + rung 2 result.**
///
/// `mem0` is the memory of the machine when the checkpoint starts. `ops` is any
/// interleaving of writes by the machine and reads by the checkpoint writer, and
/// nothing constrains the order. If the writer visits every page, and the payload
/// the commit receives is what the writer collected, then the recovered checkpoint
/// holds each page of `mem0` at its start-of-checkpoint contents.
///
/// The machine was never stopped.
pub proof fn concurrent_checkpoint_is_exact(
    g: Geom,
    s0: Store<CellVal>,
    mem0: Delta<CellVal>,
    ops: Seq<CowOp<CellVal>>,
    kvs: Payload,
    target: Slot,
    n: nat,
    crc: u64,
)
    requires
        // rung 2: the writer visited every page, and each write hit a real page
        ops_in_range(ops, mem0),
        mem0.dom().subset_of(cow_run(cow_start(mem0), ops).out.dom()),
        // the commit receives exactly what the writer collected
        kvs_delta(kvs) =~= cow_run(cow_start(mem0), ops).out,
        kvs_keys(kvs) =~= mem0.dom(),
        // rung 1: a legitimate commit into a steady store
        is_slot(g, target),
        steady(g, s0, other(g, target), n),
        distinct_keys(kvs),
        kvs_keys(kvs).subset_of(target.payload),
    ensures
        forall|p: CellId| #![auto]
            mem0.dom().contains(p) ==> {
                let r = recover(g, denote(s0, commit_program(kvs, target, n, crc)));
                &&& r.dom().contains(p)
                &&& r[p] == mem0[p]
            },
{
    cow_snapshot_is_exact(mem0, ops);
    commit_is_durable(g, s0, kvs, target, n, crc);
    assert(kvs_delta(kvs) =~= mem0);
}

/// **Rungs 1, 2 and 3 together: a machine survives a crash.**
///
/// Capture a machine, commit the capture, crash at the worst possible moment,
/// recover, and restore. The machine that comes back is the machine that went in —
/// every register, every page of memory, every page table entry.
///
/// The store handed to `restore` is whatever recovery produced, and it contains the
/// seal. `restore` does not care: it reads the layout's cells and nothing else,
/// which is the mechanism boundary doing its job.
pub proof fn a_machine_survives_a_crash(
    g: Geom,
    s0: Store<CellVal>,
    lay: Layout,
    m0: Machine,
    kvs: Payload,
    target: Slot,
    n: nat,
    crc: u64,
)
    requires
        // rung 3: the capture describes this machine, and avoids the machinery
        machine_fits(lay, m0),
        machine_outside_mechanism(lay, g),
        kvs_delta(kvs) =~= capture(lay, m0),
        kvs_keys(kvs) =~= image(lay),
        // rung 1: a legitimate commit into a steady store
        is_slot(g, target),
        steady(g, s0, other(g, target), n),
        distinct_keys(kvs),
        kvs_keys(kvs).subset_of(target.payload),
    ensures
        ({
            let restored = restore(lay, recover(g, denote(s0, commit_program(kvs, target, n, crc))));
            &&& restored.regs =~= m0.regs
            &&& restored.mem =~= m0.mem
        }),
{
    let r = recover(g, denote(s0, commit_program(kvs, target, n, crc)));

    commit_is_durable(g, s0, kvs, target, n, crc);
    capture_dom(lay, m0);
    capture_restore_roundtrip(lay, m0);

    assert(image(lay).subset_of(r.dom()));
    assert(image(lay).subset_of(capture(lay, m0).dom()));
    assert_maps_equal!(r.restrict(image(lay)), capture(lay, m0).restrict(image(lay)));

    restore_ignores_the_mechanism(lay, r, capture(lay, m0));
}

} // verus!
