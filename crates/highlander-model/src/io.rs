//! Rung 5 — the I/O boundary.
//!
//! §8 of the design doc records the limitation: the external world does not go back
//! to an earlier state. The machine checkpoints at N+1, crashes, resumes from N —
//! but the packet went out, the UART byte went out, the DMA landed.
//!
//! Rung 4 made that limitation exact.
//! `process::a_crash_repeats_the_events_since_the_checkpoint` shows the world does
//! not receive an arbitrary disturbance. It receives one specific sequence a second
//! time, and the sequence is the events emitted since the last checkpoint:
//!
//! ```text
//!   without a crash:   A ++ E
//!   with a crash:      A ++ E ++ E
//! ```
//!
//! Rung 5 makes the second `E` harmless. There are 2 halves, and they need
//! different mechanisms.
//!
//! # The output half: a high-water mark
//!
//! Give each event a tag that increases. The boundary keeps the largest tag it has
//! accepted and drops each event at or below it.
//! [`a_repeated_window_is_delivered_once`] is the result: the world receives the
//! same effects whether the crash happened or not.
//!
//! This is what a TCP sequence number does, and what an idempotency key does in a
//! durable workflow engine. §8 records that the problem is the same one, and the
//! answer is the same one.
//!
//! # The input half: a journal
//!
//! An input arrives from outside, thus the capture does not hold it and the machine
//! state does not determine it. A replay needs the inputs that arrived before, and
//! only a record of them can supply those.
//! [`a_sound_journal_discharges_same_inputs`] connects the record to
//! `process::same_inputs`, which is the hypothesis the fifth gate protects.
//!
//! The journal is cells, thus rung 1 protects the journal. Nothing new is needed to
//! make it crash consistent: commit it with the payload and the same theorem covers
//! it.

use vstd::prelude::*;
use vstd::seq_lib::{assert_seqs_equal, assert_seqs_equal_internal};

#[cfg(verus_only)]
use crate::process::same_inputs;
use crate::process::{Event, Input};

verus! {

/// An event, with the tag the boundary uses to recognise a repeat.
pub struct Tagged {
    pub seq: nat,
    pub ev: Event,
}

/// The tags increase strictly, starting above `high`.
///
/// A real emitter gets this from a counter that the checkpoint captures, so the
/// count continues across a resume rather than restarting.
pub open spec fn increasing(es: Seq<Tagged>, high: nat) -> bool
    decreases es.len(),
{
    if es.len() == 0 {
        true
    } else {
        es[0].seq > high && increasing(es.drop_first(), es[0].seq)
    }
}

/// The largest tag the boundary has accepted after processing `es`.
pub open spec fn high_after(es: Seq<Tagged>, high: nat) -> nat
    decreases es.len(),
{
    if es.len() == 0 {
        high
    } else if es[0].seq > high {
        high_after(es.drop_first(), es[0].seq)
    } else {
        high_after(es.drop_first(), high)
    }
}

/// What the world actually receives.
///
/// The boundary accepts an event whose tag is above the high-water mark, and drops
/// every other event. This is the whole of the output half.
#[cfg(not(feature = "no-output-dedup"))]
pub open spec fn deliver(es: Seq<Tagged>, high: nat) -> Seq<Event>
    decreases es.len(),
{
    if es.len() == 0 {
        Seq::empty()
    } else if es[0].seq > high {
        seq![es[0].ev] + deliver(es.drop_first(), es[0].seq)
    } else {
        deliver(es.drop_first(), high)
    }
}

/// **The sixth falsifiability gate (`--features no-output-dedup`).**
///
/// A boundary that accepts everything. The repeated window then reaches the world a
/// second time, and §8 is a real fault instead of a bounded one.
/// `a_repeated_window_is_delivered_once` must fail with this feature on.
#[cfg(feature = "no-output-dedup")]
pub open spec fn deliver(es: Seq<Tagged>, high: nat) -> Seq<Event>
    decreases es.len(),
{
    if es.len() == 0 {
        Seq::empty()
    } else {
        seq![es[0].ev] + deliver(es.drop_first(), high)
    }
}

// ---------------------------------------------------------------------------
// Delivery is additive
// ---------------------------------------------------------------------------

pub proof fn deliver_additive(x: Seq<Tagged>, y: Seq<Tagged>, high: nat)
    ensures
        deliver(x + y, high) =~= deliver(x, high) + deliver(y, high_after(x, high)),
    decreases x.len(),
{
    if x.len() == 0 {
        assert_seqs_equal!(x + y, y);
    } else {
        assert_seqs_equal!((x + y).drop_first(), x.drop_first() + y);
        assert((x + y)[0] == x[0]);
        if x[0].seq > high {
            deliver_additive(x.drop_first(), y, x[0].seq);
        } else {
            deliver_additive(x.drop_first(), y, high);
        }
        assert_seqs_equal!(
            deliver(x + y, high),
            deliver(x, high) + deliver(y, high_after(x, high))
        );
    }
}

/// An increasing run raises the mark to its own last tag, so every one of its tags
/// is at or below the mark afterwards.
pub proof fn increasing_run_covers_itself(es: Seq<Tagged>, high: nat, k: int)
    requires
        increasing(es, high),
        0 <= k < es.len(),
    ensures
        es[k].seq <= high_after(es, high),
    decreases es.len(),
{
    if k == 0 {
        increasing_high_is_monotone(es.drop_first(), es[0].seq);
    } else {
        increasing_run_covers_itself(es.drop_first(), es[0].seq, k - 1);
        assert(es.drop_first()[k - 1] == es[k]);
    }
}

pub proof fn increasing_high_is_monotone(es: Seq<Tagged>, high: nat)
    requires
        increasing(es, high),
    ensures
        high_after(es, high) >= high,
    decreases es.len(),
{
    if es.len() == 0 {
    } else {
        increasing_high_is_monotone(es.drop_first(), es[0].seq);
    }
}

/// **An event at or below the mark does not reach the world.**
///
/// One line, and it is the whole of the output half. The hints below are about the
/// shape of a sequence and hold whatever `deliver` does, thus the postcondition is
/// what fails when the boundary stops checking the mark.
///
/// This is the target of the `no-output-dedup` gate.
pub proof fn a_stale_event_is_dropped(t: Tagged, rest: Seq<Tagged>, high: nat)
    requires
        t.seq <= high,
    ensures
        deliver(seq![t] + rest, high) =~= deliver(rest, high),
{
    assert((seq![t] + rest)[0] == t);
    assert_seqs_equal!((seq![t] + rest).drop_first(), rest);
}

/// Everything at or below the mark is dropped.
pub proof fn stale_events_are_dropped(es: Seq<Tagged>, high: nat)
    requires
        forall|k: int| #![auto] 0 <= k < es.len() ==> es[k].seq <= high,
    ensures
        deliver(es, high) =~= Seq::<Event>::empty(),
    decreases es.len(),
{
    if es.len() == 0 {
    } else {
        assert(es[0].seq <= high);
        assert forall|k: int| 0 <= k < es.drop_first().len() implies es.drop_first()[k].seq
            <= high by {
            assert(es.drop_first()[k] == es[k + 1]);
        }
        stale_events_are_dropped(es.drop_first(), high);
    }
}

// ---------------------------------------------------------------------------
// The rung 5 theorem, output half
// ---------------------------------------------------------------------------

/// **The world receives the same effects, crash or no crash.**
///
/// `a` is what the machine emitted before its last checkpoint, and `e` is what it
/// emitted after. A crash makes the world receive `a ++ e ++ e`. The boundary
/// delivers exactly what it would have delivered for `a ++ e`.
///
/// §8 is now bounded rather than open: the duplicate window is the events since the
/// last checkpoint, and a boundary with a high-water mark removes it.
pub proof fn a_repeated_window_is_delivered_once(a: Seq<Tagged>, e: Seq<Tagged>, high: nat)
    requires
        increasing(a + e, high),
    ensures
        deliver(a + e + e, high) =~= deliver(a + e, high),
{
    let ae = a + e;
    deliver_additive(ae, e, high);

    assert forall|k: int| 0 <= k < e.len() implies e[k].seq <= high_after(ae, high) by {
        assert(ae[a.len() + k] == e[k]);
        increasing_run_covers_itself(ae, high, a.len() + k);
    }
    stale_events_are_dropped(e, high_after(ae, high));
    assert_seqs_equal!(deliver(a + e + e, high), deliver(ae + e, high));
}

/// The same result, in the shape `process::world_across_crash` produces.
pub proof fn the_world_sees_the_same_effects(
    world_with_crash: Seq<Tagged>,
    world_without: Seq<Tagged>,
    a: Seq<Tagged>,
    e: Seq<Tagged>,
    high: nat,
)
    requires
        increasing(a + e, high),
        world_without =~= a + e,
        world_with_crash =~= a + e + e,
    ensures
        deliver(world_with_crash, high) =~= deliver(world_without, high),
{
    a_repeated_window_is_delivered_once(a, e, high);
}

// ---------------------------------------------------------------------------
// The rung 5 theorem, input half
// ---------------------------------------------------------------------------

/// The journal holds the inputs the machine consumed since its last checkpoint.
pub open spec fn journal_sound(journal: Seq<Input>, consumed: Seq<Input>) -> bool {
    journal =~= consumed
}

/// **A sound journal discharges the hypothesis the fifth gate protects.**
///
/// `process::replay_follows_the_same_trajectory` needs `same_inputs`. Nothing in the
/// machine can supply it, because an input arrives from outside and the capture does
/// not hold it. A journal supplies it, and this lemma is the connection.
///
/// The journal is cells. Commit it with the payload and rung 1 makes it crash
/// consistent, with no new mechanism and no new axiom.
pub proof fn a_sound_journal_discharges_same_inputs(journal: Seq<Input>, consumed: Seq<Input>)
    requires
        journal_sound(journal, consumed),
    ensures
        same_inputs(consumed, journal),
{
}

} // verus!
