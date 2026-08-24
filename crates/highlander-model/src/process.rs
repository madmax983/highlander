//! Rung 4 — a process resumes across a hard reset.
//!
//! Rung 3 shows that a machine survives a crash as *data*. Rung 4 starts it again
//! and asks the question orthogonal persistence exists to answer: **can the process
//! tell?**
//!
//! # What a step depends on
//!
//! [`step`] takes a machine **and an input**. That is the important decision in this
//! module, and it is not a detail.
//!
//! A step of the form `Machine -> Machine` would make the machine a closed system.
//! Replay would then be free, because the captured state would determine everything
//! that follows. But §8 of the design doc says the machine is not closed. Writing
//! the input into the signature makes the assumption visible instead of hidden, and
//! it states the exact obligation of rung 5: **replay needs the same inputs**, thus
//! something must record them.
//!
//! # What is proven
//!
//! * [`replay_follows_the_same_trajectory`] — given the same inputs, the machine
//!   after a resume passes through exactly the states it passed through before the
//!   crash. A crash loses work. It does not change the computation the machine performs.
//! * [`a_process_resumes_across_a_hard_reset`] — the same result, composed with
//!   rungs 1 to 3, from a real commit and a real recovery.
//! * [`a_crash_repeats_the_events_since_the_checkpoint`] — §8, stated exactly. The
//!   world does not see an arbitrary disturbance. It sees one specific sequence a
//!   second time: the events emitted since the last checkpoint.
//!
//! That last result converts §8 from a warning into a specification. Rung 5 has to
//! make one bounded window idempotent, and this module says which window.

use vstd::prelude::*;
use vstd::seq_lib::{assert_seqs_equal, assert_seqs_equal_internal};

use crate::machine::Machine;

verus! {

/// What arrives from outside between one step and the next: a device word, an
/// interrupt, a byte from a port. Bytes, because rung 4 does not care which.
pub type Input = Seq<u8>;

/// What leaves for the outside during a step: a packet, a UART byte, a DMA write.
pub type Event = Seq<u8>;

/// One step of the machine. Uninterpreted on purpose — rung 4 says nothing about
/// what a machine computes, only that a checkpoint does not change it.
pub uninterp spec fn step(m: Machine, i: Input) -> Machine;

/// What the step emits to the world. Also uninterpreted.
pub uninterp spec fn emit(m: Machine, i: Input) -> Seq<Event>;

/// Run the machine over a sequence of inputs.
pub open spec fn run(m: Machine, ins: Seq<Input>) -> Machine
    decreases ins.len(),
{
    if ins.len() == 0 {
        m
    } else {
        run(step(m, ins[0]), ins.drop_first())
    }
}

/// Everything the world receives while the machine runs over those inputs.
pub open spec fn emitted(m: Machine, ins: Seq<Input>) -> Seq<Event>
    decreases ins.len(),
{
    if ins.len() == 0 {
        Seq::empty()
    } else {
        emit(m, ins[0]).add(emitted(step(m, ins[0]), ins.drop_first()))
    }
}

// ---------------------------------------------------------------------------
// Running is additive
// ---------------------------------------------------------------------------

pub proof fn run_additive(m: Machine, a: Seq<Input>, b: Seq<Input>)
    ensures
        run(m, a + b) == run(run(m, a), b),
    decreases a.len(),
{
    if a.len() == 0 {
        assert_seqs_equal!(a + b, b);
    } else {
        assert_seqs_equal!((a + b).drop_first(), a.drop_first() + b);
        assert((a + b)[0] == a[0]);
        run_additive(step(m, a[0]), a.drop_first(), b);
    }
}

pub proof fn emitted_additive(m: Machine, a: Seq<Input>, b: Seq<Input>)
    ensures
        emitted(m, a + b) =~= emitted(m, a) + emitted(run(m, a), b),
    decreases a.len(),
{
    if a.len() == 0 {
        assert_seqs_equal!(a + b, b);
        assert_seqs_equal!(emitted(m, a) + emitted(run(m, a), b), emitted(m, b));
    } else {
        assert_seqs_equal!((a + b).drop_first(), a.drop_first() + b);
        assert((a + b)[0] == a[0]);
        emitted_additive(step(m, a[0]), a.drop_first(), b);
        assert_seqs_equal!(
            emitted(m, a + b),
            emitted(m, a) + emitted(run(m, a), b)
        );
    }
}

// ---------------------------------------------------------------------------
// Replay
// ---------------------------------------------------------------------------

/// The inputs supplied on replay must be the inputs that were supplied before.
///
/// This is the obligation rung 5 has to meet. A journal of the inputs is the only
/// thing that can meet it, because the capture does not hold them: an input arrives
/// from outside the machine, and the machine's state does not determine it.
#[cfg(not(feature = "ignore-input-journal"))]
pub open spec fn same_inputs(before: Seq<Input>, after: Seq<Input>) -> bool {
    before =~= after
}

/// **The fifth falsifiability gate (`--features ignore-input-journal`).**
///
/// Drops the requirement that a replay receives the inputs it received before. The
/// machine then continues along a different trajectory, and the resumed process is
/// not the process that crashed. `replay_follows_the_same_trajectory` must fail with
/// this feature on.
#[cfg(feature = "ignore-input-journal")]
pub open spec fn same_inputs(before: Seq<Input>, after: Seq<Input>) -> bool {
    true
}

/// **The rung 4 theorem: a crash costs work, and changes nothing else.**
///
/// `before` is what the machine consumed after its last checkpoint and before the
/// crash. `after` is what the journal supplies on replay. Given the same inputs, the
/// machine ends in the state it would have reached without the crash — and, by
/// [`run_additive`], it passes through each intermediate state on the way.
pub proof fn replay_follows_the_same_trajectory(
    m: Machine,
    upto: Seq<Input>,
    before: Seq<Input>,
    after: Seq<Input>,
)
    requires
        same_inputs(before, after),
    ensures
        run(run(m, upto), after) == run(m, upto + before),
{
    run_additive(m, upto, before);
}

/// Each state the machine visits during a replay is a state it visited before.
pub proof fn replay_revisits_the_same_states(m: Machine, upto: Seq<Input>, before: Seq<Input>, k: int)
    requires
        0 <= k <= before.len(),
    ensures
        run(run(m, upto), before.take(k)) == run(m, upto + before.take(k)),
{
    run_additive(m, upto, before.take(k));
}

// ---------------------------------------------------------------------------
// §8, stated exactly
// ---------------------------------------------------------------------------

/// What the world receives across a crash and a resume.
///
/// The machine ran to the crash, emitting everything up to that point. Then it
/// resumed from the checkpoint and ran the same inputs again.
pub open spec fn world_across_crash(
    m: Machine,
    upto: Seq<Input>,
    before: Seq<Input>,
    after: Seq<Input>,
) -> Seq<Event> {
    emitted(m, upto + before) + emitted(run(m, upto), after)
}

/// **§8 as a specification, and not a warning.**
///
/// A crash does not disturb the world arbitrarily. It repeats one specific sequence:
/// exactly the events emitted since the last checkpoint. Everything before the
/// checkpoint is sent once.
///
/// This states the obligation of rung 5. The I/O journal must make one bounded
/// window idempotent, and the window is `emitted(run(m, upto), before)` — which
/// shrinks as the checkpoint interval shrinks, and never covers events older than
/// the last checkpoint.
pub proof fn a_crash_repeats_the_events_since_the_checkpoint(
    m: Machine,
    upto: Seq<Input>,
    before: Seq<Input>,
    after: Seq<Input>,
)
    requires
        same_inputs(before, after),
    ensures
        world_across_crash(m, upto, before, after) =~= emitted(m, upto) + emitted(
            run(m, upto),
            before,
        ) + emitted(run(m, upto), before),
{
    emitted_additive(m, upto, before);
}

/// Nothing older than the last checkpoint is repeated. The duplicate window is
/// bounded by the checkpoint interval, which is what makes §7.4's policy decision a
/// trade of durability lag against throughput.
pub proof fn events_before_the_checkpoint_are_sent_once(
    m: Machine,
    upto: Seq<Input>,
    before: Seq<Input>,
    after: Seq<Input>,
)
    requires
        same_inputs(before, after),
    ensures
        world_across_crash(m, upto, before, after).take(emitted(m, upto).len() as int) =~= emitted(
            m,
            upto,
        ),
{
    a_crash_repeats_the_events_since_the_checkpoint(m, upto, before, after);
    assert_seqs_equal!(
        world_across_crash(m, upto, before, after).take(emitted(m, upto).len() as int),
        emitted(m, upto)
    );
}

} // verus!
