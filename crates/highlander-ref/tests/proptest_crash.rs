//! §10.1 acceptance gate 3 — property tests against the reference implementation.
//!
//! The Verus proof checks the model against itself. These tests check that the
//! protocol, expressed independently in ordinary Rust, survives random payloads
//! landing in random orders at random interruption points.
//!
//! Two directions, and the second matters as much as the first:
//!
//! * [`crash_always_recovers_to_one_of_two`] — with the barrier, every one of the
//!   `2ⁿ` landing schedules recovers to generation `n` or `n + 1`.
//! * [`without_a_barrier_the_property_is_false`] — without it, there is a landing
//!   schedule that recovers to neither. A test suite that only demonstrates the good
//!   case cannot tell you the barrier is doing anything.

use std::collections::BTreeSet;

use highlander_ref::{
    CellVal, Geom, Slot, Store, clean, commit_epochs, crash_at, denote, gen_at, live, recover,
};
use proptest::prelude::*;

const A_SEAL: u64 = 0;
const B_SEAL: u64 = 100;
const SLOT_WIDTH: u64 = 6;

fn geometry() -> Geom {
    Geom {
        a: Slot {
            seal: A_SEAL,
            payload: (1..=SLOT_WIDTH).collect(),
        },
        b: Slot {
            seal: B_SEAL,
            payload: (101..=100 + SLOT_WIDTH).collect(),
        },
    }
}

/// A clean store: slot A sealed at `generation`, slot B entirely absent.
fn initial_store(generation: u64, live_bytes: &[u8]) -> Store {
    let mut s = Store::new();
    s.insert(A_SEAL, CellVal::Seal { generation, crc: 0 });
    for (i, b) in live_bytes.iter().enumerate() {
        s.insert(1 + i as u64, CellVal::Data(vec![*b]));
    }
    s
}

/// Every subset of `cells`, as landing schedules. This is the crash lattice,
/// enumerated: `2^|cells|` points, not `|cells| + 1` prefixes.
fn all_subsets(cells: &BTreeSet<u64>) -> Vec<BTreeSet<u64>> {
    let v: Vec<u64> = cells.iter().copied().collect();
    (0u32..(1u32 << v.len()))
        .map(|mask| {
            v.iter()
                .enumerate()
                .filter(|(i, _)| mask & (1 << i) != 0)
                .map(|(_, c)| *c)
                .collect()
        })
        .collect()
}

fn payload_strategy() -> impl Strategy<Value = Vec<(u64, Vec<u8>)>> {
    prop::collection::vec(any::<u8>(), 1..=SLOT_WIDTH as usize).prop_map(|bytes| {
        bytes
            .into_iter()
            .enumerate()
            .map(|(i, b)| (101 + i as u64, vec![b]))
            .collect()
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// The theorem, executably: for every epoch and every subset of that epoch that
    /// landed, recovery yields the old checkpoint or the new one. Nothing else.
    #[test]
    fn crash_always_recovers_to_one_of_two(
        generation in 0u64..1_000_000,
        live in prop::collection::vec(any::<u8>(), SLOT_WIDTH as usize),
        payload in payload_strategy(),
    ) {
        let g = geometry();
        prop_assert!(g.slots_wf());

        let s0 = initial_store(generation, &live);
        prop_assert!(clean(&g, &s0));

        let epochs = commit_epochs(&payload, &g.b, generation, 0, true);
        prop_assert_eq!(epochs.len(), 2, "with a barrier there are exactly two epochs");

        let old = recover(&g, &s0);
        let new = recover(&g, &denote(&s0, &epochs));

        for (k, epoch) in epochs.iter().enumerate() {
            let cells: BTreeSet<u64> = epoch.keys().copied().collect();
            for landed in all_subsets(&cells) {
                let crashed = crash_at(&s0, &epochs, k, &landed);
                let got = recover(&g, &crashed);
                prop_assert!(
                    got == old || got == new,
                    "epoch {k}, landed {landed:?} recovered to a third state",
                );
            }
        }
    }

    /// Recovery is a closure operator (§7.5): its fixed points are the clean stores.
    #[test]
    fn recover_is_idempotent(
        generation in 0u64..1_000_000,
        live in prop::collection::vec(any::<u8>(), SLOT_WIDTH as usize),
        payload in payload_strategy(),
    ) {
        let g = geometry();
        let s0 = initial_store(generation, &live);
        let epochs = commit_epochs(&payload, &g.b, generation, 0, true);

        for (k, epoch) in epochs.iter().enumerate() {
            let cells: BTreeSet<u64> = epoch.keys().copied().collect();
            for landed in all_subsets(&cells) {
                let crashed = crash_at(&s0, &epochs, k, &landed);
                let once = recover(&g, &crashed);
                let twice = recover(&g, &once);
                prop_assert_eq!(&once, &twice, "recover is not idempotent");
                prop_assert!(clean(&g, &once), "recover did not land in Clean");
            }
        }
    }

    /// A crash in the payload epoch collapses `2ⁿ` points to **one** — §7.2's first
    /// bullet, checked rather than assumed.
    #[test]
    fn payload_epoch_collapses_to_a_single_point(
        generation in 0u64..1_000_000,
        live in prop::collection::vec(any::<u8>(), SLOT_WIDTH as usize),
        payload in payload_strategy(),
    ) {
        let g = geometry();
        let s0 = initial_store(generation, &live);
        let epochs = commit_epochs(&payload, &g.b, generation, 0, true);
        let old = recover(&g, &s0);

        let cells: BTreeSet<u64> = epochs[0].keys().copied().collect();
        for landed in all_subsets(&cells) {
            let crashed = crash_at(&s0, &epochs, 0, &landed);
            prop_assert_eq!(recover(&g, &crashed), old.clone());
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// **A run of commits, not one commit.**
    ///
    /// The single-commit theorem needed a *clean* store — one holding nothing
    /// outside the live slot. A successful commit leaves the previous checkpoint in
    /// the other slot, so the store is never clean again, and the single-commit
    /// result did not cover the second commit.
    ///
    /// This test walks a run of up to 4 commits, alternating slots, and checks the
    /// whole crash lattice at every step. It also asserts the store is *not* clean
    /// after each commit — the condition that made the gap real rather than
    /// theoretical. `concrete::a_second_commit_is_also_safe` proves the same thing.
    #[test]
    fn a_run_of_commits_stays_crash_consistent(
        generation in 0u64..1_000,
        live in prop::collection::vec(any::<u8>(), SLOT_WIDTH as usize),
        runs in prop::collection::vec(
            prop::collection::vec(any::<u8>(), 1..=SLOT_WIDTH as usize), 1..=4),
    ) {
        let g = geometry();
        let mut s = initial_store(generation, &live);
        prop_assert!(clean(&g, &s), "a freshly formatted store is clean");

        let mut live_seal = A_SEAL;
        let mut n = generation;

        for (step, bytes) in runs.iter().enumerate() {
            let target = if live_seal == A_SEAL { &g.b } else { &g.a };
            let cells: Vec<u64> = target.payload.iter().copied().collect();
            let payload: Vec<(u64, Vec<u8>)> = bytes
                .iter()
                .enumerate()
                .map(|(i, b)| (cells[i], vec![*b]))
                .collect();

            let epochs = commit_epochs(&payload, target, n, 0, true);
            let old = recover(&g, &s);
            let new = recover(&g, &denote(&s, &epochs));

            for (k, epoch) in epochs.iter().enumerate() {
                let ec: BTreeSet<u64> = epoch.keys().copied().collect();
                for landed in all_subsets(&ec) {
                    let got = recover(&g, &crash_at(&s, &epochs, k, &landed));
                    prop_assert!(
                        got == old || got == new,
                        "commit {step}: epoch {k}, landed {landed:?} gave a third state",
                    );
                }
            }

            s = denote(&s, &epochs);
            live_seal = target.seal;
            n += 1;

            prop_assert_eq!(gen_at(&s, live_seal), Some(n));
            prop_assert!(
                !clean(&g, &s),
                "commit {step} left a clean store; the previous checkpoint should still be there",
            );
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    /// **Durability: a commit stores what it was given.**
    ///
    /// Crash consistency says a crash never exposes a torn state. That is a safety
    /// property, and a system exposing nothing satisfies it for free. This is the
    /// other half: after the commit completes, the recovered store holds each cell
    /// that was written, with the value that was written.
    #[test]
    fn a_commit_stores_what_it_was_given(
        generation in 0u64..1_000_000,
        live_bytes in prop::collection::vec(any::<u8>(), SLOT_WIDTH as usize),
        payload in payload_strategy(),
    ) {
        let g = geometry();
        let s0 = initial_store(generation, &live_bytes);
        let epochs = commit_epochs(&payload, &g.b, generation, 0, true);
        let r = recover(&g, &denote(&s0, &epochs));

        for (c, bytes) in &payload {
            prop_assert_eq!(
                r.get(c),
                Some(&CellVal::Data(bytes.clone())),
                "cell {} did not survive the commit",
                c,
            );
        }
        prop_assert_eq!(gen_at(&r, B_SEAL), Some(generation + 1));
        // and nothing from the other slot leaked in
        for c in std::iter::once(A_SEAL).chain(1..=SLOT_WIDTH) {
            prop_assert!(
                !r.contains_key(&c),
                "cell {} from the stale slot is in the checkpoint",
                c,
            );
        }
    }
}

/// **Why durability needs its own proof: the executable form of the second gate.**
///
/// This `recover` keeps the live seal and discards every payload cell — a checkpoint
/// system that forgets all of your data. It still satisfies crash consistency,
/// because a store holding nothing can never tear. Only a durability check rejects
/// it.
///
/// The Verus gate (`scripts/gate.sh --features degenerate-recover`) makes the same
/// point against the proof: 61 of 63 lemmas accept this definition.
#[test]
fn a_forgetful_recover_is_crash_consistent_but_loses_data() {
    fn recover_seal_only(g: &Geom, s: &Store) -> Store {
        match live(g, s) {
            None => Store::new(),
            Some(sl) => s
                .iter()
                .filter(|(k, _)| **k == sl.seal)
                .map(|(k, v)| (*k, v.clone()))
                .collect(),
        }
    }

    let g = geometry();
    let s0 = initial_store(7, &[0; SLOT_WIDTH as usize]);
    let payload: Vec<(u64, Vec<u8>)> = (101..=106).map(|c| (c, vec![1u8])).collect();
    let epochs = commit_epochs(&payload, &g.b, 7, 0, true);

    let old = recover_seal_only(&g, &s0);
    let new = recover_seal_only(&g, &denote(&s0, &epochs));

    // Crash consistency still holds, over the entire lattice.
    for (k, epoch) in epochs.iter().enumerate() {
        let cells: BTreeSet<u64> = epoch.keys().copied().collect();
        for landed in all_subsets(&cells) {
            let got = recover_seal_only(&g, &crash_at(&s0, &epochs, k, &landed));
            assert!(
                got == old || got == new,
                "a forgetful recover should still be crash consistent",
            );
        }
    }

    // But every committed cell is gone.
    for (c, _) in &payload {
        assert!(!new.contains_key(c), "cell {c} should have been discarded");
    }
    assert_eq!(new.len(), 1, "only the seal survives");

    // The real recover keeps them.
    let honest = recover(&g, &denote(&s0, &epochs));
    for (c, bytes) in &payload {
        assert_eq!(honest.get(c), Some(&CellVal::Data(bytes.clone())));
    }
}

/// **The negative case, executably.**
///
/// Without the barrier the payload and seal share one epoch, so a landing schedule
/// can deliver the seal while withholding the payload. The result claims to be
/// generation `n + 1` but its payload region is empty — a state that is neither
/// checkpoint.
///
/// This is the same failure the Verus gate (`scripts/gate.sh`) detects, observed
/// from the other side. If this test ever stops finding a counterexample, the
/// reference implementation has stopped modelling the thing the proof is about.
#[test]
fn without_a_barrier_the_property_is_false() {
    let g = geometry();
    let s0 = initial_store(7, &[0, 0, 0, 0, 0, 0]);
    assert!(clean(&g, &s0));

    let payload: Vec<(u64, Vec<u8>)> = (101..=106).map(|c| (c, vec![1u8])).collect();

    let epochs = commit_epochs(&payload, &g.b, 7, 0, false);
    assert_eq!(
        epochs.len(),
        1,
        "without a barrier the two epochs merge into one"
    );

    let old = recover(&g, &s0);
    let new = recover(&g, &denote(&s0, &epochs));

    // The seal lands; nothing else does.
    let seal_only: BTreeSet<u64> = [B_SEAL].into_iter().collect();
    let torn = crash_at(&s0, &epochs, 0, &seal_only);
    let got = recover(&g, &torn);

    assert_ne!(got, old, "expected a state that is not the old checkpoint");
    assert_ne!(got, new, "expected a state that is not the new checkpoint");

    // Concretely: it presents as generation 8 with an empty payload region.
    assert_eq!(
        got.get(&B_SEAL),
        Some(&CellVal::Seal {
            generation: 8,
            crc: 0
        })
    );
    for c in 101..=106 {
        assert!(
            !got.contains_key(&c),
            "cell {c} should be missing — that is exactly the corruption",
        );
    }

    // And a brute-force search agrees the barrier is the only thing preventing it.
    let cells: BTreeSet<u64> = epochs[0].keys().copied().collect();
    let bad = all_subsets(&cells)
        .into_iter()
        .filter(|landed| {
            let r = recover(&g, &crash_at(&s0, &epochs, 0, landed));
            r != old && r != new
        })
        .count();
    assert!(
        bad > 0,
        "no bad landing schedule found — the gate is not testing anything"
    );
    eprintln!(
        "without a barrier, {bad} of {} landing schedules corrupt the store",
        1 << cells.len()
    );
}
