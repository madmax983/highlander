# ADR 0001 — Ping-pong slots, not an append-only log

**Status:** Accepted
**Date:** 2026-08-24
**Referenced by:** design doc §7.1

## Context

Rung 1 needs a commit protocol whose crash behaviour can be proven. Two candidates:

**Append-only log.** Records are appended; recovery replays to the last complete
record. The crash model is as simple as it gets:

```
crash(log, n) = log.take(n)
```

No epochs, no barriers, nothing to reorder. A crash truncates, and truncation is
always a valid prefix.

**Ping-pong slots.** Two fixed checkpoint slots. Write the payload into the idle
slot, barrier, then atomically write a single seal cell naming the new generation.
Recovery reads whichever seal is newer. The crash model needs epochs, a barrier
axiom, and an arbitrary-subset landing model.

## Decision

Ping-pong.

## Rationale

The log's simplicity is real but temporary. Storage is bounded, so a log requires
compaction — and **compaction is an atomic switchover between two states, which is
ping-pong**. The hard problem arrives either way. The log merely defers it until
there is a working system that must then be retrofitted, at the point where the
retrofit is most expensive and least visible.

Build the hard part first, while it is the only part.

A second reason, specific to this project: the log's crash model is *too* simple to
be worth verifying. `crash(log, n) = log.take(n)` is a one-line lemma. It would
produce a proof artifact that demonstrates nothing about the technique, and the
whole premise of rung 1 (design doc §1.1) is that the checkpoint layer is where
protection derives from proof rather than from hardware.

## Consequences

**Accepted:** a substantially harder crash model — `2ⁿ` landing schedules per epoch
rather than `n + 1` prefixes; an explicit barrier axiom (A2); an explicit
single-cell atomicity axiom (A1); and the requirement that the seal fit in exactly
one cell (A4).

**Gained:** the axioms are now *named and few*. `crates/highlander-model` reduces
machine-wide crash consistency to A1, A2 and A4, with the CRC quarantined outside
the proven core as a probabilistic backstop (§5.1). That reduction is the deliverable.

**Measured:** the reference implementation's property tests report that without the
barrier, **63 of 128** landing schedules corrupt the store. The barrier is not a
performance tuning knob.

## Notes

The falsifiability gate (`scripts/gate.sh`) exists because of this decision. A crash
model this elaborate can be wrong in a way that still verifies; removing the barrier
must break the proof, or the model is describing nothing.
