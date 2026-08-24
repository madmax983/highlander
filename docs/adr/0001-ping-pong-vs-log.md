# ADR 0001 — Two checkpoint slots, and not an append-only log

**Status:** Accepted
**Date:** 2026-08-24
**Referenced by:** design doc §7.1

## Context

Rung 1 needs a commit protocol with crash behaviour that a proof can examine. There
are two candidates.

**An append-only log.** The kernel adds each record to the end of the log. Recovery
reads the log again, up to the last complete record. The crash model is very simple:

```
crash(log, n) = log.take(n)
```

There are no epochs, no barriers and no writes that change order. A crash makes the
log shorter, and a shorter log is always correct.

**Two checkpoint slots.** There are two slots at fixed positions. The kernel writes
the payload into the slot that is not live. Then the kernel does a barrier. Then the
kernel writes one seal cell with the new generation number. Recovery reads the seal
with the larger generation number. This crash model needs epochs, a barrier axiom
and a model in which an arbitrary subset of the writes lands.

## Decision

Use two checkpoint slots.

## Reasons

The simplicity of the log is real, but it is temporary. Storage is not infinite,
thus a log needs compaction. **Compaction is an atomic change from one state to
another state, which is what two slots do.** The difficult problem arrives in both
designs. The log only delays the problem. The delay puts the problem after a system
that operates, and then a person must change that system. That change is most
expensive at that time, and it is also most difficult to see.

Do the difficult part first, when it is the only part.

There is a second reason, and it is specific to this project. The crash model of the
log is too simple to give value to a proof. `crash(log, n) = log.take(n)` is a lemma
of one line. A proof of it shows nothing about the method. But §1.1 of the design doc
states the purpose of rung 1: at the checkpoint layer, a proof gives protection, and
the hardware does not.

## Results

**Accepted:** a crash model that is much more difficult. There are 2^n schedules for
the writes of one epoch, and not n + 1 shorter logs. The model needs an explicit
barrier axiom (A2), an explicit axiom for the atomicity of one cell (A1), and a
condition that the seal is in one cell only (A4).

**Received:** the axioms now have names, and there are few of them.
`crates/highlander-model` reduces the crash consistency of a full machine to A1, A2
and A4. The CRC stays outside the proof as a probabilistic test (§5.1). This
reduction is the deliverable.

**Measured:** the property tests of the reference implementation show that 63 of 128
schedules cause damage to the store if the barrier is absent. The barrier is not a
control for performance.

## Note

This decision is the reason for the falsifiability gate (`scripts/gate.sh`). A crash
model of this size can be wrong and can still pass verification. If you remove the
barrier, the proof must fail. If the proof does not fail, the model shows nothing.
