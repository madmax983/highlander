# What the proof contains

**Companion to:** `0001-checkpoint-storage-model.md`
**Status:** Correct for the rung 1 artifact — 62 verified, 0 errors.

The design doc records the intent. This document records the contents of the
artifact. It includes each place where the work changed the design. Read this
document before you trust a statement in the design doc, because some statements
changed.

---

## 1. The statement of the theorem

The design doc writes §7.3 as `|image(recover ∘ Crash(p))| ≤ 2`. The proof
(`theorem::crash_consistency`) contains the equivalent statement in this form:

```rust
forall|s2| is_crash_outcome(s0, p, s2)
    ==> recover(g, s2) =~= recover(g, s0)
     || recover(g, s2) =~= recover(g, denote(s0, p))
```

There are two differences, and both are deliberate.

**There is no count.** The `Set` type of vstd holds finite sets only in this
release. A count of the image needs a proof of finiteness in each lemma, and no part
of the crate uses the count. Rungs 2 to 5 need the form above.

**The statement uses `recover(denote(…))`, and not `denote(…)`.** The text of the
design doc says that a crash recovers to "state N+1". But the store after a
successful commit still holds the previous checkpoint in the other slot. That is
what two slots mean. The recovered view is equal to the new checkpoint. The store
itself is not. `concrete::the_two_states_are_distinct` shows that the 2 states are
different. Thus 2 names for 1 state do not satisfy the theorem.

---

## 2. The bridge lemma was almost empty

§3.1 records the risk of an empty result, and puts that risk in the cell model. The
risk was also present one level higher, in §4.3.

`Map::union_prefer_right` of vstd is equal to `◁`. The obvious definition of `•` is
the same function with a `disjoint` condition. But then the bridge lemma
`disjoint(δ₁,δ₂) ⟹ δ₁ ◁ δ₂ = δ₁ • δ₂` is only reflexivity. Verification is
immediate, and the lemma shows nothing. But §4.4, §6.1 and §7.2 all use `•` and need
it to do necessary work.

Thus in `algebra.rs`, **`◁` prefers the right operand and `•` prefers the left
operand.** The bridge lemma then makes the correct statement: the choice of operand
has no effect if the domains are disjoint.

`algebra::dunion_comm` is the test for this condition. That lemma must fail if you
remove its `disjoint` condition. A check during development shows that it does fail.
If a later change lets that lemma pass without the condition, then `•` is equal to
`◁` again, and the algebra does no work.

---

## 3. The proof of the lattice is a bijection, and not a count

§6.2 says that the sub-deltas of an epoch are isomorphic to `𝒫(dom e)`, with
"`2^|dom e|` points total". `crash.rs` proves the isomorphism with
`sub_delta_is_restriction` and `restriction_is_sub_delta`. It does not prove the
count.

No part of the crate uses the count. §7.2 needs the lattice of one cell only, and
`crash::singleton_lattice` proves that case exactly: an epoch of one cell has 2
points, `⊥` and `⊤`. A1 and A4 give that lemma, and each step of §7.2 uses it.

`concrete.rs` supplies the count separately. It examines all `2² + 2 = 6` points of
a commit on a machine of 2 cells.

---

## 4. The position of the falsifiability gate

§7.3 says that the model is empty if the proof passes after you remove the barrier.
The identity of the proof that fails is more specific than the design doc shows, and
the difference is important for maintenance of the gate.

Verus examines each function against its own signature. `crash_consistency` has
`commit_shape` as a *condition*, thus it continues to pass after you remove the
barrier. That result is correct, because the lemma makes no statement about a
program without that shape. The lemma that fails is
`commit::commit_establishes_shape`. That lemma states that the program the protocol
*writes* has the shape. Without a barrier the protocol writes 1 epoch, and not 2.

Thus `scripts/gate.sh` tests 3 conditions:

1. Verification fails.
2. The failure occurs at `commit_establishes_shape`.
3. The failure is a **postcondition** failure, and not a compile error.

A negative test that passes because the crate did not compile gives no information.

Note also that well-formedness (`wf`) holds without the barrier. A payload with
distinct keys, and a seal outside the payload region, is a legal program. The
barrier does not make the program well-formed. The barrier makes the program *2
epochs*. Do not make `wf` stronger to catch this condition, because that is a change
to the wrong part.

---

## 5. A1 has a formal position, and a price

§6.3 asks for a refinement layer in which "A1 is exactly the assumption that `tear`
is trivial". `refine.rs` gives 2 more exact statements:

- `bytewise_tear_violates_a1` — with a tear at byte level, **A1 is false** for each
  cell of more than 1 byte. The witness is explicit: a write of `01 01` over `00 00`
  can leave `00 01`. Thus A1 has content, and the model does not assume it.
- `atomic_unit_tear_is_trivial` — A1 is true if the cell is equal to the atomic
  write unit of the hardware. Thus "make each cell the size of the atomic unit" is a
  condition of the theorem, and not advice about performance.
- `abstract_model_assumes_a1` — the abstract crash lattice gives 2 results for each
  cell. Read this with the first item: **if A1 is false, the abstract model is
  unsound. It is not only less exact.**

**Deferred, and recorded here:** the full simulation argument. That argument shows
that the model at byte level refines the abstract model under A1, for full programs
of many cells. It is an operation of approximately the same size as the remainder of
the crate. §10.1 permits a delay if a document records the delay. This section and
the module docs in `refine.rs` are that record.

---

## 5a. One commit was not sufficient, thus the invariant became weaker

The first version of this artifact proved crash consistency for **one commit from a
new store**. It did not show that this result is the same as a result for a machine.

`crash_consistency` needed `clean(g, s0)`: the store holds nothing outside the
footprint of the live slot. That condition is true for a new device. It is false for
each store after the first commit, because a successful commit leaves the previous
checkpoint in the other slot on purpose. That is what 2 slots mean. Thus the
conclusion of the theorem did not give the condition of the theorem again, and no
lemma covered the second commit. §7 of the design doc has the same gap, because it
describes 1 commit in all of its text.

`clean` did necessary work in 1 position only. `seal_absent_recovers_old` used
`clean` to show that `gen_at(s0, target.seal) is None` — the target slot has no seal,
thus recovery cannot select it. That statement is false for the second commit: the
target is the old slot, and it still holds its previous seal.

`protocol::steady` is the correction. It states the weaker property that a commit
keeps:

```rust
pub open spec fn steady(g: Geom, s: Store<CellVal>, l: Slot, n: nat) -> bool {
    &&& slots_wf(g)
    &&& is_slot(g, l)
    &&& gen_at(s, l.seal) == Some(n)
    &&& gen_below(gen_at(s, other(g, l).seal), n)   // older, or absent
}
```

The condition is not "the target has no seal". The condition is "the generation of
the target is less than n". `clean_implies_steady` shows that the old condition
gives the new condition. Thus `steady` is more general, and the new device is still
a correct start state.

**A3 now does necessary work.** A3 says that the generation counter never wraps. §5
of the design doc states A3, but the proof of 1 commit uses A3 nowhere, because with
`clean` there is no second generation to compare. In a run of commits the comparison
is necessary: recovery selects the slot with the larger generation, and that order is
the only difference between the new checkpoint and the checkpoint it replaces. A
counter that wraps makes `gen_below` true for a *newer* slot, and then recovery
returns old data. A3 is no longer decoration.

`commit.rs` and `sequence.rs` now contain these results:

| Lemma | Statement |
|---|---|
| `commit_preserves_steady` | a commit changes a steady state to a steady state, with the slots exchanged and the generation larger |
| `run_preserves_steady` | the invariant holds for a full run, and each commit adds exactly 1 to the generation |
| `run_is_crash_consistent` | the next commit is crash consistent, **and** the state after it gives the conditions of this lemma again |

The third row makes the result cover each commit, and not the first commit only. The
lemma gives its own conditions again for the remainder of the sequence. Thus repeated
use of the lemma covers the full run.

`concrete::a_second_commit_is_also_safe` shows this result on the machine of 6 cells.
It also proves `!clean(g, s1)`. Thus the store after 1 commit is truly not clean, and
the gap was real.

### A related property that the proof does not need

A commit can write a **subset** of the payload region of its target. No lemma needs
the payload to cover the full slot. A partial payload leaves older cells in
position, thus the recovered checkpoint can hold more than 1 generation.

That result is correct for the question this crate answers: can a checkpoint tear?
It is not an error. The incremental checkpoints of rung 2 need this freedom. A system
that needs a checkpoint of a full slot must make
`kvs_keys(kvs).subset_of(target.payload)` an equality at its own call sites.

---

## 6. The CRC does no work, and a rule keeps it that way

§5.1 says that the CRC is a probabilistic test, outside the proof. `CellVal::Seal`
has a `crc` field, and **no spec and no proof reads that field**. `recover` does not
examine it. This is deliberate: with A1 and A2 the protocol is correct without a
checksum. A proof that used `crc` would change a proven result into a probabilistic
result, and no document would show the change.

If you need the CRC to do work, that is a different theorem with a stated
probability of collision. It does not belong in this crate.

---

## 7. Model decisions to know

**Crash results are a predicate, and not a `Set`.** The `Set` type of vstd holds
finite sets only. `Set::new` returns `Option`. Each user of the crate needs "for all
crash results …", and `is_crash_outcome` gives that form directly.

**`V` is generic in §4 and §6, and concrete in §7.** The algebra and the crash model
never examine the contents of a cell. `recover` must examine the contents, because
it reads a generation number. Thus `protocol.rs` uses the concrete type `CellVal`.

**The geometry of the slots is a parameter, and not a constant.** The code gives
`Geom` to each lemma. `slots_wf` states the conditions for no overlap. This is rule 2
of §7.5, in the form of a geometry.

**The field name is `generation`, and not `gen`.** `gen` is a reserved word in Rust
edition 2024.

---

## 8. The value of the reference implementation

`crates/highlander-ref` is a second implementation of the protocol, in usual Rust.
It has **no dependency on `highlander-model`**. A reference implementation that
shared code with the specification gives no information.

Its property tests examine the full crash lattice. They do not use samples. The
negative test has the most value: without a barrier, **63 of 128** schedules for the
writes recover to a state that is neither checkpoint. The barrier is not a control
for performance.

A second test walks a run of up to 4 commits and examines the full lattice at each
step. It also tests that the store is *not* clean after each commit, which is the
condition that §5a describes.

---

## 9. What the proof does not contain

- Any result for rungs 2 to 5. There is no COW, no register, no page table and no
  continuation after a reset.
- The I/O boundary (§8). The external world still does not go back to an earlier
  state.
- Progress of any type. The theorem says that a crash recovers to 1 of 2 consistent
  states. It says nothing about progress, and a protocol that does no commit obeys
  it. `run_is_crash_consistent` says that each commit in a sequence is safe. It does
  not say that the machine does a commit.
- A3 is still an assumption, and not a theorem. But each generation comparison in a
  run now uses A3. See §5a.
- That the *implementation* does the barrier that the model assumes. A2 is a promise
  about hardware, and a promise about a future driver. This crate cannot test either
  promise.
