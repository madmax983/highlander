# What the proof contains

**Companion to:** `0001-checkpoint-storage-model.md`
**Status:** Correct for the rung 1, 2 and 3 artifact — 83 verified, 0 errors.

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

Thus `scripts/gate.sh` tests 3 conditions for each gate:

1. Verification fails.
2. The failure occurs at the named lemma.
3. The failure is a **postcondition** failure, and not a compile error.

A negative test that passes because the crate did not compile gives no information.

There are now 2 gates:

| Feature | Lemma that must fail | Property it protects |
|---|---|---|
| `no-barrier` | `commit_establishes_shape` | A2 gives 2 epochs, and not 1 |
| `degenerate-recover` | `commit_is_durable` | a checkpoint keeps its data |
| `no-cow-copy` | `copy_preserves_visible` | the snapshot holds still |
| `overlapping-layout` | `capture_preserves_memory_at` | a capture loses nothing |

§5b describes the second gate, §10 the third, and §11 the fourth.

**A note on the target of a gate.** Gates 3 and 4 first pointed at a lemma with a
long proof. Verus then reported a failure at an assertion inside the proof, and the
output did not give the name of the lemma, thus `gate.sh` rejected the result as a
failure for the wrong reason. The correction was to state the property as a lemma
with an **empty proof body**: `copy_preserves_visible` and
`capture_preserves_memory_at`. Verus proves each of them without a hint, thus the
postcondition is what fails. A gate needs a target of this shape.

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

## 5b. Crash consistency permits a checkpoint that forgets everything

The theorem of §7.3 is a **safety** property. It says that a crash never shows a
torn state. A system that shows nothing obeys this property at no cost.

Give `recover` this definition: keep the seal of the live slot, and discard each
payload cell. It is a checkpoint system that loses all data. A test of the artifact
shows that this definition passes **61 of the 63** lemmas at that time. It obeys
`crash_consistency`, `run_is_crash_consistent`, `recover_idempotent`,
`recover_lands_clean`, `live_stable` and `seal_absent_recovers_old`. Both parts of
the disjunction in `crash_consistency` become equal, thus the disjunction is true.
Only 1 assertion in `concrete.rs`, about 1 specific store of 6 cells, rejected the
definition, and it did so by accident.

Thus the proof needed a second property. `commit::commit_is_durable` states it:

| Clause | Statement |
|---|---|
| 1 | each cell the payload wrote is in the recovered store, with the value that the commit wrote |
| 2 | the seal of the recovered store reads generation `n + 1` |
| 3 | the recovered store holds nothing outside the footprint of the target slot |

Clause 1 rejects the definition above. Clause 3 shows that the stale slot does not
enter the new checkpoint.

The `degenerate-recover` feature keeps this result honest. It replaces `recover`
with the definition that discards data, and `scripts/gate.sh` requires
`commit_is_durable` to fail. The reference implementation makes the same statement
in `a_forgetful_recover_is_crash_consistent_but_loses_data`: that test shows the
forgetful `recover` passes the full crash lattice, and then shows that each
committed cell is absent.

**Safety and durability are separate properties.** A proof of one is not a proof of
the other, and rung 1 now contains both.

---

## 5c. `wf` was not connected to anything

§4.4 states that the condition "no 2 writes in 1 epoch touch the same cell" occurs 3
times, and that the algebra needs it. `crash::wf` states that condition for a
program. But no lemma needed `wf`, and only `wf` itself used `wf`. It was dead.

This was not a defect in soundness. `commit::distinct_keys` states the same
condition for a payload, and each commit lemma needs `distinct_keys`. But `epochs`
uses `dunion`, and `dunion` is total. Thus `epochs` gives a value for a program that
is not well formed, and that value has no meaning. No lemma showed that the program
the protocol writes has meaning.

`commit::commit_program_is_wf` now shows it, with `wf_prepend_writes` and
`wf_commit_tail`. The claim in §4.4 is now true for the commit path.

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

---

## 10. Rung 2: copy-on-write

Rung 1 says that a commit does not tear and does not forget. It says nothing about
the time at which the machine can run. A checkpoint in rung 1 is a stop of the full
machine.

Rung 2 removes the stop. At the start of a checkpoint the machine marks each page
read only, and then the machine continues. A write to a page traps. The machine
copies the old contents to one side, and then the write continues. A background
writer collects the pages at its own speed.

### The design is one operator

The side table of copied pages is a delta, and the snapshot is `mem ◁ saved`.

`saved` holds the contents that a page had at the start of the checkpoint. `◁` gives
priority to the right operand (§4.1). Thus a page with a copy reads at its old
contents, and a page without a copy reads at its current contents, which are also
its old contents. **The algebra of rung 1 gives rung 2 its mechanism.** The property
that §4.1 records as a limitation — `◁` is not commutative — is the reason this
design operates.

### What the proof contains

| Lemma | Statement |
|---|---|
| `cow::copy_preserves_visible` | a write to a page that the writer does not hold does not change what the writer will see |
| `cow::mutate_preserves_inv` | a write by the machine keeps the invariant |
| `cow::flush_preserves_inv` | a read by the writer keeps the invariant |
| `cow::cow_run_preserves_inv` | **any** order of writes and reads keeps the invariant |
| `cow::complete_run_equals_mem0` | after the writer visits each page, the result is the memory at the start |
| `checkpoint::concurrent_checkpoint_is_exact` | rung 1 and rung 2 together: the stored checkpoint is the memory at the start |

### Where "the machine does not stop" is a statement

`mutate` and `flush` are both total functions, and `mutate_preserves_inv` has no
condition about the progress of the checkpoint. From each reachable state, each
write is permitted. That is the formal content of "the machine keeps running": the
machine never waits for the writer, and the writer never waits for the machine.

A model cannot state a bound on the length of a pause, because the model has no
clock. But it can state that no operation has a condition that another operation
must satisfy first. This model states that.

### The third gate

`--features no-cow-copy` removes the copy. `mutate` then writes the page and keeps
nothing, thus the snapshot follows the machine. A page that the machine writes after
the checkpoint starts, and that the writer collects after that, enters the checkpoint
at its **new** contents. The checkpoint then holds a mixture of 2 instants of the
machine. This is the same fault that rung 1 prevents at the storage layer, and it
arrives through the snapshot instead.

`copy_preserves_visible` must fail with this feature. The reference implementation
makes the same statement in `without_the_copy_the_snapshot_drifts`.

### What rung 2 does not contain

- Page tables, a trap handler and a read-only bit. The model has pages and writes to
  pages. It does not have an MMU. Rung 3 covers the hardware.
- A bound on the memory that `saved` uses. `flush` releases a copy, thus at most 1
  copy exists for each page, and only until the writer arrives. The model shows the
  release, but it does not state a bound.
- Any statement about time. There is no proof that the checkpoint finishes, or that
  the pause is short. A schedule in which the writer never operates obeys each lemma.

---

## 11. Rung 3: the state of a real machine

Rungs 1 and 2 move cells and never ask what a cell means. Rung 3 asks. The object
that persists is a machine, with registers and page tables, and the checkpoint must
hold all of it. If the capture loses anything, rung 4 cannot resume, and each result
below rung 3 describes a checkpoint of nothing in particular.

`machine::capture_restore_roundtrip` is the theorem: capture and then restore is the
identity on machines. The checkpoint is **lossless**.

### Page tables are ordinary memory

A page table is data in cells, thus `capture` treats it as data. This is a decision,
and not an omission. `capture` uses **physical** cells and never translates an
address. The other method is a capture of virtual memory, and it needs the page
tables in order to read the page tables. That circle has no start.
`page_tables_are_ordinary_memory` records the result.

### The mechanism boundary

§8 of the design doc records a boundary at the outside of the machine: the world
does not go back to an earlier state. There is a second boundary at the inside, and
the design doc does not record it.

The checkpoint machinery is part of the machine. Its seal cells, and the registers
of its writer, are state. If the capture holds them, then the capture must describe
itself, and that regress has no start. Thus the capture does not hold them:

| Lemma | Statement |
|---|---|
| `capture_excludes_the_mechanism` | a capture never writes a cell of the machinery |
| `restore_ignores_the_mechanism` | a restore reads the cells of its layout, and no other cell |

The second lemma is what makes the boundary safe. Recovery returns a slot that holds
a seal, and `restore` does not see it.

**Persistence is orthogonal for the machine, and not for the mechanism.** The
mechanism does not return from the checkpoint. A resume derives it again from the
seal. This is the same class of problem as §8, on the other side of the machine.

### The boundary is forced, and not a convention

`no_layout_captures_itself` shows that a capture always reaches outside the memory
it captures, for each machine with at least 1 register. Thus the boundary is a
result, and not a decision.

The obstruction is arithmetic, and it is not logic. A container of a fixed size
cannot hold a faithful copy of itself **and** anything else.
`capture_restore_roundtrip` states that the copy is faithful. Thus a proof of
losslessness removes the possibility of total self-inclusion. The 2 properties are
not compatible, and the artifact proves the first one.

This is the form of Russell's paradox, and it is not the form of Gödel's theorem.
There is no statement that the system can express and cannot decide. There is a
count, and the count does not permit the arrangement.

### Why the regress stops

The machinery has state, and a resume does not lose it. The state has 2 parts, and
each part has a different answer:

| Part | Answer |
|---|---|
| the 2 seal cells | they persist, outside the image of the machine |
| the progress of the writer during a checkpoint | a resume discards it, and the next checkpoint does the work again |

The second row is the reason rung 1 uses 2 slots. A checkpoint that stops in the
middle has no seal, thus recovery ignores it (§7.2). The machinery does not need to
record its own progress, because a partial checkpoint costs only the work, and it
costs no correctness.

### The condition of `•`, for the fourth time

§4.4 states that the definedness condition of `•` occurs 3 times. Rung 3 adds a
fourth: the register file and memory must not share a cell. `capture` uses `•` to
join them, and the condition is not decoration. The `overlapping-layout` gate removes
the condition, and then one region writes over the other and the capture loses state
with no indication of a fault.

### What rung 3 does not contain

- Any specific hardware. There is no x86, no ARM, no MMU and no trap handler. A
  register is a name for a byte string, and a cell is a name for a byte string.
- A resume. Rung 3 shows that a machine survives a crash as **data**. It does not
  start that machine again. Rung 4 covers that.
- The registers of the checkpoint writer itself. See the mechanism boundary above.
- Any statement about the order of the capture. `capture` is one function of the
  machine state, thus it describes one instant. Rung 2 gives that instant.
