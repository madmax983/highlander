# What was actually proven

**Companion to:** `0001-checkpoint-storage-model.md`
**Status:** Current as of the rung-1 artifact — 51 verified, 0 errors.

The design doc is the record of intent. This is the record of what the artifact
contains, including the places where building it changed the design. Read this
before trusting any claim in the design doc, because a few of them moved.

---

## 1. The theorem's actual statement

The design doc writes §7.3 as `|image(recover ∘ Crash(p))| ≤ 2`. What is proven
(`theorem::crash_consistency`) is the disjunction that bound is shorthand for:

```rust
forall|s2| is_crash_outcome(s0, p, s2)
    ==> recover(g, s2) =~= recover(g, s0)
     || recover(g, s2) =~= recover(g, denote(s0, p))
```

Two deliberate differences.

**No cardinality.** vstd's `Set` is finite-only in this release, and counting the
image would drag finiteness obligations through every lemma to establish something
no consumer needs. The disjunction is the form rungs 2–5 will actually use.

**`recover(denote(…))`, not `denote(…)`.** The design doc's prose says a crash
recovers to "state N+1". The store after a successful commit still *physically
contains* the previous checkpoint in the other slot — that is what ping-pong means.
It is the recovered view that equals the new checkpoint, not the raw store.
`concrete::the_two_states_are_distinct` pins this down: the two states really are
different, so the theorem is not satisfied vacuously by two names for one state.

---

## 2. The bridge lemma nearly was vacuous

§3.1 flags vacuity as the headline risk and locates it in the cell model. It was
also lurking one level up, in §4.3.

vstd's `Map::union_prefer_right` is exactly `◁`. The obvious way to define `•` is
the same function guarded by `disjoint` — at which point the bridge lemma
`disjoint(δ₁,δ₂) ⟹ δ₁ ◁ δ₂ = δ₁ • δ₂` is *reflexivity*. It verifies instantly and
establishes nothing, and §4.4, §6.1 and §7.2 all lean on `•` carrying weight.

So in `algebra.rs`, **`◁` prefers the right operand and `•` prefers the left one.**
The bridge lemma then states precisely what it should: the bias is unobservable
exactly when the domains are disjoint.

The guard rail is `algebra::dunion_comm`. It must not verify with its `disjoint`
precondition deleted. Checked during development: without it, the proof fails. If a
future refactor makes that lemma pass unconditionally, `•` has collapsed back into
`◁` and the algebra is decoration again.

---

## 3. The lattice is proven as a bijection, not a count

§6.2 says the sub-deltas of an epoch are isomorphic to `𝒫(dom e)`, "`2^|dom e|`
points total". What `crash.rs` proves is the isomorphism —
`sub_delta_is_restriction` and `restriction_is_sub_delta` — not the cardinality.

The cardinality is never used. What §7.2 actually needs is the *singleton* case, and
that is proven directly and exactly: `crash::singleton_lattice` shows a one-cell
epoch admits precisely `⊥` and `⊤`. That single lemma is what A1 and A4 buy, and
everything in §7.2 is downstream of it.

`concrete.rs` supplies the counting separately and concretely, by enumerating all
`2² + 2 = 6` points of a real two-cell commit.

---

## 4. Where the falsifiability gate actually fires

§7.3 says "if the proof still verifies with the barrier removed, the model is
vacuous." Which proof breaks is more specific than the doc suggests, and the
difference matters for anyone maintaining the gate.

Verus checks each function against its own signature. `crash_consistency` takes
`commit_shape` as a *hypothesis*, so it keeps verifying with the barrier removed —
correctly, because it says nothing about programs that lack the shape. What breaks
is `commit::commit_establishes_shape`: the lemma asserting that the program the
protocol *emits* has that shape. Without a barrier it emits one epoch, not two.

`scripts/gate.sh` therefore requires three things, not one: that verification fails,
that it fails on `commit_establishes_shape`, and that it fails as a **postcondition**
failure rather than a compile error. A negative test that passes because the crate
did not build is worse than no gate.

Note also that well-formedness (`wf`) still holds without the barrier — a payload
with distinct keys plus a seal outside the payload region is a perfectly legal
program. The barrier is not what makes the program well-formed; it is what makes it
*two epochs*. Anyone tempted to strengthen `wf` to catch this is fixing the wrong
thing.

---

## 5. A1: given a formal home, and a price

§6.3 asks for a refinement layer in which "A1 is exactly the assumption that `tear`
is trivial". `refine.rs` delivers a sharper pair of statements:

- `bytewise_tear_violates_a1` — under byte-level tearing, **A1 is false** for any
  cell wider than one byte. Explicit witness: writing `01 01` over `00 00` can leave
  `00 01`. So A1 has real content; the model is not assuming it away.
- `atomic_unit_tear_is_trivial` — A1 holds exactly when the cell *is* the hardware's
  atomic write unit. "Size cells to the atomic width" is a precondition of the
  theorem, not a tuning tip.
- `abstract_model_assumes_a1` — the abstract crash lattice offers each cell exactly
  two outcomes. Combined with the first point: **if A1 is false, the abstract model
  is unsound, not merely imprecise.**

**Deferred, explicitly:** the full simulation argument that the byte-level model
refines the abstract one under A1, across whole multi-cell programs. That is a body
of work comparable in size to the rest of the crate. §10.1 permits deferring it
provided the deferral is recorded rather than silent; this section and the module
docs in `refine.rs` are that record.

---

## 6. The CRC is inert, and enforced to stay that way

Per §5.1 the CRC is a probabilistic backstop, outside the proven core.
`CellVal::Seal` carries a `crc` field and **no specification or proof reads it**.
`recover` does not validate it. This is deliberate: under A1 + A2 the protocol is
correct without a checksum, and any proof that started leaning on `crc` would
silently convert a proven result into a probabilistic one.

If you need the CRC to be load-bearing, that is a different theorem with a stated
collision probability, and it does not belong in this crate.

---

## 7. Modelling choices worth knowing

**Crash outcomes are a predicate, not a `Set`.** vstd's `Set` is finite-only
(`Set::new` returns `Option`). Every consumer wants "for all crash outcomes …",
which `is_crash_outcome` gives directly.

**`V` is generic through §4 and §6, concrete in §7.** The algebra and crash model
never look inside a cell. `recover` must, because it reads a generation number, so
`protocol.rs` instantiates `CellVal`.

**Slot geometry is a parameter, not a constant.** `Geom` is threaded explicitly
rather than fixed as globals, and `slots_wf` states the non-overlap conditions —
§7.5's rule 2 in geometric form.

**`generation`, not `gen`.** `gen` is a reserved keyword in Rust edition 2024.

---

## 8. What the reference implementation adds

`crates/highlander-ref` is a second, independent expression of the protocol in
ordinary Rust. It has **no dependency on `highlander-model`** — a reference
implementation sharing code with the specification it cross-checks would be
worthless.

Its property tests brute-force the entire crash lattice rather than sampling it.
The negative test is the useful one: without a barrier, **63 of 128** landing
schedules recover to a state that is neither checkpoint. The barrier is not a
performance knob.

---

## 9. What is *not* proven

- Anything about rungs 2–5. No COW, no registers, no page tables, no resume.
- The I/O boundary (§8). The outside world still does not roll back.
- A3 (generation counter never wraps). Stated, assumed, free at 64 bits, unused.
- Liveness of any kind. The theorem says a crash recovers to one of two consistent
  states; it says nothing about progress, and a protocol that never commits
  satisfies it.
- That the *implementation* issues the barrier the model assumes. A2 is a promise
  about hardware and a promise about the eventual driver. This crate cannot check
  either.
