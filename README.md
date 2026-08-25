# highlander

> the kernel that does not die

Highlander is an orthogonally persistent kernel. The kernel writes the full state of
the machine to stable storage as one atomic transaction. The full state includes
each process, each register, and each page. There is no file system, no save
command, and no serialization step. After a crash, the machine continues from the
middle of an instruction. The machine does not do a reboot.

A process does no work to become persistent. A process is persistent because it
exists.

This repository contains rung 1 of the project: the verified checkpoint storage
model. A checkpoint tears if it holds a mixture of the old data and the new data.
If a checkpoint can tear, all layers above the checkpoint layer have no value. Thus
the crash consistency theorem is the first task. Rung 1 needs no hardware. Rung 1 is
a verified checkpoint journal, even if no person builds rungs 2 to 5.

## The result

```
Crash consistency of the full machine reduces to two hardware promises.
A probabilistic test gives protection if the hardware does not keep them.
```

| | |
|---|---|
| **A1** | A write to one cell lands fully, or the write does not land. |
| **A2** | All writes before a barrier land before all writes after the barrier. |
| **A4** | The seal is in one cell only. |

The store has `N` checkpoint slots, and `N` is 2 or more. A commit writes to a slot
that is not live, thus each other checkpoint survives the commit
(`commit::a_commit_destroys_only_its_target`). With 2 slots, a machine that writes a
checkpoint of its own corrupt state has 1 commit in which to observe the fault. With
`N` slots it has `N - 1`.

If A1, A2 and A4 are true, then each possible crash during a commit gives one of two
results. The result is the old checkpoint or the new checkpoint. No result is a
mixture of the two, and no other result is possible. Verus does a machine check of
this theorem. See `theorem::crash_consistency`.

The proof also covers a checkpoint that runs while the machine runs. Rung 2 uses
copy-on-write. At the start of a checkpoint the machine keeps a copy of the old
contents of each page that it writes. `checkpoint::concurrent_checkpoint_is_exact`
shows the result: for any order of the writes by the machine and the reads by the
checkpoint writer, the stored checkpoint is the memory of the machine at the instant
the checkpoint started. The machine does not stop.

Rung 3 captures the state of a machine: the registers, the memory and the page
tables. `machine::capture_restore_roundtrip` shows that the capture loses nothing.
`checkpoint::a_machine_survives_a_crash` joins rung 1 and rung 3: capture a machine,
commit it, crash at any point, recover and restore, and the machine that comes back
is the machine that went in.

A page table is data in cells, thus the capture treats it as data. The capture uses
physical cells and never translates an address. The other method needs the page
tables in order to read the page tables, and that circle has no start.

The proof also shows that a commit keeps its data. Crash consistency is a safety
property: it says that a crash never shows a torn state. A checkpoint that holds
nothing also obeys that property. Thus `commit::commit_is_durable` states the other
half: after a commit, the recovered store holds each cell that the commit wrote,
with the value that the commit wrote.

The proof covers a sequence of commits, and not one commit only. A machine does
many commits. Each commit writes to the other slot and increases the generation by
1. `sequence::run_is_crash_consistent` shows that each commit in the sequence is
crash consistent, and that the state after each commit obeys the same conditions
again. `protocol::steady` gives those conditions.

The CRC is not a part of this argument (design doc, §5.1). The CRC gives more
protection if A1 or A2 are not true. But the CRC guarantee is probabilistic. Thus
the CRC stays outside the proof.

## Layout

| Path | Contents |
|---|---|
| `crates/highlander-model` | the verified model: algebra, crash lattice, protocol, theorem |
| `crates/highlander-ref` | an independent reference implementation and its property tests |
| `docs/design/0001-…` | the design doc: intent, axioms, the rungs |
| `docs/design/0002-…` | the proof as built, and where the work changed the design |
| `docs/adr/0001-…` | why the protocol uses two slots and not an append-only log |

In `highlander-model`, each module uses only the modules above it in this table.

| Module | Doc section | Generic in `V` |
|---|---|---|
| `algebra`  | §4 — override `◁`, disjoint union `•`, the bridge lemma | yes |
| `crash`    | §6 — programs, epochs, the crash lattice | yes |
| `protocol` | §7 — two checkpoint slots, seals, `recover` | no |
| `theorem`  | §7.3 — the crash consistency theorem | no |
| `commit`   | §7.1 — the commit program, and the falsifiability gate | no |
| `concrete` | §10.1 — a machine of 6 cells, with a test of each lattice point | no |
| `sequence` | a run of many commits, and the invariant it keeps | no |
| `cow`      | rung 2 — copy-on-write, and the snapshot it keeps | yes |
| `machine`  | rung 3 — registers, memory, and a capture that loses nothing | no |
| `process`  | rung 4 — a resume, and what the world sees across a crash | no |
| `io`       | rung 5 — the I/O boundary, and how it absorbs a repeat | no |
| `checkpoint` | rungs 1, 2 and 3 together | no |
| `refine`   | §6.3 — A1, and the proof that the model matches a real device | no |

## How to build

A standard Rust toolchain is enough for all targets except `make verify` and
`make gate`. Those two targets need Verus.

```
make test     # property tests against the reference implementation
make check    # cargo build and clippy: the model is also usual Rust 2024
make verify   # the proof                       (Verus necessary)
make gate     # the falsifiability gate         (Verus necessary)
make          # all four targets
```

### How to install Verus

The `vstd` version in `Cargo.toml` and the `verus` program must agree. `make verify`
stops if they do not agree.

1. Download the release with `curl`:

   ```sh
   curl -L -o verus.zip \
     https://github.com/verus-lang/verus/releases/latest/download/verus-<version>-arm64-macos.zip
   ```

2. Extract the archive:

   ```sh
   unzip verus.zip
   ```

3. Move the directory to its permanent location:

   ```sh
   mv verus-arm64-macos ~/.local/share/verus
   ```

4. Make the symbolic links:

   ```sh
   ln -sf ~/.local/share/verus/verus       ~/.local/bin/verus
   ln -sf ~/.local/share/verus/cargo-verus ~/.local/bin/cargo-verus
   ```

Symbolic links in a directory that is already in `PATH` are better than a change to
your shell profile. Verus finds its `verus-root` file through a symbolic link
correctly. Verus also needs `rustup` in `PATH`, because Verus starts the pinned
toolchain itself. A usual rustup installation does this for you.

Use `curl` and do not use a browser. A browser sets the `com.apple.quarantine`
attribute on the file, but `curl` does not set it. If you use a browser, remove the
attribute:

```sh
xattr -dr com.apple.quarantine ~/.local/share/verus
```

Do not use the `macos_allow_gatekeeper.sh` file in the release. Line 5 of that file
contains `${{BASH_SOURCE[0]}}`. The two brace characters are an error, and the
script stops with the message `bad substitution`.

Verus pins rustc 1.97.1. The file `rust-toolchain.toml` pins the same version. If
you change one version, change the other version also.

## The gates

A crash model can be correct in itself and show nothing about a real machine. Three
gates prevent this condition.

**`make gate` runs 7 negative tests. Each one must fail.**

| Feature | Lemma that must fail | Property it protects |
|---|---|---|
| `no-barrier` | `commit_establishes_shape` | A2 gives 2 epochs, and not 1 |
| `degenerate-recover` | `commit_is_durable` | a checkpoint keeps its data |
| `no-cow-copy` | `copy_preserves_visible` | the snapshot holds still |
| `overlapping-layout` | `capture_preserves_memory_at` | a capture loses nothing |
| `ignore-input-journal` | `replay_follows_the_same_trajectory` | a replay needs its inputs |
| `no-output-dedup` | `a_stale_event_is_dropped` | the boundary absorbs a repeat |
| `multi-byte-cells` | `an_atomic_cell_lands_whole` | A1: a cell lands whole |

Without A2, the payload epoch and the seal epoch become 1 epoch. In that epoch this
crash result is possible: the seal lands, but the payload does not land. This result
is not generation N, and it is not generation N+1.

The second gate replaces `recover` with a version that keeps the seal and discards
each payload cell. That version obeys each crash consistency lemma, because a store
that holds nothing can never tear. Durability rejects it.

The third gate removes the copy from copy-on-write. The snapshot then follows the
machine, and a page that the machine writes during a checkpoint enters the
checkpoint at its new contents. The result mixes 2 instants of the machine.

The fourth gate lets the register file and memory share a cell. One of them writes
over the other, and the capture loses state with no indication of a fault.

Each gate also tests the cause of the failure. The failure must occur at the named
lemma, and it must be a postcondition failure and not a compile error. A negative
test that passes because the crate did not compile gives no information.

**`make test` — the reference implementation must find the same faults.** The tests
examine each point of the crash lattice, and they do not use samples. Without the
barrier, 63 of 128 landing schedules cause damage to the store. A separate test
shows that a forgetful `recover` passes the full lattice and still loses each
committed cell. A third test shows that the snapshot moves away from the start state
if the copy is absent.

## The ladder

| Rung | Deliverable | Status |
|---|---|---|
| **1** | verified checkpoint commit and recover, on the abstract cell model | ✅ |
| **2** | **copy-on-write page records, to prevent a stop of the full machine** | ✅ |
| **3** | **capture of the true machine state (registers, page tables)** | ✅ |
| **4** | **continuation of one simple process after a hard reset** | ✅ |
| **5** | **I/O journal at the boundary** | ✅ |

Each rung has value alone.

Rung 4 starts the machine again. `process::replay_follows_the_same_trajectory`
shows that a crash costs work and changes nothing else: given the same inputs, the
machine passes through the states it passed through before. A step takes a machine
**and an input**, thus the model shows that a replay needs the inputs that arrived
before. That is the obligation of rung 5.

`process::a_crash_repeats_the_events_since_the_checkpoint` states §8 exactly. A
crash does not disturb the world at random. The world receives one specific sequence
a second time: the events that the machine emitted after its last checkpoint.

Rung 5 closes the boundary. The external world does not go back to an earlier
state: the machine checkpoints at N+1, crashes, starts again at N, but the packet
went out and the DMA transfer completed. Rung 4 shows the world receives one
specific sequence a second time, and rung 5 removes it.

* **Output.** Each event carries a tag that increases. The boundary keeps the
  largest tag it accepted, and drops each event at or below it.
  `io::a_repeated_window_is_delivered_once` shows the world receives the same
  effects, with a crash or without one. A TCP sequence number does this, and so does
  an idempotency key in a durable workflow engine.
* **Input.** An input arrives from outside, thus the capture does not hold it. A
  journal records the inputs since the last checkpoint, and a replay reads them.
  `io::a_sound_journal_discharges_same_inputs` connects the journal to the condition
  that rung 4 needs. The journal is cells, thus rung 1 makes it crash consistent
  with no new mechanism and no new axiom.

## Background

KeyKOS and EROS. KeyKOS operated production banking workloads.

This project does not use the x86 paging method. That method gets protection from
the hardware: the MMU, the rings and the page tables. A formal proof cannot easily
reach that hardware. In highlander, the proof gives protection and consistency. Thus
Verus does necessary work in this project.
