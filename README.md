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

If A1, A2 and A4 are true, then each possible crash during a commit gives one of two
results. The result is the old checkpoint or the new checkpoint. No result is a
mixture of the two, and no other result is possible. Verus does a machine check of
this theorem. See `theorem::crash_consistency`.

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
| `refine`   | §6.3 — the formal position of A1, and its cost | no |

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

## The two gates

A crash model can be correct in itself and show nothing about a real machine. Two
gates prevent this condition.

**`make gate` — if you remove the barrier, the proof must fail.** Without A2, the
payload epoch and the seal epoch become one epoch. In that epoch, this crash result is
possible: the seal lands, but the payload does not land. This result is not
generation N, and it is not generation N+1. The gate also tests the cause of the failure. The failure must occur at
`commit_establishes_shape`, and the failure must be a postcondition failure and not
a compile error. A negative test that passes because the crate did not compile gives
no information.

**`make test` — the reference implementation must find the same fault.** The tests
examine each point of the crash lattice, and they do not use samples. Without the
barrier, 63 of 128 landing schedules cause damage to the store.

## The ladder

| Rung | Deliverable | Status |
|---|---|---|
| **1** | verified checkpoint commit and recover, on the abstract cell model | ✅ |
| 2 | copy-on-write page records, to prevent a stop of the full machine | — |
| 3 | capture of the true machine state (registers, page tables) | — |
| 4 | continuation of one simple process after a hard reset | — |
| 5 | I/O journal at the boundary | — |

Rungs 2 to 5 are optional. You can use rung 1 alone.

**Known limitation:** the external world does not go back to an earlier state. The
machine makes a checkpoint at generation N+1, then the machine crashes, then the
machine starts again at generation N. But the network packet went out, and the DMA
transfer completed. Orthogonal persistence is fully orthogonal only inside the
machine. See §8 of the design doc.

## Background

KeyKOS and EROS. KeyKOS operated production banking workloads.

This project does not use the x86 paging method. That method gets protection from
the hardware: the MMU, the rings and the page tables. A formal proof cannot easily
reach that hardware. In highlander, the proof gives protection and consistency. Thus
Verus does necessary work in this project.
