# highlander

> the kernel that doesn't die

An orthogonally persistent kernel: the machine checkpoints its *entire* state —
every process, every register, every page — to stable storage as an atomic
transaction. No filesystem, no `save`, no serialization step. A crash resumes
mid-instruction rather than rebooting.

Persistence stops being something a process *does* and becomes a property of
*existing*.

**This repository currently contains rung 1: the verified checkpoint storage
model.** Everything above the checkpoint layer is meaningless if the checkpoint can
tear, so the crash-consistency theorem comes first. It is self-contained, needs no
hardware, and stands on its own as a verified checkpoint journal even if rungs 2–5
are never built.

## The result

```
Crash consistency of the whole machine reduces to two stated hardware promises,
with a probabilistic backstop for when they are broken.
```

| | |
|---|---|
| **A1** | a single cell write lands entirely or not at all |
| **A2** | writes issued before a barrier land before any issued after |
| **A4** | the seal fits in exactly one cell |

Given those, every possible crash during a commit recovers to exactly one of two
states — the old checkpoint or the new one. Never a blend, never anything else.
`theorem::crash_consistency`, machine-checked by [Verus](https://github.com/verus-lang/verus).

The CRC is **not** part of that argument (§5.1). It is defence-in-depth for when A1
or A2 turn out to be false, its guarantee is probabilistic, and it is deliberately
quarantined outside the proven core.

## Layout

| Path | What |
|---|---|
| `crates/highlander-model` | the verified model — algebra, crash lattice, protocol, theorem |
| `crates/highlander-ref` | an **independent** executable reference implementation + property tests |
| `docs/design/0001-…` | the design doc: intent, axioms, the ladder |
| `docs/design/0002-…` | **what was actually proven**, including where building it changed the design |
| `docs/adr/0001-…` | why ping-pong slots rather than an append-only log |

Inside `highlander-model`, each module depends only on the ones above it:

| Module | Doc section | Generic over `V`? |
|---|---|---|
| `algebra`  | §4 — override `◁`, disjoint union `•`, the bridge lemma | yes |
| `crash`    | §6 — programs, epochs, the crash lattice | yes |
| `protocol` | §7 — ping-pong slots, seals, `recover` | no |
| `theorem`  | §7.3 — the crash-consistency theorem | no |
| `commit`   | §7.1 — the emitted program, and the falsifiability gate | no |
| `concrete` | §10.1 — a real six-cell machine, every lattice point checked | no |
| `refine`   | §6.3 — where A1 lives formally, and what it costs | no |

## Building

Everything except `make verify` and `make gate` works with a stock Rust toolchain.

```
make test     # property tests against the reference implementation
make check    # cargo build + clippy — the model is ordinary Rust 2024 too
make verify   # the proof                     (needs verus)
make gate     # the falsifiability gate       (needs verus)
make          # all four
```

### Getting Verus

The pinned `vstd` version in `Cargo.toml` must match the `verus` binary; `make
verify` refuses to run if they disagree.

```sh
curl -L -o verus.zip \
  https://github.com/verus-lang/verus/releases/latest/download/verus-<version>-arm64-macos.zip
unzip verus.zip
export PATH="$PWD/verus-arm64-macos:$PATH"
```

Use `curl`, not a browser: curl does not set `com.apple.quarantine`, so Gatekeeper
stays out of the way. If you already downloaded via a browser, run `xattr -dr
com.apple.quarantine <dir>` — **do not** run the bundled `macos_allow_gatekeeper.sh`,
which has a `${{BASH_SOURCE[0]}}` typo and fails with "bad substitution".

Verus pins rustc **1.97.1**, which is also what `rust-toolchain.toml` pins. Keep
them together.

## The two gates that make this worth anything

A crash model this elaborate can be internally consistent and describe nothing.
Two checks exist to catch that:

**`make gate` — remove the barrier, and the proof must break.** Without A2 the
payload and seal merge into one epoch, admitting the point *"seal landed, payload
didn't"* — a state that recovers to neither generation. The gate additionally
requires that the failure lands on `commit_establishes_shape` and is a
*postcondition* failure rather than a compile error, because a negative test that
passes because the crate didn't build is worse than no gate.

**`make test` — the reference implementation must find the same bug.** It
brute-forces the whole crash lattice rather than sampling it, and reports that
without a barrier **63 of 128** landing schedules corrupt the store.

## The ladder

| Rung | Deliverable | Status |
|---|---|---|
| **1** | verified checkpoint commit/recover over the abstract cell model | ✅ |
| 2 | COW page tracking, so a checkpoint doesn't stop the world | — |
| 3 | capture real machine state (registers, page tables) into a checkpoint | — |
| 4 | resume a single trivial process across a hard reset | — |
| 5 | I/O journaling at the boundary | — |

Rungs 2–5 are explicitly optional. Rung 1 is useful in isolation.

**Known limitation:** the outside world does not roll back. Checkpoint at N+1,
crash, resume from N — but the packet was sent and the DMA landed. Orthogonal
persistence is only truly orthogonal *inside* the machine. See §8 of the design doc.

## Lineage

KeyKOS (which ran production banking workloads) and EROS. Deliberately **not** the
x86-paging path — that derives protection from hardware (MMU, rings, page tables),
which is largely unreachable by formal proof. Here protection and consistency derive
from *proof*, which is what makes Verus load-bearing rather than decorative.
