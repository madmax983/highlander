# highlander

> the kernel that does not die

```
                                                                                        .-+++=:::...
                                                                                       .+**+++**##+.
                                                                                     ..+++===#=*#**.
                                                                                    ..+++=-=+=*#%#*-
                                                                                   ..++=----+#%%%#*=
   THERE                                                                          ...++=---##%%%%###-
   CAN                                                                           .:*+=-:*#%%#****+:.
   BE                                                                         ..+#*==-+%%%****=..   
   ONLY                                                                     ..=######+%@%***:..      
   ONE                                                                     ..=####%%%%%%#*+..         
                                                                       ..-*#*#%%%%%%%%%+.           
                                                                     ..=######*#%%%%%%*.            
                                                                   ..-*##%##%%%%%#%%%-              
                                                                 ..-*###*###%%%%%%%#..              
                                                               ..-*#######*%%%%%%%=.                
                                                              ..+*######%%%%%%%%*.                  
                                                            .:*######%%%%%%%%%#:                    
                                                           .+######%#%#%%%%%%+.                     
                                                        ..-*#*####%%%%%%%%%#.                       
                  .=+.                                 .-####%###%%%%%%%%#:.                        
                .==**:                               ..+########%##%%%%%-.                          
             ..+====*-.                            ..*#####%#%%%%%%%#%=.                            
           .:+=-=====++..                        ..-*####%##%%%%%%%%+..                             
          .+**=======-=*=..                    ...+*###%%%%%%*%%%%#..                               
              ..+-====--=*-.                   .**####*%%%%%%%%%%-..                                
                .:+=-=====+*:.               .-######%%%##%%%%%+..                                  
                  .-=====-==+*..            .*+##%#%%%%%%%%%%#..                                    
                    .-===-=====*..       ..*###%##%%%%%%%%%#..                                      
                      .=---==---=*..    .+####%%%%%*%%%%%#..                                        
                      ...===--==--+=.  :*###%%%%%%%%%%%#:.                                          
                        .=====--=---+:**=-=%%%%%%%%%%#:.                                            
                       .-=======--=--=#=---:+%%#%%%#:...                                            
                       .=====--=-=-=-:-==-:+#%%%%#:.                                                
                       .=-====---=----==-=#%%%*#:.                                                  
                       .=-=====--:----=----*%%-.                                                    
                     ..----=--------:--+--:--#+.                                                    
                   ..-:::=:-=-==-:----=-==--:-=*-.                                                  
                  .:-::::---:======-:-:-=-=-=---+*..                                                
                ..-:::::::-=---====-=====-=--=---+*+..                                              
              ..-:::::::::::+=-:-==-========-:-+#==+*+.                                             
            ..-:::::::::::::::+=-:-==----==--+*====-=++-.                                           
           ..-:::::::::::::::::::=+======+*+*====-----=++...                                        
          .=:::::::::::::::::::::::-+:::........+-=-----=*+.                                        
        .-::::::::::::::::::::::::=:            .:=-------=*=.                                      
      .:::::::::::::::::::::::::-:.               .-=----=-==+-....                                 
    ..-:::::::::::::::::::::::--.                   .===--===--=*-.                                 
  ..-:::::::::::::::::::::::-=.                       .+--+==-**:.                                  
 .-:::::::::::::::::::::::-=..                         .:=---#*..                                   
:-::::::..:::::::::::::::=.                             .--=*+..                                    
:::::::...:::::::::::::=..                               :**..                                      
::::::::::::::::::::-=:.                                 ...                                        
:::::::::::::::::-:=:.                                                                              
:::::::::::::::::=-..                                                                               
:::::::::::::::--..                                                                                 
::::::..:::::--..                                                                                   
```

Highlander is an orthogonally persistent kernel. The kernel writes the full state of
the machine to stable storage as one atomic transaction. The full state includes
each process, each register and each page. There is no file system, no save command
and no serialization step. After a crash, the machine continues from the middle of
an instruction. It does not do a reboot.

A process does no work to be persistent. A process is persistent because it exists.

This repository holds a model of that kernel, and a machine-checked proof about it.
**116 lemmas, 0 errors, 8 falsifiability gates, 18 property tests.** The proof uses
[Verus](https://github.com/verus-lang/verus).

---

## The result

```
The crash consistency of a full machine reduces to 3 hardware promises.
A probabilistic test gives protection if the hardware breaks them.
```

| | Promise |
|---|---|
| **A1** | A write to one cell lands fully, or the write does not land. |
| **A2** | All writes before a barrier land before all writes after the barrier. |
| **A4** | The seal is in one cell only. |

A checkpoint **tears** if it holds a mixture of the old data and the new data. Given
A1, A2 and A4, a checkpoint cannot tear. That is the first result, and each result
below stands on it.

The name is not only a joke. `protocol::at_most_one_live_slot` says that at most 1
checkpoint slot is live, and `replication::agreement` says that 1 generation has 1
checkpoint. A slot wins by holding the larger generation, and the loser stops being
the checkpoint. There can be only one.

A3 says the generation counter never wraps. It appears free, and it is not: each
comparison of 2 generations uses it, and a counter that wrapped would make recovery
select an older checkpoint. See §5a of `docs/design/0002-what-was-proven.md`.

### What the proof contains

| Result | Lemma | Rung |
|---|---|---|
| A crash during a commit recovers to the old checkpoint or the new one, and to nothing else | `theorem::crash_consistency` | 1 |
| A commit stores what it was given | `commit::commit_is_durable` | 1 |
| Each commit of an unbounded sequence is crash consistent | `sequence::run_is_crash_consistent` | 1 |
| Recovery is a closure operator, and it never writes | `protocol::recover_idempotent` | 1 |
| A commit changes 1 slot, thus each older checkpoint survives it | `commit::a_commit_destroys_only_its_target` | 1 |
| At most 1 slot is live — there can be only one | `protocol::at_most_one_live_slot` | 1 |
| A snapshot taken while the machine runs is the memory at the instant it started | `checkpoint::concurrent_checkpoint_is_exact` | 2 |
| A capture of a machine loses nothing | `machine::capture_restore_roundtrip` | 3 |
| A machine survives a crash: capture, commit, crash, recover, restore | `checkpoint::a_machine_survives_a_crash` | 3 |
| A capture cannot hold the machinery that makes it | `machine::no_layout_captures_itself` | 3 |
| A replay passes through the states it passed through before | `process::replay_follows_the_same_trajectory` | 4 |
| A crash repeats exactly the events since the last checkpoint | `process::a_crash_repeats_the_events_since_the_checkpoint` | 4 |
| The world receives the same effects, with a crash or without one | `io::a_repeated_window_is_delivered_once` | 5 |
| A journal of the inputs gives a replay what it needs | `io::a_sound_journal_discharges_same_inputs` | 5 |
| The abstract model contains the behaviour of a real device | `refine::physical_crash_is_an_abstract_crash` | — |
| Any 2 majorities of a cluster share a node | `replication::quorums_intersect` | 6 |
| 1 generation has 1 checkpoint | `replication::agreement` | 6 |
| A committed checkpoint reaches each later quorum | `replication::a_committed_checkpoint_reaches_every_quorum` | 6 |

### What the proof does not contain

- **Liveness, anywhere.** The proof says a crash recovers to a consistent state. It
  says nothing about progress, and a machine that does no commit obeys each theorem.
  For 1 machine that is a question of speed. For a cluster it is half the design: a
  partition stops progress for as long as it lasts. Rung 6 carries a `◐` for this.
- **A protocol for rung 6.** There is no election, no replication of a log and no
  change of membership. Rung 6 states the properties that a protocol must keep.
- **Any specific hardware.** There is no x86, no ARM, no MMU and no trap handler. A
  register is a name for a byte string, and a cell is a name for a byte string.
- **That an implementation issues the barrier the model assumes.** A2 is a promise
  about hardware and about a future driver. This crate cannot test either.

`docs/design/0002-what-was-proven.md` records this in full, and it records each
place where the work changed the design.

### The CRC does no work

The seal carries a CRC, and no spec and no proof reads it. With A1 and A2 the
protocol is correct without a checksum. The CRC gives more protection if A1 or A2 is
false, its guarantee is probabilistic, thus it stays outside the proof. A proof that
used the CRC would change a proven result into a probabilistic one.

---

## The gates

A model of this size can be internally consistent and describe nothing. Each gate
removes 1 thing the design says is essential, and requires the proof to notice.

**`make gate` runs 8 negative tests. Each one must fail to verify.**

| Feature | Lemma that must fail | What it protects |
|---|---|---|
| `no-barrier` | `commit_establishes_shape` | A2 gives 2 epochs, and not 1 |
| `degenerate-recover` | `commit_is_durable` | a checkpoint keeps its data |
| `no-cow-copy` | `copy_preserves_visible` | the snapshot holds still |
| `overlapping-layout` | `capture_preserves_memory_at` | a capture loses nothing |
| `ignore-input-journal` | `replay_follows_the_same_trajectory` | a replay needs its inputs |
| `no-output-dedup` | `a_stale_event_is_dropped` | the boundary absorbs a repeat |
| `multi-byte-cells` | `an_atomic_cell_lands_whole` | A1: a cell lands whole |
| `half-quorums` | `quorums_intersect` | 2 majorities share a node |

Each gate tests 3 conditions, and not 1: verification fails, the failure lands inside
the named lemma, and it is a proof failure and not a compile error. A negative test
that passes because the crate did not compile gives no information. The script finds
the position of each failure and reads the `pub proof fn` that encloses it, thus a
gate does not depend on the format of a message.

**`make test` — the reference implementation must find the same faults.**
`crates/highlander-ref` is a second implementation in usual Rust, with **no
dependency on the model**. An implementation that shared code with the specification
it checks would give no information. Its tests examine each point of the crash
lattice, and they do not use samples.

Some numbers those tests report:

- Without the barrier, **63 of 128** schedules for the writes damage the store.
- A `recover` that keeps the seal and discards the data passes **61 of 63** lemmas
  of the model at the time, and each crash consistency test. Only durability rejects
  it.
- With exactly half a cluster accepted as a quorum, a cluster of 4 nodes commits 2
  different checkpoints at 1 generation.

---

## Layout

| Path | Contents |
|---|---|
| `crates/highlander-model` | the model and the proof |
| `crates/highlander-ref` | an independent reference implementation, and its property tests |
| `docs/design/0001-…` | the design doc: intent, axioms, the ladder |
| `docs/design/0002-…` | **the proof as built**, and where the work changed the design |
| `docs/adr/0001-…` | why the protocol uses checkpoint slots and not an append-only log |

In `highlander-model`, each module uses only the modules above it in this table.

| Module | Subject | Generic in `V` |
|---|---|---|
| `algebra`  | override `◁`, disjoint union `•`, the bridge lemma | yes |
| `crash`    | programs, epochs, the crash lattice | yes |
| `protocol` | checkpoint slots, seals, `recover` | no |
| `theorem`  | the crash consistency theorem | no |
| `commit`   | the commit program, durability, the rollback window | no |
| `sequence` | a run of many commits, and the invariant it keeps | no |
| `cow`      | rung 2 — copy-on-write, and the snapshot it holds | yes |
| `machine`  | rung 3 — registers, memory, and a capture that loses nothing | no |
| `process`  | rung 4 — a resume, and what the world sees across a crash | no |
| `io`       | rung 5 — the I/O boundary, and how it absorbs a repeat | no |
| `checkpoint` | rungs 1, 2 and 3 together | no |
| `refine`   | A1, and the proof that the model matches a real device | no |
| `replication` | rung 6 — quorums, and what a cluster agrees | no |
| `concrete` | a machine of 6 cells, with a test of each lattice point | no |

---

## How to build

A standard Rust toolchain is enough for all targets except `make verify` and
`make gate`. Those 2 targets need Verus.

```
make test     # property tests against the reference implementation
make check    # cargo build and clippy: the model is also usual Rust 2024
make verify   # the proof                       (Verus necessary)
make gate     # the 8 falsifiability gates      (Verus necessary)
make          # all 4 targets
```

### How to install Verus

The `vstd` version in `Cargo.toml` and the `verus` program must agree. `make verify`
stops if they do not agree.

1. Download the release with `curl`:

   ```sh
   curl -L -o verus.zip \
     https://github.com/verus-lang/verus/releases/latest/download/verus-<version>-arm64-macos.zip
   ```

2. Extract it, and move it to a permanent position:

   ```sh
   unzip verus.zip
   mv verus-arm64-macos ~/.local/share/verus
   ```

3. Make the symbolic links:

   ```sh
   ln -sf ~/.local/share/verus/verus       ~/.local/bin/verus
   ln -sf ~/.local/share/verus/cargo-verus ~/.local/bin/cargo-verus
   ```

Symbolic links in a directory that is already in `PATH` are better than a change to
your shell profile, and Verus finds its `verus-root` file through a symbolic link
correctly. Verus also needs `rustup` in `PATH`, because Verus starts the pinned
toolchain itself. A usual rustup installation does this for you.

Use `curl` and do not use a browser. A browser sets the `com.apple.quarantine`
attribute, and `curl` does not. If you use a browser, run
`xattr -dr com.apple.quarantine ~/.local/share/verus`. Do not use the
`macos_allow_gatekeeper.sh` file in the release: line 5 contains
`${{BASH_SOURCE[0]}}`, the 2 brace characters are an error, and the script stops
with `bad substitution`.

Verus pins rustc 1.97.1, and `rust-toolchain.toml` pins the same version. If you
change one, change the other.

---

## The ladder

| Rung | Deliverable | Status |
|---|---|---|
| **1** | verified checkpoint commit and recover, on the abstract cell model | ✅ |
| **2** | copy-on-write page records, to prevent a stop of the full machine | ✅ |
| **3** | capture of the true machine state (registers, page tables) | ✅ |
| **4** | continuation of 1 simple process after a hard reset | ✅ |
| **5** | an I/O journal at the boundary | ✅ |
| **6** | replication across machines | ◐ safety proven, liveness not attempted |

Rungs 1 to 5 are complete, and each has value alone.

**Rung 6 is different.** Each rung below it rests on a promise about 1 device: A1
and A2 describe the behaviour of a single store when power fails. A partition is not
a fault that those axioms describe, thus rung 6 replaces the failure model. It is
also the first rung that is unfinished, because its liveness half is not attempted.

On 1 device, `live` is a function of the store, and 1 reader examines each slot.
Across a cluster no node sees each replica, and no node can separate a peer that is
slow from a peer that is gone. Thus the identity of the live checkpoint stops being
a lookup, and becomes a question that a group answers together. One fact gives the
answer: any 2 majorities of a set share a member.

---

## Background

KeyKOS and EROS. KeyKOS operated production banking workloads.

This project does not use the x86 paging method. That method gets protection from
the hardware: the MMU, the rings and the page tables. A formal proof cannot easily
reach that hardware. In highlander the proof gives protection and consistency. Thus
Verus does necessary work in this project.
