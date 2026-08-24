# highlander — working notes

An orthogonally persistent kernel. This repository currently holds **rung 1**: a
Verus-verified checkpoint storage model. See `README.md` for the result and
`docs/design/0002-what-was-proven.md` for what the proof does and does not cover.

## Documentation style: Simplified Technical English

**All documentation in this repository uses ASD-STE100 Simplified Technical
English.** Write new documentation in STE, and keep edits to existing documentation
in STE.

### Scope

| STE now | Exempt |
|---|---|
| `README.md` | Rust doc comments (`//!`, `///`) |
| `CLAUDE.md` (this file) | code comments (`//`) |
| each new Markdown document | commit messages |
| | `scripts/*.sh` comments |

Rust doc comments are exempt on purpose. They carry the reasoning behind the
proof — why `•` is left-biased, why the CRC stays inert, why the gate targets
`commit_establishes_shape`. STE removes the constructions that this reasoning needs.
If you want STE in the doc comments also, that is a deliberate change to make, and
not a default.

**Not yet converted.** These files use ordinary English:

| File | Why |
|---|---|
| `docs/design/0001-checkpoint-storage-model.md` | the author's text, kept word for word |
| `docs/design/0002-what-was-proven.md` | explains the reasons behind design changes |
| `docs/adr/0001-ping-pong-vs-log.md` | records a decision and its trade-offs |

A conversion of these 3 files is an open decision. Do not convert
`0001-checkpoint-storage-model.md` without permission from the author, because a
conversion changes the author's own words.

### Rules that matter most here

1. Write short sentences. 25 words maximum for description, 20 for a procedure.
2. Write one instruction per sentence. Use a numbered list for a procedure.
3. Use the active voice. Name the actor.
4. Use simple tenses: present, past, future. Do not use perfect or progressive forms.
5. Do not use an `-ing` form as a noun or an adjective, unless it is a technical name.
6. Keep a paragraph to 6 sentences maximum. Keep one topic in one paragraph.
7. Use articles. Write "the barrier", not "barrier".
8. Do not use more than 3 nouns together.
9. Use the same word for the same thing every time. Do not use synonyms for variety.
10. Do not use idiom, metaphor, slang or humour.
11. Write "do not", not "don't".
12. Write numbers as numerals.

### Word substitutions

| Do not write | Write |
|---|---|
| ensure, verify | make sure, check |
| utilize, leverage | use |
| prior to | before |
| subsequent to | after |
| in order to | to |
| due to the fact that | because |
| approximately | about |
| sufficient | enough |
| additional | more |
| multiple, numerous | many |
| commence, initiate | start |
| terminate | stop, end |
| perform, accomplish | do |
| obtain | get |
| provide | give, supply |
| indicate | show |
| require | need, must |
| attempt | try |
| assist | help |
| via | with, by, through |
| however | but |
| e.g. | for example |
| i.e. | that is |
| etc. | (do not use — list the items) |

### Technical names to keep

STE allows the technical names and technical verbs that a subject needs. These are
approved for this repository, and you must not replace them with plainer words:

> barrier, cell, checkpoint, commit, crash, delta, epoch, generation, lattice,
> payload, recover, seal, slot, store, tear, crate, lemma, postcondition, spec

Define a technical term the first time a document uses it. `README.md` defines
"tear" this way, because that word names the exact failure the theorem excludes.

### Before you commit documentation

Read the text again and check three things:

1. Each sentence is inside the word limit.
2. No sentence contains an idiom or a metaphor.
3. The same idea uses the same word everywhere in the document.

## Proof work

Two invariants hold this development together. Do not break either one silently.

- **`algebra::dunion_comm` must fail to verify if you remove its `disjoint`
  precondition.** `•` is left-biased and `◁` is right-biased on purpose. If both
  become `union_prefer_right`, the bridge lemma becomes reflexivity, and the algebra
  proves nothing.
- **`scripts/gate.sh` must fail with `--features no-barrier`.** The failure must
  occur at `commit_establishes_shape`, and it must be a postcondition failure.
- **Do not put `clean` back into a commit precondition.** `clean` holds only for a
  new store. A commit leaves the older checkpoint in the other slot, thus a store is
  never clean again. Use `protocol::steady`. See `docs/design/0002` §5a.

Run `make` before you commit. It runs the proof, the gate, the property tests and
clippy.
