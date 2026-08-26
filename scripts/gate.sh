#!/usr/bin/env bash
# Falsifiability gates: break a load-bearing part of the design, and the proof MUST
# break with it.
#
# A model this size can be internally consistent and describe nothing. Each gate
# removes one thing the design claims is essential and requires the proof to notice.
# A gate that passes because the crate failed to compile is worse than no gate at
# all, so each case checks three conditions, not one:
#
#   1. verification fails,
#   2. the failure lands inside the named lemma,
#   3. it is a *proof* failure, not a compile error.
#
# Condition 2 is resolved by source position rather than by matching the lemma name
# in the output. Verus reports a failure at the offending line, and its context does
# not always reach back far enough to include the signature, so a name match gives
# false negatives on any lemma with a multi-line signature.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

status=0

# Which `pub proof fn` encloses <file>:<line>.
enclosing_fn() {
  awk -v target="$2" '
    NR <= target && /pub proof fn / {
      line = $0
      sub(/.*pub proof fn /, "", line)
      sub(/[(<].*/, "", line)
      name = line
    }
    END { print name }
  ' "$1"
}

# gate <feature> <module> <lemma> <why it matters>
#
# Uses `cargo verus focus --verify-module`, which checks only the module holding the
# target lemma. That is roughly 17 proofs rather than 119, and it makes the check
# tighter rather than looser: the gate asserts that THIS lemma breaks, and whether
# anything else also breaks is not what it tests. `make verify` covers the crate.
gate() {
  local feature="$1" module="$2" lemma="$3" why="$4"
  echo
  echo "── gate: --features $feature  (module $module)"
  echo "   $why"

  local out rc
  out=$(cargo verus focus -p highlander-model --features "$feature" \
        -- --verify-module "$module" 2>&1)
  rc=$?

  fail() {
    echo "   GATE FAILED: $1" >&2
    echo "$out" | tail -30 >&2
    status=1
  }

  if [ $rc -eq 0 ]; then
    fail "verification SUCCEEDED with '$feature' enabled.
   The property this gate protects is not actually being proven. Nothing built
   on it means anything until that is fixed."
    return
  fi

  if echo "$out" | grep -qE 'E0[0-9]{3}|cannot find|unresolved import'; then
    fail "the build broke for the wrong reason — this is a compile error, not a
   proof failure, so the gate is not testing what it claims to test."
    return
  fi

  if ! echo "$out" | grep -qE '^error: (postcondition|precondition|assertion|invariant)'; then
    fail "verification failed, but not with a proof obligation. Expected a
   postcondition, precondition, assertion or invariant failure."
    return
  fi

  # Every source position Verus complained about, mapped to its enclosing lemma.
  local hit=0 seen=""
  while read -r loc; do
    [ -z "$loc" ] && continue
    local file="${loc%%:*}" line="${loc##*:}"
    [ -f "$file" ] || continue
    local fn
    fn=$(enclosing_fn "$file" "$line")
    [ -n "$fn" ] && seen="$seen $fn"
    [ "$fn" = "$lemma" ] && hit=1
  done <<< "$(echo "$out" | grep -oE '[A-Za-z0-9_/.-]+\.rs:[0-9]+' | sort -u)"

  if [ $hit -eq 0 ]; then
    fail "verification failed, but not inside '$lemma'.
   Failures landed in:$seen"
    return
  fi

  echo "   passed: '$lemma' fails to verify, as required."
  echo "$out" | grep -E 'verification results' | sed 's/^/   /' || true
}

gate no-barrier commit commit_establishes_shape \
  "Without A2 the payload and seal merge into one epoch, which admits the
   outcome 'seal landed, payload did not'. That recovers to neither generation."

gate degenerate-recover commit commit_is_durable \
  "A checkpoint that forgets everything never tears, so it satisfies every
   crash-consistency lemma. Only durability rejects it."

gate no-cow-copy cow copy_preserves_visible \
  "Copy-on-write without the copy. The snapshot follows the machine instead of
   holding still, so the checkpoint mixes two instants of memory."

gate overlapping-layout machine capture_preserves_memory_at \
  "A layout where the register file and memory share a cell. One overwrites the
   other, and the capture loses state without a trace."

gate ignore-input-journal process replay_follows_the_same_trajectory \
  "A replay that is not given the inputs it had before. The machine follows a
   different trajectory, so the resumed process is not the one that crashed."

gate no-output-dedup io a_stale_event_is_dropped \
  "An I/O boundary that accepts everything. The window repeated after a crash
   reaches the world a second time, so §8 is unbounded again."

gate multi-byte-cells refine an_atomic_cell_lands_whole \
  "A1 dropped: a cell wider than the atomic write unit. A crash can leave it
   holding a mixture, which no point of the abstract lattice describes."

gate half-quorums replication quorums_intersect \
  "Exactly half a cluster accepted as a quorum. Two disjoint halves of an even
   cluster are then both quorums and share no node, so two different
   checkpoints can commit at one generation."

gate elect-any-node replication an_electable_leader_has_seen_every_commit \
  "An election that ignores how far behind a candidate is. A node that missed a
   committed checkpoint can lead, and its next commit erases that checkpoint."

echo
if [ $status -eq 0 ]; then
  echo "all gates passed"
else
  echo "one or more gates FAILED" >&2
fi
exit $status
