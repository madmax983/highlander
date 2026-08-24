#!/usr/bin/env bash
# Falsifiability gates: break a load-bearing part of the design, and the proof MUST
# break with it.
#
# A crash model of this size can be internally consistent and describe nothing. Each
# gate removes one thing the design claims is essential and requires the proof to
# notice. A gate that passes because the crate failed to compile is worse than no
# gate at all, so each case checks three conditions, not one:
#
#   1. verification fails,
#   2. it fails on the named lemma,
#   3. it fails as a *proof* failure, not a compile error.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

status=0

# gate <feature> <lemma> <what it proves>
gate() {
  local feature="$1" lemma="$2" why="$3"
  echo
  echo "── gate: --features $feature"
  echo "   $why"

  local out rc
  out=$(cargo verus verify -p highlander-model --features "$feature" 2>&1)
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

  if ! echo "$out" | grep -q "$lemma"; then
    fail "verification failed, but not on '$lemma'. Something else broke instead."
    return
  fi

  if ! echo "$out" | grep -q 'failed this postcondition'; then
    fail "expected a postcondition failure; got something else."
    return
  fi

  echo "   passed: '$lemma' fails to verify, as required."
  echo "$out" | grep -E 'verification results' | sed 's/^/   /' || true
}

gate no-barrier commit_establishes_shape \
  "Without A2 the payload and seal merge into one epoch, which admits the
   outcome 'seal landed, payload did not'. That recovers to neither generation."

gate degenerate-recover commit_is_durable \
  "A checkpoint that forgets everything never tears, so it satisfies every
   crash-consistency lemma. Only durability rejects it."

gate no-cow-copy copy_preserves_visible \
  "Copy-on-write without the copy. The snapshot follows the machine instead of
   holding still, so the checkpoint mixes two instants of memory."

gate overlapping-layout capture_preserves_memory_at \
  "A layout where the register file and memory share a cell. One overwrites the
   other, and the capture loses state without a trace."

gate ignore-input-journal replay_follows_the_same_trajectory \
  "A replay that is not given the inputs it had before. The machine follows a
   different trajectory, so the resumed process is not the one that crashed."

gate no-output-dedup a_stale_event_is_dropped \
  "An I/O boundary that accepts everything. The window repeated after a crash
   reaches the world a second time, so §8 is unbounded again."

echo
if [ $status -eq 0 ]; then
  echo "all gates passed"
else
  echo "one or more gates FAILED" >&2
fi
exit $status
