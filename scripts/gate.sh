#!/usr/bin/env bash
# §7.3 falsifiability gate: remove the barrier, and the proof MUST break.
#
# A negative test that passes because the crate failed to compile is worse than no
# gate at all, so this checks three things, not one:
#
#   1. verification fails,
#   2. it fails on `commit_establishes_shape` — the lemma that bridges the program
#      the protocol emits and the shape the theorem assumes,
#   3. it fails as a *proof* failure, not a compile error.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

echo "running the barrier gate: cargo verus verify --features no-barrier"
out=$(cargo verus verify -p highlander-model --features no-barrier 2>&1)
status=$?

fail() { echo; echo "GATE FAILED: $1" >&2; echo "$out" | tail -40 >&2; exit 1; }

if [ $status -eq 0 ]; then
  fail "verification SUCCEEDED without the barrier.
The model is vacuous: it proves crash consistency of a protocol that does not
have one. Nothing built on this means anything until it is fixed."
fi

if echo "$out" | grep -qE 'E0[0-9]{3}|cannot find|unresolved import|expected .* found'; then
  fail "the build broke for the wrong reason — this is a compile error, not a
proof failure, so the gate is not testing what it claims to test."
fi

if ! echo "$out" | grep -q 'commit_establishes_shape'; then
  fail "verification failed, but not on commit_establishes_shape.
The gate is meant to break the bridge between the emitted program and the
theorem's hypotheses; something else broke instead."
fi

if ! echo "$out" | grep -q 'failed this postcondition'; then
  fail "expected a postcondition failure; got something else."
fi

echo
echo "gate passed: without the barrier, commit_establishes_shape fails to verify."
echo "$out" | grep -E 'verification results' || true
