# Recipes are thin wrappers around scripts/, so everything works without extra tools.
.PHONY: all verify gate test check fmt clean

all: verify gate test check

## Verify the whole proof development (requires `verus` on PATH).
verify:
	@./scripts/verify.sh

## §7.3 falsifiability gate — the proof must FAIL with the barrier removed.
gate:
	@./scripts/gate.sh

## Property tests against the independent reference implementation.
test:
	@cargo test --workspace

## The model is also ordinary Rust 2024.
check:
	@cargo build --workspace
	@cargo clippy --workspace --all-targets -- -D warnings

fmt:
	@cargo fmt --all

clean:
	@cargo clean
