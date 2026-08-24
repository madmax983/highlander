#!/usr/bin/env bash
# Verify the whole proof development.
#
# Refuses to run if the installed `verus` binary and the pinned `vstd` version
# disagree. They encode the same prelude; if they drift, verification is checking
# your code against a standard library your prover does not implement.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

if ! command -v verus >/dev/null 2>&1; then
  cat >&2 <<'EOF'
error: `verus` is not on PATH.

Grab a release and add its directory to PATH:

  curl -L -o verus.zip \
    https://github.com/verus-lang/verus/releases/latest/download/verus-<version>-arm64-macos.zip
  unzip verus.zip
  export PATH="$PWD/verus-arm64-macos:$PATH"

Download with curl, not a browser: curl does not set the com.apple.quarantine
attribute, so Gatekeeper stays out of the way. If you did use a browser, run
`xattr -dr com.apple.quarantine <dir>` — do not run the bundled
macos_allow_gatekeeper.sh, which has a `${{BASH_SOURCE[0]}}` typo and fails.
EOF
  exit 1
fi

pinned=$(grep -o 'vstd = { version = "=[^"]*"' Cargo.toml | sed 's/.*"=//; s/"//')
installed=$(verus --version | sed -n 's/^ *Version: *//p')

# The vstd crate is date-stamped (0.0.0-YYYY-MM-DD-HHMM); the binary is
# 0.YYYY.MM.DD.<sha>. Compare the dates, which is the part that has to agree.
pin_date=$(echo "$pinned"   | sed -n 's/^0\.0\.0-\([0-9]\{4\}\)-\([0-9]\{2\}\)-\([0-9]\{2\}\).*/\1\2\3/p')
bin_date=$(echo "$installed" | sed -n 's/^0\.\([0-9]\{4\}\)\.\([0-9]\{2\}\)\.\([0-9]\{2\}\).*/\1\2\3/p')

if [ "$pin_date" != "$bin_date" ]; then
  echo "error: vstd pin and verus binary disagree." >&2
  echo "  Cargo.toml pins vstd = $pinned  (date $pin_date)" >&2
  echo "  verus --version reports $installed  (date $bin_date)" >&2
  echo "Update the pin in Cargo.toml, or install the matching Verus release." >&2
  exit 1
fi

echo "verus $installed / vstd $pinned — versions agree"
exec cargo verus verify --workspace "$@"
