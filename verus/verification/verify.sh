#!/usr/bin/env bash
# Verify the annotated crate, then the verified client of its specifications.
#
# Usage (from anywhere): verus/verification/verify.sh
# Needs `verus` on PATH, or VERUS=/path/to/verus. Extra arguments are passed to both Verus runs
# (e.g. `--smt-option smt.random_seed=7`).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
crate="$(dirname "$here")"
verus="${VERUS:-$(command -v verus || echo verus)}"
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT

echo "== rand_core (src/lib.rs)"
"$verus" --crate-type=lib --edition=2024 --crate-name rand_core "$crate/src/lib.rs" \
    --export "$out/rand_core.vir" --compile -o "$out/librand_core.rlib" "$@"

echo "== verified client (verification/client_examples.rs)"
"$verus" --edition=2024 "$here/client_examples.rs" -o "$out/client_examples" \
    --extern rand_core="$out/librand_core.rlib" --import rand_core="$out/rand_core.vir" "$@"
