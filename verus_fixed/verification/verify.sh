#!/usr/bin/env bash
# Verify the annotated crate, then the verified clients of its specifications: the examples, the
# two refinement checks (the developer's contracts, and Claude's first-pass contracts, each
# implemented by calling the crate), and the calls that only the fixed contracts allow.
#
# Usage (from anywhere): verus_fixed/verification/verify.sh
# Needs `verus` on PATH, or VERUS=/path/to/verus. Extra arguments are passed to every Verus run
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

for client in client_examples human_spec_client claude_spec_client gap_clients; do
    echo "== verified client (verification/$client.rs)"
    "$verus" --edition=2024 "$here/$client.rs" -o "$out/$client" \
        --extern rand_core="$out/librand_core.rlib" --import rand_core="$out/rand_core.vir" "$@"
done
