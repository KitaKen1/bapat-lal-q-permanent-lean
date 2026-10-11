#!/usr/bin/env bash
set -euo pipefail

COMPARATOR_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
: "${COMPARATOR_TOOLS:?Set COMPARATOR_TOOLS to a fresh tool directory}"
mkdir -p "$COMPARATOR_TOOLS/bin"
read -r COMPARATOR_REV COMPARATOR_EXPORT_REV COMPARATOR_LANDRUN_REV < <(
  python3 - "$COMPARATOR_ROOT/comparator/pins.json" <<'PY'
import json, sys
pins = json.load(open(sys.argv[1]))
print(pins['comparator_commit'], pins['lean4export_commit'], pins['landrun_commit'])
PY
)

# Install elan without building the submitted proof.
curl --fail --silent --show-error --location \
  https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  --output "$COMPARATOR_TOOLS/elan-init.sh"
bash "$COMPARATOR_TOOLS/elan-init.sh" -y --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"
COMPARATOR_PROOF_TOOLCHAIN="$(tr -d '\r\n' < "$COMPARATOR_ROOT/lean/lean-toolchain")"
elan toolchain install "$COMPARATOR_PROOF_TOOLCHAIN"

git clone https://github.com/zouuup/landrun.git "$COMPARATOR_TOOLS/landrun"
git -C "$COMPARATOR_TOOLS/landrun" checkout --detach "$COMPARATOR_LANDRUN_REV"
(
  cd "$COMPARATOR_TOOLS/landrun"
  go build -trimpath -o "$COMPARATOR_TOOLS/bin/landrun" ./cmd/landrun
)

git clone https://github.com/leanprover/comparator.git "$COMPARATOR_TOOLS/comparator"
git -C "$COMPARATOR_TOOLS/comparator" checkout --detach "$COMPARATOR_REV"
(
  cd "$COMPARATOR_TOOLS/comparator"
  elan toolchain install "$(tr -d '\r\n' < lean-toolchain)"
  lake build comparator
)

# Build the exporter with the EXACT proof toolchain, not Comparator's toolchain.
git clone https://github.com/leanprover/lean4export.git "$COMPARATOR_TOOLS/lean4export"
git -C "$COMPARATOR_TOOLS/lean4export" checkout --detach "$COMPARATOR_EXPORT_REV"
cp "$COMPARATOR_ROOT/lean/lean-toolchain" "$COMPARATOR_TOOLS/lean4export/lean-toolchain"
(
  cd "$COMPARATOR_TOOLS/lean4export"
  lake build lean4export
)

# Trusted Mathlib cache only. Do not run lake build on Bapat here.
(
  cd "$COMPARATOR_ROOT/lean"
  lake exe cache get
)
