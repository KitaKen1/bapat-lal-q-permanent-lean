#!/usr/bin/env bash
set -euo pipefail

COMPARATOR_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
: "${COMPARATOR_TOOLS:?Run install-tools.sh first}"
COMPARATOR_RECEIPT="$COMPARATOR_ROOT/comparator-receipt"
mkdir -p "$COMPARATOR_RECEIPT"
export PATH="$HOME/.elan/bin:$PATH"

python3 "$COMPARATOR_ROOT/comparator/check-inputs.py" --receipt-dir "$COMPARATOR_RECEIPT"
COMPARATOR_PROOF_REV="$(python3 - "$COMPARATOR_ROOT/comparator/pins.json" <<'PY'
import json, sys
print(json.load(open(sys.argv[1]))['proof_commit'])
PY
)"
git -C "$COMPARATOR_ROOT" diff --exit-code "$COMPARATOR_PROOF_REV" -- \
  lean/Bapat.lean lean/Bapat lean/lean-toolchain lean/lake-manifest.json \
  > "$COMPARATOR_RECEIPT/proof.diff"

cp "$COMPARATOR_ROOT/lean/comparator.json" "$COMPARATOR_RECEIPT/config.json"
cp "$COMPARATOR_ROOT/comparator/pins.json" "$COMPARATOR_RECEIPT/pins.json"
cp "$COMPARATOR_ROOT/.github/workflows/comparator.yml" "$COMPARATOR_RECEIPT/workflow.yml"
{
  printf 'run_url=%s/%s/actions/runs/%s\n' "${GITHUB_SERVER_URL:-https://github.com}" "${GITHUB_REPOSITORY:-local}" "${GITHUB_RUN_ID:-local}"
  printf 'run_attempt=%s\n' "${GITHUB_RUN_ATTEMPT:-local}"
  printf 'verification_commit=%s\n' "$(git -C "$COMPARATOR_ROOT" rev-parse HEAD)"
  printf 'started_utc=%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  uname -a
  id
  elan --version
  go version
  (cd "$COMPARATOR_ROOT/lean" && lean --version)
  for COMPARATOR_TOOL in comparator landrun lean4export; do
    printf '%s_commit=%s\n' "$COMPARATOR_TOOL" "$(git -C "$COMPARATOR_TOOLS/$COMPARATOR_TOOL" rev-parse HEAD)"
  done
  printf '\nExporter toolchain override:\n'
  git -C "$COMPARATOR_TOOLS/lean4export" diff -- lean-toolchain
  printf '\nSandbox launcher: system service; --uid/--gid select the unprivileged runner user.\n'
  printf 'RestrictAddressFamilies=~AF_UNIX; NoNewPrivileges=yes\n'
} > "$COMPARATOR_RECEIPT/environment.txt"

printf 'NOT_RUN\n' > "$COMPARATOR_RECEIPT/status.txt"
set +e
sudo systemd-run --wait --collect --pipe \
  --uid="$(id -u)" --gid="$(id -g)" \
  --property='RestrictAddressFamilies=~AF_UNIX' \
  --property=NoNewPrivileges=yes \
  --property=RuntimeMaxSec=90min \
  --working-directory="$COMPARATOR_ROOT/lean" \
  --setenv="PATH=$PATH" --setenv="HOME=$HOME" \
  --setenv="COMPARATOR_LANDRUN=$COMPARATOR_TOOLS/bin/landrun" \
  --setenv="COMPARATOR_LEAN4EXPORT=$COMPARATOR_TOOLS/lean4export/.lake/build/bin/lean4export" \
  -- "$HOME/.elan/bin/lake" env \
  "$COMPARATOR_TOOLS/comparator/.lake/build/bin/comparator" comparator.json \
  2>&1 | tee "$COMPARATOR_RECEIPT/comparator.log"
COMPARATOR_PIPE_STATUS=("${PIPESTATUS[@]}")
set -e
COMPARATOR_EXIT="${COMPARATOR_PIPE_STATUS[0]}"
if [[ "$COMPARATOR_EXIT" -eq 0 && "${COMPARATOR_PIPE_STATUS[1]}" -eq 0 ]]; then
  printf 'PASS\n' > "$COMPARATOR_RECEIPT/status.txt"
else
  printf 'FAIL: comparator=%s tee=%s\n' "$COMPARATOR_EXIT" "${COMPARATOR_PIPE_STATUS[1]}" > "$COMPARATOR_RECEIPT/status.txt"
  exit 1
fi
