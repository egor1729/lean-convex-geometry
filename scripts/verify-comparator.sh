#!/usr/bin/env bash
set -euo pipefail

# Tier 3: Trustless sandboxed statement-vs-proof verification via the
# `lake comparator` bundled in this project's pinned Lean toolchain.
#
# By default, runs Palomar's exact independent-kernel set (Lean's default
# kernel + bundled `nanoda_bin` and `con-ron`) inside a `bwrap` sandbox.
#
# Usage:
#   bash scripts/verify-comparator.sh [--paranoid] [--skip-cache] [--check-lib]
#
# Options:
#   --paranoid    Run `lake comparator --paranoid` (Lean kernel + all 5 bundled
#                 independent checkers: leanchecker-paranoid, lean4lean,
#                 nanoda_bin, con-leche, con-ron).
#   --skip-cache  Skip `lake exe cache get` (useful when cache is already warm).
#   --check-lib   Also run `lake check --paranoid` on the default `ConvexGeom`
#                 library target.

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

PARANOID=0
SKIP_CACHE=0
CHECK_LIB=0
for arg in "$@"; do
  case "$arg" in
    --paranoid) PARANOID=1 ;;
    --skip-cache) SKIP_CACHE=1 ;;
    --check-lib) CHECK_LIB=1 ;;
    -h|--help)
      sed -n '3,19p' "$0"
      exit 0
      ;;
    *)
      echo "error: unknown option: $arg" >&2
      exit 2
      ;;
  esac
done

for required_command in bwrap lake lean python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run lake comparator" >&2
    exit 1
  fi
done

toolchain="$(tr -d '[:space:]' < lean-toolchain)"
prefix="$(lean --print-prefix)"
required_tools=(lake leanexport leanchecker nanoda_bin con-ron)
if [[ "$PARANOID" -eq 1 ]]; then
  required_tools+=(leanchecker-paranoid lean4lean con-leche)
fi
for tool in "${required_tools[@]}"; do
  if [[ ! -x "$prefix/bin/$tool" ]]; then
    echo "error: toolchain $toolchain does not bundle $tool" >&2
    echo "Lean v4.35.0+ is required for core lake comparator and bundled kernels." >&2
    exit 1
  fi
done

# Pre-flight: ensure comparator.json is Palomar-compliant (no committed external_kernels).
python3 scripts/check-lean-sources.py
python3 scripts/validate-formalization.py

if [[ "$SKIP_CACHE" -eq 0 ]]; then
  lake exe cache get
fi

if [[ "$PARANOID" -eq 1 ]]; then
  echo "==> Running lake comparator --paranoid (Lean + all 5 bundled independent kernels)"
  lake comparator --paranoid --config comparator.json
else
  # Mirror Palomar: inject the toolchain's bundled nanoda_bin and con-ron kernels
  # into a temporary config without mutating the committed comparator.json.
  config="$(mktemp "${TMPDIR:-/tmp}/convexgeom-comparator.XXXXXX.json")"
  trap 'rm -f "$config"' EXIT
  python3 - comparator.json "$config" "$prefix" <<'PY'
import json
import pathlib
import sys

source, destination, prefix = sys.argv[1:]
cfg = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
if not isinstance(cfg, dict):
    raise SystemExit(f"error: {source} must contain a JSON object")
if "external_kernels" in cfg:
    raise SystemExit(f"error: {source} must not commit external_kernels")
cfg.pop("enable_nanoda", None)
cfg["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
pathlib.Path(destination).write_text(json.dumps(cfg, indent=2) + "\n", encoding="utf-8")
PY
  echo "==> Running lake comparator with bundled independent kernels (nanoda, con-ron)"
  lake comparator --config "$config"
fi

if [[ "$CHECK_LIB" -eq 1 ]]; then
  echo "==> Running lake check --paranoid on default library target (ConvexGeom)"
  lake check --paranoid
fi

echo "COMPARATOR VERIFICATION PASSED."
