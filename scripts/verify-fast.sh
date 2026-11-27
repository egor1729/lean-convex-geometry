#!/usr/bin/env bash
set -euo pipefail

# Fast tiered verification for agent & developer inner-loop iteration.
#
# Tier 0 (--static): < 1s, zero Lean compilation.
#   Runs source hygiene (module headers, line/size caps, Challenge purity,
#   forbidden tokens) and formalization.yaml/comparator.json validation.
#
# Tier 1 (default): incremental build + targeted axiom audit of ONLY changed
#   modules (from git status / diff) or explicitly listed modules. Avoids
#   rebuilding untouched modules, audit-control fixtures, or external kernels.
#
# Usage:
#   bash scripts/verify-fast.sh --static
#   bash scripts/verify-fast.sh [ModuleName ...]

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

STATIC_ONLY=0
TARGETS=()
for arg in "$@"; do
  case "$arg" in
    --static) STATIC_ONLY=1 ;;
    -h|--help)
      sed -n '4,16p' "$0"
      exit 0
      ;;
    *) TARGETS+=("$arg") ;;
  esac
done

echo "==> [Tier 0] Static source & metadata checks"
python3 scripts/check-lean-sources.py
python3 scripts/validate-formalization.py

if [[ "$STATIC_ONLY" -eq 1 ]]; then
  echo "FAST STATIC CHECK PASSED."
  exit 0
fi

# Auto-detect changed .lean files when no explicit targets are given.
if [[ "${#TARGETS[@]}" -eq 0 ]]; then
  mapfile -t CHANGED_FILES < <(
    {
      git diff --name-only -- '*.lean' 2>/dev/null || true
      git diff --cached --name-only -- '*.lean' 2>/dev/null || true
      git ls-files --others --exclude-standard -- '*.lean' 2>/dev/null || true
    } | sort -u
  )
  for f in "${CHANGED_FILES[@]}"; do
    [[ -f "$f" ]] || continue
    mod="${f%.lean}"
    mod="${mod//\//.}"
    TARGETS+=("$mod")
  done
fi

if [[ "${#TARGETS[@]}" -eq 0 ]]; then
  echo "==> [Tier 1] No modified .lean files detected; skipping incremental build."
  echo "    Pass explicit module names (e.g. ConvexGeom.Asymptotic.BlaschkeSantalo) or run scripts/verify.sh."
  exit 0
fi

echo "==> [Tier 1] Incremental build of changed target(s): ${TARGETS[*]}"
AUDIT_MODS=()
for mod in "${TARGETS[@]}"; do
  if [[ "$mod" == "Challenge" ]]; then
    # Challenge.lean carries intentional Comparator `sorry` placeholders.
    lake build Challenge
  elif [[ "$mod" == "ConvexGeom.Verification.AxiomAudit" ]]; then
    lake env lean -DwarningAsError=true ConvexGeom/Verification/AxiomAudit.lean >/dev/null
  else
    lake build "$mod" --wfail
    if [[ "$mod" == ConvexGeom || "$mod" == ConvexGeom.* ]] &&
       [[ "$mod" != ConvexGeom.Verification && "$mod" != ConvexGeom.Verification.* ]]; then
      AUDIT_MODS+=("$mod")
    fi
  fi
done

if [[ "${#AUDIT_MODS[@]}" -gt 0 ]]; then
  AUDIT_BIN="$ROOT_DIR/.lake/build/bin/convexgeom-audit"
  if [[ ! -x "$AUDIT_BIN" ]]; then
    echo "==> [Tier 1] Building convexgeom-audit (one-time)"
    lake build convexgeom-audit --wfail
  fi
  echo "==> [Tier 1] Targeted axiom audit on: ${AUDIT_MODS[*]}"
  for mod in "${AUDIT_MODS[@]}"; do
    lake env "$AUDIT_BIN" --module "$mod" --no-check-dir
  done
fi

echo "FAST VERIFICATION PASSED (run scripts/verify.sh and scripts/verify-comparator.sh before merging)."
