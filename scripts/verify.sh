#!/usr/bin/env bash
set -euo pipefail

# Unified local and CI verification entry point for lean-convex-geometry.
# Usage: bash scripts/verify.sh [audit-report-path]

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

REPORT_PATH="${1:-audit-report.json}"

echo "==> 1. Building ConvexGeom"
lake build ConvexGeom --wfail

echo "==> 2. Building verification checks"
lake build ConvexGeom.Verification.Checks --wfail

echo "==> 3. Building convexgeom-audit"
lake build convexgeom-audit --wfail

echo "==> 4. Running environment-wide axiom audit"
lake exe convexgeom-audit --json "$REPORT_PATH"

# Attach repository provenance (git commit and manifest SHA-256) to the JSON report.
GIT_COMMIT="$(git rev-parse HEAD 2>/dev/null || echo unknown)"
MANIFEST_SHA256="$(sha256sum lake-manifest.json | awk '{print $1}')"
python3 - "$REPORT_PATH" "$GIT_COMMIT" "$MANIFEST_SHA256" <<'PY'
import json, sys
path, commit, manifest_sha = sys.argv[1:4]
with open(path, "r", encoding="utf-8") as f:
    data = json.load(f)
data["gitCommit"] = commit
data["lakeManifestSha256"] = manifest_sha
with open(path, "w", encoding="utf-8") as f:
    json.dump(data, f, indent=2)
    f.write("\n")
if not data.get("passed"):
    sys.exit(1)
PY

echo "==> 5. Running negative- and positive-control audit tests"
bash scripts/test_audit.sh

echo "==> 6. Verifying headline AxiomAudit.lean snapshot (warnings fatal, fail-closed exact match)"
out="$(lake env lean -DwarningAsError=true ConvexGeom/Verification/AxiomAudit.lean 2>&1)"
python3 - "$out" ConvexGeom/Verification/AxiomAudit.lean <<'PY'
import re, sys

text = sys.argv[1]
audit_file = sys.argv[2]

with open(audit_file, "r", encoding="utf-8") as f:
    requested = [
        m.group(1)
        for line in f
        for m in [re.match(r"^\s*#print\s+axioms\s+(\S+)\s*$", line)]
        if m
    ]

if not requested:
    print("ERROR: No #print axioms lines found in AxiomAudit.lean!")
    sys.exit(1)

if len(requested) != len(set(requested)):
    print("ERROR: Duplicate #print axioms entries detected in AxiomAudit.lean!")
    sys.exit(1)

allowed = {"propext", "Classical.choice", "Quot.sound"}
reported = {}
for m in re.finditer(
    r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
    text,
    re.S,
):
    name = m.group(1)
    axs_raw = m.group(2)
    if name in reported:
        print(f"ERROR: Duplicate axiom report for '{name}'")
        sys.exit(1)
    axs = [a.strip() for a in axs_raw.split(",") if a.strip()] if axs_raw is not None else []
    reported[name] = axs

req_set = set(requested)
rep_set = set(reported.keys())
if req_set != rep_set:
    missing = sorted(req_set - rep_set)
    extra = sorted(rep_set - req_set)
    print(f"ERROR: AxiomAudit report mismatch! missing={missing}, extra={extra}")
    sys.exit(1)

bad = [(n, [a for a in axs if a not in allowed]) for n, axs in reported.items()]
bad = [(n, u) for n, u in bad if u]
if bad:
    print("ERROR: Unexpected axiom(s) in AxiomAudit.lean:")
    for n, u in bad:
        print(f"  {n}: {u}")
    sys.exit(1)

print(f"AxiomAudit snapshot passed ({len(reported)}/{len(requested)} headline theorems verified).")
PY

echo "ALL VERIFICATION CHECKS PASSED."
