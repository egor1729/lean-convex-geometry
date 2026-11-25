#!/usr/bin/env bash
set -euo pipefail

# Negative-control and regression test suite for `convexgeom-audit`.
# Compiles isolated scratch fixtures in a temporary directory (never part of `ConvexGeom`),
# and verifies that `convexgeom-audit` catches every disallowed pattern while accepting clean code.

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

TMPDIR="$(mktemp -d)"
trap 'rm -rf "$TMPDIR"' EXIT

AUDIT_BIN="$ROOT_DIR/.lake/build/bin/convexgeom-audit"
if [[ ! -x "$AUDIT_BIN" ]]; then
  echo "Building convexgeom-audit..."
  lake build convexgeom-audit --wfail
fi

BASE_LEAN_PATH="$(lake env printenv LEAN_PATH)"
export LEAN_PATH="$TMPDIR:$BASE_LEAN_PATH"

compile_fixture() {
  local mod="$1"
  local src="$TMPDIR/${mod}.lean"
  local olean="$TMPDIR/${mod}.olean"
  mkdir -p "$(dirname "$src")"
  cat > "$src"
  lean -R "$TMPDIR" "$src" -o "$olean" >/dev/null
}

expect_fail() {
  local label="$1"
  shift
  local out
  if out="$("$AUDIT_BIN" "$@" 2>&1)"; then
    echo "FAIL [$label]: expected convexgeom-audit to reject fixture, but it PASSED!"
    echo "$out"
    exit 1
  else
    echo "PASS [$label]: correctly rejected."
  fi
}

expect_pass() {
  local label="$1"
  shift
  local out
  if out="$("$AUDIT_BIN" "$@" 2>&1)"; then
    echo "PASS [$label]: correctly accepted."
  else
    echo "FAIL [$label]: expected convexgeom-audit to accept fixture, but it FAILED!"
    echo "$out"
    exit 1
  fi
}

# 1. Unused public custom axiom
compile_fixture "AuditFixUnusedAxiom" <<'EOF'
module
public section
axiom evilUnused : False
end
EOF
expect_fail "unused public axiom" --module AuditFixUnusedAxiom --no-check-dir

# 2. Unused private custom axiom (catches module-private leaks)
compile_fixture "AuditFixPrivateAxiom" <<'EOF'
module
private axiom evilPrivate : False
public section
theorem ok : True := trivial
end
EOF
expect_fail "unused private axiom" --module AuditFixPrivateAxiom --no-check-dir

# 3. Theorem depending on custom axiom
compile_fixture "AuditFixUsedAxiom" <<'EOF'
module
private axiom evilDep : True
public section
theorem badThm : True := evilDep
end
EOF
expect_fail "theorem depending on custom axiom" --module AuditFixUsedAxiom --no-check-dir

# 4. Public theorem using sorry
compile_fixture "AuditFixSorry" <<'EOF'
module
public section
theorem badSorry : True := sorry
end
EOF
expect_fail "public sorry theorem" --module AuditFixSorry --no-check-dir

# 5. Private theorem using sorry (even if never referenced publicly)
compile_fixture "AuditFixPrivateSorry" <<'EOF'
module
private theorem hiddenSorry : True := sorry
public section
theorem ok : True := trivial
end
EOF
expect_fail "private sorry theorem" --module AuditFixPrivateSorry --no-check-dir

# 6. Disallowed axiom declared outside the module's namespace
compile_fixture "AuditFixOtherNamespace" <<'EOF'
module
namespace CompletelyOtherNamespace
public axiom sneaky : False
public theorem sneakyThm : False := sneaky
end CompletelyOtherNamespace
EOF
expect_fail "non-project namespace axiom" --module AuditFixOtherNamespace --no-check-dir

# 7. Filesystem completeness: orphan .lean file not imported by root module
mkdir -p "$TMPDIR/AuditFixPkg"
compile_fixture "AuditFixPkg" <<'EOF'
module
public section
theorem rootOk : True := trivial
end
EOF
cat > "$TMPDIR/AuditFixPkg/Orphan.lean" <<'EOF'
module
public section
theorem orphan : True := trivial
end
EOF
(cd "$TMPDIR" && expect_fail "orphan filesystem module" --module AuditFixPkg --check-dir AuditFixPkg)

# 8. Positive control: clean module with only standard axioms
compile_fixture "AuditFixClean" <<'EOF'
module
public section
theorem cleanThm : ∀ P : Prop, P ∨ ¬ P := fun P => Classical.em P
end
EOF
expect_pass "clean fixture" --module AuditFixClean --no-check-dir

# 9. Production library audit
expect_pass "production ConvexGeom library" --module ConvexGeom --check-dir ConvexGeom

echo "All convexgeom-audit negative and positive controls PASSED."
