# Conventions & Verification

Notes on definitions, normalizations, edge cases, and verification scope in `lean-convex-geometry`.

## Mathematical Conventions

- **Convex bodies (`ConvexBody E`):** Uses Mathlib's `ConvexBody E` (nonempty compact convex sets), which includes degenerate sets with empty interior such as singletons, segments, and radius-zero balls. Theorems needing nonempty interior or `0 ∈ interior K` take that hypothesis explicitly.
- **Volume and spherical measure:** `volume` uses Mathlib's Lebesgue normalization. `sphereProb μ` is the normalized cone probability measure on `Metric.sphere 0 1`. It is independent of the choice or scaling of an additive Haar measure `μ` (`sphereProb_eq_of_isAddHaarMeasure`), agrees with normalized spherical surface measure on Euclidean spaces, and is zero on the empty unit sphere in dimension `0`.
- **Width and mean width:** `width K u = supportFn K u + supportFn K (-u)` is the breadth in direction `u`, while `meanWidth K = ∫ u, supportFn K u ∂(sphereProb volume)` is half the classical mean breadth. Thus `meanWidth (bodyClosedBall c r) = r` and `∫ u, width K u ∂(sphereProb volume) = 2 * meanWidth K`.
- **Outer normal cones:** `normalCone S y = {u | ∀ z ∈ S, ⟪z - y, u⟫ ≤ 0}` does not guard on `y ∈ S` (so `0 ∈ normalCone S y` even when `y ∉ S`). `strictNormalCone S y` equals `normalCone S y` for `y ∈ S` and `∅` for `y ∉ S`.
- **Mahler volume:** `mahlerVolume μ S = μ S * μ (polarBody S)` is centered at the origin and `GL`-invariant. `mahlerVolumeAt μ S z` translates `S` by `-z` before taking the polar, and `santaloMahlerVolume μ S` infimizes over `z ∈ interior S`, giving full affine invariance.
- **Banach–Mazur distance:** `banachMazurDist` and `banachMazurEDist` are origin-fixed linear multiplicative distances. `affineBanachMazurDist` and `affineBanachMazurEDist` allow translations (recentering). The `ℝ≥0∞`-valued `*EDist` variants return `⊤` on infeasible pairs, while the real-valued infima inherit Mathlib's `sInf ∅ = 0`.
- **Steiner symmetrization and product norms:** `steinerSymm` replaces each nonempty line fiber by the centered interval of length `sSup - sInf`. On compact convex sets this agrees with measure-theoretic Steiner symmetrization (`bodySteinerSymm` packages this on `ConvexBody (ℝ × E)`), while on disconnected sets it fills gaps between the endpoints. `ℝ × E` carries Mathlib's product max-norm; Euclidean distance bounds (`steinerSymm_dist_le_diam`) are written explicitly.
- **Minkowski surface area:** `minkowskiSurfaceArea` is the lower outer Minkowski content (`liminf` as `t → 0⁺`).

## Verification Scope

`bash scripts/verify.sh` (run locally and in CI) executes:

1. `lake build ConvexGeom --wfail`
2. `lake build ConvexGeom.Verification.Checks --wfail`
3. `lake exe convexgeom-audit` — walks the compiled environment (at `.private` level, without executing module initializers) across all library modules, checks that every `.lean` file outside `ConvexGeom/Verification/` is imported by `ConvexGeom`, rejects any project-defined `axiom`, and rejects any transitive dependency outside `{propext, Classical.choice, Quot.sound}`.
4. `bash scripts/test_audit.sh` — runs positive and negative control fixtures against `convexgeom-audit`.
5. `lake env lean -DwarningAsError=true ConvexGeom/Verification/AxiomAudit.lean` — verifies the headline `#print axioms` list with exact name matching.

Verification trusts the Lean 4 (`v4.36.0`) kernel and the pinned Mathlib build artifacts in `lake-manifest.json`; `convexgeom-audit` certifies kernel dependency closure rather than acting as an independent external kernel checker.
