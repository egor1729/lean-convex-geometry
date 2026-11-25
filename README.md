# `lean-convex-geometry`

[![CI](https://github.com/egor1729/lean-convex-geometry/actions/workflows/ci.yml/badge.svg)](https://github.com/egor1729/lean-convex-geometry/actions/workflows/ci.yml)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

A Lean 4 + Mathlib (`v4.36.0`) library for **metric, volumetric, and spherical convex geometry** in finite-dimensional real inner product spaces and $\mathbb{R}^n$.

It provides reusable analytic and geometric foundations complementing algebraic polyhedral libraries (such as [`Polyhedral`](https://github.com/ooovi/Polyhedral)) and supporting downstream formalizations (such as [`sphere-max-volume`](https://github.com/egor1729/sphere-max-volume)).

## Highlights

- **Metric, Boundary & Duality (`ConvexGeom.Metric`):** Support calculus, continuous-linear body transport (`mapLinear`), constructive Minkowski representation (`bodyOfSupportFn`), Hörmander's isometry, Blaschke Selection Theorem, metric projection, outer normal cones (`normalCone` / `strictNormalCone`), supporting hyperplanes, polar bodies, Bipolar Theorem, and gauge–support duality.
- **Polytopes (`ConvexGeom.Polytope`):** Inscribed and full-dimensional inscribed general-position polytope approximation, affine general-position density, and $d$-simplex volume $|\det|/d!$ (both linear-map and explicit matrix-determinant interfaces).
- **Volume, Brunn–Minkowski & Symmetrization (`ConvexGeom.Volume`):** General-dimension half-ball bounds and inscribed polytope volume maximizers, Hausdorff continuity of volume, volumetric covering/packing bounds for arbitrary norms, $d$-dimensional Prékopa–Leindler, Brunn–Minkowski, Brunn's concavity principle, log-concave convolutions, covariograms, Bieberbach's isodiametric inequality, Rogers–Shephard, Minkowski's first inequality, Euclidean isoperimetry (lower outer Minkowski content), and Minkowski / central / Steiner symmetrization.
- **Spherical & Affine-Invariant Geometry (`ConvexGeom.Asymptotic`):** Haar-invariant spherical cone probability measure, polar-coordinate volume formula, mean width calculus, Dual Urysohn inequality, ellipsoids, origin-centered & Santaló Mahler volume, and linear / affine Banach–Mazur distances (real and extended-valued).

See [`MODULES.md`](MODULES.md) for the full repository layout, dependency graph, and module-by-module theorem index.

## Quick Start

```bash
lake exe cache get
bash scripts/verify.sh
```

`scripts/verify.sh` runs the full local and CI verification suite:

- `lake build ConvexGeom --wfail` — builds all library modules with warnings fatal.
- `lake build ConvexGeomTest --wfail` — builds the regression and counterexample test suite.
- `lake exe convexgeom-audit` — exhaustively audits every declaration across every library module.
- `bash scripts/test_audit.sh` — runs negative and positive controls against `convexgeom-audit`.
- `lake env lean -DwarningAsError=true ConvexGeom/Verification/AxiomAudit.lean` — checks the fail-closed headline theorem snapshot.

### Use as a Dependency

Add to `lakefile.toml` (matching the toolchain in `lean-toolchain`; pin a specific commit SHA or release tag for reproducible downstream formalizations, or use `rev = "main"` to track development):

```toml
[[require]]
name = "lean-convex-geometry"
git = "https://github.com/egor1729/lean-convex-geometry.git"
rev = "<commit-sha>"
```

```lean
import ConvexGeom
-- or import a layer barrel, e.g. ConvexGeom.Volume
-- or an individual module, e.g. ConvexGeom.Volume.BrunnMinkowski
```

## Conventions & Trust Boundary

- **Convex bodies:** `ConvexBody E` is Mathlib's nonempty compact convex sets, including degenerate sets with empty interior; full-dimensionality or `0 ∈ interior K` is requested explicitly where required.
- **Measures & sphere normalization:** `volume` uses Mathlib's Lebesgue normalization. `sphereProb` is the Haar-normalization-independent cone probability measure on $S(0,1)$ (coinciding with normalized spherical surface measure on Euclidean spaces; empty/zero in dimension $0$).
- **Mean width:** `meanWidth K` is half the classical mean breadth (`meanWidth (bodyClosedBall c r) = r`, with $\int \mathrm{width}(K, u)\,d\sigma(u) = 2\,\mathrm{meanWidth}(K)$).
- **Mahler volume & Banach–Mazur distance:** `mahlerVolume` is origin-centered ($\mathrm{GL}$-invariant), whereas `santaloMahlerVolume` minimizes over $z \in \mathrm{interior}(S)$ (full affine invariant). `banachMazurDist`/`EDist` are origin-fixed linear multiplicative distances, whereas `affineBanachMazurDist`/`EDist` allow recentering (`*EDist` takes value `⊤` on infeasible pairs; the real-valued totalizations return `sInf ∅ = 0`).
- **Steiner symmetrization & product norm:** `steinerSymm` is interval-hull symmetrization (matching classical measure-theoretic Steiner symmetrization on compact convex sets; `bodySteinerSymm` bundles it on `ConvexBody (ℝ × E)`). `ℝ × E` carries Mathlib's product max-norm; Euclidean distance bounds are stated explicitly.
- **Minkowski surface area:** `minkowskiSurfaceArea` is the lower outer Minkowski content ($\liminf_{t \to 0^+}$).
- **Trust boundary:** Every project module and declaration is audited by `convexgeom-audit` against Lean's standard classical axioms `{propext, Classical.choice, Quot.sound}` with zero `sorry` and `--wfail`, backed by automated negative controls and `ConvexGeomTest/`. Verification trusts the Lean 4 (`v4.36.0`) kernel and pinned Mathlib artifacts (`lake-manifest.json`); axiom auditing certifies kernel dependency closure rather than acting as an independent external kernel checker.

## Design Philosophy

- **Mathlib-native abstractions:** State definitions and theorems directly on Mathlib's existing types, measures, and metric spaces at natural generality.
- **Conceptual, reusable proofs:** Prefer structural proof routes built from general lemmas over specialized machinery for a single theorem.
- **Strict verification:** Enforce zero `sorry`, zero warnings, environment-wide axiom auditing, and semantic regression tests in a single scripted pipeline.
- **Structured commits:** Keep repository history clean with small, focused commits rather than large multi-feature dumps.

## Documentation & License

- [`MODULES.md`](MODULES.md) — Repository layout, layered dependency graph, and theorem guide.
- [`ROADMAP.md`](ROADMAP.md) — Planned targets, reference literature, and contribution guidelines.
- Licensed under the [Apache License 2.0](LICENSE); see [`CITATION.cff`](CITATION.cff) for citation metadata.
