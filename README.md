# `lean-convex-geometry`

[![CI](https://github.com/egor1729/lean-convex-geometry/actions/workflows/ci.yml/badge.svg)](https://github.com/egor1729/lean-convex-geometry/actions/workflows/ci.yml)

A Lean 4 + Mathlib (`v4.36.0`) library for **metric, volumetric, and spherical convex geometry** in finite-dimensional real inner product spaces and $\mathbb{R}^n$.

It provides reusable analytic and geometric foundations complementing algebraic polyhedral libraries (such as [`Polyhedral`](https://github.com/ooovi/Polyhedral)) and supporting downstream formalizations (such as [`sphere-max-volume`](https://github.com/egor1729/sphere-max-volume)).

## Contents

All modules are re-exported by [`ConvexGeom.lean`](ConvexGeom.lean).

| Module | Highlights |
| --- | --- |
| [`SupportFunction.lean`](ConvexGeom/SupportFunction.lean) | Support function calculus (`supportFn`), Hahn–Banach separation, directional width, Hörmander's isometric embedding (`isometry_supportFnOnBall`), Hausdorff metric algebra, Minkowski's representation theorem (`exists_convexBody_supportFn_eq`) |
| [`Blaschke.lean`](ConvexGeom/Blaschke.lean) | Completeness of `ConvexBody E` (`instCompleteSpaceConvexBody`) and the Blaschke Selection Theorem (`blaschke_selection`) |
| [`Polarity.lean`](ConvexGeom/Polarity.lean) | One-sided polar bodies (`polarBody`, `bodyPolar`), adjoint duality, Bipolar Theorem (`polarBody_polarBody`), and gauge–support duality |
| [`Polytope.lean`](ConvexGeom/Polytope.lean) | Finite convex hulls (`bodyConvexHull`), 1-Lipschitz Hausdorff stability, and inscribed polytope approximation (`exists_polytope_dist_lt`) |
| [`SimplexVolume.lean`](ConvexGeom/SimplexVolume.lean) | $d$-simplex volume $|\det|/d!$ on `Fin d → ℝ` (`volume_convexHull_simplex`) and `EuclideanSpace ℝ (Fin d)` |
| [`VolumeContinuity.lean`](ConvexGeom/VolumeContinuity.lean) | Half-ball volume identity (`addHaar_halfBall`) and Hausdorff continuity of add-Haar volume on `ConvexBody E` (`continuous_addHaar_convexBody`) |
| [`CoveringNumbers.lean`](ConvexGeom/CoveringNumbers.lean) | Volumetric covering and packing bounds for arbitrary norms on $\mathbb{R}^d$ and unit-ball bounds $(1/\varepsilon)^d \le \mathcal{N}_{\mathrm{ext}}$, $\mathcal{N} \le (3/\varepsilon)^d$ |
| [`BrunnMinkowski.lean`](ConvexGeom/BrunnMinkowski.lean) | $d$-dimensional Prékopa–Leindler (`prekopa_leindler`), multiplicative and additive Brunn–Minkowski (`brunn_minkowski_compact`, `brunn_minkowski_convexBody`), Bieberbach's isodiametric inequality (`isodiametric_inequality`), and log-concavity of marginals |
| [`Symmetrization.lean`](ConvexGeom/Symmetrization.lean) | Hyperplane reflection, Minkowski and central symmetrization (`minkowskiSymm`, `centralSymm`), and Steiner symmetrization (`steinerSymm`, convexity, compactness, volume preservation, diameter bound) |

## Quick Start

```bash
lake exe cache get
lake build ConvexGeom --wfail
lake env lean ConvexGeom/Verification/AxiomAudit.lean
```

### Use as a Dependency

Add to `lakefile.toml` (matching the toolchain in `lean-toolchain`):

```toml
[[require]]
name = "lean-convex-geometry"
git = "https://github.com/egor1729/lean-convex-geometry.git"
rev = "main"
```

```lean
import ConvexGeom
-- or import individual modules, e.g. ConvexGeom.BrunnMinkowski
```

## Design Philosophy

- **Mathlib-native abstractions:** State results directly on Mathlib's existing types, measures, and metric spaces at natural generality.
- **Conceptual, reusable proofs:** Prefer structural proof routes built from general lemmas over specialized machinery for a single theorem.
- **Strict verification:** Zero `sorry`, zero warnings (`--wfail`), and CI-enforced axiom auditing ([`AxiomAudit.lean`](ConvexGeom/Verification/AxiomAudit.lean)) against Lean's standard axioms only.
- **Structured commits:** Keep repository history clean with small, focused commits rather than large multi-feature dumps.

## Roadmap & Contributing

See [`ROADMAP.md`](ROADMAP.md) for planned modules, classical targets, reference literature, and contribution guidelines.
