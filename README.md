# `lean-convex-geometry`

[![CI](https://github.com/egor1729/lean-convex-geometry/actions/workflows/ci.yml/badge.svg)](https://github.com/egor1729/lean-convex-geometry/actions/workflows/ci.yml)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

A Lean 4 + Mathlib (`v4.36.0`) library for metric, volumetric, and spherical convex geometry in finite-dimensional real inner product spaces and $\mathbb{R}^n$.

It focuses on analytic and geometric foundations complementing algebraic polyhedral libraries (such as [`Polyhedral`](https://github.com/ooovi/Polyhedral)) and supporting downstream formalizations (such as [`sphere-max-volume`](https://github.com/egor1729/sphere-max-volume)).

## Highlights

- **Metric & Duality (`ConvexGeom.Metric`):** Support functions, linear transport, Minkowski's representation theorem, Hörmander's isometry, Blaschke Selection Theorem, metric projection, outer normal cones, supporting hyperplanes, polar bodies, Bipolar Theorem, and gauge–support duality.
- **Polytopes (`ConvexGeom.Polytope`):** Inscribed and full-dimensional general-position polytope approximation, density of affine general position, and $d$-simplex volume $|\det|/d!$.
- **Volume & Symmetrization (`ConvexGeom.Volume`):** Half-ball bounds, Hausdorff continuity of volume, inscribed polytope maximizers, volumetric covering/packing bounds, Prékopa–Leindler, Brunn–Minkowski, Brunn's concavity principle, log-concave convolutions, covariograms, Bieberbach's isodiametric inequality, Rogers–Shephard, Minkowski's first inequality, Euclidean isoperimetry (lower outer Minkowski content), and Minkowski / central / Steiner symmetrization.
- **Spherical & Affine Geometry (`ConvexGeom.Asymptotic`):** Spherical cone probability measure, polar-coordinate volume formula, mean width, Dual Urysohn inequality, ellipsoids, origin-centered and Santaló Mahler volume, and linear / affine Banach–Mazur distances.

## Quick Start

```bash
lake exe cache get
bash scripts/verify.sh
```

To build just the library:

```bash
lake build ConvexGeom --wfail
```

### Use as a Dependency

Add to `lakefile.toml` (with the same Lean version as `lean-toolchain`; pin a commit SHA or tag for reproducibility, or use `rev = "main"` to track development):

```toml
[[require]]
name = "lean-convex-geometry"
git = "https://github.com/egor1729/lean-convex-geometry.git"
rev = "<commit-sha>"
```

```lean
import ConvexGeom
-- or a layer / single module, e.g. ConvexGeom.Volume.BrunnMinkowski
```

## Design Philosophy

- **Mathlib-native abstractions:** State definitions and theorems directly on Mathlib's types, measures, and metric spaces at natural generality.
- **Reusable proofs:** Prefer structural proof routes built from general lemmas over specialized machinery for a single result.
- **Clean verification:** Maintain zero `sorry`, zero warnings, and standard-axiom verification on every commit.
- **Structured commits:** Keep git history readable with small, focused commits.

## Documentation & License

- [`docs/MODULES.md`](docs/MODULES.md) — Directory layout, dependency graph, and theorem index.
- [`docs/CONVENTIONS.md`](docs/CONVENTIONS.md) — Definitions, normalizations, and verification scope.
- [`docs/ROADMAP.md`](docs/ROADMAP.md) — Planned targets, references, and contribution guidelines.
- Licensed under the [Apache License 2.0](LICENSE). Citation metadata is in [`CITATION.cff`](CITATION.cff).
