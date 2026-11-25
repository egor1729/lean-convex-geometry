# `lean-convex-geometry`

[![CI](https://github.com/egor1729/lean-convex-geometry/actions/workflows/ci.yml/badge.svg)](https://github.com/egor1729/lean-convex-geometry/actions/workflows/ci.yml)

A Lean 4 + Mathlib (`v4.36.0`) library for **metric, volumetric, and spherical convex geometry** in finite-dimensional real inner product spaces and $\mathbb{R}^n$.

It provides reusable analytic and geometric foundations complementing algebraic polyhedral libraries (such as [`Polyhedral`](https://github.com/ooovi/Polyhedral)) and supporting downstream formalizations (such as [`sphere-max-volume`](https://github.com/egor1729/sphere-max-volume)).

## Highlights

- **Metric, Boundary & Duality:** Support calculus, Hörmander's isometry, Minkowski's representation theorem, Blaschke Selection Theorem, metric projection / outer normal cones / supporting hyperplanes, polar bodies, Bipolar Theorem, and gauge–support duality.
- **Polytopes, Volume & Covering:** Inscribed and general-position (simplicial) polytope approximation, $d$-simplex volume $|\det|/d!$, half-ball bounds, Hausdorff continuity of volume, and volumetric covering/packing bounds for arbitrary norms.
- **Brunn–Minkowski & Isoperimetry:** $d$-dimensional Prékopa–Leindler, Brunn–Minkowski, Brunn's concavity principle, log-concave convolutions, Bieberbach's isodiametric inequality, Rogers–Shephard, Minkowski's first inequality, Euclidean isoperimetry, and Minkowski / central / Steiner symmetrization.
- **Spherical & Affine-Invariant Geometry:** Uniform spherical probability measure, polar-coordinate volume formula, mean width calculus, Dual Urysohn inequality, ellipsoids, $\mathrm{GL}(E)$-invariance of Mahler volume, and polarity-invariant Banach–Mazur distance.

See [`MODULES.md`](MODULES.md) for the full repository layout, dependency graph, and module-by-module theorem index.

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

## Documentation

- [`MODULES.md`](MODULES.md) — Repository layout, dependency graph, and theorem guide.
- [`ROADMAP.md`](ROADMAP.md) — Planned targets, reference literature, and contribution guidelines.
