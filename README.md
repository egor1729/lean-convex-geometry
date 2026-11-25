# `lean-convex-geometry`

[![CI](https://github.com/egor1729/lean-convex-geometry/actions/workflows/ci.yml/badge.svg)](https://github.com/egor1729/lean-convex-geometry/actions/workflows/ci.yml)

A Lean 4 + Mathlib (`v4.36.0`) library for **metric, volumetric, and spherical convex geometry** in finite-dimensional real inner product spaces and $\mathbb{R}^n$.

It provides reusable analytic and geometric foundations complementing algebraic polyhedral libraries (such as [`Polyhedral`](https://github.com/ooovi/Polyhedral)) and supporting downstream formalizations (such as [`sphere-max-volume`](https://github.com/egor1729/sphere-max-volume)).

## Highlights

- **Support Functions & Metric Convexity:** Support calculus, Hörmander's isometric embedding, Minkowski's representation theorem, completeness of `ConvexBody E`, and the Blaschke Selection Theorem.
- **Polarity & Polytopes:** One-sided polar bodies, Bipolar Theorem, gauge–support duality, and inscribed polytope approximation.
- **Volume & Covering:** $d$-simplex volume $|\det|/d!$, half-ball bounds, Hausdorff continuity of volume, and volumetric covering/packing bounds for arbitrary norms.
- **Inequalities & Symmetrization:** $d$-dimensional Prékopa–Leindler, Brunn–Minkowski, Bieberbach's isodiametric inequality, log-concave marginals, and Minkowski / central / Steiner symmetrization.

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
