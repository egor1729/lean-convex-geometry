# `lean-convex-geometry`

A standalone Lean 4 + Mathlib library for **metric, volumetric, and spherical convex geometry** in $\mathbb{R}^n$ and $\mathbb{R}^3$.

Designed to complement algebraic/combinatorial polyhedral theory efforts (such as [`Polyhedral`](https://github.com/ooovi/Polyhedral)) and to serve as a reusable foundation for downstream geometric optimization projects (such as [`sphere-max-volume`](https://github.com/egor1729/sphere-max-volume)).

## Roadmap

- **Stage 1 — Support Functions & Simplex Volumes:** Support function $h_K(u) = \sup_{x \in K} \langle x, u \rangle$ for `ConvexBody`, sublinearity, Minkowski additivity, and $d$-simplex volume $|\det|/d!$ in `EuclideanSpace ℝ (Fin d)`.
- **Stage 2 — Stability & Metric Convexity:** Half-ball bounds, lower semicontinuity of `volume (convexHull ℝ S)`, density of general position, Blaschke selection.
- **Stage 3 — 3D Spherical Geometry:** Dihedral angles & wedges, spherical triangles, laws of sines/cosines, Girard's theorem (solid angle = spherical excess).
- **Stage 4 — Polytope Facet-Cone Tilings:** Conic Carathéodory, facet-cone tiling of $\mathbb{R}^3$, vertex angle balance, and Euler's formula.

## Quick Start

```bash
lake exe cache get
lake build ConvexGeom
```

## Using `ConvexGeom` in Another Lean 4 Project

Add `lean-convex-geometry` as a dependency in your project's `lakefile.toml` (using the same Lean/Mathlib version in `lean-toolchain`):

```toml
[[require]]
name = "lean-convex-geometry"
git = "https://github.com/egor1729/lean-convex-geometry.git"
rev = "main" # or pin to a specific commit / tag
```

Then import any module in Lean:

```lean
import ConvexGeom.SupportFunction
```
