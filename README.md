# `lean-convex-geometry`

[![CI](https://github.com/egor1729/lean-convex-geometry/actions/workflows/ci.yml/badge.svg)](https://github.com/egor1729/lean-convex-geometry/actions/workflows/ci.yml)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

A Lean 4 + Mathlib (`v4.36.0`) library for metric, volumetric, and spherical convex geometry in finite-dimensional real inner product spaces and $\mathbb{R}^n$.

It focuses on analytic and geometric foundations complementing algebraic polyhedral libraries (such as [`Polyhedral`](https://github.com/ooovi/Polyhedral)) and supporting downstream formalizations (such as [`sphere-max-volume`](https://github.com/egor1729/sphere-max-volume)).

## Highlights

- **Metric & Duality (`ConvexGeom.Metric`):** Support functions, linear transport, Minkowski's representation theorem, Hörmander's isometry, Blaschke Selection Theorem, metric projection, outer normal cones, supporting hyperplanes, polar bodies, Bipolar Theorem, gauge–support duality, spherical laws of cosines/sines, dihedral angles, and spherical caps.
- **Polytopes & Combinatorial Convexity (`ConvexGeom.Polytope`):** Inscribed and spherical general-position density, vertex push-out to $S^{d-1}$, $d$-simplex volume $|\det|/d!$, Radon, Helly, Minkowski–Carathéodory, Straszewicz, Jung's theorem, Weyl–Minkowski $V \to H$ duality, simplicial facets, and radial facet-cone tiling.
- **Volume & Symmetrization (`ConvexGeom.Volume`):** Half-ball bounds, Hausdorff continuity of volume and symmetric-difference volume, polytope maximizer reductions, metric and translative covering bounds, Prékopa–Leindler, Brunn–Minkowski, Brunn's concavity principle, log-concave convolutions, covariograms, Rogers–Shephard, central intersection lemma, isodiametric inequality, Minkowski's first inequality, Euclidean isoperimetry, and Minkowski / central / Steiner symmetrization.
- **Asymptotic, Spherical & Affine Geometry (`ConvexGeom.Asymptotic`):** Spherical cone probability measure, isotropic identities, Steiner point, polar-coordinate volume formula, mean width, Gaussian width, Dual Urysohn & Urysohn inequalities, ellipsoids, Mahler/Santaló volume, Banach–Mazur distances & compactum, Fritz John's theorem, Dvoretzky–Rogers lemma, Loomis–Whitney, geometric Brascamp–Lieb & Barthe's reverse form, Ball's volume-ratio & reverse isoperimetric inequalities, Gaussian & spherical concentration, Johnson–Lindenstrauss, Dvoretzky's theorem, directional Steiner symmetrization, Santaló point, and the Blaschke–Santaló inequality.

## Quick Start & Tiered Verification

```bash
lake exe cache get

# Tier 0–1 (fast inner loop for development / agents: static checks + changed modules only)
bash scripts/verify-fast.sh --static
bash scripts/verify-fast.sh [Module ...]

# Tier 2 (full library build, checks, environment-wide axiom audit, 300-theorem snapshot)
bash scripts/verify.sh

# Tier 3 (trustless sandboxed multi-kernel Comparator check: Challenge.lean vs Solution.lean)
bash scripts/verify-comparator.sh            # Lean kernel + nanoda_bin + con-ron
bash scripts/verify-comparator.sh --paranoid # Lean kernel + all 5 bundled external kernels
```

To build just the library:

```bash
lake build ConvexGeom --wfail
```

### Independent Statement Audit (`Challenge.lean` & `formalization.yaml`)

Anyone wanting to verify the library's headline claims without reading the full proof tree only needs to inspect two small root files and run Comparator:

- [`Challenge.lean`](Challenge.lean) — Compact (~420-line) **Mathlib-only** statement surface (zero `ConvexGeom` imports) declaring 30 landmark theorems across all four layers, verified against [`Solution.lean`](Solution.lean) using [`comparator.json`](comparator.json) and `lake comparator`.
- [`formalization.yaml`](formalization.yaml) — Structured [`v0.4`](https://github.com/mathlib-initiative/formalization.yaml) metadata recording mathematical sources, provenance, scope, automation/review disclosures, divergences, and theorem alignment.

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
- **Clean verification:** Maintain zero `sorry` (outside deliberate `Challenge.lean` Comparator holes), zero warnings (`--wfail`), standard-axiom verification, and sandboxed multi-kernel Comparator checks.
- **Structured commits:** Keep git history readable with small, focused commits.

## Documentation & License

- [`Challenge.lean`](Challenge.lean) & [`formalization.yaml`](formalization.yaml) — Mathlib-only statement surface and `v0.4` formalization metadata.
- [`docs/MODULES.md`](docs/MODULES.md) — Directory layout, dependency graph, and theorem index.
- [`docs/CONVENTIONS.md`](docs/CONVENTIONS.md) — Definitions, normalizations, proof routes, textbook divergences, and verification tiers.
- [`docs/ROADMAP.md`](docs/ROADMAP.md) — Planned targets, references, and contribution guidelines.
- Licensed under the [Apache License 2.0](LICENSE). Citation metadata is in [`CITATION.cff`](CITATION.cff).
