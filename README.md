# `lean-convex-geometry`

[![CI](https://github.com/egor1729/lean-convex-geometry/actions/workflows/ci.yml/badge.svg)](https://github.com/egor1729/lean-convex-geometry/actions/workflows/ci.yml)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

A Lean 4 + Mathlib (`v4.36.0`) library for metric, polyhedral, volumetric, spherical, and asymptotic convex geometry in finite-dimensional real inner product spaces and $\mathbb{R}^n$.

It focuses on analytic and geometric foundations complementing algebraic polyhedral libraries (such as [`Polyhedral`](https://github.com/ooovi/Polyhedral)) and supporting downstream formalizations (such as [`sphere-max-volume`](https://github.com/egor1729/sphere-max-volume)).

## Highlights

- **Metric & Duality (`ConvexGeom.Metric`):** Support functions, linear transport, Minkowski's representation theorem, Hörmander's isometry, Blaschke Selection Theorem, metric projection, outer normal cones, supporting hyperplanes, polar bodies, Bipolar Theorem, gauge–support duality, spherical laws of cosines/sines, dihedral angles, and spherical caps.
- **Polytopes & Combinatorial Convexity (`ConvexGeom.Polytope`):** Inscribed and spherical general-position density, vertex push-out to $S^{d-1}$, $d$-simplex volume $|\det|/d!$, Radon & Helly wrappers over Mathlib's `Convex.radon_partition` / `Convex.helly_theorem*`, Minkowski–Carathéodory, Straszewicz, Jung's theorem, Weyl–Minkowski $V \to H$ duality, simplicial facets, and radial facet-cone tiling.
- **Volume & Symmetrization (`ConvexGeom.Volume`):** Half-ball bounds, Hausdorff continuity of volume and symmetric-difference volume, polytope maximizer reductions, metric and translative covering bounds, Prékopa–Leindler, Brunn–Minkowski, Brunn's concavity principle, log-concave convolutions, covariograms, Rogers–Shephard, central intersection lemma, isodiametric inequality, Minkowski's first inequality, Euclidean isoperimetry, and Minkowski / central / Steiner symmetrization.
- **Asymptotic, Spherical & Affine Geometry (`ConvexGeom.Asymptotic`):** Spherical cone probability measure, isotropic identities, Steiner point, polar-coordinate volume formula, mean width, Gaussian width, Dual Urysohn & Urysohn inequalities, ellipsoids, Mahler/Santaló volume, Banach–Mazur distances & compactum, Fritz John's theorem, Dvoretzky–Rogers lemma, Loomis–Whitney, geometric Brascamp–Lieb & Barthe's reverse form, Ball's volume-ratio & reverse isoperimetric inequalities, Gaussian & spherical concentration, Johnson–Lindenstrauss, Dvoretzky's theorem, directional Steiner symmetrization, Santaló point, and the Blaschke–Santaló inequality.

## Build, Test & Verification

```bash
# Download precompiled Mathlib oleans
lake exe cache get

# Build the library and Comparator solution (warnings treated as errors)
lake build ConvexGeom Solution --wfail

# Run regression tests (ConvexGeomTest)
lake test

# Run Batteries environment linters on ConvexGeom
lake lint

# Verify ConvexGeom.lean imports every module in ConvexGeom/
lake exe mk_all --check --lib ConvexGeom

# Replay compiled module environments through Lean's bundled leanchecker
for f in $(find ConvexGeom/* -name '*.lean' | sort); do
  mod="${f%.lean}"; lake env leanchecker "${mod//\//.}"
done

# Run sandboxed lake comparator (Challenge.lean vs Solution.lean) with bundled external kernels
bash scripts/verify-comparator.sh            # Lean kernel + nanoda_bin + con-ron
bash scripts/verify-comparator.sh --paranoid # Lean kernel + all 5 bundled external kernels
```

CI ([`.github/workflows/ci.yml`](.github/workflows/ci.yml)) runs [`leanprover/lean-action`](https://github.com/leanprover/lean-action) (`lake build --wfail`, `lake test`, `lake lint`, `mk_all --check`, and [`leanprover-community/axiom-audit`](https://github.com/leanprover-community/axiom-audit)), per-module `leanchecker` replay, metadata schema validation, and sandboxed `lake comparator` with `nanoda_bin` and `con-ron`.

### Independent Statement Audit (`Challenge.lean` & `formalization.yaml`)

Anyone wanting to audit the library's headline statements without reading the full proof tree can inspect two root files and run `lake comparator`:

- [`Challenge.lean`](Challenge.lean) — Compact **Mathlib-only** statement surface (zero `ConvexGeom` imports) declaring 30 classical theorems across all four layers (note: `helly_theorem` wraps Mathlib's `Convex.helly_theorem_finset`), checked against [`Solution.lean`](Solution.lean) using [`comparator.json`](comparator.json) and `lake comparator`.
- [`formalization.yaml`](formalization.yaml) — Structured [`v0.4`](https://github.com/mathlib-initiative/formalization.yaml) metadata recording mathematical sources, provenance, scope, automation/review disclosures, divergences, and theorem alignment.

### Use as a Dependency

Add to `lakefile.toml` (matching `lean-toolchain`; pin a release tag such as `v4.36.0` or a commit SHA for reproducibility, or use `rev = "main"` to track development):

```toml
[[require]]
name = "lean-convex-geometry"
git = "https://github.com/egor1729/lean-convex-geometry.git"
rev = "<tag-or-commit-sha>"
```

```lean
import ConvexGeom
-- or a layer / single module, e.g. ConvexGeom.Volume.BrunnMinkowski
```

## Design Philosophy

- **Mathlib-native abstractions:** State definitions and theorems directly on Mathlib's types, measures, and metric spaces at natural generality.
- **Reusable proofs:** Prefer structural proof routes built from general lemmas over specialized machinery for a single result.
- **Standard verification:** Rely on Lean and community tooling (`--wfail`, `lake test`, `lake lint`, `mk_all`, `axiom-audit`, `leanchecker`, and sandboxed `lake comparator`) with zero `sorry` outside deliberate `Challenge.lean` Comparator holes and only the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- **Structured commits:** Keep git history readable with small, focused commits.

## Documentation, Contributing & License

- [`Challenge.lean`](Challenge.lean) & [`formalization.yaml`](formalization.yaml) — Mathlib-only statement surface and `v0.4` formalization metadata.
- [`docs/MODULES.md`](docs/MODULES.md) — Directory layout and module overview (regenerate the import graph with `lake exe graph`).
- [`docs/CONVENTIONS.md`](docs/CONVENTIONS.md) — Definitions, normalizations, proof routes, scope limits, textbook divergences, and verification setup.
- [`docs/ROADMAP.md`](docs/ROADMAP.md) — Planned mathematical targets and references.
- [`CONTRIBUTING.md`](CONTRIBUTING.md) — Contribution guidelines and local verification commands.
- Licensed under the [Apache License 2.0](LICENSE). Citation metadata is in [`CITATION.cff`](CITATION.cff).
