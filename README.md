# `lean-convex-geometry`

[![CI](https://github.com/egor1729/lean-convex-geometry/actions/workflows/ci.yml/badge.svg)](https://github.com/egor1729/lean-convex-geometry/actions/workflows/ci.yml)

A standalone Lean 4 + Mathlib library for **metric, volumetric, and spherical convex geometry** in finite-dimensional real inner product spaces and $\mathbb{R}^n$.

Inspired by classical and modern references — Keith Ball's *An Elementary Introduction to Modern Convex Geometry*, Bo'az Klartag's lecture notes on high-dimensional convex geometry, Roman Vershynin's *High-Dimensional Probability*, and Rolf Schneider's *Convex Bodies* — this repository fills foundational geometric building blocks currently absent from Mathlib. It complements algebraic/combinatorial polyhedral formalizations (such as [`Polyhedral`](https://github.com/ooovi/Polyhedral)) and serves as a reusable dependency for downstream projects (such as [`sphere-max-volume`](https://github.com/egor1729/sphere-max-volume)).

## Design Philosophy

- **Universal, Mathlib-native abstractions:** State theorems for general finite-dimensional real inner product spaces `E`, Mathlib's `ConvexBody E`, arbitrary add-Haar measures `μ`, and Mathlib's `coveringNumber` / `packingNumber` whenever natural.
- **Conceptual proofs over ad-hoc machinery:** Favor clean structural routes (e.g., Hörmander's isometry + Arzelà–Ascoli for Blaschke selection; layer-cake + Tonelli induction for Prékopa–Leindler → Brunn–Minkowski → Bieberbach's isodiametric inequality).
- **Zero-trust verification:** Zero `sorry`, zero compiler warnings, zero custom axioms — every headline theorem is checked against Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) in [`ConvexGeom/Verification/AxiomAudit.lean`](ConvexGeom/Verification/AxiomAudit.lean) and enforced by CI.

## Implemented Modules

All modules are re-exported by [`ConvexGeom.lean`](ConvexGeom.lean) and verified on Lean 4 / Mathlib `v4.36.0`.

| Module | Core Definitions & Theorems | Conceptual Route / Reference |
| --- | --- | --- |
| [`ConvexGeom/SupportFunction.lean`](ConvexGeom/SupportFunction.lean) | `bodySingleton`, `bodyClosedBall`, `supportFn`, sublinearity & Minkowski additivity (`supportFn_minkowski_add`), Hahn–Banach separation (`supportFn_le_iff_subset`, `supportFn_injective`), directional `width` & `diam_eq_sSup_width`, **Hörmander's isometric embedding** (`isometry_supportFnOnBall`), Hausdorff metric algebra (`dist_add_right`, `dist_add_le`, `dist_smul`), **Minkowski's representation theorem** (`exists_convexBody_supportFn_eq`) | Geometric & analytic Hahn–Banach + Riesz representation (Schneider §1.7–1.8) |
| [`ConvexGeom/Blaschke.lean`](ConvexGeom/Blaschke.lean) | `isClosed_range_supportFnOnBall`, completeness of Hausdorff space (`instCompleteSpaceConvexBody`), compactness of bounded families (`isCompact_subset_closedBall`, `isCompact_subset_of_isCompact`), **Blaschke Selection Theorem** (`blaschke_selection`) | Hörmander isometry + Minkowski representation + `BoundedContinuousFunction.arzela_ascoli₂` |
| [`ConvexGeom/Polarity.lean`](ConvexGeom/Polarity.lean) | One-sided geometric polar `polarBody`, `bodyPolar`, `polarBody_closedBall`, linear-image duality (`polarBody_image_continuousLinearMap`), compactness/interior duality, **Bipolar Theorem** (`polarBody_polarBody`), **Gauge–Support Duality** (`gauge_polarBody_eq_supportFn`, `supportFn_bodyPolar_eq_gauge`) | Geometric Hahn–Banach + adjoint operators + Mathlib `gauge` (Ball Lec. 1, Schneider §1.6) |
| [`ConvexGeom/Polytope.lean`](ConvexGeom/Polytope.lean) | `bodyConvexHull`, `supportFn_bodyConvexHull`, 1-Lipschitz Hausdorff stability (`hausdorffDist_convexHull_range_le`), **inscribed polytope approximation** (`exists_polytope_dist_lt`) | Finite $\varepsilon$-nets + support-function Hausdorff metric |
| [`ConvexGeom/SimplexVolume.lean`](ConvexGeom/SimplexVolume.lean) | `volume_orderSimplex`, `volume_solidSimplex`, **`d`-simplex volume `|\det| / d!`** on `Fin d → ℝ` (`volume_convexHull_simplex`) and `EuclideanSpace ℝ (Fin d)` (`volume_convexHull_simplex_euclideanSpace`) | Symmetric-group permutation tiling of $[0, 1]^d$ + unit-determinant partial-sum shear |
| [`ConvexGeom/VolumeContinuity.lean`](ConvexGeom/VolumeContinuity.lean) | `addHaar_hyperplane_eq_zero`, exact **half-ball volume** (`addHaar_halfBall`, `addHaar_le_half_ball`), upper & lower semicontinuity and **full continuity of add-Haar volume** on `ConvexBody E` (`continuous_addHaar_convexBody`, `continuous_addHaarReal_convexBody`) and vertex tuples (`continuous_addHaar_convexHull_range`) | Support-function homothety inclusion (`homothety_subset_of_dist_le`) + dominated convergence |
| [`ConvexGeom/CoveringNumbers.lean`](ConvexGeom/CoveringNumbers.lean) | Volumetric bounds for **any norm** on $\mathbb{R}^d$: `measure_le_externalCoveringNumber_mul_closedBall`, `packingNumber_mul_ball_le_measure_add_ball`, `coveringNumber_mul_ball_le_measure_add_ball`, and unit-ball bounds `inv_pow_le_externalCoveringNumber_closedBall` ($(1/\varepsilon)^d$), `packingNumber_closedBall_le` ($(2/\varepsilon + 1)^d$), `coveringNumber_closedBall_le_three_div` ($(3/\varepsilon)^d$) | Add-Haar scaling + Mathlib `Metric.coveringNumber` / `packingNumber` (Vershynin Prop. 4.2.12–Cor. 4.2.13, Ball Lec. 2) |
| [`ConvexGeom/BrunnMinkowski.lean`](ConvexGeom/BrunnMinkowski.lean) | 1D Brunn–Minkowski (`brunn_minkowski_one_dim`), full **$d$-dimensional Prékopa–Leindler** for arbitrary measurable `E → ℝ≥0∞` (`prekopa_leindler_one_dim`, `prekopa_leindler_pi`, `prekopa_leindler`), multiplicative & additive **Brunn–Minkowski** (`brunn_minkowski_mul_compact`, `brunn_minkowski_compact`, `brunn_minkowski_convexBody`), **Bieberbach's Isodiametric Inequality** (`isodiametric_inequality`), **Prékopa's log-concavity of marginals** (`logConcave_marginal_prod`) | Layer-cake + monotone convergence + Tonelli induction + orthonormal transfer (Ball Lec. 5, Gardner §7) |
| [`ConvexGeom/Symmetrization.lean`](ConvexGeom/Symmetrization.lean) | Hyperplane reflection `reflectHyperplane` / `reflectBody`, **Minkowski symmetrization** (`minkowskiSymm`, `supportFn_minkowskiSymm`, `reflectBody_minkowskiSymm`, `volume_le_volume_minkowskiSymm`, `diam_minkowskiSymm_le`), **central symmetrization** (`centralSymm`, `volume_le_volume_centralSymm`), **Steiner symmetrization** on `ℝ × E` (`steinerSymm`, `convex_steinerSymm`, `isCompact_steinerSymm`, exact volume preservation `volume_steinerSymm`, Euclidean distance bound `steinerSymm_dist_le_diam`) | Brunn–Minkowski + Fubini fiber-interval symmetrization (Klartag Lec. 2) |

## Next Targets Roadmap

Harder or more specialized theorems are intentionally stashed until their shared building blocks are ready, keeping each addition modular and conceptually crisp:

### Near-Term Building Blocks
- **Brunn's Concavity Principle & Log-Concave Convolutions:** $1/(d-1)$-concavity of parallel hyperplane sections of convex bodies and preservation of log-concavity under convolution (direct corollaries of `prekopa_leindler` / `brunn_minkowski_compact`).
- **Euclidean Isoperimetric Inequality (Minkowski Content Form):** Lower bound on outer Minkowski surface area $\liminf_{\varepsilon \to 0^+} \frac{\mathrm{vol}(K + \varepsilon B) - \mathrm{vol}(K)}{\varepsilon}$ directly from `brunn_minkowski_compact`.
- **Nearest-Point Projection & Outer Normal Cones:** Metric projection onto `ConvexBody E` (wrapping Mathlib's `exists_norm_eq_iInf_of_complete_convex`), 1-Lipschitz contraction, and supporting hyperplanes.
- **Density of General Position in $\mathbb{R}^d$:** Small perturbations putting any finite point configuration in general position (affine independence of every $(d+1)$-subset), useful for polytope perturbation arguments.
- **Banach–Mazur Distance & Symmetric Bodies:** Basic metric properties and compactness of the Banach–Mazur compactum via `blaschke_selection` (once Fritz John's theorem is in place).
- **Mean Width & Gaussian Width:** Basic calculus of $w(K)$ and Urysohn's inequality (linking mean width to volume via Minkowski symmetrization / Blaschke–Santaló).

### Deeper Classical Theorems & Downstream Targets
- **Fritz John's Theorem (Ball Lectures 3–4):** Existence/uniqueness of the maximal-volume inscribed ellipsoid and John's decomposition of the identity.
- **Blaschke–Santaló Inequality (Klartag Lecture 5):** $\mathrm{vol}(K)\,\mathrm{vol}(K^\circ) \le \mathrm{vol}(B_2^n)^2$ for centrally symmetric convex bodies via Steiner symmetrization (`steinerSymm`) + polarity (`polarBody`).
- **Brascamp–Lieb & Ball's Reverse Isoperimetric Inequality (Ball Lecture 6):** Functional generalization of Loomis–Whitney and volume ratio bounds.
- **Concentration of Measure, Johnson–Lindenstrauss & Dvoretzky (Ball Lectures 7–9, Klartag Lectures 3–4, Vershynin Ch. 5–9):** Spherical/Gaussian concentration and high-dimensional almost-Euclidean sections.
- **3D Spherical Geometry & Polytope Facet-Cone Tilings (for `sphere-max-volume`):** Dihedral angles & wedges, spherical laws of sines/cosines, Girard's theorem (solid angle = spherical excess), conic Carathéodory, facet-cone tiling of $\mathbb{R}^3$, and 3D Euler's formula.

## Quick Start

```bash
lake exe cache get
lake build ConvexGeom --wfail
lake env lean ConvexGeom/Verification/AxiomAudit.lean
```

## Using `ConvexGeom` in Another Lean 4 Project

Add `lean-convex-geometry` as a dependency in your project's `lakefile.toml` (matching the Lean/Mathlib toolchain in `lean-toolchain`):

```toml
[[require]]
name = "lean-convex-geometry"
git = "https://github.com/egor1729/lean-convex-geometry.git"
rev = "main" # or pin to a specific commit / tag
```

Then import the whole library or individual modules:

```lean
import ConvexGeom
-- or selectively:
import ConvexGeom.BrunnMinkowski
import ConvexGeom.Blaschke
```
