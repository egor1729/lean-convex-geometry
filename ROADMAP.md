# Roadmap & Contribution Guide

This document outlines planned directions for `lean-convex-geometry` and serves as a shared guide for both human contributors and automated coding agents.

## Contribution Standards

- **Universal building blocks first:** State definitions and theorems at natural Mathlib generality (arbitrary finite-dimensional real inner product spaces, `ConvexBody E`, general add-Haar measures, etc.) rather than building ad-hoc machinery for a single theorem.
- **Conceptual proof routes:** Prefer clean structural proofs that reuse existing lemmas. If a target requires heavy specialized scaffolding, extract the missing general layer first or defer the target here.
- **Structured commits:** Keep commits small, focused, and self-contained (e.g., one module, a cohesive group of lemmas, or a single documentation/CI change per commit). Avoid large multi-module dumps.
- **Clean verification:** Every change must pass `lake build ConvexGeom --wfail` with zero `sorry` and zero warnings, and new headline theorems should be registered in [`ConvexGeom/Verification/AxiomAudit.lean`](ConvexGeom/Verification/AxiomAudit.lean).

## Near-Term Building Blocks

Well-scoped additions that build directly on existing modules:

- **Brunn's Concavity Principle & Log-Concave Convolutions** *(builds on `BrunnMinkowski`)*
  - $1/(d-1)$-concavity of parallel hyperplane sections of convex bodies.
  - Preservation of log-concavity under convolution of measurable densities.
- **Euclidean Isoperimetric Inequality (Minkowski Content Form)** *(builds on `BrunnMinkowski`, `VolumeContinuity`)*
  - Lower bound on outer Minkowski surface area $\liminf_{\varepsilon \to 0^+} \frac{\mathrm{vol}(K + \varepsilon B) - \mathrm{vol}(K)}{\varepsilon}$ via additive Brunn–Minkowski.
- **Nearest-Point Projection & Outer Normal Cones** *(builds on `SupportFunction`, Mathlib's `exists_norm_eq_iInf_of_complete_convex`)*
  - Metric projection onto `ConvexBody E`, 1-Lipschitz contraction, and characterization of supporting hyperplanes / outer normal cones.
- **Density of General Position in $\mathbb{R}^d$** *(builds on `Polytope`)*
  - Arbitrarily small perturbations placing any finite point configuration in general position (affine independence of every $(d+1)$-subset).
- **Mean Width & Gaussian Width** *(builds on `SupportFunction`, `Symmetrization`)*
  - Basic calculus of mean width $w(K)$ and Gaussian width; Urysohn's inequality once spherical/polar links are ready.
- **Banach–Mazur Distance & Symmetric Bodies** *(builds on `Polarity`, `Blaschke`)*
  - Metric structure on equivalence classes of origin-symmetric convex bodies (preparing for compactness of the Banach–Mazur compactum via Fritz John's theorem).

## Deeper Classical Theorems & Downstream Targets

Larger milestones requiring multiple coordinated building blocks:

- **Fritz John's Theorem** *(Ball, Lectures 3–4)* — Existence and uniqueness of the maximal-volume inscribed ellipsoid and John's decomposition of the identity.
- **Blaschke–Santaló Inequality** *(Klartag, Lecture 5)* — $\mathrm{vol}(K)\,\mathrm{vol}(K^\circ) \le \mathrm{vol}(B_2^n)^2$ for origin-symmetric convex bodies via `steinerSymm` and `polarBody`.
- **Brascamp–Lieb & Ball's Reverse Isoperimetric Inequality** *(Ball, Lecture 6)* — Functional Loomis–Whitney / Brascamp–Lieb inequalities and volume ratio bounds.
- **Concentration of Measure, Johnson–Lindenstrauss & Dvoretzky** *(Ball, Lectures 7–9; Klartag, Lectures 3–4; Vershynin, Ch. 5–9)* — Spherical and Gaussian concentration, random projections, and almost-Euclidean sections.
- **3D Spherical Geometry & Polytope Facet-Cone Tilings** *(downstream support for [`sphere-max-volume`](https://github.com/egor1729/sphere-max-volume))* — Dihedral angles and wedges, spherical laws of sines/cosines, Girard's theorem (solid angle = spherical excess), conic Carathéodory, facet-cone tiling of $\mathbb{R}^3$, and 3D Euler's formula.

## Reference Literature

- Keith Ball, *An Elementary Introduction to Modern Convex Geometry*
- Bo'az Klartag, *High-Dimensional Convex Geometry* (ETH / Weizmann lecture notes)
- Roman Vershynin, *High-Dimensional Probability*
- Rolf Schneider, *Convex Bodies: The Brunn–Minkowski Theory*
