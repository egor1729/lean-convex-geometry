# Roadmap & Contribution Guide

This document outlines planned directions for `lean-convex-geometry` and serves as a shared guide for both human contributors and automated coding agents.

## Contribution Standards

- **Universal building blocks first:** State definitions and theorems at natural Mathlib generality (arbitrary finite-dimensional real inner product spaces, `ConvexBody E`, general add-Haar measures, etc.) rather than building ad-hoc machinery for a single theorem.
- **Conceptual proof routes:** Prefer clean structural proofs that reuse existing lemmas. If a target requires heavy specialized scaffolding, extract the missing general layer first or defer the target here.
- **Structured commits:** Keep commits small, focused, and self-contained (e.g., one module, a cohesive group of lemmas, or a single documentation/CI change per commit). Avoid large multi-module dumps.
- **Clean verification:** Every change must pass `lake build ConvexGeom --wfail` with zero `sorry` and zero warnings, and new headline theorems should be registered in [`ConvexGeom/Verification/AxiomAudit.lean`](ConvexGeom/Verification/AxiomAudit.lean).
- **Keep docs in sync:** Update [`MODULES.md`](MODULES.md) when adding or restructuring library modules.

---

## Near-Term $n$-Dimensional Building Blocks

Well-scoped general-dimension modules that build directly on the existing library:

- **Steiner Point & Minkowski Valuations** *(Schneider, Ch. 1 & 6; builds on `SphericalIntegration`, `SupportFunction`)*
  - Steiner point $s(K) = d \int_{S^{d-1}} h_K(u)\,u\,d\sigma(u)$ via `sphereProb`.
  - Minkowski additivity, rigid-motion equivariance, $s(K) \in K$, and Lipschitz continuity in the Hausdorff metric.
- **Centroid, Isotropic Position & Grünbaum's Inequality** *(Brazitikos–Giannopoulos–Valettas–Vritsiou, Ch. 1–2; Klartag & Lehec; builds on `BrunnConcavity`, `BanachMazur`)*
  - Barycenter, covariance operator, affine reduction to isotropic position, and isotropic constant $L_K$.
  - Grünbaum's halfspace theorem $\mathrm{vol}(K \cap H^+) \ge \left(\frac{d}{d+1}\right)^d \mathrm{vol}(K) \ge e^{-1}\mathrm{vol}(K)$ via Brunn's concavity principle.
- **Gaussian Width & Covering–Width Bridges** *(Vershynin, Ch. 7; Artstein-Avidan–Giannopoulos–Milman, Ch. 4 & 7; builds on `SphericalIntegration`, `CoveringNumbers`)*
  - Gaussian mean width $w_G(K) = \mathbb{E}\sup_{x \in K}\langle x, g\rangle$ and its exact proportionality to spherical `meanWidth`.
  - Sudakov and dual Sudakov minoration interfaces linking covering numbers and Gaussian/mean width.
- **Functional Polarity & Legendre–Fenchel Duality** *(Artstein-Avidan–Giannopoulos–Milman, Ch. 1–2; builds on `Polarity`, `BrunnMinkowski`)*
  - Legendre transform $\mathcal{L}f$, infimal convolution, and polarity of log-concave functions $e^{-\varphi}$.
- **Combinatorial Convexity Bridges: Helly, Jung & Kirchberger** *(Gruber; Schneider, Ch. 1; builds on `SupportFunction`, `Projection`, Mathlib's `Radon` & `Caratheodory`)*
  - Finite-dimensional Helly's theorem, Jung's circumradius theorem $R(K) \le \sqrt{\frac{d}{2(d+1)}}\,\mathrm{diam}(K)$, and quantitative Helly-type variants.
- **Loomis–Whitney & Coordinate Section/Projection Bounds** *(Ball, Lecture 6; Schneider, §9.3; builds on `BrunnConcavity`, `BrunnMinkowski`)*
  - General $d$-dimensional Loomis–Whitney inequality $\mathrm{vol}_d(K)^{d-1} \le \prod_{i=1}^d \mathrm{vol}_{d-1}(P_{e_i^\perp} K)$ via Hölder induction, plus Meyer's dual section inequality.
- **Borell's Lemma & Reverse Hölder Inequalities for Log-Concave Laws** *(Brazitikos et al., Ch. 2; Artstein-Avidan–Giannopoulos–Milman, Ch. 2; builds on `BrunnMinkowski`, `BrunnConcavity`)*
  - Exponential tail decay (Borell's lemma), Kahane–Khintchine reverse Hölder estimates for seminorms, and $\psi_1$ bounds for linear functionals.
- **Mixed Volumes, Quermassintegrals & Steiner's Formula** *(Schneider, Ch. 4–5; Gruber; builds on `Polytope`, `Isoperimetric`, `VolumeContinuity`)*
  - Polynomial expansion of $\mathrm{vol}(\sum_i \lambda_i K_i)$, intrinsic volumes / quermassintegrals $W_k(K)$, and Kubota's projection formula.

---

## Deeper $n$-Dimensional Classical Theorems

Major milestones combining multiple building blocks across convex geometry and asymptotic geometric analysis:

- **Fritz John's Theorem & Banach–Mazur Compactum** *(Ball, Lectures 3–4; Artstein-Avidan–Giannopoulos–Milman, Ch. 2; builds on `BanachMazur`, `Blaschke`, `Projection`)* — Existence and uniqueness of the maximal-volume inscribed ellipsoid, John's decomposition of the identity, $d_{\mathrm{BM}}(K, B_2^d) \le \sqrt{d}$ (symmetric) / $d$ (general), and compactness of the Banach–Mazur space.
- **Blaschke–Santaló, Urysohn & Bourgain–Milman** *(Klartag, Lecture 5; Artstein-Avidan–Giannopoulos–Milman, Ch. 1 & 8; builds on `Symmetrization`, `Polarity`, `SphericalIntegration`, `BanachMazur`)* — $\mathcal{P}(K) \le \mathrm{vol}(B_2^d)^2$ via Steiner symmetrization and the Santaló point (immediately giving Urysohn's inequality via `urysohn_of_santalo`), and the Bourgain–Milman reverse Santaló bound.
- **Brascamp–Lieb & Ball's Reverse Isoperimetric Inequality** *(Ball, Lecture 6; Artstein-Avidan–Giannopoulos–Milman, Ch. 2)* — Geometric Brascamp–Lieb and Barthe's reverse form, volume-ratio bounds, and minimal surface-area positions.
- **Concentration of Measure, Johnson–Lindenstrauss & Dvoretzky** *(Ball, Lectures 7–9; Vershynin, Ch. 5–9; Aubrun–Szarek, Ch. 3–5; Ledoux)* — Lévy spherical isoperimetry and Gaussian concentration, random projections (JL), Milman's $M$-ellipsoid / quotient-of-subspace theorem, and Dvoretzky's theorem on almost-Euclidean sections.
- **Aleksandrov–Fenchel & Surface Area Measures** *(Schneider, Ch. 7–8; Gruber)* — Aleksandrov–Fenchel mixed-volume inequalities, Minkowski's existence theorem for surface area measures, and Busemann–Petty / Shephard projection-section problems.
- **Log-Concave Isoperimetry, Localization & Thin-Shell** *(Klartag & Lehec; Brazitikos et al.)* — Needle decomposition / localization, Cheeger and KLS isoperimetric bounds, thin-shell concentration, and slicing-problem interfaces.

---

## Downstream Specialized Targets

- **3D Spherical Geometry & Polytope Facet-Cone Tilings** *(downstream support for [`sphere-max-volume`](https://github.com/egor1729/sphere-max-volume))* — Dihedral angles and wedges, spherical laws of sines/cosines, Girard's theorem (solid angle = spherical excess), conic Carathéodory, facet-cone tiling of $\mathbb{R}^3$, and 3D Euler's formula.

---

## Reference Literature

- Keith Ball, *An Elementary Introduction to Modern Convex Geometry* (MSRI Publications 31)
- Bo'az Klartag & Joseph Lehec, *Isoperimetric Inequalities in High-Dimensional Convex Sets* (lecture notes)
- Shiri Artstein-Avidan, Apostolos Giannopoulos & Vitali D. Milman, *Asymptotic Geometric Analysis, Parts I & II*
- Silouanos Brazitikos, Apostolos Giannopoulos, Petros Valettas & Beatrice-Helen Vritsiou, *Geometry of Isotropic Convex Bodies*
- Roman Vershynin, *High-Dimensional Probability*
- Guillaume Aubrun & Stanisław J. Szarek, *Alice and Bob Meet Banach*
- Rolf Schneider, *Convex Bodies: The Brunn–Minkowski Theory*
- Peter M. Gruber, *Convex and Discrete Geometry*
- Michel Ledoux, *The Concentration of Measure Phenomenon*
