# Roadmap & Contribution Guide

Planned directions and contribution guidelines for `lean-convex-geometry`.

## Contribution Standards

- **General building blocks first:** State definitions and theorems at natural Mathlib generality rather than building single-use machinery.
- **Structural proofs:** Reuse existing layers; if a theorem needs heavy specialized scaffolding, extract the missing general layer first or defer it here.
- **Focused commits:** Keep commits small and cohesive (one module, lemma group, or doc change per commit).
- **Verification:** Run `bash scripts/verify.sh` before pushing, and add new headline theorems to [`ConvexGeom/Verification/AxiomAudit.lean`](../ConvexGeom/Verification/AxiomAudit.lean).
- **Docs in sync:** Update [`MODULES.md`](MODULES.md) when adding or restructuring modules.

---

## Near-Term $n$-Dimensional Targets

- **Polytope Face Lattice & Triangulation** *(Gruber; Ziegler; `Polytope.Faces`)*
  - Ridge / diamond adjacency (every $(d-2)$-ridge lies in exactly two facets), $H \to V$ duality, and pulling / fan triangulation of non-simplicial facets.
- **Spherical Volume, Wedges & Solid Angles** *(`Metric.SphericalTrig`, `Asymptotic.SphericalIntegration`)*
  - Surface measure of spherical caps and wedges, and solid angles of polyhedral cones.
- **Centroid, Isotropic Position & Grünbaum's Inequality** *(Brazitikos et al., Ch. 1–2; Klartag & Lehec; `Volume.BrunnConcavity`, `Asymptotic.BanachMazur`)*
  - Barycenter, covariance operator, isotropic position, isotropic constant $L_K$, and Grünbaum's halfspace inequality $\mathrm{vol}(K \cap H^+) \ge \left(\frac{d}{d+1}\right)^d \mathrm{vol}(K)$.
- **Covering–Width Bridges** *(Vershynin, Ch. 7; Artstein-Avidan–Giannopoulos–Milman, Ch. 4 & 7; `Asymptotic.GaussianConcentration`, `Volume.CoveringNumbers`)*
  - Sudakov and dual Sudakov minoration connecting covering numbers to `gaussianWidth`.
- **Functional Polarity & Legendre–Fenchel Duality** *(Artstein-Avidan–Giannopoulos–Milman, Ch. 1–2; `Metric.Polarity`, `Volume.BrunnMinkowski`)*
  - Legendre transform, infimal convolution, and polarity of log-concave functions.
- **Combinatorial Convexity Extensions** *(Gruber; Schneider, Ch. 1; `Polytope.Combinatorial`)*
  - Kirchberger's theorem, colorful Carathéodory, and Tverberg-type refinements.
- **Dual Section & Coordinate Projection Bounds** *(Ball, Lec. 6; Schneider, §9.3; `Volume.BrunnConcavity`, `Asymptotic.BrascampLieb`)*
  - Meyer's dual section inequality and general $k$-dimensional section/projection inequalities beyond `loomis_whitney`.
- **Borell's Lemma & Reverse Hölder Inequalities** *(Brazitikos et al., Ch. 2; Artstein-Avidan–Giannopoulos–Milman, Ch. 2)*
  - Exponential tail decay for log-concave measures, Kahane–Khintchine estimates, and $\psi_1$ bounds.
- **Mixed Volumes, Quermassintegrals & Steiner's Formula** *(Schneider, Ch. 4–5; Gruber)*
  - Polynomial expansion of $\mathrm{vol}(\sum_i \lambda_i K_i)$, quermassintegrals $W_k(K)$, Kubota's formula, and identification of `minkowskiSurfaceArea` with the mixed-volume derivative.

---

## Deeper $n$-Dimensional Classical Theorems

- **Bourgain–Milman Reverse Santaló Inequality** *(Klartag, Lec. 5; Artstein-Avidan–Giannopoulos–Milman, Ch. 8)* — Reverse Mahler volume bound $\mathcal{P}^*(K) \ge c^d\,\mathrm{vol}(B_2^d)^2$ complementing `Asymptotic.BlaschkeSantalo`.
- **Milman's $M$-Ellipsoid & Quotient-of-Subspace (QS) Theorem** *(Artstein-Avidan–Giannopoulos–Milman, Ch. 7–8; Pisier)* — Covering-number ellipsoids, $M$-position, and Milman's reverse Brunn–Minkowski inequality.
- **Aleksandrov–Fenchel & Surface Area Measures** *(Schneider, Ch. 7–8; Gruber)* — Aleksandrov–Fenchel inequalities, Minkowski's existence theorem, and Busemann–Petty / Shephard problems.
- **Log-Concave Isoperimetry, Localization & Thin-Shell** *(Klartag & Lehec; Brazitikos et al.)* — Needle decomposition, Cheeger / KLS bounds, thin-shell concentration, and slicing-problem interfaces.

---

## Downstream Specialized Targets

- **3D Spherical Geometry & Polyhedral Topology** *([`sphere-max-volume`](https://github.com/egor1729/sphere-max-volume))* — 3D Girard's theorem (solid angle = spherical excess), 3D tangent-cone cyclic angle sums, and 3D Euler's formula $V - E + F = 2$.

---

## References

- Keith Ball, *An Elementary Introduction to Modern Convex Geometry* (MSRI Publications 31)
- Bo'az Klartag & Joseph Lehec, *Isoperimetric Inequalities in High-Dimensional Convex Sets*
- Shiri Artstein-Avidan, Apostolos Giannopoulos & Vitali D. Milman, *Asymptotic Geometric Analysis, Parts I & II*
- Silouanos Brazitikos, Apostolos Giannopoulos, Petros Valettas & Beatrice-Helen Vritsiou, *Geometry of Isotropic Convex Bodies*
- Roman Vershynin, *High-Dimensional Probability*
- Guillaume Aubrun & Stanisław J. Szarek, *Alice and Bob Meet Banach*
- Rolf Schneider, *Convex Bodies: The Brunn–Minkowski Theory*
- Peter M. Gruber, *Convex and Discrete Geometry*
- Günter M. Ziegler, *Lectures on Polytopes*
- Michel Ledoux, *The Concentration of Measure Phenomenon*
