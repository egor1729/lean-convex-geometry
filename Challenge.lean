/-
Copyright (c) 2026 Yegor Gorodzha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yegor Gorodzha
-/
module

public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

public section

/-!
# Landmark Convex Geometry Statements (`Challenge`)

This module is the compact, trusted statement surface audited by `lake comparator` against
`Solution.lean` (see `comparator.json`). It imports **only Lean core and Mathlib** (no modules from
`ConvexGeom`) and states 30 landmark theorems spanning all four layers of `lean-convex-geometry`:

1. **Metric & Duality:** Blaschke Selection Theorem, Bipolar Theorem, Supporting Hyperplane Theorem.
2. **Polytopes & Combinatorial Convexity:** $d$-Simplex Volume, Helly's Theorem,
   Minkowski–Carathéodory (finite-dimensional Krein–Milman), Jung's Circumradius Theorem,
   Weyl–Minkowski $V \to H$ Duality.
3. **Volume & Isoperimetry:** Prékopa–Leindler Inequality, Brunn–Minkowski Inequality,
   Bieberbach's Isodiametric Inequality, Rogers–Shephard Inequality, Euclidean Isoperimetric
   Inequality.
4. **Asymptotic Convex Geometry (Ball's Lectures):** Fritz John's Theorem (general and symmetric),
   Loomis–Whitney Inequality, Rank-1 Geometric Brascamp–Lieb and Barthe's Reverse Brascamp–Lieb
   Inequalities, Ball's Volume Ratio Theorems (symmetric and general), Ball's Reverse Isoperimetric
   Inequalities (symmetric and general), Gaussian and Spherical Concentration for Lipschitz
   Functions, Johnson–Lindenstrauss Lemma, Dvoretzky's Theorem, Blaschke–Santaló Inequalities
   (general and symmetric), Dual Urysohn Inequality, and Urysohn's Inequality.

The `sorry` placeholders below are deliberate Comparator holes proved in `Solution.lean`.
-/

namespace ConvexGeomChallenge

open MeasureTheory
open scoped ENNReal NNReal Pointwise RealInnerProductSpace

/-! ### Minimal Auxiliary Definitions (Not Yet in Mathlib) -/

/-- Lower outer Minkowski content (outer Minkowski surface area) of `K ⊆ E`:
$$\liminf_{t \to 0^+} \frac{\mathrm{vol}(K + t\,\overline{B}(0, 1)) - \mathrm{vol}(K)}{t}.$$ -/
@[expose]
noncomputable def minkowskiSurfaceArea {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (K : Set E) : ℝ≥0∞ :=
  Filter.liminf
    (fun t : ℝ => (volume (K + t • Metric.closedBall (0 : E) 1) - volume K) / ENNReal.ofReal t)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))

/-- Normalized rotation-invariant probability measure on the unit sphere `S^{d-1} ⊆ E`,
obtained by normalizing Mathlib's spherical cone measure `volume.toSphere`. -/
@[expose]
noncomputable def sphereProb {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    Measure (Metric.sphere (0 : E) 1) :=
  ((volume : Measure E).toSphere Set.univ)⁻¹ • (volume : Measure E).toSphere

/-- Half mean width of a convex body `K : ConvexBody E`:
$$w(K) = \int_{S^{d-1}} \sup_{x \in K} \langle x, u \rangle\,d\sigma(u),$$
normalized so that `meanWidth (closedBall c r) = r` (half the classical mean breadth). -/
@[expose]
noncomputable def meanWidth {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (K : ConvexBody E) : ℝ :=
  ∫ u : Metric.sphere (0 : E) 1,
    sSup ((fun x : E => ⟪x, u.1⟫) '' (K : Set E)) ∂(sphereProb (E := E))

/-! ### 1. Metric & Duality -/

/-- **Blaschke Selection Theorem:** every sequence of convex bodies contained in a compact set `C`
has a Hausdorff-convergent subsequence with limit in `C`. -/
theorem blaschke_selection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {C : Set E} (hC : IsCompact C) (K : ℕ → ConvexBody E)
    (hK : ∀ n, (K n : Set E) ⊆ C) :
    ∃ K₀ : ConvexBody E, (K₀ : Set E) ⊆ C ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Filter.Tendsto (K ∘ φ) Filter.atTop (nhds K₀) := by
  sorry

/-- **Bipolar Theorem:** for every closed convex set `K ⊆ E` containing `0`, the bipolar
`(K°)° = {z | ∀ y, (∀ x ∈ K, ⟪x, y⟫ ≤ 1) → ⟪y, z⟫ ≤ 1}` equals `K`. -/
theorem bipolar_theorem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {K : Set E} (hconv : Convex ℝ K) (hclosed : IsClosed K) (h0 : (0 : E) ∈ K) :
    {z : E | ∀ y ∈ {w : E | ∀ x ∈ K, ⟪x, w⟫ ≤ 1}, ⟪y, z⟫ ≤ 1} = K := by
  sorry

/-- **Supporting Hyperplane Theorem:** at every frontier point `y` of a convex body `K`, there is a
unit outward normal `u` (`‖u‖ = 1`) such that `⟪x, u⟫ ≤ ⟪y, u⟫` for all `x ∈ K`. -/
theorem supporting_hyperplane {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : ConvexBody E) {y : E} (hy : y ∈ frontier (K : Set E)) :
    ∃ u : E, ‖u‖ = 1 ∧ ∀ x ∈ (K : Set E), ⟪x, u⟫ ≤ ⟪y, u⟫ := by
  sorry

/-! ### 2. Polytopes & Combinatorial Convexity -/

/-- **$d$-Simplex Volume Formula:** the Lebesgue volume of the convex hull of `d + 1` points
`v : Fin (d + 1) → (Fin d → ℝ)` equals `|det (v j.succ - v 0)| / d!`. -/
theorem simplex_volume {d : ℕ} (v : Fin (d + 1) → (Fin d → ℝ)) :
    volume (convexHull ℝ (Set.range v)) =
      ENNReal.ofReal (|(Matrix.of fun i j : Fin d =>
        v j.succ i - v 0 i).det| / (d.factorial : ℝ)) := by
  sorry

/-- **Helly's Theorem:** if a finite family of at least `d + 1` convex bodies in a `d`-dimensional
space has the property that every `d + 1` of them intersect, then all of them intersect. -/
theorem helly_theorem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (F : Finset (ConvexBody E))
    (hcard : Module.finrank ℝ E + 1 ≤ F.card)
    (hinter : ∀ G ⊆ F, G.card = Module.finrank ℝ E + 1 → (⋂ K ∈ G, (K : Set E)).Nonempty) :
    (⋂ K ∈ F, (K : Set E)).Nonempty := by
  sorry

/-- **Minkowski–Carathéodory Theorem (Finite-Dimensional Krein–Milman):** every compact convex set
in a finite-dimensional real inner product space is the convex hull of its extreme points. -/
theorem krein_milman_finDim {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hKc : IsCompact K) (hKconv : Convex ℝ K) :
    convexHull ℝ (K.extremePoints ℝ) = K := by
  sorry

/-- **Jung's Circumradius Theorem:** every convex body `K` in dimension `d` is contained in a
closed Euclidean ball of radius $\sqrt{d / (2(d + 1))}\,\mathrm{diam}(K)$. -/
theorem jung_theorem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : ConvexBody E) :
    ∃ c : E, (K : Set E) ⊆ Metric.closedBall c
      (Real.sqrt ((Module.finrank ℝ E : ℝ) / (2 * (Module.finrank ℝ E + 1))) *
        Metric.diam (K : Set E)) := by
  sorry

/-- **Weyl–Minkowski $V \to H$ Duality:** every finite polytope with `0` in its interior is a
finite intersection of closed halfspaces `{x | ⟪x, u⟫ ≤ 1}`. -/
theorem weyl_minkowski_halfspaces {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Finset E} (h0 : (0 : E) ∈ interior (convexHull ℝ (S : Set E))) :
    ∃ U : Finset E, convexHull ℝ (S : Set E) = {x : E | ∀ u ∈ U, ⟪x, u⟫ ≤ 1} := by
  sorry

/-! ### 3. Volume & Isoperimetry -/

/-- **Prékopa–Leindler Inequality:** for `t ∈ (0, 1)` and measurable `f, g, h : E → ℝ≥0∞`
satisfying `f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y)`,
`(∫⁻ f) ^ (1 - t) * (∫⁻ g) ^ t ≤ ∫⁻ h`. -/
theorem prekopa_leindler {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {f g h : E → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hcond : ∀ x y : E, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y)) :
    (∫⁻ x, f x) ^ (1 - t) * (∫⁻ y, g y) ^ t ≤ ∫⁻ z, h z := by
  sorry

/-- **Brunn–Minkowski Inequality:** for nonempty compact sets `A, B ⊆ E` in dimension `d ≥ 1`,
`volume A ^ (1 / d) + volume B ^ (1 / d) ≤ volume (A + B) ^ (1 / d)`. -/
theorem brunn_minkowski {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {A B : Set E} (hAc : IsCompact A) (hAne : A.Nonempty)
    (hBc : IsCompact B) (hBne : B.Nonempty) :
    volume A ^ (1 / (Module.finrank ℝ E : ℝ)) + volume B ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
      volume (A + B) ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  sorry

/-- **Bieberbach's Isodiametric Inequality:** every compact set `K ⊆ E` has volume at most that
of the Euclidean ball of diameter `diam K`. -/
theorem isodiametric_inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K : Set E} (hKc : IsCompact K) :
    volume K ≤ volume (Metric.closedBall (0 : E) (Metric.diam K / 2)) := by
  sorry

/-- **Rogers–Shephard Inequality:** for every compact convex `K ⊆ E` in dimension `d`,
`volume (K - K) ≤ (2d choose d) * volume K`. -/
theorem rogers_shephard {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K : Set E} (hKconv : Convex ℝ K) (hKc : IsCompact K) :
    volume (K - K) ≤ ((Nat.choose (2 * Module.finrank ℝ E) (Module.finrank ℝ E) : ℕ) : ℝ≥0∞) *
      volume K := by
  sorry

/-- **Euclidean Isoperimetric Inequality:** for every nonempty compact `K ⊆ E` in dimension `d ≥ 1`,
`d * volume K ^ ((d - 1) / d) * volume B₁ ^ (1 / d) ≤ minkowskiSurfaceArea K`. -/
theorem isoperimetric_inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {K : Set E} (hKc : IsCompact K) (hKne : K.Nonempty) :
    (Module.finrank ℝ E : ℝ≥0∞) *
        volume K ^ (((Module.finrank ℝ E - 1 : ℕ) : ℝ) / (Module.finrank ℝ E : ℝ)) *
        volume (Metric.closedBall (0 : E) 1) ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
      minkowskiSurfaceArea K := by
  sorry

/-! ### 4. Asymptotic Convex Geometry (Ball's Lectures) -/

/-- **Fritz John's Theorem (General Convex Bodies):** every convex body `K` with nonempty interior
in dimension `d ≥ 1` has an affine image satisfying `B₁ ⊆ A '' K ⊆ d • B₁`. -/
theorem john_theorem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (K : ConvexBody E) (hint : (interior (K : Set E)).Nonempty) :
    ∃ A : E ≃ᵃ[ℝ] E,
      Metric.closedBall (0 : E) 1 ⊆ A '' (K : Set E) ∧
      A '' (K : Set E) ⊆ (Module.finrank ℝ E : ℝ) • Metric.closedBall (0 : E) 1 := by
  sorry

/-- **Fritz John's Theorem (Origin-Symmetric Convex Bodies):** every origin-symmetric convex body
`K` with `0 ∈ interior K` in dimension `d ≥ 1` has a linear image satisfying
`B₁ ⊆ T '' K ⊆ √d • B₁`. -/
theorem john_theorem_symmetric {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (K : ConvexBody E) (hsym : ∀ x ∈ (K : Set E), -x ∈ (K : Set E))
    (h0 : (0 : E) ∈ interior (K : Set E)) :
    ∃ T : E ≃ₗ[ℝ] E,
      Metric.closedBall (0 : E) 1 ⊆ T '' (K : Set E) ∧
      T '' (K : Set E) ⊆ Real.sqrt (Module.finrank ℝ E : ℝ) • Metric.closedBall (0 : E) 1 := by
  sorry

/-- **Loomis–Whitney Inequality:** for every orthonormal basis `b` of an `(n + 2)`-dimensional
inner product space `E` and every compact `K ⊆ E`, `volume K ^ (n + 1)` is bounded by the product
of the `(n + 1)`-dimensional volumes of its coordinate hyperplane projections. -/
theorem loomis_whitney {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} (b : OrthonormalBasis (Fin (n + 2)) ℝ E) {K : Set E} (hKc : IsCompact K) :
    volume K ^ (n + 1) ≤
      ∏ i : Fin (n + 2),
        volume ((fun x : E => Fin.removeNth i (WithLp.ofLp (b.repr x))) '' K) := by
  sorry

/-- **Rank-1 Geometric Brascamp–Lieb Inequality (Ball; Barthe 1998):** for unit vectors `u i`
and positive weights `c i` forming a John decomposition `∑ i, (c i * ⟪u i, x⟫) • u i = x`
and measurable `f : ι → ℝ → ℝ≥0∞`,
`∫⁻ x, ∏ i, f i ⟪x, u i⟫ ^ c i ≤ ∏ i, (∫⁻ t, f i t) ^ c i`. -/
theorem brascamp_lieb_rankOne {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} [Fintype ι] {u : ι → E} {c : ι → ℝ}
    (hu : ∀ i, ‖u i‖ = 1) (hc : ∀ i, 0 < c i)
    (hid : ∀ x : E, ∑ i, (c i * ⟪u i, x⟫) • u i = x)
    {f : ι → ℝ → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : E, ∏ i, f i ⟪x, u i⟫ ^ c i ≤ ∏ i, (∫⁻ t : ℝ, f i t) ^ c i := by
  sorry

/-- **Barthe's Reverse Brascamp–Lieb Inequality (Rank-1 Geometric Form, Barthe 1998):**
for a John decomposition `(u, c)`, nonempty open intervals `I i ⊆ ℝ`, continuous strictly positive
integrable `f i` on `I i`, and `H : E → ℝ≥0∞` dominating `∏ i, f i (y i) ^ c i` at
`∑ i, (c i * y i) • u i`, we have `∏ i, (∫ t in I i, f i t) ^ c i ≤ ∫⁻ z, H z`. -/
theorem reverse_brascamp_lieb_rankOne {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} [Fintype ι] {u : ι → E} {c : ι → ℝ}
    (hu : ∀ i, ‖u i‖ = 1) (hc : ∀ i, 0 < c i)
    (hid : ∀ x : E, ∑ i, (c i * ⟪u i, x⟫) • u i = x)
    {I : ι → Set ℝ} (hIopen : ∀ i, IsOpen (I i)) (hIconn : ∀ i, IsPreconnected (I i))
    (hIne : ∀ i, (I i).Nonempty)
    {f : ι → ℝ → ℝ} (hf_cont : ∀ i, ContinuousOn (f i) (I i))
    (hf_pos : ∀ i, ∀ t ∈ I i, 0 < f i t) (hf_int : ∀ i, IntegrableOn (f i) (I i) volume)
    {H : E → ℝ≥0∞}
    (hdom : ∀ y : ι → ℝ, (∀ i, y i ∈ I i) →
      ∏ i, ENNReal.ofReal (f i (y i)) ^ c i ≤ H (∑ i, (c i * y i) • u i)) :
    ∏ i, ENNReal.ofReal (∫ t in I i, f i t) ^ c i ≤ ∫⁻ z : E, H z := by
  sorry

/-- **Ball's Volume Ratio Theorem (Origin-Symmetric / Cube Bound, Ball 1989):** every
origin-symmetric convex body `K` with `0 ∈ interior K` has a linear image containing `B₁` of
volume at most `2 ^ d`. -/
theorem ball_volume_ratio_symmetric {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (K : ConvexBody E) (hsym : ∀ x ∈ (K : Set E), -x ∈ (K : Set E))
    (h0 : (0 : E) ∈ interior (K : Set E)) :
    ∃ T : E ≃ₗ[ℝ] E,
      Metric.closedBall (0 : E) 1 ⊆ T '' (K : Set E) ∧
      volume (T '' (K : Set E)) ≤ (2 : ℝ≥0∞) ^ Module.finrank ℝ E := by
  sorry

/-- **Ball's Volume Ratio Theorem (General / Simplex Bound, Ball 1991):** every convex body `K`
with nonempty interior has an affine image containing `B₁` whose volume is at most that of the
regular `d`-simplex circumscribing `B₁`: $d^{d/2} (d + 1)^{(d + 1)/2} / d!$. -/
theorem ball_volume_ratio {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (K : ConvexBody E) (hint : (interior (K : Set E)).Nonempty) :
    ∃ e : E ≃ᵃ[ℝ] E,
      Metric.closedBall (0 : E) 1 ⊆ e '' (K : Set E) ∧
      volume (e '' (K : Set E)) ≤
        ENNReal.ofReal ((Module.finrank ℝ E : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2) *
          ((Module.finrank ℝ E : ℝ) + 1) ^ (((Module.finrank ℝ E : ℝ) + 1) / 2) /
          (Nat.factorial (Module.finrank ℝ E) : ℝ)) := by
  sorry

/-- **Ball's Reverse Isoperimetric Inequality (Origin-Symmetric, Ball 1991):** every
origin-symmetric convex body `K` with `0 ∈ interior K` has a linear image whose isoperimetric ratio
is at most that of the cube `[-1, 1]^d`. -/
theorem ball_reverse_isoperimetric_symmetric {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [BorelSpace E]
    (K : ConvexBody E) (hsym : ∀ x ∈ (K : Set E), -x ∈ (K : Set E))
    (h0 : (0 : E) ∈ interior (K : Set E)) :
    ∃ T : E ≃ₗ[ℝ] E,
      minkowskiSurfaceArea (T '' (K : Set E)) ≤
        (2 * (Module.finrank ℝ E : ℝ≥0∞)) *
          volume (T '' (K : Set E)) ^
            (((Module.finrank ℝ E - 1 : ℕ) : ℝ) / (Module.finrank ℝ E : ℝ)) := by
  sorry

/-- **Ball's Reverse Isoperimetric Inequality (General / Simplex Form, Ball 1991):** every convex
body `K` with nonempty interior has an affine image whose isoperimetric ratio is at most that of
the regular `d`-simplex. -/
theorem ball_reverse_isoperimetric {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (K : ConvexBody E) (hint : (interior (K : Set E)).Nonempty) :
    ∃ e : E ≃ᵃ[ℝ] E,
      minkowskiSurfaceArea (e '' (K : Set E)) ≤
        (Module.finrank ℝ E : ℝ≥0∞) *
          ENNReal.ofReal ((Module.finrank ℝ E : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2) *
            ((Module.finrank ℝ E : ℝ) + 1) ^ (((Module.finrank ℝ E : ℝ) + 1) / 2) /
            (Nat.factorial (Module.finrank ℝ E) : ℝ)) ^ (1 / (Module.finrank ℝ E : ℝ)) *
          volume (e '' (K : Set E)) ^
            (((Module.finrank ℝ E - 1 : ℕ) : ℝ) / (Module.finrank ℝ E : ℝ)) := by
  sorry

/-- **Gaussian Concentration for Lipschitz Functions (around the mean):** for every `L`-Lipschitz
function `f : E → ℝ` (`L > 0`) and `t ≥ 0`,
`γ_E {x | |f x - 𝔼[f]| ≥ t} ≤ 2 exp(-t² / (4 L²))`. -/
theorem gaussian_lipschitz_concentration {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {L : ℝ≥0} (hL : 0 < L) {f : E → ℝ} (hf : LipschitzWith L f) {t : ℝ} (ht : 0 ≤ t) :
    ProbabilityTheory.stdGaussian E
        {x : E | t ≤ |f x - ∫ y : E, f y ∂ProbabilityTheory.stdGaussian E|} ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (4 * (L : ℝ) ^ 2))) := by
  sorry

/-- **Spherical Concentration for Lipschitz Functions (around a median):** for every `L`-Lipschitz
function `f : S^{d-1} → ℝ` (`L > 0`) with median `m` under `sphereProb` and `t ≥ 0`,
`σ {u | |f u - m| > t} ≤ 576 exp(-d t² / (8 L²))`. -/
theorem spherical_lipschitz_concentration {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [BorelSpace E]
    {L : ℝ≥0} (hL : 0 < L) {f : Metric.sphere (0 : E) 1 → ℝ} (hf : LipschitzWith L f) {m : ℝ}
    (hm_le : ENNReal.ofReal (1 / 2 : ℝ) ≤ sphereProb (E := E) {u | f u ≤ m})
    (hm_ge : ENNReal.ofReal (1 / 2 : ℝ) ≤ sphereProb (E := E) {u | m ≤ f u})
    {t : ℝ} (ht : 0 ≤ t) :
    sphereProb (E := E) {u | t < |f u - m|} ≤
      ENNReal.ofReal (576 * Real.exp (-(Module.finrank ℝ E : ℝ) * t ^ 2 / (8 * (L : ℝ) ^ 2))) := by
  sorry

/-- **Johnson–Lindenstrauss Lemma:** any `N` points in a finite-dimensional real inner product
space admit a linear map `L : E →ₗ[ℝ] EuclideanSpace ℝ (Fin k)` preserving all pairwise squared
distances up to `1 ± ε` whenever `16 log N / ε² ≤ k`. -/
theorem johnson_lindenstrauss {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {N k : ℕ} (x : Fin N → E) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hk : (16 : ℝ) * Real.log (N : ℝ) / ε ^ 2 ≤ (k : ℝ)) :
    ∃ L : E →ₗ[ℝ] EuclideanSpace ℝ (Fin k),
      ∀ i j : Fin N,
        (1 - ε) * ‖x i - x j‖ ^ 2 ≤ ‖L (x i) - L (x j)‖ ^ 2 ∧
        ‖L (x i) - L (x j)‖ ^ 2 ≤ (1 + ε) * ‖x i - x j‖ ^ 2 := by
  sorry

/-- **Dvoretzky's Theorem:** every origin-symmetric convex body `K` with `0 ∈ interior K` in
dimension `d ≥ 2` has a `k`-dimensional section `K ∩ F` within multiplicative distortion `1 + ε`
of a Euclidean ellipsoid whenever `8192 k log(48 / ε) ≤ ε² log d`. -/
theorem dvoretzky_theorem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : ConvexBody E) (hsym : ∀ x ∈ (K : Set E), -x ∈ (K : Set E))
    (h0 : (0 : E) ∈ interior (K : Set E)) (hd2 : 2 ≤ Module.finrank ℝ E)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {k : ℕ}
    (hk_bd : (8192 : ℝ) * (k : ℝ) * Real.log (48 / ε) ≤
      ε ^ 2 * Real.log (Module.finrank ℝ E : ℝ)) :
    ∃ (F : Submodule ℝ E) (T : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] F),
      Module.finrank ℝ F = k ∧
      (∀ w : EuclideanSpace ℝ (Fin k),
        ‖w‖ ≤ gauge (K : Set E) (T w : E) ∧ gauge (K : Set E) (T w : E) ≤ (1 + ε) * ‖w‖) ∧
      ((1 + ε)⁻¹ •
          ((F.subtype.comp T.toLinearMap) ''
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) ⊆
          (K : Set E) ∩ (F : Set E) ∧
        (K : Set E) ∩ (F : Set E) ⊆
          (F.subtype.comp T.toLinearMap) ''
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) := by
  sorry

/-- **Blaschke–Santaló Inequality (General Convex Bodies):** for every convex body `K` with
nonempty interior in dimension `d ≥ 1`, there exists a Santaló point `z ∈ interior K` such that
`volume K * volume (K - z)° ≤ volume B₁ ^ 2`. -/
theorem blaschke_santalo {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (K : ConvexBody E) (hne : (interior (K : Set E)).Nonempty) :
    ∃ z ∈ interior (K : Set E),
      volume (K : Set E) * volume {y : E | ∀ x ∈ (K : Set E), ⟪x - z, y⟫ ≤ 1} ≤
        volume (Metric.closedBall (0 : E) 1) ^ 2 := by
  sorry

/-- **Blaschke–Santaló Inequality (Origin-Symmetric Convex Bodies):** for every origin-symmetric
convex body `K` with `0 ∈ interior K` in dimension `d ≥ 1`,
`volume K * volume K° ≤ volume B₁ ^ 2`. -/
theorem blaschke_santalo_symmetric {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (K : ConvexBody E) (hsym : ∀ x ∈ (K : Set E), -x ∈ (K : Set E))
    (h0 : (0 : E) ∈ interior (K : Set E)) :
    volume (K : Set E) * volume {y : E | ∀ x ∈ (K : Set E), ⟪x, y⟫ ≤ 1} ≤
      volume (Metric.closedBall (0 : E) 1) ^ 2 := by
  sorry

/-- **Dual Urysohn Inequality:** for every convex body `K` with `0 ∈ interior K` in dimension
`d ≥ 1`, `(volume.real B₁ / volume.real K°) ^ (1 / d) ≤ meanWidth K`. -/
theorem dual_urysohn_inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (K : ConvexBody E) (h0 : (0 : E) ∈ interior (K : Set E)) :
    (volume.real (Metric.closedBall (0 : E) 1) /
        volume.real {y : E | ∀ x ∈ (K : Set E), ⟪x, y⟫ ≤ 1}) ^
        (1 / (Module.finrank ℝ E : ℝ)) ≤
      meanWidth K := by
  sorry

/-- **Urysohn's Inequality:** for every convex body `K` in dimension `d ≥ 1`,
`(volume.real K / volume.real B₁) ^ (1 / d) ≤ meanWidth K`. -/
theorem urysohn_inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (K : ConvexBody E) :
    (volume.real (K : Set E) / volume.real (Metric.closedBall (0 : E) 1)) ^
        (1 / (Module.finrank ℝ E : ℝ)) ≤
      meanWidth K := by
  sorry

end ConvexGeomChallenge

end
