/-
Copyright (c) 2026 Yegor Gorodzha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yegor Gorodzha
-/
module

public import ConvexGeom.Metric.Polarity
public import ConvexGeom.Volume.Symmetrization
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Origin-Symmetric Bodies, Ellipsoids, Mahler Volume, and Banach–Mazur Distance

This module provides the linear- and affine-invariant geometric foundations used throughout
asymptotic geometric analysis, including Mathlib bridges between `IsOriginSymmetric` and
`Balanced` / `gaugeSeminorm`.

## Main definitions

* `ConvexGeom.IsOriginSymmetric`: `∀ x ∈ S, -x ∈ S`, bridged to Mathlib's `Balanced ℝ S` and
  `gaugeSeminorm` via `isOriginSymmetric_iff_balanced` and `originSymmetricGaugeSeminorm`.
* `ConvexGeom.adjointLinearEquiv`: the adjoint equivalence `T† : E ≃ₗ[ℝ] E`.
* `ConvexGeom.ellipsoid`: centered ellipsoid `T '' closedBall 0 1`.
* `ConvexGeom.mahlerVolume`, `ConvexGeom.mahlerVolumeAt`, `ConvexGeom.santaloMahlerVolume`:
  origin-centered, point-centered, and affine-invariant Santaló Mahler volumes.
* `ConvexGeom.banachMazurDist`, `ConvexGeom.banachMazurEDist`,
  `ConvexGeom.affineBanachMazurDist`, `ConvexGeom.affineBanachMazurEDist`:
  linear and affine Banach–Mazur distances (both real-valued and `ℝ≥0∞`-valued).

## Main statements

* `ConvexGeom.isOriginSymmetric_iff_balanced` ,
  `ConvexGeom.isOriginSymmetric_convexBody_iff_supportFn` ,
  `ConvexGeom.gauge_smul_abs_of_isOriginSymmetric`, `ConvexGeom.mem_polarBody_iff_abs_inner_le_one`.
* `ConvexGeom.det_adjoint_eq_det`, `ConvexGeom.polarBody_linearEquiv_image`,
  `ConvexGeom.mahlerVolume_linearEquiv`, `ConvexGeom.santaloMahlerVolume_affineEquiv`.
* `ConvexGeom.banachMazurDist_symm`, `ConvexGeom.banachMazurDist_mul_triangle`,
  `ConvexGeom.banachMazurEDist_mul_triangle`, `ConvexGeom.banachMazurDist_polar`,
  `ConvexGeom.affineBanachMazurDist_affineEquiv_left`,
  `ConvexGeom.affineBanachMazurEDist_mul_triangle`.

## Implementation notes

The real-valued `banachMazurDist` and `affineBanachMazurDist` default to `0` on infeasible pairs
via `Real.sInf_empty`, whereas `banachMazurEDist` and `affineBanachMazurEDist` take values in
`ℝ≥0∞` (returning `⊤` on infeasible pairs) and satisfy unconditional multiplicative triangle
inequalities.

## References

* [K. Ball, *An Elementary Introduction to Modern Convex Geometry*][ball1997], Lectures 3–4
* [S. Artstein-Avidan, A. Giannopoulos, V. D. Milman, *Asymptotic Geometric Analysis,
  Part I*][agm2015], Chapters 1–4
-/

open MeasureTheory Set Metric
open scoped RealInnerProductSpace Pointwise ENNReal

namespace ConvexGeom

public section

/-! ### 1. Origin-Symmetric Sets -/

section OriginSymmetricBasic

variable {E : Type*} [NormedAddCommGroup E]

/-- A set `S ⊆ E` is **origin-symmetric** if `x ∈ S → -x ∈ S`. -/
@[expose]
def IsOriginSymmetric (S : Set E) : Prop :=
  ∀ x ∈ S, -x ∈ S

lemma isOriginSymmetric_iff_neg_eq {S : Set E} :
    IsOriginSymmetric S ↔ -S = S := by
  constructor
  · intro h
    ext x
    simp only [Set.mem_neg]
    exact ⟨fun hx => by simpa using h (-x) hx, fun hx => h x hx⟩
  · intro h x hx
    rw [← h]
    simpa using hx

lemma isOriginSymmetric_closedBall (r : ℝ) :
    IsOriginSymmetric (closedBall (0 : E) r) := by
  intro x hx
  simpa [mem_closedBall_zero_iff] using hx

lemma isOriginSymmetric_ball (r : ℝ) :
    IsOriginSymmetric (ball (0 : E) r) := by
  intro x hx
  simpa [mem_ball_zero_iff] using hx

lemma isOriginSymmetric_add {S T : Set E} (hS : IsOriginSymmetric S) (hT : IsOriginSymmetric T) :
    IsOriginSymmetric (S + T) := by
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact ⟨-x, hS x hx, -y, hT y hy, (neg_add x y).symm⟩

end OriginSymmetricBasic

section OriginSymmetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A convex set in a real vector space is origin-symmetric if and only if it is `Balanced ℝ`. -/
theorem isOriginSymmetric_iff_balanced {S : Set E} (hconv : Convex ℝ S) :
    IsOriginSymmetric S ↔ Balanced ℝ S := by
  rw [balanced_iff_neg_mem hconv]
  rfl

/-- An origin-symmetric convex set is `Balanced ℝ`. -/
lemma IsOriginSymmetric.balanced {S : Set E} (hS : IsOriginSymmetric S) (hconv : Convex ℝ S) :
    Balanced ℝ S :=
  (isOriginSymmetric_iff_balanced hconv).mp hS

/-- Package the Minkowski gauge of an origin-symmetric, convex, absorbent set as Mathlib's
`gaugeSeminorm`. -/
@[expose]
noncomputable def originSymmetricGaugeSeminorm {S : Set E}
    (hS : IsOriginSymmetric S) (hconv : Convex ℝ S) (habs : Absorbent ℝ S) : Seminorm ℝ E :=
  gaugeSeminorm (hS.balanced hconv) hconv habs

@[simp]
lemma originSymmetricGaugeSeminorm_apply {S : Set E}
    (hS : IsOriginSymmetric S) (hconv : Convex ℝ S) (habs : Absorbent ℝ S) (x : E) :
    originSymmetricGaugeSeminorm hS hconv habs x = gauge S x :=
  rfl

lemma isOriginSymmetric_polarBody {S : Set E} (hS : IsOriginSymmetric S) :
    IsOriginSymmetric (polarBody S) := by
  intro y hy
  rw [mem_polarBody] at hy ⊢
  intro x hx
  have h1 := hy (-x) (hS x hx)
  simpa [inner_neg_left, inner_neg_right] using h1

lemma isOriginSymmetric_linearMap_image {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : E →ₗ[ℝ] F) {S : Set E} (hS : IsOriginSymmetric S) :
    IsOriginSymmetric (f '' S) := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨-x, hS x hx, map_neg f x⟩

lemma isOriginSymmetric_smul (c : ℝ) {S : Set E} (hS : IsOriginSymmetric S) :
    IsOriginSymmetric (c • S) := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨-x, hS x hx, smul_neg c x⟩

lemma zero_mem_of_isOriginSymmetric {S : Set E} (hconv : Convex ℝ S) (hne : S.Nonempty)
    (hsym : IsOriginSymmetric S) : (0 : E) ∈ S := by
  obtain ⟨x, hx⟩ := hne
  have hmid := hconv hx (hsym x hx) (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  simpa [smul_neg, add_neg_cancel] using hmid

lemma supportFn_neg_of_isOriginSymmetric {K : ConvexBody E}
    (hK : IsOriginSymmetric (K : Set E)) (u : E) :
    supportFn K (-u) = supportFn K u := by
  apply le_antisymm
  · rw [supportFn_le_iff]
    intro x hx
    simpa [inner_neg_left, inner_neg_right] using inner_le_supportFn (hK x hx) u
  · rw [supportFn_le_iff]
    intro x hx
    simpa [inner_neg_left, inner_neg_right] using inner_le_supportFn (hK x hx) (-u)

/-- A convex body in a Hilbert space is origin-symmetric iff its support function is even. -/
theorem isOriginSymmetric_convexBody_iff_supportFn [CompleteSpace E] (K : ConvexBody E) :
    IsOriginSymmetric (K : Set E) ↔ ∀ u : E, supportFn K (-u) = supportFn K u := by
  constructor
  · exact supportFn_neg_of_isOriginSymmetric
  · intro heven
    have hbody : ((-1 : ℝ) • K : ConvexBody E) = K := by
      apply supportFn_injective
      ext u
      rw [supportFn_neg_one_smul, heven u]
    intro x hx
    have hmem : (-1 : ℝ) • x ∈ ((-1 : ℝ) • K : ConvexBody E) := by
      rw [← SetLike.mem_coe, ConvexBody.coe_smul]
      exact ⟨x, hx, rfl⟩
    rw [hbody] at hmem
    simpa using hmem

lemma isOriginSymmetric_centralSymm [CompleteSpace E] (K : ConvexBody E) :
    IsOriginSymmetric (centralSymm K : Set E) := by
  rw [isOriginSymmetric_convexBody_iff_supportFn]
  intro u
  rw [supportFn_centralSymm, supportFn_centralSymm, width_eq_supportFn_diff,
    width_eq_supportFn_diff, supportFn_minkowski_add, supportFn_minkowski_add,
    supportFn_neg_one_smul, supportFn_neg_one_smul, neg_neg, add_comm]

lemma isOriginSymmetric_minkowskiSymm [CompleteSpace E] {u : E} (hu : ‖u‖ = 1) (K : ConvexBody E)
    (hK : IsOriginSymmetric (K : Set E)) :
    IsOriginSymmetric (minkowskiSymm hu K : Set E) := by
  rw [isOriginSymmetric_convexBody_iff_supportFn]
  intro v
  rw [supportFn_minkowskiSymm, supportFn_minkowskiSymm, map_neg,
    supportFn_neg_of_isOriginSymmetric hK v,
    supportFn_neg_of_isOriginSymmetric hK (reflectHyperplane hu v)]

/-- For an origin-symmetric set `S`, the Minkowski gauge is even: `gauge S (-x) = gauge S x`. -/
lemma gauge_neg_of_isOriginSymmetric {S : Set E} (hS : IsOriginSymmetric S) (x : E) :
    gauge S (-x) = gauge S x :=
  gauge_neg hS x

/-- For an origin-symmetric set `S`, the Minkowski gauge is positively and negatively homogeneous:
`gauge S (c • x) = |c| * gauge S x` for all `c : ℝ`. -/
theorem gauge_smul_abs_of_isOriginSymmetric {S : Set E} (hS : IsOriginSymmetric S)
    (c : ℝ) (x : E) :
    gauge S (c • x) = |c| * gauge S x := by
  rcases le_total 0 c with hc | hc
  · rw [abs_of_nonneg hc, gauge_smul_of_nonneg hc, smul_eq_mul]
  · rw [abs_of_nonpos hc]
    have hneg : c • x = (-c) • (-x) := by simp [smul_neg, neg_smul]
    rw [hneg, gauge_smul_of_nonneg (neg_nonneg.mpr hc), gauge_neg_of_isOriginSymmetric hS,
      smul_eq_mul]

/-- For an origin-symmetric set `S`, one-sided polarity coincides with the absolute polar:
`y ∈ polarBody S ↔ ∀ x ∈ S, |⟪x, y⟫| ≤ 1`. -/
theorem mem_polarBody_iff_abs_inner_le_one {S : Set E} (hS : IsOriginSymmetric S) (y : E) :
    y ∈ polarBody S ↔ ∀ x ∈ S, |⟪x, y⟫| ≤ 1 := by
  rw [mem_polarBody]
  constructor
  · intro hy x hx
    rw [abs_le]
    refine ⟨?_, hy x hx⟩
    have := hy (-x) (hS x hx)
    rw [inner_neg_left] at this
    linarith
  · intro h x hx
    exact (le_abs_self _).trans (h x hx)

end OriginSymmetric

/-! ### 2. Adjoint Determinant and Linear Equivalence Law for Polar Bodies -/

section AdjointAndPolar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- On a finite-dimensional real inner product space, the adjoint has the same determinant:
`det (f†) = det f`. -/
theorem det_adjoint_eq_det [FiniteDimensional ℝ E] (f : E →ₗ[ℝ] E) :
    LinearMap.det (LinearMap.adjoint f) = LinearMap.det f := by
  let b := stdOrthonormalBasis ℝ E
  rw [← LinearMap.det_toMatrix b.toBasis, ← LinearMap.det_toMatrix b.toBasis,
    LinearMap.toMatrix_adjoint b b, Matrix.det_conjTranspose]
  simp

/-- The adjoint of a linear equivalence `T : E ≃ₗ[ℝ] E` as a linear equivalence `T† : E ≃ₗ[ℝ] E`. -/
noncomputable def adjointLinearEquiv [FiniteDimensional ℝ E] (T : E ≃ₗ[ℝ] E) : E ≃ₗ[ℝ] E where
  toFun := LinearMap.adjoint (T : E →ₗ[ℝ] E)
  invFun := LinearMap.adjoint (T.symm : E →ₗ[ℝ] E)
  left_inv x := by
    have hcomp : LinearMap.adjoint (T.symm : E →ₗ[ℝ] E) ∘ₗ LinearMap.adjoint (T : E →ₗ[ℝ] E) =
        LinearMap.id := by
      rw [← LinearMap.adjoint_comp]
      have hTT : (T : E →ₗ[ℝ] E) ∘ₗ (T.symm : E →ₗ[ℝ] E) = LinearMap.id := by
        ext y; simp
      rw [hTT, LinearMap.adjoint_id]
    exact congrArg (fun f : E →ₗ[ℝ] E => f x) hcomp
  right_inv x := by
    have hcomp : LinearMap.adjoint (T : E →ₗ[ℝ] E) ∘ₗ LinearMap.adjoint (T.symm : E →ₗ[ℝ] E) =
        LinearMap.id := by
      rw [← LinearMap.adjoint_comp]
      have hTT : (T.symm : E →ₗ[ℝ] E) ∘ₗ (T : E →ₗ[ℝ] E) = LinearMap.id := by
        ext y; simp
      rw [hTT, LinearMap.adjoint_id]
    exact congrArg (fun f : E →ₗ[ℝ] E => f x) hcomp
  map_add' x y := map_add (LinearMap.adjoint (T : E →ₗ[ℝ] E)) x y
  map_smul' c x := map_smul (LinearMap.adjoint (T : E →ₗ[ℝ] E)) c x

@[simp]
lemma adjointLinearEquiv_apply [FiniteDimensional ℝ E] (T : E ≃ₗ[ℝ] E) (x : E) :
    adjointLinearEquiv T x = LinearMap.adjoint (T : E →ₗ[ℝ] E) x := by
  rfl

@[simp]
lemma adjointLinearEquiv_toLinearMap [FiniteDimensional ℝ E] (T : E ≃ₗ[ℝ] E) :
    (adjointLinearEquiv T : E →ₗ[ℝ] E) = LinearMap.adjoint (T : E →ₗ[ℝ] E) := by
  ext x; rfl

@[simp]
lemma adjointLinearEquiv_symm_apply [FiniteDimensional ℝ E] (T : E ≃ₗ[ℝ] E) (x : E) :
    (adjointLinearEquiv T).symm x = LinearMap.adjoint (T.symm : E →ₗ[ℝ] E) x := by
  rfl

/-- **Linear equivalence law for polar bodies:**
for any invertible linear map `T : E ≃ₗ[ℝ] E` in finite dimensions,
`(T '' S)° = (T⁻¹)† '' S°`. -/
theorem polarBody_linearEquiv_image [FiniteDimensional ℝ E] (T : E ≃ₗ[ℝ] E) (S : Set E) :
    polarBody (T '' S) = (adjointLinearEquiv T.symm) '' polarBody S := by
  ext y
  simp only [mem_polarBody, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · intro hy
    refine ⟨adjointLinearEquiv T y, fun x hx => ?_, ?_⟩
    · rw [adjointLinearEquiv_apply, LinearMap.adjoint_inner_right]
      exact hy x hx
    · exact (adjointLinearEquiv T).left_inv y
  · rintro ⟨z, hz, rfl⟩ x hx
    have hinner : ⟪T x, adjointLinearEquiv T.symm z⟫ = ⟪x, z⟫ := by
      rw [adjointLinearEquiv_apply, LinearMap.adjoint_inner_right]
      simp
    rw [hinner]
    exact hz x hx

end AdjointAndPolar

/-! ### 3. Ellipsoids and Affine Invariance of Mahler Volume -/

section EllipsoidAndMahler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A centered ellipsoid in `E`: the image of the closed unit ball under `T : E ≃ₗ[ℝ] E`. -/
@[expose]
def ellipsoid (T : E ≃ₗ[ℝ] E) : Set E :=
  T '' closedBall (0 : E) 1

lemma convex_ellipsoid (T : E ≃ₗ[ℝ] E) : Convex ℝ (ellipsoid T) :=
  (convex_closedBall (0 : E) 1).linear_image T.toLinearMap

lemma isOriginSymmetric_ellipsoid (T : E ≃ₗ[ℝ] E) : IsOriginSymmetric (ellipsoid T) :=
  isOriginSymmetric_linearMap_image T.toLinearMap (isOriginSymmetric_closedBall 1)

lemma isCompact_ellipsoid [FiniteDimensional ℝ E] (T : E ≃ₗ[ℝ] E) :
    IsCompact (ellipsoid T) :=
  (isCompact_closedBall (0 : E) 1).image T.toContinuousLinearEquiv.continuous

lemma zero_mem_interior_ellipsoid [FiniteDimensional ℝ E] (T : E ≃ₗ[ℝ] E) :
    (0 : E) ∈ interior (ellipsoid T) := by
  let hT : E ≃ₜ E := T.toContinuousLinearEquiv.toHomeomorph
  have heq : ellipsoid T = hT '' closedBall (0 : E) 1 := rfl
  rw [heq, ← hT.image_interior]
  refine ⟨0, ?_, map_zero T⟩
  exact mem_interior.mpr ⟨ball (0 : E) 1, ball_subset_closedBall, isOpen_ball,
    mem_ball_self zero_lt_one⟩

/-- The polar of an ellipsoid is the dual ellipsoid:
`(T(B₁))° = (T⁻¹)†(B₁)`. -/
theorem polarBody_ellipsoid [FiniteDimensional ℝ E] (T : E ≃ₗ[ℝ] E) :
    polarBody (ellipsoid T) = ellipsoid (adjointLinearEquiv T.symm) := by
  rw [ellipsoid, polarBody_linearEquiv_image, polarBody_closedBall one_pos, inv_one, ellipsoid]

/-- Add-Haar volume of an ellipsoid: `μ (T(B₁)) = |det T| * μ (B₁)`. -/
theorem addHaar_ellipsoid [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (T : E ≃ₗ[ℝ] E) :
    μ (ellipsoid T) =
      ENNReal.ofReal |LinearMap.det (T : E →ₗ[ℝ] E)| * μ (closedBall (0 : E) 1) := by
  change μ ((T : E →ₗ[ℝ] E) '' closedBall (0 : E) 1) = _
  exact Measure.addHaar_image_linearMap μ (T : E →ₗ[ℝ] E) (closedBall (0 : E) 1)

/-- The **origin-centered Mahler volume** (volume product) of `S ⊆ E` with respect to `μ`:
`mahlerVolume μ S := μ S * μ (polarBody S)`.

Note: `mahlerVolume` is `GL(E)`-invariant (`mahlerVolume_linearEquiv`) but depends on the choice
of origin (e.g., on `[-1, ε] ⊂ ℝ` with `0 < ε < 1`, `mahlerVolume volume [-1, ε] > 4`). For the
translation- and affine-invariant volume product over interior centers, see `santaloMahlerVolume` .
-/
@[expose]
noncomputable def mahlerVolume [MeasurableSpace E] (μ : Measure E) (S : Set E) : ℝ≥0∞ :=
  μ S * μ (polarBody S)

/-- **Linear (`GL(E)`) invariance of Mahler volume:**
for every invertible linear map `T : E ≃ₗ[ℝ] E` and every additive Haar measure `μ`,
`mahlerVolume μ (T '' S) = mahlerVolume μ S`. -/
theorem mahlerVolume_linearEquiv [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (T : E ≃ₗ[ℝ] E) (S : Set E) :
    mahlerVolume μ (T '' S) = mahlerVolume μ S := by
  unfold mahlerVolume
  rw [polarBody_linearEquiv_image]
  change μ ((T : E →ₗ[ℝ] E) '' S) *
      μ ((adjointLinearEquiv T.symm : E →ₗ[ℝ] E) '' polarBody S) = _
  rw [Measure.addHaar_image_linearMap, Measure.addHaar_image_linearMap,
    adjointLinearEquiv_toLinearMap, det_adjoint_eq_det, LinearEquiv.det_coe_symm]
  have hd : LinearMap.det (T : E →ₗ[ℝ] E) ≠ 0 := T.isUnit_det'.ne_zero
  have hmul : ENNReal.ofReal |LinearMap.det (T : E →ₗ[ℝ] E)| *
      ENNReal.ofReal |(LinearMap.det (T : E →ₗ[ℝ] E))⁻¹| = 1 := by
    rw [← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, mul_inv_cancel₀ hd, abs_one,
      ENNReal.ofReal_one]
  calc
    ENNReal.ofReal |LinearMap.det (T : E →ₗ[ℝ] E)| * μ S *
        (ENNReal.ofReal |(LinearMap.det (T : E →ₗ[ℝ] E))⁻¹| * μ (polarBody S))
      = (ENNReal.ofReal |LinearMap.det (T : E →ₗ[ℝ] E)| *
          ENNReal.ofReal |(LinearMap.det (T : E →ₗ[ℝ] E))⁻¹|) * (μ S * μ (polarBody S)) := by
          ring
    _ = μ S * μ (polarBody S) := by rw [hmul, one_mul]

private lemma smulOfNeZero_image {c : ℝ} (hc : c ≠ 0) (S : Set E) :
    (LinearEquiv.smulOfNeZero ℝ E c hc) '' S = c • S := by
  ext x
  simp [mem_smul_set]

/-- Scale invariance of Mahler volume for any nonzero scalar `c`. -/
theorem mahlerVolume_smul [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {c : ℝ} (hc : c ≠ 0) (S : Set E) :
    mahlerVolume μ (c • S) = mahlerVolume μ S := by
  rw [← smulOfNeZero_image hc]
  exact mahlerVolume_linearEquiv μ (LinearEquiv.smulOfNeZero ℝ E c hc) S

/-- Every centered ellipsoid has the same Mahler volume as the Euclidean unit ball:
`mahlerVolume μ (ellipsoid T) = μ (closedBall 0 1) ^ 2`. -/
theorem mahlerVolume_ellipsoid [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (T : E ≃ₗ[ℝ] E) :
    mahlerVolume μ (ellipsoid T) = μ (closedBall (0 : E) 1) ^ 2 := by
  rw [ellipsoid, mahlerVolume_linearEquiv, mahlerVolume, polarBody_closedBall one_pos, inv_one, sq]

private lemma affineEquiv_sub (A : E ≃ᵃ[ℝ] E) (x z : E) :
    A x - A z = A.linear (x - z) := by
  have h := A.map_vadd z (x - z)
  simp only [vadd_eq_add, sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

/-- The **Mahler volume of `S` centered at `z`**:
`mahlerVolumeAt μ S z := mahlerVolume μ ((· - z) '' S)`. -/
@[expose]
noncomputable def mahlerVolumeAt [MeasurableSpace E] (μ : Measure E) (S : Set E) (z : E) : ℝ≥0∞ :=
  mahlerVolume μ ((fun x : E => x - z) '' S)

@[simp]
lemma mahlerVolumeAt_zero [MeasurableSpace E] (μ : Measure E) (S : Set E) :
    mahlerVolumeAt μ S 0 = mahlerVolume μ S := by
  simp [mahlerVolumeAt]

lemma mahlerVolumeAt_translate [MeasurableSpace E] (μ : Measure E) (S : Set E) (z a : E) :
    mahlerVolumeAt μ ((fun x : E => x + a) '' S) (z + a) = mahlerVolumeAt μ S z := by
  unfold mahlerVolumeAt
  congr 1
  ext y
  simp only [mem_image]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by abel⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x + a, ⟨x, hx, rfl⟩, by abel⟩

/-- Covariant transformation of centered Mahler volume under any affine equivalence `A : E ≃ᵃ[ℝ] E`
. -/
theorem mahlerVolumeAt_affineEquiv [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (A : E ≃ᵃ[ℝ] E) (S : Set E) (z : E) :
    mahlerVolumeAt μ (A '' S) (A z) = mahlerVolumeAt μ S z := by
  unfold mahlerVolumeAt
  have heq : (fun y : E => y - A z) '' (A '' S) = A.linear '' ((fun x : E => x - z) '' S) := by
    ext y
    simp only [mem_image]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x - z, ⟨x, hx, rfl⟩, (affineEquiv_sub A x z).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨A x, ⟨x, hx, rfl⟩, affineEquiv_sub A x z⟩
  rw [heq, mahlerVolume_linearEquiv]

/-- The **Santaló Mahler volume** (affine-invariant volume product) of `S ⊆ E`:
$$\mathcal{P}^*_\mu(S) := \inf_{z \in \mathrm{int}(S)} \mu(S - z)\,\mu((S - z)^\circ).$$
Note: if `interior S = ∅`, this infimum over an empty subtype is `⊤`. -/
@[expose]
noncomputable def santaloMahlerVolume [MeasurableSpace E] (μ : Measure E) (S : Set E) : ℝ≥0∞ :=
  ⨅ z : interior S, mahlerVolumeAt μ S z.1

theorem santaloMahlerVolume_le_mahlerVolumeAt [MeasurableSpace E] (μ : Measure E) {S : Set E}
    {z : E} (hz : z ∈ interior S) :
    santaloMahlerVolume μ S ≤ mahlerVolumeAt μ S z :=
  iInf_le (fun w : interior S => mahlerVolumeAt μ S w.1) ⟨z, hz⟩

theorem santaloMahlerVolume_le_mahlerVolume [MeasurableSpace E] (μ : Measure E) {S : Set E}
    (h0 : (0 : E) ∈ interior S) :
    santaloMahlerVolume μ S ≤ mahlerVolume μ S := by
  simpa [mahlerVolumeAt_zero] using santaloMahlerVolume_le_mahlerVolumeAt μ h0

/-- **Translation invariance** of the Santaló Mahler volume. -/
theorem santaloMahlerVolume_translate [MeasurableSpace E] (μ : Measure E) (S : Set E) (a : E) :
    santaloMahlerVolume μ ((fun x : E => x + a) '' S) = santaloMahlerVolume μ S := by
  let h : E ≃ₜ E := Homeomorph.addRight a
  have hS : (fun x : E => x + a) '' S = h '' S := rfl
  have hint : interior ((fun x : E => x + a) '' S) = h '' interior S := by
    rw [hS, h.image_interior]
  let e : interior S ≃ interior ((fun x : E => x + a) '' S) :=
    { toFun := fun z => ⟨z.1 + a, hint ▸ ⟨z.1, z.2, rfl⟩⟩
      invFun := fun w => ⟨w.1 - a, by
        have hw : w.1 ∈ h '' interior S := hint ▸ w.2
        rcases hw with ⟨x, hx, hxw⟩
        have hx' : w.1 - a = x := by change x + a = w.1 at hxw; rw [← hxw, add_sub_cancel_right]
        rwa [hx']⟩
      left_inv := fun z => Subtype.ext (add_sub_cancel_right z.1 a)
      right_inv := fun w => Subtype.ext (sub_add_cancel w.1 a) }
  unfold santaloMahlerVolume
  rw [← e.iInf_comp]
  refine iInf_congr fun z => ?_
  exact mahlerVolumeAt_translate μ S z.1 a

/-- **Full affine invariance** of the Santaló Mahler volume under any `A : E ≃ᵃ[ℝ] E`. -/
theorem santaloMahlerVolume_affineEquiv [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (A : E ≃ᵃ[ℝ] E) (S : Set E) :
    santaloMahlerVolume μ (A '' S) = santaloMahlerVolume μ S := by
  let h : E ≃ₜ E := A.toContinuousAffineEquiv.toHomeomorph
  have hS : A '' S = h '' S := rfl
  have hint : interior (A '' S) = A '' interior S := by
    rw [hS, ← h.image_interior]
    rfl
  let e : interior S ≃ interior (A '' S) :=
    { toFun := fun z => ⟨A z.1, hint ▸ ⟨z.1, z.2, rfl⟩⟩
      invFun := fun w => ⟨A.symm w.1, by
        have hw : w.1 ∈ A '' interior S := hint ▸ w.2
        rcases hw with ⟨x, hx, hxw⟩
        rw [← hxw, A.symm_apply_apply]
        exact hx⟩
      left_inv := fun z => Subtype.ext (A.symm_apply_apply z.1)
      right_inv := fun w => Subtype.ext (A.apply_symm_apply w.1) }
  unfold santaloMahlerVolume
  rw [← e.iInf_comp]
  refine iInf_congr fun z => ?_
  exact mahlerVolumeAt_affineEquiv μ A S z.1

end EllipsoidAndMahler

/-! ### 4. Multiplicative Banach–Mazur Distance -/

section BanachMazur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The set of multiplicative distortion factors `r ≥ 1` admitting an invertible linear map
`T : E ≃ₗ[ℝ] E` with `K ⊆ T '' L ⊆ r • K`. -/
@[expose]
def banachMazurSet (K L : Set E) : Set ℝ :=
  {r : ℝ | 1 ≤ r ∧ ∃ T : E ≃ₗ[ℝ] E, K ⊆ T '' L ∧ T '' L ⊆ r • K}

/-- The **origin-fixed (linear) multiplicative Banach–Mazur distance** between sets `K, L ⊆ E`:
$$d_{\mathrm{BM}}(K, L) :=
  \inf \{ r \ge 1 \mid \exists T \in \mathrm{GL}(E),\; K \subseteq T(L) \subseteq r K \}.$$

This matches the classical Banach–Mazur distance for origin-symmetric bodies. On infeasible pairs
(when `banachMazurSet K L = ∅`), `Real.sInf_empty` returns `0`; use `banachMazurEDist` for
`ℝ≥0∞`-valued semantics returning `⊤`. For general (non-symmetric) bodies requiring recentering,
use `affineBanachMazurDist` / `affineBanachMazurEDist`. -/
@[expose]
noncomputable def banachMazurDist (K L : Set E) : ℝ :=
  sInf (banachMazurSet K L)

lemma bddBelow_banachMazurSet (K L : Set E) : BddBelow (banachMazurSet K L) :=
  ⟨1, fun _ hr => hr.1⟩

/-- Whenever `K` and `L` are bounded and contain `0` in their interiors, their Banach–Mazur
distortion set is nonempty. -/
lemma banachMazurSet_nonempty {K L : Set E}
    (hK0 : (0 : E) ∈ interior K) (hKb : Bornology.IsBounded K)
    (hL0 : (0 : E) ∈ interior L) (hLb : Bornology.IsBounded L) :
    (banachMazurSet K L).Nonempty := by
  obtain ⟨r₁, hr₁, hballK⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hK0)
  obtain ⟨r₂, hr₂, hballL⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hL0)
  obtain ⟨R₁, hKR₁⟩ := hKb.subset_closedBall (0 : E)
  obtain ⟨R₂, hLR₂⟩ := hLb.subset_closedBall (0 : E)
  set a₁ := r₁ / 2
  set a₂ := r₂ / 2
  set b₁ := max R₁ 1
  set b₂ := max R₂ 1
  have ha₁ : 0 < a₁ := half_pos hr₁
  have ha₂ : 0 < a₂ := half_pos hr₂
  have hb₁ : 0 < b₁ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hb₂ : 0 < b₂ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hcbK : closedBall (0 : E) a₁ ⊆ K :=
    (closedBall_subset_ball (half_lt_self hr₁)).trans hballK
  have hcbL : closedBall (0 : E) a₂ ⊆ L :=
    (closedBall_subset_ball (half_lt_self hr₂)).trans hballL
  have hKb₁ : K ⊆ closedBall (0 : E) b₁ :=
    hKR₁.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hLb₂ : L ⊆ closedBall (0 : E) b₂ :=
    hLR₂.trans (closedBall_subset_closedBall (le_max_left _ _))
  set c := b₁ / a₂
  have hc : 0 < c := div_pos hb₁ ha₂
  set r := max 1 (c * b₂ / a₁)
  have hr1 : 1 ≤ r := le_max_left _ _
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  refine ⟨r, hr1, LinearEquiv.smulOfNeZero ℝ E c hc.ne', ?_, ?_⟩
  · intro x hx
    rw [smulOfNeZero_image]
    refine ⟨c⁻¹ • x, hcbL ?_, by dsimp only; rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]⟩
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
    have hxnorm : ‖x‖ ≤ b₁ := mem_closedBall_zero_iff.mp (hKb₁ hx)
    calc
      c⁻¹ * ‖x‖ ≤ c⁻¹ * b₁ := mul_le_mul_of_nonneg_left hxnorm (inv_nonneg.mpr hc.le)
      _ = a₂ := by dsimp only [c]; field_simp [hb₁.ne', ha₂.ne']
  · intro y hy
    rw [smulOfNeZero_image] at hy
    rcases hy with ⟨z, hz, rfl⟩
    refine ⟨r⁻¹ • (c • z), hcbK ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hr_pos), abs_of_pos hc]
      have hznorm : ‖z‖ ≤ b₂ := mem_closedBall_zero_iff.mp (hLb₂ hz)
      have hrge : c * b₂ / a₁ ≤ r := le_max_right _ _
      have hcb_le : c * b₂ ≤ r * a₁ := (div_le_iff₀ ha₁).mp hrge
      calc
        r⁻¹ * (c * ‖z‖) ≤ r⁻¹ * (c * b₂) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hznorm hc.le)
            (inv_nonneg.mpr hr_pos.le)
        _ ≤ r⁻¹ * (r * a₁) := mul_le_mul_of_nonneg_left hcb_le (inv_nonneg.mpr hr_pos.le)
        _ = a₁ := by field_simp [hr_pos.ne']
    · dsimp only
      rw [smul_smul, mul_inv_cancel₀ hr_pos.ne', one_smul]

/-- `1 ≤ banachMazurDist K L` whenever the distortion set is nonempty. -/
theorem one_le_banachMazurDist {K L : Set E} (hne : (banachMazurSet K L).Nonempty) :
    1 ≤ banachMazurDist K L :=
  le_csInf hne fun _ hr => hr.1

/-- Reflexivity: `banachMazurDist K K = 1`. -/
theorem banachMazurDist_self (K : Set E) : banachMazurDist K K = 1 := by
  have h1 : (1 : ℝ) ∈ banachMazurSet K K :=
    ⟨le_rfl, LinearEquiv.refl ℝ E,
      fun x hx => ⟨x, hx, rfl⟩,
      by rintro _ ⟨x, hx, rfl⟩; exact ⟨x, hx, one_smul ℝ x⟩⟩
  exact le_antisymm (csInf_le (bddBelow_banachMazurSet K K) h1)
    (one_le_banachMazurDist ⟨1, h1⟩)

lemma banachMazurSet_symm (K L : Set E) :
    banachMazurSet K L = banachMazurSet L K := by
  have hsub : ∀ A B : Set E, banachMazurSet A B ⊆ banachMazurSet B A := by
    intro A B r ⟨hr1, T, h1, h2⟩
    have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
    refine ⟨hr1, (LinearEquiv.smulOfNeZero ℝ E r hr_pos.ne').trans T.symm, ?_, ?_⟩
    · intro y hy
      have hTy : T y ∈ r • A := h2 ⟨y, hy, rfl⟩
      rcases hTy with ⟨x, hx, hrx⟩
      dsimp only at hrx
      refine ⟨x, hx, ?_⟩
      change T.symm (r • x) = y
      rw [hrx, T.symm_apply_apply]
    · rintro _ ⟨x, hx, rfl⟩
      rcases h1 hx with ⟨y, hy, hTy⟩
      refine ⟨y, hy, ?_⟩
      change r • y = T.symm (r • x)
      rw [← hTy, ← map_smul, T.symm_apply_apply]
  exact Set.Subset.antisymm (hsub K L) (hsub L K)

/-- Symmetry: `banachMazurDist K L = banachMazurDist L K`. -/
theorem banachMazurDist_symm (K L : Set E) :
    banachMazurDist K L = banachMazurDist L K := by
  rw [banachMazurDist, banachMazurSet_symm, banachMazurDist]

lemma banachMazurSet_linearEquiv_right (K L : Set E) (A : E ≃ₗ[ℝ] E) :
    banachMazurSet K (A '' L) = banachMazurSet K L := by
  ext r
  simp only [banachMazurSet, mem_ofPred_eq, and_congr_right_iff]
  intro _
  constructor
  · rintro ⟨T, h1, h2⟩
    have himg : (A.trans T) '' L = T '' (A '' L) := by
      ext x; simp [LinearEquiv.trans_apply]
    exact ⟨A.trans T, himg.symm ▸ h1, himg.symm ▸ h2⟩
  · rintro ⟨T, h1, h2⟩
    have himg : (A.symm.trans T) '' (A '' L) = T '' L := by
      ext x; simp [LinearEquiv.trans_apply]
    exact ⟨A.symm.trans T, himg.symm ▸ h1, himg.symm ▸ h2⟩

/-- Right `GL(E)`-invariance of Banach–Mazur distance. -/
theorem banachMazurDist_linearEquiv_right (K L : Set E) (A : E ≃ₗ[ℝ] E) :
    banachMazurDist K (A '' L) = banachMazurDist K L := by
  rw [banachMazurDist, banachMazurSet_linearEquiv_right, banachMazurDist]

/-- Left `GL(E)`-invariance of Banach–Mazur distance. -/
theorem banachMazurDist_linearEquiv_left (K L : Set E) (A : E ≃ₗ[ℝ] E) :
    banachMazurDist (A '' K) L = banachMazurDist K L := by
  rw [banachMazurDist_symm, banachMazurDist_linearEquiv_right, banachMazurDist_symm]

/-- Scale invariance of Banach–Mazur distance on both arguments. -/
theorem banachMazurDist_smul_right (K L : Set E) {c : ℝ} (hc : c ≠ 0) :
    banachMazurDist K (c • L) = banachMazurDist K L := by
  rw [← smulOfNeZero_image hc, banachMazurDist_linearEquiv_right]

theorem banachMazurDist_smul_left (K L : Set E) {c : ℝ} (hc : c ≠ 0) :
    banachMazurDist (c • K) L = banachMazurDist K L := by
  rw [← smulOfNeZero_image hc, banachMazurDist_linearEquiv_left]

/-- **Multiplicative Triangle Inequality:**
`banachMazurDist K M ≤ banachMazurDist K L * banachMazurDist L M`
(so `log ∘ banachMazurDist` is a pseudometric). -/
theorem banachMazurDist_mul_triangle {K L M : Set E}
    (hKL : (banachMazurSet K L).Nonempty) (hLM : (banachMazurSet L M).Nonempty) :
    banachMazurDist K M ≤ banachMazurDist K L * banachMazurDist L M := by
  have hmul_mem : ∀ r₁ ∈ banachMazurSet K L, ∀ r₂ ∈ banachMazurSet L M,
      r₁ * r₂ ∈ banachMazurSet K M := by
    rintro r₁ ⟨hr₁, T₁, hK1, h1K⟩ r₂ ⟨hr₂, T₂, hL2, h2L⟩
    refine ⟨by nlinarith, T₂.trans T₁, ?_, ?_⟩
    · intro x hx
      rcases hK1 hx with ⟨y, hy, rfl⟩
      rcases hL2 hy with ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      have hT2 : T₂ z ∈ r₂ • L := h2L ⟨z, hz, rfl⟩
      rcases hT2 with ⟨y, hy, hyz⟩
      have hT1 : T₁ y ∈ r₁ • K := h1K ⟨y, hy, rfl⟩
      rcases hT1 with ⟨x, hx, hxy⟩
      refine ⟨x, hx, ?_⟩
      change (r₁ * r₂) • x = T₁ (T₂ z)
      rw [← hyz, map_smul, ← hxy, smul_smul, mul_comm]
  have hstep1 : ∀ r₁ ∈ banachMazurSet K L, banachMazurDist K M ≤ r₁ * banachMazurDist L M := by
    intro r₁ hr₁
    have hr₁_pos : 0 < r₁ := lt_of_lt_of_le zero_lt_one hr₁.1
    rw [← div_le_iff₀' hr₁_pos]
    refine le_csInf hLM fun r₂ hr₂ => ?_
    rw [div_le_iff₀' hr₁_pos]
    exact csInf_le (bddBelow_banachMazurSet K M) (hmul_mem r₁ hr₁ r₂ hr₂)
  have hdLM_pos : 0 < banachMazurDist L M := lt_of_lt_of_le zero_lt_one (one_le_banachMazurDist hLM)
  rw [← div_le_iff₀ hdLM_pos]
  refine le_csInf hKL fun r₁ hr₁ => ?_
  rw [div_le_iff₀ hdLM_pos]
  exact hstep1 r₁ hr₁

/-- **Polarity Invariance of Banach–Mazur Distance:**
in finite dimensions, for closed convex sets `K, L` containing `0`,
`banachMazurDist (polarBody K) (polarBody L) = banachMazurDist K L`. -/
theorem banachMazurDist_polar [FiniteDimensional ℝ E] {K L : Set E}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hK0 : (0 : E) ∈ K)
    (hLc : Convex ℝ L) (hLcl : IsClosed L) (hL0 : (0 : E) ∈ L) :
    banachMazurDist (polarBody K) (polarBody L) = banachMazurDist K L := by
  have hsub : ∀ A B : Set E, banachMazurSet A B ⊆ banachMazurSet (polarBody A) (polarBody B) := by
    intro A B r ⟨hr1, T, h1, h2⟩
    have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
    let S : E ≃ₗ[ℝ] E :=
      (adjointLinearEquiv T.symm).trans (LinearEquiv.smulOfNeZero ℝ E r hr_pos.ne')
    have hSimg : S '' polarBody B = r • polarBody (T '' B) := by
      rw [polarBody_linearEquiv_image, ← smulOfNeZero_image hr_pos.ne', ← Set.image_comp]
      rfl
    refine ⟨hr1, S, ?_, ?_⟩
    · rw [hSimg]
      have hpol2 : r⁻¹ • polarBody A ⊆ polarBody (T '' B) := by
        rw [← polarBody_smul hr_pos]; exact polarBody_antitone h2
      intro y hy
      have hy' : r⁻¹ • y ∈ polarBody (T '' B) := hpol2 ⟨y, hy, rfl⟩
      refine ⟨r⁻¹ • y, hy', ?_⟩
      dsimp only
      rw [smul_smul, mul_inv_cancel₀ hr_pos.ne', one_smul]
    · rw [hSimg]
      exact Set.smul_set_mono (polarBody_antitone h1)
  have heq : banachMazurSet (polarBody K) (polarBody L) = banachMazurSet K L := by
    apply Set.Subset.antisymm _ (hsub K L)
    calc
      banachMazurSet (polarBody K) (polarBody L)
        ⊆ banachMazurSet (polarBody (polarBody K)) (polarBody (polarBody L)) :=
          hsub (polarBody K) (polarBody L)
      _ = banachMazurSet K L := by
          rw [polarBody_polarBody hKc hKcl hK0, polarBody_polarBody hLc hLcl hL0]
  rw [banachMazurDist, heq, banachMazurDist]

/-- **Mahler Volume Comparison via Banach–Mazur Distance:**
for any additive Haar measure `μ` and any sets `K, L` with nonempty distortion set,
$$\mathcal{P}_\mu(L) \le d_{\mathrm{BM}}(K, L)^d\,\mathcal{P}_\mu(K).$$ -/
theorem mahlerVolume_le_banachMazurDist_pow_mul [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {K L : Set E} (hne : (banachMazurSet K L).Nonempty) :
    mahlerVolume μ L ≤
      ENNReal.ofReal (banachMazurDist K L ^ Module.finrank ℝ E) * mahlerVolume μ K := by
  set d := Module.finrank ℝ E
  have hbound : ∀ r ∈ banachMazurSet K L,
      mahlerVolume μ L ≤ ENNReal.ofReal (r ^ d) * mahlerVolume μ K := by
    rintro r ⟨hr1, T, hKsub, hsubrK⟩
    have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
    rw [← mahlerVolume_linearEquiv μ T L, mahlerVolume, mahlerVolume]
    have hvol1 : μ (T '' L) ≤ ENNReal.ofReal (r ^ d) * μ K := by
      calc
        μ (T '' L) ≤ μ (r • K) := measure_mono hsubrK
        _ = ENNReal.ofReal (r ^ d) * μ K := Measure.addHaar_smul_of_nonneg μ hr_pos.le K
    have hvol2 : μ (polarBody (T '' L)) ≤ μ (polarBody K) :=
      measure_mono (polarBody_antitone hKsub)
    calc
      μ (T '' L) * μ (polarBody (T '' L))
        ≤ (ENNReal.ofReal (r ^ d) * μ K) * μ (polarBody K) := mul_le_mul' hvol1 hvol2
      _ = ENNReal.ofReal (r ^ d) * (μ K * μ (polarBody K)) := by ring
  rcases eq_or_ne (mahlerVolume μ K) ⊤ with hKtop | hKfin
  · have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (banachMazurDist K L ^ d) := by
      rw [ENNReal.ofReal_pos]
      exact pow_pos (lt_of_lt_of_le zero_lt_one (one_le_banachMazurDist hne)) d
    rw [hKtop, ENNReal.mul_top hpos.ne']
    exact le_top
  · have ⟨r₀, hr₀⟩ := hne
    have hLfin : mahlerVolume μ L ≠ ⊤ := by
      have h1 := hbound r₀ hr₀
      exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKfin) h1
    have hreal : (mahlerVolume μ L).toReal ≤
        banachMazurDist K L ^ d * (mahlerVolume μ K).toReal := by
      have hfor : ∀ ε : ℝ, 0 < ε →
          (mahlerVolume μ L).toReal ≤
            (banachMazurDist K L + ε) ^ d * (mahlerVolume μ K).toReal := by
        intro ε hε
        obtain ⟨r, hr_mem, hr_lt⟩ := Real.lt_sInf_add_pos hne hε
        have h1 := hbound r hr_mem
        have hto : (mahlerVolume μ L).toReal ≤ r ^ d * (mahlerVolume μ K).toReal := by
          have hrnn : 0 ≤ r ^ d := pow_nonneg (le_trans zero_le_one hr_mem.1) d
          have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKfin) h1
          rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hrnn] at this
        have hpow : r ^ d ≤ (banachMazurDist K L + ε) ^ d :=
          pow_le_pow_left₀ (le_trans zero_le_one hr_mem.1) hr_lt.le d
        exact hto.trans (mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg)
      have htend : Filter.Tendsto
          (fun ε : ℝ => (banachMazurDist K L + ε) ^ d * (mahlerVolume μ K).toReal)
          (nhdsWithin 0 (Ioi 0))
          (nhds (banachMazurDist K L ^ d * (mahlerVolume μ K).toReal)) := by
        have hcont : Continuous (fun ε : ℝ =>
            (banachMazurDist K L + ε) ^ d * (mahlerVolume μ K).toReal) :=
          ((continuous_const.add continuous_id).pow d).mul continuous_const
        simpa [add_zero] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
      exact ge_of_tendsto htend (Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => hfor ε hε)
    rw [← ENNReal.ofReal_toReal hLfin, ← ENNReal.ofReal_toReal hKfin,
      ← ENNReal.ofReal_mul (pow_nonneg (le_trans zero_le_one (one_le_banachMazurDist hne)) d)]
    exact ENNReal.ofReal_le_ofReal hreal

/-- Specialization to the Euclidean unit ball:
$$\mathcal{P}_\mu(L) \le d_{\mathrm{BM}}(B_2^d, L)^d\,\mu(B_2^d)^2.$$ -/
theorem mahlerVolume_le_banachMazurDist_ball_pow_mul [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {L : Set E} (hL0 : (0 : E) ∈ interior L) (hLb : Bornology.IsBounded L) :
    mahlerVolume μ L ≤
      ENNReal.ofReal (banachMazurDist (closedBall (0 : E) 1) L ^ Module.finrank ℝ E) *
        μ (closedBall (0 : E) 1) ^ 2 := by
  have hB0 : (0 : E) ∈ interior (closedBall (0 : E) 1) :=
    mem_interior.mpr ⟨ball (0 : E) 1, ball_subset_closedBall, isOpen_ball,
      mem_ball_self zero_lt_one⟩
  have hne := banachMazurSet_nonempty hB0 isBounded_closedBall hL0 hLb
  have hball : mahlerVolume μ (closedBall (0 : E) 1) = μ (closedBall (0 : E) 1) ^ 2 := by
    rw [mahlerVolume, polarBody_closedBall one_pos, inv_one, sq]
  simpa [hball] using mahlerVolume_le_banachMazurDist_pow_mul μ hne

/-- Extended (`ℝ≥0∞`-valued) origin-fixed Banach–Mazur distance:
equals `ENNReal.ofReal (banachMazurDist K L)` when `banachMazurSet K L` is nonempty, and `⊤`
when no invertible linear map embeds `K ⊆ T(L) ⊆ r K` (avoiding the `Real.sInf_empty = 0`
totalization artifact). -/
@[expose]
noncomputable def banachMazurEDist (K L : Set E) : ℝ≥0∞ :=
  sInf (ENNReal.ofReal '' banachMazurSet K L)

theorem banachMazurEDist_eq_top_of_empty {K L : Set E} (hemp : banachMazurSet K L = ∅) :
    banachMazurEDist K L = ⊤ := by
  simp [banachMazurEDist, hemp]

theorem banachMazurEDist_eq_ofReal {K L : Set E} (hne : (banachMazurSet K L).Nonempty) :
    banachMazurEDist K L = ENNReal.ofReal (banachMazurDist K L) := by
  apply le_antisymm
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε' : (0 : ℝ) < (ε : ℝ) := NNReal.coe_pos.mpr hε
    obtain ⟨r, hr_mem, hr_lt⟩ := Real.lt_sInf_add_pos hne hε'
    calc
      banachMazurEDist K L ≤ ENNReal.ofReal r := sInf_le ⟨r, hr_mem, rfl⟩
      _ ≤ ENNReal.ofReal (banachMazurDist K L + (ε : ℝ)) := ENNReal.ofReal_le_ofReal hr_lt.le
      _ = ENNReal.ofReal (banachMazurDist K L) + (ε : ℝ≥0∞) := by
          rw [ENNReal.ofReal_add (le_trans zero_le_one (one_le_banachMazurDist hne)) hε'.le,
            ENNReal.ofReal_coe_nnreal]
  · refine le_sInf ?_
    rintro _ ⟨r, hr, rfl⟩
    exact ENNReal.ofReal_le_ofReal (csInf_le (bddBelow_banachMazurSet K L) hr)

theorem one_le_banachMazurEDist (K L : Set E) : 1 ≤ banachMazurEDist K L := by
  refine le_sInf ?_
  rintro _ ⟨r, hr, rfl⟩
  simpa using ENNReal.ofReal_le_ofReal hr.1

theorem banachMazurEDist_self (K : Set E) : banachMazurEDist K K = 1 := by
  have h1 : (1 : ℝ) ∈ banachMazurSet K K :=
    ⟨le_rfl, LinearEquiv.refl ℝ E,
      fun x hx => ⟨x, hx, rfl⟩,
      by rintro _ ⟨x, hx, rfl⟩; exact ⟨x, hx, one_smul ℝ x⟩⟩
  rw [banachMazurEDist_eq_ofReal ⟨1, h1⟩, banachMazurDist_self, ENNReal.ofReal_one]

theorem banachMazurEDist_symm (K L : Set E) :
    banachMazurEDist K L = banachMazurEDist L K := by
  rw [banachMazurEDist, banachMazurSet_symm, banachMazurEDist]

/-- **Unconditional multiplicative triangle inequality for `banachMazurEDist`:**
holds for all sets `K, L, M ⊆ E` (with infeasible pairs yielding `⊤`). -/
theorem banachMazurEDist_mul_triangle (K L M : Set E) :
    banachMazurEDist K M ≤ banachMazurEDist K L * banachMazurEDist L M := by
  by_cases hKL : (banachMazurSet K L).Nonempty
  · by_cases hLM : (banachMazurSet L M).Nonempty
    · have hKM : (banachMazurSet K M).Nonempty := by
        obtain ⟨r₁, hr₁, T₁, hK1, h1K⟩ := hKL
        obtain ⟨r₂, hr₂, T₂, hL2, h2L⟩ := hLM
        refine ⟨r₁ * r₂, by nlinarith, T₂.trans T₁, ?_, ?_⟩
        · intro x hx
          rcases hK1 hx with ⟨y, hy, rfl⟩
          rcases hL2 hy with ⟨z, hz, rfl⟩
          exact ⟨z, hz, rfl⟩
        · rintro _ ⟨z, hz, rfl⟩
          rcases h2L ⟨z, hz, rfl⟩ with ⟨y, hy, hyz⟩
          rcases h1K ⟨y, hy, rfl⟩ with ⟨x, hx, hxy⟩
          refine ⟨x, hx, ?_⟩
          change (r₁ * r₂) • x = T₁ (T₂ z)
          rw [← hyz, map_smul, ← hxy, smul_smul, mul_comm]
      rw [banachMazurEDist_eq_ofReal hKM, banachMazurEDist_eq_ofReal hKL,
        banachMazurEDist_eq_ofReal hLM,
        ← ENNReal.ofReal_mul (le_trans zero_le_one (one_le_banachMazurDist hKL))]
      exact ENNReal.ofReal_le_ofReal (banachMazurDist_mul_triangle hKL hLM)
    · rw [Set.not_nonempty_iff_eq_empty] at hLM
      rw [banachMazurEDist_eq_top_of_empty hLM,
        ENNReal.mul_top (lt_of_lt_of_le zero_lt_one (one_le_banachMazurEDist K L)).ne']
      exact le_top
  · rw [Set.not_nonempty_iff_eq_empty] at hKL
    rw [banachMazurEDist_eq_top_of_empty hKL,
      ENNReal.top_mul (lt_of_lt_of_le zero_lt_one (one_le_banachMazurEDist L M)).ne']
    exact le_top

end BanachMazur

/-! ### 5. Affine Banach–Mazur Distance (Allowing Recentering) -/

section AffineBanachMazur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The set of affine Banach–Mazur distortion factors `r ≥ 1`:
there exist `T ∈ GL(E)` and centers `x, y ∈ E` such that
`K - x ⊆ T(L - y) ⊆ r • (K - x)`. -/
@[expose]
def affineBanachMazurSet (K L : Set E) : Set ℝ :=
  {r : ℝ | 1 ≤ r ∧ ∃ (T : E ≃ₗ[ℝ] E) (x y : E),
    (fun z => z - x) '' K ⊆ T '' ((fun z => z - y) '' L) ∧
    T '' ((fun z => z - y) '' L) ⊆ r • ((fun z => z - x) '' K)}

/-- The **affine multiplicative Banach–Mazur distance** between sets `K, L ⊆ E`:
$$d_{\mathrm{BM}}^{\mathrm{aff}}(K, L) :=
  \inf \{ r \ge 1 \mid \exists T \in \mathrm{GL}(E),\, x, y \in E,\;
    K - x \subseteq T(L - y) \subseteq r (K - x) \}.$$
This is the standard Banach–Mazur distance for general (non-symmetric) convex bodies, where
Fritz John's theorem gives `d_BM^aff(K, B₂^d) ≤ d`. On infeasible pairs, `Real.sInf_empty`
returns `0`; use `affineBanachMazurEDist` for `ℝ≥0∞`-valued semantics returning `⊤`. -/
@[expose]
noncomputable def affineBanachMazurDist (K L : Set E) : ℝ :=
  sInf (affineBanachMazurSet K L)

/-- Extended (`ℝ≥0∞`-valued) affine Banach–Mazur distance (equals `⊤` on infeasible pairs). -/
@[expose]
noncomputable def affineBanachMazurEDist (K L : Set E) : ℝ≥0∞ :=
  sInf (ENNReal.ofReal '' affineBanachMazurSet K L)

lemma mem_affineBanachMazurSet_iff {K L : Set E} {r : ℝ} :
    r ∈ affineBanachMazurSet K L ↔
      ∃ x y : E, r ∈ banachMazurSet ((fun z => z - x) '' K) ((fun z => z - y) '' L) := by
  simp only [affineBanachMazurSet, banachMazurSet, mem_ofPred_eq]
  constructor
  · rintro ⟨hr, T, x, y, h1, h2⟩; exact ⟨x, y, hr, T, h1, h2⟩
  · rintro ⟨x, y, hr, T, h1, h2⟩; exact ⟨hr, T, x, y, h1, h2⟩

lemma bddBelow_affineBanachMazurSet (K L : Set E) : BddBelow (affineBanachMazurSet K L) :=
  ⟨1, fun _ hr => hr.1⟩

lemma banachMazurSet_subset_affineBanachMazurSet (K L : Set E) :
    banachMazurSet K L ⊆ affineBanachMazurSet K L := by
  intro r hr
  rw [mem_affineBanachMazurSet_iff]
  exact ⟨0, 0, by simpa using hr⟩

/-- Any two bounded sets with nonempty interior have nonempty affine Banach–Mazur set
(without requiring `0` to lie in their interiors). -/
lemma affineBanachMazurSet_nonempty {K L : Set E}
    (hKint : (interior K).Nonempty) (hKb : Bornology.IsBounded K)
    (hLint : (interior L).Nonempty) (hLb : Bornology.IsBounded L) :
    (affineBanachMazurSet K L).Nonempty := by
  obtain ⟨x, hx⟩ := hKint
  obtain ⟨y, hy⟩ := hLint
  have hK0 : (0 : E) ∈ interior ((fun z => z - x) '' K) := by
    let e : E ≃ₜ E := Homeomorph.addRight (-x)
    have himg : (fun z => z - x) '' K = e '' K := by ext w; simp [e, sub_eq_add_neg]
    rw [himg, ← e.image_interior]
    exact ⟨x, hx, by simp [e]⟩
  have hL0 : (0 : E) ∈ interior ((fun z => z - y) '' L) := by
    let e : E ≃ₜ E := Homeomorph.addRight (-y)
    have himg : (fun z => z - y) '' L = e '' L := by ext w; simp [e, sub_eq_add_neg]
    rw [himg, ← e.image_interior]
    exact ⟨y, hy, by simp [e]⟩
  have hKb' : Bornology.IsBounded ((fun z => z - x) '' K) := by
    obtain ⟨R, hKR⟩ := hKb.subset_closedBall x
    refine (Metric.isBounded_iff_subset_closedBall (0 : E)).mpr ⟨R, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    simpa [mem_closedBall, dist_eq_norm] using hKR hz
  have hLb' : Bornology.IsBounded ((fun z => z - y) '' L) := by
    obtain ⟨R, hLR⟩ := hLb.subset_closedBall y
    refine (Metric.isBounded_iff_subset_closedBall (0 : E)).mpr ⟨R, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    simpa [mem_closedBall, dist_eq_norm] using hLR hz
  obtain ⟨r, hr⟩ := banachMazurSet_nonempty hK0 hKb' hL0 hLb'
  exact ⟨r, mem_affineBanachMazurSet_iff.mpr ⟨x, y, hr⟩⟩

theorem one_le_affineBanachMazurDist {K L : Set E} (hne : (affineBanachMazurSet K L).Nonempty) :
    1 ≤ affineBanachMazurDist K L :=
  le_csInf hne fun _ hr => hr.1

theorem affineBanachMazurDist_self (K : Set E) : affineBanachMazurDist K K = 1 := by
  have h1 : (1 : ℝ) ∈ affineBanachMazurSet K K :=
    banachMazurSet_subset_affineBanachMazurSet K K
      ⟨le_rfl, LinearEquiv.refl ℝ E,
        fun x hx => ⟨x, hx, rfl⟩,
        by rintro _ ⟨x, hx, rfl⟩; exact ⟨x, hx, one_smul ℝ x⟩⟩
  exact le_antisymm (csInf_le (bddBelow_affineBanachMazurSet K K) h1)
    (one_le_affineBanachMazurDist ⟨1, h1⟩)

lemma affineBanachMazurSet_symm (K L : Set E) :
    affineBanachMazurSet K L = affineBanachMazurSet L K := by
  ext r
  simp only [mem_affineBanachMazurSet_iff]
  constructor
  · rintro ⟨x, y, hr⟩
    rw [banachMazurSet_symm] at hr
    exact ⟨y, x, hr⟩
  · rintro ⟨y, x, hr⟩
    rw [banachMazurSet_symm] at hr
    exact ⟨x, y, hr⟩

theorem affineBanachMazurDist_symm (K L : Set E) :
    affineBanachMazurDist K L = affineBanachMazurDist L K := by
  rw [affineBanachMazurDist, affineBanachMazurSet_symm, affineBanachMazurDist]

theorem affineBanachMazurDist_le_banachMazurDist {K L : Set E}
    (hne : (banachMazurSet K L).Nonempty) :
    affineBanachMazurDist K L ≤ banachMazurDist K L :=
  csInf_le_csInf (bddBelow_affineBanachMazurSet K L) hne
    (banachMazurSet_subset_affineBanachMazurSet K L)

theorem affineBanachMazurEDist_le_banachMazurEDist (K L : Set E) :
    affineBanachMazurEDist K L ≤ banachMazurEDist K L :=
  sInf_le_sInf (Set.image_mono (banachMazurSet_subset_affineBanachMazurSet K L))

lemma affineBanachMazurSet_affineEquiv_right (K L : Set E) (A : E ≃ᵃ[ℝ] E) :
    affineBanachMazurSet K (A '' L) = affineBanachMazurSet K L := by
  ext r
  simp only [mem_affineBanachMazurSet_iff]
  have hshift : ∀ y : E,
      (fun z : E => z - A y) '' (A '' L) = A.linear '' ((fun z : E => z - y) '' L) := by
    intro y
    ext w
    simp only [mem_image]
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z - y, ⟨z, hz, rfl⟩, (affineEquiv_sub A z y).symm⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨A z, ⟨z, hz, rfl⟩, affineEquiv_sub A z y⟩
  constructor
  · rintro ⟨x, y', hr⟩
    refine ⟨x, A.symm y', ?_⟩
    have hy' : A (A.symm y') = y' := A.apply_symm_apply y'
    rw [← hy', hshift, banachMazurSet_linearEquiv_right] at hr
    exact hr
  · rintro ⟨x, y, hr⟩
    refine ⟨x, A y, ?_⟩
    rw [hshift, banachMazurSet_linearEquiv_right]
    exact hr

/-- Right invariance of affine Banach–Mazur distance under all affine equivalences `E ≃ᵃ[ℝ] E`. -/
theorem affineBanachMazurDist_affineEquiv_right (K L : Set E) (A : E ≃ᵃ[ℝ] E) :
    affineBanachMazurDist K (A '' L) = affineBanachMazurDist K L := by
  rw [affineBanachMazurDist, affineBanachMazurSet_affineEquiv_right, affineBanachMazurDist]

/-- Left invariance of affine Banach–Mazur distance under all affine equivalences `E ≃ᵃ[ℝ] E`. -/
theorem affineBanachMazurDist_affineEquiv_left (K L : Set E) (A : E ≃ᵃ[ℝ] E) :
    affineBanachMazurDist (A '' K) L = affineBanachMazurDist K L := by
  rw [affineBanachMazurDist_symm, affineBanachMazurDist_affineEquiv_right,
    affineBanachMazurDist_symm]

private lemma affineBanachMazurSet_mul {K L M : Set E} {r₁ r₂ : ℝ}
    (hr₁ : r₁ ∈ affineBanachMazurSet K L) (hr₂ : r₂ ∈ affineBanachMazurSet L M) :
    r₁ * r₂ ∈ affineBanachMazurSet K M := by
  rcases hr₁ with ⟨h1_ge, T₁, x, y₁, hK1, h1K⟩
  rcases hr₂ with ⟨h2_ge, T₂, y₂, z, hL2, h2L⟩
  let v : E := T₁ (y₂ - y₁)
  -- Choose `w : E` so that `(1 - r₂) • v - w = -(r₁ * r₂) • w`.
  have hex_w : ∃ w : E, (1 - r₂) • v - w = -(r₁ * r₂) • w := by
    by_cases h12 : r₁ * r₂ = 1
    · have hr₂1 : r₂ = 1 := by nlinarith
      refine ⟨0, ?_⟩
      simp [hr₂1]
    · have hdenom : r₁ * r₂ - 1 ≠ 0 := sub_ne_zero.mpr h12
      refine ⟨((r₂ - 1) / (r₁ * r₂ - 1)) • v, ?_⟩
      rw [smul_smul, ← sub_smul]
      congr 1
      apply mul_right_cancel₀ hdenom
      rw [sub_mul, div_mul_cancel₀ _ hdenom, mul_assoc, div_mul_cancel₀ _ hdenom]
      ring
  obtain ⟨w, hw⟩ := hex_w
  let x' : E := x + w
  let z' : E := z - T₂.symm (T₁.symm (v - w))
  refine ⟨by nlinarith, T₂.trans T₁, x', z', ?_, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩
    rcases hK1 ⟨k, hk, rfl⟩ with ⟨_, ⟨l, hl, rfl⟩, hkl⟩
    rcases hL2 ⟨l, hl, rfl⟩ with ⟨_, ⟨m, hm, rfl⟩, hlm⟩
    refine ⟨m - z', ⟨m, hm, rfl⟩, ?_⟩
    change T₁ (T₂ (m - z')) = k - x'
    have hT2 : T₂ (m - z') = T₂ (m - z) + T₁.symm (v - w) := by
      have hmz : m - z' = (m - z) + T₂.symm (T₁.symm (v - w)) := by dsimp only [z']; abel
      rw [hmz, map_add, T₂.apply_symm_apply]
    have hly : l - y₁ = (l - y₂) + (y₂ - y₁) := by abel
    dsimp only at hkl hlm
    rw [hT2, map_add, T₁.apply_symm_apply, hlm]
    dsimp only [v, x']
    rw [← add_sub_assoc, ← map_add, ← hly, hkl]
    abel
  · rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    have hT2 : T₂ (m - z') = T₂ (m - z) + T₁.symm (v - w) := by
      have hmz : m - z' = (m - z) + T₂.symm (T₁.symm (v - w)) := by dsimp only [z']; abel
      rw [hmz, map_add, T₂.apply_symm_apply]
    rcases h2L ⟨m - z, ⟨m, hm, rfl⟩, rfl⟩ with ⟨_, ⟨l, hl, rfl⟩, hlm⟩
    rcases h1K ⟨l - y₁, ⟨l, hl, rfl⟩, rfl⟩ with ⟨_, ⟨k, hk, rfl⟩, hkl⟩
    refine ⟨k - x', ⟨k, hk, rfl⟩, ?_⟩
    change (r₁ * r₂) • (k - x') = T₁ (T₂ (m - z'))
    have hsub_ly : T₁ (l - y₂) = T₁ (l - y₁) - v := by
      dsimp only [v]
      rw [← map_sub]
      congr 1; abel
    have hT12 : T₁ (T₂ (m - z')) = ((1 - r₂) • v - w) + r₂ • T₁ (l - y₁) := by
      rw [hT2, map_add, T₁.apply_symm_apply, ← hlm, map_smul, hsub_ly, smul_sub, sub_smul, one_smul]
      abel
    rw [hT12, hw, ← hkl, smul_smul, mul_comm r₂ r₁]
    dsimp only [x']
    rw [show k - (x + w) = (k - x) - w by abel, smul_sub, neg_smul]
    abel

/-- **Multiplicative triangle inequality for affine Banach–Mazur distance:**
holds for all sets `K, L, M` with nonempty affine distortion sets. -/
theorem affineBanachMazurDist_mul_triangle {K L M : Set E}
    (hKL : (affineBanachMazurSet K L).Nonempty) (hLM : (affineBanachMazurSet L M).Nonempty) :
    affineBanachMazurDist K M ≤ affineBanachMazurDist K L * affineBanachMazurDist L M := by
  have hstep1 : ∀ r₁ ∈ affineBanachMazurSet K L,
      affineBanachMazurDist K M ≤ r₁ * affineBanachMazurDist L M := by
    intro r₁ hr₁
    have hr₁_pos : 0 < r₁ := lt_of_lt_of_le zero_lt_one hr₁.1
    rw [← div_le_iff₀' hr₁_pos]
    refine le_csInf hLM fun r₂ hr₂ => ?_
    rw [div_le_iff₀' hr₁_pos]
    exact csInf_le (bddBelow_affineBanachMazurSet K M) (affineBanachMazurSet_mul hr₁ hr₂)
  have hdLM_pos : 0 < affineBanachMazurDist L M :=
    lt_of_lt_of_le zero_lt_one (one_le_affineBanachMazurDist hLM)
  rw [← div_le_iff₀ hdLM_pos]
  refine le_csInf hKL fun r₁ hr₁ => ?_
  rw [div_le_iff₀ hdLM_pos]
  exact hstep1 r₁ hr₁

theorem affineBanachMazurEDist_eq_top_of_empty {K L : Set E}
    (hemp : affineBanachMazurSet K L = ∅) :
    affineBanachMazurEDist K L = ⊤ := by
  simp [affineBanachMazurEDist, hemp]

theorem affineBanachMazurEDist_eq_ofReal {K L : Set E}
    (hne : (affineBanachMazurSet K L).Nonempty) :
    affineBanachMazurEDist K L = ENNReal.ofReal (affineBanachMazurDist K L) := by
  apply le_antisymm
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε' : (0 : ℝ) < (ε : ℝ) := NNReal.coe_pos.mpr hε
    obtain ⟨r, hr_mem, hr_lt⟩ := Real.lt_sInf_add_pos hne hε'
    calc
      affineBanachMazurEDist K L ≤ ENNReal.ofReal r := sInf_le ⟨r, hr_mem, rfl⟩
      _ ≤ ENNReal.ofReal (affineBanachMazurDist K L + (ε : ℝ)) := ENNReal.ofReal_le_ofReal hr_lt.le
      _ = ENNReal.ofReal (affineBanachMazurDist K L) + (ε : ℝ≥0∞) := by
          rw [ENNReal.ofReal_add (le_trans zero_le_one (one_le_affineBanachMazurDist hne)) hε'.le,
            ENNReal.ofReal_coe_nnreal]
  · refine le_sInf ?_
    rintro _ ⟨r, hr, rfl⟩
    exact ENNReal.ofReal_le_ofReal (csInf_le (bddBelow_affineBanachMazurSet K L) hr)

theorem one_le_affineBanachMazurEDist (K L : Set E) : 1 ≤ affineBanachMazurEDist K L := by
  refine le_sInf ?_
  rintro _ ⟨r, hr, rfl⟩
  simpa using ENNReal.ofReal_le_ofReal hr.1

/-- **Unconditional multiplicative triangle inequality for `affineBanachMazurEDist`.** -/
theorem affineBanachMazurEDist_mul_triangle (K L M : Set E) :
    affineBanachMazurEDist K M ≤ affineBanachMazurEDist K L * affineBanachMazurEDist L M := by
  by_cases hKL : (affineBanachMazurSet K L).Nonempty
  · by_cases hLM : (affineBanachMazurSet L M).Nonempty
    · obtain ⟨r₁, hr₁⟩ := hKL
      obtain ⟨r₂, hr₂⟩ := hLM
      have hKM : (affineBanachMazurSet K M).Nonempty := ⟨r₁ * r₂, affineBanachMazurSet_mul hr₁ hr₂⟩
      rw [affineBanachMazurEDist_eq_ofReal hKM, affineBanachMazurEDist_eq_ofReal ⟨r₁, hr₁⟩,
        affineBanachMazurEDist_eq_ofReal ⟨r₂, hr₂⟩,
        ← ENNReal.ofReal_mul (le_trans zero_le_one (one_le_affineBanachMazurDist ⟨r₁, hr₁⟩))]
      exact ENNReal.ofReal_le_ofReal (affineBanachMazurDist_mul_triangle ⟨r₁, hr₁⟩ ⟨r₂, hr₂⟩)
    · rw [Set.not_nonempty_iff_eq_empty] at hLM
      rw [affineBanachMazurEDist_eq_top_of_empty hLM,
        ENNReal.mul_top (lt_of_lt_of_le zero_lt_one (one_le_affineBanachMazurEDist K L)).ne']
      exact le_top
  · rw [Set.not_nonempty_iff_eq_empty] at hKL
    rw [affineBanachMazurEDist_eq_top_of_empty hKL,
      ENNReal.top_mul (lt_of_lt_of_le zero_lt_one (one_le_affineBanachMazurEDist L M)).ne']
    exact le_top

end AffineBanachMazur

end

end ConvexGeom
