/-
Copyright (c) 2026 Yegor Gorodzha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yegor Gorodzha
-/
module

public import ConvexGeom.Asymptotic.SphericalIntegration

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Spherical Isotropic Identity and the Steiner Point

Built on `ConvexGeom.Asymptotic.SphericalIntegration`, this file establishes the second-moment
isotropy of the uniform spherical measure `sphereProb volume` and develops the Steiner point of a
convex body.

## Main definitions

* `ConvexGeom.steinerPoint`: the Steiner point
  `steinerPoint K := d • ∫ u, supportFn K u • u ∂(sphereProb volume)`.

## Main statements

* `ConvexGeom.integral_sphereProb_id`, `ConvexGeom.integral_inner_sq_sphereProb`,
  `ConvexGeom.integral_inner_mul_inner_sphereProb`,
  `ConvexGeom.finrank_smul_integral_inner_smul_sphereProb`: spherical isotropic identities
  `∫ u, u = 0`, `∫ u, ⟪u, v⟫ * ⟪u, w⟫ = ⟪v, w⟫ / d`, and `d • ∫ u, ⟪x, u⟫ • u = x`.
* `ConvexGeom.steinerPoint_mem`: intrinsic selection `steinerPoint K ∈ (K : Set E)`.
* `ConvexGeom.dist_steinerPoint_le`, `ConvexGeom.lipschitzWith_steinerPoint`,
  `ConvexGeom.continuous_steinerPoint`: Hausdorff stability
  `dist (steinerPoint K) (steinerPoint L) ≤ √d * dist K L`.

## References

* [R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*][schneider2014], §1.7
-/

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ENNReal NNReal Pointwise

namespace ConvexGeom

public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ### 1. Spherical Isotropic Identity -/

/-- The mean of the unit vector on `sphere 0 1` under `sphereProb volume` is `0`. -/
theorem integral_sphereProb_id :
    ∫ u : sphere (0 : E) 1, (u : E) ∂(sphereProb (volume : Measure E)) = 0 := by
  have hmp := measurePreserving_sphereNeg_sphereProb (volume : Measure E)
  have hneg : ∫ u : sphere (0 : E) 1, (u : E) ∂(sphereProb (volume : Measure E)) =
      -(∫ u : sphere (0 : E) 1, (u : E) ∂(sphereProb (volume : Measure E))) := by
    have hcomp := hmp.integral_comp
      (sphereMap (LinearIsometryEquiv.neg ℝ (E := E))).measurableEmbedding
      (fun u : sphere (0 : E) 1 => (u : E))
    simpa [sphereMap_coe, integral_neg] using hcomp.symm
  have htwo : (2 : ℝ) • (∫ u : sphere (0 : E) 1, (u : E) ∂(sphereProb (volume : Measure E))) =
    0 := by
    rw [two_smul]
    conv_rhs =>
      rw [← add_neg_cancel (∫ u : sphere (0 : E) 1, (u : E) ∂(sphereProb (volume : Measure E)))]
    congr 1
  exact (smul_eq_zero.mp htwo).resolve_left two_ne_zero

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Helper: reflection across `(v - w)⊥` maps unit vector `v` to unit vector `w`. -/
private lemma exists_linearIsometry_map_eq {v w : E} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ∃ U : E ≃ₗᵢ[ℝ] E, U v = w := by
  by_cases hvw : v = w
  · exact ⟨LinearIsometryEquiv.refl ℝ E, hvw⟩
  · have hne : v - w ≠ 0 := sub_ne_zero.mpr hvw
    have hn_pos : 0 < ‖v - w‖ := norm_pos_iff.mpr hne
    let a : E := ‖v - w‖⁻¹ • (v - w)
    have ha : ‖a‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn_pos), inv_mul_cancel₀ hn_pos.ne']
    refine ⟨reflectHyperplane ha, ?_⟩
    rw [reflectHyperplane_apply]
    have hsq : ‖v - w‖ ^ 2 = 2 * (1 - ⟪v, w⟫) := by
      rw [norm_sub_sq_real, hv, hw]; ring
    have hinner : ⟪v, v - w⟫ = 1 - ⟪v, w⟫ := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq, hv, one_pow]
    have hcoeff : (2 * ⟪v, a⟫) * ‖v - w‖⁻¹ = 1 := by
      have h1 : ⟪v, a⟫ = ‖v - w‖⁻¹ * (1 - ⟪v, w⟫) := by
        dsimp only [a]
        rw [inner_smul_right, hinner]
      rw [h1]
      have h2 : 2 * (1 - ⟪v, w⟫) = ‖v - w‖ ^ 2 := hsq.symm
      field_simp [hn_pos.ne']
      linarith
    dsimp only [a]
    rw [smul_smul, hcoeff, one_smul, sub_sub_cancel]

/-- **Spherical Second Moment:**
for any `v : E` in dimension `d = finrank ℝ E ≥ 1`,
`∫ u, ⟪u, v⟫ ^ 2 ∂(sphereProb volume) = ‖v‖ ^ 2 / d`. -/
theorem integral_inner_sq_sphereProb [Nontrivial E] (v : E) :
    ∫ u : sphere (0 : E) 1, ⟪u.1, v⟫ ^ 2 ∂(sphereProb (volume : Measure E)) =
      ‖v‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
  set d := Module.finrank ℝ E
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr Module.finrank_pos
  have hunit_eq : ∀ {e₁ e₂ : E}, ‖e₁‖ = 1 → ‖e₂‖ = 1 →
      ∫ u : sphere (0 : E) 1, ⟪u.1, e₁⟫ ^ 2 ∂(sphereProb (volume : Measure E)) =
        ∫ u : sphere (0 : E) 1, ⟪u.1, e₂⟫ ^ 2 ∂(sphereProb (volume : Measure E)) := by
    intro e₁ e₂ he₁ he₂
    obtain ⟨U, hU⟩ := exists_linearIsometry_map_eq he₁ he₂
    have hmp := measurePreserving_sphereMap_sphereProb (volume : Measure E) U.symm
      U.symm.measurePreserving
    have hcomp := hmp.integral_comp (sphereMap U.symm).measurableEmbedding
      (fun u : sphere (0 : E) 1 => ⟪u.1, e₁⟫ ^ 2)
    rw [← hcomp]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have hinner : ⟪(sphereMap U.symm u : E), e₁⟫ = ⟪u.1, e₂⟫ := by
      rw [sphereMap_coe, ← hU, ← U.inner_map_map (U.symm u.1) e₁, U.apply_symm_apply]
    dsimp only
    rw [hinner]
  have hunit : ∀ {e : E}, ‖e‖ = 1 →
      ∫ u : sphere (0 : E) 1, ⟪u.1, e⟫ ^ 2 ∂(sphereProb (volume : Measure E)) = 1 / (d : ℝ) := by
    intro e he
    let b := stdOrthonormalBasis ℝ E
    have hint_i : ∀ i : Fin d,
        Integrable (fun u : sphere (0 : E) 1 => ⟪u.1, b i⟫ ^ 2)
          (sphereProb (volume : Measure E)) := fun i =>
      ((continuous_subtype_val.inner continuous_const).pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hsum_pt : ∀ u : sphere (0 : E) 1, ∑ i : Fin d, ⟪u.1, b i⟫ ^ 2 = 1 := fun u => by
      have hnorm := b.sum_sq_inner_right u.1
      rw [mem_sphere_zero_iff_norm.mp u.2, one_pow] at hnorm
      simpa [real_inner_comm] using hnorm
    have hsum_int :
        (∑ i : Fin d, ∫ u : sphere (0 : E) 1, ⟪u.1, b i⟫ ^ 2 ∂(sphereProb (volume : Measure E))) =
          1 := by
      rw [← integral_finsetSum Finset.univ (fun i _ => hint_i i)]
      simp_rw [hsum_pt]
      simp [integral_const]
    have hconst : ∀ i : Fin d,
        ∫ u : sphere (0 : E) 1, ⟪u.1, b i⟫ ^ 2 ∂(sphereProb (volume : Measure E)) =
          ∫ u : sphere (0 : E) 1, ⟪u.1, e⟫ ^ 2 ∂(sphereProb (volume : Measure E)) := fun i =>
      hunit_eq (b.orthonormal.1 i) he
    simp_rw [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum_int
    exact eq_one_div_of_mul_eq_one_right hsum_int
  by_cases hv : v = 0
  · simp [hv]
  · have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let e : E := ‖v‖⁻¹ • v
    have he : ‖e‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvn), inv_mul_cancel₀ hvn.ne']
    have hv_eq : v = ‖v‖ • e := by
      dsimp only [e]; rw [smul_smul, mul_inv_cancel₀ hvn.ne', one_smul]
    have hfun : (fun u : sphere (0 : E) 1 => ⟪u.1, v⟫ ^ 2) =
        fun u : sphere (0 : E) 1 => ‖v‖ ^ 2 * ⟪u.1, e⟫ ^ 2 := by
      ext u
      conv_lhs => rw [hv_eq]
      rw [inner_smul_right, mul_pow]
    rw [hfun, integral_const_mul, hunit he, mul_one_div]

/-- **Spherical Bilinear Covariance:**
for any `v, w : E` in dimension `d = finrank ℝ E ≥ 1`,
`∫ u, ⟪u, v⟫ * ⟪u, w⟫ ∂(sphereProb volume) = ⟪v, w⟫ / d`. -/
theorem integral_inner_mul_inner_sphereProb [Nontrivial E] (v w : E) :
    ∫ u : sphere (0 : E) 1, ⟪u.1, v⟫ * ⟪u.1, w⟫ ∂(sphereProb (volume : Measure E)) =
      ⟪v, w⟫ / (Module.finrank ℝ E : ℝ) := by
  have hint : ∀ z : E,
      Integrable (fun u : sphere (0 : E) 1 => ⟪u.1, z⟫ ^ 2)
        (sphereProb (volume : Measure E)) := fun z =>
    ((continuous_subtype_val.inner continuous_const).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpol : (fun u : sphere (0 : E) 1 => ⟪u.1, v⟫ * ⟪u.1, w⟫) =
      fun u : sphere (0 : E) 1 => (1 / 4 : ℝ) * (⟪u.1, v + w⟫ ^ 2 - ⟪u.1, v - w⟫ ^ 2) := by
    ext u
    rw [inner_add_right, inner_sub_right]
    ring
  rw [hpol, integral_const_mul, integral_sub (hint (v + w)) (hint (v - w)),
    integral_inner_sq_sphereProb (v + w), integral_inner_sq_sphereProb (v - w),
    norm_add_sq_real, norm_sub_sq_real]
  ring

/-- **Vector-Valued Isotropic Identity:**
for every `x : E` in dimension `d = finrank ℝ E ≥ 1`,
`d • ∫ u, ⟪x, u⟫ • u ∂(sphereProb volume) = x`. -/
theorem finrank_smul_integral_inner_smul_sphereProb [Nontrivial E] (x : E) :
    (Module.finrank ℝ E : ℝ) •
        ∫ u : sphere (0 : E) 1, ⟪x, u.1⟫ • (u.1 : E) ∂(sphereProb (volume : Measure E)) =
      x := by
  set d := Module.finrank ℝ E
  have hd_ne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  refine ext_inner_right ℝ fun v => ?_
  have hint : Integrable (fun u : sphere (0 : E) 1 => ⟪x, u.1⟫ • (u.1 : E))
      (sphereProb (volume : Measure E)) :=
    ((continuous_const.inner continuous_subtype_val).smul
      continuous_subtype_val).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [inner_smul_left, RCLike.conj_to_real]
  have hcomm : ⟪∫ u : sphere (0 : E) 1, ⟪x, u.1⟫ • (u.1 : E) ∂(sphereProb (volume : Measure E)),
    v⟫ =
      ∫ u : sphere (0 : E) 1, ⟪u.1, x⟫ * ⟪u.1, v⟫ ∂(sphereProb (volume : Measure E)) := by
    have h := (innerSL ℝ v).integral_comp_comm hint
    rw [real_inner_comm v _]
    have h' : ⟪v, ∫ u : sphere (0 : E) 1, ⟪x, u.1⟫ • (u.1 : E) ∂(sphereProb (volume : Measure E))⟫ =
        ∫ u : sphere (0 : E) 1, ⟪x, u.1⟫ * ⟪v, u.1⟫ ∂(sphereProb (volume : Measure E)) := by
      simpa using h.symm
    rw [h']
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    rw [real_inner_comm x u.1, real_inner_comm v u.1]
  rw [hcomm, integral_inner_mul_inner_sphereProb x v, mul_div_cancel₀ _ hd_ne]

/-! ### 2. The Steiner Point of a Convex Body -/

/-- The **Steiner point** of a convex body `K : ConvexBody E`:
`steinerPoint K := (finrank ℝ E : ℝ) • ∫ u, supportFn K u • u ∂(sphereProb volume)`. -/
@[expose]
noncomputable def steinerPoint (K : ConvexBody E) : E :=
  (Module.finrank ℝ E : ℝ) •
    ∫ u : sphere (0 : E) 1, supportFn K u.1 • (u.1 : E) ∂(sphereProb (volume : Measure E))

lemma integrable_supportFn_smul_sphereProb [Nontrivial E] (K : ConvexBody E) :
    Integrable (fun u : sphere (0 : E) 1 => supportFn K u.1 • (u.1 : E))
      (sphereProb (volume : Measure E)) :=
  (((continuous_supportFn K).comp continuous_subtype_val).smul
    continuous_subtype_val).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

@[simp]
theorem steinerPoint_bodySingleton [Nontrivial E] (x : E) :
    steinerPoint (bodySingleton x) = x := by
  unfold steinerPoint
  simp_rw [supportFn_bodySingleton]
  exact finrank_smul_integral_inner_smul_sphereProb x

theorem steinerPoint_add [Nontrivial E] (K L : ConvexBody E) :
    steinerPoint (K + L) = steinerPoint K + steinerPoint L := by
  unfold steinerPoint
  have hfun : (fun u : sphere (0 : E) 1 => supportFn (K + L) u.1 • (u.1 : E)) =
      fun u : sphere (0 : E) 1 => supportFn K u.1 • (u.1 : E) + supportFn L u.1 • (u.1 : E) := by
    ext u; rw [supportFn_minkowski_add, add_smul]
  rw [hfun, integral_add (integrable_supportFn_smul_sphereProb K)
    (integrable_supportFn_smul_sphereProb L), smul_add]

theorem steinerPoint_smul (K : ConvexBody E) {c : ℝ} (hc : 0 ≤ c) :
    steinerPoint (c • K) = c • steinerPoint K := by
  unfold steinerPoint
  have hfun : (fun u : sphere (0 : E) 1 => supportFn (c • K) u.1 • (u.1 : E)) =
      fun u : sphere (0 : E) 1 => c • (supportFn K u.1 • (u.1 : E)) := by
    ext u; rw [supportFn_body_smul K hc, mul_smul]
  rw [hfun, integral_smul, smul_comm]

theorem steinerPoint_translate [Nontrivial E] (K : ConvexBody E) (x : E) :
    steinerPoint (K + bodySingleton x) = steinerPoint K + x := by
  rw [steinerPoint_add, steinerPoint_bodySingleton]

theorem steinerPoint_neg_one_smul (K : ConvexBody E) :
    steinerPoint ((-1 : ℝ) • K) = -steinerPoint K := by
  unfold steinerPoint
  have hmp := measurePreserving_sphereNeg_sphereProb (volume : Measure E)
  have hcomp := hmp.integral_comp
    (sphereMap (LinearIsometryEquiv.neg ℝ (E := E))).measurableEmbedding
    (fun u : sphere (0 : E) 1 => supportFn K u.1 • (u.1 : E))
  have hfun : (fun u : sphere (0 : E) 1 => supportFn ((-1 : ℝ) • K) u.1 • (u.1 : E)) =
      fun u : sphere (0 : E) 1 => -(supportFn K (-u.1) • (-u.1 : E)) := by
    ext u
    rw [supportFn_neg_one_smul, smul_neg, neg_neg]
  rw [hfun, integral_neg]
  have hneg_eq :
      ∫ u : sphere (0 : E) 1, supportFn K (-u.1) • (-u.1 : E) ∂(sphereProb (volume : Measure E)) =
        ∫ u : sphere (0 : E) 1, supportFn K u.1 • (u.1 : E) ∂(sphereProb (volume : Measure E)) := by
    simpa [sphereMap_coe] using hcomp
  rw [hneg_eq, smul_neg]

/-- Orthogonal equivariance of the Steiner point:
`steinerPoint (U K) = U (steinerPoint K)` for every `U : E ≃ₗᵢ[ℝ] E`. -/
theorem steinerPoint_mapLinearIsometry [Nontrivial E] (U : E ≃ₗᵢ[ℝ] E) (K : ConvexBody E) :
    steinerPoint (mapLinear U.toLinearIsometry.toContinuousLinearMap K) = U (steinerPoint K) := by
  unfold steinerPoint
  rw [map_smul]
  congr 1
  have hcomm := U.toContinuousLinearMap.integral_comp_comm (integrable_supportFn_smul_sphereProb K)
  have hmp := measurePreserving_sphereMap_sphereProb (volume : Measure E) U.symm
    U.symm.measurePreserving
  have hcomp := hmp.integral_comp (sphereMap U.symm).measurableEmbedding
    (fun u : sphere (0 : E) 1 => supportFn K u.1 • U u.1)
  have hfun : (fun u : sphere (0 : E) 1 =>
        supportFn (mapLinear U.toLinearIsometry.toContinuousLinearMap K) u.1 • (u.1 : E)) =
      fun u : sphere (0 : E) 1 => supportFn K (U.symm u.1) • U (U.symm u.1) := by
    ext u
    rw [supportFn_mapLinearIsometry, U.apply_symm_apply]
  rw [hfun]
  calc
    ∫ u : sphere (0 : E) 1, supportFn K (U.symm u.1) • U (U.symm u.1)
        ∂(sphereProb (volume : Measure E))
      = ∫ u : sphere (0 : E) 1, supportFn K u.1 • U u.1
          ∂(sphereProb (volume : Measure E)) := by simpa [sphereMap_coe] using hcomp
    _ = ∫ u : sphere (0 : E) 1, U.toContinuousLinearMap (supportFn K u.1 • (u.1 : E))
          ∂(sphereProb (volume : Measure E)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          simp [map_smul]
    _ = U (∫ u : sphere (0 : E) 1, supportFn K u.1 • (u.1 : E)
          ∂(sphereProb (volume : Measure E))) := hcomm

@[simp]
theorem steinerPoint_bodyClosedBall [Nontrivial E] (c : E) {r : ℝ} (hr : 0 ≤ r) :
    steinerPoint (bodyClosedBall c hr) = c := by
  unfold steinerPoint
  have hfun : (fun u : sphere (0 : E) 1 => supportFn (bodyClosedBall c hr) u.1 • (u.1 : E)) =
      fun u : sphere (0 : E) 1 => ⟪c, u.1⟫ • (u.1 : E) + r • (u.1 : E) := by
    ext u
    rw [supportFn_bodyClosedBall, mem_sphere_zero_iff_norm.mp u.2, mul_one, add_smul]
  have hint1 : Integrable (fun u : sphere (0 : E) 1 => ⟪c, u.1⟫ • (u.1 : E))
      (sphereProb (volume : Measure E)) :=
    ((continuous_const.inner continuous_subtype_val).smul
      continuous_subtype_val).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint2 : Integrable (fun u : sphere (0 : E) 1 => r • (u.1 : E))
      (sphereProb (volume : Measure E)) :=
    (continuous_const.smul continuous_subtype_val).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [hfun, integral_add hint1 hint2, integral_smul, integral_sphereProb_id, smul_zero, add_zero]
  exact finrank_smul_integral_inner_smul_sphereProb c

/-- Helper: inner product of `steinerPoint K` with any `v : E`. -/
private lemma inner_steinerPoint [Nontrivial E] (K : ConvexBody E) (v : E) :
    ⟪steinerPoint K, v⟫ =
      (Module.finrank ℝ E : ℝ) *
        ∫ u : sphere (0 : E) 1, supportFn K u.1 * ⟪u.1, v⟫
          ∂(sphereProb (volume : Measure E)) := by
  unfold steinerPoint
  rw [inner_smul_left, RCLike.conj_to_real]
  congr 1
  have hcomm := (innerSL ℝ v).integral_comp_comm (integrable_supportFn_smul_sphereProb K)
  rw [real_inner_comm v _]
  have hrew : ⟪v, ∫ u : sphere (0 : E) 1, supportFn K u.1 • (u.1 : E)
        ∂(sphereProb (volume : Measure E))⟫ =
      ∫ u : sphere (0 : E) 1, supportFn K u.1 * ⟪v, u.1⟫
        ∂(sphereProb (volume : Measure E)) := by
    simpa using hcomm.symm
  rw [hrew]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  dsimp only
  rw [real_inner_comm v u.1]

/-- **Intrinsic Selection (`steinerPoint_mem`):**
for every convex body `K : ConvexBody E` in dimension `≥ 1`, its Steiner point lies in `K`. -/
theorem steinerPoint_mem [Nontrivial E] (K : ConvexBody E) :
    steinerPoint K ∈ (K : Set E) := by
  set d := Module.finrank ℝ E
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr Module.finrank_pos
  change steinerPoint K ∈ K
  rw [mem_iff_forall_inner_le_supportFn]
  have hunit : ∀ {v : E}, ‖v‖ = 1 → ⟪steinerPoint K, v⟫ ≤ supportFn K v := by
    intro v hv
    let R := reflectHyperplane hv
    have hmp := measurePreserving_sphereMap_sphereProb (volume : Measure E) R R.measurePreserving
    set I := ∫ u : sphere (0 : E) 1, supportFn K u.1 * ⟪u.1, v⟫
      ∂(sphereProb (volume : Measure E))
    have hint1 : Integrable (fun u : sphere (0 : E) 1 => supportFn K u.1 * ⟪u.1, v⟫)
        (sphereProb (volume : Measure E)) :=
      (((continuous_supportFn K).comp continuous_subtype_val).mul
        (continuous_subtype_val.inner continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hint2 : Integrable (fun u : sphere (0 : E) 1 => supportFn K (R u.1) * ⟪u.1, v⟫)
        (sphereProb (volume : Measure E)) :=
      (((continuous_supportFn K).comp (R.continuous.comp continuous_subtype_val)).mul
        (continuous_subtype_val.inner continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hI_refl : I =
        -(∫ u : sphere (0 : E) 1, supportFn K (R u.1) * ⟪u.1, v⟫
          ∂(sphereProb (volume : Measure E))) := by
      have hcomp := hmp.integral_comp (sphereMap R).measurableEmbedding
        (fun u : sphere (0 : E) 1 => supportFn K u.1 * ⟪u.1, v⟫)
      dsimp only [I]
      rw [← hcomp]
      have hfun : (fun u : sphere (0 : E) 1 => supportFn K (sphereMap R u : E) *
            ⟪(sphereMap R u : E), v⟫) =
          fun u : sphere (0 : E) 1 => -(supportFn K (R u.1) * ⟪u.1, v⟫) := by
        ext u
        have hinner : ⟪R u.1, v⟫ = -⟪u.1, v⟫ := by
          rw [reflectHyperplane_apply, inner_sub_left, inner_smul_left, RCLike.conj_to_real,
            real_inner_self_eq_norm_sq, hv, one_pow, mul_one]
          ring
        rw [sphereMap_coe, hinner, mul_neg]
      rw [hfun, integral_neg]
    have h2I : 2 * I =
        ∫ u : sphere (0 : E) 1, (supportFn K u.1 - supportFn K (R u.1)) * ⟪u.1, v⟫
          ∂(sphereProb (volume : Measure E)) := by
      have hsub := integral_sub hint1 hint2
      have hrew : (fun u : sphere (0 : E) 1 => (supportFn K u.1 - supportFn K (R u.1)) * ⟪u.1, v⟫) =
          fun u : sphere (0 : E) 1 =>
            supportFn K u.1 * ⟪u.1, v⟫ - supportFn K (R u.1) * ⟪u.1, v⟫ := by
        ext u; ring
      rw [hrew, hsub]
      linarith
    have hpt : ∀ u : sphere (0 : E) 1,
        (supportFn K u.1 - supportFn K (R u.1)) * ⟪u.1, v⟫ ≤
          (2 * supportFn K v) * ⟪u.1, v⟫ ^ 2 := fun u => by
      rcases le_total 0 ⟪u.1, v⟫ with hpos | hneg
      · have hu_eq : u.1 = R u.1 + (2 * ⟪u.1, v⟫) • v := by
          rw [reflectHyperplane_apply, sub_add_cancel]
        have hsub := supportFn_add_le K (R u.1) ((2 * ⟪u.1, v⟫) • v)
        rw [← hu_eq, supportFn_smul K (by linarith) v] at hsub
        have hdiff : supportFn K u.1 - supportFn K (R u.1) ≤ 2 * ⟪u.1, v⟫ * supportFn K v := by
          linarith
        have hmul := mul_le_mul_of_nonneg_right hdiff hpos
        linarith
      · have hRu_eq : R u.1 = u.1 + (-2 * ⟪u.1, v⟫) • v := by
          rw [reflectHyperplane_apply]
          module
        have hsub := supportFn_add_le K u.1 ((-2 * ⟪u.1, v⟫) • v)
        rw [← hRu_eq, supportFn_smul K (by linarith) v] at hsub
        have hdiff : supportFn K (R u.1) - supportFn K u.1 ≤ (-2 * ⟪u.1, v⟫) * supportFn K v := by
          linarith
        have hmul := mul_le_mul_of_nonneg_right hdiff (by linarith : 0 ≤ -⟪u.1, v⟫)
        linarith
    have hint_lhs : Integrable (fun u : sphere (0 : E) 1 =>
          (supportFn K u.1 - supportFn K (R u.1)) * ⟪u.1, v⟫)
        (sphereProb (volume : Measure E)) := by
      have hrew : (fun u : sphere (0 : E) 1 => (supportFn K u.1 - supportFn K (R u.1)) * ⟪u.1, v⟫) =
          fun u : sphere (0 : E) 1 =>
            supportFn K u.1 * ⟪u.1, v⟫ - supportFn K (R u.1) * ⟪u.1, v⟫ := by
        ext u; ring
      rw [hrew]
      exact hint1.sub hint2
    have hint_rhs : Integrable (fun u : sphere (0 : E) 1 => (2 * supportFn K v) * ⟪u.1, v⟫ ^ 2)
        (sphereProb (volume : Measure E)) :=
      (continuous_const.mul
        ((continuous_subtype_val.inner continuous_const).pow 2)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have h2I_le : 2 * I ≤ (2 * supportFn K v) / (d : ℝ) := by
      calc
        2 * I ≤ ∫ u : sphere (0 : E) 1, (2 * supportFn K v) * ⟪u.1, v⟫ ^ 2
            ∂(sphereProb (volume : Measure E)) := by
              rw [h2I]; exact integral_mono hint_lhs hint_rhs hpt
        _ = (2 * supportFn K v) *
              ∫ u : sphere (0 : E) 1, ⟪u.1, v⟫ ^ 2 ∂(sphereProb (volume : Measure E)) :=
              integral_const_mul _ _
        _ = (2 * supportFn K v) * (1 / (d : ℝ)) := by
              rw [integral_inner_sq_sphereProb v, hv, one_pow]
        _ = (2 * supportFn K v) / (d : ℝ) := by rw [mul_one_div]
    rw [inner_steinerPoint]
    have hdI : (d : ℝ) * I ≤ supportFn K v := by
      have hmul := mul_le_mul_of_nonneg_left h2I_le hd_pos.le
      rw [mul_div_cancel₀ _ hd_pos.ne'] at hmul
      linarith
    exact hdI
  intro v
  by_cases hv : v = 0
  · simp [hv]
  · have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let e : E := ‖v‖⁻¹ • v
    have he : ‖e‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvn), inv_mul_cancel₀ hvn.ne']
    have hv_eq : v = ‖v‖ • e := by
      dsimp only [e]; rw [smul_smul, mul_inv_cancel₀ hvn.ne', one_smul]
    rw [hv_eq, inner_smul_right, supportFn_smul K hvn.le e]
    exact mul_le_mul_of_nonneg_left (hunit he) hvn.le

/-- **Hausdorff Stability of the Steiner Point:**
`dist (steinerPoint K) (steinerPoint L) ≤ √(finrank ℝ E) * dist K L`. -/
theorem dist_steinerPoint_le [Nontrivial E] (K L : ConvexBody E) :
    dist (steinerPoint K) (steinerPoint L) ≤
      Real.sqrt (Module.finrank ℝ E : ℝ) * dist K L := by
  set d := Module.finrank ℝ E
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr Module.finrank_pos
  rw [dist_eq_norm]
  set w : E := steinerPoint K - steinerPoint L
  by_cases hw : w = 0
  · rw [hw, norm_zero]; positivity
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let v : E := ‖w‖⁻¹ • w
  have hv : ‖v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwn), inv_mul_cancel₀ hwn.ne']
  have hnorm_eq : ‖w‖ = ⟪w, v⟫ := by
    dsimp only [v]
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [hwn.ne']
  have hinner_diff : ⟪w, v⟫ =
      (d : ℝ) * ∫ u : sphere (0 : E) 1, (supportFn K u.1 - supportFn L u.1) * ⟪u.1, v⟫
        ∂(sphereProb (volume : Measure E)) := by
    dsimp only [w]
    rw [inner_sub_left, inner_steinerPoint, inner_steinerPoint, ← mul_sub]
    congr 1
    have hintK : Integrable (fun u : sphere (0 : E) 1 => supportFn K u.1 * ⟪u.1, v⟫)
        (sphereProb (volume : Measure E)) :=
      (((continuous_supportFn K).comp continuous_subtype_val).mul
        (continuous_subtype_val.inner continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hintL : Integrable (fun u : sphere (0 : E) 1 => supportFn L u.1 * ⟪u.1, v⟫)
        (sphereProb (volume : Measure E)) :=
      (((continuous_supportFn L).comp continuous_subtype_val).mul
        (continuous_subtype_val.inner continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [← integral_sub hintK hintL]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)
  -- Cauchy–Schwarz on `sphereProb volume`: `(∫ |⟪u, v⟫|)² ≤ ∫ ⟪u, v⟫² = 1 / d`.
  have hint_abs : Integrable (fun u : sphere (0 : E) 1 => |⟪u.1, v⟫|)
      (sphereProb (volume : Measure E)) :=
    (continuous_subtype_val.inner continuous_const).abs.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hint_sq : Integrable (fun u : sphere (0 : E) 1 => ⟪u.1, v⟫ ^ 2)
      (sphereProb (volume : Measure E)) :=
    ((continuous_subtype_val.inner continuous_const).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  set m := ∫ u : sphere (0 : E) 1, |⟪u.1, v⟫| ∂(sphereProb (volume : Measure E))
  have hm_nonneg : 0 ≤ m := integral_nonneg fun u => abs_nonneg _
  have hm_sq : m ^ 2 ≤ 1 / (d : ℝ) := by
    have h0 : 0 ≤ ∫ u : sphere (0 : E) 1, (|⟪u.1, v⟫| - m) ^ 2
        ∂(sphereProb (volume : Measure E)) := integral_nonneg fun _ => sq_nonneg _
    have hsplit :
        ∫ u : sphere (0 : E) 1, (|⟪u.1, v⟫| - m) ^ 2 ∂(sphereProb (volume : Measure E)) =
          (∫ u : sphere (0 : E) 1, ⟪u.1, v⟫ ^ 2 ∂(sphereProb (volume : Measure E))) -
            (2 * m) * (∫ u : sphere (0 : E) 1, |⟪u.1, v⟫| ∂(sphereProb (volume : Measure E))) +
            m ^ 2 := by
      have hexp : (fun u : sphere (0 : E) 1 => (|⟪u.1, v⟫| - m) ^ 2) =
          fun u : sphere (0 : E) 1 => (⟪u.1, v⟫ ^ 2 - (2 * m) * |⟪u.1, v⟫|) + m ^ 2 := by
        ext u; rw [sub_sq, sq_abs]; ring
      rw [hexp,
        integral_add (f := fun u : sphere (0 : E) 1 => ⟪u.1, v⟫ ^ 2 - (2 * m) * |⟪u.1, v⟫|)
          (g := fun _ => m ^ 2) (hint_sq.sub (hint_abs.const_mul _)) (integrable_const _),
        integral_sub (f := fun u : sphere (0 : E) 1 => ⟪u.1, v⟫ ^ 2)
          (g := fun u : sphere (0 : E) 1 => (2 * m) * |⟪u.1, v⟫|)
          hint_sq (hint_abs.const_mul _),
        integral_const_mul]
      simp [integral_const]
    rw [hsplit, integral_inner_sq_sphereProb v, hv, one_pow] at h0
    linarith
  have hm_le : m ≤ 1 / Real.sqrt (d : ℝ) := by
    calc
      m = Real.sqrt (m ^ 2) := (Real.sqrt_sq hm_nonneg).symm
      _ ≤ Real.sqrt (1 / (d : ℝ)) := Real.sqrt_le_sqrt hm_sq
      _ = 1 / Real.sqrt (d : ℝ) := by rw [Real.sqrt_div zero_le_one, Real.sqrt_one]
  have hpt_le : ∀ u : sphere (0 : E) 1,
      (supportFn K u.1 - supportFn L u.1) * ⟪u.1, v⟫ ≤ dist K L * |⟪u.1, v⟫| := fun u => by
    have h1 : |supportFn K u.1 - supportFn L u.1| ≤ dist K L :=
      (dist_le_iff_supportFn_sub_le dist_nonneg).mp le_rfl u.1 (mem_sphere_zero_iff_norm.mp u.2).le
    calc
      (supportFn K u.1 - supportFn L u.1) * ⟪u.1, v⟫
        ≤ |(supportFn K u.1 - supportFn L u.1) * ⟪u.1, v⟫| := le_abs_self _
      _ = |supportFn K u.1 - supportFn L u.1| * |⟪u.1, v⟫| := abs_mul _ _
      _ ≤ dist K L * |⟪u.1, v⟫| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have hint_prod : Integrable
      (fun u : sphere (0 : E) 1 => (supportFn K u.1 - supportFn L u.1) * ⟪u.1, v⟫)
      (sphereProb (volume : Measure E)) :=
    ((((continuous_supportFn K).comp continuous_subtype_val).sub
      ((continuous_supportFn L).comp continuous_subtype_val)).mul
      (continuous_subtype_val.inner continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    ‖w‖ = (d : ℝ) * ∫ u : sphere (0 : E) 1, (supportFn K u.1 - supportFn L u.1) * ⟪u.1, v⟫
          ∂(sphereProb (volume : Measure E)) := by rw [hnorm_eq, hinner_diff]
    _ ≤ (d : ℝ) * ∫ u : sphere (0 : E) 1, dist K L * |⟪u.1, v⟫|
          ∂(sphereProb (volume : Measure E)) :=
        mul_le_mul_of_nonneg_left (integral_mono hint_prod (hint_abs.const_mul _) hpt_le) hd_pos.le
    _ = (d : ℝ) * (dist K L * m) := by rw [integral_const_mul]
    _ ≤ (d : ℝ) * (dist K L * (1 / Real.sqrt (d : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm_le dist_nonneg) hd_pos.le
    _ = Real.sqrt (d : ℝ) * dist K L := by
        have hsqrt_ne : Real.sqrt (d : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hd_pos).ne'
        have hsq : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt hd_pos.le
        field_simp [hsqrt_ne]
        rw [hsq]
        ring

theorem lipschitzWith_steinerPoint [Nontrivial E] :
    LipschitzWith ⟨Real.sqrt (Module.finrank ℝ E : ℝ), Real.sqrt_nonneg _⟩
      (steinerPoint (E := E)) :=
  LipschitzWith.of_dist_le_mul dist_steinerPoint_le

theorem continuous_steinerPoint [Nontrivial E] :
    Continuous (steinerPoint (E := E)) :=
  lipschitzWith_steinerPoint.continuous

end

end ConvexGeom
