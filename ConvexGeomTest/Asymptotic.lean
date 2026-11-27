/-
Copyright (c) 2026 Yegor Gorodzha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yegor Gorodzha
-/
module

import ConvexGeom.Asymptotic

/-! Checks for `ConvexGeom.Asymptotic` (1D interval bounds, totalization, and Haar scaling). -/

namespace ConvexGeomChecks

open ConvexGeom MeasureTheory Metric Set
open scoped ENNReal Pointwise

/-- On `K = [-1, ε]` (`0 < ε < 1`) and `B = [-1, 1]`, the origin-fixed (linear) Banach–Mazur
distance equals `ε⁻¹` (which blows up as `ε → 0⁺`). -/
example {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    banachMazurDist (Icc (-1 : ℝ) ε) (Icc (-1 : ℝ) 1) = ε⁻¹ := by
  have hεinv_gt1 : 1 < ε⁻¹ := one_lt_inv₀ hε0 |>.mpr hε1
  have hmem : ε⁻¹ ∈ banachMazurSet (Icc (-1 : ℝ) ε) (Icc (-1 : ℝ) 1) := by
    refine ⟨hεinv_gt1.le, LinearEquiv.refl ℝ ℝ, ?_, ?_⟩
    · intro x ⟨hx1, hx2⟩
      exact ⟨x, ⟨hx1, hx2.trans hε1.le⟩, rfl⟩
    · rintro y ⟨x, ⟨hx1, hx2⟩, rfl⟩
      refine ⟨ε * x, ⟨?_, ?_⟩, ?_⟩
      · nlinarith
      · nlinarith
      · change ε⁻¹ * (ε * x) = x
        rw [← mul_assoc, inv_mul_cancel₀ hε0.ne', one_mul]
  have hle : banachMazurDist (Icc (-1 : ℝ) ε) (Icc (-1 : ℝ) 1) ≤ ε⁻¹ :=
    csInf_le (bddBelow_banachMazurSet _ _) hmem
  have hge : ε⁻¹ ≤ banachMazurDist (Icc (-1 : ℝ) ε) (Icc (-1 : ℝ) 1) := by
    refine le_csInf ⟨ε⁻¹, hmem⟩ ?_
    rintro r ⟨hr1, T, h1, h2⟩
    let c : ℝ := T 1
    have hT : ∀ t : ℝ, T t = t * c := fun t => by
      have := T.map_smul t (1 : ℝ)
      simpa [c, smul_eq_mul] using this
    -- `-1 ∈ T '' [-1, 1]` and `ε ∈ T '' [-1, 1]` force `1 ≤ |c|`.
    rcases h1 (show (-1 : ℝ) ∈ Icc (-1) ε by constructor <;> linarith) with ⟨t₀, ⟨ht0a, ht0b⟩, ht0eq⟩
    have hc_ge1 : 1 ≤ |c| := by
      have h1' : |t₀ * c| = 1 := by rw [← hT t₀, ht0eq]; norm_num
      rw [abs_mul] at h1'
      have ht0_le1 : |t₀| ≤ 1 := abs_le.mpr ⟨ht0a, ht0b⟩
      nlinarith [abs_nonneg c]
    -- Both `c` and `-c` lie in `T '' [-1, 1] ⊆ r • [-1, ε]`, so `|c| ∈ r • [-1, ε]` implies `|c| ≤ r * ε`.
    have habs_mem : |c| ∈ T '' Icc (-1 : ℝ) 1 := by
      rcases le_total 0 c with hc | hc
      · exact ⟨1, ⟨by norm_num, le_rfl⟩, by rw [hT, one_mul, abs_of_nonneg hc]⟩
      · exact ⟨-1, ⟨le_rfl, by norm_num⟩, by rw [hT, neg_one_mul, abs_of_nonpos hc]⟩
    rcases h2 habs_mem with ⟨u, ⟨_, hu2⟩, hru⟩
    have hcr : |c| ≤ r * ε := by
      change r * u = |c| at hru
      nlinarith
    have hr_ge : ε⁻¹ ≤ r := by
      have := mul_le_mul_of_nonneg_left (hc_ge1.trans hcr) (inv_nonneg.mpr hε0.le)
      rwa [mul_one, ← mul_assoc, mul_comm ε⁻¹ r, mul_assoc, inv_mul_cancel₀ hε0.ne', mul_one] at this
    exact hr_ge
  exact le_antisymm hle hge

/-- On the exact same `K = [-1, ε]` (`0 < ε < 1`) and `B = [-1, 1]`, the **affine** Banach–Mazur
distance is `1` (because recentering maps `[-1, ε]` affinely onto `[-1, 1]`). -/
example {ε : ℝ} (hε0 : 0 < ε) :
    affineBanachMazurDist (Icc (-1 : ℝ) ε) (Icc (-1 : ℝ) 1) = 1 := by
  let mid : ℝ := (ε - 1) / 2
  let rad : ℝ := (ε + 1) / 2
  have hrad_pos : 0 < rad := by dsimp only [rad]; linarith
  have h1 : (1 : ℝ) ∈ affineBanachMazurSet (Icc (-1 : ℝ) ε) (Icc (-1 : ℝ) 1) := by
    refine ⟨le_rfl, smulLinearEquiv hrad_pos.ne', mid, 0, ?_, ?_⟩
    · rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
      refine ⟨rad⁻¹ * (x - mid), ⟨rad⁻¹ * (x - mid), ⟨?_, ?_⟩, by simp⟩, ?_⟩
      · rw [← div_eq_inv_mul, le_div_iff₀ hrad_pos]; dsimp only [mid, rad]; linarith
      · rw [← div_eq_inv_mul, div_le_iff₀ hrad_pos]; dsimp only [mid, rad]; linarith
      · simp [smulLinearEquiv_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hrad_pos.ne']
    · rintro _ ⟨_, ⟨y, ⟨hy1, hy2⟩, rfl⟩, rfl⟩
      refine ⟨rad * y, ⟨mid + rad * y, ⟨?_, ?_⟩, by ring⟩, by simp [smulLinearEquiv_apply]⟩
      · dsimp only [mid, rad]; nlinarith
      · dsimp only [mid, rad]; nlinarith
  exact le_antisymm (csInf_le (bddBelow_affineBanachMazurSet _ _) h1)
    (one_le_affineBanachMazurDist ⟨1, h1⟩)

/-- Origin-centered Mahler volume counterexample on `K = [-1, ε]` (`0 < ε < 1`):
`mahlerVolume volume K > volume (closedBall 0 1) ^ 2` (`(1 + ε)(1 + ε⁻¹) > 4`),
whereas `santaloMahlerVolume volume K ≤ volume (closedBall 0 1) ^ 2`. -/
example {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    volume (closedBall (0 : ℝ) 1) ^ 2 < mahlerVolume volume (Icc (-1 : ℝ) ε) ∧
      santaloMahlerVolume volume (Icc (-1 : ℝ) ε) ≤ volume (closedBall (0 : ℝ) 1) ^ 2 := by
  have hpol : polarBody (Icc (-1 : ℝ) ε) = Icc (-1 : ℝ) ε⁻¹ := by
    ext y
    rw [mem_polarBody]
    simp only [mem_Icc, RCLike.inner_apply, conj_trivial]
    constructor
    · intro hy
      refine ⟨?_, ?_⟩
      · have := hy (-1) ⟨le_rfl, by linarith⟩; linarith
      · have hεy : y * ε ≤ 1 := hy ε ⟨by linarith, le_rfl⟩
        calc
          y = (y * ε) * ε⁻¹ := by field_simp [hε0.ne']
          _ ≤ 1 * ε⁻¹ := mul_le_mul_of_nonneg_right hεy (inv_nonneg.mpr hε0.le)
          _ = ε⁻¹ := one_mul _
    · rintro ⟨hy1, hy2⟩ x ⟨hx1, hx2⟩
      rcases le_total 0 y with hy0 | hy0
      · calc
          y * x ≤ y * ε := mul_le_mul_of_nonneg_left hx2 hy0
          _ ≤ ε⁻¹ * ε := mul_le_mul_of_nonneg_right hy2 hε0.le
          _ = 1 := inv_mul_cancel₀ hε0.ne'
      · nlinarith
  constructor
  · rw [mahlerVolume, hpol, Real.volume_Icc, Real.volume_Icc, Real.volume_closedBall,
      ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ ε - -1), sq,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2 * 1)]
    have hprod_pos : 0 < (ε - -1) * (ε⁻¹ - -1) :=
      mul_pos (by linarith) (by have := inv_pos.mpr hε0; linarith)
    apply (ENNReal.ofReal_lt_ofReal_iff hprod_pos).mpr
    have hsq : 0 < (1 - ε) ^ 2 := sq_pos_of_pos (sub_pos.mpr hε1)
    have hmul : (ε - -1) * (ε⁻¹ - -1) = 4 + (1 - ε) ^ 2 / ε := by
      field_simp [hε0.ne']; ring
    have hdiv_pos : 0 < (1 - ε) ^ 2 / ε := div_pos hsq hε0
    linarith
  · -- Centered at midpoint `mid = (ε - 1) / 2`, `K - mid = [-rad, rad]` has Mahler volume `4`.
    let mid : ℝ := (ε - 1) / 2
    let rad : ℝ := (ε + 1) / 2
    have hrad_pos : 0 < rad := by dsimp only [rad]; linarith
    have hmid_int : mid ∈ interior (Icc (-1 : ℝ) ε) := by
      rw [interior_Icc]
      dsimp only [mid]
      constructor <;> linarith
    have hshift : (fun x : ℝ => x - mid) '' Icc (-1 : ℝ) ε = closedBall (0 : ℝ) rad := by
      ext y
      simp only [mem_image, mem_Icc, mem_closedBall_zero_iff, Real.norm_eq_abs, abs_le]
      constructor
      · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
        dsimp only [mid, rad]; constructor <;> linarith
      · rintro ⟨hy1, hy2⟩
        refine ⟨y + mid, ⟨?_, ?_⟩, add_sub_cancel_right y mid⟩
        · dsimp only [mid, rad] at hy1 hy2 ⊢; linarith
        · dsimp only [mid, rad] at hy1 hy2 ⊢; linarith
    have hAt : mahlerVolumeAt volume (Icc (-1 : ℝ) ε) mid = volume (closedBall (0 : ℝ) 1) ^ 2 := by
      rw [mahlerVolumeAt, hshift]
      have hsmul : closedBall (0 : ℝ) rad = rad • closedBall (0 : ℝ) 1 := by
        ext y
        simp only [mem_closedBall_zero_iff, Set.mem_smul_set, smul_eq_mul, Real.norm_eq_abs]
        constructor
        · intro hy
          refine ⟨rad⁻¹ * y, ?_, by rw [← mul_assoc, mul_inv_cancel₀ hrad_pos.ne', one_mul]⟩
          rw [abs_mul, abs_of_pos (inv_pos.mpr hrad_pos), inv_mul_le_iff₀ hrad_pos, mul_one]
          exact hy
        · rintro ⟨u, hu, rfl⟩
          rw [abs_mul, abs_of_pos hrad_pos]
          nlinarith
      rw [hsmul, mahlerVolume_smul volume hrad_pos.ne', mahlerVolume, polarBody_closedBall one_pos,
        inv_one, sq]
    exact (santaloMahlerVolume_le_mahlerVolumeAt volume hmid_int).trans_eq hAt

/-- Infeasible Banach–Mazur pair: `banachMazurDist ∅ {0} = 0` via `Real.sInf_empty`,
whereas `banachMazurEDist ∅ {0} = ⊤`. -/
example :
    banachMazurDist (∅ : Set ℝ) {(0 : ℝ)} = 0 ∧
      banachMazurEDist (∅ : Set ℝ) {(0 : ℝ)} = ⊤ := by
  have hemp : banachMazurSet (∅ : Set ℝ) {(0 : ℝ)} = ∅ := by
    ext r
    simp only [banachMazurSet, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_exists]
    intro _ T _ h2
    have h0 : T 0 ∈ r • (∅ : Set ℝ) := h2 ⟨0, mem_singleton 0, rfl⟩
    simp at h0
  exact ⟨by rw [banachMazurDist, hemp, Real.sInf_empty], banachMazurEDist_eq_top_of_empty hemp⟩

/-- Haar-rescaling invariance of `sphereProb`. -/
example : sphereProb ((2 : ℝ≥0∞) • (volume : Measure ℝ)) = sphereProb volume :=
  sphereProb_smul volume (by norm_num) (by norm_num)

/-- Mean breadth equals `2 * meanWidth` on `bodyClosedBall 0 3`. -/
example :
    ∫ u : sphere (0 : ℝ) 1, width (bodyClosedBall (0 : ℝ) (by norm_num : (0 : ℝ) ≤ 3)) u.1
      ∂(sphereProb (volume : Measure ℝ)) = 6 := by
  rw [integral_width_eq_two_mul_meanWidth, meanWidth_bodyClosedBall]
  norm_num

/-- Concrete 1D Fritz John decomposition: `u 0 = 1`, `c 0 = 1` satisfies `sum_weights` (`= 1`)
and `banachMazurDist_closedBall_le_sqrt_finrank` on `bodyClosedBall 0 1`. -/
example :
    IsJohnDecomposition (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) ∧
      banachMazurDist (bodyClosedBall (0 : ℝ) zero_le_one : Set ℝ) (closedBall (0 : ℝ) 1) ≤
        Real.sqrt (Module.finrank ℝ ℝ : ℝ) := by
  refine ⟨⟨fun _ => by simp, fun _ => zero_lt_one, ?_⟩, ?_⟩
  · ext
    simp [rankOne_apply]
  · refine banachMazurDist_closedBall_le_sqrt_finrank (bodyClosedBall (0 : ℝ) zero_le_one) ?_ ?_
    · intro x hx
      simpa [coe_bodyClosedBall, mem_closedBall_zero_iff] using hx
    · rw [coe_bodyClosedBall]
      exact mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds 0 zero_lt_one)

/-- Ball's symmetric volume-ratio bound is tight in 1D (`volume [-1, 1] = 2 = 2^1`). -/
example :
    ∃ T : ℝ ≃ₗ[ℝ] ℝ,
      closedBall (0 : ℝ) 1 ⊆ T '' (bodyClosedBall (0 : ℝ) zero_le_one : Set ℝ) ∧
      volume (T '' (bodyClosedBall (0 : ℝ) zero_le_one : Set ℝ)) ≤
        (2 : ℝ≥0∞) ^ Module.finrank ℝ ℝ :=
  ball_volume_ratio_symmetric (bodyClosedBall (0 : ℝ) zero_le_one)
    (fun x hx => by simpa [coe_bodyClosedBall, mem_closedBall_zero_iff] using hx)
    (by rw [coe_bodyClosedBall]; exact mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds 0 zero_lt_one))

/-- Standard Gaussian second moment and Gaussian-width proportionality on `bodyClosedBall 0 3`. -/
example :
    (∫ x : ℝ, ‖x‖ ^ 2 ∂stdGaussian ℝ) = 1 ∧
      gaussianWidth (bodyClosedBall (0 : ℝ) (by norm_num : (0 : ℝ) ≤ 3)) =
        3 * ∫ x : ℝ, ‖x‖ ∂stdGaussian ℝ := by
  refine ⟨by simpa using integral_norm_sq_stdGaussian (E := ℝ), ?_⟩
  rw [gaussianWidth_eq_integral_norm_mul_meanWidth, meanWidth_bodyClosedBall, mul_comm]

/-- Blaschke–Santaló and Urysohn's inequality on `bodyClosedBall 0 3` in `ℝ` (where both are tight). -/
example :
    santaloMahlerVolume (volume : Measure ℝ)
        (bodyClosedBall (0 : ℝ) (by norm_num : (0 : ℝ) ≤ 3) : Set ℝ) ≤
      volume (closedBall (0 : ℝ) 1) ^ 2 ∧
    (volume.real (bodyClosedBall (0 : ℝ) (by norm_num : (0 : ℝ) ≤ 3) : Set ℝ) /
        volume.real (closedBall (0 : ℝ) 1)) ^ (1 / (Module.finrank ℝ ℝ : ℝ)) ≤
      meanWidth (bodyClosedBall (0 : ℝ) (by norm_num : (0 : ℝ) ≤ 3)) := by
  refine ⟨blaschke_santalo _ ⟨0, ?_⟩, urysohn_inequality _⟩
  rw [coe_bodyClosedBall]
  exact mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds 0 (by norm_num))

end ConvexGeomChecks
