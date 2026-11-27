/-
Copyright (c) 2026 Yegor Gorodzha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yegor Gorodzha
-/
module

public import ConvexGeom.Metric.SupportFunction
public import ConvexGeom.Polytope.GeneralPosition
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Continuity, Stability, and Symmetric-Difference Metric of Volume

Metric-measure foundations for `ConvexBody E` in a finite-dimensional real inner product space `E`
equipped with an additive Haar measure `μ`.

## Main definitions

* `ConvexGeom.symmDiffVol`, `ConvexGeom.symmDiffVolReal`: `ℝ≥0∞`- and `ℝ`-valued symmetric
  difference volume `μ (A ∆ B)`.

## Main statements

* `ConvexGeom.addHaar_smul_rpow_inv_finrank`, `ConvexGeom.addHaar_halfBall`,
  `ConvexGeom.addHaar_le_half_closedBall_of_zero_not_mem_interior`: volume-root scaling and the
  half-ball origin-in-interior criterion.
* `ConvexGeom.continuous_addHaar_convexBody`, `ConvexGeom.continuous_addHaarReal_convexBody`:
  Hausdorff continuity of volume on `ConvexBody E`.
* `ConvexGeom.continuous_addHaar_convexHull_range`,
  `ConvexGeom.exists_max_addHaar_convexHull_of_isCompact`,
  `ConvexGeom.iSup_addHaar_convexHull_closedBall_eq_sphere`,
  `ConvexGeom.iSup_addHaar_convexHull_sphere_eq_generalPosition`: polytope volume continuity,
  attainment, sphere reduction, and general-position density.
* `ConvexGeom.continuous_symmDiffVolReal_convexBody` ,
  `ConvexGeom.continuous_symmDiffVol_convexBody` :
  joint continuity of symmetric-difference volume in the Hausdorff metric.

## References

* [R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*][schneider2014], §1.8.
-/

open MeasureTheory Set Filter
open scoped RealInnerProductSpace Pointwise Topology ENNReal

namespace ConvexGeom

public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### 1. Volume-Root Scaling and Half-Ball Volume Identities -/

/-- **Volume-root homogeneity (`ℝ≥0∞` form):**
for any additive Haar measure `μ` in dimension `d = finrank ℝ E ≥ 1`, any `c ≥ 0`, and any set
`A ⊆ E`, `μ (c • A) ^ (1 / d) = ENNReal.ofReal c * μ A ^ (1 / d)`. -/
theorem addHaar_smul_rpow_inv_finrank [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {c : ℝ} (hc : 0 ≤ c) (A : Set E) :
    μ (c • A) ^ (1 / (Module.finrank ℝ E : ℝ)) =
      ENNReal.ofReal c * μ A ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  set d := Module.finrank ℝ E
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr Module.finrank_pos
  have hinv_pos : (0 : ℝ) < 1 / (d : ℝ) := one_div_pos.mpr hd_pos
  rcases hc.eq_or_lt with rfl | hc_pos
  · have hsub : (0 : ℝ) • A ⊆ ({0} : Set E) := by
      rintro _ ⟨x, _, rfl⟩; simp
    have hzero : μ ((0 : ℝ) • A) = 0 := measure_mono_null hsub (measure_singleton 0)
    rw [hzero, ENNReal.zero_rpow_of_pos hinv_pos, ENNReal.ofReal_zero, zero_mul]
  · rw [Measure.addHaar_smul, abs_of_nonneg (pow_nonneg hc _),
      ENNReal.mul_rpow_of_nonneg _ _ hinv_pos.le,
      ENNReal.ofReal_rpow_of_pos (pow_pos hc_pos d), ← Real.rpow_natCast,
      ← Real.rpow_mul hc, mul_one_div_cancel hd_pos.ne', Real.rpow_one]

/-- **Volume-root homogeneity (`ℝ` form):**
`(μ.real (c • A)) ^ (1 / d) = c * (μ.real A) ^ (1 / d)` for `c ≥ 0` in dimension `d ≥ 1`. -/
theorem addHaar_real_smul_rpow_inv_finrank [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {c : ℝ} (hc : 0 ≤ c) (A : Set E) :
    (μ.real (c • A)) ^ (1 / (Module.finrank ℝ E : ℝ)) =
      c * (μ.real A) ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  have h := congrArg ENNReal.toReal (addHaar_smul_rpow_inv_finrank μ hc A)
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc,
    ← ENNReal.toReal_rpow] at h
  exact h

/-- The hyperplane `{x | ⟪x, u⟫ = 0}` for `u ≠ 0` has Haar measure `0`. -/
lemma addHaar_hyperplane_eq_zero (μ : Measure E) [μ.IsAddHaarMeasure] {u : E} (hu : u ≠ 0) :
    μ {x : E | ⟪x, u⟫ = 0} = 0 := by
  let H : Submodule ℝ E :=
    { carrier := {x | ⟪x, u⟫ = 0}
      add_mem' := fun {a b} ha hb => by
        change ⟪a, u⟫ = 0 at ha; change ⟪b, u⟫ = 0 at hb
        change ⟪a + b, u⟫ = 0; rw [inner_add_left, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c {a} ha => by
        change ⟪a, u⟫ = 0 at ha
        change ⟪c • a, u⟫ = 0; rw [inner_smul_left, RCLike.conj_to_real, ha, mul_zero] }
  have hH_ne : H ≠ ⊤ := by
    intro htop
    have huH : u ∈ H := by rw [htop]; trivial
    have h0 : ⟪u, u⟫ = 0 := huH
    exact hu (inner_self_eq_zero.mp h0)
  exact Measure.addHaar_submodule μ H hH_ne

/-- **Half-ball volume identity:** for any `u ≠ 0` and any `r : ℝ`,
`μ (closedBall 0 r ∩ {x | 0 ≤ ⟪x, u⟫}) = μ (closedBall 0 r) / 2`. -/
theorem addHaar_halfBall (μ : Measure E) [μ.IsAddHaarMeasure] {u : E} (hu : u ≠ 0) (r : ℝ) :
    μ (Metric.closedBall (0 : E) r ∩ {x : E | 0 ≤ ⟪x, u⟫}) =
      μ (Metric.closedBall (0 : E) r) / 2 := by
  let B := Metric.closedBall (0 : E) r
  let P := B ∩ {x : E | 0 ≤ ⟪x, u⟫}
  let Q := B ∩ {x : E | ⟪x, u⟫ ≤ 0}
  have hP_meas : MeasurableSet P :=
    measurableSet_closedBall.inter
      (isClosed_le continuous_const (continuous_id.inner continuous_const)).measurableSet
  have hQ_meas : MeasurableSet Q :=
    measurableSet_closedBall.inter
      (isClosed_le (continuous_id.inner continuous_const) continuous_const).measurableSet
  have hunion : P ∪ Q = B := by
    ext x
    simp only [P, Q, mem_union, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      rcases le_total 0 ⟪x, u⟫ with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  have hinter : μ (P ∩ Q) = 0 := by
    refine measure_mono_null ?_ (addHaar_hyperplane_eq_zero μ hu)
    intro x ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
    exact le_antisymm h2 h1
  have hQ_eq : Q = (-1 : ℝ) • P := by
    ext x
    simp only [P, Q, B, Set.mem_smul_set, mem_inter_iff, Metric.mem_closedBall, dist_zero_right,
      mem_ofPred_eq]
    constructor
    · intro ⟨hxB, hxu⟩
      refine ⟨-x, ⟨by simpa using hxB, by simpa [inner_neg_left] using hxu⟩, by simp⟩
    · rintro ⟨y, ⟨hyB, hyu⟩, rfl⟩
      exact ⟨by simpa using hyB, by simpa [inner_neg_left] using hyu⟩
  have hmeas_eq : μ Q = μ P := by
    rw [hQ_eq, Measure.addHaar_smul]
    simp
  have hsum : μ P + μ Q = μ B := by
    have h := measure_union_add_inter P hQ_meas (μ := μ)
    rw [hunion, hinter, add_zero] at h
    exact h.symm
  rw [hmeas_eq, ← two_mul] at hsum
  have h2ne : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  rw [← hsum, div_eq_mul_inv, mul_comm (2 : ℝ≥0∞) (μ P), mul_assoc,
    ENNReal.mul_inv_cancel h2ne h2top, mul_one]

/-- Any set contained in a closed half-space inside `closedBall 0 r` has measure at most
half the ball's measure. -/
theorem addHaar_le_half_ball (μ : Measure E) [μ.IsAddHaarMeasure] {S : Set E} {u : E} (hu : u ≠ 0)
    {r : ℝ} (hSball : S ⊆ Metric.closedBall (0 : E) r) (hShalf : ∀ x ∈ S, 0 ≤ ⟪x, u⟫) :
    μ S ≤ μ (Metric.closedBall (0 : E) r) / 2 := by
  rw [← addHaar_halfBall μ hu r]
  exact measure_mono fun x hx => ⟨hSball hx, hShalf x hx⟩

/-- **Half-ball origin-in-interior criterion (general dimension):**
if a convex set `K ⊆ closedBall 0 r` does not contain `0` in its interior, then
`μ K ≤ μ (closedBall 0 r) / 2`. Equivalently, any convex subset of `closedBall 0 r` with
volume strictly exceeding half the ball must contain `0` in its interior. -/
theorem addHaar_le_half_closedBall_of_zero_not_mem_interior (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hKconv : Convex ℝ K) {r : ℝ} (hKball : K ⊆ Metric.closedBall (0 : E) r)
    (h0 : (0 : E) ∉ interior K) :
    μ K ≤ μ (Metric.closedBall (0 : E) r) / 2 := by
  by_cases hint : (interior K).Nonempty
  · obtain ⟨f, hf⟩ := geometric_hahn_banach_point_open hKconv.interior isOpen_interior h0
    let u : E := (InnerProductSpace.toDual ℝ E).symm f
    have hf_eq : ∀ x : E, f x = ⟪u, x⟫ := fun x => by
      simp [u, InnerProductSpace.toDual_symm_apply]
    have hu_ne : u ≠ 0 := by
      intro hu0
      obtain ⟨b, hb⟩ := hint
      have hlt := hf b hb
      rw [hf_eq 0, hf_eq b, hu0, inner_zero_left, inner_zero_left] at hlt
      exact lt_irrefl 0 hlt
    have h_int : ∀ x ∈ interior K, 0 ≤ ⟪x, u⟫ := by
      intro x hx
      have hlt := hf x hx
      rw [hf_eq 0, hf_eq x, inner_zero_right, real_inner_comm] at hlt
      exact hlt.le
    have hK_sub : K ⊆ closure (interior K) :=
      subset_closure.trans_eq (hKconv.closure_interior_eq_closure_of_nonempty_interior hint).symm
    have h_half : ∀ x ∈ K, 0 ≤ ⟪x, u⟫ := by
      intro x hx
      have hclosed : IsClosed {y : E | 0 ≤ ⟪y, u⟫} :=
        isClosed_le continuous_const (continuous_id.inner continuous_const)
      exact hclosed.closure_subset_iff.mpr h_int (hK_sub hx)
    exact addHaar_le_half_ball μ hu_ne hKball h_half
  · rw [Set.not_nonempty_iff_eq_empty] at hint
    have hKsub : K ⊆ frontier K := by
      rw [frontier, hint, sdiff_empty]
      exact subset_closure
    have hK0 : μ K = 0 := measure_mono_null hKsub (hKconv.addHaar_frontier μ)
    rw [hK0]
    exact zero_le

/-! ### 2. Continuity of Volume on `ConvexBody E` -/

/-- Upper semicontinuity of Haar measure on `ConvexBody E`:
if `K_n → K` in the Hausdorff metric, then `lim sup μ(K_n) ≤ μ(K)`. -/
theorem upperSemicontinuous_addHaar_convexBody (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : ConvexBody E) :
    ∀ ε : ℝ≥0∞, μ (K : Set E) < ε →
      ∀ᶠ L : ConvexBody E in 𝓝 K, μ (L : Set E) < ε := by
  intro ε hε
  -- For `r_n = 1 / (n + 1)`, the compact sets `K + closedBall 0 r_n` decrease to `K`.
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr_pos : ∀ n, 0 < r n := fun n => by positivity
  let S : ℕ → Set E := fun n => (K : Set E) + Metric.closedBall (0 : E) (r n)
  have hS_anti : Antitone S := by
    intro m n hmn x hx
    rcases Set.mem_add.mp hx with ⟨y, hy, z, hz, rfl⟩
    refine Set.add_mem_add hy ?_
    have hrmn : r n ≤ r m := by
      dsimp only [r]
      gcongr
    exact Metric.closedBall_subset_closedBall hrmn hz
  have hS_compact : ∀ n, IsCompact (S n) := fun n =>
    K.isCompact.add (isCompact_closedBall (0 : E) (r n))
  have hS_meas : ∀ n, NullMeasurableSet (S n) μ := fun n =>
    (hS_compact n).isClosed.measurableSet.nullMeasurableSet
  have hS_fin : ∃ n, μ (S n) ≠ ∞ :=
    ⟨0, (hS_compact 0).measure_lt_top.ne⟩
  have hInter : (⋂ n : ℕ, S n) = (K : Set E) := by
    ext x
    simp only [mem_iInter]
    constructor
    · intro hx
      -- For every `n`, `infDist x K ≤ r n`, so `infDist x K = 0` and `x ∈ K` (closed).
      have hdist : ∀ n, ∃ y ∈ K, dist x y ≤ r n := fun n => by
        rcases Set.mem_add.mp (hx n) with ⟨y, hy, z, hz, hxyz⟩
        refine ⟨y, hy, ?_⟩
        rw [← hxyz, dist_eq_norm, add_sub_cancel_left]
        simpa [Metric.mem_closedBall, dist_zero_right] using hz
      choose yn hyn hdist_yn using hdist
      have htend : Tendsto yn atTop (𝓝 x) := by
        rw [Metric.tendsto_atTop]
        intro δ hδ
        obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
        refine ⟨N, fun n hn => ?_⟩
        rw [dist_comm]
        have hrle : r n ≤ 1 / ((N : ℝ) + 1) := by
          dsimp only [r]; gcongr
        exact (hdist_yn n).trans_lt (hrle.trans_lt hN)
      exact K.isClosed.mem_of_tendsto htend (Eventually.of_forall hyn)
    · intro hx n
      refine ⟨x, hx, 0, Metric.mem_closedBall_self (hr_pos n).le, add_zero x⟩
  have htend_meas : Tendsto (fun n => μ (S n)) atTop (𝓝 (μ (K : Set E))) := by
    rw [← hInter]
    exact tendsto_measure_iInter_atTop hS_meas hS_anti hS_fin
  have hev : ∀ᶠ n in atTop, μ (S n) < ε := htend_meas.eventually (gt_mem_nhds hε)
  obtain ⟨N, hN⟩ := hev.exists
  rw [Metric.eventually_nhds_iff]
  refine ⟨r N, hr_pos N, fun L hLK => ?_⟩
  have hLsub : (L : Set E) ⊆ S N := by
    intro x hxL
    obtain ⟨y, hyK, hinf⟩ := K.isCompact.exists_infDist_eq_dist K.nonempty x
    have hxy : dist x y ≤ r N := by
      rw [← hinf]
      have h1 : Metric.infDist x (K : Set E) ≤ dist L K := by
        rw [← ConvexBody.hausdorffDist_coe]
        exact Metric.infDist_le_hausdorffDist_of_mem hxL ConvexBody.hausdorffEDist_ne_top
      exact h1.trans hLK.le
    refine ⟨y, hyK, x - y, ?_, by abel_nf⟩
    simpa [Metric.mem_closedBall, dist_zero_right, dist_eq_norm] using hxy
  exact (measure_mono hLsub).trans_lt hN

omit [MeasurableSpace E] [BorelSpace E] in
/-- Key geometric inclusion via support functions: if `closedBall x₀ r ⊆ K` (`r > 0`) and
`dist L K ≤ (1 - t) * r` for `0 < t < 1` , then the contracted copy `x₀ + t • (K - x₀)` lies in `L`
. -/
lemma homothety_subset_of_dist_le {K L : ConvexBody E} {x₀ : E} {r t : ℝ}
    (hr : 0 < r) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hball : Metric.closedBall x₀ r ⊆ K)
    (hdist : dist L K ≤ (1 - t) * r) :
    (((1 - t) • bodySingleton x₀ + t • K : ConvexBody E) : Set E) ⊆ (L : Set E) := by
  refine supportFn_le_iff_subset.mp fun u => ?_
  rw [supportFn_minkowski_add, supportFn_body_smul _ (sub_nonneg.mpr ht1),
    supportFn_bodySingleton, supportFn_body_smul _ ht0]
  have hball_sup : ⟪x₀, u⟫ + r * ‖u‖ ≤ supportFn K u := by
    have hsub : (bodyClosedBall x₀ hr.le : Set E) ⊆ K := by simpa [coe_bodyClosedBall] using hball
    have := supportFn_mono (K := bodyClosedBall x₀ hr.le) (L := K) hsub u
    rwa [supportFn_bodyClosedBall] at this
  have hKL_sup : supportFn K u - supportFn L u ≤ (1 - t) * r * ‖u‖ := by
    by_cases hu : u = 0
    · subst hu; simp
    · have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
      have hunit : ‖‖u‖⁻¹ • u‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hpos.le),
          inv_mul_cancel₀ hpos.ne']
      have h0 := (dist_le_iff_supportFn_sub_le (mul_nonneg (sub_nonneg.mpr ht1) hr.le)).mp
        hdist (‖u‖⁻¹ • u) hunit
      rw [supportFn_smul L (inv_nonneg.mpr hpos.le),
        supportFn_smul K (inv_nonneg.mpr hpos.le), ← mul_sub, abs_mul,
        abs_of_nonneg (inv_nonneg.mpr hpos.le)] at h0
      have hmul := mul_le_mul_of_nonneg_left h0 hpos.le
      rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at hmul
      have hneg := (neg_le_abs _).trans hmul
      linarith
  nlinarith

/-- Lower semicontinuity of Haar measure on `ConvexBody E`:
if `c < μ(K)`, then for all `L` sufficiently close to `K` in Hausdorff distance, `c < μ(L)`. -/
theorem lowerSemicontinuous_addHaar_convexBody (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : ConvexBody E) :
    ∀ c : ℝ≥0∞, c < μ (K : Set E) →
      ∀ᶠ L : ConvexBody E in 𝓝 K, c < μ (L : Set E) := by
  intro c hc
  have hint_ne : (interior (K : Set E)).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hKsub : (K : Set E) ⊆ frontier (K : Set E) := by
      rw [frontier, K.isClosed.closure_eq, hemp, sdiff_empty]
    have hK0 : μ (K : Set E) = 0 := measure_mono_null hKsub (K.convex.addHaar_frontier μ)
    rw [hK0] at hc
    exact not_lt_zero hc
  obtain ⟨x₀, hx₀⟩ := hint_ne
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx₀)
  have hcb : Metric.closedBall x₀ (r / 2) ⊆ K :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  set d := Module.finrank ℝ E
  have hK_fin : μ (K : Set E) ≠ ∞ := K.isCompact.measure_lt_top.ne
  have htend : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ d) * μ (K : Set E)) (𝓝 1)
      (𝓝 (μ (K : Set E))) := by
    have h1 : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ d)) (𝓝 1) (𝓝 1) := by
      have hpow : Tendsto (fun t : ℝ => t ^ d) (𝓝 1) (𝓝 (1 : ℝ)) := by
        simpa using (continuous_pow d).tendsto (1 : ℝ)
      have hcomp := (ENNReal.continuous_ofReal.tendsto 1).comp hpow
      simpa [Function.comp_def] using hcomp
    simpa [one_mul] using (ENNReal.Tendsto.mul_const h1 (Or.inr hK_fin))
  have hev_t : ∀ᶠ t : ℝ in 𝓝[<] 1, c < ENNReal.ofReal (t ^ d) * μ (K : Set E) ∧ 0 < t := by
    have h1 : ∀ᶠ t : ℝ in 𝓝[<] 1, c < ENNReal.ofReal (t ^ d) * μ (K : Set E) :=
      nhdsWithin_le_nhds (htend.eventually (lt_mem_nhds hc))
    have h2 : ∀ᶠ t : ℝ in 𝓝[<] 1, (0 : ℝ) < t :=
      nhdsWithin_le_nhds (lt_mem_nhds zero_lt_one)
    exact h1.and h2
  obtain ⟨t, ⟨ht_meas, ht_pos⟩, ht_lt1⟩ := (hev_t.and self_mem_nhdsWithin).exists
  have hδ_pos : 0 < (1 - t) * (r / 2) := mul_pos (sub_pos.mpr ht_lt1) (by linarith)
  rw [Metric.eventually_nhds_iff]
  refine ⟨(1 - t) * (r / 2), hδ_pos, fun L hLK => ?_⟩
  have hsub := homothety_subset_of_dist_le (by linarith) ht_pos.le ht_lt1.le hcb hLK.le
  have hvol_hom :
      μ (((1 - t) • bodySingleton x₀ + t • K : ConvexBody E) : Set E) =
        ENNReal.ofReal (t ^ d) * μ (K : Set E) := by
    have hset : (((1 - t) • bodySingleton x₀ + t • K : ConvexBody E) : Set E) =
        (fun x => -((1 - t) • x₀) + x) ⁻¹' (t • (K : Set E)) := by
      ext x
      rw [ConvexBody.coe_add, ConvexBody.coe_smul, ConvexBody.coe_smul, coe_bodySingleton]
      simp only [Set.mem_add, Set.mem_smul_set, Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro ⟨_, ⟨_, rfl, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨y, hy, by abel⟩
      · rintro ⟨y, hy, hxy⟩
        refine ⟨(1 - t) • x₀, ⟨x₀, rfl, rfl⟩, t • y, ⟨y, hy, rfl⟩, ?_⟩
        calc
          (1 - t) • x₀ + t • y = (1 - t) • x₀ + (-((1 - t) • x₀) + x) := by rw [← hxy]
          _ = x := by abel
    rw [hset, measure_preimage_add, Measure.addHaar_smul, abs_of_nonneg (pow_nonneg ht_pos.le _)]
  calc
    c < ENNReal.ofReal (t ^ d) * μ (K : Set E) := ht_meas
    _ = μ (((1 - t) • bodySingleton x₀ + t • K : ConvexBody E) : Set E) := hvol_hom.symm
    _ ≤ μ (L : Set E) := measure_mono hsub

/-- **Continuity of Volume on `ConvexBody E`:**
In a finite-dimensional real inner product space, every additive Haar measure (in particular
Lebesgue `volume`) is continuous on `ConvexBody E` with respect to the Hausdorff metric. -/
theorem continuous_addHaar_convexBody (μ : Measure E) [μ.IsAddHaarMeasure] :
    Continuous (fun K : ConvexBody E => μ (K : Set E)) := by
  rw [continuous_iff_continuousAt]
  intro K
  rw [ContinuousAt, tendsto_order]
  exact ⟨lowerSemicontinuous_addHaar_convexBody μ K, upperSemicontinuous_addHaar_convexBody μ K⟩

/-- Real-valued continuity of `K ↦ μ.real (K : Set E)` on `ConvexBody E`. -/
theorem continuous_addHaarReal_convexBody (μ : Measure E) [μ.IsAddHaarMeasure] :
    Continuous (fun K : ConvexBody E => μ.real (K : Set E)) := by
  rw [continuous_iff_continuousAt]
  intro K
  have hfin : μ (K : Set E) ≠ ∞ := K.isCompact.measure_lt_top.ne
  exact (ENNReal.continuousAt_toReal hfin).comp
    (f := fun M : ConvexBody E => μ (M : Set E))
    (continuous_addHaar_convexBody μ).continuousAt

/-- **Continuity of Finite Convex-Hull Volume:**
For any nonempty finite index type `ι`, the map `v ↦ μ (convexHull ℝ (Set.range v))` is
continuous on `ι → E`. -/
theorem continuous_addHaar_convexHull_range (μ : Measure E) [μ.IsAddHaarMeasure]
    {ι : Type*} [Finite ι] [Nonempty ι] :
    Continuous (fun v : ι → E => μ (convexHull ℝ (Set.range v))) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  let hullBody : (ι → E) → ConvexBody E := fun v =>
    bodyConvexHull (Finset.univ.image v) (Finset.univ_nonempty.image v)
  have hcoe : ∀ v, (hullBody v : Set E) = convexHull ℝ (Set.range v) := fun v => by
    simp [hullBody, Finset.coe_image]
  have hlip : LipschitzWith 1 hullBody := by
    refine LipschitzWith.of_dist_le_mul fun v w => ?_
    rw [NNReal.coe_one, one_mul, ← ConvexBody.hausdorffDist_coe, hcoe v, hcoe w]
    exact hausdorffDist_convexHull_range_le v w dist_nonneg fun i => dist_le_pi_dist v w i
  have heq : (fun v : ι → E => μ (convexHull ℝ (Set.range v))) =
      (fun K : ConvexBody E => μ (K : Set E)) ∘ hullBody := by
    ext v; simp [hcoe]
  rw [heq]
  exact (continuous_addHaar_convexBody μ).comp hlip.continuous

/-- Real-valued continuity of finite convex-hull volume:
`v ↦ μ.real (convexHull ℝ (Set.range v))` is continuous on `ι → E`. -/
theorem continuous_addHaarReal_convexHull_range (μ : Measure E) [μ.IsAddHaarMeasure]
    {ι : Type*} [Finite ι] [Nonempty ι] :
    Continuous (fun v : ι → E => μ.real (convexHull ℝ (Set.range v))) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  rw [continuous_iff_continuousAt]
  intro v
  have hc : IsCompact (convexHull ℝ (Set.range v)) := by
    have hcoe : (bodyConvexHull (Finset.univ.image v) (Finset.univ_nonempty.image v) : Set E) =
        convexHull ℝ (Set.range v) := by simp [Finset.coe_image]
    rw [← hcoe]
    exact (bodyConvexHull _ _).isCompact
  exact (ENNReal.continuousAt_toReal hc.measure_lt_top.ne).comp
    (f := fun w : ι → E => μ (convexHull ℝ (Set.range w)))
    (continuous_addHaar_convexHull_range μ).continuousAt

/-- **Existence of a maximal-volume polytope over any compact nonempty vertex domain (`ℝ≥0∞`):**
for any compact nonempty `S ⊆ E` and nonempty finite index type `ι`, there exists `v : ι → E`
with vertices in `S` maximizing `μ (convexHull ℝ (Set.range v))`. -/
theorem exists_max_addHaar_convexHull_of_isCompact (μ : Measure E) [μ.IsAddHaarMeasure]
    {ι : Type*} [Finite ι] [Nonempty ι] {S : Set E} (hSc : IsCompact S) (hSne : S.Nonempty) :
    ∃ v : ι → E, (∀ i, v i ∈ S) ∧
      ∀ w : ι → E, (∀ i, w i ∈ S) →
        μ (convexHull ℝ (Set.range w)) ≤ μ (convexHull ℝ (Set.range v)) := by
  let D : Set (ι → E) := Set.univ.pi (fun _ => S)
  have hDc : IsCompact D := isCompact_univ_pi fun _ => hSc
  obtain ⟨x₀, hx₀⟩ := hSne
  have hDne : D.Nonempty := ⟨fun _ => x₀, fun _ _ => hx₀⟩
  obtain ⟨v, hv_mem, hv_max⟩ :=
    hDc.exists_isMaxOn hDne (continuous_addHaar_convexHull_range μ).continuousOn
  exact ⟨v, fun i => hv_mem i (Set.mem_univ i), fun w hw => hv_max (fun i _ => hw i)⟩

/-- Real-valued version of `exists_max_addHaar_convexHull_of_isCompact`. -/
theorem exists_max_addHaarReal_convexHull_of_isCompact (μ : Measure E) [μ.IsAddHaarMeasure]
    {ι : Type*} [Finite ι] [Nonempty ι] {S : Set E} (hSc : IsCompact S) (hSne : S.Nonempty) :
    ∃ v : ι → E, (∀ i, v i ∈ S) ∧
      ∀ w : ι → E, (∀ i, w i ∈ S) →
        μ.real (convexHull ℝ (Set.range w)) ≤ μ.real (convexHull ℝ (Set.range v)) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨v, hv_mem, hv_max⟩ := exists_max_addHaar_convexHull_of_isCompact μ (ι := ι) hSc hSne
  have hc : IsCompact (convexHull ℝ (Set.range v)) := by
    have hcoe : (bodyConvexHull (Finset.univ.image v) (Finset.univ_nonempty.image v) : Set E) =
        convexHull ℝ (Set.range v) := by simp [Finset.coe_image]
    rw [← hcoe]
    exact (bodyConvexHull _ _).isCompact
  exact ⟨v, hv_mem, fun w hw => ENNReal.toReal_mono hc.measure_lt_top.ne (hv_max w hw)⟩

/-- Existence of a maximal-volume polytope with vertices on `Metric.sphere 0 r` (`r ≥ 0`)
in any nontrivial finite-dimensional real inner product space. -/
theorem exists_max_addHaar_convexHull_sphere [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {ι : Type*} [Finite ι] [Nonempty ι] {r : ℝ} (hr : 0 ≤ r) :
    ∃ v : ι → E, (∀ i, v i ∈ Metric.sphere (0 : E) r) ∧
      ∀ w : ι → E, (∀ i, w i ∈ Metric.sphere (0 : E) r) →
        μ (convexHull ℝ (Set.range w)) ≤ μ (convexHull ℝ (Set.range v)) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have hne : (Metric.sphere (0 : E) r).Nonempty := by
    refine ⟨r • (‖x‖⁻¹ • x), ?_⟩
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hr, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx), mul_one]
  exact exists_max_addHaar_convexHull_of_isCompact μ (isCompact_sphere (0 : E) r) hne

/-- Existence of a maximal-volume polytope with vertices in `Metric.closedBall 0 r` (`r ≥ 0`). -/
theorem exists_max_addHaar_convexHull_closedBall (μ : Measure E) [μ.IsAddHaarMeasure]
    {ι : Type*} [Finite ι] [Nonempty ι] {r : ℝ} (hr : 0 ≤ r) :
    ∃ v : ι → E, (∀ i, v i ∈ Metric.closedBall (0 : E) r) ∧
      ∀ w : ι → E, (∀ i, w i ∈ Metric.closedBall (0 : E) r) →
        μ (convexHull ℝ (Set.range w)) ≤ μ (convexHull ℝ (Set.range v)) :=
  exists_max_addHaar_convexHull_of_isCompact μ (isCompact_closedBall (0 : E) r)
    ⟨0, Metric.mem_closedBall_self hr⟩

/-- **Half-ball origin criterion:** if a convex set `K ⊆ closedBall 0 r` has volume strictly
greater than half the volume of `closedBall 0 r`, then `0 ∈ interior K`. -/
theorem zero_mem_interior_of_addHaar_gt_half_closedBall (μ : Measure E) [μ.IsAddHaarMeasure]
    {r : ℝ} {K : Set E} (hKconv : Convex ℝ K)
    (hKsub : K ⊆ Metric.closedBall (0 : E) r)
    (hgt : μ (Metric.closedBall (0 : E) r) / 2 < μ K) :
    (0 : E) ∈ interior K := by
  by_contra h0
  exact hgt.not_ge (addHaar_le_half_closedBall_of_zero_not_mem_interior μ hKconv hKsub h0)

omit [FiniteDimensional ℝ E] in
/-- Adding an exterior point `w ∉ P` to a compact set `P` with nonempty interior strictly
increases its additive Haar measure. -/
theorem strict_addHaar_convexHull_insert_of_notMem (μ : Measure E) [μ.IsAddHaarMeasure]
    {P : Set E} (hPc : IsCompact P) (hPint : (interior P).Nonempty)
    {w : E} (hw : w ∉ P) :
    μ P < μ (convexHull ℝ (insert w P)) := by
  obtain ⟨x₀, hx₀⟩ := hPint
  obtain ⟨ε, hε, hball_sub⟩ := Metric.isOpen_iff.mp isOpen_interior x₀ hx₀
  have hball_P : Metric.ball x₀ ε ⊆ P := hball_sub.trans interior_subset
  have hPclosed : IsClosed P := hPc.isClosed
  obtain ⟨δ, hδ, hdisj_ball⟩ := Metric.isOpen_iff.mp hPclosed.isOpen_compl w hw
  set M : ℝ := ‖x₀ - w‖ + ε + 1
  have hM_pos : 0 < M := by positivity
  set t : ℝ := min (1 / 2) (δ / (2 * M))
  have ht_pos : 0 < t := lt_min (by norm_num) (by positivity)
  have ht_lt_one : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  let c : E := (1 - t) • w + t • x₀
  let U : Set E := Metric.ball c (t * ε)
  have hU_sub : U ⊆ convexHull ℝ (insert w P) := by
    intro z hz
    have hnorm_z : ‖z - c‖ < t * ε := by simpa [U, Metric.mem_ball, dist_eq_norm] using hz
    let y : E := x₀ + t⁻¹ • (z - c)
    have hy_ball : y ∈ Metric.ball x₀ ε := by
      rw [Metric.mem_ball, dist_eq_norm, show y - x₀ = t⁻¹ • (z - c) by simp [y],
        norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht_pos)]
      calc
        t⁻¹ * ‖z - c‖ < t⁻¹ * (t * ε) :=
          mul_lt_mul_of_pos_left hnorm_z (inv_pos.mpr ht_pos)
        _ = ε := by rw [← mul_assoc, inv_mul_cancel₀ ht_pos.ne', one_mul]
    have hz_comb : (1 - t) • w + t • y = z := by
      dsimp only [y, c]
      rw [smul_add, smul_smul, mul_inv_cancel₀ ht_pos.ne', one_smul]
      abel
    rw [← hz_comb]
    exact (convex_convexHull ℝ _)
      (subset_convexHull ℝ _ (Set.mem_insert w P))
      (subset_convexHull ℝ _ (Set.mem_insert_of_mem w (hball_P hy_ball)))
      (sub_nonneg.mpr ht_lt_one.le) ht_pos.le (by ring)
  have hU_disj : Disjoint P U := by
    rw [Set.disjoint_left]
    intro z hzP hzU
    have hz_w : z ∈ Metric.ball w δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : ‖z - c‖ < t * ε := by simpa [U, Metric.mem_ball, dist_eq_norm] using hzU
      have h2 : c - w = t • (x₀ - w) := by
        dsimp only [c]; rw [sub_smul, one_smul, smul_sub]; abel
      have h3 : ‖z - w‖ ≤ ‖z - c‖ + ‖c - w‖ := by
        have := norm_add_le (z - c) (c - w)
        simpa [sub_add_sub_cancel] using this
      have h4 : ‖c - w‖ = t * ‖x₀ - w‖ := by
        rw [h2, norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
      have ht_le : t ≤ δ / (2 * M) := min_le_right _ _
      have h5 : t * M ≤ δ / 2 := by
        calc
          t * M ≤ (δ / (2 * M)) * M := mul_le_mul_of_nonneg_right ht_le hM_pos.le
          _ = δ / 2 := by field_simp [hM_pos.ne']
      have h6 : t * ε + t * ‖x₀ - w‖ < t * M := by
        dsimp only [M]; nlinarith
      linarith
    exact hdisj_ball hz_w hzP
  have hP_sub : P ⊆ convexHull ℝ (insert w P) :=
    (Set.subset_insert w P).trans (subset_convexHull ℝ _)
  have hU_pos : 0 < μ U :=
    Metric.isOpen_ball.measure_pos μ ⟨c, Metric.mem_ball_self (by positivity)⟩
  have hunion : μ P + μ U ≤ μ (convexHull ℝ (insert w P)) := by
    rw [← measure_union hU_disj measurableSet_ball]
    exact measure_mono (Set.union_subset hP_sub hU_sub)
  have hP_lt_top : μ P < ⊤ := hPc.measure_lt_top
  exact lt_of_lt_of_le (ENNReal.lt_add_right hP_lt_top.ne hU_pos.ne') hunion

/-- Pushing vertices from `closedBall 0 r` onto `sphere 0 r` preserves the supremum of polytope
volume for any finite vertex budget in a nontrivial space. -/
theorem iSup_addHaar_convexHull_closedBall_eq_sphere [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {ι : Type*} [Finite ι] [Nonempty ι]
    (r : ℝ) :
    (⨆ (v : ι → E) (_ : ∀ i, v i ∈ Metric.closedBall (0 : E) r),
        μ (convexHull ℝ (Set.range v))) =
      ⨆ (v : ι → E) (_ : ∀ i, v i ∈ Metric.sphere (0 : E) r),
        μ (convexHull ℝ (Set.range v)) := by
  have : Fintype ι := Fintype.ofFinite ι
  apply le_antisymm
  · refine iSup₂_le fun v hv => ?_
    by_cases hcard : 2 ≤ Fintype.card ι
    · obtain ⟨w, hw_sph, hw_sub⟩ := exists_pushOut_range_sphere hcard v hv
      exact (measure_mono hw_sub).trans (le_iSup₂_of_le w hw_sph le_rfl)
    · -- `Fintype.card ι = 1`: every range is a singleton, so its convex hull has Haar measure `0`.
      have hsub : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp (by omega)
      have hrange : Set.range v = {v (Classical.arbitrary ι)} := by
        ext x; simp only [Set.mem_range, Set.mem_singleton_iff]
        exact ⟨fun ⟨i, hi⟩ => by
            rw [Subsingleton.elim i (Classical.arbitrary ι)] at hi
            exact hi.symm,
          fun h => ⟨Classical.arbitrary ι, h.symm⟩⟩
      rw [hrange, convexHull_singleton, measure_singleton]
      exact zero_le
  · refine iSup₂_le fun v hv => ?_
    exact le_iSup₂_of_le v (fun i => Metric.sphere_subset_closedBall (hv i)) le_rfl

omit [FiniteDimensional ℝ E] in
/-- Every extreme vertex of a full-dimensional maximal-volume polytope in `closedBall 0 r`
lies on the boundary sphere `sphere 0 r` (in any nontrivial space). -/
theorem mem_sphere_of_max_addHaar_convexHull_closedBall [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {ι : Type*} [Finite ι] {r : ℝ}
    {v : ι → E} (hv : ∀ i, v i ∈ Metric.closedBall (0 : E) r)
    (hmax : ∀ w : ι → E, (∀ j, w j ∈ Metric.closedBall (0 : E) r) →
      μ (convexHull ℝ (Set.range w)) ≤ μ (convexHull ℝ (Set.range v)))
    (hint : (interior (convexHull ℝ (Set.range v))).Nonempty)
    {i : ι} (hext : v i ∈ (convexHull ℝ (Set.range v)).extremePoints ℝ) :
    v i ∈ Metric.sphere (0 : E) r := by
  classical
  by_contra hnot_sph
  set P : Set E := convexHull ℝ (Set.range v)
  have hPc : IsCompact P := (Set.finite_range v).isCompact_convexHull ℝ
  -- Since `interior P` is nonempty and `E` is nontrivial, `P` is not a singleton, so some
  -- `v j ≠ v i` .
  have hdiff : ∃ j : ι, v j ≠ v i := by
    by_contra hall
    push Not at hall
    have hsub : Set.range v ⊆ {v i} := by
      rintro _ ⟨j, rfl⟩; exact Set.mem_singleton_iff.mpr (hall j)
    have hPsub : P ⊆ {v i} := convexHull_min hsub (convex_singleton (v i))
    obtain ⟨x, hx⟩ := hint
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
    have hball_sub : Metric.ball x ε ⊆ {v i} := hball.trans (interior_subset.trans hPsub)
    obtain ⟨y, hy⟩ := exists_ne (0 : E)
    let z : E := x + ((ε / 2) / ‖y‖) • y
    have hz_ball : z ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, dist_eq_norm, show z - x = ((ε / 2) / ‖y‖) • y by simp [z],
        norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hy)]
      linarith
    have hx_eq : x = v i := Set.mem_singleton_iff.mp (hball_sub (Metric.mem_ball_self hε))
    have hz_eq : z = v i := Set.mem_singleton_iff.mp (hball_sub hz_ball)
    have hz_ne_x : z ≠ x := by
      intro hzx
      have : ((ε / 2) / ‖y‖) • y = 0 := by
        have := congrArg (fun a => a - x) hzx
        simpa [z] using this
      rcases smul_eq_zero.mp this with h0 | hy0
      · exact (div_pos (half_pos hε) (norm_pos_iff.mpr hy)).ne' h0
      · exact hy hy0
    exact hz_ne_x (hz_eq.trans hx_eq.symm)
  obtain ⟨j, hj⟩ := hdiff
  obtain ⟨t, ht1, hqt⟩ := exists_ray_mem_sphere (hv i) hj.symm
  set q : E := v j + t • (v i - v j)
  have ht_gt : 1 < t := lt_of_le_of_ne ht1 fun h => by
    have hqv : q = v i := by
      dsimp only [q]; rw [← h, one_smul, add_sub_cancel]
    exact hnot_sph (hqv ▸ hqt)
  have ht_pos : 0 < t := by linarith
  have hvi_comb : (1 - t⁻¹) • v j + t⁻¹ • q = v i := by
    have ht_ne : t ≠ 0 := ht_pos.ne'
    calc
      (1 - t⁻¹) • v j + t⁻¹ • (v j + t • (v i - v j))
        = (1 - t⁻¹) • v j + t⁻¹ • v j + (t⁻¹ * t) • (v i - v j) := by
            rw [smul_add, smul_smul, add_assoc]
      _ = ((1 - t⁻¹) + t⁻¹) • v j + (1 : ℝ) • (v i - v j) := by
            rw [← add_smul, inv_mul_cancel₀ ht_ne]
      _ = v j + (v i - v j) := by simp
      _ = v i := add_sub_cancel _ _
  have hq_not_P : q ∉ P := by
    intro hqP
    have hopen : v i ∈ openSegment ℝ (v j) q :=
      ⟨1 - t⁻¹, t⁻¹, sub_pos.mpr (inv_lt_one_of_one_lt₀ ht_gt), inv_pos.mpr ht_pos,
        by ring, hvi_comb⟩
    have hvjP : v j ∈ P := subset_convexHull ℝ _ ⟨j, rfl⟩
    exact hj (hext.2 hvjP hqP hopen)
  let w : ι → E := Function.update v i q
  have hw_ball : ∀ k, w k ∈ Metric.closedBall (0 : E) r := fun k => by
    by_cases hk : k = i
    · rw [hk]; simpa [w] using Metric.sphere_subset_closedBall hqt
    · simp [w, hk, hv k]
  have hsub_w : convexHull ℝ (insert q P) ⊆ convexHull ℝ (Set.range w) := by
    refine convexHull_min ?_ (convex_convexHull ℝ _)
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hxP
    · exact subset_convexHull ℝ _ ⟨i, by simp [w]⟩
    · refine convexHull_min ?_ (convex_convexHull ℝ _) hxP
      rintro _ ⟨k, rfl⟩
      by_cases hk : k = i
      · rw [hk]
        have hj_ne : j ≠ i := fun h => hj (congrArg v h)
        have hvj_mem : v j ∈ Set.range w := ⟨j, by simp [w, hj_ne]⟩
        have hq_mem : q ∈ Set.range w := ⟨i, by simp [w]⟩
        rw [← hvi_comb]
        exact (convex_convexHull ℝ _)
          (subset_convexHull ℝ _ hvj_mem) (subset_convexHull ℝ _ hq_mem)
          (sub_nonneg.mpr (inv_le_one_of_one_le₀ ht1)) (inv_nonneg.mpr ht_pos.le) (by ring)
      · exact subset_convexHull ℝ _ ⟨k, by simp [w, hk]⟩
  have hlt : μ P < μ (convexHull ℝ (Set.range w)) :=
    (strict_addHaar_convexHull_insert_of_notMem μ hPc hint hq_not_P).trans_le
      (measure_mono hsub_w)
  exact hlt.not_ge (hmax w hw_ball)

/-- In dimension `≥ 2`, the supremum of polytope volume over `sphere 0 r` (`r > 0`) equals the
supremum restricted to configurations in `InSphericalGeneralPosition r`. -/
theorem iSup_addHaar_convexHull_sphere_eq_generalPosition
    (hd : 2 ≤ Module.finrank ℝ E) (μ : Measure E) [μ.IsAddHaarMeasure]
    {ι : Type*} [Finite ι] [Nonempty ι] {r : ℝ} (hr : 0 < r) :
    (⨆ (v : ι → E) (_ : ∀ i, v i ∈ Metric.sphere (0 : E) r),
        μ (convexHull ℝ (Set.range v))) =
      ⨆ (v : ι → E) (_ : InSphericalGeneralPosition r v),
        μ (convexHull ℝ (Set.range v)) := by
  apply le_antisymm
  · refine iSup₂_le fun v hv => ?_
    have hex : ∀ n : ℕ, ∃ w : ι → E, InSphericalGeneralPosition r w ∧
        ∀ i, dist (w i) (v i) < 1 / ((n : ℝ) + 1) := fun n =>
      exists_sphericalGeneralPosition_dist_lt_of_fintype hd hr v hv (by positivity)
    choose w hw_gp hw_dist using hex
    have htend : Tendsto w atTop (𝓝 v) := by
      rw [tendsto_pi_nhds]
      intro i
      rw [Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
      exact (hw_dist n i).trans (h1.trans_lt hN)
    have hvol_tend :
        Tendsto (fun n => μ (convexHull ℝ (Set.range (w n)))) atTop
          (𝓝 (μ (convexHull ℝ (Set.range v)))) :=
      (continuous_addHaar_convexHull_range μ).continuousAt.tendsto.comp htend
    exact le_of_tendsto' hvol_tend fun n => le_iSup₂_of_le (w n) (hw_gp n) le_rfl
  · refine iSup₂_le fun v hv => ?_
    exact le_iSup₂_of_le v hv.1 le_rfl

/-! ### 4. Symmetric-Difference Volume Metric -/

section SymmDiffBasic

variable {α : Type*} [MeasurableSpace α]

/-- The **symmetric-difference volume** (Nikodym pseudometric) in `ℝ≥0∞`:
`symmDiffVol μ A B := μ (symmDiff A B)`. -/
@[expose]
noncomputable def symmDiffVol (μ : Measure α) (A B : Set α) : ℝ≥0∞ :=
  μ (symmDiff A B)

/-- The real-valued **symmetric-difference volume**: `(μ (symmDiff A B)).toReal`. -/
@[expose]
noncomputable def symmDiffVolReal (μ : Measure α) (A B : Set α) : ℝ :=
  (symmDiffVol μ A B).toReal

@[simp]
lemma symmDiffVol_self (μ : Measure α) (A : Set α) :
    symmDiffVol μ A A = 0 := by
  simp [symmDiffVol]

lemma symmDiffVol_comm (μ : Measure α) (A B : Set α) :
    symmDiffVol μ A B = symmDiffVol μ B A := by
  rw [symmDiffVol, symmDiffVol, symmDiff_comm]

theorem symmDiffVol_triangle (μ : Measure α) (A B C : Set α) :
    symmDiffVol μ A C ≤ symmDiffVol μ A B + symmDiffVol μ B C := by
  unfold symmDiffVol
  have hsub : symmDiff A C ⊆ symmDiff A B ∪ symmDiff B C := by
    intro x hx
    simp only [Set.mem_symmDiff, mem_union] at hx ⊢
    by_cases hB : x ∈ B <;> tauto
  exact (measure_mono hsub).trans (measure_union_le _ _)

lemma symmDiffVol_of_subset (μ : Measure α) {A B : Set α} (hAB : A ⊆ B) :
    symmDiffVol μ A B = μ (B \ A) := by
  rw [symmDiffVol, symmDiff_of_le hAB]

lemma symmDiffVol_eq_add_sdiff (μ : Measure α) {A B : Set α}
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    symmDiffVol μ A B = μ (A \ B) + μ (B \ A) := by
  unfold symmDiffVol
  rw [Set.symmDiff_def]
  exact measure_union (Set.disjoint_left.mpr fun x h1 h2 => h1.2 h2.1) (hBm.diff hAm)

lemma symmDiffVol_le_add (μ : Measure α) (A B : Set α) :
    symmDiffVol μ A B ≤ μ A + μ B := by
  unfold symmDiffVol
  rw [Set.symmDiff_def]
  exact (measure_union_le _ _).trans (add_le_add (measure_mono Set.sdiff_subset)
    (measure_mono Set.sdiff_subset))

lemma symmDiffVol_ne_top (μ : Measure α) {A B : Set α} (hA : μ A ≠ ⊤) (hB : μ B ≠ ⊤) :
    symmDiffVol μ A B ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hA, hB⟩) (symmDiffVol_le_add μ A B)

lemma symmDiffVolReal_nonneg (μ : Measure α) (A B : Set α) :
    0 ≤ symmDiffVolReal μ A B :=
  ENNReal.toReal_nonneg

@[simp]
lemma symmDiffVolReal_self (μ : Measure α) (A : Set α) :
    symmDiffVolReal μ A A = 0 := by
  simp [symmDiffVolReal]

lemma symmDiffVolReal_comm (μ : Measure α) (A B : Set α) :
    symmDiffVolReal μ A B = symmDiffVolReal μ B A := by
  rw [symmDiffVolReal, symmDiffVolReal, symmDiffVol_comm]

theorem symmDiffVolReal_triangle (μ : Measure α) {A B C : Set α}
    (hAB : symmDiffVol μ A B ≠ ⊤) (hBC : symmDiffVol μ B C ≠ ⊤) :
    symmDiffVolReal μ A C ≤ symmDiffVolReal μ A B + symmDiffVolReal μ B C := by
  unfold symmDiffVolReal
  rw [← ENNReal.toReal_add hAB hBC]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hAB, hBC⟩) (symmDiffVol_triangle μ A B C)

/-- Volume difference is controlled by symmetric-difference volume:
`|μ.real A - μ.real B| ≤ symmDiffVolReal μ A B` for finite-measure sets `A, B`. -/
theorem abs_measureReal_sub_le_symmDiffVolReal (μ : Measure α) {A B : Set α}
    (hA : μ A ≠ ⊤) (hB : μ B ≠ ⊤) :
    |μ.real A - μ.real B| ≤ symmDiffVolReal μ A B := by
  have hAB : symmDiffVol μ A B ≠ ⊤ := symmDiffVol_ne_top μ hA hB
  have h1 : μ A ≤ μ B + symmDiffVol μ A B := by
    have hsub : A ⊆ B ∪ symmDiff A B := fun x hx => by
      by_cases hxB : x ∈ B
      · exact Or.inl hxB
      · exact Or.inr (Or.inl ⟨hx, hxB⟩)
    exact (measure_mono hsub).trans (measure_union_le _ _)
  have h2 : μ B ≤ μ A + symmDiffVol μ A B := by
    have hsub : B ⊆ A ∪ symmDiff A B := fun x hx => by
      by_cases hxA : x ∈ A
      · exact Or.inl hxA
      · exact Or.inr (Or.inr ⟨hx, hxA⟩)
    exact (measure_mono hsub).trans (measure_union_le _ _)
  have h1r := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hB, hAB⟩) h1
  have h2r := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hA, hAB⟩) h2
  rw [ENNReal.toReal_add hB hAB] at h1r
  rw [ENNReal.toReal_add hA hAB] at h2r
  rw [Measure.real, Measure.real, symmDiffVolReal, abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

end SymmDiffBasic

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Translation invariance of symmetric-difference volume. -/
theorem symmDiffVol_vadd (μ : Measure E) [μ.IsAddHaarMeasure] (x : E) (A B : Set E) :
    symmDiffVol μ (x +ᵥ A) (x +ᵥ B) = symmDiffVol μ A B := by
  unfold symmDiffVol
  have hpre : symmDiff (x +ᵥ A) (x +ᵥ B) = (fun y : E => -x + y) ⁻¹' symmDiff A B := by
    ext y
    simp only [Set.mem_symmDiff, Set.mem_vadd_set, mem_preimage, vadd_eq_add]
    have hiff : ∀ S : Set E, (∃ a ∈ S, x + a = y) ↔ -x + y ∈ S := fun S =>
      ⟨fun ⟨a, ha, h⟩ => by rwa [← h, neg_add_cancel_left],
        fun hy => ⟨-x + y, hy, add_neg_cancel_left x y⟩⟩
    rw [hiff A, hiff B]
  rw [hpre, measure_preimage_add]

/-- Scaling equivariance of symmetric-difference volume for `c ≠ 0`. -/
theorem symmDiffVol_smul (μ : Measure E) [μ.IsAddHaarMeasure] {c : ℝ} (hc : c ≠ 0) (A B : Set E) :
    symmDiffVol μ (c • A) (c • B) =
      ENNReal.ofReal (|c| ^ Module.finrank ℝ E) * symmDiffVol μ A B := by
  unfold symmDiffVol
  have heq : symmDiff (c • A) (c • B) = c • symmDiff A B := by
    ext y
    simp only [Set.mem_symmDiff, Set.mem_smul_set]
    have hiff : ∀ S : Set E, (∃ a ∈ S, c • a = y) ↔ c⁻¹ • y ∈ S := fun S =>
      ⟨fun ⟨a, ha, h⟩ => by rw [← h, smul_smul, inv_mul_cancel₀ hc, one_smul]; exact ha,
        fun hy => ⟨c⁻¹ • y, hy, by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]⟩⟩
    rw [hiff A, hiff B]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨c⁻¹ • y, Or.inl ⟨h1, h2⟩, by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]⟩
      · exact ⟨c⁻¹ • y, Or.inr ⟨h1, h2⟩, by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]⟩
    · rintro ⟨a, ha, rfl⟩
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      exact ha
  rw [heq, Measure.addHaar_smul, abs_pow]

/-- **Hausdorff-to-Nikodym Continuity at the Diagonal:**
as `L → K` in the Hausdorff metric on `ConvexBody E`, `μ (K Δ L) → 0`. -/
theorem tendsto_symmDiffVol_self (μ : Measure E) [μ.IsAddHaarMeasure] (K : ConvexBody E) :
    Tendsto (fun L : ConvexBody E => symmDiffVol μ (K : Set E) (L : Set E)) (𝓝 K) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  let δ : ℝ≥0∞ := min (ε / 2) 1
  have hδ_pos : 0 < δ := lt_min (ENNReal.half_pos hε.ne') zero_lt_one
  have hδ_top : δ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have h2δ : δ + δ ≤ ε := by
    calc
      δ + δ ≤ ε / 2 + ε / 2 := add_le_add (min_le_left _ _) (min_le_left _ _)
      _ = ε := ENNReal.add_halves ε
  have hK_fin : μ (K : Set E) ≠ ⊤ := K.isCompact.measure_lt_top.ne
  -- Part 1: `μ (L \ K) ≤ δ` for `L` sufficiently close to `K` (outer parallel-body approximation).
  have houter : ∀ᶠ L : ConvexBody E in 𝓝 K, μ ((L : Set E) \ (K : Set E)) ≤ δ := by
    let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    have hr_pos : ∀ n, 0 < r n := fun n => by positivity
    let S : ℕ → Set E := fun n => (K : Set E) + Metric.closedBall (0 : E) (r n)
    have hS_anti : Antitone S := by
      intro m n hmn x hx
      rcases Set.mem_add.mp hx with ⟨y, hy, z, hz, rfl⟩
      refine Set.add_mem_add hy (Metric.closedBall_subset_closedBall ?_ hz)
      dsimp only [r]; gcongr
    have hS_compact : ∀ n, IsCompact (S n) := fun n =>
      K.isCompact.add (isCompact_closedBall (0 : E) (r n))
    have hS_meas : ∀ n, NullMeasurableSet (S n) μ := fun n =>
      (hS_compact n).isClosed.measurableSet.nullMeasurableSet
    have hInter : (⋂ n : ℕ, S n) = (K : Set E) := by
      ext x
      simp only [mem_iInter]
      constructor
      · intro hx
        have hdist : ∀ n, ∃ y ∈ K, dist x y ≤ r n := fun n => by
          rcases Set.mem_add.mp (hx n) with ⟨y, hy, z, hz, hxyz⟩
          refine ⟨y, hy, ?_⟩
          rw [← hxyz, dist_eq_norm, add_sub_cancel_left]
          simpa [Metric.mem_closedBall, dist_zero_right] using hz
        choose yn hyn hdist_yn using hdist
        have htend : Tendsto yn atTop (𝓝 x) := by
          rw [Metric.tendsto_atTop]
          intro η hη
          obtain ⟨N, hN⟩ := exists_nat_one_div_lt hη
          refine ⟨N, fun n hn => ?_⟩
          rw [dist_comm]
          have hrle : r n ≤ 1 / ((N : ℝ) + 1) := by dsimp only [r]; gcongr
          exact (hdist_yn n).trans_lt (hrle.trans_lt hN)
        exact K.isClosed.mem_of_tendsto htend (Eventually.of_forall hyn)
      · intro hx n
        exact ⟨x, hx, 0, Metric.mem_closedBall_self (hr_pos n).le, add_zero x⟩
    have htend_meas : Tendsto (fun n => μ (S n)) atTop (𝓝 (μ (K : Set E))) := by
      rw [← hInter]
      exact tendsto_measure_iInter_atTop hS_meas hS_anti ⟨0, (hS_compact 0).measure_lt_top.ne⟩
    have hlt : μ (K : Set E) < μ (K : Set E) + δ := ENNReal.lt_add_right hK_fin hδ_pos.ne'
    obtain ⟨N, hN⟩ := (htend_meas.eventually (gt_mem_nhds hlt)).exists
    rw [Metric.eventually_nhds_iff]
    refine ⟨r N, hr_pos N, fun L hLK => ?_⟩
    have hLsub : (L : Set E) ⊆ S N := by
      intro x hxL
      obtain ⟨y, hyK, hinf⟩ := K.isCompact.exists_infDist_eq_dist K.nonempty x
      have hxy : dist x y ≤ r N := by
        rw [← hinf]
        have h1 : Metric.infDist x (K : Set E) ≤ dist L K := by
          rw [← ConvexBody.hausdorffDist_coe]
          exact Metric.infDist_le_hausdorffDist_of_mem hxL ConvexBody.hausdorffEDist_ne_top
        exact h1.trans hLK.le
      refine ⟨y, hyK, x - y, ?_, by abel_nf⟩
      simpa [Metric.mem_closedBall, dist_zero_right, dist_eq_norm] using hxy
    have hKsub : (K : Set E) ⊆ S N := fun x hx =>
      ⟨x, hx, 0, Metric.mem_closedBall_self (hr_pos N).le, add_zero x⟩
    calc
      μ ((L : Set E) \ (K : Set E)) ≤ μ (S N \ (K : Set E)) :=
        measure_mono (Set.sdiff_subset_sdiff_left hLsub)
      _ = μ (S N) - μ (K : Set E) :=
        measure_sdiff hKsub K.isClosed.measurableSet.nullMeasurableSet hK_fin
      _ ≤ δ := tsub_le_iff_left.mpr hN.le
  -- Part 2: `μ (K \ L) ≤ δ` for `L` sufficiently close to `K` (inner homothety approximation).
  have hinner : ∀ᶠ L : ConvexBody E in 𝓝 K, μ ((K : Set E) \ (L : Set E)) ≤ δ := by
    by_cases hK0 : μ (K : Set E) = 0
    · exact Eventually.of_forall fun L => by
        rw [measure_mono_null Set.sdiff_subset hK0]; exact zero_le
    have hint_ne : (interior (K : Set E)).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have hKsub : (K : Set E) ⊆ frontier (K : Set E) := by
        rw [frontier, K.isClosed.closure_eq, hemp, sdiff_empty]
      exact hK0 (measure_mono_null hKsub (K.convex.addHaar_frontier μ))
    obtain ⟨x₀, hx₀⟩ := hint_ne
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx₀)
    have hcb : Metric.closedBall x₀ (r / 2) ⊆ K :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    set d := Module.finrank ℝ E
    have htend : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ d) * μ (K : Set E)) (𝓝 1)
        (𝓝 (μ (K : Set E))) := by
      have h1 : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ d)) (𝓝 1) (𝓝 1) := by
        have hpow : Tendsto (fun t : ℝ => t ^ d) (𝓝 1) (𝓝 (1 : ℝ)) := by
          simpa using (continuous_pow d).tendsto (1 : ℝ)
        simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 1).comp hpow
      simpa [one_mul] using (ENNReal.Tendsto.mul_const h1 (Or.inr hK_fin))
    have hsub_lt : μ (K : Set E) - δ < μ (K : Set E) :=
      ENNReal.sub_lt_self hK_fin hK0 hδ_pos.ne'
    have hev_t : ∀ᶠ t : ℝ in 𝓝[<] 1,
        μ (K : Set E) - δ < ENNReal.ofReal (t ^ d) * μ (K : Set E) ∧ 0 < t := by
      have h1 : ∀ᶠ t : ℝ in 𝓝[<] 1,
          μ (K : Set E) - δ < ENNReal.ofReal (t ^ d) * μ (K : Set E) :=
        nhdsWithin_le_nhds (htend.eventually (lt_mem_nhds hsub_lt))
      have h2 : ∀ᶠ t : ℝ in 𝓝[<] 1, (0 : ℝ) < t :=
        nhdsWithin_le_nhds (lt_mem_nhds zero_lt_one)
      exact h1.and h2
    obtain ⟨t, ⟨ht_meas, ht_pos⟩, ht_lt1⟩ := (hev_t.and self_mem_nhdsWithin).exists
    have hδ_r : 0 < (1 - t) * (r / 2) := mul_pos (sub_pos.mpr ht_lt1) (by linarith)
    rw [Metric.eventually_nhds_iff]
    refine ⟨(1 - t) * (r / 2), hδ_r, fun L hLK => ?_⟩
    let H : ConvexBody E := (1 - t) • bodySingleton x₀ + t • K
    have hH_sub_L : (H : Set E) ⊆ (L : Set E) :=
      homothety_subset_of_dist_le (by linarith) ht_pos.le ht_lt1.le hcb hLK.le
    have hH_sub_K : (H : Set E) ⊆ (K : Set E) := by
      intro z hz
      rw [ConvexBody.coe_add, ConvexBody.coe_smul, ConvexBody.coe_smul, coe_bodySingleton] at hz
      rcases Set.mem_add.mp hz with ⟨_, ⟨_, rfl, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      exact K.convex (interior_subset hx₀) hy (sub_nonneg.mpr ht_lt1.le)
        ht_pos.le (sub_add_cancel 1 t)
    have hvol_H : μ (H : Set E) = ENNReal.ofReal (t ^ d) * μ (K : Set E) := by
      have hset : (H : Set E) = (fun x => -((1 - t) • x₀) + x) ⁻¹' (t • (K : Set E)) := by
        ext x
        rw [ConvexBody.coe_add, ConvexBody.coe_smul, ConvexBody.coe_smul, coe_bodySingleton]
        simp only [Set.mem_add, Set.mem_smul_set, Set.mem_singleton_iff, Set.mem_preimage]
        constructor
        · rintro ⟨_, ⟨_, rfl, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
          exact ⟨y, hy, by abel⟩
        · rintro ⟨y, hy, hxy⟩
          refine ⟨(1 - t) • x₀, ⟨x₀, rfl, rfl⟩, t • y, ⟨y, hy, rfl⟩, ?_⟩
          calc
            (1 - t) • x₀ + t • y = (1 - t) • x₀ + (-((1 - t) • x₀) + x) := by rw [← hxy]
            _ = x := by abel
      rw [hset, measure_preimage_add, Measure.addHaar_smul, abs_of_nonneg (pow_nonneg ht_pos.le _)]
    have hH_fin : μ (H : Set E) ≠ ⊤ := H.isCompact.measure_lt_top.ne
    calc
      μ ((K : Set E) \ (L : Set E)) ≤ μ ((K : Set E) \ (H : Set E)) :=
        measure_mono (Set.sdiff_subset_sdiff_right hH_sub_L)
      _ = μ (K : Set E) - μ (H : Set E) :=
        measure_sdiff hH_sub_K H.isClosed.measurableSet.nullMeasurableSet hH_fin
      _ = μ (K : Set E) - ENNReal.ofReal (t ^ d) * μ (K : Set E) := by rw [hvol_H]
      _ ≤ δ := by
        rw [tsub_le_iff_left]
        simpa [add_comm] using tsub_le_iff_left.mp ht_meas.le
  filter_upwards [hinner, houter] with L hL_in hL_out
  rw [symmDiffVol_eq_add_sdiff μ K.isClosed.measurableSet L.isClosed.measurableSet]
  exact (add_le_add hL_in hL_out).trans h2δ

/-- Real-valued diagonal continuity: `symmDiffVolReal μ K L → 0` as `L → K`. -/
theorem tendsto_symmDiffVolReal_self (μ : Measure E) [μ.IsAddHaarMeasure] (K : ConvexBody E) :
    Tendsto (fun L : ConvexBody E => symmDiffVolReal μ (K : Set E) (L : Set E)) (𝓝 K) (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (tendsto_symmDiffVol_self μ K)
  simpa [symmDiffVolReal, Function.comp_def] using h

/-- **Joint Continuity of Real Symmetric-Difference Volume on `ConvexBody E`:**
`(K, L) ↦ symmDiffVolReal μ K L` is continuous with respect to the Hausdorff metric. -/
theorem continuous_symmDiffVolReal_convexBody (μ : Measure E) [μ.IsAddHaarMeasure] :
    Continuous (fun p : ConvexBody E × ConvexBody E =>
      symmDiffVolReal μ (p.1 : Set E) (p.2 : Set E)) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨K, L⟩
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hK_ev : ∀ᶠ K' : ConvexBody E in 𝓝 K,
      symmDiffVolReal μ (K : Set E) (K' : Set E) < ε / 2 := by
    have ht := Metric.tendsto_nhds.mp (tendsto_symmDiffVolReal_self μ K) (ε / 2) (half_pos hε)
    filter_upwards [ht] with K' hK'
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (symmDiffVolReal_nonneg μ _ _)] at hK'
  have hL_ev : ∀ᶠ L' : ConvexBody E in 𝓝 L,
      symmDiffVolReal μ (L : Set E) (L' : Set E) < ε / 2 := by
    have ht := Metric.tendsto_nhds.mp (tendsto_symmDiffVolReal_self μ L) (ε / 2) (half_pos hε)
    filter_upwards [ht] with L' hL'
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (symmDiffVolReal_nonneg μ _ _)] at hL'
  obtain ⟨δ₁, hδ₁, hK_ball⟩ := Metric.eventually_nhds_iff.mp hK_ev
  obtain ⟨δ₂, hδ₂, hL_ball⟩ := Metric.eventually_nhds_iff.mp hL_ev
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  rintro ⟨K', L'⟩ hdist
  have hK' : symmDiffVolReal μ (K : Set E) (K' : Set E) < ε / 2 :=
    hK_ball (lt_of_le_of_lt (le_max_left _ _) (hdist.trans_le (min_le_left _ _)))
  have hL' : symmDiffVolReal μ (L : Set E) (L' : Set E) < ε / 2 :=
    hL_ball (lt_of_le_of_lt (le_max_right _ _) (hdist.trans_le (min_le_right _ _)))
  have hfin : ∀ A B : ConvexBody E, symmDiffVol μ (A : Set E) (B : Set E) ≠ ⊤ := fun A B =>
    symmDiffVol_ne_top μ A.isCompact.measure_lt_top.ne B.isCompact.measure_lt_top.ne
  have htri1 : symmDiffVolReal μ (K' : Set E) (L' : Set E) ≤
      symmDiffVolReal μ (K' : Set E) (K : Set E) + symmDiffVolReal μ (K : Set E) (L : Set E) +
        symmDiffVolReal μ (L : Set E) (L' : Set E) := by
    have t1 := symmDiffVolReal_triangle μ (hfin K' K) (hfin K L')
    have t2 := symmDiffVolReal_triangle μ (hfin K L) (hfin L L')
    linarith
  have htri2 : symmDiffVolReal μ (K : Set E) (L : Set E) ≤
      symmDiffVolReal μ (K : Set E) (K' : Set E) + symmDiffVolReal μ (K' : Set E) (L' : Set E) +
        symmDiffVolReal μ (L' : Set E) (L : Set E) := by
    have t1 := symmDiffVolReal_triangle μ (hfin K K') (hfin K' L)
    have t2 := symmDiffVolReal_triangle μ (hfin K' L') (hfin L' L)
    linarith
  rw [symmDiffVolReal_comm μ (K' : Set E) (K : Set E)] at htri1
  rw [symmDiffVolReal_comm μ (L' : Set E) (L : Set E)] at htri2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **Joint Continuity of `ℝ≥0∞` Symmetric-Difference Volume on `ConvexBody E`:**
`(K, L) ↦ symmDiffVol μ K L` is continuous with respect to the Hausdorff metric. -/
theorem continuous_symmDiffVol_convexBody (μ : Measure E) [μ.IsAddHaarMeasure] :
    Continuous (fun p : ConvexBody E × ConvexBody E =>
      symmDiffVol μ (p.1 : Set E) (p.2 : Set E)) := by
  have heq : (fun p : ConvexBody E × ConvexBody E =>
        symmDiffVol μ (p.1 : Set E) (p.2 : Set E)) =
      fun p => ENNReal.ofReal (symmDiffVolReal μ (p.1 : Set E) (p.2 : Set E)) := by
    ext ⟨K, L⟩
    exact (ENNReal.ofReal_toReal (symmDiffVol_ne_top μ
      K.isCompact.measure_lt_top.ne L.isCompact.measure_lt_top.ne)).symm
  rw [heq]
  exact ENNReal.continuous_ofReal.comp (continuous_symmDiffVolReal_convexBody μ)

end

end ConvexGeom
