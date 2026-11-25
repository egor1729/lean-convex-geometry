module

public import ConvexGeom.Metric.SupportFunction
public import ConvexGeom.Polytope.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Continuity and Stability of Volume on Convex Bodies

This file proves metric-measure foundations for `ConvexBody E` in a finite-dimensional real
inner product space `E` equipped with an additive Haar measure `μ` (in particular, Lebesgue
`volume`; see Schneider, *Convex Bodies*, §1.8):

1. **Volume-Root Scaling & Half-Ball Identities (`addHaar_smul_rpow_inv_finrank`,
   `addHaar_halfBall`, `addHaar_le_half_ball`,
   `addHaar_le_half_closedBall_of_zero_not_mem_interior`):**
   - `μ (c • A) ^ (1 / d) = ENNReal.ofReal c * μ A ^ (1 / d)` for `c ≥ 0` in dimension `d ≥ 1`.
   - For any nonzero vector `u : E`, the half-ball `closedBall 0 r ∩ {x | 0 ≤ ⟪x, u⟫}` has
     exactly half the volume of `closedBall 0 r`.
   - Any convex set `K ⊆ closedBall 0 r` with `0 ∉ interior K` has `μ K ≤ μ (closedBall 0 r) / 2`.
2. **Hausdorff Continuity of Volume (`continuous_addHaar_convexBody`,
   `continuous_addHaarReal_convexBody`):**
   `K ↦ μ (K : Set E)` (and `K ↦ (μ (K : Set E)).toReal`) is **continuous** on `ConvexBody E`
   with respect to the Hausdorff metric:
   - *Upper semicontinuity* follows from monotone downward continuity of measure on
     `⋂ n, K + closedBall 0 (1 / (n + 1)) = K`.
   - *Lower semicontinuity* is proved cleanly via support functions: if `closedBall x₀ r ⊆ K`,
     then `dist L K < (1 - t) * r` implies `x₀ + t • (K - x₀) ⊆ L` in three lines via
     `supportFn_le_iff_subset`.
3. **Continuity and Compactness of Polytope Hull Volume (`continuous_addHaar_convexHull_range`,
   `exists_max_addHaar_convexHull_of_isCompact`):**
   For finite point configurations `v : ι → E`, `v ↦ μ (convexHull ℝ (Set.range v))` is
   continuous, hence attains its maximum over any compact nonempty vertex domain `S ⊆ E`
   (in particular `sphere 0 r` and `closedBall 0 r`).
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
    measurableSet_closedBall.inter (isClosed_le continuous_const (continuous_id.inner continuous_const)).measurableSet
  have hQ_meas : MeasurableSet Q :=
    measurableSet_closedBall.inter (isClosed_le (continuous_id.inner continuous_const) continuous_const).measurableSet
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
`dist L K ≤ (1 - t) * r` for `0 < t < 1`, then the contracted copy `x₀ + t • (K - x₀)` lies in `L`. -/
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
    {ι : Type*} [Fintype ι] [Nonempty ι] :
    Continuous (fun v : ι → E => μ (convexHull ℝ (Set.range v))) := by
  classical
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
    {ι : Type*} [Fintype ι] [Nonempty ι] :
    Continuous (fun v : ι → E => μ.real (convexHull ℝ (Set.range v))) := by
  classical
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
    {ι : Type*} [Fintype ι] [Nonempty ι] {S : Set E} (hSc : IsCompact S) (hSne : S.Nonempty) :
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
    {ι : Type*} [Fintype ι] [Nonempty ι] {S : Set E} (hSc : IsCompact S) (hSne : S.Nonempty) :
    ∃ v : ι → E, (∀ i, v i ∈ S) ∧
      ∀ w : ι → E, (∀ i, w i ∈ S) →
        μ.real (convexHull ℝ (Set.range w)) ≤ μ.real (convexHull ℝ (Set.range v)) := by
  classical
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
    {ι : Type*} [Fintype ι] [Nonempty ι] {r : ℝ} (hr : 0 ≤ r) :
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
    {ι : Type*} [Fintype ι] [Nonempty ι] {r : ℝ} (hr : 0 ≤ r) :
    ∃ v : ι → E, (∀ i, v i ∈ Metric.closedBall (0 : E) r) ∧
      ∀ w : ι → E, (∀ i, w i ∈ Metric.closedBall (0 : E) r) →
        μ (convexHull ℝ (Set.range w)) ≤ μ (convexHull ℝ (Set.range v)) :=
  exists_max_addHaar_convexHull_of_isCompact μ (isCompact_closedBall (0 : E) r)
    ⟨0, Metric.mem_closedBall_self hr⟩

end

end ConvexGeom
