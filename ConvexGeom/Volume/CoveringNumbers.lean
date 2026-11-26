module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.MetricSpace.CoveringNumbers

import Mathlib.Order.Zorn

/-!
# Volumetric Bounds for Covering and Packing Numbers

Volumetric bounds for metric and translative covering/packing numbers in a finite-dimensional
real normed space `E` with an additive Haar measure `μ`
(Vershynin, *High-Dimensional Probability*, §4.2; Ball, Lecture 2;
Artstein-Avidan–Giannopoulos–Milman, *Asymptotic Geometric Analysis I*, §4.1):

1. **General Volumetric Lower Bound (`measure_le_externalCoveringNumber_mul_closedBall`):**
   For `0 < ε`, `μ(A) ≤ N_ext(A, ε) * μ(closedBall 0 ε)`.
2. **General Volumetric Upper Bound (`packingNumber_mul_ball_le_measure_add_ball`):**
   `P(A, ε) * μ(ball 0 (ε / 2)) ≤ μ(A + ball 0 (ε / 2))`, and likewise for `coveringNumber`.
3. **Unit-Ball Bounds for Any Norm (`inv_pow_le_externalCoveringNumber_closedBall`,
   `packingNumber_closedBall_le`, `coveringNumber_closedBall_le`,
   `coveringNumber_closedBall_le_three_div`):**
   `(1 / ε)^d ≤ N_ext(B, ε)` and `N(B, ε) ≤ P(B, ε) ≤ (2 / ε + 1)^d`.
4. **Translative Covering Numbers (`IsTranslativeCover`, `translativeCoveringNumber`,
   `translativeCoveringNumber_mul_le`, `measure_le_translativeCoveringNumber_mul`,
   `translativeCoveringNumber_sub_mul_le`, `translativeCoveringNumber_symm_smul_le`):**
   General `N(A, T) = inf { |C| : A ⊆ C + T }`, submultiplicativity, volumetric lower bound,
   Zorn packing bound `N(A, B - B) * μ(B) ≤ μ(A + B)`, and origin-symmetric homothet bound
   `N(K, t • K) ≤ (2 / t + 1)^d`.
-/

open MeasureTheory Set Metric
open scoped ENNReal NNReal Pointwise

namespace ConvexGeom

public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Helper: cancellation `a * b ≤ c * b → a ≤ c` in `ℝ≥0∞` when `0 < b < ∞`. -/
private lemma ennreal_le_of_mul_le_mul_right {a b c : ℝ≥0∞} (hb0 : b ≠ 0) (hbtop : b ≠ ⊤)
    (h : a * b ≤ c * b) : a ≤ c := by
  calc
    a = a * (b * b⁻¹) := by rw [ENNReal.mul_inv_cancel hb0 hbtop, mul_one]
    _ = (a * b) * b⁻¹ := (mul_assoc a b b⁻¹).symm
    _ ≤ (c * b) * b⁻¹ := by gcongr
    _ = c := by rw [mul_assoc, ENNReal.mul_inv_cancel hb0 hbtop, mul_one]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Helper: an open ball of positive radius has strictly positive Haar measure. -/
private lemma addHaar_ball_pos (μ : Measure E) [μ.IsAddHaarMeasure] {r : ℝ} (hr : 0 < r) :
    0 < μ (Metric.ball (0 : E) r) :=
  Metric.isOpen_ball.measure_pos μ (Metric.nonempty_ball.mpr hr)

/-! ### 1. General Volumetric Lower Bound -/

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Any `ε`-cover `C` of `A` (with `0 < ε`) satisfies `μ A ≤ C.encard * μ (closedBall 0 ε)`. -/
lemma measure_le_encard_mul_closedBall_of_isCover (μ : Measure E) [μ.IsAddHaarMeasure]
    {ε : ℝ≥0} (hε : 0 < ε) {A C : Set E} (hC : Metric.IsCover ε A C) :
    μ A ≤ (C.encard : ℝ≥0∞) * μ (Metric.closedBall (0 : E) ε) := by
  by_cases hfin : C.Finite
  · have hsub : A ⊆ ⋃ x ∈ hfin.toFinset, Metric.closedBall x ε := by
      intro a ha
      obtain ⟨x, hxC, hax⟩ := hC ha
      refine mem_iUnion₂.mpr ⟨x, hfin.mem_toFinset.mpr hxC, ?_⟩
      rw [Metric.mem_closedBall]
      have hle : edist a x ≤ (ε : ℝ≥0∞) := hax
      rw [edist_dist, ← ENNReal.ofReal_coe_nnreal] at hle
      exact (ENNReal.ofReal_le_ofReal_iff ε.coe_nonneg).mp hle
    calc
      μ A ≤ μ (⋃ x ∈ hfin.toFinset, Metric.closedBall x ε) := measure_mono hsub
      _ ≤ ∑ x ∈ hfin.toFinset, μ (Metric.closedBall x ε) := measure_biUnion_finset_le _ _
      _ = ∑ _x ∈ hfin.toFinset, μ (Metric.closedBall (0 : E) ε) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            exact Measure.addHaar_closedBall_center μ x ε
      _ = (hfin.toFinset.card : ℝ≥0∞) * μ (Metric.closedBall (0 : E) ε) := by simp
      _ = (C.encard : ℝ≥0∞) * μ (Metric.closedBall (0 : E) ε) := by
            rw [hfin.encard_eq_coe_toFinset_card]; simp
  · have htop : C.encard = ⊤ := Set.Infinite.encard_eq hfin
    have hball_ne : μ (Metric.closedBall (0 : E) ε) ≠ 0 :=
      ne_of_gt ((addHaar_ball_pos μ hε).trans_le (measure_mono Metric.ball_subset_closedBall))
    rw [htop, ENat.toENNReal_top, ENNReal.top_mul hball_ne]
    exact le_top

/-- **Volumetric Lower Bound for External Covering Number:**
For `0 < ε`, `μ A ≤ externalCoveringNumber ε A * μ (closedBall 0 ε)`. -/
theorem measure_le_externalCoveringNumber_mul_closedBall
    (μ : Measure E) [μ.IsAddHaarMeasure] {ε : ℝ≥0} (hε : 0 < ε) (A : Set E) :
    μ A ≤ (Metric.externalCoveringNumber ε A : ℝ≥0∞) * μ (Metric.closedBall (0 : E) ε) := by
  have hball_ne : μ (Metric.closedBall (0 : E) ε) ≠ 0 :=
    ne_of_gt ((addHaar_ball_pos μ hε).trans_le (measure_mono Metric.ball_subset_closedBall))
  have hball_top : μ (Metric.closedBall (0 : E) ε) ≠ ⊤ :=
    (isCompact_closedBall (0 : E) ε).measure_lt_top.ne
  by_cases htop : Metric.externalCoveringNumber ε A = ⊤
  · rw [htop, ENat.toENNReal_top, ENNReal.top_mul hball_ne]
    exact le_top
  · -- When `externalCoveringNumber ε A < ⊤`, it is attained by a cover `C` since `ℕ∞` is well-ordered!
    have hne : {n : ℕ∞ | ∃ C : Set E, Metric.IsCover ε A C ∧ C.encard = n}.Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have hnone : ∀ C : Set E, ¬ Metric.IsCover ε A C := fun C hC =>
        Set.notMem_empty C.encard (hemp ▸ ⟨C, hC, rfl⟩)
      have : Metric.externalCoveringNumber ε A = ⊤ := by
        simp [Metric.externalCoveringNumber, hnone]
      exact htop this
    have hex : ∃ C : Set E, Metric.IsCover ε A C ∧ C.encard = Metric.externalCoveringNumber ε A := by
      obtain ⟨n, hn_mem, hn_min⟩ :=
        WellFounded.has_min wellFounded_lt _ hne
      obtain ⟨C, hC, rfl⟩ := hn_mem
      refine ⟨C, hC, le_antisymm ?_ ?_⟩
      · refine le_iInf fun D => le_iInf fun hD => ?_
        exact not_lt.mp (hn_min D.encard ⟨D, hD, rfl⟩)
      · exact iInf_le_of_le C (iInf_le_of_le hC le_rfl)
    obtain ⟨C, hC, hcard⟩ := hex
    rw [← hcard]
    exact measure_le_encard_mul_closedBall_of_isCover μ hε hC

/-- **Volumetric Lower Bound for Internal Covering Number:**
For `0 < ε`, `μ A ≤ coveringNumber ε A * μ (closedBall 0 ε)`. -/
theorem measure_le_coveringNumber_mul_closedBall
    (μ : Measure E) [μ.IsAddHaarMeasure] {ε : ℝ≥0} (hε : 0 < ε) (A : Set E) :
    μ A ≤ (Metric.coveringNumber ε A : ℝ≥0∞) * μ (Metric.closedBall (0 : E) ε) := by
  refine (measure_le_externalCoveringNumber_mul_closedBall μ hε A).trans ?_
  gcongr
  exact Metric.externalCoveringNumber_le_coveringNumber ε A

/-! ### 2. General Volumetric Upper Bound (via Packing) -/

/-- Any `ε`-separated subset `C ⊆ A` has pairwise disjoint open balls of radius `ε / 2`,
all contained in `A + ball 0 (ε / 2)`, giving `C.encard * μ (ball 0 (ε / 2)) ≤ μ (A + ball 0 (ε / 2))`. -/
lemma encard_mul_ball_le_measure_add_ball_of_isSeparated (μ : Measure E) [μ.IsAddHaarMeasure]
    {ε : ℝ≥0} {A C : Set E} (hCA : C ⊆ A) (hsep : Metric.IsSeparated ε C) :
    (C.encard : ℝ≥0∞) * μ (Metric.ball (0 : E) ((ε : ℝ) / 2)) ≤
      μ (A + Metric.ball (0 : E) ((ε : ℝ) / 2)) := by
  have hfin_bound : ∀ F : Finset E, (F : Set E) ⊆ C →
      (F.card : ℝ≥0∞) * μ (Metric.ball (0 : E) ((ε : ℝ) / 2)) ≤
        μ (A + Metric.ball (0 : E) ((ε : ℝ) / 2)) := by
    intro F hFC
    have hdisj : Set.PairwiseDisjoint (F : Set E) (fun x => Metric.ball x ((ε : ℝ) / 2)) := by
      intro x hx y hy hxy
      change Disjoint (Metric.ball x ((ε : ℝ) / 2)) (Metric.ball y ((ε : ℝ) / 2))
      rw [Set.disjoint_left]
      intro z hzx hzy
      have hhalf_eq : (ε : ℝ≥0∞) / 2 = ENNReal.ofReal ((ε : ℝ) / 2) := by
        rw [ENNReal.ofReal_div_of_pos zero_lt_two]; simp
      have h1 : edist z x < (ε : ℝ≥0∞) / 2 := by
        rw [Metric.mem_ball] at hzx
        rw [edist_dist, hhalf_eq]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [dist_nonneg (x := z) (y := x)])).mpr hzx
      have h2 : edist z y < (ε : ℝ≥0∞) / 2 := by
        rw [Metric.mem_ball] at hzy
        rw [edist_dist, hhalf_eq]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [dist_nonneg (x := z) (y := y)])).mpr hzy
      have hlt : edist x y < ε := by
        calc
          edist x y ≤ edist x z + edist z y := edist_triangle x z y
          _ = edist z x + edist z y := by rw [edist_comm]
          _ < (ε : ℝ≥0∞) / 2 + (ε : ℝ≥0∞) / 2 := ENNReal.add_lt_add h1 h2
          _ = ε := ENNReal.add_halves _
      exact not_lt.mpr (hsep (hFC hx) (hFC hy) hxy).le hlt
    have hsub : (⋃ x ∈ F, Metric.ball x ((ε : ℝ) / 2)) ⊆ A + Metric.ball (0 : E) ((ε : ℝ) / 2) := by
      intro z hz
      rcases mem_iUnion₂.mp hz with ⟨x, hxF, hzx⟩
      refine ⟨x, hCA (hFC hxF), z - x, ?_, by abel_nf⟩
      simpa [Metric.mem_ball, dist_eq_norm] using hzx
    calc
      (F.card : ℝ≥0∞) * μ (Metric.ball (0 : E) ((ε : ℝ) / 2))
        = ∑ _x ∈ F, μ (Metric.ball (0 : E) ((ε : ℝ) / 2)) := by simp
      _ = ∑ x ∈ F, μ (Metric.ball x ((ε : ℝ) / 2)) := by
            refine Finset.sum_congr rfl fun x _ => (Measure.addHaar_ball_center μ x _).symm
      _ = μ (⋃ x ∈ F, Metric.ball x ((ε : ℝ) / 2)) :=
            (measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)).symm
      _ ≤ μ (A + Metric.ball (0 : E) ((ε : ℝ) / 2)) := measure_mono hsub
  by_cases hfin : C.Finite
  · rw [hfin.encard_eq_coe_toFinset_card]
    simpa using hfin_bound hfin.toFinset (by simp)
  · have htop : C.encard = ⊤ := Set.Infinite.encard_eq hfin
    rw [htop, ENat.toENNReal_top]
    by_cases hball : μ (Metric.ball (0 : E) ((ε : ℝ) / 2)) = 0
    · simp [hball]
    · rw [ENNReal.top_mul hball, top_le_iff]
      by_contra hne_top
      have hball_ne_top : μ (Metric.ball (0 : E) ((ε : ℝ) / 2)) ≠ ⊤ :=
        ne_of_lt ((measure_mono Metric.ball_subset_closedBall).trans_lt
          (isCompact_closedBall (0 : E) ((ε : ℝ) / 2)).measure_lt_top)
      let r : ℝ := (μ (A + Metric.ball (0 : E) ((ε : ℝ) / 2))).toReal /
        (μ (Metric.ball (0 : E) ((ε : ℝ) / 2))).toReal
      obtain ⟨n, hn⟩ := exists_nat_gt r
      obtain ⟨F, hFC, hFcard⟩ := Set.Infinite.exists_subset_card_eq hfin n
      have hle := hfin_bound F hFC
      rw [hFcard] at hle
      have hle_real := ENNReal.toReal_mono hne_top hle
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hle_real
      have hpos_real : 0 < (μ (Metric.ball (0 : E) ((ε : ℝ) / 2))).toReal :=
        ENNReal.toReal_pos hball hball_ne_top
      have hlt_real : (μ (A + Metric.ball (0 : E) ((ε : ℝ) / 2))).toReal <
          (n : ℝ) * (μ (Metric.ball (0 : E) ((ε : ℝ) / 2))).toReal :=
        (div_lt_iff₀ hpos_real).mp hn
      linarith

/-- **Volumetric Upper Bound for Packing Number:**
`packingNumber ε A * μ (ball 0 (ε / 2)) ≤ μ (A + ball 0 (ε / 2))`. -/
theorem packingNumber_mul_ball_le_measure_add_ball
    (μ : Measure E) [μ.IsAddHaarMeasure] (ε : ℝ≥0) (A : Set E) :
    (Metric.packingNumber ε A : ℝ≥0∞) * μ (Metric.ball (0 : E) ((ε : ℝ) / 2)) ≤
      μ (A + Metric.ball (0 : E) ((ε : ℝ) / 2)) := by
  by_cases htop : Metric.packingNumber ε A = ⊤
  · rw [htop, ENat.toENNReal_top]
    by_cases hball : μ (Metric.ball (0 : E) ((ε : ℝ) / 2)) = 0
    · simp [hball]
    · rw [ENNReal.top_mul hball, top_le_iff]
      by_contra hne_top
      have hball_ne_top : μ (Metric.ball (0 : E) ((ε : ℝ) / 2)) ≠ ⊤ :=
        ne_of_lt ((measure_mono Metric.ball_subset_closedBall).trans_lt
          (isCompact_closedBall (0 : E) ((ε : ℝ) / 2)).measure_lt_top)
      let r : ℝ := (μ (A + Metric.ball (0 : E) ((ε : ℝ) / 2))).toReal /
        (μ (Metric.ball (0 : E) ((ε : ℝ) / 2))).toReal
      obtain ⟨n, hn⟩ := exists_nat_gt r
      -- Since `packingNumber ε A = ⊤`, there exists an `ε`-separated `C ⊆ A` with `n < C.encard`.
      have hex : ∃ C : Set E, C ⊆ A ∧ Metric.IsSeparated ε C ∧ (n : ℕ∞) < C.encard := by
        by_contra hall
        push Not at hall
        have hle_n : Metric.packingNumber ε A ≤ n :=
          iSup_le fun C => iSup_le fun hCA => iSup_le fun hsep => hall C hCA hsep
        rw [htop] at hle_n
        exact (ENat.natCast_lt_top n).not_ge hle_n
      obtain ⟨C, hCA, hsep, hcard⟩ := hex
      have hle := encard_mul_ball_le_measure_add_ball_of_isSeparated μ hCA hsep
      have hle_n : (n : ℝ≥0∞) * μ (Metric.ball (0 : E) ((ε : ℝ) / 2)) ≤
          μ (A + Metric.ball (0 : E) ((ε : ℝ) / 2)) := by
        refine le_trans ?_ hle
        gcongr
        exact_mod_cast hcard.le
      have hle_real := ENNReal.toReal_mono hne_top hle_n
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hle_real
      have hpos_real : 0 < (μ (Metric.ball (0 : E) ((ε : ℝ) / 2))).toReal :=
        ENNReal.toReal_pos hball hball_ne_top
      have hlt_real : (μ (A + Metric.ball (0 : E) ((ε : ℝ) / 2))).toReal <
          (n : ℝ) * (μ (Metric.ball (0 : E) ((ε : ℝ) / 2))).toReal :=
        (div_lt_iff₀ hpos_real).mp hn
      linarith
  · rw [← Metric.encard_maximalSeparatedSet htop]
    exact encard_mul_ball_le_measure_add_ball_of_isSeparated μ
      Metric.maximalSeparatedSet_subset Metric.isSeparated_maximalSeparatedSet

/-- **Volumetric Upper Bound for Internal Covering Number:**
`coveringNumber ε A * μ (ball 0 (ε / 2)) ≤ μ (A + ball 0 (ε / 2))`. -/
theorem coveringNumber_mul_ball_le_measure_add_ball
    (μ : Measure E) [μ.IsAddHaarMeasure] (ε : ℝ≥0) (A : Set E) :
    (Metric.coveringNumber ε A : ℝ≥0∞) * μ (Metric.ball (0 : E) ((ε : ℝ) / 2)) ≤
      μ (A + Metric.ball (0 : E) ((ε : ℝ) / 2)) := by
  refine le_trans ?_ (packingNumber_mul_ball_le_measure_add_ball μ ε A)
  gcongr
  exact Metric.coveringNumber_le_packingNumber ε A

/-! ### 3. Sharp Covering & Packing Bounds for the Unit Ball in ANY Norm on `ℝ^d` -/

/-- **Volumetric Lower Bound for the Unit Ball (Vershynin Cor. 4.2.13):**
For any `0 < ε` and any norm on a finite-dimensional real space `E` of dimension `d`,
`(1 / ε)^d ≤ externalCoveringNumber ε (closedBall 0 1)`. -/
theorem inv_pow_le_externalCoveringNumber_closedBall
    (μ : Measure E) [μ.IsAddHaarMeasure] {ε : ℝ≥0} (hε : 0 < ε) :
    ENNReal.ofReal ((1 / (ε : ℝ)) ^ Module.finrank ℝ E) ≤
      (Metric.externalCoveringNumber ε (Metric.closedBall (0 : E) 1) : ℝ≥0∞) := by
  set d := Module.finrank ℝ E
  have hε_pos : (0 : ℝ) < ε := hε
  have h1 := measure_le_externalCoveringNumber_mul_closedBall μ hε (Metric.closedBall (0 : E) 1)
  have hball_ε : μ (Metric.closedBall (0 : E) ε) =
      ENNReal.ofReal ((ε : ℝ) ^ d) * μ (Metric.closedBall (0 : E) 1) := by
    have := Measure.addHaar_closedBall_mul_of_pos μ (0 : E) hε_pos 1
    simpa [mul_one, abs_of_nonneg hε_pos.le] using this
  rw [hball_ε] at h1
  have hB_pos : 0 < μ (Metric.closedBall (0 : E) 1) :=
    (addHaar_ball_pos μ zero_lt_one).trans_le (measure_mono Metric.ball_subset_closedBall)
  have hB_top : μ (Metric.closedBall (0 : E) 1) ≠ ⊤ :=
    (isCompact_closedBall (0 : E) 1).measure_lt_top.ne
  have hcancel : (1 : ℝ≥0∞) ≤
      (Metric.externalCoveringNumber ε (Metric.closedBall (0 : E) 1) : ℝ≥0∞) *
        ENNReal.ofReal ((ε : ℝ) ^ d) := by
    refine ennreal_le_of_mul_le_mul_right hB_pos.ne' hB_top ?_
    simpa [one_mul, mul_assoc] using h1
  have hinv : ENNReal.ofReal ((1 / (ε : ℝ)) ^ d) * ENNReal.ofReal ((ε : ℝ) ^ d) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow, one_div_mul_cancel hε_pos.ne', one_pow,
      ENNReal.ofReal_one]
  calc
    ENNReal.ofReal ((1 / (ε : ℝ)) ^ d)
      = ENNReal.ofReal ((1 / (ε : ℝ)) ^ d) * 1 := (mul_one _).symm
    _ ≤ ENNReal.ofReal ((1 / (ε : ℝ)) ^ d) *
          ((Metric.externalCoveringNumber ε (Metric.closedBall (0 : E) 1) : ℝ≥0∞) *
            ENNReal.ofReal ((ε : ℝ) ^ d)) := by gcongr
    _ = (Metric.externalCoveringNumber ε (Metric.closedBall (0 : E) 1) : ℝ≥0∞) *
          (ENNReal.ofReal ((1 / (ε : ℝ)) ^ d) * ENNReal.ofReal ((ε : ℝ) ^ d)) := by ring
    _ = (Metric.externalCoveringNumber ε (Metric.closedBall (0 : E) 1) : ℝ≥0∞) := by
          rw [hinv, mul_one]

/-- **Volumetric Upper Bound for Packing Number of the Unit Ball (Vershynin Cor. 4.2.13):**
For any `0 < ε` and any norm on a finite-dimensional real space `E` of dimension `d`,
`packingNumber ε (closedBall 0 1) ≤ (2 / ε + 1)^d`. -/
theorem packingNumber_closedBall_le
    (μ : Measure E) [μ.IsAddHaarMeasure] {ε : ℝ≥0} (hε : 0 < ε) :
    (Metric.packingNumber ε (Metric.closedBall (0 : E) 1) : ℝ≥0∞) ≤
      ENNReal.ofReal ((2 / (ε : ℝ) + 1) ^ Module.finrank ℝ E) := by
  set d := Module.finrank ℝ E
  have hε_pos : (0 : ℝ) < ε := hε
  have hhalf_pos : (0 : ℝ) < (ε : ℝ) / 2 := half_pos hε_pos
  have h1 := packingNumber_mul_ball_le_measure_add_ball μ ε (Metric.closedBall (0 : E) 1)
  have hsub : Metric.closedBall (0 : E) 1 + Metric.ball (0 : E) ((ε : ℝ) / 2) ⊆
      Metric.ball (0 : E) (1 + (ε : ℝ) / 2) := by
    intro z hz
    rcases Set.mem_add.mp hz with ⟨x, hx, y, hy, rfl⟩
    rw [Metric.mem_ball, dist_zero_right]
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    rw [Metric.mem_ball, dist_zero_right] at hy
    calc
      ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
      _ < 1 + (ε : ℝ) / 2 := by linarith
  have h2 : (Metric.packingNumber ε (Metric.closedBall (0 : E) 1) : ℝ≥0∞) *
      μ (Metric.ball (0 : E) ((ε : ℝ) / 2)) ≤
      μ (Metric.ball (0 : E) (1 + (ε : ℝ) / 2)) :=
    h1.trans (measure_mono hsub)
  have hscale : μ (Metric.ball (0 : E) (1 + (ε : ℝ) / 2)) =
      ENNReal.ofReal ((2 / (ε : ℝ) + 1) ^ d) * μ (Metric.ball (0 : E) ((ε : ℝ) / 2)) := by
    have hfactor : 1 + (ε : ℝ) / 2 = (2 / (ε : ℝ) + 1) * ((ε : ℝ) / 2) := by
      field_simp [hε_pos.ne']
    have hpos_f : (0 : ℝ) < 2 / (ε : ℝ) + 1 := by positivity
    rw [hfactor]
    simpa [abs_of_nonneg hpos_f.le] using
      Measure.addHaar_ball_mul_of_pos μ (0 : E) hpos_f ((ε : ℝ) / 2)
  rw [hscale] at h2
  have hball_pos : 0 < μ (Metric.ball (0 : E) ((ε : ℝ) / 2)) := addHaar_ball_pos μ hhalf_pos
  have hball_top : μ (Metric.ball (0 : E) ((ε : ℝ) / 2)) ≠ ⊤ :=
    ne_of_lt ((measure_mono Metric.ball_subset_closedBall).trans_lt
      (isCompact_closedBall (0 : E) ((ε : ℝ) / 2)).measure_lt_top)
  exact ennreal_le_of_mul_le_mul_right hball_pos.ne' hball_top h2

/-- **Volumetric Upper Bound for Internal Covering Number of the Unit Ball:**
For any `0 < ε`, `coveringNumber ε (closedBall 0 1) ≤ (2 / ε + 1)^d`. -/
theorem coveringNumber_closedBall_le
    (μ : Measure E) [μ.IsAddHaarMeasure] {ε : ℝ≥0} (hε : 0 < ε) :
    (Metric.coveringNumber ε (Metric.closedBall (0 : E) 1) : ℝ≥0∞) ≤
      ENNReal.ofReal ((2 / (ε : ℝ) + 1) ^ Module.finrank ℝ E) := by
  refine le_trans ?_ (packingNumber_closedBall_le μ hε)
  exact_mod_cast Metric.coveringNumber_le_packingNumber ε _

/-- **Vershynin's Classic `(3 / ε)^d` Covering Bound for the Unit Ball:**
For `0 < ε ≤ 1` and any norm on a `d`-dimensional real space `E`,
`coveringNumber ε (closedBall 0 1) ≤ (3 / ε)^d`. -/
theorem coveringNumber_closedBall_le_three_div
    (μ : Measure E) [μ.IsAddHaarMeasure] {ε : ℝ≥0} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (Metric.coveringNumber ε (Metric.closedBall (0 : E) 1) : ℝ≥0∞) ≤
      ENNReal.ofReal ((3 / (ε : ℝ)) ^ Module.finrank ℝ E) := by
  refine (coveringNumber_closedBall_le μ hε).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hε_pos : (0 : ℝ) < ε := hε
  have hε1' : (ε : ℝ) ≤ 1 := hε1
  have hle : 2 / (ε : ℝ) + 1 ≤ 3 / (ε : ℝ) := by
    have h1 : (1 : ℝ) ≤ 1 / (ε : ℝ) := (le_div_iff₀ hε_pos).mpr (by linarith)
    linarith [show (3 : ℝ) / ε = 2 / ε + 1 / ε by ring]
  exact pow_le_pow_left₀ (by positivity) hle _

/-! ### 4. Translative Covering Numbers -/

section TranslativeAlgebra

variable {G : Type*} [AddCommGroup G]

/-- A set `C ⊆ G` is a **translative cover** of `A` by `T` if `A ⊆ C + T`, i.e.,
`A ⊆ ⋃ x ∈ C, (x +ᵥ T)`. -/
@[expose]
def IsTranslativeCover (A T C : Set G) : Prop :=
  A ⊆ C + T

/-- The **translative covering number** `N(A, T)`: the minimum cardinality (in `ℕ∞`) of a set `C`
such that `A ⊆ C + T`. -/
@[expose]
noncomputable def translativeCoveringNumber (A T : Set G) : ℕ∞ :=
  ⨅ (C : Set G) (_ : IsTranslativeCover A T C), C.encard

lemma translativeCoveringNumber_le_encard {A T C : Set G} (hC : IsTranslativeCover A T C) :
    translativeCoveringNumber A T ≤ C.encard :=
  iInf_le_of_le C (iInf_le_of_le hC le_rfl)

lemma le_translativeCoveringNumber_iff {A T : Set G} {n : ℕ∞} :
    n ≤ translativeCoveringNumber A T ↔ ∀ C : Set G, IsTranslativeCover A T C → n ≤ C.encard := by
  simp [translativeCoveringNumber]

/-- When `translativeCoveringNumber A T ≠ ⊤`, the infimum is attained by some cover `C`. -/
lemma exists_isTranslativeCover_encard_eq {A T : Set G}
    (hfin : translativeCoveringNumber A T ≠ ⊤) :
    ∃ C : Set G, IsTranslativeCover A T C ∧ C.encard = translativeCoveringNumber A T := by
  have hne : {n : ℕ∞ | ∃ C : Set G, IsTranslativeCover A T C ∧ C.encard = n}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hnone : ∀ C : Set G, ¬ IsTranslativeCover A T C := fun C hC =>
      Set.notMem_empty C.encard (hemp ▸ ⟨C, hC, rfl⟩)
    exact hfin (by simp [translativeCoveringNumber, hnone])
  obtain ⟨n, ⟨C, hC, rfl⟩, hn_min⟩ := WellFounded.has_min wellFounded_lt _ hne
  refine ⟨C, hC, le_antisymm ?_ (translativeCoveringNumber_le_encard hC)⟩
  exact le_translativeCoveringNumber_iff.mpr fun D hD => not_lt.mp (hn_min D.encard ⟨D, hD, rfl⟩)

lemma translativeCoveringNumber_mono_left {A₁ A₂ T : Set G} (h : A₁ ⊆ A₂) :
    translativeCoveringNumber A₁ T ≤ translativeCoveringNumber A₂ T :=
  le_translativeCoveringNumber_iff.mpr fun _ hC =>
    translativeCoveringNumber_le_encard (h.trans hC)

lemma translativeCoveringNumber_antitone_right {A T₁ T₂ : Set G} (h : T₁ ⊆ T₂) :
    translativeCoveringNumber A T₂ ≤ translativeCoveringNumber A T₁ :=
  le_translativeCoveringNumber_iff.mpr fun _ hC =>
    translativeCoveringNumber_le_encard (hC.trans (Set.add_subset_add_left h))

@[simp]
lemma translativeCoveringNumber_empty (T : Set G) :
    translativeCoveringNumber (∅ : Set G) T = 0 :=
  le_antisymm
    (by
      have h := translativeCoveringNumber_le_encard (C := (∅ : Set G)) (T := T) (Set.empty_subset _)
      simpa using h)
    (zero_le)

lemma translativeCoveringNumber_self_le_one (A : Set G) :
    translativeCoveringNumber A A ≤ 1 := by
  have hcov : IsTranslativeCover A A {0} := by
    intro a ha
    exact ⟨0, Set.mem_singleton 0, a, ha, zero_add a⟩
  simpa using translativeCoveringNumber_le_encard hcov

lemma one_le_translativeCoveringNumber {A T : Set G} (hA : A.Nonempty) :
    1 ≤ translativeCoveringNumber A T := by
  refine le_translativeCoveringNumber_iff.mpr fun C hC => ?_
  obtain ⟨a, ha⟩ := hA
  rcases Set.mem_add.mp (hC ha) with ⟨c, hc, _, _, _⟩
  exact Set.one_le_encard_iff_nonempty.mpr ⟨c, hc⟩

private lemma translativeCoveringNumber_vadd_left_le (x : G) (A T : Set G) :
    translativeCoveringNumber (x +ᵥ A) T ≤ translativeCoveringNumber A T := by
  refine le_translativeCoveringNumber_iff.mpr fun C hC => ?_
  have hcov : IsTranslativeCover (x +ᵥ A) T (x +ᵥ C) := by
    rintro _ ⟨a, ha, rfl⟩
    rcases Set.mem_add.mp (hC ha) with ⟨c, hc, t, ht, rfl⟩
    exact ⟨x + c, ⟨c, hc, rfl⟩, t, ht, add_assoc x c t⟩
  have hcard : (x +ᵥ C).encard = C.encard :=
    (add_right_injective x).encard_image C
  exact hcard ▸ translativeCoveringNumber_le_encard hcov

@[simp]
lemma translativeCoveringNumber_vadd_left (x : G) (A T : Set G) :
    translativeCoveringNumber (x +ᵥ A) T = translativeCoveringNumber A T :=
  le_antisymm (translativeCoveringNumber_vadd_left_le x A T)
    (by simpa using translativeCoveringNumber_vadd_left_le (-x) (x +ᵥ A) T)

private lemma translativeCoveringNumber_vadd_right_le (x : G) (A T : Set G) :
    translativeCoveringNumber A (x +ᵥ T) ≤ translativeCoveringNumber A T := by
  refine le_translativeCoveringNumber_iff.mpr fun C hC => ?_
  have hcov : IsTranslativeCover A (x +ᵥ T) ((-x) +ᵥ C) := by
    intro a ha
    rcases Set.mem_add.mp (hC ha) with ⟨c, hc, t, ht, rfl⟩
    exact ⟨-x + c, ⟨c, hc, rfl⟩, x + t, ⟨t, ht, rfl⟩, by abel_nf⟩
  have hcard : ((-x) +ᵥ C).encard = C.encard :=
    (add_right_injective (-x)).encard_image C
  exact hcard ▸ translativeCoveringNumber_le_encard hcov

@[simp]
lemma translativeCoveringNumber_vadd_right (x : G) (A T : Set G) :
    translativeCoveringNumber A (x +ᵥ T) = translativeCoveringNumber A T :=
  le_antisymm (translativeCoveringNumber_vadd_right_le x A T)
    (by simpa using translativeCoveringNumber_vadd_right_le (-x) A (x +ᵥ T))

/-- **Submultiplicativity of translative covering numbers:**
when `B` is nonempty, `N(A, T) ≤ N(A, B) * N(B, T)`. -/
theorem translativeCoveringNumber_mul_le (A : Set G) {B : Set G} (hB : B.Nonempty) (T : Set G) :
    translativeCoveringNumber A T ≤
      translativeCoveringNumber A B * translativeCoveringNumber B T := by
  rcases A.eq_empty_or_nonempty with rfl | hAne
  · simp
  have hAB_pos : translativeCoveringNumber A B ≠ 0 :=
    (one_le_translativeCoveringNumber hAne).trans_lt' (by decide) |>.ne'
  have hBT_pos : translativeCoveringNumber B T ≠ 0 :=
    (one_le_translativeCoveringNumber hB).trans_lt' (by decide) |>.ne'
  by_cases hAB : translativeCoveringNumber A B = ⊤
  · rw [hAB, ENat.top_mul hBT_pos]; exact le_top
  by_cases hBT : translativeCoveringNumber B T = ⊤
  · rw [hBT, ENat.mul_top hAB_pos]; exact le_top
  obtain ⟨C₁, hC₁, hc₁⟩ := exists_isTranslativeCover_encard_eq hAB
  obtain ⟨C₂, hC₂, hc₂⟩ := exists_isTranslativeCover_encard_eq hBT
  have hcov : IsTranslativeCover A T (C₁ + C₂) := by
    intro a ha
    rcases Set.mem_add.mp (hC₁ ha) with ⟨c₁, hc₁m, b, hb, rfl⟩
    rcases Set.mem_add.mp (hC₂ hb) with ⟨c₂, hc₂m, t, ht, rfl⟩
    exact ⟨c₁ + c₂, Set.add_mem_add hc₁m hc₂m, t, ht, add_assoc c₁ c₂ t⟩
  have hadd_eq : C₁ + C₂ = (fun p : G × G => p.1 + p.2) '' (C₁ ×ˢ C₂) := by
    ext z
    simp only [Set.mem_add, Set.mem_image, Set.mem_prod, Prod.exists]
    exact ⟨fun ⟨a, ha, b, hb, h⟩ => ⟨a, b, ⟨ha, hb⟩, h⟩,
      fun ⟨a, b, ⟨ha, hb⟩, h⟩ => ⟨a, ha, b, hb, h⟩⟩
  have hcard : (C₁ + C₂).encard ≤ C₁.encard * C₂.encard := by
    rw [hadd_eq]
    exact (Set.encard_image_le _ _).trans_eq Set.encard_prod
  exact (translativeCoveringNumber_le_encard hcov).trans (by rwa [hc₁, hc₂] at hcard)

end TranslativeAlgebra

section TranslativeScaling

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

private lemma translativeCoveringNumber_smul_le {c : ℝ} (hc : c ≠ 0) (A T : Set V) :
    translativeCoveringNumber (c • A) (c • T) ≤ translativeCoveringNumber A T := by
  refine le_translativeCoveringNumber_iff.mpr fun C hC => ?_
  have hcov : IsTranslativeCover (c • A) (c • T) (c • C) := by
    rintro _ ⟨a, ha, rfl⟩
    rcases Set.mem_add.mp (hC ha) with ⟨x, hx, t, ht, rfl⟩
    exact ⟨c • x, Set.smul_mem_smul_set hx, c • t, Set.smul_mem_smul_set ht, (smul_add c x t).symm⟩
  have hcard : (c • C).encard = C.encard :=
    (smul_right_injective V hc).encard_image C
  exact hcard ▸ translativeCoveringNumber_le_encard hcov

/-- Scale invariance of translative covering numbers for any nonzero scalar `c`. -/
lemma translativeCoveringNumber_smul {c : ℝ} (hc : c ≠ 0) (A T : Set V) :
    translativeCoveringNumber (c • A) (c • T) = translativeCoveringNumber A T := by
  refine le_antisymm (translativeCoveringNumber_smul_le hc A T) ?_
  have h := translativeCoveringNumber_smul_le (inv_ne_zero hc) (c • A) (c • T)
  simpa [smul_smul, inv_mul_cancel₀ hc] using h

end TranslativeScaling

/-! ### 5. Volumetric Bounds for Translative Covering Numbers -/

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma addHaar_vadd (μ : Measure E) [μ.IsAddHaarMeasure] (x : E) (S : Set E) :
    μ (x +ᵥ S) = μ S := by
  have hpre : x +ᵥ S = (fun y : E => -x + y) ⁻¹' S := by
    ext y
    simp only [Set.mem_vadd_set, mem_preimage, vadd_eq_add]
    exact ⟨fun ⟨s, hs, h⟩ => by rwa [← h, neg_add_cancel_left],
      fun hy => ⟨-x + y, hy, add_neg_cancel_left x y⟩⟩
  rw [hpre, measure_preimage_add]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Volumetric Lower Bound for Translative Covering Number:**
whenever `μ T ≠ 0`, `μ A ≤ N(A, T) * μ T`. -/
theorem measure_le_translativeCoveringNumber_mul (μ : Measure E) [μ.IsAddHaarMeasure]
    (A : Set E) {T : Set E} (hT : μ T ≠ 0) :
    μ A ≤ (translativeCoveringNumber A T : ℝ≥0∞) * μ T := by
  by_cases htop : translativeCoveringNumber A T = ⊤
  · rw [htop, ENat.toENNReal_top, ENNReal.top_mul hT]; exact le_top
  obtain ⟨C, hC, hcard⟩ := exists_isTranslativeCover_encard_eq htop
  have hfin : C.Finite := Set.encard_ne_top_iff.mp (hcard ▸ htop)
  have hsub : A ⊆ ⋃ x ∈ hfin.toFinset, x +ᵥ T := by
    intro a ha
    rcases Set.mem_add.mp (hC ha) with ⟨x, hx, t, ht, rfl⟩
    exact mem_iUnion₂.mpr ⟨x, hfin.mem_toFinset.mpr hx, ⟨t, ht, rfl⟩⟩
  calc
    μ A ≤ μ (⋃ x ∈ hfin.toFinset, x +ᵥ T) := measure_mono hsub
    _ ≤ ∑ x ∈ hfin.toFinset, μ (x +ᵥ T) := measure_biUnion_finset_le _ _
    _ = ∑ _x ∈ hfin.toFinset, μ T := Finset.sum_congr rfl fun x _ => addHaar_vadd μ x T
    _ = (hfin.toFinset.card : ℝ≥0∞) * μ T := by simp
    _ = (translativeCoveringNumber A T : ℝ≥0∞) * μ T := by
          rw [← hcard, hfin.encard_eq_coe_toFinset_card]; simp

/-- **Zorn Packing / Difference-Body Upper Bound (Ball / Artstein-Avidan–Giannopoulos–Milman):**
for any `A ⊆ E` and any nonempty measurable set `B ⊆ E`,
`N(A, B - B) * μ B ≤ μ (A + B)`. -/
theorem translativeCoveringNumber_sub_mul_le (μ : Measure E) [μ.IsAddHaarMeasure]
    (A : Set E) {B : Set E} (hBne : B.Nonempty) (hBm : MeasurableSet B) :
    (translativeCoveringNumber A (B - B) : ℝ≥0∞) * μ B ≤ μ (A + B) := by
  let ℱ : Set (Set E) := {C | C ⊆ A ∧ Set.PairwiseDisjoint C (fun x => x +ᵥ B)}
  have hchain : ∀ c ⊆ ℱ, IsChain (· ⊆ ·) c → ∃ ub ∈ ℱ, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hch
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · exact Set.sUnion_subset fun s hs => (hc hs).1
    · rintro x ⟨s₁, hs₁, hx⟩ y ⟨s₂, hs₂, hy⟩ hxy
      rcases hch.total hs₁ hs₂ with h12 | h21
      · exact (hc hs₂).2 (h12 hx) hy hxy
      · exact (hc hs₁).2 hx (h21 hy) hxy
  obtain ⟨C, hCmem, hCmax⟩ := zorn_subset ℱ hchain
  -- Maximality implies `C` covers `A` by translates of `B - B`.
  have hcov : IsTranslativeCover A (B - B) C := by
    intro a ha
    by_cases haC : a ∈ C
    · obtain ⟨b, hb⟩ := hBne
      exact ⟨a, haC, 0, ⟨b, hb, b, hb, sub_self b⟩, add_zero a⟩
    · have hnot : ¬ (insert a C ∈ ℱ) := fun hins =>
        haC (hCmax hins (Set.subset_insert a C) (Set.mem_insert a C))
      have hnot_disj : ¬ Set.PairwiseDisjoint (insert a C) (fun x => x +ᵥ B) := fun hpd =>
        hnot ⟨Set.insert_subset ha hCmem.1, hpd⟩
      have hex : ∃ x ∈ C, ¬ Disjoint (a +ᵥ B) (x +ᵥ B) := by
        by_contra hnone
        push Not at hnone
        apply hnot_disj
        rintro x (rfl | hx) y (rfl | hy) hxy
        · exact (hxy rfl).elim
        · exact hnone y hy
        · exact (hnone x hx).symm
        · exact hCmem.2 hx hy hxy
      obtain ⟨x, hxC, hnd⟩ := hex
      rw [Set.not_disjoint_iff] at hnd
      rcases hnd with ⟨z, ⟨b₁, hb₁, hz₁⟩, ⟨b₂, hb₂, hz₂⟩⟩
      refine ⟨x, hxC, b₂ - b₁, Set.sub_mem_sub hb₂ hb₁, ?_⟩
      change a + b₁ = z at hz₁
      change x + b₂ = z at hz₂
      rw [← hz₁] at hz₂
      calc
        x + (b₂ - b₁) = (x + b₂) - b₁ := (add_sub_assoc x b₂ b₁).symm
        _ = (a + b₁) - b₁ := by rw [hz₂]
        _ = a := add_sub_cancel_right a b₁
  -- Every finite subset `F ⊆ C` satisfies `F.card * μ B ≤ μ (A + B)`.
  have hfin_bound : ∀ F : Finset E, (F : Set E) ⊆ C → (F.card : ℝ≥0∞) * μ B ≤ μ (A + B) := by
    intro F hFC
    have hdisj : Set.PairwiseDisjoint (F : Set E) (fun x => x +ᵥ B) := hCmem.2.subset hFC
    have hmeas : ∀ x ∈ F, MeasurableSet (x +ᵥ B) := fun x _ => by
      have hpre : x +ᵥ B = (fun y : E => -x + y) ⁻¹' B := by
        ext y; simp only [Set.mem_vadd_set, mem_preimage, vadd_eq_add]
        exact ⟨fun ⟨s, hs, h⟩ => by rwa [← h, neg_add_cancel_left],
          fun hy => ⟨-x + y, hy, add_neg_cancel_left x y⟩⟩
      rw [hpre]
      exact (measurable_const.add measurable_id) hBm
    have hsub : (⋃ x ∈ F, x +ᵥ B) ⊆ A + B := by
      intro z hz
      rcases mem_iUnion₂.mp hz with ⟨x, hxF, b, hb, rfl⟩
      exact Set.add_mem_add (hCmem.1 (hFC hxF)) hb
    calc
      (F.card : ℝ≥0∞) * μ B = ∑ _x ∈ F, μ B := by simp
      _ = ∑ x ∈ F, μ (x +ᵥ B) := Finset.sum_congr rfl fun x _ => (addHaar_vadd μ x B).symm
      _ = μ (⋃ x ∈ F, x +ᵥ B) := (measure_biUnion_finset hdisj hmeas).symm
      _ ≤ μ (A + B) := measure_mono hsub
  have hC_bound : (C.encard : ℝ≥0∞) * μ B ≤ μ (A + B) := by
    by_cases hfin : C.Finite
    · rw [hfin.encard_eq_coe_toFinset_card]
      simpa using hfin_bound hfin.toFinset (by simp)
    · rw [Set.Infinite.encard_eq hfin, ENat.toENNReal_top]
      by_cases hB0 : μ B = 0
      · simp [hB0]
      by_cases hBtop : μ B = ⊤
      · obtain ⟨x, hxC⟩ := Set.Infinite.nonempty hfin
        have hsub : x +ᵥ B ⊆ A + B := by
          rintro _ ⟨b, hb, rfl⟩; exact Set.add_mem_add (hCmem.1 hxC) hb
        have htop : μ (A + B) = ⊤ :=
          top_unique (by rw [← hBtop, ← addHaar_vadd μ x B]; exact measure_mono hsub)
        rw [htop]; exact le_top
      rw [ENNReal.top_mul hB0, top_le_iff]
      by_contra hne_top
      obtain ⟨n, hn⟩ := exists_nat_gt ((μ (A + B)).toReal / (μ B).toReal)
      obtain ⟨F, hFC, hFcard⟩ := Set.Infinite.exists_subset_card_eq hfin n
      have hle := hfin_bound F hFC
      rw [hFcard] at hle
      have hle_real := ENNReal.toReal_mono hne_top hle
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hle_real
      have hBpos : 0 < (μ B).toReal := ENNReal.toReal_pos hB0 hBtop
      have hlt_real : (μ (A + B)).toReal < (n : ℝ) * (μ B).toReal :=
        (div_lt_iff₀ hBpos).mp hn
      linarith
  exact (mul_le_mul_left (by exact_mod_cast translativeCoveringNumber_le_encard hcov) (μ B)).trans
    hC_bound

/-- **Homothet Covering Bound for Origin-Symmetric Convex Sets:**
for a measurable convex origin-symmetric set `K ⊆ E` with `0 < μ K < ∞` and any `t > 0`,
`N(K, t • K) ≤ (2 / t + 1) ^ finrank ℝ E`. -/
theorem translativeCoveringNumber_symm_smul_le (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hKconv : Convex ℝ K) (hKsymm : ∀ x ∈ K, -x ∈ K)
    (hKm : MeasurableSet K) (hK0 : μ K ≠ 0) (hKtop : μ K ≠ ⊤) {t : ℝ} (ht : 0 < t) :
    (translativeCoveringNumber K (t • K) : ℝ≥0∞) ≤
      ENNReal.ofReal ((2 / t + 1) ^ Module.finrank ℝ E) := by
  set d := Module.finrank ℝ E
  have hKne : K.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    exact hK0 (by simp [hemp])
  have hhalf_pos : 0 < t / 2 := half_pos ht
  let B : Set E := (t / 2 : ℝ) • K
  have hBne : B.Nonempty := hKne.smul_set
  have hBm : MeasurableSet B := by
    have hpre : B = (fun y : E => (t / 2 : ℝ)⁻¹ • y) ⁻¹' K := by
      ext y; simp only [B, Set.mem_smul_set, mem_preimage]
      exact ⟨fun ⟨x, hx, h⟩ => by rw [← h, smul_smul, inv_mul_cancel₀ hhalf_pos.ne', one_smul]; exact hx,
        fun hy => ⟨(t / 2 : ℝ)⁻¹ • y, hy, by rw [smul_smul, mul_inv_cancel₀ hhalf_pos.ne', one_smul]⟩⟩
    rw [hpre]
    exact (measurable_const.smul measurable_id) hKm
  have hdiff_sub : B - B ⊆ t • K := by
    rintro z ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (-y),
      hKconv hx (hKsymm y hy) (by norm_num) (by norm_num) (by norm_num), ?_⟩
    dsimp only
    rw [smul_add, smul_smul, smul_smul, smul_neg, sub_eq_add_neg]
    ring_nf
  have hadd_sub : K + B ⊆ (1 + t / 2) • K := by
    rintro z ⟨x, hx, _, ⟨y, hy, rfl⟩, rfl⟩
    have hc : 0 < 1 + t / 2 := by linarith
    refine ⟨(1 / (1 + t / 2)) • x + ((t / 2) / (1 + t / 2)) • y,
      hKconv hx hy (by positivity) (by positivity) (by field_simp [hc.ne']), ?_⟩
    dsimp only
    rw [smul_add, smul_smul, smul_smul]
    congr 1
    · rw [mul_one_div_cancel hc.ne', one_smul]
    · congr 1; field_simp [hc.ne']
  have hpack := translativeCoveringNumber_sub_mul_le μ K hBne hBm
  have h1 : (translativeCoveringNumber K (t • K) : ℝ≥0∞) * μ B ≤ μ ((1 + t / 2) • K) := by
    calc
      (translativeCoveringNumber K (t • K) : ℝ≥0∞) * μ B
        ≤ (translativeCoveringNumber K (B - B) : ℝ≥0∞) * μ B := by
          gcongr
          exact translativeCoveringNumber_antitone_right hdiff_sub
      _ ≤ μ (K + B) := hpack
      _ ≤ μ ((1 + t / 2) • K) := measure_mono hadd_sub
  have hBvol : μ B = ENNReal.ofReal ((t / 2) ^ d) * μ K := by
    rw [Measure.addHaar_smul, abs_of_nonneg (pow_nonneg hhalf_pos.le _)]
  have haddvol : μ ((1 + t / 2) • K) =
      ENNReal.ofReal ((2 / t + 1) ^ d) * μ B := by
    have hfac : (1 + t / 2) ^ d = (2 / t + 1) ^ d * (t / 2) ^ d := by
      rw [← mul_pow]; congr 1; field_simp [ht.ne']
    rw [Measure.addHaar_smul, abs_of_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ 1 + t / 2) _),
      hfac, ENNReal.ofReal_mul (by positivity), mul_assoc, ← hBvol]
  rw [haddvol] at h1
  have hB0 : μ B ≠ 0 := by
    rw [hBvol]
    exact mul_ne_zero (ENNReal.ofReal_pos.mpr (pow_pos hhalf_pos d)).ne' hK0
  have hBtop : μ B ≠ ⊤ := by
    rw [hBvol]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKtop
  exact ennreal_le_of_mul_le_mul_right hB0 hBtop h1

end

end ConvexGeom
