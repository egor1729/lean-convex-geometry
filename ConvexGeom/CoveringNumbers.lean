module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Volumetric Bounds for Covering and Packing Numbers

This file proves the classical volumetric bounds for covering and packing numbers in any
finite-dimensional real normed space `E` equipped with an additive Haar measure `μ`
(Vershynin, *High-Dimensional Probability*, Proposition 4.2.12 & Corollary 4.2.13;
Ball, *An Elementary Introduction to Modern Convex Geometry*, Lecture 2):

1. **General Volumetric Lower Bound (`measure_le_externalCoveringNumber_mul_closedBall`):**
   For `0 < ε`,
   $$\mu(A) \le \mathcal{N}_{\mathrm{ext}}(A, \varepsilon) \cdot \mu(\overline{B}(0, \varepsilon)).$$
2. **General Volumetric Upper Bound (`packingNumber_mul_ball_le_measure_add_ball`):**
   $$\mathcal{P}(A, \varepsilon) \cdot \mu(B(0, \varepsilon / 2)) \le \mu(A + B(0, \varepsilon / 2)),$$
   and hence by `Metric.coveringNumber_le_packingNumber`:
   $$\mathcal{N}(A, \varepsilon) \cdot \mu(B(0, \varepsilon / 2)) \le \mu(A + B(0, \varepsilon / 2)).$$
3. **Covering and Packing Numbers of the Unit Ball (for ANY norm on $\mathbb{R}^d$):**
   For `0 < ε` and `d = Module.finrank ℝ E`:
   - `inv_pow_le_externalCoveringNumber_closedBall`: $(1 / \varepsilon)^d \le \mathcal{N}_{\mathrm{ext}}(B, \varepsilon)$
   - `packingNumber_closedBall_le`: $\mathcal{P}(B, \varepsilon) \le (2 / \varepsilon + 1)^d$
   - `coveringNumber_closedBall_le`: $\mathcal{N}(B, \varepsilon) \le (2 / \varepsilon + 1)^d$
   - `coveringNumber_closedBall_le_three_div`: for $0 < \varepsilon \le 1$, $\mathcal{N}(B, \varepsilon) \le (3 / \varepsilon)^d$.
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

end

end ConvexGeom
