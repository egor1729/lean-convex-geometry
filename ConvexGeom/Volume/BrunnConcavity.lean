module

public import ConvexGeom.Volume.BrunnMinkowski
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import ConvexGeom.Volume.Continuity
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Brunn's Concavity Principle, Log-Concave Convolutions, and Rogers–Shephard

This file develops classical volumetric consequences of Brunn–Minkowski and Prékopa–Leindler
(Rogers–Shephard, *The difference body of a convex body*, Arch. Math. 8 (1957), 220–233;
Ball, *An Elementary Introduction to Modern Convex Geometry*, Lecture 5; Klartag, Lectures 1–2;
Artstein-Avidan–Giannopoulos–Milman, *Asymptotic Geometric Analysis I*, Ch. 1–2;
Schneider, *Convex Bodies*, §7.1 & §10.1):

1. **Brunn's Concavity Principle for Parallel Sections:**
   For a compact convex set `K ⊆ ℝ × E` (`d = finrank ℝ E`), the slice volume
   `t ↦ volume {y : E | (t, y) ∈ K}` is log-concave (`logConcave_sections`), and for `d ≥ 1`,
   `t ↦ volume {y : E | (t, y) ∈ K} ^ (1 / d : ℝ)` is concave on the projection of `K`
   (`brunn_concavity_sections`, `concaveOn_volume_slice_rpow`).
2. **Log-Concavity of Convolutions (`logConcave_convolution`):**
   If `f, g : E → ℝ≥0∞` are measurable log-concave, then `(f ⋆ g)(z) = ∫⁻ x, f x * g (z - x)`
   is log-concave.
3. **Covariogram (`covariogram`) & Difference Body (`covariogram_lintegral`,
   `covariogram_rpow_concave`):**
   `covariogram μ K x := μ {y | y ∈ K ∧ y - x ∈ K}` satisfies
   `∫⁻ x, covariogram volume K x = volume K * volume K`, is even, supported on `K - K`,
   and has a concave `1 / d`-th root on `K - K`.
4. **Rogers–Shephard Inequality (`rogers_shephard`) and Lower Bound (`two_pow_mul_volume_le_volume_diff`):**
   For every compact convex `K ⊆ E` in dimension `d = finrank ℝ E`:
   $$2^d\,\mathrm{vol}(K) \le \mathrm{vol}(K - K) \le \binom{2d}{d}\,\mathrm{vol}(K).$$
-/

open MeasureTheory Set
open scoped ENNReal NNReal Pointwise

namespace ConvexGeom

public section

/-! ### 1. Brunn's Concavity Principle for Parallel Hyperplane Sections -/

section Sections

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The parallel slice `{y : E | (t, y) ∈ K}` of `K ⊆ ℝ × E` at height `t : ℝ`. -/
@[expose]
def slice (K : Set (ℝ × E)) (t : ℝ) : Set E :=
  {y : E | (t, y) ∈ K}

omit [MeasurableSpace E] [BorelSpace E] in
lemma isCompact_slice {K : Set (ℝ × E)} (hKc : IsCompact K) (t : ℝ) :
    IsCompact (slice K t) := by
  have hclosed : IsClosed (slice K t) :=
    hKc.isClosed.preimage (continuous_const.prodMk continuous_id)
  have hbdd : Bornology.IsBounded (slice K t) := by
    obtain ⟨R, hKR⟩ := hKc.isBounded.subset_closedBall (0 : ℝ × E)
    refine (Metric.isBounded_iff_subset_closedBall (0 : E)).mpr ⟨R, fun y hy => ?_⟩
    have hmem : (t, y) ∈ Metric.closedBall (0 : ℝ × E) R := hKR hy
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at hmem
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (le_max_right _ _).trans hmem
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbdd

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma smul_slice_add_smul_slice_subset {K : Set (ℝ × E)} (hKconv : Convex ℝ K)
    {s t a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • slice K s + b • slice K t ⊆ slice K (a * s + b * t) := by
  intro z hz
  rcases Set.mem_add.mp hz with ⟨_, ⟨y₁, hy₁, rfl⟩, _, ⟨y₂, hy₂, rfl⟩, rfl⟩
  have hmem := hKconv hy₁ hy₂ ha hb hab
  simpa [slice, Prod.smul_mk, Prod.mk_add_mk] using hmem

/-- **Log-concavity of parallel sections:** for compact convex `K ⊆ ℝ × E` and `θ ∈ (0, 1)`,
`volume (slice K s) ^ (1 - θ) * volume (slice K t) ^ θ ≤ volume (slice K ((1 - θ) * s + θ * t))`. -/
theorem logConcave_sections {K : Set (ℝ × E)} (hKconv : Convex ℝ K) (hKc : IsCompact K)
    (s t : ℝ) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    volume (slice K s) ^ (1 - θ) * volume (slice K t) ^ θ ≤
      volume (slice K ((1 - θ) * s + θ * t)) :=
  (brunn_minkowski_mul_compact (isCompact_slice hKc s) (isCompact_slice hKc t) hθ0 hθ1).trans
    (measure_mono (smul_slice_add_smul_slice_subset hKconv (sub_pos.mpr hθ1).le hθ0.le
      (sub_add_cancel 1 θ)))

/-- **Brunn's Concavity Principle (`ℝ≥0∞` form):**
for compact convex `K ⊆ ℝ × E` (`d = finrank ℝ E ≥ 1`), whenever `slice K s` and `slice K t` are
nonempty and `a, b ≥ 0` with `a + b = 1`:
`a * volume (slice K s) ^ (1 / d) + b * volume (slice K t) ^ (1 / d) ≤ volume (slice K (a*s + b*t)) ^ (1 / d)`. -/
theorem brunn_concavity_sections [Nontrivial E]
    {K : Set (ℝ × E)} (hKconv : Convex ℝ K) (hKc : IsCompact K)
    {s t : ℝ} (hs : (slice K s).Nonempty) (ht : (slice K t).Nonempty)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ENNReal.ofReal a * volume (slice K s) ^ (1 / (Module.finrank ℝ E : ℝ)) +
        ENNReal.ofReal b * volume (slice K t) ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
      volume (slice K (a * s + b * t)) ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  have hd_pos : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  have hinv_pos : (0 : ℝ) < 1 / (Module.finrank ℝ E : ℝ) := one_div_pos.mpr hd_pos
  have hbm := brunn_minkowski_compact ((isCompact_slice hKc s).smul a) hs.smul_set
    ((isCompact_slice hKc t).smul b) ht.smul_set
  rw [addHaar_smul_rpow_inv_finrank volume ha, addHaar_smul_rpow_inv_finrank volume hb] at hbm
  exact hbm.trans (ENNReal.rpow_le_rpow
    (measure_mono (smul_slice_add_smul_slice_subset hKconv ha hb hab)) hinv_pos.le)

/-- **Brunn's Concavity Principle (`ConcaveOn ℝ` form):**
`t ↦ (volume (slice K t)).toReal ^ (1 / d)` is concave on `{t : ℝ | (slice K t).Nonempty}`. -/
theorem concaveOn_volume_slice_rpow [Nontrivial E]
    {K : Set (ℝ × E)} (hKconv : Convex ℝ K) (hKc : IsCompact K) :
    ConcaveOn ℝ {t : ℝ | (slice K t).Nonempty}
      (fun t => (volume (slice K t)).toReal ^ (1 / (Module.finrank ℝ E : ℝ))) := by
  set d := Module.finrank ℝ E
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr Module.finrank_pos
  have hinv_pos : (0 : ℝ) < 1 / (d : ℝ) := one_div_pos.mpr hd_pos
  refine ⟨?_, ?_⟩
  · rintro s ⟨y₁, hy₁⟩ t ⟨y₂, hy₂⟩ a b ha hb hab
    exact ⟨a • y₁ + b • y₂, smul_slice_add_smul_slice_subset hKconv ha hb hab
      (Set.add_mem_add (Set.smul_mem_smul_set hy₁) (Set.smul_mem_smul_set hy₂))⟩
  · intro s hs t ht a b ha hb hab
    have hbrunn := brunn_concavity_sections hKconv hKc hs ht ha hb hab
    have hfin : ∀ u : ℝ, volume (slice K u) ≠ ⊤ := fun u => (isCompact_slice hKc u).measure_lt_top.ne
    have htoReal_rpow : ∀ u : ℝ,
        ENNReal.ofReal ((volume (slice K u)).toReal ^ (1 / (d : ℝ))) =
          volume (slice K u) ^ (1 / (d : ℝ)) := fun u => by
      rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hinv_pos.le,
        ENNReal.ofReal_toReal (hfin u)]
    have hfin_rhs : volume (slice K (a * s + b * t)) ^ (1 / (d : ℝ)) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg hinv_pos.le (hfin _)
    have hmul_eq : ∀ (c : ℝ) (_hc : 0 ≤ c) (u : ℝ),
        ENNReal.ofReal (c * (volume (slice K u)).toReal ^ (1 / (d : ℝ))) =
          ENNReal.ofReal c * volume (slice K u) ^ (1 / (d : ℝ)) := fun c hc u => by
      rw [ENNReal.ofReal_mul hc, htoReal_rpow u]
    rw [← hmul_eq a ha s, ← hmul_eq b hb t,
      ← ENNReal.ofReal_add (mul_nonneg ha (Real.rpow_nonneg ENNReal.toReal_nonneg _))
        (mul_nonneg hb (Real.rpow_nonneg ENNReal.toReal_nonneg _)),
      ← htoReal_rpow (a * s + b * t)] at hbrunn
    simpa [smul_eq_mul] using
      (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg ENNReal.toReal_nonneg _)).mp hbrunn

end Sections

/-! ### 2. Log-Concavity of Convolutions -/

/-- **Log-Concavity of Convolutions:**
if `f, g : E → ℝ≥0∞` are measurable log-concave functions on a finite-dimensional real inner
product space `E`, then their convolution `z ↦ ∫⁻ x, f x * g (z - x)` is also log-concave. -/
theorem logConcave_convolution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f g : E → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hf_log : ∀ x y : E, f x ^ (1 - t) * f y ^ t ≤ f ((1 - t) • x + t • y))
    (hg_log : ∀ x y : E, g x ^ (1 - t) * g y ^ t ≤ g ((1 - t) • x + t • y))
    (z₁ z₂ : E) :
    (∫⁻ x : E, f x * g (z₁ - x)) ^ (1 - t) * (∫⁻ x : E, f x * g (z₂ - x)) ^ t ≤
      ∫⁻ x : E, f x * g (((1 - t) • z₁ + t • z₂) - x) := by
  have h1t : 0 < 1 - t := sub_pos.mpr ht1
  let F : E × E → ℝ≥0∞ := fun p => f p.2 * g (p.1 - p.2)
  have hFm : Measurable F := (hf.comp measurable_snd).mul (hg.comp (measurable_fst.sub measurable_snd))
  refine logConcave_marginal_prod hFm ht0 ht1 (fun u₁ u₂ x₁ x₂ => ?_) z₁ z₂
  dsimp only [F]
  have hsub : (1 - t) • (u₁ - x₁) + t • (u₂ - x₂) =
      ((1 - t) • u₁ + t • u₂) - ((1 - t) • x₁ + t • x₂) := by
    rw [smul_sub, smul_sub]; abel
  calc
    (f x₁ * g (u₁ - x₁)) ^ (1 - t) * (f x₂ * g (u₂ - x₂)) ^ t
      = (f x₁ ^ (1 - t) * f x₂ ^ t) * (g (u₁ - x₁) ^ (1 - t) * g (u₂ - x₂) ^ t) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ h1t.le, ENNReal.mul_rpow_of_nonneg _ _ ht0.le]
        ring
    _ ≤ f ((1 - t) • x₁ + t • x₂) * g ((1 - t) • (u₁ - x₁) + t • (u₂ - x₂)) :=
        mul_le_mul' (hf_log x₁ x₂) (hg_log (u₁ - x₁) (u₂ - x₂))
    _ = f ((1 - t) • x₁ + t • x₂) *
          g (((1 - t) • u₁ + t • u₂) - ((1 - t) • x₁ + t • x₂)) := by rw [hsub]

/-! ### 3. Covariogram and Elementary Beta Integral -/

/-- Elementary real Beta integral for natural exponents:
`∫ s in (0 : ℝ)..1, s ^ a * (1 - s) ^ b = a! * b! / (a + b + 1)!`. -/
theorem integral_pow_mul_one_sub_pow : ∀ (b a : ℕ),
    ∫ s in (0 : ℝ)..1, s ^ a * (1 - s) ^ b =
      (a.factorial : ℝ) * (b.factorial : ℝ) / ((a + b + 1).factorial : ℝ)
  | 0, a => by
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, add_zero,
      integral_pow, one_pow, zero_pow (Nat.succ_ne_zero a), sub_zero]
    rw [Nat.factorial_succ, Nat.cast_mul]
    have hfac : (a.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)
    push_cast
    field_simp [hfac]
  | b + 1, a => by
    have ha1 : (a : ℝ) + 1 ≠ 0 := by positivity
    let u : ℝ → ℝ := fun s => (1 - s) ^ (b + 1)
    let u' : ℝ → ℝ := fun s => -((b + 1 : ℝ) * (1 - s) ^ b)
    let v : ℝ → ℝ := fun s => s ^ (a + 1) / ((a : ℝ) + 1)
    let v' : ℝ → ℝ := fun s => s ^ a
    have hu : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt u (u' s) s := fun s _ => by
      have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) s := (hasDerivAt_id s).const_sub 1
      have h2 := h1.pow (b + 1)
      convert h2 using 1
      dsimp only [u']
      push_cast; ring
    have hv : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt v (v' s) s := fun s _ => by
      have h1 := (hasDerivAt_pow (a + 1) s).div_const ((a : ℝ) + 1)
      convert h1 using 1
      dsimp only [v']
      push_cast
      field_simp [ha1]
    have hu'_int : IntervalIntegrable u' volume 0 1 :=
      (Continuous.intervalIntegrable (by fun_prop) 0 1)
    have hv'_int : IntervalIntegrable v' volume 0 1 :=
      (Continuous.intervalIntegrable (by fun_prop) 0 1)
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu'_int hv'_int
    have hbdry : u 1 * v 1 - u 0 * v 0 = 0 := by
      simp [u, v, zero_pow (Nat.succ_ne_zero b), zero_pow (Nat.succ_ne_zero a)]
    have hlhs : ∫ s in (0 : ℝ)..1, s ^ a * (1 - s) ^ (b + 1) =
        ∫ s in (0 : ℝ)..1, u s * v' s := by
      refine intervalIntegral.integral_congr fun s _ => ?_
      dsimp only [u, v']; ring
    have hrhs : ∫ s in (0 : ℝ)..1, u' s * v s =
        -(((b + 1 : ℝ) / ((a : ℝ) + 1)) * ∫ s in (0 : ℝ)..1, s ^ (a + 1) * (1 - s) ^ b) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun s _ => ?_
      dsimp only [u', v]; ring
    rw [hlhs, hibp, hbdry, zero_sub, hrhs, neg_neg, integral_pow_mul_one_sub_pow b (a + 1)]
    have hidx : a + 1 + b + 1 = a + (b + 1) + 1 := by omega
    rw [hidx, Nat.factorial_succ a, Nat.factorial_succ b]
    push_cast
    field_simp [ha1]

/-- The Rogers–Shephard Beta weight integral:
for `d ≥ 1`, `∫ s in (0 : ℝ)..1, d * s ^ (d - 1) * (1 - s) ^ d = 1 / Nat.choose (2 * d) d`. -/
theorem integral_rogers_shephard_weight {d : ℕ} (hd : 1 ≤ d) :
    ∫ s in (0 : ℝ)..1, (d : ℝ) * s ^ (d - 1) * (1 - s) ^ d =
      1 / ((Nat.choose (2 * d) d : ℕ) : ℝ) := by
  have heq : (fun s : ℝ => (d : ℝ) * s ^ (d - 1) * (1 - s) ^ d) =
      fun s : ℝ => (d : ℝ) * (s ^ (d - 1) * (1 - s) ^ d) := by ext s; ring
  rw [heq, intervalIntegral.integral_const_mul, integral_pow_mul_one_sub_pow d (d - 1)]
  have hsum : d - 1 + d + 1 = 2 * d := by omega
  have hchoose := Nat.choose_mul_factorial_mul_factorial (show d ≤ 2 * d by omega)
  have h2d : 2 * d - d = d := by omega
  rw [h2d] at hchoose
  have hfac_d : (d : ℝ) * ((d - 1).factorial : ℝ) = (d.factorial : ℝ) := by
    exact_mod_cast Nat.mul_factorial_pred (by omega : d ≠ 0)
  have hchoose_r : ((Nat.choose (2 * d) d : ℕ) : ℝ) * (d.factorial : ℝ) * (d.factorial : ℝ) =
      ((2 * d).factorial : ℝ) := by exact_mod_cast hchoose
  have hfd_ne : (d.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  have hc_ne : ((Nat.choose (2 * d) d : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega : d ≤ 2 * d)).ne'
  rw [hsum, ← hchoose_r]
  calc
    (d : ℝ) * (((d - 1).factorial : ℝ) * (d.factorial : ℝ) /
        (((Nat.choose (2 * d) d : ℕ) : ℝ) * (d.factorial : ℝ) * (d.factorial : ℝ)))
      = ((d : ℝ) * ((d - 1).factorial : ℝ)) * (d.factorial : ℝ) /
        (((Nat.choose (2 * d) d : ℕ) : ℝ) * (d.factorial : ℝ) * (d.factorial : ℝ)) := by ring
    _ = (d.factorial : ℝ) * (d.factorial : ℝ) /
        (((Nat.choose (2 * d) d : ℕ) : ℝ) * (d.factorial : ℝ) * (d.factorial : ℝ)) := by
        rw [hfac_d]
    _ = 1 / ((Nat.choose (2 * d) d : ℕ) : ℝ) := by
        field_simp [hfd_ne, hc_ne]

section CovariogramBasic

variable {E : Type*} [AddCommGroup E] [MeasurableSpace E]

/-- The **covariogram** of `K ⊆ E` with respect to a measure `μ`:
`covariogram μ K x := μ {y : E | y ∈ K ∧ y - x ∈ K} = μ (K ∩ (x + K))`. -/
@[expose]
noncomputable def covariogram (μ : Measure E) (K : Set E) (x : E) : ℝ≥0∞ :=
  μ {y : E | y ∈ K ∧ y - x ∈ K}

@[simp]
lemma covariogram_zero (μ : Measure E) (K : Set E) :
    covariogram μ K 0 = μ K := by
  simp [covariogram]

lemma covariogram_le_self (μ : Measure E) (K : Set E) (x : E) :
    covariogram μ K x ≤ μ K :=
  measure_mono fun _ hy => hy.1

lemma covariogram_eq_zero_of_notMem_sub (μ : Measure E) {K : Set E} {x : E} (hx : x ∉ K - K) :
    covariogram μ K x = 0 := by
  have hemp : {y : E | y ∈ K ∧ y - x ∈ K} = ∅ := by
    ext y
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro hy hyx
    exact hx ⟨y, hy, y - x, hyx, sub_sub_cancel y x⟩
  simp [covariogram, hemp]

end CovariogramBasic

lemma covariogram_neg {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (K : Set E) (x : E) :
    covariogram μ K (-x) = covariogram μ K x := by
  unfold covariogram
  have hpre : {y : E | y ∈ K ∧ y - -x ∈ K} =
      (fun y : E => x + y) ⁻¹' {z : E | z ∈ K ∧ z - x ∈ K} := by
    ext y
    simp only [mem_ofPred_eq, mem_preimage, sub_neg_eq_add, add_sub_cancel_left]
    rw [add_comm y x, and_comm]
  rw [hpre, measure_preimage_add]

section CovariogramAndRogersShephard

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Covariogram integral identity:**
for any measurable set `K ⊆ E`, `∫⁻ x, covariogram volume K x = volume K * volume K`. -/
theorem covariogram_lintegral {K : Set E} (hKm : MeasurableSet K) :
    ∫⁻ x : E, covariogram volume K x = volume K * volume K := by
  let S : Set (E × E) := {p : E × E | p.2 ∈ K ∧ p.2 - p.1 ∈ K}
  have hSm : MeasurableSet S :=
    (measurable_snd hKm).inter ((measurable_snd.sub measurable_fst) hKm)
  have hslice_x : ∀ x : E,
      covariogram volume K x = ∫⁻ y : E, S.indicator 1 (x, y) := fun x => by
    unfold covariogram
    have heq : (fun y : E => S.indicator (1 : E × E → ℝ≥0∞) (x, y)) =
        {y : E | y ∈ K ∧ y - x ∈ K}.indicator 1 := by
      ext y; by_cases hy : y ∈ K ∧ y - x ∈ K <;> simp [S, hy]
    have hxm : MeasurableSet {y : E | y ∈ K ∧ y - x ∈ K} :=
      hKm.inter ((measurable_id.sub measurable_const) hKm)
    rw [heq, lintegral_indicator_one hxm]
  simp_rw [hslice_x]
  rw [lintegral_lintegral_swap (f := fun x y => S.indicator (1 : E × E → ℝ≥0∞) (x, y))
    (measurable_const.indicator hSm).aemeasurable]
  have hslice_y : ∀ y : E, ∫⁻ x : E, S.indicator 1 (x, y) = K.indicator (fun _ => volume K) y := by
    intro y
    by_cases hy : y ∈ K
    · have heq : (fun x : E => S.indicator (1 : E × E → ℝ≥0∞) (x, y)) =
          {x : E | y - x ∈ K}.indicator 1 := by
        ext x; by_cases hx : y - x ∈ K <;> simp [S, hy, hx]
      have hym : MeasurableSet {x : E | y - x ∈ K} := (measurable_const.sub measurable_id) hKm
      rw [heq, lintegral_indicator_one hym, indicator_of_mem hy]
      have hpre : {x : E | y - x ∈ K} = (fun x => -y + x) ⁻¹' ((-1 : ℝ) • K) := by
        ext x; simp only [mem_ofPred_eq, mem_preimage, Set.mem_smul_set]
        constructor
        · intro hx
          refine ⟨y - x, hx, ?_⟩
          rw [neg_smul, one_smul]; abel
        · rintro ⟨z, hz, hzx⟩
          rw [neg_smul, one_smul] at hzx
          have : y - x = z := by
            have := congrArg (fun w => -w) hzx
            simpa [sub_eq_add_neg, add_comm] using this.symm
          rwa [this]
      rw [hpre, measure_preimage_add, Measure.addHaar_smul]
      simp
    · have heq : ∀ x : E, S.indicator (1 : E × E → ℝ≥0∞) (x, y) = 0 := fun x => by
        simp [S, hy]
      simp [heq, hy]
  simp_rw [hslice_y]
  rw [lintegral_indicator hKm, lintegral_const, Measure.restrict_apply_univ, mul_comm]

/-- **Concavity of the `1 / d`-th root of the covariogram:**
for compact convex `K ⊆ E` (`d = finrank ℝ E ≥ 1`) and `x₁, x₂ ∈ K - K`,
`a * g(x₁)^(1/d) + b * g(x₂)^(1/d) ≤ g(a • x₁ + b • x₂)^(1/d)`. -/
theorem covariogram_rpow_concave [Nontrivial E]
    {K : Set E} (hKconv : Convex ℝ K) (hKc : IsCompact K)
    {x₁ x₂ : E} (hx₁ : x₁ ∈ K - K) (hx₂ : x₂ ∈ K - K)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ENNReal.ofReal a * covariogram volume K x₁ ^ (1 / (Module.finrank ℝ E : ℝ)) +
        ENNReal.ofReal b * covariogram volume K x₂ ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
      covariogram volume K (a • x₁ + b • x₂) ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  have hd_pos : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  have hinv_pos : (0 : ℝ) < 1 / (Module.finrank ℝ E : ℝ) := one_div_pos.mpr hd_pos
  let S : E → Set E := fun x => {y : E | y ∈ K ∧ y - x ∈ K}
  have hSc : ∀ x, IsCompact (S x) := fun x =>
    hKc.inter_right (hKc.isClosed.preimage (continuous_id.sub continuous_const))
  have hSne : ∀ x ∈ K - K, (S x).Nonempty := by
    intro x hx
    rcases Set.mem_sub.mp hx with ⟨u, hu, v, hv, rfl⟩
    exact ⟨u, hu, by simpa using hv⟩
  have hsub : a • S x₁ + b • S x₂ ⊆ S (a • x₁ + b • x₂) := by
    intro z hz
    rcases Set.mem_add.mp hz with ⟨_, ⟨y₁, ⟨hy₁K, hy₁x⟩, rfl⟩, _, ⟨y₂, ⟨hy₂K, hy₂x⟩, rfl⟩, rfl⟩
    refine ⟨hKconv hy₁K hy₂K ha hb hab, ?_⟩
    have hid : (a • y₁ + b • y₂) - (a • x₁ + b • x₂) = a • (y₁ - x₁) + b • (y₂ - x₂) := by
      rw [smul_sub, smul_sub]; abel
    rw [hid]
    exact hKconv hy₁x hy₂x ha hb hab
  have hbm := brunn_minkowski_compact ((hSc x₁).smul a) (hSne x₁ hx₁).smul_set
    ((hSc x₂).smul b) (hSne x₂ hx₂).smul_set
  rw [addHaar_smul_rpow_inv_finrank volume ha, addHaar_smul_rpow_inv_finrank volume hb] at hbm
  exact hbm.trans (ENNReal.rpow_le_rpow (measure_mono hsub) hinv_pos.le)

/-- Helper: if a convex set `K ⊆ E` has measure `0`, then `K - K` also has measure `0`. -/
private lemma volume_sub_eq_zero_of_volume_eq_zero {K : Set E} (hKconv : Convex ℝ K)
    (hK0 : volume K = 0) : volume (K - K) = 0 := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp
  by_cases htop : affineSpan ℝ K = ⊤
  · -- A nonempty convex set with full affine span has nonempty interior, contradicting `volume K = 0`.
    exfalso
    obtain ⟨y, hy⟩ := hKne.intrinsicInterior hKconv
    rw [mem_intrinsicInterior] at hy
    obtain ⟨⟨y', hy'mem⟩, hy'int, rfl⟩ := hy
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hy'int
    obtain ⟨r, hr, hball⟩ := hy'int
    have hsub : Metric.ball y' r ⊆ K := fun w hw => by
      have hwmem : w ∈ affineSpan ℝ K := htop ▸ trivial
      exact hball (show (⟨w, hwmem⟩ : affineSpan ℝ K) ∈ Metric.ball ⟨y', hy'mem⟩ r from hw)
    have hpos : 0 < volume (Metric.ball y' r) :=
      Metric.isOpen_ball.measure_pos volume ⟨y', Metric.mem_ball_self hr⟩
    exact hpos.ne' (le_antisymm ((measure_mono hsub).trans_eq hK0) zero_le)
  · -- Otherwise `K - K` lies in the proper linear direction `(affineSpan ℝ K).direction ≠ ⊤`.
    have hdir_ne : (affineSpan ℝ K).direction ≠ ⊤ := by
      intro hdir
      apply htop
      obtain ⟨x₀, hx₀⟩ := hKne
      rw [eq_top_iff]
      intro w _
      have hw : w -ᵥ x₀ ∈ (affineSpan ℝ K).direction := hdir ▸ trivial
      have := AffineSubspace.vadd_mem_of_mem_direction hw (subset_affineSpan ℝ K hx₀)
      simpa using this
    have hsub : K - K ⊆ ((affineSpan ℝ K).direction : Set E) := by
      intro z hz
      rcases Set.mem_sub.mp hz with ⟨a, ha, b, hb, rfl⟩
      exact AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ K ha)
        (subset_affineSpan ℝ K hb)
    exact measure_mono_null hsub (Measure.addHaar_submodule volume _ hdir_ne)

/-- **Difference-Body Lower Bound (from Brunn–Minkowski):**
for any compact set `K ⊆ E` in dimension `d = finrank ℝ E`,
`2^d * volume K ≤ volume (K - K)`. -/
theorem two_pow_mul_volume_le_volume_diff {K : Set E} (hKc : IsCompact K) :
    ((2 : ℝ≥0∞) ^ (Module.finrank ℝ E)) * volume K ≤ volume (K - K) := by
  have hneg_vol : volume ((-1 : ℝ) • K) = volume K := by
    rw [Measure.addHaar_smul]; simp
  have hbm := brunn_minkowski_mul_compact hKc (hKc.smul (-1 : ℝ)) (t := (1 / 2 : ℝ))
    (by norm_num) (by norm_num)
  have hhalf : (1 - (1 / 2 : ℝ)) = 1 / 2 := by norm_num
  rw [hhalf, hneg_vol,
    ← ENNReal.rpow_add_of_nonneg (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num),
    show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, ENNReal.rpow_one] at hbm
  have hset : (1 / 2 : ℝ) • K + (1 / 2 : ℝ) • ((-1 : ℝ) • K) = (1 / 2 : ℝ) • (K - K) := by
    rw [← smul_set_add]
    congr 1
    ext z
    simp only [Set.mem_add, Set.mem_sub, Set.mem_smul_set]
    constructor
    · rintro ⟨x, hx, _, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨x, hx, y, hy, by rw [neg_smul, one_smul, sub_eq_add_neg]⟩
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨x, hx, (-1 : ℝ) • y, ⟨y, hy, rfl⟩, by rw [neg_smul, one_smul, sub_eq_add_neg]⟩
  rw [hset, Measure.addHaar_smul, abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) _)] at hbm
  have hmul : ENNReal.ofReal ((2 : ℝ) ^ Module.finrank ℝ E) * volume K ≤
      ENNReal.ofReal ((2 : ℝ) ^ Module.finrank ℝ E) *
        (ENNReal.ofReal ((1 / 2 : ℝ) ^ Module.finrank ℝ E) * volume (K - K)) := by gcongr
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow,
    show (2 : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, one_pow, ENNReal.ofReal_one, one_mul] at hmul
  simpa [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)] using hmul

/-- Helper for Rogers–Shephard: if `s ∈ (0, 1)` and `(1 - s)⁻¹ • x ∈ K - K` for convex `K`, then
a translate of `s • K` fits inside `K ∩ (x + K)`, yielding `s ^ d * volume K ≤ covariogram volume K x`. -/
private lemma rogers_shephard_homothety_volume {K : Set E} (hKconv : Convex ℝ K)
    {x : E} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hmem : (1 - s)⁻¹ • x ∈ K - K) :
    ENNReal.ofReal (s ^ Module.finrank ℝ E) * volume K ≤ covariogram volume K x := by
  rcases Set.mem_sub.mp hmem with ⟨a, ha, b, hb, hab⟩
  have h1s : 0 < 1 - s := sub_pos.mpr hs1
  have hx_eq : x = (1 - s) • (a - b) := by
    have := congrArg (fun v => (1 - s) • v) hab
    simpa [smul_smul, mul_inv_cancel₀ h1s.ne'] using this.symm
  have hhom : (fun z : E => (1 - s) • a + z) '' (s • K) ⊆ {y : E | y ∈ K ∧ y - x ∈ K} := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · dsimp only
      rw [add_comm]
      exact hKconv hz ha hs0.le h1s.le (add_sub_cancel s 1)
    · dsimp only
      have heq : ((1 - s) • a + s • z) - x = s • z + (1 - s) • b := by
        rw [hx_eq, smul_sub]; abel
      rw [heq]
      exact hKconv hz hb hs0.le h1s.le (add_sub_cancel s 1)
  have htrans : volume ((fun z : E => (1 - s) • a + z) '' (s • K)) =
      ENNReal.ofReal (s ^ Module.finrank ℝ E) * volume K := by
    have heq : (fun z : E => (1 - s) • a + z) '' (s • K) =
        (fun z : E => -((1 - s) • a) + z) ⁻¹' (s • K) := by
      ext z; simp only [mem_image, mem_preimage]
      exact ⟨fun ⟨u, hu, huz⟩ => by rwa [← huz, neg_add_cancel_left],
        fun hz => ⟨-((1 - s) • a) + z, hz, by abel⟩⟩
    rw [heq, measure_preimage_add, Measure.addHaar_smul, abs_of_nonneg (pow_nonneg hs0.le _)]
  exact htrans ▸ measure_mono hhom

/-- Helper for Rogers–Shephard: for each `x : E`, the weighted radial integral over
`{s ∈ (0, 1) | (1 - s)⁻¹ • x ∈ K - K}` is bounded by `covariogram volume K x / volume K`. -/
private lemma rogers_shephard_radial_bound {K : Set E} (hKconv : Convex ℝ K)
    (hd : 1 ≤ Module.finrank ℝ E) (hK0 : volume K ≠ 0) (hKfin : volume K ≠ ⊤) (x : E) :
    ∫⁻ s : ℝ, {p : E × ℝ | p.2 ∈ Ioo (0 : ℝ) 1 ∧ (1 - p.2)⁻¹ • p.1 ∈ K - K}.indicator
        (fun p => ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * p.2 ^ (Module.finrank ℝ E - 1)))
        (x, s) ≤
      covariogram volume K x / volume K := by
  set d := Module.finrank ℝ E
  have hd0 : d ≠ 0 := by omega
  have hd_rpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  let S : Set (E × ℝ) := {p : E × ℝ | p.2 ∈ Ioo (0 : ℝ) 1 ∧ (1 - p.2)⁻¹ • p.1 ∈ K - K}
  let w : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal ((d : ℝ) * s ^ (d - 1))
  have hratio_le1 : covariogram volume K x / volume K ≤ 1 := by
    rw [ENNReal.div_le_iff_le_mul (Or.inl hK0) (Or.inl hKfin), one_mul]
    exact covariogram_le_self volume K x
  let c : ℝ := (covariogram volume K x / volume K).toReal
  have hc_nn : 0 ≤ c := ENNReal.toReal_nonneg
  have hc_ofReal : ENNReal.ofReal c = covariogram volume K x / volume K :=
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hratio_le1)
  let r : ℝ := c ^ (1 / (d : ℝ))
  have hr_nn : 0 ≤ r := Real.rpow_nonneg hc_nn _
  have hr_pow : r ^ d = c := by
    dsimp only [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc_nn, one_div_mul_cancel hd_rpos.ne', Real.rpow_one]
  have hsub_s : {s : ℝ | (x, s) ∈ S} ⊆ Ioc (0 : ℝ) r := by
    intro s ⟨⟨hs0, hs1⟩, hmem⟩
    refine ⟨hs0, ?_⟩
    have hvol_hom := rogers_shephard_homothety_volume hKconv hs0 hs1 hmem
    have hsd_le : ENNReal.ofReal (s ^ d) ≤ ENNReal.ofReal c := by
      rw [hc_ofReal, ENNReal.le_div_iff_mul_le (Or.inl hK0) (Or.inl hKfin)]
      exact hvol_hom
    have hsd_le' : s ^ d ≤ r ^ d := by
      rw [hr_pow]
      exact (ENNReal.ofReal_le_ofReal_iff hc_nn).mp hsd_le
    by_contra hlt
    push Not at hlt
    have : r ^ d < s ^ d := pow_lt_pow_left₀ hlt hr_nn hd0
    linarith
  have hpt_le : ∀ s : ℝ, S.indicator (fun p => w p.2) (x, s) ≤ (Ioc (0 : ℝ) r).indicator w s := by
    intro s
    by_cases hs : (x, s) ∈ S
    · rw [indicator_of_mem hs, indicator_of_mem (hsub_s hs)]
    · rw [indicator_of_notMem hs]; exact zero_le
  have hd_sub : ((d - 1 : ℕ) : ℝ) + 1 = d := by exact_mod_cast Nat.sub_add_cancel hd
  calc
    ∫⁻ s : ℝ, S.indicator (fun p => w p.2) (x, s)
      ≤ ∫⁻ s : ℝ, (Ioc (0 : ℝ) r).indicator w s := lintegral_mono hpt_le
    _ = ∫⁻ s in Ioc (0 : ℝ) r, w s := lintegral_indicator measurableSet_Ioc w
    _ = ENNReal.ofReal (∫ s in (0 : ℝ)..r, (d : ℝ) * s ^ (d - 1)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal
          ((Continuous.intervalIntegrable (by fun_prop) 0 r).1)
          (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
              exact mul_nonneg hd_rpos.le (pow_nonneg hs.1.le _)),
          ← intervalIntegral.integral_of_le hr_nn]
    _ = ENNReal.ofReal (r ^ d) := by
        rw [intervalIntegral.integral_const_mul, integral_pow,
          Nat.sub_add_cancel hd, hd_sub, zero_pow hd0, sub_zero,
          mul_div_cancel₀ _ hd_rpos.ne']
    _ = covariogram volume K x / volume K := by rw [hr_pow, hc_ofReal]

/-- **Rogers–Shephard Inequality (1957):**
for every compact convex set `K ⊆ E` in a finite-dimensional real inner product space `E` of
dimension `d = finrank ℝ E`:
$$\mathrm{vol}(K - K) \le \binom{2d}{d}\,\mathrm{vol}(K).$$ -/
theorem rogers_shephard {K : Set E} (hKconv : Convex ℝ K) (hKc : IsCompact K) :
    volume (K - K) ≤ ((Nat.choose (2 * Module.finrank ℝ E) (Module.finrank ℝ E) : ℕ) : ℝ≥0∞) *
      volume K := by
  set d := Module.finrank ℝ E
  by_cases hd0 : d = 0
  · have : Subsingleton E := Module.finrank_zero_iff.mp hd0
    rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
    · simp
    · have hKuniv : K = Set.univ := Set.eq_univ_of_forall fun x => Subsingleton.elim x x₀ ▸ hx₀
      have hSubuniv : K - K = Set.univ := Set.eq_univ_of_forall fun x =>
        ⟨x₀, hx₀, x₀, hx₀, Subsingleton.elim _ _⟩
      rw [hSubuniv, hKuniv]
      simp [hd0]
  have hd_pos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
  have hd_rpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd_pos
  by_cases hK0 : volume K = 0
  · rw [volume_sub_eq_zero_of_volume_eq_zero hKconv hK0, hK0, mul_zero]
  have hKfin : volume K ≠ ⊤ := hKc.measure_lt_top.ne
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hKKc : IsCompact (K - K) := by
    have heq : K - K = K + (-1 : ℝ) • K := by
      ext z; simp only [Set.mem_sub, Set.mem_add, Set.mem_smul_set]
      exact ⟨fun ⟨x, hx, y, hy, h⟩ => ⟨x, hx, -y, ⟨y, hy, by simp⟩, by rw [← h, sub_eq_add_neg]⟩,
        fun ⟨x, hx, _, ⟨y, hy, rfl⟩, h⟩ => ⟨x, hx, y, hy, by rw [← h, neg_smul, one_smul, sub_eq_add_neg]⟩⟩
    rw [heq]
    exact hKc.add (hKc.smul (-1 : ℝ))
  have hKKm : MeasurableSet (K - K) := hKKc.isClosed.measurableSet
  -- Define `S = {(x, s) ∈ E × (0, 1) | (1 - s)⁻¹ • x ∈ K - K}` and weight `w(s) = d * s^(d - 1)`.
  let S : Set (E × ℝ) := {p : E × ℝ | p.2 ∈ Ioo (0 : ℝ) 1 ∧ (1 - p.2)⁻¹ • p.1 ∈ K - K}
  have hSm : MeasurableSet S := by
    have h1 : MeasurableSet {p : E × ℝ | p.2 ∈ Ioo (0 : ℝ) 1} := measurable_snd measurableSet_Ioo
    have h2 : MeasurableSet {p : E × ℝ | (1 - p.2)⁻¹ • p.1 ∈ K - K} :=
      ((measurable_const.sub measurable_snd).inv.smul measurable_fst) hKKm
    exact h1.inter h2
  let w : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal ((d : ℝ) * s ^ (d - 1))
  have hwm : Measurable w :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_id.pow_const _))
  let F : E → ℝ → ℝ≥0∞ := fun x s => S.indicator (fun p => w p.2) (x, s)
  have hFm : Measurable (Function.uncurry F) := (hwm.comp measurable_snd).indicator hSm
  -- Side 1: integrate `x` first, then `s`.
  have hlhs : ∫⁻ s : ℝ, ∫⁻ x : E, F x s =
      volume (K - K) * ENNReal.ofReal (1 / ((Nat.choose (2 * d) d : ℕ) : ℝ)) := by
    have hinner : ∀ s : ℝ, ∫⁻ x : E, F x s =
        (Ioo (0 : ℝ) 1).indicator
          (fun s => volume (K - K) * ENNReal.ofReal ((d : ℝ) * s ^ (d - 1) * (1 - s) ^ d)) s := by
      intro s
      by_cases hs : s ∈ Ioo (0 : ℝ) 1
      · have h1s : 0 < 1 - s := sub_pos.mpr hs.2
        have hslice : {x : E | (x, s) ∈ S} = (1 - s) • (K - K) := by
          ext x
          simp only [S, mem_ofPred_eq, hs, true_and, Set.mem_smul_set]
          constructor
          · intro hx
            exact ⟨(1 - s)⁻¹ • x, hx, by rw [smul_smul, mul_inv_cancel₀ h1s.ne', one_smul]⟩
          · rintro ⟨z, hz, rfl⟩
            rwa [smul_smul, inv_mul_cancel₀ h1s.ne', one_smul]
        have hfun : (fun x : E => F x s) = ((1 - s) • (K - K)).indicator (fun _ => w s) := by
          ext x
          dsimp only [F]
          by_cases hx : (x, s) ∈ S
          · have hx' : x ∈ (1 - s) • (K - K) := hslice ▸ hx
            simp [hx, hx']
          · have hx' : x ∉ (1 - s) • (K - K) := hslice ▸ hx
            simp [hx, hx']
        have hsm : MeasurableSet ((1 - s) • (K - K)) := (hKKc.smul (1 - s)).isClosed.measurableSet
        rw [hfun, lintegral_indicator hsm, lintegral_const, Measure.restrict_apply_univ,
          Measure.addHaar_smul, abs_of_nonneg (pow_nonneg h1s.le _), indicator_of_mem hs]
        dsimp only [w]
        change ENNReal.ofReal ((d : ℝ) * s ^ (d - 1)) *
            (ENNReal.ofReal ((1 - s) ^ d) * volume (K - K)) =
          volume (K - K) * ENNReal.ofReal ((d : ℝ) * s ^ (d - 1) * (1 - s) ^ d)
        rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg hd_rpos.le (pow_nonneg hs.1.le _)),
          mul_comm _ (volume (K - K))]
      · have hfun : ∀ x : E, F x s = 0 := fun x => by
          have hnot : (x, s) ∉ S := fun h => hs h.1
          simp [F, hnot]
        simp [hfun, hs]
    simp_rw [hinner]
    have hmeas_g : Measurable (fun a : ℝ => ENNReal.ofReal ((d : ℝ) * a ^ (d - 1) * (1 - a) ^ d)) :=
      ENNReal.measurable_ofReal.comp
        ((measurable_const.mul (measurable_id.pow_const _)).mul
          ((measurable_const.sub measurable_id).pow_const _))
    rw [lintegral_indicator measurableSet_Ioo, lintegral_const_mul _ hmeas_g]
    congr 1
    rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc,
      ← ofReal_integral_eq_lintegral_ofReal
        ((Continuous.intervalIntegrable (by fun_prop) 0 1).1)
        (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
            exact mul_nonneg (mul_nonneg hd_rpos.le (pow_nonneg hs.1.le _))
              (pow_nonneg (sub_nonneg.mpr hs.2) _)),
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_rogers_shephard_weight hd_pos]
  -- Side 2: integrate `s` first, then `x`, using `rogers_shephard_radial_bound`.
  have hswap : volume (K - K) * ENNReal.ofReal (1 / ((Nat.choose (2 * d) d : ℕ) : ℝ)) ≤ volume K := by
    calc
      volume (K - K) * ENNReal.ofReal (1 / ((Nat.choose (2 * d) d : ℕ) : ℝ))
        = ∫⁻ s : ℝ, ∫⁻ x : E, F x s := hlhs.symm
      _ = ∫⁻ x : E, ∫⁻ s : ℝ, F x s := (lintegral_lintegral_swap hFm.aemeasurable).symm
      _ ≤ ∫⁻ x : E, covariogram volume K x / volume K :=
          lintegral_mono fun x => rogers_shephard_radial_bound hKconv hd_pos hK0 hKfin x
      _ = (∫⁻ x : E, covariogram volume K x) / volume K := by
          simp_rw [ENNReal.div_eq_inv_mul]
          rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hK0)]
      _ = (volume K * volume K) / volume K := by rw [covariogram_lintegral hKm]
      _ = volume K := by
          rw [ENNReal.div_eq_inv_mul, ← mul_assoc, ENNReal.inv_mul_cancel hK0 hKfin, one_mul]
  have hc_pos : (0 : ℝ) < (Nat.choose (2 * d) d : ℕ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (by omega : d ≤ 2 * d))
  have hmul : ((Nat.choose (2 * d) d : ℕ) : ℝ≥0∞) *
      (volume (K - K) * ENNReal.ofReal (1 / ((Nat.choose (2 * d) d : ℕ) : ℝ))) ≤
      ((Nat.choose (2 * d) d : ℕ) : ℝ≥0∞) * volume K := by gcongr
  have hcancel : ((Nat.choose (2 * d) d : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (1 / ((Nat.choose (2 * d) d : ℕ) : ℝ)) = 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hc_pos.le,
      mul_one_div_cancel hc_pos.ne', ENNReal.ofReal_one]
  rwa [mul_left_comm, hcancel, mul_one] at hmul

end CovariogramAndRogersShephard

end

end ConvexGeom
