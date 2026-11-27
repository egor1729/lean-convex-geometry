/-
Copyright (c) 2026 Yegor Gorodzha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yegor Gorodzha
-/
module

public import ConvexGeom.Asymptotic.JohnEllipsoid
public import ConvexGeom.Metric.Polarity
public import ConvexGeom.Volume.Isoperimetric
public import Mathlib.Probability.Distributions.Gaussian.Real

import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Loomis–Whitney, Rank-1 Brascamp–Lieb, Barthe's Reverse Brascamp–Lieb, and Ball's Volume Ratio

This module establishes the Loomis–Whitney inequality, the geometric rank-1 **Brascamp–Lieb**
and **Reverse Brascamp–Lieb** inequalities via Barthe's monotone Gaussian mass-transport method,
and derives their central convex-geometric consequences.

## Main definitions

* `ConvexGeom.stdGaussianDensity`: standard Gaussian density `(2 * π)^(-d / 2) * exp (-‖x‖² / 2)`
  on a finite-dimensional real inner product space `E`.

## Main statements

* `ConvexGeom.lintegral_stdGaussianDensity_eq_one`, `ConvexGeom.measure_preimage_inner_null`:
  Gaussian normalization and hyperplane null-set pullbacks.
* `ConvexGeom.loomis_whitney_lintegral`, `ConvexGeom.loomis_whitney_pi`,
  `ConvexGeom.loomis_whitney`: Loomis–Whitney inequality
  `vol_d(K)^(d - 1) ≤ ∏ i, vol_{d - 1}(P_{e_i⊥}(K))`.
* `ConvexGeom.exists_gaussian_transport`: 1D monotone Gaussian optimal transport on open intervals.
* `ConvexGeom.brascamp_lieb_rankOne_of_continuous_pos`, `ConvexGeom.brascamp_lieb_rankOne`:
  rank-1 geometric Brascamp–Lieb inequality for arbitrary measurable `ℝ≥0∞`-valued functions.
* `ConvexGeom.reverse_brascamp_lieb_rankOne`: Barthe's rank-1 geometric reverse Brascamp–Lieb
  inequality.
* `ConvexGeom.volume_le_two_pow_of_john_position_symmetric`,
  `ConvexGeom.ball_volume_ratio_symmetric`, `ConvexGeom.volume_le_simplex_bound_of_john_position`,
  `ConvexGeom.ball_volume_ratio`: Ball's volume ratio theorems for symmetric and general bodies.
* `ConvexGeom.ball_reverse_isoperimetric_symmetric`, `ConvexGeom.ball_reverse_isoperimetric`:
  Ball's reverse isoperimetric inequalities (cube and regular-simplex bounds).
* `ConvexGeom.barthe_polar_volume_of_john_position_symmetric`,
  `ConvexGeom.barthe_outer_volume_ratio_symmetric`: Barthe's `2^d / d!` polar volume lower bound.
* `ConvexGeom.john_position_gaussian_measure_le`: `γ_d(r K) ≤ γ_1([-r, r])^d` in John's position.

## Implementation notes

While `brascamp_lieb_rankOne` holds for arbitrary measurable `ℝ≥0∞`-valued functions,
`reverse_brascamp_lieb_rankOne` is currently stated for continuous, strictly positive, integrable
densities `f i` supported on open preconnected nonempty intervals `I i ⊆ ℝ` (matching the
hypotheses of `exists_gaussian_transport`), rather than arbitrary measurable functions.

## References

* [K. Ball, *An Elementary Introduction to Modern Convex Geometry*][ball1997], Lecture 6
* [F. Barthe, *On a reverse form of the Brascamp–Lieb inequality*][barthe1998]
-/

open MeasureTheory Set Filter Metric ProbabilityTheory
open scoped RealInnerProductSpace ENNReal NNReal Pointwise Topology

namespace ConvexGeom

public section

/-! ### Private Algebraic Helpers for `ℝ≥0∞` Powers -/

private lemma ennreal_finset_prod_rpow {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞)
    {r : ℝ} (hr : 0 ≤ r) :
    (∏ i ∈ s, f i) ^ r = ∏ i ∈ s, f i ^ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, ENNReal.mul_rpow_of_nonneg _ _ hr, ih]

private lemma ennreal_rpow_sum_of_pos {ι : Type*} (s : Finset ι) {a : ℝ≥0∞}
    (ha0 : 0 < a) (hatop : a ≠ ⊤) (f : ι → ℝ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.prod_insert hj, ENNReal.rpow_add _ _ ha0.ne' hatop, ih]

private lemma integrableOn_Ioi_rpow_mul_exp_neg_mul {q b : ℝ} (hq : -1 < q) (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => x ^ q * Real.exp (-b * x)) (Ioi 0) volume := by
  have hgam : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ ((q + 1) - 1)) (Ioi 0) volume :=
    Real.GammaIntegral_convergent (by linarith)
  have hgam' : IntegrableOn (fun x : ℝ => x ^ q * Real.exp (-x)) (Ioi 0) volume :=
    hgam.congr_fun (fun x _ => by ring_nf) measurableSet_Ioi
  have h1 : Integrable ((Ioi (0 : ℝ)).indicator (fun x : ℝ => x ^ q * Real.exp (-x))) volume :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hgam'
  have hcomp : Integrable
      (fun x : ℝ => (Ioi (0 : ℝ)).indicator (fun y : ℝ => y ^ q * Real.exp (-y)) (b * x)) volume :=
    h1.comp_mul_left' hb.ne'
  have hscale : IntegrableOn
      (fun x : ℝ => b ^ (-q) * (Ioi (0 : ℝ)).indicator (fun y : ℝ => y ^ q * Real.exp (-y)) (b * x))
      (Ioi 0) volume :=
    (hcomp.const_mul (b ^ (-q))).integrableOn
  refine hscale.congr_fun (fun x hx => ?_) measurableSet_Ioi
  dsimp only
  rw [indicator_of_mem (mem_Ioi.mpr (mul_pos hb hx)), Real.mul_rpow hb.le (le_of_lt hx),
    ← mul_assoc, ← mul_assoc, ← Real.rpow_add hb, neg_add_cancel, Real.rpow_zero, one_mul, neg_mul]

private lemma ennreal_tendsto_finset_prod {ι α : Type*} {l : Filter α}
    (s : Finset ι) {f : ι → α → ℝ≥0∞} {b : ι → ℝ≥0∞}
    (hf : ∀ i ∈ s, Tendsto (f i) l (𝓝 (b i))) (hb : ∀ i ∈ s, b i ≠ ⊤) :
    Tendsto (fun n => ∏ i ∈ s, f i n) l (𝓝 (∏ i ∈ s, b i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tendsto_const_nhds
  | insert a s ha ih =>
      simp_rw [Finset.prod_insert ha]
      have hprod_ne : ∏ i ∈ s, b i ≠ ⊤ :=
        ENNReal.prod_ne_top fun i hi => hb i (Finset.mem_insert_of_mem hi)
      exact ENNReal.Tendsto.mul (hf a (Finset.mem_insert_self a s)) (Or.inr hprod_ne)
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => hb i (Finset.mem_insert_of_mem hi)))
        (Or.inr (hb a (Finset.mem_insert_self a s)))

/-! ### 1. Standard Gaussian Density and Product Integral Helpers -/

section GaussianDensity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Standard `d`-dimensional Gaussian probability density on a finite-dimensional real inner
product space `E`: `(2 * π) ^ (-d / 2) * exp (-‖x‖² / 2)`. -/
@[expose]
noncomputable def stdGaussianDensity (x : E) : ℝ :=
  (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (-(‖x‖ ^ 2) / 2)

lemma stdGaussianDensity_pos (x : E) : 0 < stdGaussianDensity x := by
  unfold stdGaussianDensity
  positivity

lemma stdGaussianDensity_nonneg (x : E) : 0 ≤ stdGaussianDensity x :=
  (stdGaussianDensity_pos x).le

lemma continuous_stdGaussianDensity : Continuous (stdGaussianDensity : E → ℝ) := by
  unfold stdGaussianDensity
  fun_prop

lemma measurable_stdGaussianDensity [MeasurableSpace E] [BorelSpace E] :
    Measurable (stdGaussianDensity : E → ℝ) :=
  continuous_stdGaussianDensity.measurable

/-- Product of `Fin d` nonnegative measurable functions integrates to the product of their 1D
integrals on `(Fin d → ℝ)` under product Lebesgue measure. -/
theorem lintegral_pi_prod_eq_prod : ∀ {d : ℕ} (f : Fin d → ℝ → ℝ≥0∞),
    (∀ i, Measurable (f i)) →
    ∫⁻ x : Fin d → ℝ, ∏ i, f i (x i) = ∏ i, ∫⁻ t : ℝ, f i t
  | 0, f, _ => by
      simp [volume_pi]
  | d + 1, f, hf => by
      have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) (0 : Fin (d + 1))
      have hmeas : Measurable (fun p : ℝ × (Fin d → ℝ) =>
          f 0 p.1 * ∏ j : Fin d, f j.succ (p.2 j)) :=
        ((hf 0).comp measurable_fst).mul
          (Finset.measurable_fun_prod Finset.univ fun (j : Fin d) _ =>
            (hf j.succ).comp ((measurable_pi_apply j).comp measurable_snd))
      have hcomp := hmp.lintegral_comp_emb (MeasurableEquiv.piFinSuccAbove _ 0).measurableEmbedding
        (fun p : ℝ × (Fin d → ℝ) => f 0 p.1 * ∏ j : Fin d, f j.succ (p.2 j))
      have hfun : (fun x : Fin (d + 1) → ℝ =>
          f 0 (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 x).1 *
            ∏ j : Fin d, f j.succ ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 x).2 j)) =
          (fun x : Fin (d + 1) → ℝ => ∏ i : Fin (d + 1), f i (x i)) := by
        ext x
        rw [Fin.prod_univ_succ]
        simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.tail]
      rw [hfun] at hcomp
      rw [hcomp, Measure.volume_eq_prod, lintegral_prod _ hmeas.aemeasurable]
      have hprod_meas : Measurable (fun y : Fin d → ℝ => ∏ j : Fin d, f j.succ (y j)) :=
        Finset.measurable_fun_prod Finset.univ fun (j : Fin d) _ =>
          (hf j.succ).comp (measurable_pi_apply j)
      simp_rw [lintegral_const_mul _ hprod_meas]
      rw [lintegral_mul_const _ (hf 0), lintegral_pi_prod_eq_prod (fun j => f j.succ)
        (fun j => hf j.succ), Fin.prod_univ_succ]

/-- The 1D Gaussian density product formula on `Fin d → ℝ`. -/
private lemma prod_gaussianPDFReal_eq (d : ℕ) (x : Fin d → ℝ) :
    ∏ i : Fin d, gaussianPDFReal 0 1 (x i) =
      (2 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-(∑ i : Fin d, (x i) ^ 2) / 2) := by
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 : ∀ t : ℝ, gaussianPDFReal 0 1 t =
      (2 * Real.pi) ^ (-(1 : ℝ) / 2) * Real.exp (-(t ^ 2) / 2) := fun t => by
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg h2pi_pos.le]
    ring_nf
  simp_rw [h1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum, ← Real.rpow_natCast, ← Real.rpow_mul h2pi_pos.le]
  congr 1
  · congr 1; ring
  · congr 1
    rw [← Finset.sum_div, Finset.sum_neg_distrib]

/-- On any finite-dimensional real inner product space `E`, `stdGaussianDensity` integrates to `1`
with respect to Lebesgue measure `volume`. -/
theorem lintegral_stdGaussianDensity_eq_one [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] :
    ∫⁻ x : E, ENNReal.ofReal (stdGaussianDensity x) = 1 := by
  set d := Module.finrank ℝ E
  let b := stdOrthonormalBasis ℝ E
  let psi : (Fin d → ℝ) → E := fun x => b.repr.symm (WithLp.toLp 2 x)
  have hmp : MeasurePreserving psi volume volume :=
    (b.repr.symm.measurePreserving).comp (PiLp.volume_preserving_toLp (Fin d))
  have hemb : MeasurableEmbedding psi :=
    b.repr.symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding.comp
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding
  rw [← hmp.lintegral_comp_emb hemb (fun x : E => ENNReal.ofReal (stdGaussianDensity x))]
  have hfn : ∀ x : Fin d → ℝ,
      ENNReal.ofReal (stdGaussianDensity (psi x)) =
        ∏ i : Fin d, ENNReal.ofReal (gaussianPDFReal 0 1 (x i)) := fun x => by
    have hnorm : ‖psi x‖ ^ 2 = ∑ i : Fin d, (x i) ^ 2 := by
      change ‖b.repr.symm (WithLp.toLp 2 x)‖ ^ 2 = ∑ i : Fin d, (x i) ^ 2
      rw [b.repr.symm.norm_map, EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Real.norm_eq_abs, sq_abs]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg 0 1 (x i)),
      prod_gaussianPDFReal_eq]
    simp only [stdGaussianDensity, d, hnorm]
  simp_rw [hfn]
  rw [lintegral_pi_prod_eq_prod _ (fun _ => (measurable_gaussianPDFReal 0 1).ennreal_ofReal)]
  simp [lintegral_gaussianPDFReal_eq_one 0 one_ne_zero]

/-- Explicit Gaussian integral `∫⁻ x : E, ofReal (exp (-‖x‖² / 2)) = ofReal ((2 * π) ^ (d / 2))`. -/
theorem lintegral_exp_neg_half_norm_sq [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] :
    ∫⁻ x : E, ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 2)) =
      ENNReal.ofReal ((2 * Real.pi) ^ ((Module.finrank ℝ E : ℝ) / 2)) := by
  set d := Module.finrank ℝ E
  set c : ℝ := (2 * Real.pi) ^ ((d : ℝ) / 2)
  have hc_pos : 0 < c := by positivity
  have h1 := lintegral_stdGaussianDensity_eq_one (E := E)
  have hmul : ∀ x : E, ENNReal.ofReal (Real.exp (-(‖x‖ ^ 2) / 2)) =
      ENNReal.ofReal c * ENNReal.ofReal (stdGaussianDensity x) := fun x => by
    rw [← ENNReal.ofReal_mul hc_pos.le]
    congr 1
    simp only [stdGaussianDensity, c, d, ← mul_assoc,
      ← Real.rpow_add (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have hzero : (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 := by ring
    rw [hzero, Real.rpow_zero, one_mul]
  simp_rw [hmul]
  rw [lintegral_const_mul _ measurable_stdGaussianDensity.ennreal_ofReal, h1, mul_one]

/-- Pulling back a 1D Lebesgue-null set along a nonzero linear functional `x ↦ ⟪x, u⟫` yields a
Lebesgue-null set in `E`. -/
theorem measure_preimage_inner_null [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E} (hu : u ≠ 0) {s : Set ℝ} (hs : volume s = 0) :
    volume {x : E | ⟪x, u⟫ ∈ s} = 0 := by
  let v : E := ‖u‖⁻¹ • u
  have hv_norm : ‖v‖ = 1 := by
    simp [v, norm_smul, hu]
  let L : Submodule ℝ E := ℝ ∙ v
  let e1 : ℝ ≃ₗᵢ[ℝ] L := LinearIsometryEquiv.toSpanUnitSingleton v hv_norm
  let e2 : WithLp 2 (L × Lᗮ) ≃ₗᵢ[ℝ] E := L.orthogonalDecomposition.symm
  let ψ : ℝ × Lᗮ → E := fun p => e2 (WithLp.toLp 2 (e1 p.1, p.2))
  have hmp_e1 : MeasurePreserving (Prod.map e1 (id : Lᗮ → Lᗮ))
      ((volume : Measure ℝ).prod (volume : Measure Lᗮ))
      ((volume : Measure L).prod (volume : Measure Lᗮ)) :=
    e1.measurePreserving.prod (MeasurePreserving.id (volume : Measure Lᗮ))
  have hmp : MeasurePreserving ψ volume volume :=
    (e2.measurePreserving.comp (WithLp.volume_preserving_toLp (U := L) (V := Lᗮ))).comp hmp_e1
  have hψ_inner : ∀ p : ℝ × Lᗮ, ⟪ψ p, u⟫ = p.1 * ‖u‖ := fun ⟨r, y⟩ => by
    have hψ_val : ψ (r, y) = r • v + (y : E) := by
      change (e1 r : E) + (y : E) = r • v + (y : E)
      rfl
    have hyu : ⟪(y : E), u⟫ = 0 := by
      have hv_mem : v ∈ L := Submodule.subset_span (Set.mem_singleton v)
      have hyv : ⟪v, (y : E)⟫ = 0 := y.2 v hv_mem
      have hu_eq : u = ‖u‖ • v := by simp [v, smul_smul, hu]
      rw [hu_eq, inner_smul_right, real_inner_comm v (y : E), hyv, mul_zero]
    have hvu : ⟪v, u⟫ = ‖u‖ := by
      have hu_eq : u = ‖u‖ • v := by simp [v, smul_smul, hu]
      conv_lhs => rw [hu_eq]
      rw [inner_smul_right, real_inner_self_eq_norm_sq, hv_norm, one_pow, mul_one]
    rw [hψ_val, inner_add_left, inner_smul_left, RCLike.conj_to_real, hvu, hyu, add_zero]
  obtain ⟨t, hst, htm, ht0⟩ := exists_measurable_superset_of_null hs
  have hpre_t : ψ ⁻¹' {x : E | ⟪x, u⟫ ∈ t} =
      ((fun r : ℝ => r * ‖u‖) ⁻¹' t) ×ˢ (Set.univ : Set Lᗮ) := by
    ext ⟨r, y⟩
    simp only [mem_preimage, mem_ofPred_eq, mem_prod, mem_univ, and_true, hψ_inner]
  have ht' : volume ((fun r : ℝ => r * ‖u‖) ⁻¹' t) = 0 := by
    have hmul : (fun r : ℝ => r * ‖u‖) ⁻¹' t = (fun r : ℝ => ‖u‖ • r) ⁻¹' t := by
      ext r; simp [smul_eq_mul, mul_comm]
    rw [hmul, Measure.addHaar_preimage_smul volume (norm_ne_zero_iff.mpr hu), ht0, mul_zero]
  have hmeas_E : MeasurableSet {x : E | ⟪x, u⟫ ∈ t} :=
    htm.preimage (continuous_id.inner continuous_const).measurable
  have hE_t : volume {x : E | ⟪x, u⟫ ∈ t} = 0 := by
    rw [← hmp.map_eq, Measure.map_apply hmp.measurable hmeas_E,
      hpre_t, Measure.volume_eq_prod, Measure.prod_prod, ht', zero_mul]
  exact measure_mono_null (fun x hx => hst hx) hE_t

end GaussianDensity

/-! ### 2. Multilinear Hölder and the Loomis–Whitney Inequality -/

section LoomisWhitney

/-- **Functional Loomis–Whitney Inequality (Ball, Lecture 6):**
on `Fin (n + 2) → ℝ` (dimension `d = n + 2 ≥ 2`), for any family of measurable functions
`f i : (Fin (n + 1) → ℝ) → ℝ≥0∞`:
$$\int_{\mathbb{R}^{n+2}} \prod_{i=0}^{n+1} f_i(\pi_i(x))^{\frac{1}{n+1}}\,dx
  \le \prod_{i=0}^{n+1} \left(\int_{\mathbb{R}^{n+1}} f_i(y)\,dy\right)^{\frac{1}{n+1}},$$
where `π_i = Fin.removeNth i` omits coordinate `i`. -/
theorem loomis_whitney_lintegral : ∀ {n : ℕ}
    (f : Fin (n + 2) → (Fin (n + 1) → ℝ) → ℝ≥0∞),
    (∀ i, Measurable (f i)) →
    ∫⁻ x : Fin (n + 2) → ℝ, ∏ i : Fin (n + 2), f i (Fin.removeNth i x) ^ (1 / ((n + 1 : ℕ) : ℝ)) ≤
      ∏ i : Fin (n + 2), (∫⁻ y : Fin (n + 1) → ℝ, f i y) ^ (1 / ((n + 1 : ℕ) : ℝ))
  | 0, f, hf => by
      let e0 : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)
      have hmp0 : MeasurePreserving e0 volume volume :=
        volume_preserving_piUnique (fun _ : Fin 1 => ℝ)
      have hfn : ∀ x : Fin 2 → ℝ,
          ∏ i : Fin 2, f i (Fin.removeNth i x) ^ (1 / ((0 + 1 : ℕ) : ℝ)) =
            f 0 (e0.symm (x 1)) * f 1 (e0.symm (x 0)) := fun x => by
        rw [Fin.prod_univ_two]
        simp only [Nat.zero_add, Nat.cast_one, div_one, ENNReal.rpow_one]
        congr 2
        · ext k; fin_cases k; rfl
        · ext k; fin_cases k; rfl
      simp_rw [hfn]
      have hg0 : Measurable (fun t : ℝ => f 0 (e0.symm t)) := (hf 0).comp e0.symm.measurable
      have hg1 : Measurable (fun t : ℝ => f 1 (e0.symm t)) := (hf 1).comp e0.symm.measurable
      have hprod := lintegral_pi_prod_eq_prod (d := 2)
        (fun i t => if i = 0 then f 1 (e0.symm t) else f 0 (e0.symm t))
        (fun i => by fin_cases i <;> simpa using ‹_›)
      have hlhs : ∫⁻ x : Fin 2 → ℝ, f 0 (e0.symm (x 1)) * f 1 (e0.symm (x 0)) =
          ∫⁻ x : Fin 2 → ℝ, ∏ i : Fin 2, (if i = 0 then f 1 (e0.symm (x i)) else f 0 (e0.symm (x i))) := by
        congr 1; ext x; rw [Fin.prod_univ_two]; simp [mul_comm]
      rw [hlhs, hprod, Fin.prod_univ_two, Fin.prod_univ_two]
      simp only [↓reduceIte, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, Nat.zero_add,
        Nat.cast_one, div_one, ENNReal.rpow_one]
      rw [mul_comm]
      have h0 := hmp0.symm.lintegral_comp_emb e0.symm.measurableEmbedding (f 0)
      have h1 := hmp0.symm.lintegral_comp_emb e0.symm.measurableEmbedding (f 1)
      rw [h0, h1]
  | n + 1, f, hf => by
      let d : ℕ := n + 1 + 1
      have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
      have hd1_pos : (0 : ℝ) < (n + 1 : ℕ) := Nat.cast_pos.mpr (by omega)
      have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 3) => ℝ) (0 : Fin (n + 3))
      let eIns : ℝ × (Fin (n + 1) → ℝ) ≃ᵐ (Fin (n + 2) → ℝ) :=
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) 0).symm
      let g : Fin (n + 2) → ℝ → (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
        fun j t z => f j.succ (eIns (t, z))
      have hg_meas_prod : ∀ j : Fin (n + 2),
          Measurable (fun p : ℝ × (Fin (n + 1) → ℝ) => g j p.1 p.2) := fun j => by
        change Measurable (fun p => f j.succ (eIns p))
        exact (hf j.succ).comp eIns.measurable
      have hg_meas : ∀ j t, Measurable (g j t) := fun j t =>
        (hg_meas_prod j).comp (measurable_const.prodMk measurable_id)
      have hF : ∀ x : Fin (n + 3) → ℝ,
          ∏ i : Fin (n + 3), f i (Fin.removeNth i x) ^ (1 / ((n + 1 + 1 : ℕ) : ℝ)) =
            f 0 (Fin.tail x) ^ (1 / (d : ℝ)) *
              ∏ j : Fin (n + 2), g j (x 0) (Fin.removeNth j (Fin.tail x)) ^ (1 / (d : ℝ)) := fun x => by
        rw [Fin.prod_univ_succ]
        congr 1
        refine Finset.prod_congr rfl fun j _ => ?_
        congr 1
        dsimp only [g]
        congr 1
        ext k
        refine Fin.cases ?_ (fun m => ?_) k
        · simp [eIns, Fin.removeNth, Fin.succAbove]
        · simp [eIns, Fin.removeNth, Fin.tail, Fin.succ_succAbove_succ]
      simp_rw [hF]
      let Fprod : ℝ × (Fin (n + 2) → ℝ) → ℝ≥0∞ := fun p =>
        f 0 p.2 ^ (1 / (d : ℝ)) *
          ∏ j : Fin (n + 2), g j p.1 (Fin.removeNth j p.2) ^ (1 / (d : ℝ))
      have hFprod_meas : Measurable Fprod := by
        refine (((hf 0).comp measurable_snd).pow_const _).mul ?_
        refine Finset.measurable_fun_prod Finset.univ fun j _ => ?_
        have hrem : Measurable (fun y : Fin (n + 2) → ℝ => Fin.removeNth j y) :=
          (continuous_pi fun k => continuous_apply _).measurable
        exact ((hg_meas_prod j).comp (measurable_fst.prodMk (hrem.comp measurable_snd))).pow_const _
      have hcomp := hmp.lintegral_comp_emb (MeasurableEquiv.piFinSuccAbove _ 0).measurableEmbedding Fprod
      have hF_eq : (fun x : Fin (n + 3) → ℝ => Fprod (MeasurableEquiv.piFinSuccAbove _ 0 x)) =
          (fun x : Fin (n + 3) → ℝ => f 0 (Fin.tail x) ^ (1 / (d : ℝ)) *
            ∏ j : Fin (n + 2), g j (x 0) (Fin.removeNth j (Fin.tail x)) ^ (1 / (d : ℝ))) := by
        ext x
        simp [Fprod, MeasurableEquiv.piFinSuccAbove_apply]
      rw [hF_eq] at hcomp
      rw [hcomp, Measure.volume_eq_prod, lintegral_prod _ hFprod_meas.aemeasurable]
      have hinner : ∀ t : ℝ,
          ∫⁻ y : Fin (n + 2) → ℝ, Fprod (t, y) ≤
            (∫⁻ y : Fin (n + 2) → ℝ, f 0 y) ^ (1 / (d : ℝ)) *
              ∏ j : Fin (n + 2), (∫⁻ z : Fin (n + 1) → ℝ, g j t z) ^ (1 / (d : ℝ)) := fun t => by
        let G : (Fin (n + 2) → ℝ) → ℝ≥0∞ := fun y =>
          ∏ j : Fin (n + 2), g j t (Fin.removeNth j y) ^ (1 / ((n + 1 : ℕ) : ℝ))
        have hG_meas : Measurable G :=
          Finset.measurable_fun_prod Finset.univ fun j _ =>
            ((hg_meas j t).comp (continuous_pi fun k => continuous_apply _).measurable).pow_const _
        have hrewrite : ∀ y : Fin (n + 2) → ℝ,
            Fprod (t, y) = f 0 y ^ (1 / (d : ℝ)) * G y ^ (((n + 1 : ℕ) : ℝ) / (d : ℝ)) := fun y => by
          dsimp only [Fprod, G]
          congr 1
          rw [ennreal_finset_prod_rpow Finset.univ _ (by positivity)]
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [← ENNReal.rpow_mul]
          congr 1
          field_simp [hd_pos.ne', hd1_pos.ne']
        simp_rw [hrewrite]
        have hsum_exp : (1 : ℝ) / (d : ℝ) + ((n + 1 : ℕ) : ℝ) / (d : ℝ) = 1 := by
          rw [← add_div]
          have hnum : (1 : ℝ) + ((n + 1 : ℕ) : ℝ) = (d : ℝ) := by
            dsimp only [d]; push_cast; ring
          rw [hnum, div_self hd_pos.ne']
        have hhold := ENNReal.lintegral_mul_norm_pow_le (μ := volume)
          (hf 0).aemeasurable hG_meas.aemeasurable (by positivity) (by positivity) hsum_exp
        have hih := loomis_whitney_lintegral (n := n) (fun j => g j t) (fun j => hg_meas j t)
        calc
          ∫⁻ y, f 0 y ^ (1 / (d : ℝ)) * G y ^ (((n + 1 : ℕ) : ℝ) / (d : ℝ))
            ≤ (∫⁻ y, f 0 y) ^ (1 / (d : ℝ)) * (∫⁻ y, G y) ^ (((n + 1 : ℕ) : ℝ) / (d : ℝ)) := hhold
          _ ≤ (∫⁻ y, f 0 y) ^ (1 / (d : ℝ)) *
                (∏ j : Fin (n + 2), (∫⁻ z, g j t z) ^ (1 / ((n + 1 : ℕ) : ℝ))) ^
                  (((n + 1 : ℕ) : ℝ) / (d : ℝ)) := by gcongr
          _ = (∫⁻ y, f 0 y) ^ (1 / (d : ℝ)) *
                ∏ j : Fin (n + 2), (∫⁻ z, g j t z) ^ (1 / (d : ℝ)) := by
              congr 1
              rw [ennreal_finset_prod_rpow Finset.univ _ (by positivity)]
              refine Finset.prod_congr rfl fun j _ => ?_
              rw [← ENNReal.rpow_mul]
              congr 1
              field_simp [hd_pos.ne', hd1_pos.ne']
      let h : Fin (n + 2) → ℝ → ℝ≥0∞ := fun j t => ∫⁻ z : Fin (n + 1) → ℝ, g j t z
      have hh_meas : ∀ j, Measurable (h j) := fun j =>
        (hg_meas_prod j).lintegral_prod_right'
      have houter : ∫⁻ t : ℝ, ∏ j : Fin (n + 2), h j t ^ (1 / (d : ℝ)) ≤
          ∏ j : Fin (n + 2), (∫⁻ t : ℝ, h j t) ^ (1 / (d : ℝ)) :=
        ENNReal.lintegral_prod_norm_pow_le Finset.univ
          (fun j _ => (hh_meas j).aemeasurable)
          (by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            dsimp only [d]; push_cast
            have hne : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
            field_simp [hne]; ring)
          (fun _ _ => by positivity)
      have htonelli : ∀ j : Fin (n + 2), ∫⁻ t : ℝ, h j t = ∫⁻ y : Fin (n + 2) → ℝ, f j.succ y := fun j => by
        dsimp only [h, g]
        rw [← lintegral_prod _ (hg_meas_prod j).aemeasurable, ← Measure.volume_eq_prod]
        have hmpj := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) 0).symm
        exact hmpj.lintegral_comp_emb eIns.measurableEmbedding (f j.succ)
      have hh_prod_meas : Measurable (fun t : ℝ => ∏ j : Fin (n + 2), h j t ^ (1 / (d : ℝ))) :=
        Finset.measurable_fun_prod Finset.univ fun j _ => (hh_meas j).pow_const _
      calc
        ∫⁻ t : ℝ, ∫⁻ y : Fin (n + 2) → ℝ, Fprod (t, y)
          ≤ ∫⁻ t : ℝ, (∫⁻ y, f 0 y) ^ (1 / (d : ℝ)) *
              ∏ j : Fin (n + 2), h j t ^ (1 / (d : ℝ)) :=
            lintegral_mono hinner
        _ = (∫⁻ y, f 0 y) ^ (1 / (d : ℝ)) *
              ∫⁻ t : ℝ, ∏ j : Fin (n + 2), h j t ^ (1 / (d : ℝ)) :=
            lintegral_const_mul _ hh_prod_meas
        _ ≤ (∫⁻ y, f 0 y) ^ (1 / (d : ℝ)) *
              ∏ j : Fin (n + 2), (∫⁻ t : ℝ, h j t) ^ (1 / (d : ℝ)) := by gcongr
        _ = (∫⁻ y, f 0 y) ^ (1 / (d : ℝ)) *
              ∏ j : Fin (n + 2), (∫⁻ y, f j.succ y) ^ (1 / (d : ℝ)) := by
            simp_rw [htonelli]
        _ = ∏ i : Fin (n + 3), (∫⁻ y, f i y) ^ (1 / (d : ℝ)) :=
            (Fin.prod_univ_succ (fun i : Fin (n + 3) => (∫⁻ y, f i y) ^ (1 / (d : ℝ)))).symm

/-- **Geometric Loomis–Whitney Inequality on `Fin d → ℝ` (`d ≥ 2`, Ball, Lecture 6):**
for any measurable set `K ⊆ Fin d → ℝ` and any family of measurable sets `P i ⊆ Fin (d - 1) → ℝ`
covering the coordinate projections `Fin.removeNth i '' K ⊆ P i`:
$$\mathrm{vol}(K)^{d - 1} \le \prod_{i} \mathrm{vol}(P_i).$$ -/
theorem loomis_whitney_pi {n : ℕ} {K : Set (Fin (n + 2) → ℝ)} (hKm : MeasurableSet K)
    {P : Fin (n + 2) → Set (Fin (n + 1) → ℝ)} (hPm : ∀ i, MeasurableSet (P i))
    (hKP : ∀ i, Fin.removeNth i '' K ⊆ P i) :
    volume K ^ (n + 1) ≤ ∏ i : Fin (n + 2), volume (P i) := by
  let f : Fin (n + 2) → (Fin (n + 1) → ℝ) → ℝ≥0∞ := fun i => (P i).indicator 1
  have hf : ∀ i, Measurable (f i) := fun i => measurable_const.indicator (hPm i)
  have hlw := loomis_whitney_lintegral f hf
  have hle : K.indicator (1 : (Fin (n + 2) → ℝ) → ℝ≥0∞) ≤
      fun x => ∏ i : Fin (n + 2), f i (Fin.removeNth i x) ^ (1 / ((n + 1 : ℕ) : ℝ)) := by
    intro x
    by_cases hx : x ∈ K
    · simp only [indicator_of_mem hx, Pi.one_apply]
      have hprod : ∏ i : Fin (n + 2), f i (Fin.removeNth i x) ^ (1 / ((n + 1 : ℕ) : ℝ)) = 1 :=
        Finset.prod_eq_one fun i _ => by
          have hi : Fin.removeNth i x ∈ P i := hKP i ⟨x, hx, rfl⟩
          simp [f, indicator_of_mem hi]
      rw [hprod]
    · simp [indicator_of_notMem hx]
  have hvol_le : volume K ≤ ∏ i : Fin (n + 2), volume (P i) ^ (1 / ((n + 1 : ℕ) : ℝ)) := by
    calc
      volume K = ∫⁻ x, K.indicator 1 x := (lintegral_indicator_one hKm).symm
      _ ≤ ∫⁻ x, ∏ i, f i (Fin.removeNth i x) ^ (1 / ((n + 1 : ℕ) : ℝ)) := lintegral_mono hle
      _ ≤ ∏ i, (∫⁻ y, f i y) ^ (1 / ((n + 1 : ℕ) : ℝ)) := hlw
      _ = ∏ i, volume (P i) ^ (1 / ((n + 1 : ℕ) : ℝ)) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [lintegral_indicator_one (hPm i)]
  have hpow := pow_le_pow_left' hvol_le (n + 1)
  have hrhs : (∏ i : Fin (n + 2), volume (P i) ^ (1 / ((n + 1 : ℕ) : ℝ))) ^ (n + 1) =
      ∏ i : Fin (n + 2), volume (P i) := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, one_div_mul_cancel (by positivity),
      ENNReal.rpow_one]
  rwa [hrhs] at hpow

/-- **Geometric Loomis–Whitney Inequality for Compact Sets on `E` (Ball, Lecture 6):**
for any orthonormal basis `b : OrthonormalBasis (Fin (n + 2)) ℝ E` of an `(n + 2)`-dimensional
inner product space `E` and any compact `K ⊆ E`:
$$\mathrm{vol}(K)^{n + 1} \le \prod_{i=0}^{n+1} \mathrm{vol}(\pi_i(b.\mathrm{repr}(K))),$$
where `π_i` drops the `i`-th coordinate in the basis `b`. -/
theorem loomis_whitney {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} (b : OrthonormalBasis (Fin (n + 2)) ℝ E)
    {K : Set E} (hKc : IsCompact K) :
    volume K ^ (n + 1) ≤
      ∏ i : Fin (n + 2),
        volume ((fun x : E => Fin.removeNth i (WithLp.ofLp (b.repr x))) '' K) := by
  let ψ : E → (Fin (n + 2) → ℝ) := fun x => WithLp.ofLp (b.repr x)
  have hψ_cont : Continuous ψ :=
    (PiLp.continuous_ofLp 2 (fun _ : Fin (n + 2) => ℝ)).comp b.repr.continuous
  have hmp_ofLp : MeasurePreserving (WithLp.ofLp : EuclideanSpace ℝ (Fin (n + 2)) → Fin (n + 2) → ℝ)
      volume volume :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (n + 2))
  have hmp : MeasurePreserving ψ volume volume :=
    hmp_ofLp.comp b.repr.measurePreserving
  have hψK_comp : IsCompact (ψ '' K) := hKc.image hψ_cont
  have hvol_eq : volume (ψ '' K) = volume K := by
    have hpre : ψ ⁻¹' (ψ '' K) = K := by
      ext x
      simp only [mem_preimage, mem_image]
      constructor
      · rintro ⟨y, hy, hxy⟩
        have hby : b.repr y = b.repr x := WithLp.ofLp_injective 2 hxy
        exact (b.repr.injective hby) ▸ hy
      · intro hx; exact ⟨x, hx, rfl⟩
    rw [← hmp.measure_preimage hψK_comp.isClosed.measurableSet.nullMeasurableSet, hpre]
  have hrem_cont : ∀ i : Fin (n + 2), Continuous (Fin.removeNth i : (Fin (n + 2) → ℝ) → _) :=
    fun i => continuous_pi fun k => continuous_apply _
  have hP_comp : ∀ i, IsCompact (Fin.removeNth i '' (ψ '' K)) := fun i =>
    hψK_comp.image (hrem_cont i)
  have hlw := loomis_whitney_pi hψK_comp.isClosed.measurableSet
    (fun i => (hP_comp i).isClosed.measurableSet) (fun _ => Subset.rfl)
  rw [hvol_eq] at hlw
  refine hlw.trans_eq (Finset.prod_congr rfl fun i _ => ?_)
  congr 1
  ext y
  simp [ψ]

end LoomisWhitney

/-! ### 3. One-Dimensional Monotone Gaussian Transport (Barthe 1998) -/

section MonotoneTransport

/-- Cumulative distribution function on an open connected nonempty interval `I ⊆ ℝ`:
`cdfOn I f t = ∫ x in I ∩ Iic t, f x`. -/
private noncomputable def cdfOn (I : Set ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in I ∩ Iic t, f x

/-- Key properties of `cdfOn I f` for a continuous, strictly positive probability density `f`
on an open preconnected nonempty set `I ⊆ ℝ`: strictly increasing on `I`, `HasDerivAt` equal to
`f t` at every `t ∈ I`, and `cdfOn I f '' I = Ioo 0 1`. -/
private lemma cdfOn_properties {I : Set ℝ} (hIopen : IsOpen I) (hIconn : IsPreconnected I)
    (hIne : I.Nonempty) {f : ℝ → ℝ} (hf_cont : ContinuousOn f I)
    (hf_pos : ∀ t ∈ I, 0 < f t) (hf_int : IntegrableOn f I volume)
    (hf_one : ∫ t in I, f t = 1) :
    StrictMonoOn (cdfOn I f) I ∧
    (∀ t ∈ I, HasDerivAt (cdfOn I f) (f t) t) ∧
    cdfOn I f '' I = Ioo 0 1 := by
  have hIord : I.OrdConnected := hIconn.ordConnected
  have hdiff : ∀ {a b : ℝ}, a ∈ I → b ∈ I → a ≤ b →
      cdfOn I f b - cdfOn I f a = ∫ x in a..b, f x := by
    intro a b ha hb hab
    have hIoc_sub : Ioc a b ⊆ I :=
      Ioc_subset_Icc_self.trans (hIord.out ha hb)
    have hunion : I ∩ Iic b = (I ∩ Iic a) ∪ Ioc a b := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_union, mem_Ioc]
      constructor
      · rintro ⟨hxI, hxb⟩
        by_cases hxa : x ≤ a
        · exact Or.inl ⟨hxI, hxa⟩
        · exact Or.inr ⟨lt_of_not_ge hxa, hxb⟩
      · rintro (⟨hxI, hxa⟩ | ⟨hax, hxb⟩)
        · exact ⟨hxI, hxa.trans hab⟩
        · exact ⟨hIoc_sub ⟨hax, hxb⟩, hxb⟩
    have hdisj : Disjoint (I ∩ Iic a) (Ioc a b) :=
      Set.disjoint_left.mpr fun x ⟨_, hxa⟩ ⟨hax, _⟩ => not_lt_of_ge hxa hax
    have hint1 : IntegrableOn f (I ∩ Iic a) volume := hf_int.mono_set inter_subset_left
    have hint2 : IntegrableOn f (Ioc a b) volume := hf_int.mono_set hIoc_sub
    have hadd : ∫ x in I ∩ Iic b, f x = (∫ x in I ∩ Iic a, f x) + ∫ x in Ioc a b, f x := by
      rw [hunion, setIntegral_union hdisj measurableSet_Ioc hint1 hint2]
    rw [intervalIntegral.integral_of_le hab]
    dsimp only [cdfOn]
    linarith
  have hstrict : StrictMonoOn (cdfOn I f) I := by
    intro a ha b hb hab
    have hd := hdiff ha hb hab.le
    have hIcc_sub : Icc a b ⊆ I := hIord.out ha hb
    have hpos_int : 0 < ∫ x in a..b, f x :=
      intervalIntegral.integral_pos hab (hf_cont.mono hIcc_sub)
        (fun x hx => (hf_pos x (hIcc_sub (Ioc_subset_Icc_self hx))).le)
        ⟨(a + b) / 2, ⟨by linarith, by linarith⟩,
          hf_pos _ (hIcc_sub ⟨by linarith, by linarith⟩)⟩
    linarith
  have hderiv : ∀ t ∈ I, HasDerivAt (cdfOn I f) (f t) t := by
    intro t ht
    obtain ⟨δ, hδ_pos, hball⟩ := Metric.isOpen_iff.mp hIopen t ht
    have hsub_ball : Ioo (t - δ) (t + δ) ⊆ I := by
      intro x hx
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have heq_nhds : cdfOn I f =ᶠ[𝓝 t] fun s => cdfOn I f t + ∫ x in t..s, f x := by
      filter_upwards [Ioo_mem_nhds (by linarith : t - δ < t) (by linarith : t < t + δ)] with s hs
      have hsI : s ∈ I := hsub_ball hs
      rcases le_total t s with hts | hst
      · linarith [hdiff ht hsI hts]
      · have := hdiff hsI ht hst
        rw [intervalIntegral.integral_symm s t]
        linarith
    have hint_f : IntervalIntegrable f volume t t := IntervalIntegrable.refl
    have hcont_at : ContinuousAt f t := hf_cont.continuousAt (hIopen.mem_nhds ht)
    have hmeas_at : StronglyMeasurableAtFilter f (𝓝 t) volume :=
      hf_cont.stronglyMeasurableAtFilter hIopen t ht
    have hd0 : HasDerivAt (fun s => cdfOn I f t + ∫ x in t..s, f x) (f t) t := by
      simpa using (intervalIntegral.integral_hasDerivAt_right hint_f hmeas_at hcont_at).const_add
        (cdfOn I f t)
    exact hd0.congr_of_eventuallyEq heq_nhds
  have hsub_Ioo : cdfOn I f '' I ⊆ Ioo 0 1 := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨δ, hδ_pos, hball⟩ := Metric.isOpen_iff.mp hIopen t ht
    have ht1 : t - δ / 2 ∈ I := hball (by
      rw [Metric.mem_ball, Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos (half_pos hδ_pos)]
      linarith)
    have ht2 : t + δ / 2 ∈ I := hball (by
      rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hδ_pos)]
      linarith)
    have hnn : ∀ x ∈ I, 0 ≤ f x := fun x hx => (hf_pos x hx).le
    have h0_le : 0 ≤ cdfOn I f (t - δ / 2) :=
      setIntegral_nonneg (hIopen.measurableSet.inter measurableSet_Iic)
        (fun x hx => hnn x hx.1)
    have hle_1 : cdfOn I f (t + δ / 2) ≤ 1 := by
      rw [← hf_one]
      exact setIntegral_mono_set hf_int
        (ae_restrict_of_forall_mem hIopen.measurableSet hnn)
        (Eventually.of_forall inter_subset_left)
    exact ⟨lt_of_le_of_lt h0_le (hstrict ht1 ht (by linarith)),
      lt_of_lt_of_le (hstrict ht ht2 (by linarith)) hle_1⟩
  have hIoo_sub : Ioo 0 1 ⊆ cdfOn I f '' I := by
    intro y hy
    have hex_low : ∃ t₁ ∈ I, cdfOn I f t₁ < y := by
      have hex_seq : ∃ a : ℕ → ℝ, (∀ n, a n ∈ I) ∧ ∀ x ∈ I, ∀ᶠ n in atTop, a n < x := by
        by_cases hbdd : BddBelow I
        · set L := sInf I
          have hL_not : L ∉ I := by
            intro hLI
            obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hIopen L hLI
            have hmem : L - δ / 2 ∈ I := hball (by
              rw [Metric.mem_ball, Real.dist_eq, sub_sub_cancel_left, abs_neg,
                abs_of_pos (half_pos hδ)]
              linarith)
            linarith [csInf_le hbdd hmem]
          have hchoose : ∀ n : ℕ, ∃ t ∈ I, t < L + 1 / ((n : ℝ) + 1) := fun n => by
            obtain ⟨t, ht, hlt⟩ := Real.lt_sInf_add_pos hIne (show 0 < 1 / ((n : ℝ) + 1) by positivity)
            exact ⟨t, ht, hlt⟩
          choose a haI halt using hchoose
          refine ⟨a, haI, fun x hx => ?_⟩
          have hLx : L < x := lt_of_le_of_ne (csInf_le hbdd hx) (fun h => hL_not (h ▸ hx))
          obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.mpr hLx)
          filter_upwards [Filter.eventually_ge_atTop N] with n hn
          have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
            one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
          linarith [halt n]
        · have hchoose : ∀ n : ℕ, ∃ t ∈ I, t < -(n : ℝ) := fun n => by
            by_contra hnot
            push Not at hnot
            exact hbdd ⟨-(n : ℝ), fun t ht => hnot t ht⟩
          choose a haI halt using hchoose
          refine ⟨a, haI, fun x _ => ?_⟩
          obtain ⟨N, hN⟩ := exists_nat_gt (-x)
          filter_upwards [Filter.eventually_ge_atTop N] with n hn
          have : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
          linarith [halt n]
      obtain ⟨a, haI, ha_lt⟩ := hex_seq
      have htend : Tendsto (fun n => cdfOn I f (a n)) atTop (𝓝 0) := by
        have h0 : (0 : ℝ) = ∫ _ in I, (0 : ℝ) := by simp
        rw [h0]
        have hrew : ∀ n, cdfOn I f (a n) = ∫ x in I, (Iic (a n)).indicator f x := fun n => by
          dsimp only [cdfOn]
          rw [setIntegral_indicator measurableSet_Iic]
        simp_rw [hrew]
        refine tendsto_integral_of_dominated_convergence (fun x => f x)
          (fun n => (hf_int.aestronglyMeasurable.indicator measurableSet_Iic))
          hf_int ?_ ?_
        · intro n
          filter_upwards [ae_restrict_mem hIopen.measurableSet] with x hx
          by_cases hxa : x ≤ a n
          · rw [indicator_of_mem (mem_Iic.mpr hxa), Real.norm_eq_abs, abs_of_pos (hf_pos x hx)]
          · rw [indicator_of_notMem (show x ∉ Iic (a n) from hxa), norm_zero]
            exact (hf_pos x hx).le
        · filter_upwards [ae_restrict_mem hIopen.measurableSet] with x hx
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [ha_lt x hx] with n hn
          rw [indicator_of_notMem (show x ∉ Iic (a n) from not_le.mpr hn)]
      obtain ⟨n, hn⟩ := (htend.eventually (Iio_mem_nhds hy.1)).exists
      exact ⟨a n, haI n, hn⟩
    have hex_high : ∃ t₂ ∈ I, y < cdfOn I f t₂ := by
      have hex_seq : ∃ b : ℕ → ℝ, (∀ n, b n ∈ I) ∧ ∀ x ∈ I, ∀ᶠ n in atTop, x < b n := by
        by_cases hbdd : BddAbove I
        · set U := sSup I
          have hU_not : U ∉ I := by
            intro hUI
            obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hIopen U hUI
            have hmem : U + δ / 2 ∈ I := hball (by
              rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hδ)]
              linarith)
            linarith [le_csSup hbdd hmem]
          have hchoose : ∀ n : ℕ, ∃ t ∈ I, U - 1 / ((n : ℝ) + 1) < t := fun n => by
            obtain ⟨t, ht, hlt⟩ := Real.add_neg_lt_sSup hIne
              (show -(1 / ((n : ℝ) + 1)) < 0 by linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity])
            exact ⟨t, ht, by linarith⟩
          choose b hbI hbgt using hchoose
          refine ⟨b, hbI, fun x hx => ?_⟩
          have hxU : x < U := lt_of_le_of_ne (le_csSup hbdd hx) (fun h => hU_not (h ▸ hx))
          obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.mpr hxU)
          filter_upwards [Filter.eventually_ge_atTop N] with n hn
          have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
            one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
          linarith [hbgt n]
        · have hchoose : ∀ n : ℕ, ∃ t ∈ I, (n : ℝ) < t := fun n => by
            by_contra hnot
            push Not at hnot
            exact hbdd ⟨(n : ℝ), fun t ht => hnot t ht⟩
          choose b hbI hbgt using hchoose
          refine ⟨b, hbI, fun x _ => ?_⟩
          obtain ⟨N, hN⟩ := exists_nat_gt x
          filter_upwards [Filter.eventually_ge_atTop N] with n hn
          have : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
          linarith [hbgt n]
      obtain ⟨b, hbI, hb_gt⟩ := hex_seq
      have htend : Tendsto (fun n => cdfOn I f (b n)) atTop (𝓝 1) := by
        rw [← hf_one]
        have hrew : ∀ n, cdfOn I f (b n) = ∫ x in I, (Iic (b n)).indicator f x := fun n => by
          dsimp only [cdfOn]
          rw [setIntegral_indicator measurableSet_Iic]
        simp_rw [hrew]
        refine tendsto_integral_of_dominated_convergence (fun x => f x)
          (fun n => (hf_int.aestronglyMeasurable.indicator measurableSet_Iic))
          hf_int ?_ ?_
        · intro n
          filter_upwards [ae_restrict_mem hIopen.measurableSet] with x hx
          by_cases hxb : x ≤ b n
          · rw [indicator_of_mem (mem_Iic.mpr hxb), Real.norm_eq_abs, abs_of_pos (hf_pos x hx)]
          · rw [indicator_of_notMem (show x ∉ Iic (b n) from hxb), norm_zero]
            exact (hf_pos x hx).le
        · filter_upwards [ae_restrict_mem hIopen.measurableSet] with x hx
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [hb_gt x hx] with n hn
          rw [indicator_of_mem (mem_Iic.mpr hn.le)]
      obtain ⟨n, hn⟩ := (htend.eventually (Ioi_mem_nhds hy.2)).exists
      exact ⟨b n, hbI n, hn⟩
    obtain ⟨t₁, ht₁, hlt₁⟩ := hex_low
    obtain ⟨t₂, ht₂, hgt₂⟩ := hex_high
    have hcont : ContinuousOn (cdfOn I f) I := fun t ht =>
      (hderiv t ht).continuousAt.continuousWithinAt
    have hmem_Icc : y ∈ Icc (cdfOn I f t₁) (cdfOn I f t₂) := ⟨hlt₁.le, hgt₂.le⟩
    exact hIconn.intermediate_value ht₁ ht₂ hcont hmem_Icc
  exact ⟨hstrict, hderiv, Subset.antisymm hsub_Ioo hIoo_sub⟩

/-- Continuous inverse on `Ioo 0 1` of a strictly increasing continuous map `F` mapping an open
interval `I` onto `Ioo 0 1`. -/
private lemma exists_inverse_of_strictMonoOn_Ioo {I : Set ℝ} (hIopen : IsOpen I)
    {F : ℝ → ℝ} (hmono : StrictMonoOn F I) (himg : F '' I = Ioo 0 1) :
    ∃ G : ℝ → ℝ,
      (∀ y ∈ Ioo 0 1, G y ∈ I) ∧
      (∀ y ∈ Ioo 0 1, F (G y) = y) ∧
      (∀ t ∈ I, G (F t) = t) ∧
      StrictMonoOn G (Ioo 0 1) ∧
      (∀ y ∈ Ioo 0 1, ContinuousAt G y) := by
  have hex : ∀ y : ℝ, ∃ t : ℝ, y ∈ Ioo 0 1 → t ∈ I ∧ F t = y := fun y => by
    by_cases hy : y ∈ Ioo 0 1
    · rw [← himg] at hy
      obtain ⟨t, ht, hFt⟩ := hy
      exact ⟨t, fun _ => ⟨ht, hFt⟩⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose G hG using hex
  have hG_mem : ∀ y ∈ Ioo 0 1, G y ∈ I := fun y hy => (hG y hy).1
  have hFG : ∀ y ∈ Ioo 0 1, F (G y) = y := fun y hy => (hG y hy).2
  have hGF : ∀ t ∈ I, G (F t) = t := fun t ht => by
    have hFt : F t ∈ Ioo 0 1 := himg ▸ ⟨t, ht, rfl⟩
    exact hmono.injOn (hG_mem _ hFt) ht (hFG _ hFt)
  have hG_mono : StrictMonoOn G (Ioo 0 1) := fun y₁ hy₁ y₂ hy₂ hlt => by
    by_contra hnot
    have hle : G y₂ ≤ G y₁ := not_lt.mp hnot
    have hFle : F (G y₂) ≤ F (G y₁) := hmono.monotoneOn (hG_mem y₂ hy₂) (hG_mem y₁ hy₁) hle
    rw [hFG y₂ hy₂, hFG y₁ hy₁] at hFle
    linarith
  have hG_cont : ∀ y ∈ Ioo 0 1, ContinuousAt G y := fun y hy => by
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ_pos, hball⟩ := Metric.isOpen_iff.mp hIopen (G y) (hG_mem y hy)
    set r := min (δ / 2) (ε / 2)
    have hr_pos : 0 < r := lt_min (half_pos hδ_pos) (half_pos hε)
    have ht_lo : G y - r ∈ I := hball (by
      rw [Metric.mem_ball, Real.dist_eq]
      simp only [sub_sub_cancel_left, abs_neg, abs_of_pos hr_pos]
      exact (min_le_left _ _).trans_lt (half_lt_self hδ_pos))
    have ht_hi : G y + r ∈ I := hball (by
      rw [Metric.mem_ball, Real.dist_eq]
      simp only [add_sub_cancel_left, abs_of_pos hr_pos]
      exact (min_le_left _ _).trans_lt (half_lt_self hδ_pos))
    have hFlo_mem : F (G y - r) ∈ Ioo 0 1 := himg ▸ ⟨_, ht_lo, rfl⟩
    have hFhi_mem : F (G y + r) ∈ Ioo 0 1 := himg ▸ ⟨_, ht_hi, rfl⟩
    have hFlo_lt : F (G y - r) < y := by
      have := hmono ht_lo (hG_mem y hy) (by linarith)
      rwa [hFG y hy] at this
    have hFhi_gt : y < F (G y + r) := by
      have := hmono (hG_mem y hy) ht_hi (by linarith)
      rwa [hFG y hy] at this
    set η := min (y - F (G y - r)) (F (G y + r) - y)
    have hη_pos : 0 < η := lt_min (sub_pos.mpr hFlo_lt) (sub_pos.mpr hFhi_gt)
    refine ⟨η, hη_pos, fun y' hy' => ?_⟩
    rw [Real.dist_eq, abs_lt] at hy' ⊢
    have h1 : F (G y - r) < y' := by linarith [min_le_left (y - F (G y - r)) (F (G y + r) - y)]
    have h2 : y' < F (G y + r) := by linarith [min_le_right (y - F (G y - r)) (F (G y + r) - y)]
    have hy'_mem : y' ∈ Ioo 0 1 := ⟨hFlo_mem.1.trans h1, h2.trans hFhi_mem.2⟩
    have hG1 : G y - r < G y' := by
      rw [← hGF (G y - r) ht_lo]
      exact hG_mono hFlo_mem hy'_mem h1
    have hG2 : G y' < G y + r := by
      rw [← hGF (G y + r) ht_hi]
      exact hG_mono hy'_mem hFhi_mem h2
    have hr_lt_ε : r < ε := (min_le_right _ _).trans_lt (half_lt_self hε)
    exact ⟨by linarith, by linarith⟩
  exact ⟨G, hG_mem, hFG, hGF, hG_mono, hG_cont⟩

/-- **1D Monotone Gaussian Transport (Barthe 1998):**
for any continuous, strictly positive probability density `f` on an open preconnected nonempty
interval `I ⊆ ℝ` (`∫ t in I, f t = 1`), there exist mutually inverse strictly increasing
differentiable transport maps `T : I → ℝ` and `S : ℝ → I` satisfying:
- `T` pushes `f` forward to `γ := gaussianPDFReal 0 1`: `T'(t) = f(t) / γ(T(t))` on `I`;
- `S` pushes `γ` forward to `f`: `S'(y) = γ(y) / f(S(y))` on `ℝ`. -/
theorem exists_gaussian_transport {I : Set ℝ} (hIopen : IsOpen I) (hIconn : IsPreconnected I)
    (hIne : I.Nonempty) {f : ℝ → ℝ} (hf_cont : ContinuousOn f I)
    (hf_pos : ∀ t ∈ I, 0 < f t) (hf_int : IntegrableOn f I volume)
    (hf_one : ∫ t in I, f t = 1) :
    ∃ (T S : ℝ → ℝ),
      StrictMonoOn T I ∧
      StrictMono S ∧
      (∀ y : ℝ, S y ∈ I) ∧
      (∀ t ∈ I, S (T t) = t) ∧
      (∀ y : ℝ, T (S y) = y) ∧
      (∀ t ∈ I, HasDerivAt T (f t / gaussianPDFReal 0 1 (T t)) t) ∧
      (∀ y : ℝ, HasDerivAt S (gaussianPDFReal 0 1 y / f (S y)) y) := by
  let γ : ℝ → ℝ := gaussianPDFReal 0 1
  have hγ_cont : ContinuousOn γ Set.univ := by
    have : Continuous γ := by
      unfold γ gaussianPDFReal
      fun_prop
    exact this.continuousOn
  have hγ_pos : ∀ y ∈ (Set.univ : Set ℝ), 0 < γ y := fun y _ => gaussianPDFReal_pos 0 1 y one_ne_zero
  have hγ_int : IntegrableOn γ Set.univ volume :=
    integrableOn_univ.mpr (integrable_gaussianPDFReal 0 1)
  have hγ_one : ∫ y in (Set.univ : Set ℝ), γ y = 1 := by
    rw [Measure.restrict_univ]
    exact integral_gaussianPDFReal_eq_one 0 one_ne_zero
  obtain ⟨hF_mono, hF_deriv, hF_img⟩ :=
    cdfOn_properties hIopen hIconn hIne hf_cont hf_pos hf_int hf_one
  obtain ⟨hΦ_mono, hΦ_deriv, hΦ_img⟩ :=
    cdfOn_properties isOpen_univ isPreconnected_univ ⟨0, trivial⟩ hγ_cont hγ_pos hγ_int hγ_one
  obtain ⟨GF, hGF_mem, hFGF, hGFF, hGF_mono, hGF_cont⟩ :=
    exists_inverse_of_strictMonoOn_Ioo hIopen hF_mono hF_img
  obtain ⟨GΦ, _, hΦGΦ, hGΦΦ, hGΦ_mono, hGΦ_cont⟩ :=
    exists_inverse_of_strictMonoOn_Ioo isOpen_univ hΦ_mono hΦ_img
  let T : ℝ → ℝ := fun t => GΦ (cdfOn I f t)
  let S : ℝ → ℝ := fun y => GF (cdfOn Set.univ γ y)
  have hF_mem : ∀ t ∈ I, cdfOn I f t ∈ Ioo 0 1 := fun t ht => hF_img ▸ ⟨t, ht, rfl⟩
  have hΦ_mem : ∀ y : ℝ, cdfOn Set.univ γ y ∈ Ioo 0 1 := fun y => hΦ_img ▸ ⟨y, trivial, rfl⟩
  refine ⟨T, S, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    exact hGΦ_mono (hF_mem a ha) (hF_mem b hb) (hF_mono ha hb hab)
  · intro a b hab
    exact hGF_mono (hΦ_mem a) (hΦ_mem b) (hΦ_mono trivial trivial hab)
  · intro y
    exact hGF_mem _ (hΦ_mem y)
  · intro t ht
    dsimp only [T, S]
    rw [hΦGΦ _ (hF_mem t ht), hGFF t ht]
  · intro y
    dsimp only [T, S]
    rw [hFGF _ (hΦ_mem y), hGΦΦ y trivial]
  · intro t ht
    have hT_cont : ContinuousAt T t :=
      (hGΦ_cont _ (hF_mem t ht)).comp (hF_deriv t ht).continuousAt
    have hcomp : cdfOn Set.univ γ ∘ T =ᶠ[𝓝 t] cdfOn I f := by
      filter_upwards [hIopen.mem_nhds ht] with s hs
      exact hΦGΦ _ (hF_mem s hs)
    exact HasDerivAt.of_comp_left hT_cont (hΦ_deriv (T t) trivial) (hF_deriv t ht)
      (hγ_pos (T t) trivial).ne' hcomp
  · intro y
    have hS_cont : ContinuousAt S y :=
      (hGF_cont _ (hΦ_mem y)).comp (hΦ_deriv y trivial).continuousAt
    have hcomp : cdfOn I f ∘ S =ᶠ[𝓝 y] cdfOn Set.univ γ := by
      filter_upwards with z
      exact hFGF _ (hΦ_mem z)
    exact HasDerivAt.of_comp_left hS_cont (hF_deriv (S y) (hGF_mem _ (hΦ_mem y)))
      (hΦ_deriv y trivial) (hf_pos (S y) (hGF_mem _ (hΦ_mem y))).ne' hcomp

end MonotoneTransport

/-! ### 4. Rank-1 Geometric Brascamp–Lieb Inequality (Barthe 1998; Ball, Lecture 6) -/

section BrascampLieb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Helper: injectivity of any transport map `x ↦ ∑ i, (c i * T i ⟪x, u i⟫) • u i` built from a
John decomposition and strictly increasing 1D maps `T i`. -/
private lemma transport_injective {ι : Type*} [Fintype ι] {u : ι → E} {c : ι → ℝ}
    (h : IsJohnDecomposition u c) {T : ι → ℝ → ℝ} (hT : ∀ i, StrictMono (T i)) :
    Function.Injective (fun x : E => ∑ i, (c i * T i ⟪x, u i⟫) • u i) := by
  intro x y hxy
  dsimp only at hxy
  by_contra hne
  have hnorm_pos : 0 < ‖x - y‖ ^ 2 := sq_pos_of_pos (norm_sub_pos_iff.mpr hne)
  rw [h.norm_sq_eq_sum (x - y)] at hnorm_pos
  have hex : ∃ i₀ : ι, ⟪x - y, u i₀⟫ ≠ 0 := by
    by_contra hall
    push Not at hall
    have h0 : ∑ i, c i * ⟪x - y, u i⟫ ^ 2 = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hall i, zero_pow two_ne_zero, mul_zero]
    linarith
  obtain ⟨i₀, hi₀⟩ := hex
  have hterm_nn : ∀ i : ι, 0 ≤ c i * (T i ⟪x, u i⟫ - T i ⟪y, u i⟫) * ⟪x - y, u i⟫ := fun i => by
    rw [inner_sub_left]
    rcases lt_trichotomy ⟪x, u i⟫ ⟪y, u i⟫ with hlt | heq | hgt
    · have hTlt : T i ⟪x, u i⟫ < T i ⟪y, u i⟫ := hT i hlt
      have hprod : 0 ≤ (T i ⟪x, u i⟫ - T i ⟪y, u i⟫) * (⟪x, u i⟫ - ⟪y, u i⟫) :=
        mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hTlt.le) (sub_nonpos.mpr hlt.le)
      rw [mul_assoc]
      exact mul_nonneg (h.weight_pos i).le hprod
    · simp [heq]
    · have hTgt : T i ⟪y, u i⟫ < T i ⟪x, u i⟫ := hT i hgt
      have hprod : 0 ≤ (T i ⟪x, u i⟫ - T i ⟪y, u i⟫) * (⟪x, u i⟫ - ⟪y, u i⟫) :=
        mul_nonneg (sub_nonneg.mpr hTgt.le) (sub_nonneg.mpr hgt.le)
      rw [mul_assoc]
      exact mul_nonneg (h.weight_pos i).le hprod
  have hterm_pos : 0 < c i₀ * (T i₀ ⟪x, u i₀⟫ - T i₀ ⟪y, u i₀⟫) * ⟪x - y, u i₀⟫ := by
    rw [inner_sub_left] at hi₀ ⊢
    have hne' : ⟪x, u i₀⟫ ≠ ⟪y, u i₀⟫ := sub_ne_zero.mp hi₀
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · have hTlt : T i₀ ⟪x, u i₀⟫ < T i₀ ⟪y, u i₀⟫ := hT i₀ hlt
      rw [mul_assoc]
      exact mul_pos (h.weight_pos i₀)
        (mul_pos_of_neg_of_neg (sub_neg.mpr hTlt) (sub_neg.mpr hlt))
    · have hTgt : T i₀ ⟪y, u i₀⟫ < T i₀ ⟪x, u i₀⟫ := hT i₀ hgt
      rw [mul_assoc]
      exact mul_pos (h.weight_pos i₀)
        (mul_pos (sub_pos.mpr hTgt) (sub_pos.mpr hgt))
  have hsum_pos : 0 < ∑ i, c i * (T i ⟪x, u i⟫ - T i ⟪y, u i⟫) * ⟪x - y, u i⟫ :=
    Finset.sum_pos' (fun i _ => hterm_nn i) ⟨i₀, Finset.mem_univ i₀, hterm_pos⟩
  have hinner_zero :
      ⟪(∑ i, (c i * T i ⟪x, u i⟫) • u i) - (∑ i, (c i * T i ⟪y, u i⟫) • u i), x - y⟫ = 0 := by
    rw [hxy, sub_self, inner_zero_left]
  have hinner_eq :
      ⟪(∑ i, (c i * T i ⟪x, u i⟫) • u i) - (∑ i, (c i * T i ⟪y, u i⟫) • u i), x - y⟫ =
        ∑ i, c i * (T i ⟪x, u i⟫ - T i ⟪y, u i⟫) * ⟪x - y, u i⟫ := by
    rw [← Finset.sum_sub_distrib, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_smul, inner_smul_left, RCLike.conj_to_real, real_inner_comm (u i) (x - y)]
    ring
  linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Helper: Fréchet derivative of `x ↦ ∑ i, (c i * T i ⟪x, u i⟫) • u i` is
`∑ i, (c i * T' i ⟪x, u i⟫) • InnerProductSpace.rankOne ℝ (u i) (u i)`. -/
private lemma hasFDerivAt_transport {ι : Type*} [Fintype ι] (u : ι → E) (c : ι → ℝ)
    (T T' : ι → ℝ → ℝ) (x : E) (hT : ∀ i, HasDerivAt (T i) (T' i ⟪x, u i⟫) ⟪x, u i⟫) :
    HasFDerivAt (fun z : E => ∑ i, (c i * T i ⟪z, u i⟫) • u i)
      (∑ i, (c i * T' i ⟪x, u i⟫) • InnerProductSpace.rankOne ℝ (u i) (u i)) x := by
  have hterm : ∀ i : ι,
      HasFDerivAt (fun z : E => (c i * T i ⟪z, u i⟫) • u i)
        ((c i * T' i ⟪x, u i⟫) • InnerProductSpace.rankOne ℝ (u i) (u i)) x := fun i => by
    have hlin : HasFDerivAt (fun z : E => ⟪z, u i⟫) (innerSL ℝ (u i)) x := by
      have heq : (fun z : E => ⟪z, u i⟫) = (innerSL ℝ (u i) : E → ℝ) := by
        ext z; exact real_inner_comm (u i) z
      rw [heq]
      exact (innerSL ℝ (u i)).hasFDerivAt
    have hcomp : HasFDerivAt (fun z : E => T i ⟪z, u i⟫) (T' i ⟪x, u i⟫ • innerSL ℝ (u i)) x :=
      (hT i).comp_hasFDerivAt x hlin
    have hsmul : HasFDerivAt (fun z : E => c i * T i ⟪z, u i⟫)
        (c i • (T' i ⟪x, u i⟫ • innerSL ℝ (u i))) x := hcomp.const_mul (c i)
    have hvec := hsmul.smul_const (u i)
    convert hvec using 1
    ext v
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply,
      InnerProductSpace.rankOne_apply, innerSL_apply_apply, smul_eq_mul, smul_smul]
  have hfin : ∀ s : Finset ι,
      HasFDerivAt (fun z : E => ∑ i ∈ s, (c i * T i ⟪z, u i⟫) • u i)
        (∑ i ∈ s, (c i * T' i ⟪x, u i⟫) • InnerProductSpace.rankOne ℝ (u i) (u i)) x := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => simpa using hasFDerivAt_const (0 : E) x
    | insert a s ha ih =>
      simp_rw [Finset.sum_insert ha]
      exact (hterm a).add ih
  exact hfin Finset.univ

/-- **Smooth Rank-1 Geometric Brascamp–Lieb Inequality (Barthe 1998):**
for a John decomposition `IsJohnDecomposition u c` on `E` and continuous strictly positive
probability densities `f i : ℝ → ℝ` (`∫ f i = 1`):
$$\int_E \prod_i f_i(\langle x, u_i\rangle)^{c_i}\,dx \le 1.$$ -/
theorem brascamp_lieb_rankOne_of_continuous_pos {ι : Type*} [Fintype ι]
    {u : ι → E} {c : ι → ℝ} (h : IsJohnDecomposition u c)
    {f : ι → ℝ → ℝ} (hf_cont : ∀ i, Continuous (f i)) (hf_pos : ∀ i t, 0 < f i t)
    (hf_int : ∀ i, Integrable (f i)) (hf_one : ∀ i, ∫ t, f i t = 1) :
    ∫⁻ x : E, ∏ i, ENNReal.ofReal (f i ⟪x, u i⟫) ^ c i ≤ 1 := by
  set d := Module.finrank ℝ E
  let γ : ℝ → ℝ := gaussianPDFReal 0 1
  have hexT : ∀ i : ι, ∃ T : ℝ → ℝ,
      StrictMono T ∧ ∀ t : ℝ, HasDerivAt T (f i t / γ (T t)) t := fun i => by
    obtain ⟨T, _, hT_mono, _, _, _, _, hT_deriv, _⟩ :=
      exists_gaussian_transport isOpen_univ isPreconnected_univ ⟨0, trivial⟩
        (hf_cont i).continuousOn (fun t _ => hf_pos i t)
        (integrableOn_univ.mpr (hf_int i))
        (by rw [Measure.restrict_univ]; exact hf_one i)
    exact ⟨T, fun a b hab => hT_mono trivial trivial hab, fun t => hT_deriv t trivial⟩
  choose T hT_mono hT_deriv using hexT
  let T' : ι → ℝ → ℝ := fun i t => f i t / γ (T i t)
  have hT'_pos : ∀ i t, 0 < T' i t := fun i t =>
    div_pos (hf_pos i t) (gaussianPDFReal_pos 0 1 (T i t) one_ne_zero)
  let Θ : E → E := fun x => ∑ i, (c i * T i ⟪x, u i⟫) • u i
  let DΘ : E → (E →L[ℝ] E) :=
    fun x => ∑ i, (c i * T' i ⟪x, u i⟫) • InnerProductSpace.rankOne ℝ (u i) (u i)
  have hΘ_inj : Function.Injective Θ := transport_injective h hT_mono
  have hΘ_fderiv : ∀ x : E, HasFDerivAt Θ (DΘ x) x := fun x =>
    hasFDerivAt_transport u c T T' x (fun i => hT_deriv i ⟪x, u i⟫)
  have hpt : ∀ x : E,
      ∏ i, ENNReal.ofReal (f i ⟪x, u i⟫) ^ c i ≤
        ENNReal.ofReal |(DΘ x).det| * ENNReal.ofReal (stdGaussianDensity (Θ x)) := fun x => by
    have hdet_eq : (DΘ x).det =
        LinearMap.det (∑ i, (c i * T' i ⟪x, u i⟫) • rankOne (u i) (u i)) := by
      change LinearMap.det (DΘ x : E →ₗ[ℝ] E) = _
      congr 1
      ext v
      simp [DΘ, rankOne_apply, real_inner_comm]
    have hdet_ge : ∏ i, T' i ⟪x, u i⟫ ^ c i ≤ (DΘ x).det := by
      rw [hdet_eq]
      exact h.det_sum_rankOne_ge_prod (fun i => hT'_pos i ⟪x, u i⟫)
    have hdet_nn : 0 ≤ (DΘ x).det :=
      (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hT'_pos i ⟪x, u i⟫).le _).trans hdet_ge
    have hprod_γ : ∏ i, γ (T i ⟪x, u i⟫) ^ c i ≤ stdGaussianDensity (Θ x) := by
      have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
      have hγ_form : ∀ t : ℝ, γ t = (2 * Real.pi) ^ (-(1 : ℝ) / 2) * Real.exp (-(t ^ 2) / 2) := fun t => by
        rw [show γ t = gaussianPDFReal 0 1 t from rfl, gaussianPDFReal_def]
        simp only [NNReal.coe_one, mul_one, sub_zero]
        congr 1
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg h2pi_pos.le]
        ring_nf
      have h1 : ∏ i, γ (T i ⟪x, u i⟫) ^ c i =
          (2 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-(∑ i, c i * (T i ⟪x, u i⟫) ^ 2) / 2) := by
        have hterm : ∀ i, γ (T i ⟪x, u i⟫) ^ c i =
            (2 * Real.pi) ^ (-c i / 2) * Real.exp (-(c i * (T i ⟪x, u i⟫) ^ 2) / 2) := fun i => by
          rw [hγ_form, Real.mul_rpow (by positivity) (Real.exp_pos _).le,
            ← Real.rpow_mul h2pi_pos.le, ← Real.exp_mul]
          congr 1
          · congr 1; ring
          · congr 1; ring
        simp_rw [hterm, Finset.prod_mul_distrib, ← Real.exp_sum]
        have hpow : ∏ i, (2 * Real.pi) ^ (-c i / 2) = (2 * Real.pi) ^ (-(d : ℝ) / 2) := by
          rw [← Real.rpow_sum_of_pos h2pi_pos]
          congr 1
          rw [← Finset.sum_div, Finset.sum_neg_distrib, h.sum_weights]
        rw [hpow]
        congr 2
        rw [← Finset.sum_div, Finset.sum_neg_distrib]
      rw [h1, stdGaussianDensity]
      have hbessel : ‖Θ x‖ ^ 2 ≤ ∑ i, c i * (T i ⟪x, u i⟫) ^ 2 :=
        h.norm_sum_smul_sq_le (fun i => T i ⟪x, u i⟫)
      gcongr
    have hreal : ∏ i, f i ⟪x, u i⟫ ^ c i ≤ |(DΘ x).det| * stdGaussianDensity (Θ x) := by
      have hsplit : ∏ i, f i ⟪x, u i⟫ ^ c i =
          (∏ i, T' i ⟪x, u i⟫ ^ c i) * (∏ i, γ (T i ⟪x, u i⟫) ^ c i) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← Real.mul_rpow (hT'_pos i _).le (gaussianPDFReal_pos 0 1 _ one_ne_zero).le]
        dsimp only [T']
        rw [div_mul_cancel₀ _ (gaussianPDFReal_pos 0 1 _ one_ne_zero).ne']
      rw [hsplit, abs_of_nonneg hdet_nn]
      exact mul_le_mul hdet_ge hprod_γ
        (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (gaussianPDFReal_pos 0 1 _ one_ne_zero).le _)
        hdet_nn
    rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    have hlhs : ∏ i, ENNReal.ofReal (f i ⟪x, u i⟫) ^ c i =
        ENNReal.ofReal (∏ i, f i ⟪x, u i⟫ ^ c i) := by
      rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (hf_pos i _).le _)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [ENNReal.ofReal_rpow_of_pos (hf_pos i _)]
    rw [hlhs]
    exact ENNReal.ofReal_le_ofReal hreal
  calc
    ∫⁻ x : E, ∏ i, ENNReal.ofReal (f i ⟪x, u i⟫) ^ c i
      ≤ ∫⁻ x : E, ENNReal.ofReal |(DΘ x).det| * ENNReal.ofReal (stdGaussianDensity (Θ x)) :=
        lintegral_mono hpt
    _ = ∫⁻ x in Set.univ, ENNReal.ofReal |(DΘ x).det| * ENNReal.ofReal (stdGaussianDensity (Θ x)) := by
        rw [Measure.restrict_univ]
    _ = ∫⁻ y in Θ '' Set.univ, ENNReal.ofReal (stdGaussianDensity y) :=
        (lintegral_image_eq_lintegral_abs_det_fderiv_mul volume MeasurableSet.univ
          (fun x _ => (hΘ_fderiv x).hasFDerivWithinAt) hΘ_inj.injOn
          (fun y => ENNReal.ofReal (stdGaussianDensity y))).symm
    _ ≤ ∫⁻ y : E, ENNReal.ofReal (stdGaussianDensity y) := setLIntegral_le_lintegral _ _
    _ = 1 := lintegral_stdGaussianDensity_eq_one

/-- Helper: every measurable nonnegative probability density `g : ℝ → ℝ` (`∫ g = 1`) can be
approximated a.e. and in `L¹` by a sequence `phi n` of continuous, strictly positive integrable
functions with `∫ phi n → 1`. -/
private lemma exists_continuous_pos_approx_of_integrable
    {g : ℝ → ℝ} (hg_meas : Measurable g) (hg_nn : ∀ t, 0 ≤ g t)
    (hg_int : Integrable g) (hg_one : ∫ t, g t = 1) :
    ∃ phi : ℕ → ℝ → ℝ,
      (∀ n, Continuous (phi n)) ∧
      (∀ n t, 0 < phi n t) ∧
      (∀ n, Integrable (phi n)) ∧
      (∀ n, 0 < ∫ t, phi n t) ∧
      Tendsto (fun n => ∫ t, phi n t) atTop (𝓝 1) ∧
      (∀ᵐ t : ℝ, Tendsto (fun n => phi n t) atTop (𝓝 (g t))) := by
  have hex_approx : ∀ n : ℕ, ∃ k : ℝ → ℝ,
      Continuous k ∧ Integrable k ∧ ∫ t, ‖g t - k t‖ ≤ (1 / 2 : ℝ) ^ n := fun n => by
    obtain ⟨k, _, hdist, hk_cont, hk_int⟩ :=
      hg_int.exists_hasCompactSupport_integral_sub_le (show (0 : ℝ) < (1 / 2 : ℝ) ^ n by positivity)
    exact ⟨k, hk_cont, hk_int, hdist⟩
  choose k hk_cont hk_int hk_dist using hex_approx
  let γ : ℝ → ℝ := gaussianPDFReal 0 1
  have hγ_cont : Continuous γ := by unfold γ gaussianPDFReal; fun_prop
  have hγ_pos : ∀ t, 0 < γ t := fun t => gaussianPDFReal_pos 0 1 t one_ne_zero
  have hγ_int : Integrable γ := integrable_gaussianPDFReal 0 1
  have hγ_one : ∫ t, γ t = 1 := integral_gaussianPDFReal_eq_one 0 one_ne_zero
  let phi : ℕ → ℝ → ℝ := fun n t => max (k n t) 0 + (1 / 2 : ℝ) ^ n * γ t
  have hphi_cont : ∀ n, Continuous (phi n) := fun n =>
    ((hk_cont n).max continuous_const).add (continuous_const.mul hγ_cont)
  have hphi_pos : ∀ n t, 0 < phi n t := fun n t =>
    add_pos_of_nonneg_of_pos (le_max_right _ _) (mul_pos (by positivity) (hγ_pos t))
  have hphi_int : ∀ n, Integrable (phi n) := fun n =>
    ((hk_int n).sup (integrable_zero _ _ _)).add (hγ_int.const_mul _)
  have hM_pos : ∀ n, 0 < ∫ t, phi n t := fun n =>
    integral_pos_of_integrable_nonneg_ne_zero (hphi_cont n) (hphi_int n)
      (fun t => (hphi_pos n t).le) (hphi_pos n 0).ne'
  have hdiff_le : ∀ n t, |phi n t - g t| ≤ ‖g t - k n t‖ + (1 / 2 : ℝ) ^ n * γ t := fun n t => by
    have hmax : |max (k n t) 0 - g t| ≤ |g t - k n t| := by
      have hg0 := hg_nn t
      rw [abs_le]
      rcases le_total (k n t) 0 with hk0 | hk0
      · rw [max_eq_right hk0]
        have h1 : |g t - k n t| = g t - k n t := abs_of_nonneg (by linarith)
        rw [h1]; constructor <;> linarith
      · rw [max_eq_left hk0, abs_sub_comm]
        exact ⟨neg_abs_le _, le_abs_self _⟩
    have htri : |phi n t - g t| ≤ |max (k n t) 0 - g t| + |(1 / 2 : ℝ) ^ n * γ t| := by
      simpa [phi, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        abs_add_le (max (k n t) 0 - g t) ((1 / 2 : ℝ) ^ n * γ t)
    have hpos2 : |(1 / 2 : ℝ) ^ n * γ t| = (1 / 2 : ℝ) ^ n * γ t :=
      abs_of_pos (mul_pos (by positivity) (hγ_pos t))
    rw [Real.norm_eq_abs]
    linarith
  have hL1_le : ∀ n, ∫ t, |phi n t - g t| ≤ 2 * (1 / 2 : ℝ) ^ n := fun n => by
    have hnorm_int : Integrable (fun t => ‖g t - k n t‖) volume :=
      (hg_int.sub (hk_int n)).norm
    calc
      ∫ t, |phi n t - g t| ≤ ∫ t, (‖g t - k n t‖ + (1 / 2 : ℝ) ^ n * γ t) :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
          (hnorm_int.add (hγ_int.const_mul _)) (ae_of_all _ (hdiff_le n))
      _ = (∫ t, ‖g t - k n t‖) + (1 / 2 : ℝ) ^ n * ∫ t, γ t := by
        rw [integral_add hnorm_int (hγ_int.const_mul _), integral_const_mul]
      _ ≤ (1 / 2 : ℝ) ^ n + (1 / 2 : ℝ) ^ n * 1 := by rw [hγ_one]; linarith [hk_dist n]
      _ = 2 * (1 / 2 : ℝ) ^ n := by ring
  have hM_tendsto : Tendsto (fun n => ∫ t, phi n t) atTop (𝓝 1) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have htend : Tendsto (fun n : ℕ => 2 * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 2
    obtain ⟨N, hN⟩ := (htend.eventually (Iio_mem_nhds hε)).exists_forall_of_atTop
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    have hsub : (∫ t, phi n t) - 1 = ∫ t, (phi n t - g t) := by
      rw [integral_sub (hphi_int n) hg_int, hg_one]
    calc
      |(∫ t, phi n t) - 1| = |∫ t, (phi n t - g t)| := by rw [hsub]
      _ ≤ ∫ t, |phi n t - g t| := abs_integral_le_integral_abs
      _ ≤ 2 * (1 / 2 : ℝ) ^ n := hL1_le n
      _ < ε := hN n hn
  have hae_conv : ∀ᵐ t : ℝ, Tendsto (fun n => phi n t) atTop (𝓝 (g t)) := by
    have hmeas_diff : ∀ n, Measurable (fun t => ENNReal.ofReal |phi n t - g t|) := fun n =>
      (continuous_abs.measurable.comp ((hphi_cont n).measurable.sub hg_meas)).ennreal_ofReal
    have htsum_lt : ∫⁻ t : ℝ, ∑' n : ℕ, ENNReal.ofReal |phi n t - g t| < ⊤ := by
      rw [lintegral_tsum fun n => (hmeas_diff n).aemeasurable]
      have hterm_le : ∀ n : ℕ, ∫⁻ t : ℝ, ENNReal.ofReal |phi n t - g t| ≤
          ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ n) := fun n => by
        have habs_int : Integrable (fun t => |phi n t - g t|) volume :=
          ((hphi_int n).sub hg_int).abs
        rw [← ofReal_integral_eq_lintegral_ofReal habs_int (ae_of_all _ fun _ => abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (hL1_le n)
      calc
        ∑' n : ℕ, ∫⁻ t, ENNReal.ofReal |phi n t - g t|
          ≤ ∑' n : ℕ, ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ n) := tsum_le_tsum hterm_le
        _ = ENNReal.ofReal (∑' n : ℕ, 2 * (1 / 2 : ℝ) ^ n) :=
            (ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
              ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2)).symm
        _ < ⊤ := ENNReal.ofReal_lt_top
    have hae_fin : ∀ᵐ t : ℝ, ∑' n : ℕ, ENNReal.ofReal |phi n t - g t| < ⊤ :=
      ae_lt_top (Measurable.tsum hmeas_diff) htsum_lt.ne
    filter_upwards [hae_fin] with t ht
    have h0 : Tendsto (fun n => ENNReal.ofReal |phi n t - g t|) atTop (𝓝 0) :=
      ENNReal.tendsto_atTop_zero_of_tsum_ne_top ht.ne
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ :=
      (h0.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))).exists_forall_of_atTop
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mp (hN n hn)
  exact ⟨phi, hphi_cont, hphi_pos, hphi_int, hM_pos, hM_tendsto, hae_conv⟩

/-- **Rank-1 Geometric Brascamp–Lieb Inequality (Ball, Lecture 6; Barthe 1998):**
for any John decomposition `IsJohnDecomposition u c` on a finite-dimensional real inner product
space `E` and any measurable functions `f : ι → ℝ → ℝ≥0∞`:
$$\int_E \prod_i f_i(\langle x, u_i\rangle)^{c_i}\,dx
  \le \prod_i \left(\int_{\mathbb{R}} f_i(t)\,dt\right)^{c_i}.$$ -/
theorem brascamp_lieb_rankOne {ι : Type*} [Fintype ι]
    {u : ι → E} {c : ι → ℝ} (h : IsJohnDecomposition u c)
    {f : ι → ℝ → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : E, ∏ i, f i ⟪x, u i⟫ ^ c i ≤
      ∏ i, (∫⁻ t : ℝ, f i t) ^ c i := by
  by_cases hzero : ∃ i, ∫⁻ t : ℝ, f i t = 0
  · obtain ⟨i₀, hi₀⟩ := hzero
    have hae : f i₀ =ᵐ[volume] 0 := (lintegral_eq_zero_iff (hf i₀)).mp hi₀
    have hs_null : volume {t : ℝ | f i₀ t ≠ 0} = 0 := ae_iff.mp hae
    have hu_ne : u i₀ ≠ 0 := by
      intro hu0
      have := h.norm_eq_one i₀
      rw [hu0, norm_zero] at this
      norm_num at this
    have hE_null : volume {x : E | ⟪x, u i₀⟫ ∈ {t : ℝ | f i₀ t ≠ 0}} = 0 :=
      measure_preimage_inner_null hu_ne hs_null
    have hprod_ae : (fun x : E => ∏ i, f i ⟪x, u i⟫ ^ c i) =ᵐ[volume] fun _ => 0 := by
      rw [Filter.EventuallyEq, ae_iff]
      refine measure_mono_null (fun x hx => ?_) hE_null
      simp only [mem_ofPred_eq] at hx ⊢
      intro hfx0
      apply hx
      refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
      rw [hfx0, ENNReal.zero_rpow_of_pos (h.weight_pos i₀)]
    rw [lintegral_congr_ae hprod_ae, lintegral_zero]
    exact zero_le
  push Not at hzero
  by_cases htop : ∃ i, ∫⁻ t : ℝ, f i t = ⊤
  · obtain ⟨i₀, hi₀⟩ := htop
    have hrhs_top : ∏ i, (∫⁻ t : ℝ, f i t) ^ c i = ⊤ := by
      classical
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀), hi₀,
        ENNReal.top_rpow_of_pos (h.weight_pos i₀), ENNReal.top_mul]
      refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
      exact (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.mpr (hzero i)) (h.weight_pos i).le).ne'
    rw [hrhs_top]
    exact le_top
  push Not at htop
  let I : ι → ℝ≥0∞ := fun i => ∫⁻ t : ℝ, f i t
  have hI_ne_top : ∀ i, I i ≠ ⊤ := htop
  let g : ι → ℝ → ℝ := fun i t => ((I i)⁻¹ * f i t).toReal
  have hg_nn : ∀ i t, 0 ≤ g i t := fun _ _ => ENNReal.toReal_nonneg
  have hg_meas : ∀ i, Measurable (g i) := fun i =>
    ((hf i).const_mul (I i)⁻¹).ennreal_toReal
  have hg_int : ∀ i, Integrable (g i) := fun i => by
    refine integrable_toReal_of_lintegral_ne_top
      (((hf i).const_mul (I i)⁻¹).aemeasurable) ?_
    rw [lintegral_const_mul _ (hf i)]
    exact (ENNReal.inv_mul_cancel (hzero i) (hI_ne_top i)).trans_lt ENNReal.one_lt_top |>.ne
  have hg_ofReal : ∀ i, (fun t => ENNReal.ofReal (g i t)) =ᵐ[volume] fun t => (I i)⁻¹ * f i t := fun i => by
    have hfin : ∀ᵐ t : ℝ, (I i)⁻¹ * f i t ≠ ⊤ := by
      have hlt : ∫⁻ t, (I i)⁻¹ * f i t < ⊤ := by
        rw [lintegral_const_mul _ (hf i), ENNReal.inv_mul_cancel (hzero i) (hI_ne_top i)]
        exact ENNReal.one_lt_top
      filter_upwards [ae_lt_top ((hf i).const_mul (I i)⁻¹) hlt.ne] with t ht
      exact ht.ne
    filter_upwards [hfin] with t ht
    exact ENNReal.ofReal_toReal ht
  have hg_one : ∀ i, ∫ t, g i t = 1 := fun i => by
    have h1 : ENNReal.ofReal (∫ t, g i t) = 1 := by
      rw [ofReal_integral_eq_lintegral_ofReal (hg_int i) (ae_of_all _ (hg_nn i)),
        lintegral_congr_ae (hg_ofReal i), lintegral_const_mul _ (hf i),
        ENNReal.inv_mul_cancel (hzero i) (hI_ne_top i)]
    rwa [← ENNReal.ofReal_one,
      ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (hg_nn i)) zero_le_one] at h1
  choose phi hphi_cont hphi_pos hphi_int hM_pos hM_tendsto hae_conv using
    fun i => exists_continuous_pos_approx_of_integrable (hg_meas i) (hg_nn i) (hg_int i) (hg_one i)
  let M : ι → ℕ → ℝ := fun i n => ∫ t, phi i n t
  have hae_E : ∀ᵐ x : E, ∀ i : ι,
      Tendsto (fun n => ENNReal.ofReal (phi i n ⟪x, u i⟫) ^ c i) atTop
        (𝓝 (((I i)⁻¹ * f i ⟪x, u i⟫) ^ c i)) ∧
      ((I i)⁻¹ * f i ⟪x, u i⟫) ^ c i ≠ ⊤ := by
    rw [ae_all_iff]
    intro i
    have hu_ne : u i ≠ 0 := fun hu0 => by
      have := h.norm_eq_one i; rw [hu0, norm_zero] at this; norm_num at this
    have hbad1 : volume {t : ℝ | ¬ Tendsto (fun n => phi i n t) atTop (𝓝 (g i t))} = 0 :=
      ae_iff.mp (hae_conv i)
    have hbad2 : volume {t : ℝ | ENNReal.ofReal (g i t) ≠ (I i)⁻¹ * f i t} = 0 :=
      ae_iff.mp (hg_ofReal i)
    have hE1 := measure_preimage_inner_null hu_ne hbad1
    have hE2 := measure_preimage_inner_null hu_ne hbad2
    have hE_union : volume ({x : E | ⟪x, u i⟫ ∈ {t | ¬ Tendsto (fun n => phi i n t) atTop (𝓝 (g i t))}} ∪
        {x : E | ⟪x, u i⟫ ∈ {t | ENNReal.ofReal (g i t) ≠ (I i)⁻¹ * f i t}}) = 0 :=
      measure_union_null hE1 hE2
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) hE_union
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hnot
    apply hx
    rw [← hnot.2]
    refine ⟨(ENNReal.continuous_rpow_const.tendsto _).comp
      ((ENNReal.continuous_ofReal.tendsto _).comp hnot.1), ?_⟩
    exact ENNReal.rpow_ne_top_of_nonneg (h.weight_pos i).le ENNReal.ofReal_ne_top
  have hstep : ∀ n : ℕ,
      ∫⁻ x : E, ∏ i, ENNReal.ofReal (phi i n ⟪x, u i⟫) ^ c i ≤
        ∏ i, ENNReal.ofReal (M i n) ^ c i := fun n => by
    have hsm := brascamp_lieb_rankOne_of_continuous_pos h
      (f := fun i t => phi i n t / M i n)
      (fun i => (hphi_cont i n).div_const _)
      (fun i t => div_pos (hphi_pos i n t) (hM_pos i n))
      (fun i => (hphi_int i n).div_const _)
      (fun i => by rw [integral_div, div_self (hM_pos i n).ne'])
    have hscale : ∀ x : E,
        ∏ i, ENNReal.ofReal (phi i n ⟪x, u i⟫) ^ c i =
          (∏ i, ENNReal.ofReal (M i n) ^ c i) *
            ∏ i, ENNReal.ofReal (phi i n ⟪x, u i⟫ / M i n) ^ c i := fun x => by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← ENNReal.mul_rpow_of_nonneg _ _ (h.weight_pos i).le,
        ← ENNReal.ofReal_mul (hM_pos i n).le, mul_div_cancel₀ _ (hM_pos i n).ne']
    simp_rw [hscale]
    have hmeas_p : Measurable (fun x : E => ∏ i, ENNReal.ofReal (phi i n ⟪x, u i⟫ / M i n) ^ c i) :=
      Finset.measurable_fun_prod Finset.univ fun i _ =>
        (((hphi_cont i n).div_const _).measurable.comp
          (continuous_id.inner continuous_const).measurable).ennreal_ofReal.pow_const _
    rw [lintegral_const_mul _ hmeas_p]
    calc
      (∏ i, ENNReal.ofReal (M i n) ^ c i) *
          ∫⁻ x, ∏ i, ENNReal.ofReal (phi i n ⟪x, u i⟫ / M i n) ^ c i
        ≤ (∏ i, ENNReal.ofReal (M i n) ^ c i) * 1 := by gcongr
      _ = ∏ i, ENNReal.ofReal (M i n) ^ c i := mul_one _
  have hnorm_le_one :
      ∫⁻ x : E, ∏ i, ((I i)⁻¹ * f i ⟪x, u i⟫) ^ c i ≤ 1 := by
    have hliminf_ae : (fun x : E => ∏ i, ((I i)⁻¹ * f i ⟪x, u i⟫) ^ c i) =ᵐ[volume]
        fun x => liminf (fun n => ∏ i, ENNReal.ofReal (phi i n ⟪x, u i⟫) ^ c i) atTop := by
      filter_upwards [hae_E] with x hx
      have htend : Tendsto (fun n => ∏ i, ENNReal.ofReal (phi i n ⟪x, u i⟫) ^ c i) atTop
          (𝓝 (∏ i, ((I i)⁻¹ * f i ⟪x, u i⟫) ^ c i)) :=
        ennreal_tendsto_finset_prod Finset.univ (fun i _ => (hx i).1) (fun i _ => (hx i).2)
      exact htend.liminf_eq.symm
    have hM_prod_tendsto :
        Tendsto (fun n => ∏ i, ENNReal.ofReal (M i n) ^ c i) atTop (𝓝 1) := by
      have h1 : (1 : ℝ≥0∞) = ∏ _i : ι, (1 : ℝ≥0∞) ^ c _i := by simp
      rw [h1]
      exact ennreal_tendsto_finset_prod Finset.univ
        (fun i _ => (ENNReal.continuous_rpow_const.tendsto _).comp
          (by simpa [Function.comp_def, ENNReal.ofReal_one] using
            (ENNReal.continuous_ofReal.tendsto 1).comp (hM_tendsto i)))
        (fun i _ => by simp)
    calc
      ∫⁻ x : E, ∏ i, ((I i)⁻¹ * f i ⟪x, u i⟫) ^ c i
        = ∫⁻ x : E, liminf (fun n => ∏ i, ENNReal.ofReal (phi i n ⟪x, u i⟫) ^ c i) atTop :=
          lintegral_congr_ae hliminf_ae
      _ ≤ liminf (fun n => ∫⁻ x : E, ∏ i, ENNReal.ofReal (phi i n ⟪x, u i⟫) ^ c i) atTop :=
          lintegral_liminf_le fun n => Finset.measurable_fun_prod Finset.univ fun i _ =>
            ((hphi_cont i n).measurable.comp
              (continuous_id.inner continuous_const).measurable).ennreal_ofReal.pow_const _
      _ ≤ liminf (fun n => ∏ i, ENNReal.ofReal (M i n) ^ c i) atTop :=
          liminf_le_liminf (Eventually.of_forall hstep)
      _ = 1 := hM_prod_tendsto.liminf_eq
  have hunscale : ∀ x : E,
      ∏ i, f i ⟪x, u i⟫ ^ c i =
        (∏ i, I i ^ c i) * ∏ i, ((I i)⁻¹ * f i ⟪x, u i⟫) ^ c i := fun x => by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (h.weight_pos i).le, ← mul_assoc,
      ENNReal.mul_inv_cancel (hzero i) (hI_ne_top i), one_mul]
  simp_rw [hunscale]
  have hmeas_un : Measurable (fun x : E => ∏ i, ((I i)⁻¹ * f i ⟪x, u i⟫) ^ c i) :=
    Finset.measurable_fun_prod Finset.univ fun i _ =>
      (((hf i).comp (continuous_id.inner continuous_const).measurable).const_mul _).pow_const _
  rw [lintegral_const_mul _ hmeas_un]
  calc
    (∏ i, I i ^ c i) * ∫⁻ x, ∏ i, ((I i)⁻¹ * f i ⟪x, u i⟫) ^ c i
      ≤ (∏ i, I i ^ c i) * 1 := by gcongr
    _ = ∏ i, I i ^ c i := mul_one _

end BrascampLieb

/-! ### 5. Barthe's Reverse Brascamp–Lieb Inequality (Barthe 1998) -/

section ReverseBrascampLieb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Barthe's Reverse Brascamp–Lieb Inequality (Rank-1 Geometric Form, Barthe 1998):**
for a John decomposition `IsJohnDecomposition u c` on `E`, open preconnected nonempty intervals
`I i ⊆ ℝ`, continuous strictly positive integrable densities `f i` on `I i` with
`M i = ∫ t in I i, f i t`, and any `H : E → ℝ≥0∞` satisfying
$$\prod_i f_i(y_i)^{c_i} \le H\!\left(\sum_i (c_i y_i) u_i\right) \qquad (\forall y_i \in I_i),$$
we have
$$\prod_i \left(\int_{I_i} f_i(t)\,dt\right)^{c_i} \le \int_E H(z)\,dz.$$ -/
theorem reverse_brascamp_lieb_rankOne {ι : Type*} [Fintype ι]
    {u : ι → E} {c : ι → ℝ} (h : IsJohnDecomposition u c)
    {I : ι → Set ℝ} (hIopen : ∀ i, IsOpen (I i)) (hIconn : ∀ i, IsPreconnected (I i))
    (hIne : ∀ i, (I i).Nonempty)
    {f : ι → ℝ → ℝ} (hf_cont : ∀ i, ContinuousOn (f i) (I i))
    (hf_pos : ∀ i, ∀ t ∈ I i, 0 < f i t) (hf_int : ∀ i, IntegrableOn (f i) (I i) volume)
    {H : E → ℝ≥0∞}
    (hdom : ∀ y : ι → ℝ, (∀ i, y i ∈ I i) →
      ∏ i, ENNReal.ofReal (f i (y i)) ^ c i ≤ H (∑ i, (c i * y i) • u i)) :
    ∏ i, ENNReal.ofReal (∫ t in I i, f i t) ^ c i ≤ ∫⁻ z : E, H z := by
  let γ : ℝ → ℝ := gaussianPDFReal 0 1
  let M : ι → ℝ := fun i => ∫ t in I i, f i t
  have hM_pos : ∀ i, 0 < M i := fun i => by
    obtain ⟨t₀, ht₀⟩ := hIne i
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hIopen i) t₀ ht₀
    have hIcc_sub : Icc (t₀ - δ / 2) (t₀ + δ / 2) ⊆ I i := fun x hx =>
      hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2])
    have hpos_int : 0 < ∫ x in (t₀ - δ / 2)..(t₀ + δ / 2), f i x :=
      intervalIntegral.integral_pos (by linarith) ((hf_cont i).mono hIcc_sub)
        (fun x hx => (hf_pos i x (hIcc_sub (Ioc_subset_Icc_self hx))).le)
        ⟨t₀, ⟨by linarith, by linarith⟩, hf_pos i t₀ ht₀⟩
    rw [intervalIntegral.integral_of_le (by linarith)] at hpos_int
    have hle : ∫ x in Ioc (t₀ - δ / 2) (t₀ + δ / 2), f i x ≤ ∫ x in I i, f i x :=
      setIntegral_mono_set (hf_int i)
        (ae_restrict_of_forall_mem (hIopen i).measurableSet fun x hx => (hf_pos i x hx).le)
        (Eventually.of_forall (Ioc_subset_Icc_self.trans hIcc_sub))
    exact hpos_int.trans_le hle
  have hexS : ∀ i : ι, ∃ S : ℝ → ℝ,
      StrictMono S ∧ (∀ y : ℝ, S y ∈ I i) ∧
        ∀ y : ℝ, HasDerivAt S (γ y / (f i (S y) / M i)) y := fun i => by
    obtain ⟨_, S, _, hS_mono, hS_mem, _, _, _, hS_deriv⟩ :=
      exists_gaussian_transport (hIopen i) (hIconn i) (hIne i)
        ((hf_cont i).div_const (M i))
        (fun t ht => div_pos (hf_pos i t ht) (hM_pos i))
        ((hf_int i).div_const (M i))
        (by rw [integral_div, div_self (hM_pos i).ne'])
    exact ⟨S, hS_mono, hS_mem, hS_deriv⟩
  choose S hS_mono hS_mem hS_deriv using hexS
  let S' : ι → ℝ → ℝ := fun i y => γ y / (f i (S i y) / M i)
  have hS'_pos : ∀ i y, 0 < S' i y := fun i y =>
    div_pos (gaussianPDFReal_pos 0 1 y one_ne_zero)
      (div_pos (hf_pos i (S i y) (hS_mem i y)) (hM_pos i))
  let Ψ : E → E := fun x => ∑ i, (c i * S i ⟪x, u i⟫) • u i
  let DΨ : E → (E →L[ℝ] E) :=
    fun x => ∑ i, (c i * S' i ⟪x, u i⟫) • InnerProductSpace.rankOne ℝ (u i) (u i)
  have hΨ_inj : Function.Injective Ψ := transport_injective h hS_mono
  have hΨ_fderiv : ∀ x : E, HasFDerivAt Ψ (DΨ x) x := fun x =>
    hasFDerivAt_transport u c S S' x (fun i => hS_deriv i ⟪x, u i⟫)
  have hpt : ∀ x : E,
      (∏ i, ENNReal.ofReal (M i) ^ c i) * ENNReal.ofReal (stdGaussianDensity x) ≤
        ENNReal.ofReal |(DΨ x).det| * H (Ψ x) := fun x => by
    have hprod_γ : ∏ i, γ ⟪x, u i⟫ ^ c i = stdGaussianDensity x := by
      have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
      have hγ_form : ∀ t : ℝ, γ t = (2 * Real.pi) ^ (-(1 : ℝ) / 2) * Real.exp (-(t ^ 2) / 2) := fun t => by
        rw [show γ t = gaussianPDFReal 0 1 t from rfl, gaussianPDFReal_def]
        simp only [NNReal.coe_one, mul_one, sub_zero]
        congr 1
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg h2pi_pos.le]
        ring_nf
      have hterm : ∀ i, γ ⟪x, u i⟫ ^ c i =
          (2 * Real.pi) ^ (-c i / 2) * Real.exp (-(c i * ⟪x, u i⟫ ^ 2) / 2) := fun i => by
        rw [hγ_form, Real.mul_rpow (by positivity) (Real.exp_pos _).le,
          ← Real.rpow_mul h2pi_pos.le, ← Real.exp_mul]
        congr 1
        · congr 1; ring
        · congr 1; ring
      simp_rw [hterm, Finset.prod_mul_distrib, ← Real.exp_sum]
      rw [← Real.rpow_sum_of_pos h2pi_pos]
      unfold stdGaussianDensity
      congr 1
      · congr 1
        rw [← Finset.sum_div, Finset.sum_neg_distrib, h.sum_weights]
      · congr 1
        rw [← Finset.sum_div, Finset.sum_neg_distrib, h.norm_sq_eq_sum x]
    have hdet_eq : (DΨ x).det =
        LinearMap.det (∑ i, (c i * S' i ⟪x, u i⟫) • rankOne (u i) (u i)) := by
      change LinearMap.det (DΨ x : E →ₗ[ℝ] E) = _
      congr 1; ext v; simp [DΨ, rankOne_apply, real_inner_comm]
    have hdet_ge : ∏ i, S' i ⟪x, u i⟫ ^ c i ≤ (DΨ x).det := by
      rw [hdet_eq]
      exact h.det_sum_rankOne_ge_prod (fun i => hS'_pos i ⟪x, u i⟫)
    have hdet_nn : 0 ≤ (DΨ x).det :=
      (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hS'_pos i ⟪x, u i⟫).le _).trans hdet_ge
    have hsplit : (∏ i, M i ^ c i) * stdGaussianDensity x =
        (∏ i, S' i ⟪x, u i⟫ ^ c i) * ∏ i, f i (S i ⟪x, u i⟫) ^ c i := by
      rw [← hprod_γ, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Real.mul_rpow (hM_pos i).le (gaussianPDFReal_pos 0 1 _ one_ne_zero).le,
        ← Real.mul_rpow (hS'_pos i _).le (hf_pos i _ (hS_mem i _)).le]
      congr 1
      dsimp only [S', γ]
      field_simp [(hf_pos i _ (hS_mem i _)).ne', (hM_pos i).ne']
    have hreal_le : (∏ i, M i ^ c i) * stdGaussianDensity x ≤
        |(DΨ x).det| * ∏ i, f i (S i ⟪x, u i⟫) ^ c i := by
      rw [hsplit, abs_of_nonneg hdet_nn]
      exact mul_le_mul_of_nonneg_right hdet_ge
        (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hf_pos i _ (hS_mem i _)).le _)
    have hlhs_eq : (∏ i, ENNReal.ofReal (M i) ^ c i) * ENNReal.ofReal (stdGaussianDensity x) =
        ENNReal.ofReal ((∏ i, M i ^ c i) * stdGaussianDensity x) := by
      rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hM_pos i).le _),
        ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (hM_pos i).le _)]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ENNReal.ofReal_rpow_of_pos (hM_pos i)
    have hmid_eq : ENNReal.ofReal (|(DΨ x).det| * ∏ i, f i (S i ⟪x, u i⟫) ^ c i) =
        ENNReal.ofReal |(DΨ x).det| * ∏ i, ENNReal.ofReal (f i (S i ⟪x, u i⟫)) ^ c i := by
      rw [ENNReal.ofReal_mul (abs_nonneg _),
        ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (hf_pos i _ (hS_mem i _)).le _)]
      congr 1
      refine Finset.prod_congr rfl fun i _ =>
        (ENNReal.ofReal_rpow_of_pos (hf_pos i _ (hS_mem i _))).symm
    calc
      (∏ i, ENNReal.ofReal (M i) ^ c i) * ENNReal.ofReal (stdGaussianDensity x)
        = ENNReal.ofReal ((∏ i, M i ^ c i) * stdGaussianDensity x) := hlhs_eq
      _ ≤ ENNReal.ofReal (|(DΨ x).det| * ∏ i, f i (S i ⟪x, u i⟫) ^ c i) :=
          ENNReal.ofReal_le_ofReal hreal_le
      _ = ENNReal.ofReal |(DΨ x).det| * ∏ i, ENNReal.ofReal (f i (S i ⟪x, u i⟫)) ^ c i := hmid_eq
      _ ≤ ENNReal.ofReal |(DΨ x).det| * H (Ψ x) := by
          gcongr
          exact hdom (fun i => S i ⟪x, u i⟫) (fun i => hS_mem i ⟪x, u i⟫)
  calc
    ∏ i, ENNReal.ofReal (M i) ^ c i
      = (∏ i, ENNReal.ofReal (M i) ^ c i) * ∫⁻ x : E, ENNReal.ofReal (stdGaussianDensity x) := by
        rw [lintegral_stdGaussianDensity_eq_one, mul_one]
    _ = ∫⁻ x : E, (∏ i, ENNReal.ofReal (M i) ^ c i) * ENNReal.ofReal (stdGaussianDensity x) :=
        (lintegral_const_mul _ measurable_stdGaussianDensity.ennreal_ofReal).symm
    _ ≤ ∫⁻ x : E, ENNReal.ofReal |(DΨ x).det| * H (Ψ x) := lintegral_mono hpt
    _ = ∫⁻ x in Set.univ, ENNReal.ofReal |(DΨ x).det| * H (Ψ x) := by rw [Measure.restrict_univ]
    _ = ∫⁻ z in Ψ '' Set.univ, H z :=
        (lintegral_image_eq_lintegral_abs_det_fderiv_mul volume MeasurableSet.univ
          (fun x _ => (hΨ_fderiv x).hasFDerivWithinAt) hΨ_inj.injOn H).symm
    _ ≤ ∫⁻ z : E, H z := setLIntegral_le_lintegral _ _

end ReverseBrascampLieb

/-! ### 6. Applications: Ball's Volume Ratio, Reverse Isoperimetry, Barthe's Polar Bound, and Gaussian Measure -/

section Applications

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Ball's Volume Ratio Bound in John's Position (Origin-Symmetric, Ball, Lecture 6):**
if `K : ConvexBody E` is origin-symmetric and in John's position in dimension `d = finrank ℝ E ≥ 1`,
then `volume K ≤ 2 ^ d` (matching the unit cube `[-1, 1]^d`). -/
theorem volume_le_two_pow_of_john_position_symmetric [Nontrivial E]
    (K : ConvexBody E) (hsym : IsOriginSymmetric (K : Set E))
    (hJ : IsJohnPosition (K : Set E)) :
    volume (K : Set E) ≤ (2 : ℝ≥0∞) ^ Module.finrank ℝ E := by
  set d := Module.finrank ℝ E
  obtain ⟨m, u, c, hdecomp, _, hsup⟩ := john_decomposition_of_john_position K hJ
  let f : Fin m → ℝ → ℝ≥0∞ := fun _ => (Icc (-1 : ℝ) 1).indicator 1
  have hf : ∀ i, Measurable (f i) := fun _ => measurable_const.indicator measurableSet_Icc
  have hle : (K : Set E).indicator (1 : E → ℝ≥0∞) ≤ fun x => ∏ i, f i ⟪x, u i⟫ ^ c i := by
    intro x
    by_cases hx : x ∈ (K : Set E)
    · simp only [indicator_of_mem hx, Pi.one_apply]
      have hprod : ∏ i, f i ⟪x, u i⟫ ^ c i = 1 := Finset.prod_eq_one fun i _ => by
        have hupper : ⟪x, u i⟫ ≤ 1 := by
          rw [← hsup i]; exact inner_le_supportFn hx (u i)
        have hlower : -1 ≤ ⟪x, u i⟫ := by
          have hneg : -x ∈ (K : Set E) := hsym x hx
          have := inner_le_supportFn hneg (u i)
          rw [hsup i, inner_neg_left] at this
          linarith
        simp [f, indicator_of_mem (show ⟪x, u i⟫ ∈ Icc (-1 : ℝ) 1 from ⟨hlower, hupper⟩)]
      rw [hprod]
    · simp [indicator_of_notMem hx]
  have hint_f : ∀ i, ∫⁻ t : ℝ, f i t = 2 := fun _ => by
    rw [lintegral_indicator_one measurableSet_Icc, Real.volume_Icc]
    norm_num
  calc
    volume (K : Set E) = ∫⁻ x, (K : Set E).indicator 1 x :=
      (lintegral_indicator_one K.isCompact.isClosed.measurableSet).symm
    _ ≤ ∫⁻ x, ∏ i, f i ⟪x, u i⟫ ^ c i := lintegral_mono hle
    _ ≤ ∏ i, (∫⁻ t : ℝ, f i t) ^ c i := brascamp_lieb_rankOne hdecomp hf
    _ = ∏ i, (2 : ℝ≥0∞) ^ c i := by simp_rw [hint_f]
    _ = (2 : ℝ≥0∞) ^ (∑ i, c i) :=
        (ennreal_rpow_sum_of_pos Finset.univ (by norm_num : (0 : ℝ≥0∞) < 2) (by norm_num) c).symm
    _ = (2 : ℝ≥0∞) ^ d := by rw [hdecomp.sum_weights, ENNReal.rpow_natCast]

/-- **Ball's Volume Ratio Theorem (Origin-Symmetric, Ball, Lecture 6):**
every origin-symmetric convex body `K` with `0 ∈ interior K` has a linear image `T '' K`
containing the unit Euclidean ball `closedBall 0 1` with `volume (T '' K) ≤ 2 ^ d`. -/
theorem ball_volume_ratio_symmetric [Nontrivial E]
    (K : ConvexBody E) (hsym : IsOriginSymmetric (K : Set E))
    (h0 : (0 : E) ∈ interior (K : Set E)) :
    ∃ T : E ≃ₗ[ℝ] E,
      closedBall (0 : E) 1 ⊆ T '' (K : Set E) ∧
      volume (T '' (K : Set E)) ≤ (2 : ℝ≥0∞) ^ Module.finrank ℝ E := by
  obtain ⟨T, hJ⟩ := exists_linearEquiv_isJohnPosition_of_isOriginSymmetric K hsym h0
  let TK : ConvexBody E := mapLinear (T.toContinuousLinearMap) K
  have hTK_coe : (TK : Set E) = T '' (K : Set E) := by simp [TK]
  have hTK_sym : IsOriginSymmetric (TK : Set E) := by
    rw [hTK_coe]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨-x, hsym x hx, map_neg T x⟩
  have hvol := volume_le_two_pow_of_john_position_symmetric TK hTK_sym (hTK_coe ▸ hJ)
  exact ⟨T, hJ.1, hTK_coe ▸ hvol⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- Helper (Ball's `(d + 1)`-dimensional cone lifting): a balanced John decomposition `(u, c)` on
`E` lifts to a John decomposition `(v, c')` on `WithLp 2 (E × ℝ)` with
`v i = (-√(d/(d+1)) • u i, 1/√(d+1))` and `c' i = ((d+1)/d) * c i`. -/
private lemma isJohnDecomposition_lift_cone [Nontrivial E] {m : ℕ}
    {u : Fin m → E} {c : Fin m → ℝ}
    (hdecomp : IsJohnDecomposition u c) (hsum0 : ∑ i, c i • u i = 0) :
    IsJohnDecomposition
      (fun i : Fin m => WithLp.toLp 2
        ((-Real.sqrt ((Module.finrank ℝ E : ℝ) / ((Module.finrank ℝ E : ℝ) + 1))) • u i,
          1 / Real.sqrt ((Module.finrank ℝ E : ℝ) + 1)))
      (fun i : Fin m => (((Module.finrank ℝ E : ℝ) + 1) / (Module.finrank ℝ E : ℝ)) * c i) := by
  set d := Module.finrank ℝ E
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr Module.finrank_pos
  have hd1_pos : (0 : ℝ) < (d : ℝ) + 1 := by linarith
  let F := WithLp 2 (E × ℝ)
  let v : Fin m → F := fun i =>
    WithLp.toLp 2 ((-Real.sqrt ((d : ℝ) / ((d : ℝ) + 1))) • u i, 1 / Real.sqrt ((d : ℝ) + 1))
  let c' : Fin m → ℝ := fun i => (((d : ℝ) + 1) / (d : ℝ)) * c i
  have hv_inner : ∀ (i : Fin m) (z : F),
      ⟪z, v i⟫ = -Real.sqrt ((d : ℝ) / ((d : ℝ) + 1)) * ⟪(WithLp.ofLp z).1, u i⟫ +
        (WithLp.ofLp z).2 / Real.sqrt ((d : ℝ) + 1) := fun i z => by
    change ⟪(WithLp.ofLp z).1, (-Real.sqrt ((d : ℝ) / ((d : ℝ) + 1))) • u i⟫ +
        ⟪(WithLp.ofLp z).2, 1 / Real.sqrt ((d : ℝ) + 1)⟫ = _
    rw [inner_smul_right, RCLike.inner_apply, conj_trivial]
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hsq : ‖v i‖ ^ 2 = 1 := by
      rw [WithLp.prod_norm_sq_eq_of_L2]
      change ‖(-Real.sqrt ((d : ℝ) / ((d : ℝ) + 1))) • u i‖ ^ 2 +
          ‖1 / Real.sqrt ((d : ℝ) + 1)‖ ^ 2 = 1
      rw [norm_smul, hdecomp.norm_eq_one i, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
        sq_abs, sq_abs, neg_sq, div_pow, one_pow,
        Real.sq_sqrt (div_nonneg hd_pos.le hd1_pos.le), Real.sq_sqrt hd1_pos.le]
      field_simp [hd1_pos.ne']
    nlinarith [norm_nonneg (v i)]
  · intro i
    exact mul_pos (div_pos hd1_pos hd_pos) (hdecomp.weight_pos i)
  · ext z
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, rankOne_apply, LinearMap.id_apply]
    apply WithLp.ofLp_injective 2
    have h1 : (WithLp.ofLp (∑ i, c' i • (⟪z, v i⟫ • v i))).1 = (WithLp.ofLp z).1 := by
      rw [WithLp.ofLp_sum, Prod.fst_sum]
      have hterm : ∀ i : Fin m,
          (WithLp.ofLp (c' i • (⟪z, v i⟫ • v i))).1 =
            (c i * ⟪(WithLp.ofLp z).1, u i⟫) • u i -
              ((WithLp.ofLp z).2 / Real.sqrt (d : ℝ)) • (c i • u i) := fun i => by
        have hlhs_eq : (WithLp.ofLp (c' i • (⟪z, v i⟫ • v i))).1 =
            (c' i * ⟪z, v i⟫ * (-Real.sqrt ((d : ℝ) / ((d : ℝ) + 1)))) • u i := by
          change c' i • (⟪z, v i⟫ • ((-Real.sqrt ((d : ℝ) / ((d : ℝ) + 1))) • u i)) = _
          rw [smul_smul, smul_smul]
        rw [hlhs_eq, hv_inner]
        have hcoeff : c' i * (-Real.sqrt ((d : ℝ) / ((d : ℝ) + 1)) * ⟪(WithLp.ofLp z).1, u i⟫ +
            (WithLp.ofLp z).2 / Real.sqrt ((d : ℝ) + 1)) *
            (-Real.sqrt ((d : ℝ) / ((d : ℝ) + 1))) =
            c i * ⟪(WithLp.ofLp z).1, u i⟫ - (WithLp.ofLp z).2 / Real.sqrt (d : ℝ) * c i := by
          dsimp only [c']
          have hsq1 : Real.sqrt ((d : ℝ) / ((d : ℝ) + 1)) * Real.sqrt ((d : ℝ) / ((d : ℝ) + 1)) =
              (d : ℝ) / ((d : ℝ) + 1) := Real.mul_self_sqrt (div_nonneg hd_pos.le hd1_pos.le)
          have hsq2 : Real.sqrt ((d : ℝ) / ((d : ℝ) + 1)) / Real.sqrt ((d : ℝ) + 1) =
              Real.sqrt (d : ℝ) / ((d : ℝ) + 1) := by
            rw [Real.sqrt_div hd_pos.le, div_div, Real.mul_self_sqrt hd1_pos.le]
          have hsqd : Real.sqrt (d : ℝ) / (d : ℝ) = 1 / Real.sqrt (d : ℝ) := by
            field_simp [(Real.sqrt_pos.mpr hd_pos).ne']
            rw [Real.sq_sqrt hd_pos.le]
          calc
            ((d : ℝ) + 1) / (d : ℝ) * c i *
                (-Real.sqrt ((d : ℝ) / ((d : ℝ) + 1)) * ⟪(WithLp.ofLp z).1, u i⟫ +
                  (WithLp.ofLp z).2 / Real.sqrt ((d : ℝ) + 1)) *
                -Real.sqrt ((d : ℝ) / ((d : ℝ) + 1))
              = ((d : ℝ) + 1) / (d : ℝ) * c i *
                  (Real.sqrt ((d : ℝ) / ((d : ℝ) + 1)) * Real.sqrt ((d : ℝ) / ((d : ℝ) + 1))) *
                  ⟪(WithLp.ofLp z).1, u i⟫ -
                ((d : ℝ) + 1) / (d : ℝ) * c i * (WithLp.ofLp z).2 *
                  (Real.sqrt ((d : ℝ) / ((d : ℝ) + 1)) / Real.sqrt ((d : ℝ) + 1)) := by ring
            _ = ((d : ℝ) + 1) / (d : ℝ) * c i * ((d : ℝ) / ((d : ℝ) + 1)) *
                  ⟪(WithLp.ofLp z).1, u i⟫ -
                ((d : ℝ) + 1) / (d : ℝ) * c i * (WithLp.ofLp z).2 *
                  (Real.sqrt (d : ℝ) / ((d : ℝ) + 1)) := by rw [hsq1, hsq2]
            _ = c i * ⟪(WithLp.ofLp z).1, u i⟫ -
                (WithLp.ofLp z).2 * (Real.sqrt (d : ℝ) / (d : ℝ)) * c i := by
                field_simp [hd_pos.ne', hd1_pos.ne']
            _ = c i * ⟪(WithLp.ofLp z).1, u i⟫ -
                (WithLp.ofLp z).2 / Real.sqrt (d : ℝ) * c i := by rw [hsqd]; ring
        rw [hcoeff, sub_smul, smul_smul]
      simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.smul_sum, hsum0, smul_zero, sub_zero]
      simpa [smul_smul] using hdecomp.sum_smul_inner (WithLp.ofLp z).1
    have h2 : (WithLp.ofLp (∑ i, c' i • (⟪z, v i⟫ • v i))).2 = (WithLp.ofLp z).2 := by
      rw [WithLp.ofLp_sum, Prod.snd_sum]
      have hterm : ∀ i : Fin m,
          (WithLp.ofLp (c' i • (⟪z, v i⟫ • v i))).2 =
            -(1 / Real.sqrt (d : ℝ)) * ⟪(WithLp.ofLp z).1, c i • u i⟫ +
              ((WithLp.ofLp z).2 / (d : ℝ)) * c i := fun i => by
        have hlhs_eq : (WithLp.ofLp (c' i • (⟪z, v i⟫ • v i))).2 =
            c' i * (⟪z, v i⟫ * (1 / Real.sqrt ((d : ℝ) + 1))) := rfl
        rw [hlhs_eq, hv_inner, inner_smul_right]
        have hsq1 : Real.sqrt ((d : ℝ) / ((d : ℝ) + 1)) * (1 / Real.sqrt ((d : ℝ) + 1)) =
            Real.sqrt (d : ℝ) / ((d : ℝ) + 1) := by
          rw [Real.sqrt_div hd_pos.le, mul_one_div, div_div, Real.mul_self_sqrt hd1_pos.le]
        have hsq2 : (1 / Real.sqrt ((d : ℝ) + 1)) * (1 / Real.sqrt ((d : ℝ) + 1)) =
            1 / ((d : ℝ) + 1) := by
          rw [mul_comm, one_div_mul_one_div, Real.mul_self_sqrt hd1_pos.le]
        have hsqd : Real.sqrt (d : ℝ) / (d : ℝ) = 1 / Real.sqrt (d : ℝ) := by
          field_simp [(Real.sqrt_pos.mpr hd_pos).ne']
          rw [Real.sq_sqrt hd_pos.le]
        dsimp only [c']
        calc
          ((d : ℝ) + 1) / (d : ℝ) * c i *
              ((-Real.sqrt ((d : ℝ) / ((d : ℝ) + 1)) * ⟪(WithLp.ofLp z).1, u i⟫ +
                (WithLp.ofLp z).2 / Real.sqrt ((d : ℝ) + 1)) * (1 / Real.sqrt ((d : ℝ) + 1)))
            = -(((d : ℝ) + 1) / (d : ℝ) *
                (Real.sqrt ((d : ℝ) / ((d : ℝ) + 1)) * (1 / Real.sqrt ((d : ℝ) + 1)))) *
                (c i * ⟪(WithLp.ofLp z).1, u i⟫) +
              ((d : ℝ) + 1) / (d : ℝ) * c i * (WithLp.ofLp z).2 *
                ((1 / Real.sqrt ((d : ℝ) + 1)) * (1 / Real.sqrt ((d : ℝ) + 1))) := by
              rw [div_eq_mul_one_div (WithLp.ofLp z).2]; ring
          _ = -(((d : ℝ) + 1) / (d : ℝ) * (Real.sqrt (d : ℝ) / ((d : ℝ) + 1))) *
                (c i * ⟪(WithLp.ofLp z).1, u i⟫) +
              ((d : ℝ) + 1) / (d : ℝ) * c i * (WithLp.ofLp z).2 * (1 / ((d : ℝ) + 1)) := by
              rw [hsq1, hsq2]
          _ = -(Real.sqrt (d : ℝ) / (d : ℝ)) * (c i * ⟪(WithLp.ofLp z).1, u i⟫) +
              (WithLp.ofLp z).2 / (d : ℝ) * c i := by
              field_simp [hd_pos.ne', hd1_pos.ne']
          _ = -(1 / Real.sqrt (d : ℝ)) * (c i * ⟪(WithLp.ofLp z).1, u i⟫) +
              (WithLp.ofLp z).2 / (d : ℝ) * c i := by rw [hsqd]
      simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← inner_sum, hsum0,
        inner_zero_right, mul_zero, zero_add, hdecomp.sum_weights]
      dsimp only [d] at hd_pos ⊢
      rw [div_mul_cancel₀ _ hd_pos.ne']
    exact Prod.ext h1 h2

/-- Helper: exact evaluation of the exponential integral over the cone
`{(x, r) : E × ℝ | 0 < r ∧ x ∈ (r / √d) • K}` on `WithLp 2 (E × ℝ)`. -/
private lemma lintegral_exp_cone [Nontrivial E] (K : ConvexBody E) :
    ∫⁻ z : WithLp 2 (E × ℝ),
      ({p : E × ℝ | 0 < p.2 ∧
          p.1 ∈ (p.2 / Real.sqrt (Module.finrank ℝ E : ℝ)) • (K : Set E)}).indicator
        (fun p : E × ℝ => ENNReal.ofReal (Real.exp (-p.2 * Real.sqrt ((Module.finrank ℝ E : ℝ) + 1))))
        (WithLp.ofLp z) =
      volume (K : Set E) * ENNReal.ofReal ((Module.finrank ℝ E : ℝ) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        ((Module.finrank ℝ E : ℝ) + 1) ^ (-((Module.finrank ℝ E : ℝ) + 1) / 2) *
        (Nat.factorial (Module.finrank ℝ E) : ℝ)) := by
  set d := Module.finrank ℝ E
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr Module.finrank_pos
  have hd1_pos : (0 : ℝ) < (d : ℝ) + 1 := by linarith
  let cone : Set (E × ℝ) := {p : E × ℝ | 0 < p.2 ∧ p.1 ∈ (p.2 / Real.sqrt (d : ℝ)) • (K : Set E)}
  let g : E × ℝ → ℝ≥0∞ :=
    cone.indicator fun p => ENNReal.ofReal (Real.exp (-p.2 * Real.sqrt ((d : ℝ) + 1)))
  have hg_meas : Measurable g := by
    have hcone_meas : MeasurableSet cone := by
      have heq : cone =
          {p : E × ℝ | 0 < p.2} ∩
            (fun p : E × ℝ => (Real.sqrt (d : ℝ) / p.2) • p.1) ⁻¹' (K : Set E) := by
        ext ⟨x, r⟩
        simp only [cone, mem_ofPred_eq, mem_inter_iff, mem_preimage, Set.mem_smul_set]
        constructor
        · rintro ⟨hr, k, hk, rfl⟩
          refine ⟨hr, ?_⟩
          rw [smul_smul]
          have h1 : Real.sqrt (d : ℝ) / r * (r / Real.sqrt (d : ℝ)) = 1 := by
            field_simp [hr.ne', (Real.sqrt_pos.mpr hd_pos).ne']
          rwa [h1, one_smul]
        · rintro ⟨hr, hk⟩
          refine ⟨hr, (Real.sqrt (d : ℝ) / r) • x, hk, ?_⟩
          rw [smul_smul]
          have h1 : r / Real.sqrt (d : ℝ) * (Real.sqrt (d : ℝ) / r) = 1 := by
            field_simp [hr.ne', (Real.sqrt_pos.mpr hd_pos).ne']
          rw [h1, one_smul]
      rw [heq]
      refine (isOpen_lt continuous_const continuous_snd).measurableSet.inter ?_
      have hmap : Measurable (fun p : E × ℝ => (Real.sqrt (d : ℝ) / p.2) • p.1) :=
        (measurable_const.div measurable_snd).smul measurable_fst
      exact K.isCompact.isClosed.measurableSet.preimage hmap
    have hfun_meas : Measurable (fun p : E × ℝ =>
        ENNReal.ofReal (Real.exp (-p.2 * Real.sqrt ((d : ℝ) + 1)))) := by
      fun_prop
    exact hfun_meas.indicator hcone_meas
  have hmp_ofLp := WithLp.volume_preserving_ofLp (U := E) (V := ℝ)
  change ∫⁻ z : WithLp 2 (E × ℝ), g (WithLp.ofLp z) = _
  rw [hmp_ofLp.lintegral_comp_emb (MeasurableEquiv.toLp 2 (E × ℝ)).symm.measurableEmbedding g,
    Measure.volume_eq_prod, lintegral_prod_symm _ hg_meas.aemeasurable]
  have hslice : ∀ r : ℝ, ∫⁻ x : E, g (x, r) =
      (Ioi (0 : ℝ)).indicator (fun r =>
        volume (K : Set E) * ENNReal.ofReal ((d : ℝ) ^ (-(d : ℝ) / 2) *
          (r ^ (d : ℝ) * Real.exp (-Real.sqrt ((d : ℝ) + 1) * r)))) r := fun r => by
    by_cases hr : 0 < r
    · rw [indicator_of_mem hr]
      have hg_r : ∀ x : E, g (x, r) =
          ((r / Real.sqrt (d : ℝ)) • (K : Set E)).indicator
            (fun _ => ENNReal.ofReal (Real.exp (-r * Real.sqrt ((d : ℝ) + 1)))) x := fun x => by
        dsimp only [g]
        by_cases hx : x ∈ (r / Real.sqrt (d : ℝ)) • (K : Set E)
        · rw [indicator_of_mem (show (x, r) ∈ cone from ⟨hr, hx⟩), indicator_of_mem hx]
        · rw [indicator_of_notMem (show (x, r) ∉ cone from fun h => hx h.2), indicator_of_notMem hx]
      simp_rw [hg_r]
      have hsmul_meas : MeasurableSet ((r / Real.sqrt (d : ℝ)) • (K : Set E)) :=
        (K.isCompact.smul _).isClosed.measurableSet
      rw [lintegral_indicator_const hsmul_meas,
        Measure.addHaar_smul volume (r / Real.sqrt (d : ℝ)) (K : Set E),
        abs_of_pos (pow_pos (div_pos hr (Real.sqrt_pos.mpr hd_pos)) d),
        mul_comm (ENNReal.ofReal (Real.exp _)), ← mul_assoc,
        mul_comm _ (volume (K : Set E)), mul_assoc]
      congr 1
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Real.rpow_natCast, div_pow]
      have hsqrt_inv : ((Real.sqrt (d : ℝ)) ^ d)⁻¹ = (d : ℝ) ^ (-(d : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hd_pos.le,
          ← Real.rpow_neg hd_pos.le]
        congr 1; ring
      rw [div_eq_mul_inv, hsqrt_inv]
      ring_nf
    · rw [indicator_of_notMem hr]
      have hg_r : ∀ x : E, g (x, r) = 0 := fun x =>
        indicator_of_notMem (show (x, r) ∉ cone from fun h => hr h.1) _
      simp [hg_r]
  simp_rw [hslice]
  rw [lintegral_indicator measurableSet_Ioi]
  have hpull : ∫⁻ r in Ioi (0 : ℝ),
      volume (K : Set E) * ENNReal.ofReal ((d : ℝ) ^ (-(d : ℝ) / 2) *
        (r ^ (d : ℝ) * Real.exp (-Real.sqrt ((d : ℝ) + 1) * r))) =
      volume (K : Set E) * ∫⁻ r in Ioi (0 : ℝ),
        ENNReal.ofReal ((d : ℝ) ^ (-(d : ℝ) / 2) *
          (r ^ (d : ℝ) * Real.exp (-Real.sqrt ((d : ℝ) + 1) * r))) :=
    lintegral_const_mul _ (by fun_prop)
  rw [hpull]
  congr 1
  have hpull2 : ∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal ((d : ℝ) ^ (-(d : ℝ) / 2) *
        (r ^ (d : ℝ) * Real.exp (-Real.sqrt ((d : ℝ) + 1) * r))) =
      ENNReal.ofReal ((d : ℝ) ^ (-(d : ℝ) / 2)) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (d : ℝ) * Real.exp (-Real.sqrt ((d : ℝ) + 1) * r)) := by
    simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg hd_pos.le _)]
    exact lintegral_const_mul _ (by fun_prop)
  rw [hpull2]
  have hgam_int : ∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal (r ^ (d : ℝ) * Real.exp (-Real.sqrt ((d : ℝ) + 1) * r)) =
      ENNReal.ofReal (((d : ℝ) + 1) ^ (-((d : ℝ) + 1) / 2) * (Nat.factorial d : ℝ)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrableOn_Ioi_rpow_mul_exp_neg_mul (by linarith) (Real.sqrt_pos.mpr hd1_pos))]
    · have hg := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := (d : ℝ))
        (b := Real.sqrt ((d : ℝ) + 1)) zero_lt_one (by linarith) (Real.sqrt_pos.mpr hd1_pos)
      simp only [Real.rpow_one, div_one, mul_one, Real.Gamma_nat_eq_factorial] at hg
      rw [hg]
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hd1_pos.le]
      congr 2; ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_pos _).le
  rw [hgam_int, ← ENNReal.ofReal_mul (Real.rpow_nonneg hd_pos.le _)]
  congr 1; ring

/-- **Ball's Volume Ratio Bound in John's Position (General / Simplex Bound, Ball, Lecture 6):**
for ANY convex body `K : ConvexBody E` in John's position in dimension `d = finrank ℝ E ≥ 1`:
$$\mathrm{vol}(K) \le \frac{d^{d/2} (d + 1)^{(d + 1)/2}}{d!},$$
with equality attained by the regular `d`-simplex circumscribing the unit ball. -/
theorem volume_le_simplex_bound_of_john_position [Nontrivial E]
    (K : ConvexBody E) (hJ : IsJohnPosition (K : Set E)) :
    volume (K : Set E) ≤
      ENNReal.ofReal ((Module.finrank ℝ E : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2) *
        ((Module.finrank ℝ E : ℝ) + 1) ^ (((Module.finrank ℝ E : ℝ) + 1) / 2) /
        (Nat.factorial (Module.finrank ℝ E) : ℝ)) := by
  set d := Module.finrank ℝ E
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr Module.finrank_pos
  have hd1_pos : (0 : ℝ) < (d : ℝ) + 1 := by linarith
  obtain ⟨m, u, c, hdecomp, hsum0, hsup⟩ := john_decomposition_of_john_position K hJ
  let F := WithLp 2 (E × ℝ)
  let v : Fin m → F := fun i =>
    WithLp.toLp 2 ((-Real.sqrt ((d : ℝ) / ((d : ℝ) + 1))) • u i, 1 / Real.sqrt ((d : ℝ) + 1))
  let c' : Fin m → ℝ := fun i => (((d : ℝ) + 1) / (d : ℝ)) * c i
  have hv_inner : ∀ (i : Fin m) (z : F),
      ⟪z, v i⟫ = -Real.sqrt ((d : ℝ) / ((d : ℝ) + 1)) * ⟪(WithLp.ofLp z).1, u i⟫ +
        (WithLp.ofLp z).2 / Real.sqrt ((d : ℝ) + 1) := fun i z => by
    change ⟪(WithLp.ofLp z).1, (-Real.sqrt ((d : ℝ) / ((d : ℝ) + 1))) • u i⟫ +
        ⟪(WithLp.ofLp z).2, 1 / Real.sqrt ((d : ℝ) + 1)⟫ = _
    rw [inner_smul_right, RCLike.inner_apply, conj_trivial]
    ring
  have hv_decomp : IsJohnDecomposition v c' := isJohnDecomposition_lift_cone hdecomp hsum0
  let f : Fin m → ℝ → ℝ≥0∞ :=
    fun _ t => (Ici (0 : ℝ)).indicator (fun s => ENNReal.ofReal (Real.exp (-s))) t
  have hf : ∀ i, Measurable (f i) := fun _ =>
    (Real.continuous_exp.comp continuous_neg).measurable.ennreal_ofReal.indicator measurableSet_Ici
  have hf_int : ∀ i, ∫⁻ t : ℝ, f i t = 1 := fun _ => by
    dsimp only [f]
    rw [lintegral_indicator measurableSet_Ici,
      setLIntegral_congr Ioi_ae_eq_Ici.symm,
      ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi 0)
        (ae_of_all _ fun _ => (Real.exp_pos _).le)]
    have hexp := integral_exp_neg_rpow zero_lt_one
    simp only [Real.rpow_one, div_one] at hexp
    have hgam : Real.Gamma (1 + 1) = 1 := by simpa using Real.Gamma_nat_eq_factorial 1
    rw [hexp, hgam, ENNReal.ofReal_one]
  have hbl := brascamp_lieb_rankOne hv_decomp hf
  simp_rw [hf_int, ENNReal.one_rpow, Finset.prod_const_one] at hbl
  have hpt_le : ∀ z : F,
      ({p : E × ℝ | 0 < p.2 ∧ p.1 ∈ (p.2 / Real.sqrt (d : ℝ)) • (K : Set E)}).indicator
        (fun p : E × ℝ => ENNReal.ofReal (Real.exp (-p.2 * Real.sqrt ((d : ℝ) + 1))))
        (WithLp.ofLp z) ≤ ∏ i, f i ⟪z, v i⟫ ^ c' i := fun z => by
    by_cases hcond : 0 < (WithLp.ofLp z).2 ∧
        (WithLp.ofLp z).1 ∈ ((WithLp.ofLp z).2 / Real.sqrt (d : ℝ)) • (K : Set E)
    · rw [indicator_of_mem hcond]
      rcases hcond with ⟨hr_pos, k, hk, hkx⟩
      have hge0 : ∀ i, 0 ≤ ⟪z, v i⟫ := fun i => by
        rw [hv_inner, ← hkx, inner_smul_left, RCLike.conj_to_real]
        have hk_le : ⟪k, u i⟫ ≤ 1 := by rw [← hsup i]; exact inner_le_supportFn hk (u i)
        have hsqrt : Real.sqrt ((d : ℝ) / ((d : ℝ) + 1)) * ((WithLp.ofLp z).2 / Real.sqrt (d : ℝ)) =
            (WithLp.ofLp z).2 / Real.sqrt ((d : ℝ) + 1) := by
          rw [Real.sqrt_div hd_pos.le]
          field_simp [(Real.sqrt_pos.mpr hd_pos).ne', (Real.sqrt_pos.mpr hd1_pos).ne']
        have h1 : Real.sqrt ((d : ℝ) / ((d : ℝ) + 1)) *
            ((WithLp.ofLp z).2 / Real.sqrt (d : ℝ) * ⟪k, u i⟫) ≤
            (WithLp.ofLp z).2 / Real.sqrt ((d : ℝ) + 1) := by
          calc
            Real.sqrt ((d : ℝ) / ((d : ℝ) + 1)) *
                ((WithLp.ofLp z).2 / Real.sqrt (d : ℝ) * ⟪k, u i⟫)
              = (Real.sqrt ((d : ℝ) / ((d : ℝ) + 1)) *
                  ((WithLp.ofLp z).2 / Real.sqrt (d : ℝ))) * ⟪k, u i⟫ := by ring
            _ = ((WithLp.ofLp z).2 / Real.sqrt ((d : ℝ) + 1)) * ⟪k, u i⟫ := by rw [hsqrt]
            _ ≤ ((WithLp.ofLp z).2 / Real.sqrt ((d : ℝ) + 1)) * 1 :=
                mul_le_mul_of_nonneg_left hk_le (by positivity)
            _ = (WithLp.ofLp z).2 / Real.sqrt ((d : ℝ) + 1) := mul_one _
        linarith
      have hsum_inner : ∑ i, c' i * ⟪z, v i⟫ = (WithLp.ofLp z).2 * Real.sqrt ((d : ℝ) + 1) := by
        have hterm : ∀ i, c' i * ⟪z, v i⟫ =
            -(((d : ℝ) + 1) / (d : ℝ) * Real.sqrt ((d : ℝ) / ((d : ℝ) + 1))) *
              ⟪(WithLp.ofLp z).1, c i • u i⟫ +
            (((d : ℝ) + 1) / (d : ℝ) * ((WithLp.ofLp z).2 / Real.sqrt ((d : ℝ) + 1))) * c i := fun i => by
          rw [hv_inner, inner_smul_right]; dsimp only [c']; ring
        simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← inner_sum, hsum0,
          inner_zero_right, mul_zero, zero_add, hdecomp.sum_weights]
        have hsq : ((d : ℝ) + 1) / Real.sqrt ((d : ℝ) + 1) = Real.sqrt ((d : ℝ) + 1) := by
          field_simp [(Real.sqrt_pos.mpr hd1_pos).ne']
          rw [Real.sq_sqrt hd1_pos.le]
        calc
          ((d : ℝ) + 1) / (d : ℝ) * ((WithLp.ofLp z).2 / Real.sqrt ((d : ℝ) + 1)) * (d : ℝ)
            = (WithLp.ofLp z).2 * (((d : ℝ) + 1) / Real.sqrt ((d : ℝ) + 1)) := by
              field_simp [hd_pos.ne']
          _ = (WithLp.ofLp z).2 * Real.sqrt ((d : ℝ) + 1) := by rw [hsq]
      have hprod_eq : ∏ i, f i ⟪z, v i⟫ ^ c' i =
          ENNReal.ofReal (Real.exp (-(WithLp.ofLp z).2 * Real.sqrt ((d : ℝ) + 1))) := by
        have hterm : ∀ i, f i ⟪z, v i⟫ ^ c' i = ENNReal.ofReal (Real.exp (-(c' i * ⟪z, v i⟫))) := fun i => by
          dsimp only [f]
          rw [indicator_of_mem (hge0 i), ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
            ← Real.exp_mul]
          congr 2; ring
        simp_rw [hterm]
        rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le), ← Real.exp_sum,
          Finset.sum_neg_distrib, hsum_inner]
        congr 2; ring
      rw [hprod_eq]
    · rw [indicator_of_notMem hcond]
      exact zero_le
  have hle1 : volume (K : Set E) * ENNReal.ofReal ((d : ℝ) ^ (-(d : ℝ) / 2) *
      ((d : ℝ) + 1) ^ (-((d : ℝ) + 1) / 2) * (Nat.factorial d : ℝ)) ≤ 1 := by
    rw [← lintegral_exp_cone K]
    exact (lintegral_mono hpt_le).trans hbl
  set C : ℝ := (d : ℝ) ^ (-(d : ℝ) / 2) * ((d : ℝ) + 1) ^ (-((d : ℝ) + 1) / 2) * (Nat.factorial d : ℝ)
  have hC_pos : 0 < C := by positivity
  have hinv : C⁻¹ = (d : ℝ) ^ ((d : ℝ) / 2) * ((d : ℝ) + 1) ^ (((d : ℝ) + 1) / 2) / (Nat.factorial d : ℝ) := by
    dsimp only [C]
    rw [mul_inv, mul_inv, ← Real.rpow_neg hd_pos.le, ← Real.rpow_neg hd1_pos.le]
    have h1 : -(-(d : ℝ) / 2) = (d : ℝ) / 2 := by ring
    have h2 : -(-((d : ℝ) + 1) / 2) = ((d : ℝ) + 1) / 2 := by ring
    rw [h1, h2, ← div_eq_mul_inv]
  rw [← hinv, ENNReal.ofReal_inv_of_pos hC_pos]
  have hC_ne0 : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.mpr hC_pos).ne'
  calc
    volume (K : Set E) = volume (K : Set E) * ENNReal.ofReal C * (ENNReal.ofReal C)⁻¹ := by
      rw [mul_assoc, ENNReal.mul_inv_cancel hC_ne0 ENNReal.ofReal_ne_top, mul_one]
    _ ≤ 1 * (ENNReal.ofReal C)⁻¹ := by gcongr
    _ = (ENNReal.ofReal C)⁻¹ := one_mul _

/-- **Ball's Volume Ratio Theorem (General / Simplex Bound, Ball, Lecture 6):**
every convex body `K` with nonempty interior has an affine image `e '' K` containing
`closedBall 0 1` whose volume is at most that of the regular `d`-simplex circumscribing
`closedBall 0 1`. -/
theorem ball_volume_ratio [Nontrivial E]
    (K : ConvexBody E) (hint : (interior (K : Set E)).Nonempty) :
    ∃ e : E ≃ᵃ[ℝ] E,
      closedBall (0 : E) 1 ⊆ e '' (K : Set E) ∧
      volume (e '' (K : Set E)) ≤
        ENNReal.ofReal ((Module.finrank ℝ E : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2) *
          ((Module.finrank ℝ E : ℝ) + 1) ^ (((Module.finrank ℝ E : ℝ) + 1) / 2) /
          (Nat.factorial (Module.finrank ℝ E) : ℝ)) := by
  obtain ⟨e, hJ⟩ := exists_affineEquiv_isJohnPosition K hint
  let eK : ConvexBody E :=
    ⟨e '' (K : Set E), K.convex.affine_image e.toAffineMap,
      K.isCompact.image e.continuous_of_finiteDimensional, K.nonempty.image e⟩
  have hvol := volume_le_simplex_bound_of_john_position eK hJ
  exact ⟨e, hJ.1, hvol⟩

/-- **Outer Minkowski Content Upper Bound from Inscribed Unit Ball:**
if `closedBall 0 1 ⊆ K` for a convex body `K`, then `K + t • B₁ ⊆ (1 + t) • K` for all `t > 0`,
and consequently `minkowskiSurfaceArea K ≤ d * volume K`. -/
theorem minkowskiSurfaceArea_le_finrank_mul_volume_of_closedBall_subset
    (K : ConvexBody E) (hB : closedBall (0 : E) 1 ⊆ (K : Set E)) :
    minkowskiSurfaceArea (K : Set E) ≤ (Module.finrank ℝ E : ℝ≥0∞) * volume (K : Set E) := by
  set d := Module.finrank ℝ E
  set V := volume (K : Set E)
  have hV_ne_top : V ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hsub : ∀ {t : ℝ}, 0 < t → (K : Set E) + t • closedBall (0 : E) 1 ⊆ (1 + t) • (K : Set E) := by
    intro t ht
    calc
      (K : Set E) + t • closedBall (0 : E) 1 ⊆ (K : Set E) + t • (K : Set E) :=
        Set.add_subset_add_left (Set.smul_set_mono hB)
      _ = (1 + t) • (K : Set E) := by
        rw [K.convex.add_smul zero_le_one ht.le, one_smul]
  have hdiff_le : ∀ {t : ℝ}, 0 < t →
      (volume ((K : Set E) + t • closedBall (0 : E) 1) - V) / ENNReal.ofReal t ≤
        ENNReal.ofReal (((1 + t) ^ d - 1) / t) * V := by
    intro t ht
    have hvol_le : volume ((K : Set E) + t • closedBall (0 : E) 1) ≤
        ENNReal.ofReal ((1 + t) ^ d) * V := by
      calc
        volume ((K : Set E) + t • closedBall (0 : E) 1)
          ≤ volume ((1 + t) • (K : Set E)) := measure_mono (hsub ht)
        _ = ENNReal.ofReal (|(1 + t) ^ d|) * V := by
            rw [Measure.addHaar_smul volume (1 + t) (K : Set E)]
        _ = ENNReal.ofReal ((1 + t) ^ d) * V := by
            rw [abs_of_pos (pow_pos (by linarith) d)]
    have hsub_le : volume ((K : Set E) + t • closedBall (0 : E) 1) - V ≤
        ENNReal.ofReal ((1 + t) ^ d - 1) * V := by
      have h1 : (1 : ℝ) ≤ (1 + t) ^ d := one_le_pow₀ (by linarith)
      have heq : ENNReal.ofReal ((1 + t) ^ d) * V =
          ENNReal.ofReal ((1 + t) ^ d - 1) * V + V := by
        rw [← add_one_mul, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (sub_nonneg.mpr h1) zero_le_one,
          sub_add_cancel]
      exact tsub_le_iff_right.mpr (hvol_le.trans_eq heq)
    have hdiv : ENNReal.ofReal ((1 + t) ^ d - 1) / ENNReal.ofReal t =
        ENNReal.ofReal (((1 + t) ^ d - 1) / t) :=
      (ENNReal.ofReal_div_of_pos ht).symm
    calc
      (volume ((K : Set E) + t • closedBall (0 : E) 1) - V) / ENNReal.ofReal t
        ≤ (ENNReal.ofReal ((1 + t) ^ d - 1) * V) / ENNReal.ofReal t := by gcongr
      _ = (ENNReal.ofReal ((1 + t) ^ d - 1) / ENNReal.ofReal t) * V := by
          rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, mul_assoc]
      _ = ENNReal.ofReal (((1 + t) ^ d - 1) / t) * V := by rw [hdiv]
  have hderiv_pow : HasDerivAt (fun t : ℝ => (1 + t) ^ d) (d : ℝ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).fun_pow d
  have hslope : Tendsto (fun t : ℝ => ((1 + t) ^ d - 1) / t) (𝓝[>] (0 : ℝ)) (𝓝 (d : ℝ)) := by
    have h := (hasDerivAt_iff_tendsto_slope_zero.mp hderiv_pow).mono_left
      (nhdsWithin_mono (0 : ℝ) (show Ioi (0 : ℝ) ⊆ ({0} : Set ℝ)ᶜ from fun _ hx => ne_of_gt hx))
    simpa [smul_eq_mul, inv_mul_eq_div] using h
  have htend : Tendsto (fun t : ℝ => ENNReal.ofReal (((1 + t) ^ d - 1) / t) * V)
      (𝓝[>] (0 : ℝ)) (𝓝 ((d : ℝ≥0∞) * V)) := by
    have h1 : Tendsto (fun t : ℝ => ENNReal.ofReal (((1 + t) ^ d - 1) / t))
        (𝓝[>] (0 : ℝ)) (𝓝 (d : ℝ≥0∞)) := by
      simpa [Function.comp_def, ENNReal.ofReal_natCast] using
        (ENNReal.continuous_ofReal.tendsto (d : ℝ)).comp hslope
    exact (ENNReal.Tendsto.mul_const h1 (Or.inr hV_ne_top))
  calc
    minkowskiSurfaceArea (K : Set E)
      = liminf (fun t : ℝ => (volume ((K : Set E) + t • closedBall (0 : E) 1) - V) / ENNReal.ofReal t)
          (𝓝[>] (0 : ℝ)) := rfl
    _ ≤ liminf (fun t : ℝ => ENNReal.ofReal (((1 + t) ^ d - 1) / t) * V) (𝓝[>] (0 : ℝ)) :=
        liminf_le_liminf (eventually_nhdsWithin_of_forall fun _ ht => hdiff_le ht)
    _ = (d : ℝ≥0∞) * V := htend.liminf_eq

/-- **Ball's Reverse Isoperimetric Inequality (Origin-Symmetric, Ball 1991, Lecture 6):**
every origin-symmetric convex body `K` with `0 ∈ interior K` in dimension `d ≥ 1` has a linear
image `T '' K` whose isoperimetric ratio is at most that of the `d`-cube `[-1, 1]^d`:
$$S(T K) \le 2 d\,\mathrm{vol}(T K)^{(d - 1) / d}.$$ -/
theorem ball_reverse_isoperimetric_symmetric [Nontrivial E]
    (K : ConvexBody E) (hsym : IsOriginSymmetric (K : Set E))
    (h0 : (0 : E) ∈ interior (K : Set E)) :
    ∃ T : E ≃ₗ[ℝ] E,
      minkowskiSurfaceArea (T '' (K : Set E)) ≤
        (2 * (Module.finrank ℝ E : ℝ≥0∞)) *
          volume (T '' (K : Set E)) ^ (((Module.finrank ℝ E - 1 : ℕ) : ℝ) / (Module.finrank ℝ E : ℝ)) := by
  set d := Module.finrank ℝ E
  have hd_pos : 1 ≤ d := Module.finrank_pos
  have hd_rpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd_pos
  obtain ⟨T, hB, hvol_le⟩ := ball_volume_ratio_symmetric K hsym h0
  let TK : ConvexBody E := mapLinear (T.toContinuousLinearMap) K
  have hTK_coe : (TK : Set E) = T '' (K : Set E) := by simp [TK]
  have hsurf := minkowskiSurfaceArea_le_finrank_mul_volume_of_closedBall_subset TK (hTK_coe ▸ hB)
  rw [hTK_coe] at hsurf
  set V := volume (T '' (K : Set E))
  have hV_rpow : V ^ (1 / (d : ℝ)) ≤ 2 := by
    calc
      V ^ (1 / (d : ℝ)) ≤ ((2 : ℝ≥0∞) ^ d) ^ (1 / (d : ℝ)) :=
        ENNReal.rpow_le_rpow hvol_le (by positivity)
      _ = 2 := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_one_div_cancel hd_rpos.ne',
          ENNReal.rpow_one]
  have hV_split : V = V ^ (1 / (d : ℝ)) * V ^ (((d - 1 : ℕ) : ℝ) / (d : ℝ)) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity)]
    have hsum : (1 : ℝ) / (d : ℝ) + ((d - 1 : ℕ) : ℝ) / (d : ℝ) = 1 := by
      rw [← add_div, Nat.cast_sub hd_pos, Nat.cast_one]
      field_simp [hd_rpos.ne']; ring
    rw [hsum, ENNReal.rpow_one]
  refine ⟨T, ?_⟩
  calc
    minkowskiSurfaceArea (T '' (K : Set E)) ≤ (d : ℝ≥0∞) * V := hsurf
    _ = (d : ℝ≥0∞) * (V ^ (1 / (d : ℝ)) * V ^ (((d - 1 : ℕ) : ℝ) / (d : ℝ))) := by rw [← hV_split]
    _ ≤ (d : ℝ≥0∞) * (2 * V ^ (((d - 1 : ℕ) : ℝ) / (d : ℝ))) := by gcongr
    _ = (2 * (d : ℝ≥0∞)) * V ^ (((d - 1 : ℕ) : ℝ) / (d : ℝ)) := by ring

/-- **Ball's Reverse Isoperimetric Inequality (General / Simplex Form, Ball 1991, Lecture 6):**
every convex body `K` with nonempty interior in dimension `d ≥ 1` has an affine image `e '' K`
whose isoperimetric ratio is at most that of the regular `d`-simplex:
$$S(e K) \le d \, V_\Delta^{1/d} \, \mathrm{vol}(e K)^{(d - 1) / d},$$
where $V_\Delta = d^{d/2} (d + 1)^{(d + 1)/2} / d!$. -/
theorem ball_reverse_isoperimetric [Nontrivial E]
    (K : ConvexBody E) (hint : (interior (K : Set E)).Nonempty) :
    ∃ e : E ≃ᵃ[ℝ] E,
      minkowskiSurfaceArea (e '' (K : Set E)) ≤
        (Module.finrank ℝ E : ℝ≥0∞) *
          ENNReal.ofReal ((Module.finrank ℝ E : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2) *
            ((Module.finrank ℝ E : ℝ) + 1) ^ (((Module.finrank ℝ E : ℝ) + 1) / 2) /
            (Nat.factorial (Module.finrank ℝ E) : ℝ)) ^ (1 / (Module.finrank ℝ E : ℝ)) *
          volume (e '' (K : Set E)) ^ (((Module.finrank ℝ E - 1 : ℕ) : ℝ) / (Module.finrank ℝ E : ℝ)) := by
  set d := Module.finrank ℝ E
  have hd_pos : 1 ≤ d := Module.finrank_pos
  have hd_rpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd_pos
  obtain ⟨e, hB, hvol_le⟩ := ball_volume_ratio K hint
  let eK : ConvexBody E :=
    ⟨e '' (K : Set E), K.convex.affine_image e.toAffineMap,
      K.isCompact.image e.continuous_of_finiteDimensional, K.nonempty.image e⟩
  have hsurf := minkowskiSurfaceArea_le_finrank_mul_volume_of_closedBall_subset eK hB
  set V := volume (e '' (K : Set E))
  have hV_split : V = V ^ (1 / (d : ℝ)) * V ^ (((d - 1 : ℕ) : ℝ) / (d : ℝ)) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity)]
    have hsum : (1 : ℝ) / (d : ℝ) + ((d - 1 : ℕ) : ℝ) / (d : ℝ) = 1 := by
      rw [← add_div, Nat.cast_sub hd_pos, Nat.cast_one]
      field_simp [hd_rpos.ne']; ring
    rw [hsum, ENNReal.rpow_one]
  refine ⟨e, ?_⟩
  calc
    minkowskiSurfaceArea (e '' (K : Set E)) ≤ (d : ℝ≥0∞) * V := hsurf
    _ = (d : ℝ≥0∞) * (V ^ (1 / (d : ℝ)) * V ^ (((d - 1 : ℕ) : ℝ) / (d : ℝ))) := by rw [← hV_split]
    _ = ((d : ℝ≥0∞) * V ^ (1 / (d : ℝ))) * V ^ (((d - 1 : ℕ) : ℝ) / (d : ℝ)) := by ring
    _ ≤ ((d : ℝ≥0∞) * ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) / 2) *
          ((d : ℝ) + 1) ^ (((d : ℝ) + 1) / 2) / (Nat.factorial d : ℝ)) ^ (1 / (d : ℝ))) *
          V ^ (((d - 1 : ℕ) : ℝ) / (d : ℝ)) := by
        gcongr

/-- **Barthe's Polar Volume Lower Bound in John's Position (Origin-Symmetric, Barthe 1998):**
for any origin-symmetric `K : ConvexBody E` in John's position in dimension `d ≥ 1`:
$$\frac{2^d}{d!} \le \mathrm{vol}(K^\circ),$$
with equality attained by the cube `K = [-1, 1]^d` (whose polar is the cross-polytope `B₁^d`). -/
theorem barthe_polar_volume_of_john_position_symmetric [Nontrivial E]
    (K : ConvexBody E) (hsym : IsOriginSymmetric (K : Set E))
    (hJ : IsJohnPosition (K : Set E)) :
    ENNReal.ofReal ((2 : ℝ) ^ Module.finrank ℝ E / (Nat.factorial (Module.finrank ℝ E) : ℝ)) ≤
      volume (polarBody (K : Set E)) := by
  set d := Module.finrank ℝ E
  obtain ⟨m, u, c, hdecomp, _, hsup⟩ := john_decomposition_of_john_position K hJ
  let f : Fin m → ℝ → ℝ := fun _ t => Real.exp (-|t|)
  have hf_cont : ∀ i, ContinuousOn (f i) Set.univ := fun _ =>
    (Real.continuous_exp.comp continuous_abs.neg).continuousOn
  have hf_pos : ∀ i, ∀ t ∈ (Set.univ : Set ℝ), 0 < f i t := fun _ _ _ => Real.exp_pos _
  have hf_int_pos : ∫ t in Ioi (0 : ℝ), Real.exp (-t) = 1 := by
    have h1 := integral_exp_neg_rpow zero_lt_one
    simp only [Real.rpow_one, div_one] at h1
    rw [h1]
    simpa using Real.Gamma_nat_eq_factorial 1
  have hf_int_on : IntegrableOn (fun t : ℝ => Real.exp (-|t|)) Set.univ volume := by
    have hpos : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) volume :=
      integrableOn_exp_neg_Ioi 0
    have hpos_abs : IntegrableOn (fun t : ℝ => Real.exp (-|t|)) (Ioi 0) volume :=
      hpos.congr_fun (fun t ht => by simp [abs_of_pos ht]) measurableSet_Ioi
    have hneg_abs : IntegrableOn (fun t : ℝ => Real.exp (-|t|)) (Iio 0) volume := by
      have hcomp := (Measure.measurePreserving_neg volume).integrableOn_comp_preimage
        (Homeomorph.neg ℝ).toMeasurableEquiv.measurableEmbedding (s := Ioi 0)
        (f := fun t : ℝ => Real.exp (-|t|))
      have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Ioi 0 = Iio 0 := by ext t; simp
      rw [hpre] at hcomp
      have h1 := hcomp.mpr hpos_abs
      simpa [Function.comp_def, abs_neg] using h1
    have hunion : IntegrableOn (fun t : ℝ => Real.exp (-|t|)) (Iio 0 ∪ Ioi 0) volume :=
      hneg_abs.union hpos_abs
    have hae : (Set.univ : Set ℝ) =ᵐ[volume] (Iio (0 : ℝ) ∪ Ioi 0 : Set ℝ) := by
      symm
      have hcompl : (Iio (0 : ℝ) ∪ Ioi 0)ᶜ = {0} := by
        ext t; simp
      rw [ae_eq_univ, hcompl, measure_singleton]
    exact hunion.congr_set_ae hae
  have hf_int_val : ∫ t in (Set.univ : Set ℝ), Real.exp (-|t|) = 2 := by
    have hae : (Iio (0 : ℝ) ∪ Ioi 0 : Set ℝ) =ᵐ[volume] Set.univ := by
      have hcompl : (Iio (0 : ℝ) ∪ Ioi 0)ᶜ = {0} := by
        ext t; simp
      rw [ae_eq_univ, hcompl, measure_singleton]
    rw [← setIntegral_congr_set hae, setIntegral_union
      (Set.disjoint_left.mpr fun t h1 h2 => lt_asymm h1 h2) measurableSet_Ioi
      (hf_int_on.mono_set (subset_univ _)) (hf_int_on.mono_set (subset_univ _))]
    have hpos_eq : ∫ t in Ioi (0 : ℝ), Real.exp (-|t|) = 1 := by
      rw [setIntegral_congr_fun measurableSet_Ioi
        (f := fun t => Real.exp (-|t|)) (g := fun t => Real.exp (-t))
        (fun t ht => by simp [abs_of_pos ht]), hf_int_pos]
    have hneg_eq : ∫ t in Iio (0 : ℝ), Real.exp (-|t|) = 1 := by
      rw [setIntegral_congr_set Iio_ae_eq_Iic]
      have hcomp := integral_comp_neg_Ioi (f := fun t : ℝ => Real.exp (-|t|)) 0
      simp only [neg_zero, abs_neg] at hcomp
      rw [← hcomp, hpos_eq]
    rw [hneg_eq, hpos_eq]; norm_num
  have hsup_bound : ∀ y : Fin m → ℝ,
      supportFn K (∑ i, (c i * y i) • u i) ≤ ∑ i, c i * |y i| := fun y => by
    rw [supportFn_le_iff]
    intro x hx
    rw [inner_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [inner_smul_right]
    have hupper : ⟪x, u i⟫ ≤ 1 := by rw [← hsup i]; exact inner_le_supportFn hx (u i)
    have hlower : -1 ≤ ⟪x, u i⟫ := by
      have := inner_le_supportFn (hsym x hx) (u i)
      rw [hsup i, inner_neg_left] at this; linarith
    have habs : |⟪x, u i⟫| ≤ 1 := abs_le.mpr ⟨hlower, hupper⟩
    calc
      c i * y i * ⟪x, u i⟫ ≤ |c i * y i * ⟪x, u i⟫| := le_abs_self _
      _ = c i * |y i| * |⟪x, u i⟫| := by
        rw [abs_mul, abs_mul, abs_of_pos (hdecomp.weight_pos i)]
      _ ≤ c i * |y i| * 1 :=
        mul_le_mul_of_nonneg_left habs (mul_nonneg (hdecomp.weight_pos i).le (abs_nonneg _))
      _ = c i * |y i| := mul_one _
  let H : E → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (-supportFn K z))
  have hdom : ∀ y : Fin m → ℝ, (∀ i, y i ∈ (Set.univ : Set ℝ)) →
      ∏ i, ENNReal.ofReal (f i (y i)) ^ c i ≤ H (∑ i, (c i * y i) • u i) := fun y _ => by
    have hlhs : ∏ i, ENNReal.ofReal (f i (y i)) ^ c i =
        ENNReal.ofReal (Real.exp (-∑ i, c i * |y i|)) := by
      have hterm : ∀ i, ENNReal.ofReal (f i (y i)) ^ c i =
          ENNReal.ofReal (Real.exp (-(c i * |y i|))) := fun i => by
        dsimp only [f]
        rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
        congr 2; ring
      simp_rw [hterm]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),
        ← Real.exp_sum, Finset.sum_neg_distrib]
    rw [hlhs]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg (hsup_bound y)))
  have hrev := reverse_brascamp_lieb_rankOne hdecomp (fun _ => isOpen_univ)
    (fun _ => isPreconnected_univ) (fun _ => ⟨0, trivial⟩) hf_cont hf_pos
    (fun _ => hf_int_on) hdom
  dsimp only [f] at hrev
  simp_rw [hf_int_val] at hrev
  have hlhs_2d : ∏ i : Fin m, ENNReal.ofReal 2 ^ c i = ENNReal.ofReal ((2 : ℝ) ^ d) := by
    have hterm : ∀ i, ENNReal.ofReal 2 ^ c i = ENNReal.ofReal ((2 : ℝ) ^ c i) := fun i =>
      ENNReal.ofReal_rpow_of_pos zero_lt_two
    simp_rw [hterm]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity),
      ← Real.rpow_sum_of_pos zero_lt_two, hdecomp.sum_weights, Real.rpow_natCast]
  rw [hlhs_2d] at hrev
  have hsup_nn : ∀ z : E, 0 ≤ supportFn K z := fun z => by
    have h0K : (0 : E) ∈ (K : Set E) := hJ.1 (Metric.mem_closedBall_self zero_le_one)
    simpa using inner_le_supportFn h0K z
  have hexp_eq : ∀ z : E,
      H z = ∫⁻ t in Ioi (0 : ℝ),
        ({p : E × ℝ | supportFn K p.1 < p.2}).indicator
          (fun p => ENNReal.ofReal (Real.exp (-p.2))) (z, t) := fun z => by
    have hset : ∫⁻ t in Ioi (0 : ℝ),
        ({p : E × ℝ | supportFn K p.1 < p.2}).indicator
          (fun p => ENNReal.ofReal (Real.exp (-p.2))) (z, t) =
        ∫⁻ t in Ioi (supportFn K z), ENNReal.ofReal (Real.exp (-t)) := by
      rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
      congr 1; ext t
      by_cases h1 : supportFn K z < t
      · have h0t : 0 < t := lt_of_le_of_lt (hsup_nn z) h1
        simp [indicator_of_mem (show (z, t) ∈ {p : E × ℝ | supportFn K p.1 < p.2} from h1),
          indicator_of_mem (mem_Ioi.mpr h0t), indicator_of_mem (mem_Ioi.mpr h1)]
      · by_cases h0t : 0 < t
        · simp [indicator_of_notMem (show (z, t) ∉ {p : E × ℝ | supportFn K p.1 < p.2} from h1),
            indicator_of_mem (mem_Ioi.mpr h0t), indicator_of_notMem (show t ∉ Ioi (supportFn K z) from h1)]
        · simp [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from h0t),
            indicator_of_notMem (show t ∉ Ioi (supportFn K z) from h1)]
    rw [hset]
    have h1 : ∫⁻ t in Ioi (supportFn K z), ENNReal.ofReal (Real.exp (-t)) =
        ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(s + supportFn K z))) := by
      rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
      have heq := lintegral_add_right_eq_self (μ := volume)
        (fun t : ℝ => (Ioi (supportFn K z)).indicator (fun u => ENNReal.ofReal (Real.exp (-u))) t)
        (supportFn K z)
      rw [← heq]
      congr 1; ext s
      by_cases hs : 0 < s
      · have hs' : supportFn K z < s + supportFn K z := by linarith
        simp [indicator_of_mem (mem_Ioi.mpr hs), indicator_of_mem (mem_Ioi.mpr hs')]
      · have hs' : ¬ supportFn K z < s + supportFn K z := by linarith
        simp [indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs),
          indicator_of_notMem (show s + supportFn K z ∉ Ioi (supportFn K z) from hs')]
    rw [h1]
    have hfac : ∀ s : ℝ, ENNReal.ofReal (Real.exp (-(s + supportFn K z))) =
        ENNReal.ofReal (Real.exp (-supportFn K z)) * ENNReal.ofReal (Real.exp (-s)) := fun s => by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2; ring
    simp_rw [hfac]
    have hexp_meas : Measurable (fun s : ℝ => ENNReal.ofReal (Real.exp (-s))) := by fun_prop
    rw [lintegral_const_mul _ hexp_meas,
      ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi 0)
        (ae_of_all _ fun _ => (Real.exp_pos _).le),
      hf_int_pos, ENNReal.ofReal_one, mul_one]
  have hH_le : ∫⁻ z : E, H z ≤ ENNReal.ofReal (Nat.factorial d : ℝ) * volume (polarBody (K : Set E)) := by
    let F : E → ℝ → ℝ≥0∞ := fun z t =>
      ({p : E × ℝ | supportFn K p.1 < p.2}).indicator
        (fun p => ENNReal.ofReal (Real.exp (-p.2))) (z, t)
    have hmeas_ind : Measurable (Function.uncurry F) := by
      have hopen : IsOpen {p : E × ℝ | supportFn K p.1 < p.2} :=
        isOpen_lt ((continuous_supportFn K).comp continuous_fst) continuous_snd
      have hfun : Measurable (fun p : E × ℝ => ENNReal.ofReal (Real.exp (-p.2))) := by fun_prop
      exact hfun.indicator hopen.measurableSet
    simp_rw [hexp_eq]
    change ∫⁻ z : E, ∫⁻ t in Ioi (0 : ℝ), F z t ≤ _
    rw [lintegral_lintegral_swap hmeas_ind.aemeasurable]
    have hslice : ∀ t : ℝ, 0 < t →
        ∫⁻ z : E, F z t ≤
          ENNReal.ofReal (t ^ (d : ℝ) * Real.exp (-t)) * volume (polarBody (K : Set E)) := fun t ht => by
      have hsub : {z : E | supportFn K z < t} ⊆ t • polarBody (K : Set E) := fun z hz => by
        refine ⟨t⁻¹ • z, ?_, by dsimp only; rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]⟩
        intro x hx
        rw [inner_smul_right, inv_mul_le_iff₀ ht, mul_one]
        exact (inner_le_supportFn hx z).trans hz.le
      have hopen : IsOpen {z : E | supportFn K z < t} :=
        isOpen_lt (continuous_supportFn K) continuous_const
      have heq_ind : ∀ z : E,
          F z t =
          ({z : E | supportFn K z < t}).indicator
            (fun _ => ENNReal.ofReal (Real.exp (-t))) z := fun z => by
        dsimp only [F]
        by_cases hz : supportFn K z < t <;> simp [hz]
      simp_rw [heq_ind]
      rw [lintegral_indicator_const hopen.measurableSet]
      calc
        ENNReal.ofReal (Real.exp (-t)) * volume {z : E | supportFn K z < t}
          ≤ ENNReal.ofReal (Real.exp (-t)) * volume (t • polarBody (K : Set E)) := by
            gcongr
        _ = ENNReal.ofReal (Real.exp (-t)) *
              (ENNReal.ofReal (t ^ d) * volume (polarBody (K : Set E))) := by
            rw [Measure.addHaar_smul volume t (polarBody (K : Set E)), abs_of_pos (pow_pos ht d)]
        _ = ENNReal.ofReal (t ^ (d : ℝ) * Real.exp (-t)) * volume (polarBody (K : Set E)) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm (Real.exp (-t)),
              Real.rpow_natCast]
    calc
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ z : E, F z t
        ≤ ∫⁻ t in Ioi (0 : ℝ),
            ENNReal.ofReal (t ^ (d : ℝ) * Real.exp (-t)) * volume (polarBody (K : Set E)) :=
          setLIntegral_mono_ae' measurableSet_Ioi (ae_of_all _ fun t ht => hslice t ht)
      _ = (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (d : ℝ) * Real.exp (-t))) *
            volume (polarBody (K : Set E)) :=
          lintegral_mul_const _ (by fun_prop)
      _ = ENNReal.ofReal (Nat.factorial d : ℝ) * volume (polarBody (K : Set E)) := by
          congr 1
          have hint_gam : IntegrableOn (fun t : ℝ => t ^ (d : ℝ) * Real.exp (-t)) (Ioi 0) volume := by
            have h1 := integrableOn_Ioi_rpow_mul_exp_neg_mul (q := (d : ℝ)) (b := 1)
              (by linarith [Nat.cast_nonneg (α := ℝ) d]) zero_lt_one
            simpa using h1
          rw [← ofReal_integral_eq_lintegral_ofReal hint_gam]
          · have hg := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := (d : ℝ)) (b := 1)
              zero_lt_one (by linarith [Nat.cast_nonneg (α := ℝ) d]) zero_lt_one
            simp only [Real.rpow_one, one_mul, neg_mul, div_one, Real.one_rpow,
              mul_one, Real.Gamma_nat_eq_factorial] at hg
            rw [hg]
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
  have hcomb : ENNReal.ofReal ((2 : ℝ) ^ d) ≤
      ENNReal.ofReal (Nat.factorial d : ℝ) * volume (polarBody (K : Set E)) :=
    hrev.trans hH_le
  have hfac_pos : (0 : ℝ) < (Nat.factorial d : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos d)
  rw [ENNReal.ofReal_div_of_pos hfac_pos, ENNReal.div_le_iff_le_mul
    (Or.inl (ENNReal.ofReal_pos.mpr hfac_pos).ne') (Or.inl ENNReal.ofReal_ne_top)]
  rwa [mul_comm]

/-- **Barthe's Outer Volume Ratio Theorem (Origin-Symmetric, Barthe 1998):**
every origin-symmetric convex body `K` with `0 ∈ interior K` in dimension `d ≥ 1` has a linear
image `T '' K` contained in the unit Euclidean ball `closedBall 0 1` with
$$\frac{2^d}{d!} \le \mathrm{vol}(T K)$$
(matching the cross-polytope `B₁^d`). -/
theorem barthe_outer_volume_ratio_symmetric [Nontrivial E]
    (K : ConvexBody E) (hsym : IsOriginSymmetric (K : Set E))
    (h0 : (0 : E) ∈ interior (K : Set E)) :
    ∃ T : E ≃ₗ[ℝ] E,
      T '' (K : Set E) ⊆ closedBall (0 : E) 1 ∧
      ENNReal.ofReal ((2 : ℝ) ^ Module.finrank ℝ E / (Nat.factorial (Module.finrank ℝ E) : ℝ)) ≤
        volume (T '' (K : Set E)) := by
  let Kpol : ConvexBody E := bodyPolar K h0
  have hKpol_coe : (Kpol : Set E) = polarBody (K : Set E) := coe_bodyPolar (K : Set E) h0
  have hKpol_sym : IsOriginSymmetric (Kpol : Set E) := by
    rw [hKpol_coe]
    intro z hz x hx
    have := hz (-x) (hsym x hx)
    rwa [inner_neg_left, ← inner_neg_right] at this
  have h0_Kpol : (0 : E) ∈ interior (Kpol : Set E) := by
    rw [hKpol_coe]
    exact zero_mem_interior_polarBody_of_isBounded K.isCompact.isBounded
  obtain ⟨S, hJ⟩ := exists_linearEquiv_isJohnPosition_of_isOriginSymmetric Kpol hKpol_sym h0_Kpol
  let SKpol : ConvexBody E := mapLinear S.toContinuousLinearMap Kpol
  have hSKpol_coe : (SKpol : Set E) = S '' (Kpol : Set E) := by simp [SKpol]
  have hSKpol_sym : IsOriginSymmetric (SKpol : Set E) := by
    rw [hSKpol_coe]
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨-z, hKpol_sym z hz, map_neg S z⟩
  have hvol := barthe_polar_volume_of_john_position_symmetric SKpol hSKpol_sym (hSKpol_coe ▸ hJ)
  let Sadj : E ≃ₗ[ℝ] E := LinearEquiv.ofLinearMap (LinearMap.adjoint S.toLinearMap)
    (LinearMap.adjoint S.symm.toLinearMap)
    (by
      ext x
      apply ext_inner_right ℝ
      intro y
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left]
      simp)
    (by
      ext x
      apply ext_inner_right ℝ
      intro y
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left]
      simp)
  let T : E ≃ₗ[ℝ] E := Sadj.symm
  have hpol_eq : polarBody (SKpol : Set E) = T '' (K : Set E) := by
    have hK_bipolar : polarBody (Kpol : Set E) = (K : Set E) := by
      rw [hKpol_coe]
      exact polarBody_polarBody K.convex K.isCompact.isClosed (interior_subset h0)
    ext w
    simp only [hSKpol_coe, mem_image]
    constructor
    · intro hw
      have hSw : Sadj w ∈ polarBody (Kpol : Set E) := by
        intro z hz
        have hinner : ⟪z, Sadj w⟫ = ⟪S z, w⟫ := by
          change ⟪z, LinearMap.adjoint S.toLinearMap w⟫ = ⟪S.toLinearMap z, w⟫
          exact LinearMap.adjoint_inner_right S.toLinearMap z w
        rw [hinner]
        exact hw (S z) ⟨z, hz, rfl⟩
      rw [hK_bipolar] at hSw
      exact ⟨Sadj w, hSw, Sadj.symm_apply_apply w⟩
    · rintro ⟨x, hx, rfl⟩
      rintro _ ⟨z, hz, rfl⟩
      have hinner : ⟪S z, T x⟫ = ⟪z, x⟫ := by
        have h1 : ⟪S.toLinearMap z, T x⟫ = ⟪z, LinearMap.adjoint S.toLinearMap (T x)⟫ :=
          (LinearMap.adjoint_inner_right S.toLinearMap z (T x)).symm
        have h2 : LinearMap.adjoint S.toLinearMap (T x) = x := Sadj.apply_symm_apply x
        simpa [h2] using h1
      rw [hinner]
      rw [← hK_bipolar] at hx
      exact hx z hz
  have hsub_ball : T '' (K : Set E) ⊆ closedBall (0 : E) 1 := by
    rw [← hpol_eq]
    exact (polarBody_subset_closedBall_of_closedBall_subset zero_lt_one (hSKpol_coe ▸ hJ.1)).trans
      (by simp)
  exact ⟨T, hsub_ball, hpol_eq ▸ hvol⟩

/-- **John-Position Gaussian Measure Upper Bound (Ball, Lecture 6 & 9):**
if `K : ConvexBody E` is origin-symmetric and in John's position in dimension `d ≥ 1`, then for
every `r > 0`:
$$\int_{r K} (2\pi)^{-d/2} e^{-\|x\|^2 / 2}\,dx
  \le \left(\int_{-r}^r (2\pi)^{-1/2} e^{-t^2 / 2}\,dt\right)^d.$$
This directly bridges Brascamp–Lieb to the lower bound on Gaussian width / norm expectation
needed for Dvoretzky's theorem. -/
theorem john_position_gaussian_measure_le [Nontrivial E]
    (K : ConvexBody E) (hsym : IsOriginSymmetric (K : Set E))
    (hJ : IsJohnPosition (K : Set E)) {r : ℝ} (hr : 0 < r) :
    ∫⁻ x in r • (K : Set E), ENNReal.ofReal (stdGaussianDensity x) ≤
      ENNReal.ofReal (∫ t in Icc (-r) r, gaussianPDFReal 0 1 t) ^ Module.finrank ℝ E := by
  set d := Module.finrank ℝ E
  obtain ⟨m, u, c, hdecomp, _, hsup⟩ := john_decomposition_of_john_position K hJ
  let γ : ℝ → ℝ := gaussianPDFReal 0 1
  let f : Fin m → ℝ → ℝ≥0∞ := fun _ =>
    (Icc (-r) r).indicator (fun t => ENNReal.ofReal (γ t))
  have hf : ∀ i, Measurable (f i) := fun _ =>
    (measurable_gaussianPDFReal 0 1).ennreal_ofReal.indicator measurableSet_Icc
  have hle : (r • (K : Set E)).indicator (fun x => ENNReal.ofReal (stdGaussianDensity x)) ≤
      fun x => ∏ i, f i ⟪x, u i⟫ ^ c i := by
    intro x
    by_cases hx : x ∈ r • (K : Set E)
    · rw [indicator_of_mem hx]
      rcases hx with ⟨k, hk, rfl⟩
      have hmem : ∀ i, ⟪r • k, u i⟫ ∈ Icc (-r) r := fun i => by
        rw [inner_smul_left, RCLike.conj_to_real]
        have hupper : ⟪k, u i⟫ ≤ 1 := by rw [← hsup i]; exact inner_le_supportFn hk (u i)
        have hlower : -1 ≤ ⟪k, u i⟫ := by
          have := inner_le_supportFn (hsym k hk) (u i)
          rw [hsup i, inner_neg_left] at this; linarith
        exact ⟨by nlinarith, by nlinarith⟩
      have hprod_eq : ∏ i, f i ⟪r • k, u i⟫ ^ c i = ENNReal.ofReal (stdGaussianDensity (r • k)) := by
        have hterm : ∀ i, f i ⟪r • k, u i⟫ ^ c i = ENNReal.ofReal (γ ⟪r • k, u i⟫ ^ c i) := fun i => by
          dsimp only [f]
          rw [indicator_of_mem (hmem i),
            ENNReal.ofReal_rpow_of_pos (gaussianPDFReal_pos 0 1 _ one_ne_zero)]
        simp_rw [hterm]
        rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ =>
          Real.rpow_nonneg (gaussianPDFReal_nonneg 0 1 _) _)]
        congr 1
        have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
        have hγ_form : ∀ t : ℝ, γ t = (2 * Real.pi) ^ (-(1 : ℝ) / 2) * Real.exp (-(t ^ 2) / 2) := fun t => by
          rw [show γ t = gaussianPDFReal 0 1 t from rfl, gaussianPDFReal_def]
          simp only [NNReal.coe_one, mul_one, sub_zero]
          congr 1
          rw [Real.sqrt_eq_rpow, ← Real.rpow_neg h2pi_pos.le]
          ring_nf
        have hterm2 : ∀ i, γ ⟪r • k, u i⟫ ^ c i =
            (2 * Real.pi) ^ (-c i / 2) * Real.exp (-(c i * ⟪r • k, u i⟫ ^ 2) / 2) := fun i => by
          rw [hγ_form, Real.mul_rpow (by positivity) (Real.exp_pos _).le,
            ← Real.rpow_mul h2pi_pos.le, ← Real.exp_mul]
          congr 1
          · congr 1; ring
          · congr 1; ring
        have hprod_real : ∏ i, γ ⟪r • k, u i⟫ ^ c i = stdGaussianDensity (r • k) := by
          simp_rw [hterm2, Finset.prod_mul_distrib, ← Real.exp_sum]
          rw [← Real.rpow_sum_of_pos h2pi_pos]
          unfold stdGaussianDensity
          congr 1
          · congr 1
            rw [← Finset.sum_div, Finset.sum_neg_distrib, hdecomp.sum_weights]
          · congr 1
            rw [← Finset.sum_div, Finset.sum_neg_distrib, hdecomp.norm_sq_eq_sum (r • k)]
        exact hprod_real
      dsimp only
      rw [hprod_eq]
    · simp [indicator_of_notMem hx]
  have hrK_meas : MeasurableSet (r • (K : Set E)) := (K.isCompact.smul r).isClosed.measurableSet
  have hint_f : ∀ i, ∫⁻ t : ℝ, f i t = ENNReal.ofReal (∫ t in Icc (-r) r, γ t) := fun _ => by
    dsimp only [f]
    rw [lintegral_indicator measurableSet_Icc,
      ← ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal 0 1).integrableOn
        (ae_of_all _ (gaussianPDFReal_nonneg 0 1))]
  have hI_nn : 0 ≤ ∫ t in Icc (-r) r, γ t :=
    setIntegral_nonneg measurableSet_Icc fun _ _ => gaussianPDFReal_nonneg 0 1 _
  calc
    ∫⁻ x in r • (K : Set E), ENNReal.ofReal (stdGaussianDensity x)
      = ∫⁻ x, (r • (K : Set E)).indicator (fun x => ENNReal.ofReal (stdGaussianDensity x)) x :=
        (lintegral_indicator hrK_meas _).symm
    _ ≤ ∫⁻ x, ∏ i, f i ⟪x, u i⟫ ^ c i := lintegral_mono hle
    _ ≤ ∏ i, (∫⁻ t : ℝ, f i t) ^ c i := brascamp_lieb_rankOne hdecomp hf
    _ = ∏ i, ENNReal.ofReal (∫ t in Icc (-r) r, γ t) ^ c i := by simp_rw [hint_f]
    _ = ENNReal.ofReal (∫ t in Icc (-r) r, γ t) ^ (∑ i, c i) := by
        by_cases h0 : ∫ t in Icc (-r) r, γ t = 0
        · rw [h0, ENNReal.ofReal_zero, hdecomp.sum_weights, ENNReal.rpow_natCast,
            zero_pow Module.finrank_pos.ne']
          have hne : Nonempty (Fin m) := by
            by_contra hempty
            rw [not_nonempty_iff] at hempty
            have hsum0 := hdecomp.sum_weights
            simp at hsum0
            exact (Nat.cast_pos (α := ℝ).mpr Module.finrank_pos).ne' hsum0.symm
          obtain ⟨i₀⟩ := hne
          exact Finset.prod_eq_zero (Finset.mem_univ i₀)
            (ENNReal.zero_rpow_of_pos (hdecomp.weight_pos i₀))
        · have hpos : 0 < ∫ t in Icc (-r) r, γ t := lt_of_le_of_ne hI_nn (Ne.symm h0)
          exact (ennreal_rpow_sum_of_pos Finset.univ (ENNReal.ofReal_pos.mpr hpos)
            ENNReal.ofReal_ne_top c).symm
    _ = ENNReal.ofReal (∫ t in Icc (-r) r, γ t) ^ d := by
        rw [hdecomp.sum_weights, ENNReal.rpow_natCast]

end Applications

end

end ConvexGeom
