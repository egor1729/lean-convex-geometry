/-
Copyright (c) 2026 Yegor Gorodzha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yegor Gorodzha
-/
module

public import ConvexGeom.Asymptotic.BrascampLieb
public import ConvexGeom.Asymptotic.SphericalIntegration
public import ConvexGeom.Volume.BrunnMinkowski
public import ConvexGeom.Volume.CoveringNumbers
public import ConvexGeom.Volume.Symmetrization
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Real

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Gaussian and Spherical Concentration, Johnson–Lindenstrauss, and Dvoretzky

This module develops the probabilistic and concentration-of-measure pillars of asymptotic convex
geometry using Mathlib's `ProbabilityTheory.stdGaussian`: density representation, polar
factorization, Gaussian width, Maurey–Prékopa–Leindler concentration, spherical concentration,
the Johnson–Lindenstrauss lemma, and Dvoretzky's theorem.

## Main definitions

* `ConvexGeom.stdGaussianRadial`: radial distribution of `ProbabilityTheory.stdGaussian E` on
  `Set.Ioi (0 : ℝ)`.
* `ConvexGeom.gaussianWidth`: Gaussian width `∫ x, supportFn K x ∂ProbabilityTheory.stdGaussian E`.

## Main statements

* `ConvexGeom.stdGaussian_eq_withDensity`: bridges Mathlib's `ProbabilityTheory.stdGaussian E` to
  the explicit Lebesgue density `(2 * π) ^ (-d / 2) * exp (-‖x‖² / 2)`.
* `ConvexGeom.measurePreserving_homeomorphUnitSphereProd_stdGaussian`: polar factorization of
  `ProbabilityTheory.stdGaussian E` into `sphereProb volume` and `stdGaussianRadial E`.
* `ConvexGeom.gaussianWidth_eq_integral_norm_mul_meanWidth`: exact proportionality between Gaussian
  width and mean width.
* `ConvexGeom.gaussian_lipschitz_concentration_mean`,
  `ConvexGeom.gaussian_lipschitz_concentration_median`: Gaussian concentration for Lipschitz
  functions.
* `ConvexGeom.spherical_lipschitz_concentration_median`: spherical concentration around a median.
* `ConvexGeom.johnson_lindenstrauss`: Johnson–Lindenstrauss dimensionality reduction lemma.
* `ConvexGeom.milman_gaussian_dvoretzky`, `ConvexGeom.dvoretzky_theorem`: Milman's probabilistic
  Dvoretzky theorem and Dvoretzky's theorem on almost-Euclidean sections.

## References

* K. Ball, *An Elementary Introduction to Modern Convex Geometry*, Lectures 7–9 [ball1997].
* M. Ledoux, *The Concentration of Measure Phenomenon* [ledoux2001].
* S. Artstein-Avidan, A. Giannopoulos, and V. D. Milman, *Asymptotic Geometric Analysis, Part I*
  [agm2015].
-/

open MeasureTheory Set Filter Metric ProbabilityTheory
open scoped RealInnerProductSpace ENNReal NNReal Pointwise Topology

namespace ConvexGeom

public section

/-! ### 1. Standard Gaussian Probability Measure and Orthogonal Invariance -/

section StdGaussian

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- Any linear isometry equivalence `U : E ≃ₗᵢ[ℝ] F` preserves the standard Gaussian measure. -/
theorem measurePreserving_linearIsometryEquiv_stdGaussian (U : E ≃ₗᵢ[ℝ] F) :
    MeasurePreserving U (stdGaussian E) (stdGaussian F) :=
  ⟨U.continuous.measurable, stdGaussian_map U⟩

/-- Product Gaussian measure on `Fin d → ℝ` matches `stdGaussian (EuclideanSpace ℝ (Fin d))` via
`WithLp.ofLp`. -/
theorem measurePreserving_ofLp_stdGaussian (d : ℕ) :
    MeasurePreserving (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Fin d → ℝ)
      (stdGaussian (EuclideanSpace ℝ (Fin d)))
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  refine ⟨(MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurable, ?_⟩
  rw [← map_pi_eq_stdGaussian,
    Measure.map_map (f := WithLp.toLp 2) (g := WithLp.ofLp)
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurable
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable]
  exact Measure.map_id

/-- Pushing `stdGaussian E` forward along an orthonormal basis `b : OrthonormalBasis (Fin d) ℝ E`
yields `d` i.i.d. standard 1D Gaussians `Measure.pi (fun _ : Fin d => gaussianReal 0 1)`. -/
theorem measurePreserving_orthonormalBasis_stdGaussian {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ E) :
    MeasurePreserving (fun x : E => WithLp.ofLp (b.repr x))
      (stdGaussian E) (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) :=
  (measurePreserving_ofLp_stdGaussian d).comp
    (measurePreserving_linearIsometryEquiv_stdGaussian b.repr)

/-- On `Fin d → ℝ`, the product of `d` standard 1D Gaussians equals `volume.withDensity` of the
product Gaussian density. -/
private lemma pi_gaussianReal_eq_withDensity (d : ℕ) :
    Measure.pi (fun _ : Fin d => gaussianReal 0 1) =
      volume.withDensity (fun x : Fin d → ℝ =>
        ENNReal.ofReal (∏ i : Fin d, gaussianPDFReal 0 1 (x i))) := by
  have hmeas_prod : Measurable (fun x : Fin d → ℝ =>
      ENNReal.ofReal (∏ i : Fin d, gaussianPDFReal 0 1 (x i))) :=
    ENNReal.measurable_ofReal.comp
      (Finset.measurable_fun_prod Finset.univ fun i _ =>
        (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i))
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hind : ∀ x : Fin d → ℝ,
      (Set.univ.pi s).indicator (fun y =>
        ENNReal.ofReal (∏ i : Fin d, gaussianPDFReal 0 1 (y i))) x =
        ∏ i : Fin d, (s i).indicator (fun t => ENNReal.ofReal (gaussianPDFReal 0 1 t)) (x i) :=
          fun x => by
    by_cases hx : x ∈ Set.univ.pi s
    · rw [indicator_of_mem hx,
        ENNReal.ofReal_prod_of_nonneg (fun _ _ => gaussianPDFReal_nonneg 0 1 _)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [indicator_of_mem (hx i (mem_univ i))]
    · rw [indicator_of_notMem hx]
      simp only [mem_univ_pi, not_forall] at hx
      obtain ⟨i₀, hi₀⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i₀) (by rw [indicator_of_notMem hi₀])).symm
  simp_rw [hind]
  have hm_g : Measurable (fun t : ℝ => ENNReal.ofReal (gaussianPDFReal 0 1 t)) :=
    ENNReal.measurable_ofReal.comp (measurable_gaussianPDFReal 0 1)
  rw [lintegral_pi_prod_eq_prod _ fun i => hm_g.indicator (hs i)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [lintegral_indicator (hs i), gaussianReal_apply 0 one_ne_zero (s i)]
  rfl

private lemma prod_gaussianPDFReal_eq_stdGaussianDensity (d : ℕ) (x : Fin d → ℝ) :
    (∏ i : Fin d, gaussianPDFReal 0 1 (x i)) =
      stdGaussianDensity (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) := by
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 : ∀ t : ℝ, gaussianPDFReal 0 1 t =
      (2 * Real.pi) ^ (-(1 : ℝ) / 2) * Real.exp (-(t ^ 2) / 2) := fun t => by
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg h2pi_pos.le]
    ring_nf
  simp_rw [h1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum]
  rw [← Real.rpow_natCast, ← Real.rpow_mul h2pi_pos.le]
  unfold stdGaussianDensity
  rw [finrank_euclideanSpace_fin, EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  congr 1
  · congr 1; ring
  · congr 1
    rw [← Finset.sum_div, Finset.sum_neg_distrib]

private lemma stdGaussian_euclideanSpace_eq_withDensity (d : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin d)) =
      volume.withDensity (fun x => ENNReal.ofReal (stdGaussianDensity x)) := by
  have hmeas : Measurable (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable
  rw [← map_pi_eq_stdGaussian, pi_gaussianReal_eq_withDensity d]
  ext s hs
  rw [Measure.map_apply hmeas hs, withDensity_apply _ (hs.preimage hmeas),
    withDensity_apply _ hs, ← lintegral_indicator hs, ← lintegral_indicator (hs.preimage hmeas),
    ← (PiLp.volume_preserving_toLp (Fin d)).lintegral_comp_emb
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding]
  refine lintegral_congr fun x => ?_
  by_cases hx : WithLp.toLp 2 x ∈ s
  · simp [indicator_of_mem hx, indicator_of_mem (show x ∈ WithLp.toLp 2 ⁻¹' s from hx),
      prod_gaussianPDFReal_eq_stdGaussianDensity d x]
  · simp [indicator_of_notMem hx, indicator_of_notMem (show x ∉ WithLp.toLp 2 ⁻¹' s from hx)]

/-- Mathlib's `ProbabilityTheory.stdGaussian E` equals `volume.withDensity` of the standard
Gaussian density `(2 * π) ^ (-d / 2) * exp (-‖x‖² / 2)`. -/
theorem stdGaussian_eq_withDensity :
    stdGaussian E = volume.withDensity (fun x => ENNReal.ofReal (stdGaussianDensity x)) := by
  let U : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃ₗᵢ[ℝ] E :=
    (stdOrthonormalBasis ℝ E).repr.symm
  rw [← stdGaussian_map U, stdGaussian_euclideanSpace_eq_withDensity]
  ext s hs
  rw [Measure.map_apply U.continuous.measurable hs,
    withDensity_apply _ (hs.preimage U.continuous.measurable), withDensity_apply _ hs,
    ← lintegral_indicator hs, ← lintegral_indicator (hs.preimage U.continuous.measurable),
    ← U.measurePreserving.lintegral_comp_emb U.toHomeomorph.toMeasurableEquiv.measurableEmbedding]
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) =
      Module.finrank ℝ E := U.toLinearEquiv.finrank_eq
  have hdens : ∀ x, stdGaussianDensity (U x) = stdGaussianDensity x := fun x => by
    unfold stdGaussianDensity
    rw [hdim, U.norm_map]
  refine lintegral_congr fun x => ?_
  by_cases hx : U x ∈ s
  · simp [indicator_of_mem hx, indicator_of_mem (show x ∈ U ⁻¹' s from hx), hdens x]
  · simp [indicator_of_notMem hx, indicator_of_notMem (show x ∉ U ⁻¹' s from hx)]

/-- Computing Lebesgue integrals against `stdGaussian E`. -/
lemma lintegral_stdGaussian {f : E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂stdGaussian E = ∫⁻ x, ENNReal.ofReal (stdGaussianDensity x) * f x := by
  have hm : Measurable (fun x : E => ENNReal.ofReal (stdGaussianDensity x)) :=
    ENNReal.measurable_ofReal.comp measurable_stdGaussianDensity
  rw [stdGaussian_eq_withDensity, lintegral_withDensity_eq_lintegral_mul _ hm hf]
  rfl

/-- Computing Bochner integrals against `stdGaussian E`. -/
lemma integral_stdGaussian {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E → G) :
    ∫ x, f x ∂stdGaussian E = ∫ x, stdGaussianDensity x • f x := by
  have hm : Measurable (fun x : E => ENNReal.ofReal (stdGaussianDensity x)) :=
    ENNReal.measurable_ofReal.comp measurable_stdGaussianDensity
  rw [stdGaussian_eq_withDensity, integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only
  rw [ENNReal.toReal_ofReal (stdGaussianDensity_nonneg x)]

/-- Integrability criterion with respect to `stdGaussian E`. -/
lemma integrable_stdGaussian_iff {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → G} :
    Integrable f (stdGaussian E) ↔ Integrable (fun x => stdGaussianDensity x • f x) volume := by
  have hm : Measurable (fun x : E => ENNReal.ofReal (stdGaussianDensity x)) :=
    ENNReal.measurable_ofReal.comp measurable_stdGaussianDensity
  have h1 := integrable_withDensity_iff_integrable_smul₀'
    (μ := (volume : Measure E))
    (f := fun x => ENNReal.ofReal (stdGaussianDensity x))
    hm.aemeasurable
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) (g := f)
  simpa [stdGaussian_eq_withDensity, ENNReal.toReal_ofReal (stdGaussianDensity_nonneg _)] using h1

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Given any two unit vectors `u, v : E`, there exists a self-adjoint linear isometry equivalence
`Q : E ≃ₗᵢ[ℝ] E` (`Q.symm = Q`) sending `u` to `v`. -/
lemma exists_selfAdjoint_linearIsometryEquiv_map_eq {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∃ Q : E ≃ₗᵢ[ℝ] E, Q u = v ∧ Q.symm = Q := by
  by_cases huv : u = v
  · exact ⟨LinearIsometryEquiv.refl ℝ E, huv, rfl⟩
  · have hne : u - v ≠ 0 := sub_ne_zero.mpr huv
    have hnorm_pos : 0 < ‖u - v‖ := norm_pos_iff.mpr hne
    let w : E := ‖u - v‖⁻¹ • (u - v)
    have hw : ‖w‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm_pos),
        inv_mul_cancel₀ hnorm_pos.ne']
    refine ⟨reflectHyperplane hw, ?_, reflectHyperplane_symm hw⟩
    rw [reflectHyperplane_apply]
    have hinner : 2 * ⟪u, u - v⟫ = ‖u - v‖ ^ 2 := by
      rw [norm_sub_sq_real, hu, hv, inner_sub_right, real_inner_self_eq_norm_sq, hu]
      ring
    have hcoeff : 2 * ⟪u, w⟫ = ‖u - v‖ := by
      dsimp only [w]
      rw [inner_smul_right, ← mul_assoc, mul_comm 2 ‖u - v‖⁻¹, mul_assoc, hinner]
      field_simp [hnorm_pos.ne']
    rw [hcoeff]
    dsimp only [w]
    rw [smul_smul, mul_inv_cancel₀ hnorm_pos.ne', one_smul, sub_sub_cancel]

/-- **1D Projection of Standard Gaussian:** for any unit vector `u ∈ E` (`‖u‖ = 1`), the linear
functional `x ↦ ⟪x, u⟫` pushes `stdGaussian E` forward to `gaussianReal 0 1`. -/
theorem measurePreserving_inner_stdGaussian {u : E} (hu : ‖u‖ = 1) :
    MeasurePreserving (fun x : E => ⟪x, u⟫) (stdGaussian E) (gaussianReal 0 1) := by
  have : Nontrivial E := ⟨⟨u, 0, by intro h; simp [h] at hu⟩⟩
  set d := Module.finrank ℝ E
  have hd : 0 < d := Module.finrank_pos
  let i0 : Fin d := ⟨0, hd⟩
  let b := stdOrthonormalBasis ℝ E
  have hb0 : ‖b i0‖ = 1 := b.orthonormal.1 i0
  obtain ⟨Q, hQu, hQsymm⟩ := exists_selfAdjoint_linearIsometryEquiv_map_eq hb0 hu
  have hmp1 : MeasurePreserving Q (stdGaussian E) (stdGaussian E) :=
    measurePreserving_linearIsometryEquiv_stdGaussian Q
  have hmp2 : MeasurePreserving (fun x : E => WithLp.ofLp (b.repr x))
      (stdGaussian E) (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) :=
    measurePreserving_orthonormalBasis_stdGaussian b
  have hmp3 : MeasurePreserving (Function.eval i0)
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) (gaussianReal 0 1) :=
    measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) i0
  have hcomp := (hmp3.comp hmp2).comp hmp1
  have hfun : ((Function.eval i0 ∘ (fun x : E => WithLp.ofLp (b.repr x))) ∘ Q) =
      (fun x : E => ⟪x, u⟫) := by
    ext x
    simp only [Function.comp_apply, Function.eval]
    change (b.repr (Q x)) i0 = ⟪x, u⟫
    rw [b.repr_apply_apply, ← hQu]
    have hQinv : Q (Q x) = x := by
      have := Q.symm_apply_apply x
      rwa [hQsymm] at this
    have h1 := Q.inner_map_map (Q x) (b i0)
    rw [hQinv] at h1
    rw [h1, real_inner_comm]
  rwa [hfun] at hcomp

/-- **Linear Combination of i.i.d. Standard Gaussians:** for any `z : Fin k → ℝ` with
`∑ j, (z j)^2 = 1`, the random vector `∑ j, z j • g j` (where `g : Fin k → E` is drawn from
`Measure.pi (fun _ => stdGaussian E)`) has exact law `stdGaussian E`. -/
theorem measurePreserving_linearComb_stdGaussian {k : ℕ} {z : Fin k → ℝ}
    (hz : ∑ j : Fin k, z j ^ 2 = 1) :
    MeasurePreserving (fun g : Fin k → E => ∑ j : Fin k, z j • g j)
      (Measure.pi (fun _ : Fin k => stdGaussian E)) (stdGaussian E) := by
  have hk_pos : 0 < k := by
    by_contra hk0
    push Not at hk0
    have hk_eq : k = 0 := Nat.eq_zero_of_le_zero hk0
    subst hk_eq
    simp at hz
  let i0 : Fin k := ⟨0, hk_pos⟩
  set d := Module.finrank ℝ E
  let b := stdOrthonormalBasis ℝ E
  -- Build a self-adjoint orthogonal operator `Q` on `ℝ^k` sending `e_{i0}` to `z`.
  let zLp : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 z
  let e0 : EuclideanSpace ℝ (Fin k) := EuclideanSpace.single i0 1
  have hzLp : ‖zLp‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [zLp, hz]
  have he0 : ‖e0‖ = 1 := by
    simp [e0]
  obtain ⟨Q, hQe0, hQsymm⟩ := exists_selfAdjoint_linearIsometryEquiv_map_eq he0 hzLp
  -- Lift `Q` to act column-wise on `EuclideanSpace ℝ (Fin k × Fin d)`.
  let Qmat_fun : EuclideanSpace ℝ (Fin k × Fin d) → EuclideanSpace ℝ (Fin k × Fin d) := fun M =>
    WithLp.toLp 2 fun p : Fin k × Fin d =>
      WithLp.ofLp (Q (WithLp.toLp 2 fun j : Fin k => WithLp.ofLp M (j, p.2))) p.1
  have hQmat_invol : ∀ M, Qmat_fun (Qmat_fun M) = M := fun M => by
    apply WithLp.ofLp_injective 2
    ext ⟨i, l⟩
    dsimp only [Qmat_fun]
    have hinner : (WithLp.toLp 2 fun j : Fin k =>
        WithLp.ofLp (Q (WithLp.toLp 2 fun r : Fin k => WithLp.ofLp M (r, l))) j) =
        Q (WithLp.toLp 2 fun r : Fin k => WithLp.ofLp M (r, l)) := by
      apply WithLp.ofLp_injective 2; ext j; rfl
    rw [hinner]
    have hQ2 : Q (Q (WithLp.toLp 2 fun r : Fin k => WithLp.ofLp M (r, l))) =
        WithLp.toLp 2 fun r : Fin k => WithLp.ofLp M (r, l) := by
      have := Q.symm_apply_apply (WithLp.toLp 2 fun r : Fin k => WithLp.ofLp M (r, l))
      rwa [hQsymm] at this
    rw [hQ2]
  let Qmat : EuclideanSpace ℝ (Fin k × Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k × Fin d) :=
    { toFun := Qmat_fun
      invFun := Qmat_fun
      left_inv := hQmat_invol
      right_inv := hQmat_invol
      map_add' := fun M N => by
        apply WithLp.ofLp_injective 2
        ext ⟨i, l⟩
        dsimp only [Qmat_fun]
        have hcol : (WithLp.toLp 2 fun j : Fin k => WithLp.ofLp (M + N) (j, l)) =
            (WithLp.toLp 2 fun j : Fin k => WithLp.ofLp M (j, l)) +
            (WithLp.toLp 2 fun j : Fin k => WithLp.ofLp N (j, l)) := by
          apply WithLp.ofLp_injective 2; ext j; rfl
        rw [hcol, map_add]; rfl
      map_smul' := fun c M => by
        apply WithLp.ofLp_injective 2
        ext ⟨i, l⟩
        dsimp only [Qmat_fun]
        have hcol : (WithLp.toLp 2 fun j : Fin k => WithLp.ofLp (c • M) (j, l)) =
            c • (WithLp.toLp 2 fun j : Fin k => WithLp.ofLp M (j, l)) := by
          apply WithLp.ofLp_injective 2; ext j; rfl
        rw [hcol, map_smul]; rfl
      norm_map' := fun M => by
        have hsq : ‖Qmat_fun M‖ ^ 2 = ‖M‖ ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
          simp only [Real.norm_eq_abs, sq_abs]
          rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
          refine Finset.sum_congr rfl fun l _ => ?_
          have hcol := Q.norm_map (WithLp.toLp 2 fun j : Fin k => WithLp.ofLp M (j, l))
          have hcol_sq : ‖Q (WithLp.toLp 2 fun j : Fin k => WithLp.ofLp M (j, l))‖ ^ 2 =
              ‖WithLp.toLp 2 (fun j : Fin k => WithLp.ofLp M (j, l))‖ ^ 2 := by
            rw [hcol]
          rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hcol_sq
          simpa [Qmat_fun, Real.norm_eq_abs, sq_abs] using hcol_sq
        have h1 : 0 ≤ ‖Qmat_fun M‖ := norm_nonneg _
        have h2 : 0 ≤ ‖M‖ := norm_nonneg _
        change ‖Qmat_fun M‖ = ‖M‖
        nlinarith }
  -- Step 1: `(Fin k → E)` → `EuclideanSpace ℝ (Fin k × Fin d)` via `b.repr` and uncurrying.
  let enc : (Fin k → E) → EuclideanSpace ℝ (Fin k × Fin d) :=
    fun g => WithLp.toLp 2 fun p : Fin k × Fin d => WithLp.ofLp (b.repr (g p.1)) p.2
  have henc_meas : Measurable enc := by
    have hcont : Continuous enc := by
      refine (PiLp.continuous_toLp 2 (fun _ : Fin k × Fin d => ℝ)).comp ?_
      refine continuous_pi fun p => ?_
      exact (continuous_apply p.2).comp
        (((PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ)).comp b.repr.continuous).comp
          (continuous_apply p.1))
    exact hcont.measurable
  -- Prove `enc` is measure-preserving from `Measure.pi (fun _ => stdGaussian E)` to
  -- `stdGaussian (EuclideanSpace ℝ (Fin k × Fin d))` by matching both to
  -- `Measure.pi (fun _ : Fin k × Fin d => gaussianReal 0 1)` via
  -- `e_idx : Fin k × Fin d ≃ Fin (k * d)` .
  let eIdx : Fin k × Fin d ≃ Fin (k * d) := finProdFinEquiv
  have hmp_prod_std : MeasurePreserving (fun M : EuclideanSpace ℝ (Fin k × Fin d) => WithLp.ofLp M)
      (stdGaussian (EuclideanSpace ℝ (Fin k × Fin d)))
      (Measure.pi (fun _ : Fin k × Fin d => gaussianReal 0 1)) := by
    let Uidx : EuclideanSpace ℝ (Fin k × Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k * d)) :=
      LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ eIdx
    have h1 := measurePreserving_linearIsometryEquiv_stdGaussian Uidx
    have h2 := measurePreserving_ofLp_stdGaussian (k * d)
    have h3 : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : Fin k × Fin d => ℝ) eIdx.symm)
        (Measure.pi (fun _ : Fin (k * d) => gaussianReal 0 1))
        (Measure.pi (fun _ : Fin k × Fin d => gaussianReal 0 1)) := by
      refine ⟨(MeasurableEquiv.piCongrLeft (fun _ : Fin k × Fin d => ℝ) eIdx.symm).measurable, ?_⟩
      simpa using Measure.pi_map_piCongrLeft (μ := fun _ : Fin k × Fin d =>
        gaussianReal 0 1) eIdx.symm
    have hcomp := h3.comp (h2.comp h1)
    have hfun : (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin k × Fin d => ℝ) eIdx.symm) ∘
        WithLp.ofLp ∘ ⇑Uidx) =
          (WithLp.ofLp : EuclideanSpace ℝ (Fin k × Fin d) → Fin k × Fin d → ℝ) := by
      ext M ⟨i, l⟩
      simp [Uidx, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, LinearIsometryEquiv.piLpCongrLeft]
    rwa [hfun] at hcomp
  have hmp_enc : MeasurePreserving enc
      (Measure.pi (fun _ : Fin k => stdGaussian E))
      (stdGaussian (EuclideanSpace ℝ (Fin k × Fin d))) := by
    refine ⟨henc_meas, ?_⟩
    -- Push both sides along the measurable equivalence `WithLp.ofLp` to `Fin k × Fin d → ℝ`.
    let eOfLp := (MeasurableEquiv.toLp 2 (Fin k × Fin d → ℝ)).symm
    have h_eq_ofLp : (Measure.map enc (Measure.pi (fun _ : Fin k => stdGaussian E))).map eOfLp =
        (stdGaussian (EuclideanSpace ℝ (Fin k × Fin d))).map eOfLp := by
      have hrhs_eq : (stdGaussian (EuclideanSpace ℝ (Fin k × Fin d))).map eOfLp =
          Measure.pi (fun _ : Fin k × Fin d => gaussianReal 0 1) := hmp_prod_std.map_eq
      rw [hrhs_eq, Measure.map_map eOfLp.measurable henc_meas]
      -- Now LHS is map along `g ↦ (fun (j, l) => (b.repr (g j)) l)`.
      refine (Measure.pi_eq (μ := fun _ : Fin k × Fin d => gaussianReal 0 1) fun s hs => ?_).symm
      rw [Measure.map_apply (eOfLp.measurable.comp henc_meas) (MeasurableSet.univ_pi hs)]
      have hpre : (eOfLp ∘ enc) ⁻¹' Set.univ.pi s =
          Set.univ.pi (fun j : Fin k =>
            (fun x : E => WithLp.ofLp (b.repr x)) ⁻¹' Set.univ.pi (fun l : Fin d => s (j, l))) := by
        ext g
        simp only [mem_preimage, Function.comp_apply, Set.mem_pi, mem_univ, forall_const,
          Prod.forall, eOfLp, enc]
        exact ⟨fun h j l => h j l, fun h j l => h j l⟩
      rw [hpre, Measure.pi_pi]
      have hrow : ∀ j : Fin k,
          stdGaussian E ((fun x : E => WithLp.ofLp (b.repr x)) ⁻¹'
            Set.univ.pi (fun l : Fin d => s (j, l))) =
            ∏ l : Fin d, gaussianReal 0 1 (s (j, l)) := fun j => by
        rw [(measurePreserving_orthonormalBasis_stdGaussian b).measure_preimage
          (MeasurableSet.univ_pi fun l => hs (j, l)).nullMeasurableSet, Measure.pi_pi]
      simp_rw [hrow]
      rw [Fintype.prod_prod_type]
    have hinj : Measure.map eOfLp.symm
        ((Measure.map enc (Measure.pi (fun _ : Fin k => stdGaussian E))).map eOfLp) =
        Measure.map eOfLp.symm ((stdGaussian (EuclideanSpace ℝ (Fin k × Fin d))).map eOfLp) :=
      congrArg (Measure.map eOfLp.symm) h_eq_ofLp
    simpa [Measure.map_map eOfLp.symm.measurable eOfLp.measurable] using hinj
  -- Step 2: `Qmat` preserves `stdGaussian (EuclideanSpace ℝ (Fin k × Fin d))`.
  have hmp_Qmat := measurePreserving_linearIsometryEquiv_stdGaussian Qmat
  -- Step 3: Projecting `Fin k × Fin d → ℝ` onto row `i0` preserves product Gaussian measure.
  let rowProj : (Fin k × Fin d → ℝ) → (Fin d → ℝ) := fun f l => f (i0, l)
  have hmp_row : MeasurePreserving rowProj
      (Measure.pi (fun _ : Fin k × Fin d => gaussianReal 0 1))
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
    have hmeas_row : Measurable rowProj :=
      (continuous_pi fun l => continuous_apply (i0, l)).measurable
    refine ⟨hmeas_row, ?_⟩
    refine (Measure.pi_eq (μ := fun _ : Fin d => gaussianReal 0 1) fun s hs => ?_).symm
    rw [Measure.map_apply hmeas_row (MeasurableSet.univ_pi hs)]
    let t : Fin k × Fin d → Set ℝ := fun p => if p.1 = i0 then s p.2 else Set.univ
    have hpre : rowProj ⁻¹' Set.univ.pi s = Set.univ.pi t := by
      ext f
      simp only [mem_preimage, mem_univ_pi, rowProj, t]
      constructor
      · intro h ⟨j, l⟩
        split_ifs with hj
        · subst hj; exact h l
        · trivial
      · intro h l
        simpa using h (i0, l)
    rw [hpre, Measure.pi_pi, Fintype.prod_prod_type]
    rw [Finset.prod_eq_single i0]
    · simp [t]
    · intro j _ hj
      simp [t, hj]
    · intro h; exact absurd (Finset.mem_univ i0) h
  -- Step 4: Map `Fin d → ℝ` back to `E` via `b.repr.symm ∘ WithLp.toLp 2`.
  have hmp_back : MeasurePreserving (fun v : Fin d → ℝ => b.repr.symm (WithLp.toLp 2 v))
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) (stdGaussian E) := by
    have h1 := (measurePreserving_ofLp_stdGaussian d).symm
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
    have h2 := measurePreserving_linearIsometryEquiv_stdGaussian b.repr.symm
    exact h2.comp h1
  -- Compose all steps and verify the resulting function equals `g ↦ ∑ j, z j • g j`.
  have htotal := hmp_back.comp (hmp_row.comp (hmp_prod_std.comp (hmp_Qmat.comp hmp_enc)))
  have hfun : (fun g : Fin k → E =>
      b.repr.symm (WithLp.toLp 2 (rowProj (WithLp.ofLp (Qmat (enc g)))))) =
      (fun g : Fin k → E => ∑ j : Fin k, z j • g j) := by
    ext g
    apply b.repr.injective
    apply WithLp.ofLp_injective 2
    ext l
    simp only [LinearIsometryEquiv.apply_symm_apply, rowProj, Qmat, Qmat_fun, enc,
      map_sum, map_smul, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    -- The `i0`-th entry of `Q col` equals `⟪Q col, e0⟫ = ⟪col, Q e0⟫ = ⟪col, zLp⟫`.
    let col : EuclideanSpace ℝ (Fin k) :=
      WithLp.toLp 2 fun j : Fin k => WithLp.ofLp (b.repr (g j)) l
    have hinner1 : WithLp.ofLp (Q col) i0 = ⟪Q col, e0⟫ := by
      rw [EuclideanSpace.inner_single_right]
      simp
    have hinner2 : ⟪Q col, e0⟫ = ⟪col, zLp⟫ := by
      have hQ2 : Q (Q col) = col := by
        have := Q.symm_apply_apply col
        rwa [hQsymm] at this
      have h := Q.inner_map_map (Q col) e0
      rw [hQ2, hQe0] at h
      exact h.symm
    have hinner3 : ⟪col, zLp⟫ = ∑ j : Fin k, z j * WithLp.ofLp (b.repr (g j)) l := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [col, zLp, dotProduct]
    change WithLp.ofLp (Q col) i0 = ∑ j : Fin k, z j * WithLp.ofLp (b.repr (g j)) l
    rw [hinner1, hinner2, hinner3]
  simpa [Function.comp_def, hfun] using htotal

end StdGaussian

/-! ### 2. Polar Factorization, Gaussian Norm Moments, and Gaussian Width -/

section PolarAndMoments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Radial probability distribution of `‖x‖` for `x ~ stdGaussian E` on `Ioi (0 : ℝ)`
(in dimension `d = finrank ℝ E ≥ 1`). -/
@[expose]
noncomputable def stdGaussianRadial (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Measure (Ioi (0 : ℝ)) :=
  ((volume : Measure E).toSphere Set.univ) •
    (Measure.volumeIoiPow (Module.finrank ℝ E - 1)).withDensity
      (fun r : Ioi (0 : ℝ) =>
        ENNReal.ofReal ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
          Real.exp (-((r : ℝ) ^ 2) / 2)))

/-- **Polar Radial–Angular Factorization of `stdGaussian E`:**
under `homeomorphUnitSphereProd E`, the restriction of `stdGaussian E` to `{0}ᶜ` factors as the
independent product of uniform spherical measure `sphereProb volume` and `stdGaussianRadial E`. -/
theorem measurePreserving_homeomorphUnitSphereProd_stdGaussian [Nontrivial E] :
    MeasurePreserving (homeomorphUnitSphereProd E)
      ((stdGaussian E).comap (Subtype.val : ({0}ᶜ : Set E) → E))
      ((sphereProb (volume : Measure E)).prod (stdGaussianRadial E)) := by
  set d := Module.finrank ℝ E
  let ρ : Ioi (0 : ℝ) → ℝ≥0∞ := fun r =>
    ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-((r : ℝ) ^ 2) / 2))
  have hρ_meas : Measurable ρ := by
    refine ENNReal.measurable_ofReal.comp ?_
    have hcont : Continuous (fun r : Ioi (0 : ℝ) =>
        (2 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-((r : ℝ) ^ 2) / 2)) := by
      fun_prop
    exact hcont.measurable
  have hemb : MeasurableEmbedding (Subtype.val : ({0}ᶜ : Set E) → E) :=
    MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : E)).compl
  have hdens_val : ∀ x : ({0}ᶜ : Set E),
      ENNReal.ofReal (stdGaussianDensity x.1) = ρ (homeomorphUnitSphereProd E x).2 := fun x => by
    simp [d, ρ, stdGaussianDensity, homeomorphUnitSphereProd_apply_snd_coe]
  -- Check equality on all measurable sets `s ⊆ sphere 0 1 × Ioi 0`.
  refine ⟨(homeomorphUnitSphereProd E).continuous.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (homeomorphUnitSphereProd E).continuous.measurable hs]
  have hpre_m : MeasurableSet ((homeomorphUnitSphereProd E) ⁻¹' s) :=
    hs.preimage (homeomorphUnitSphereProd E).continuous.measurable
  -- Compute LHS via `comap` + `withDensity` + `measurePreserving_homeomorphUnitSphereProd`.
  have hcomap : ((stdGaussian E).comap (Subtype.val : ({0}ᶜ : Set E) → E))
      ((homeomorphUnitSphereProd E) ⁻¹' s) =
      ∫⁻ x in (homeomorphUnitSphereProd E) ⁻¹' s,
        ENNReal.ofReal (stdGaussianDensity x.1)
          ∂(volume.comap (Subtype.val : ({0}ᶜ : Set E) → E)) := by
    rw [Measure.comap_apply _ Subtype.val_injective (fun t ht =>
      hemb.measurableSet_image.mpr ht) _ hpre_m,
      stdGaussian_eq_withDensity, withDensity_apply _ (hemb.measurableSet_image.mpr hpre_m),
      ← lintegral_indicator (hemb.measurableSet_image.mpr hpre_m),
      ← lintegral_indicator hpre_m]
    have hmp_val : MeasurePreserving (Subtype.val : ({0}ᶜ : Set E) → E)
        (volume.comap (Subtype.val : ({0}ᶜ : Set E) → E))
        (volume.restrict ({0}ᶜ : Set E)) := by
      refine ⟨continuous_subtype_val.measurable, ?_⟩
      ext t ht
      rw [Measure.map_apply continuous_subtype_val.measurable ht,
        Measure.restrict_apply ht,
        Measure.comap_apply _ Subtype.val_injective (fun u hu => hemb.measurableSet_image.mpr hu) _
          (ht.preimage continuous_subtype_val.measurable)]
      congr 1
      ext y; simp [and_comm]
    have hcomp := hmp_val.lintegral_comp_emb hemb
      ((Subtype.val '' ((homeomorphUnitSphereProd E) ⁻¹' s)).indicator
        (fun y => ENNReal.ofReal (stdGaussianDensity y)))
    have hres : ∫⁻ y, (Subtype.val '' ((homeomorphUnitSphereProd E) ⁻¹' s)).indicator
        (fun y => ENNReal.ofReal (stdGaussianDensity y)) y ∂(volume.restrict ({0}ᶜ : Set E)) =
        ∫⁻ y, (Subtype.val '' ((homeomorphUnitSphereProd E) ⁻¹' s)).indicator
          (fun y => ENNReal.ofReal (stdGaussianDensity y)) y := by
      rw [lintegral_indicator (hemb.measurableSet_image.mpr hpre_m),
        lintegral_indicator (hemb.measurableSet_image.mpr hpre_m),
        Measure.restrict_restrict_of_subset (Subtype.coe_image_subset _ _)]
    rw [← hres, ← hcomp]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ (homeomorphUnitSphereProd E) ⁻¹' s
    · rw [indicator_of_mem hx,
        indicator_of_mem (show x.1 ∈ Subtype.val '' ((homeomorphUnitSphereProd E) ⁻¹' s) from ⟨x,
          hx, rfl⟩)]
    · rw [indicator_of_notMem hx,
        indicator_of_notMem (by rintro ⟨y, hy, hxy⟩; exact hx (Subtype.ext hxy ▸ hy))]
  rw [hcomap]
  have hmp_pol := (volume : Measure E).measurePreserving_homeomorphUnitSphereProd
  have h_lhs : ∫⁻ x in (homeomorphUnitSphereProd E) ⁻¹' s,
      ENNReal.ofReal (stdGaussianDensity x.1) ∂(volume.comap (Subtype.val : ({0}ᶜ : Set E) → E)) =
      ∫⁻ p in s, ρ p.2 ∂((volume : Measure E).toSphere.prod (Measure.volumeIoiPow (d - 1))) := by
    rw [← lintegral_indicator hpre_m, ← lintegral_indicator hs,
      ← hmp_pol.lintegral_comp_emb
        (homeomorphUnitSphereProd E).toMeasurableEquiv.measurableEmbedding]
    refine lintegral_congr fun x => ?_
    by_cases hx : homeomorphUnitSphereProd E x ∈ s
    · simp [indicator_of_mem hx,
        indicator_of_mem (show x ∈ (homeomorphUnitSphereProd E) ⁻¹' s from hx),
        hdens_val x]
    · simp [indicator_of_notMem hx,
        indicator_of_notMem (show x ∉ (homeomorphUnitSphereProd E) ⁻¹' s from hx)]
  have hρ_snd : Measurable (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => ρ p.2) :=
    hρ_meas.comp measurable_snd
  rw [h_lhs, ← lintegral_indicator hs,
    lintegral_prod _ (hρ_snd.indicator hs).aemeasurable]
  -- Now expand the RHS using `Measure.prod_apply`.
  have h_sphere_eq : (volume : Measure E).toSphere =
      ((volume : Measure E).toSphere Set.univ) • sphereProb (volume : Measure E) := by
    rw [sphereProb, smul_smul]
    have hpos : (volume : Measure E).toSphere Set.univ ≠ 0 := by
      rw [Measure.toSphere_apply_univ]
      have hball : 0 < volume (ball (0 : E) 1) :=
        isOpen_ball.measure_pos volume ⟨0, mem_ball_self zero_lt_one⟩
      exact mul_ne_zero (Nat.cast_ne_zero.mpr Module.finrank_pos.ne') hball.ne'
    have hfin : (volume : Measure E).toSphere Set.univ ≠ ⊤ := by
      rw [Measure.toSphere_apply_univ]
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        ((measure_mono ball_subset_closedBall).trans_lt
          (isCompact_closedBall (0 : E) 1).measure_lt_top).ne
    rw [ENNReal.mul_inv_cancel hpos hfin, one_smul]
  -- Show `SFinite (stdGaussianRadial E)` so `Measure.prod_apply` applies cleanly.
  have h_rad_finite : stdGaussianRadial E Set.univ ≠ ⊤ := by
    have htop :=
      (hmp_pol.lintegral_comp_emb (homeomorphUnitSphereProd E).toMeasurableEquiv.measurableEmbedding
      (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => ρ p.2)).symm
    have htot_eq : ∫⁻ p,
      ρ p.2 ∂((volume : Measure E).toSphere.prod (Measure.volumeIoiPow (d - 1))) = 1 := by
      rw [htop]
      have h1 : (fun x : ({0}ᶜ : Set E) => ρ (homeomorphUnitSphereProd E x).2) =
          (fun x : ({0}ᶜ : Set E) => ENNReal.ofReal (stdGaussianDensity x.1)) := by
        ext x; exact (hdens_val x).symm
      rw [h1]
      have h2 := lintegral_stdGaussianDensity_eq_one (E := E)
      have hzero : volume ({0} : Set E) = 0 := measure_singleton 0
      have hres_vol : (volume : Measure E).restrict ({0}ᶜ : Set E) = volume :=
        Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; simp [hzero])
      rw [← hres_vol] at h2
      have hmp_val : MeasurePreserving (Subtype.val : ({0}ᶜ : Set E) → E)
          (volume.comap (Subtype.val : ({0}ᶜ : Set E) → E))
          (volume.restrict ({0}ᶜ : Set E)) := by
        refine ⟨continuous_subtype_val.measurable, ?_⟩
        ext t ht
        rw [Measure.map_apply continuous_subtype_val.measurable ht, Measure.restrict_apply ht,
          Measure.comap_apply _ Subtype.val_injective (fun u hu =>
            hemb.measurableSet_image.mpr hu) _
            (ht.preimage continuous_subtype_val.measurable)]
        congr 1; ext y; simp [and_comm]
      rw [← hmp_val.lintegral_comp_emb hemb (fun y => ENNReal.ofReal (stdGaussianDensity y))] at h2
      exact h2
    rw [lintegral_prod _ hρ_snd.aemeasurable] at htot_eq
    dsimp only at htot_eq
    rw [lintegral_const] at htot_eq
    have hrad_eq : stdGaussianRadial E Set.univ =
        (∫⁻ r : Ioi (0 : ℝ), ρ r ∂Measure.volumeIoiPow (d - 1)) *
          (volume : Measure E).toSphere Set.univ := by
      rw [stdGaussianRadial, smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ,
        Measure.restrict_univ, mul_comm]
    rw [hrad_eq, htot_eq]
    exact ENNReal.one_ne_top
  have : IsFiniteMeasure (stdGaussianRadial E) := ⟨lt_top_iff_ne_top.mpr h_rad_finite⟩
  rw [Measure.prod_apply hs, h_sphere_eq, lintegral_smul_measure, smul_eq_mul,
    ← lintegral_const_mul _ ((hρ_snd.indicator hs).lintegral_prod_right')]
  refine lintegral_congr fun u => ?_
  have hm_pre : MeasurableSet (Prod.mk u ⁻¹' s) :=
    hs.preimage (measurable_const.prodMk measurable_id)
  rw [stdGaussianRadial, smul_apply, smul_eq_mul, withDensity_apply _ hm_pre,
    ← lintegral_indicator hm_pre]
  congr 1

instance instIsProbabilityMeasureStdGaussianRadial [Nontrivial E] :
    IsProbabilityMeasure (stdGaussianRadial E) where
  measure_univ := by
    have hmp := measurePreserving_homeomorphUnitSphereProd_stdGaussian (E := E)
    have h1 := hmp.measure_preimage MeasurableSet.univ.nullMeasurableSet
    -- First show `SFinite (stdGaussianRadial E)` from `stdGaussianRadial E = c • withDensity`.
    have hsf : SFinite (stdGaussianRadial E) := by
      unfold stdGaussianRadial
      infer_instance
    rw [← Set.univ_prod_univ, Measure.prod_prod, measure_univ, one_mul] at h1
    have hzero : stdGaussian E ({0} : Set E) = 0 := by
      rw [stdGaussian_eq_withDensity, withDensity_apply _ (measurableSet_singleton 0),
        Measure.restrict_eq_zero.mpr (measure_singleton 0), lintegral_zero_measure]
    have hcomap_univ : ((stdGaussian E).comap (Subtype.val : ({0}ᶜ : Set E) → E)) Set.univ = 1 := by
      have hemb : MeasurableEmbedding (Subtype.val : ({0}ᶜ : Set E) → E) :=
        MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : E)).compl
      rw [Measure.comap_apply _ Subtype.val_injective (fun t ht =>
        hemb.measurableSet_image.mpr ht) _
        MeasurableSet.univ, Set.image_univ, Subtype.range_coe_subtype]
      have hcompl : stdGaussian E ({0}ᶜ : Set E) = stdGaussian E Set.univ := by
        rw [Set.compl_eq_univ_sdiff, measure_sdiff_null hzero]
      rw [show {x : E | x ∈ ({0} : Set E)ᶜ} = ({0} : Set E)ᶜ from rfl, hcompl, measure_univ]
    rw [Set.univ_prod_univ, preimage_univ, hcomap_univ] at h1
    exact h1.symm

/-- **Radial–Angular Independence for Standard Gaussian:**
for any measurable `S ⊆ sphere (0 : E) 1` and `R ⊆ Ioi (0 : ℝ)`, the event
`{x ≠ 0 | (‖x‖⁻¹ • x) ∈ S ∧ ‖x‖ ∈ R}` has `stdGaussian E` measure equal to the product of
`sphereProb volume S` and `stdGaussianRadial E R`. -/
theorem stdGaussian_polar_cone [Nontrivial E] {S : Set (sphere (0 : E) 1)} (hS : MeasurableSet S)
    {R : Set (Ioi (0 : ℝ))} (hR : MeasurableSet R) :
    stdGaussian E (Subtype.val '' ((homeomorphUnitSphereProd E) ⁻¹' (S ×ˢ R))) =
      sphereProb (volume : Measure E) S * stdGaussianRadial E R := by
  have hmp := measurePreserving_homeomorphUnitSphereProd_stdGaussian (E := E)
  have hemb : MeasurableEmbedding (Subtype.val : ({0}ᶜ : Set E) → E) :=
    MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : E)).compl
  have hpre_m : MeasurableSet ((homeomorphUnitSphereProd E) ⁻¹' (S ×ˢ R)) :=
    (hS.prod hR).preimage (homeomorphUnitSphereProd E).continuous.measurable
  rw [← Measure.prod_prod, ← hmp.measure_preimage (hS.prod hR).nullMeasurableSet,
    Measure.comap_apply _ Subtype.val_injective (fun t ht =>
      hemb.measurableSet_image.mpr ht) _ hpre_m]

/-- The radial law `stdGaussianRadial E` agrees with the distribution of `‖x‖` on `(0, ∞)`. -/
lemma stdGaussianRadial_Ici [Nontrivial E] {r₀ : ℝ} (hr₀ : 0 < r₀) :
    stdGaussianRadial E (Ici ⟨r₀, hr₀⟩) = stdGaussian E {x : E | r₀ ≤ ‖x‖} := by
  have h := stdGaussian_polar_cone (E :=
    E) MeasurableSet.univ (measurableSet_Ici (a := (⟨r₀, hr₀⟩ : Ioi (0 : ℝ))))
  rw [measure_univ, one_mul] at h
  rw [← h]
  congr 1
  ext x
  simp only [mem_image, mem_preimage, mem_prod, mem_univ, true_and, mem_Ici, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨y, hy⟩, hle, rfl⟩
    change r₀ ≤ ((homeomorphUnitSphereProd E ⟨y, hy⟩).2 : ℝ) at hle
    simpa [homeomorphUnitSphereProd_apply_snd_coe] using hle
  · intro hle
    have hx0 : x ≠ 0 := fun h0 => by rw [h0, norm_zero] at hle; linarith
    refine ⟨⟨x, hx0⟩, ?_, rfl⟩
    change r₀ ≤ ((homeomorphUnitSphereProd E ⟨x, hx0⟩).2 : ℝ)
    simpa [homeomorphUnitSphereProd_apply_snd_coe] using hle

/-! #### 1D Gaussian Moments (2nd and 4th) -/

/-- Helper: `t ^ m * gaussianPDFReal 0 1 t` is integrable on `ℝ` for every `m : ℕ`. -/
private lemma integrable_pow_mul_gaussianPDFReal (m : ℕ) :
    Integrable (fun t : ℝ => t ^ m * gaussianPDFReal 0 1 t) volume := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ => t ^ m * gaussianPDFReal 0 1 t) volume :=
    ((continuous_pow m).measurable.mul (measurable_gaussianPDFReal 0 1)).aestronglyMeasurable
  -- Bound `|t|^m * exp(-t²/2) ≤ C * exp(-t²/4)` using `|t|^m ≤ m! * exp(|t|)` and `|t| ≤ t²/4 + 1`.
  have hbase : Integrable (fun t : ℝ => Real.exp (-(t ^ 2) / 4)) volume := by
    have hinv_ne : (1 / Real.sqrt 2 : ℝ) ≠ 0 := by positivity
    have h1 := (integrable_gaussianPDFReal 0 1).comp_mul_left' hinv_ne
    have h2 := h1.const_mul (Real.sqrt (2 * Real.pi))
    refine h2.congr (ae_of_all _ fun t => ?_)
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    have hsqrt_pos : (0 : ℝ) < Real.sqrt (2 * Real.pi) := by positivity
    rw [← mul_assoc (Real.sqrt (2 * Real.pi)), mul_inv_cancel₀ hsqrt_pos.ne', one_mul]
    congr 1
    rw [mul_pow, div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  refine (hbase.const_mul (((2 * Real.pi) ^ (-(1 : ℝ) / 2)) * (m.factorial : ℝ) * Real.exp 1)).mono'
    hmeas (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 t)]
  have hfact : |t| ^ m / (m.factorial : ℝ) ≤ Real.exp |t| :=
    Real.pow_div_factorial_le_exp |t| (abs_nonneg t) m
  have hpow : |t| ^ m ≤ (m.factorial : ℝ) * Real.exp |t| := by
    have hfac_pos : (0 : ℝ) < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
    rw [mul_comm]
    exact (div_le_iff₀ hfac_pos).mp hfact
  have hquad : |t| ≤ t ^ 2 / 4 + 1 := by
    have : 0 ≤ (|t| - 2) ^ 2 := sq_nonneg _
    nlinarith [sq_abs t]
  have hpdf : gaussianPDFReal 0 1 t = (2 * Real.pi) ^ (-(1 : ℝ) / 2) * Real.exp (-(t ^ 2) / 2) := by
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    ring_nf
  rw [hpdf]
  calc
    |t| ^ m * ((2 * Real.pi) ^ (-(1 : ℝ) / 2) * Real.exp (-(t ^ 2) / 2))
      ≤ ((m.factorial : ℝ) * Real.exp |t|) *
          ((2 * Real.pi) ^ (-(1 : ℝ) / 2) * Real.exp (-(t ^ 2) / 2)) := by
        gcongr
    _ = (2 * Real.pi) ^ (-(1 : ℝ) / 2) * (m.factorial : ℝ) *
          Real.exp (|t| + -(t ^ 2) / 2) := by
        rw [Real.exp_add]; ring
    _ ≤ (2 * Real.pi) ^ (-(1 : ℝ) / 2) * (m.factorial : ℝ) *
          Real.exp ((t ^ 2 / 4 + 1) + -(t ^ 2) / 2) := by
        gcongr
    _ = (2 * Real.pi) ^ (-(1 : ℝ) / 2) * (m.factorial : ℝ) * Real.exp 1 *
          Real.exp (-(t ^ 2) / 4) := by
        rw [mul_assoc _ (Real.exp 1), ← Real.exp_add]
        congr 2; ring

private lemma integrable_pow_gaussianReal (m : ℕ) :
    Integrable (fun t : ℝ => t ^ m) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero]
  have h1 := integrable_withDensity_iff_integrable_smul₀' (μ := (volume : Measure ℝ))
    (f := gaussianPDF 0 1) (measurable_gaussianPDF 0 1).aemeasurable
    (ae_of_all _ fun _ => gaussianPDF_lt_top) (g := fun t : ℝ => t ^ m)
  rw [h1]
  refine (integrable_pow_mul_gaussianPDFReal m).congr (ae_of_all _ fun t => ?_)
  simp [toReal_gaussianPDF, smul_eq_mul, mul_comm]

/-- Second moment of a standard 1D Gaussian: `∫ t, t² ∂(gaussianReal 0 1) = 1`. -/
theorem integral_sq_gaussianReal :
    ∫ t : ℝ, t ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have hvar := variance_id_gaussianReal (μ := 0) (v := 1)
  have hmean := integral_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (memLp_id_gaussianReal 2).aemeasurable] at hvar
  simpa [hmean] using hvar

/-- Fourth moment of a standard 1D Gaussian: `∫ t, t⁴ ∂(gaussianReal 0 1) = 3`. -/
theorem integral_pow_four_gaussianReal :
    ∫ t : ℝ, t ^ 4 ∂(gaussianReal 0 1) = 3 := by
  -- Use `d/dt (t^3 * γ(t)) = (3 t^2 - t^4) * γ(t)` and
  -- `integral_eq_zero_of_hasDerivAt_of_integrable` .
  have hpdf : ∀ t : ℝ, gaussianPDFReal 0 1 t =
      (2 * Real.pi) ^ (-(1 : ℝ) / 2) * Real.exp (-(t ^ 2) / 2) := fun t => by
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    ring_nf
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun x : ℝ => x ^ 3 * gaussianPDFReal 0 1 x)
        ((3 * t ^ 2 - t ^ 4) * gaussianPDFReal 0 1 t) t := fun t => by
    have h1 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * t ^ 2) t := by
      simpa using hasDerivAt_pow 3 t
    have h2 : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-t) t := by
      have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
      simpa [neg_div] using (hp.neg.div_const 2)
    have h3 : HasDerivAt (gaussianPDFReal 0 1) (-t * gaussianPDFReal 0 1 t) t := by
      have hfun : gaussianPDFReal 0 1 =
          fun x : ℝ => (2 * Real.pi) ^ (-(1 : ℝ) / 2) * Real.exp (-(x ^ 2) / 2) := funext hpdf
      rw [hfun]
      convert (h2.exp.const_mul ((2 * Real.pi) ^ (-(1 : ℝ) / 2))) using 1
      dsimp only; ring
    convert h1.fun_mul h3 using 1
    ring
  have hf_int : Integrable (fun t : ℝ => t ^ 3 * gaussianPDFReal 0 1 t) volume :=
    integrable_pow_mul_gaussianPDFReal 3
  have hf'_int : Integrable (fun t : ℝ => (3 * t ^ 2 - t ^ 4) * gaussianPDFReal 0 1 t) volume := by
    have hsub : (fun t : ℝ => (3 * t ^ 2 - t ^ 4) * gaussianPDFReal 0 1 t) =
        fun t : ℝ => 3 * (t ^ 2 * gaussianPDFReal 0 1 t) - t ^ 4 * gaussianPDFReal 0 1 t := by
      ext t; ring
    rw [hsub]
    exact ((integrable_pow_mul_gaussianPDFReal 2).const_mul 3).sub
      (integrable_pow_mul_gaussianPDFReal 4)
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hderiv hf'_int hf_int
  have hsplit : ∫ t : ℝ, (3 * t ^ 2 - t ^ 4) * gaussianPDFReal 0 1 t =
      3 * (∫ t : ℝ, t ^ 2 * gaussianPDFReal 0 1 t) - ∫ t : ℝ, t ^ 4 * gaussianPDFReal 0 1 t := by
    have hfun : (fun t : ℝ => (3 * t ^ 2 - t ^ 4) * gaussianPDFReal 0 1 t) =
        fun t : ℝ => 3 * (t ^ 2 * gaussianPDFReal 0 1 t) - t ^ 4 * gaussianPDFReal 0 1 t := by
      ext t; ring
    rw [hfun, integral_sub ((integrable_pow_mul_gaussianPDFReal 2).const_mul 3)
      (integrable_pow_mul_gaussianPDFReal 4), integral_const_mul]
  have hconv : ∀ m : ℕ, ∫ t : ℝ, t ^ m ∂(gaussianReal 0 1) =
      ∫ t : ℝ, t ^ m * gaussianPDFReal 0 1 t := fun m => by
    rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp [smul_eq_mul, mul_comm]
  rw [hconv 4]
  have hsq : ∫ t : ℝ, t ^ 2 * gaussianPDFReal 0 1 t = 1 := by
    rw [← hconv 2]; exact integral_sq_gaussianReal
  linarith

/-! #### `d`-Dimensional Gaussian Norm Moments and Paley–Zygmund Lower Bound -/

private lemma integrable_comp_mp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β} (hmp : MeasurePreserving f μ ν)
    {g : β → ℝ} (hg : Integrable g ν) : Integrable (fun x => g (f x)) μ :=
  (integrable_map_measure (hmp.map_eq.symm ▸ hg.aestronglyMeasurable)
    hmp.measurable.aemeasurable).mp (hmp.map_eq.symm ▸ hg)

/-- `x ↦ ‖x‖ ^ 2` is integrable under `stdGaussian E`. -/
lemma integrable_norm_sq_stdGaussian :
    Integrable (fun x : E => ‖x‖ ^ 2) (stdGaussian E) := by
  let b := stdOrthonormalBasis ℝ E
  set d := Module.finrank ℝ E
  have hmp := measurePreserving_orthonormalBasis_stdGaussian b
  have hpi : Integrable (fun v : Fin d → ℝ => ∑ i : Fin d, v i ^ 2)
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) :=
    integrable_finsetSum Finset.univ fun i _ =>
      integrable_comp_mp (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) i)
        (integrable_pow_gaussianReal 2)
  have hcomp := integrable_comp_mp hmp hpi
  refine hcomp.congr (ae_of_all _ fun x => ?_)
  dsimp only
  have hnorm : ‖x‖ ^ 2 = ‖b.repr x‖ ^ 2 := by rw [b.repr.norm_map]
  rw [hnorm, EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

/-- `x ↦ ‖x‖ ^ 4` is integrable under `stdGaussian E`. -/
lemma integrable_norm_pow_four_stdGaussian :
    Integrable (fun x : E => ‖x‖ ^ 4) (stdGaussian E) := by
  let b := stdOrthonormalBasis ℝ E
  set d := Module.finrank ℝ E
  have hmp := measurePreserving_orthonormalBasis_stdGaussian b
  have hpi : Integrable (fun v : Fin d → ℝ => (∑ i : Fin d, v i ^ 2) ^ 2)
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
    have hexpand : (fun v : Fin d → ℝ => (∑ i : Fin d, v i ^ 2) ^ 2) =
        fun v => ∑ i : Fin d, ∑ j : Fin d, v i ^ 2 * v j ^ 2 := by
      ext v; rw [sq, Finset.sum_mul_sum]
    rw [hexpand]
    refine integrable_finsetSum Finset.univ fun i _ =>
      integrable_finsetSum Finset.univ fun j _ => ?_
    have hdom : ∀ v : Fin d → ℝ, ‖v i ^ 2 * v j ^ 2‖ ≤ v i ^ 4 + v j ^ 4 := fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [sq_nonneg (v i ^ 2 - v j ^ 2)]
    have hi4 : Integrable (fun v : Fin d → ℝ => v i ^ 4)
        (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) :=
      integrable_comp_mp (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) i)
        (integrable_pow_gaussianReal 4)
    have hj4 : Integrable (fun v : Fin d → ℝ => v j ^ 4)
        (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) :=
      integrable_comp_mp (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) j)
        (integrable_pow_gaussianReal 4)
    have hsum_int : Integrable (fun v : Fin d → ℝ => v i ^ 4 + v j ^ 4)
        (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := hi4.add hj4
    exact hsum_int.mono'
      (((measurable_pi_apply i).pow_const 2).mul
        ((measurable_pi_apply j).pow_const 2)).aestronglyMeasurable
      (ae_of_all _ hdom)
  have hcomp := integrable_comp_mp hmp hpi
  refine hcomp.congr (ae_of_all _ fun x => ?_)
  dsimp only
  have hnorm : ‖x‖ ^ 4 = (‖b.repr x‖ ^ 2) ^ 2 := by rw [b.repr.norm_map]; ring
  rw [hnorm, EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

/-- `x ↦ ‖x‖` is integrable under `stdGaussian E`. -/
lemma integrable_norm_stdGaussian :
    Integrable (fun x : E => ‖x‖) (stdGaussian E) := by
  refine (integrable_norm_sq_stdGaussian.add (integrable_const (1 : ℝ))).mono'
    continuous_norm.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
  nlinarith [sq_nonneg (‖x‖ - 1)]

/-- **Second Moment of Gaussian Norm:** `∫ ‖x‖² ∂stdGaussian E = finrank ℝ E`. -/
theorem integral_norm_sq_stdGaussian :
    ∫ x : E, ‖x‖ ^ 2 ∂stdGaussian E = (Module.finrank ℝ E : ℝ) := by
  let b := stdOrthonormalBasis ℝ E
  set d := Module.finrank ℝ E
  have hmp := measurePreserving_orthonormalBasis_stdGaussian b
  have hfun : (fun x : E => ‖x‖ ^ 2) = fun x : E =>
    ∑ i : Fin d, (WithLp.ofLp (b.repr x) i) ^ 2 := by
    ext x
    have hnorm : ‖x‖ ^ 2 = ‖b.repr x‖ ^ 2 := by rw [b.repr.norm_map]
    rw [hnorm, EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hfun]
  have hmeas_sum : Measurable (fun v : Fin d → ℝ => ∑ i : Fin d, v i ^ 2) :=
    Finset.measurable_sum Finset.univ fun i _ => (measurable_pi_apply i).pow_const 2
  have heq : ∫ x : E, ∑ i : Fin d, WithLp.ofLp (b.repr x) i ^ 2 ∂stdGaussian E =
      ∫ v : Fin d → ℝ, ∑ i : Fin d, v i ^ 2 ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1) := by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hmeas_sum.aestronglyMeasurable]
  rw [heq, integral_finsetSum Finset.univ fun i _ =>
    integrable_comp_mp (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) i)
      (integrable_pow_gaussianReal 2)]
  have hterm : ∀ i : Fin d,
      ∫ v : Fin d → ℝ, v i ^ 2 ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1) = 1 := fun i => by
    have hmp_i : MeasurePreserving (fun v : Fin d → ℝ => v i)
        (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) (gaussianReal 0 1) :=
      measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) i
    have h2 : ∫ v : Fin d → ℝ, v i ^ 2 ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1) =
        ∫ t : ℝ, t ^ 2 ∂gaussianReal 0 1 := by
      have h := integral_map (μ := Measure.pi (fun _ : Fin d => gaussianReal 0 1))
        (φ := fun v : Fin d → ℝ => v i) (f := fun t : ℝ => t ^ 2)
        (measurable_pi_apply i).aemeasurable (continuous_pow 2).aestronglyMeasurable
      rw [hmp_i.map_eq] at h
      exact h.symm
    rw [h2, integral_sq_gaussianReal]
  simp [hterm]

/-- **Fourth Moment of Gaussian Norm:** `∫ ‖x‖⁴ ∂stdGaussian E = d * (d + 2)`. -/
theorem integral_norm_pow_four_stdGaussian :
    ∫ x : E, ‖x‖ ^ 4 ∂stdGaussian E =
      (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) + 2) := by
  let b := stdOrthonormalBasis ℝ E
  set d := Module.finrank ℝ E
  have hmp := measurePreserving_orthonormalBasis_stdGaussian b
  have hfun : (fun x : E => ‖x‖ ^ 4) =
      fun x : E => (∑ i : Fin d, (WithLp.ofLp (b.repr x) i) ^ 2) ^ 2 := by
    ext x
    have hnorm : ‖x‖ ^ 4 = (‖b.repr x‖ ^ 2) ^ 2 := by rw [b.repr.norm_map]; ring
    rw [hnorm, EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hfun]
  have hmeas_sq : Measurable (fun v : Fin d → ℝ => (∑ i : Fin d, v i ^ 2) ^ 2) :=
    (Finset.measurable_sum Finset.univ fun i _ => (measurable_pi_apply i).pow_const 2).pow_const 2
  have heq : ∫ x : E, (∑ i : Fin d, WithLp.ofLp (b.repr x) i ^ 2) ^ 2 ∂stdGaussian E =
      ∫ v : Fin d → ℝ, (∑ i : Fin d, v i ^ 2) ^ 2
        ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1) := by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hmeas_sq.aestronglyMeasurable]
  rw [heq]
  have hexpand : ∀ v : Fin d → ℝ,
      (∑ i : Fin d, v i ^ 2) ^ 2 = ∑ i : Fin d, ∑ j : Fin d, v i ^ 2 * v j ^ 2 := fun v => by
    rw [sq, Finset.sum_mul_sum]
  simp_rw [hexpand]
  have hint_pair : ∀ i j : Fin d, Integrable (fun v : Fin d → ℝ => v i ^ 2 * v j ^ 2)
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := fun i j => by
    have hi4 : Integrable (fun v : Fin d → ℝ => v i ^ 4)
        (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) :=
      integrable_comp_mp (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) i)
        (integrable_pow_gaussianReal 4)
    have hj4 : Integrable (fun v : Fin d → ℝ => v j ^ 4)
        (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) :=
      integrable_comp_mp (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) j)
        (integrable_pow_gaussianReal 4)
    have hsum_int : Integrable (fun v : Fin d → ℝ => v i ^ 4 + v j ^ 4)
        (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := hi4.add hj4
    refine hsum_int.mono'
      (((measurable_pi_apply i).pow_const 2).mul
        ((measurable_pi_apply j).pow_const 2)).aestronglyMeasurable
      (ae_of_all _ fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (v i ^ 2 - v j ^ 2)]
  rw [integral_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum Finset.univ fun j _ => hint_pair i j]
  have hinner_sum : ∀ i : Fin d,
      ∫ v : Fin d → ℝ, ∑ j : Fin d, v i ^ 2 * v j ^ 2
        ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1) = (d : ℝ) + 2 := fun i => by
    rw [integral_finsetSum Finset.univ fun j _ => hint_pair i j]
    have hterm : ∀ j : Fin d,
        ∫ v : Fin d → ℝ, v i ^ 2 * v j ^ 2
          ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1) = if j = i then 3 else 1 := fun j => by
      by_cases hji : j = i
      · subst hji
        simp only [ite_true]
        have hpow4 : (fun v : Fin d → ℝ => v j ^ 2 * v j ^ 2) = fun v => v j ^ 4 := by
          ext v; ring
        have hmp_j : MeasurePreserving (fun v : Fin d → ℝ => v j)
            (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) (gaussianReal 0 1) :=
          measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) j
        have h2 : ∫ v : Fin d → ℝ, v j ^ 4 ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1) =
            ∫ t : ℝ, t ^ 4 ∂gaussianReal 0 1 := by
          have h := integral_map (μ := Measure.pi (fun _ : Fin d => gaussianReal 0 1))
            (φ := fun v : Fin d → ℝ => v j) (f := fun t : ℝ => t ^ 4)
            (measurable_pi_apply j).aemeasurable (continuous_pow 4).aestronglyMeasurable
          rw [hmp_j.map_eq] at h
          exact h.symm
        rw [hpow4, h2, integral_pow_four_gaussianReal]
      · simp only [hji, ite_false]
        let f : Fin d → ℝ → ℝ := fun k t => if k = i ∨ k = j then t ^ 2 else 1
        have hprod : (fun v : Fin d → ℝ => v i ^ 2 * v j ^ 2) =
            fun v => ∏ k : Fin d, f k (v k) := by
          ext v
          rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i),
            Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
              (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, by simp [hji]⟩)]
          have hrest : ∏ k ∈ (Finset.univ \ {i}) \ {j}, f k (v k) = 1 :=
            Finset.prod_eq_one fun k hk => by
              simp only [Finset.mem_sdiff, Finset.mem_singleton] at hk
              simp [f, hk.1.2, hk.2]
          simp [f, hrest]
        rw [hprod, integral_fintype_prod_eq_prod]
        refine Finset.prod_eq_one fun k _ => ?_
        dsimp only [f]
        split_ifs
        · exact integral_sq_gaussianReal
        · simp
    simp_rw [hterm]
    have hsplit : ∑ x : Fin d, (if x = i then (3 : ℝ) else 1) =
        (∑ _x : Fin d, (1 : ℝ)) + (∑ x : Fin d, if x = i then (2 : ℝ) else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => by split_ifs <;> norm_num
    rw [hsplit]
    simp
  simp_rw [hinner_sum]
  simp
  ring

/-- Upper bound on the expected Euclidean norm of a standard Gaussian:
`∫ ‖x‖ ∂stdGaussian E ≤ √(finrank ℝ E)`. -/
theorem integral_norm_stdGaussian_le_sqrt :
    ∫ x : E, ‖x‖ ∂stdGaussian E ≤ Real.sqrt (Module.finrank ℝ E : ℝ) := by
  have hjensen : (∫ x : E, ‖x‖ ∂stdGaussian E) ^ 2 ≤ ∫ x : E, ‖x‖ ^ 2 ∂stdGaussian E := by
    have h := (convexOn_pow 2).map_integral_le (continuous_pow 2).continuousOn isClosed_Ici
      (ae_of_all _ fun x => norm_nonneg x) integrable_norm_stdGaussian
      (show Integrable ((fun t : ℝ => t ^ 2) ∘ fun x : E => ‖x‖) (stdGaussian E) from
        integrable_norm_sq_stdGaussian)
    simpa [Function.comp_def] using h
  rw [integral_norm_sq_stdGaussian] at hjensen
  exact Real.le_sqrt_of_sq_le hjensen

/-- Tight lower bound on the expected Euclidean norm of a standard Gaussian:
`d / √(d + 2) ≤ ∫ ‖x‖ ∂stdGaussian E`. -/
theorem div_sqrt_le_integral_norm_stdGaussian :
    (Module.finrank ℝ E : ℝ) / Real.sqrt ((Module.finrank ℝ E : ℝ) + 2) ≤
      ∫ x : E, ‖x‖ ∂stdGaussian E := by
  set d : ℝ := (Module.finrank ℝ E : ℝ)
  have hd_nn : 0 ≤ d := Nat.cast_nonneg _
  set c : ℝ := Real.sqrt (d + 2)
  have hc_pos : 0 < c := Real.sqrt_pos.mpr (by linarith)
  have hc_sq : c ^ 2 = d + 2 := Real.sq_sqrt (by linarith)
  -- Pointwise algebraic inequality: `3 c² t² ≤ 2 c³ t + t⁴` for `t ≥ 0, c > 0`.
  have hpt : ∀ x : E, 3 * c ^ 2 * ‖x‖ ^ 2 ≤ 2 * c ^ 3 * ‖x‖ + ‖x‖ ^ 4 := fun x => by
    have hfac : 2 * c ^ 3 * ‖x‖ + ‖x‖ ^ 4 - 3 * c ^ 2 * ‖x‖ ^ 2 =
        ‖x‖ * (‖x‖ - c) ^ 2 * (‖x‖ + 2 * c) := by ring
    have hnn : 0 ≤ ‖x‖ * (‖x‖ - c) ^ 2 * (‖x‖ + 2 * c) := by
      have h1 : 0 ≤ ‖x‖ := norm_nonneg x
      have h2 : 0 ≤ (‖x‖ - c) ^ 2 := sq_nonneg _
      have h3 : 0 ≤ ‖x‖ + 2 * c := by linarith
      positivity
    linarith
  have hint_lhs : Integrable (fun x : E => 3 * c ^ 2 * ‖x‖ ^ 2) (stdGaussian E) :=
    integrable_norm_sq_stdGaussian.const_mul (3 * c ^ 2)
  have hint_rhs : Integrable (fun x : E => 2 * c ^ 3 * ‖x‖ + ‖x‖ ^ 4) (stdGaussian E) :=
    (integrable_norm_stdGaussian.const_mul (2 * c ^ 3)).add integrable_norm_pow_four_stdGaussian
  have hint_le := integral_mono hint_lhs hint_rhs hpt
  rw [integral_const_mul, integral_add (integrable_norm_stdGaussian.const_mul (2 * c ^ 3))
    integrable_norm_pow_four_stdGaussian, integral_const_mul,
    integral_norm_sq_stdGaussian, integral_norm_pow_four_stdGaussian] at hint_le
  have hmul : d ≤ c * ∫ x : E, ‖x‖ ∂stdGaussian E := by
    have h1 : 2 * c ^ 2 * d ≤ 2 * c ^ 2 * (c * ∫ x : E, ‖x‖ ∂stdGaussian E) := by
      have hc3 : c ^ 3 = c ^ 2 * c := by ring
      rw [hc3] at hint_le
      nlinarith [hc_sq]
    have hpos2 : 0 < 2 * c ^ 2 := by positivity
    nlinarith
  exact (div_le_iff₀ hc_pos).mpr (by linarith)

/-- **Paley–Zygmund Radial Lower Bound:** in dimension `d ≥ 1`,
`stdGaussian E {x | √(d / 2) ≤ ‖x‖} ≥ 1 / 12`. -/
theorem stdGaussian_norm_ge_sqrt_half_dim [Nontrivial E] :
    ENNReal.ofReal (1 / 12 : ℝ) ≤
      stdGaussian E {x : E | Real.sqrt ((Module.finrank ℝ E : ℝ) / 2) ≤ ‖x‖} := by
  set d : ℝ := (Module.finrank ℝ E : ℝ)
  have hd_ge1 : (1 : ℝ) ≤ d := Nat.one_le_cast.mpr Module.finrank_pos
  set A : Set E := {x : E | Real.sqrt (d / 2) ≤ ‖x‖}
  have hAm : MeasurableSet A := isClosed_le continuous_const continuous_norm |>.measurableSet
  -- Step 1: `d / 2 ≤ ∫ x in A, ‖x‖² ∂stdGaussian E`.
  have hAc_le : ∫ x in Aᶜ, ‖x‖ ^ 2 ∂stdGaussian E ≤ d / 2 := by
    have hpt : ∀ x ∈ Aᶜ, ‖x‖ ^ 2 ≤ d / 2 := fun x hx => by
      have hlt : ‖x‖ < Real.sqrt (d / 2) := not_le.mp hx
      have hsq := sq_le_sq' (by linarith [norm_nonneg x, Real.sqrt_nonneg (d / 2)]) hlt.le
      rwa [Real.sq_sqrt (by linarith)] at hsq
    calc
      ∫ x in Aᶜ, ‖x‖ ^ 2 ∂stdGaussian E
        ≤ ∫ _x in Aᶜ, (d / 2) ∂stdGaussian E :=
          setIntegral_mono_on integrable_norm_sq_stdGaussian.integrableOn
            (integrable_const _).integrableOn hAm.compl hpt
      _ = (stdGaussian E).real Aᶜ * (d / 2) := by rw [setIntegral_const, smul_eq_mul]
      _ ≤ 1 * (d / 2) := by
          gcongr
          rw [Measure.real]
          exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
      _ = d / 2 := one_mul _
  have hsplit : ∫ x in A, ‖x‖ ^ 2 ∂stdGaussian E + ∫ x in Aᶜ, ‖x‖ ^ 2 ∂stdGaussian E = d := by
    rw [integral_add_compl hAm integrable_norm_sq_stdGaussian, integral_norm_sq_stdGaussian]
  have hA_ge : d / 2 ≤ ∫ x in A, ‖x‖ ^ 2 ∂stdGaussian E := by linarith
  -- Step 2: Pointwise AM-GM `2 c * 1_A * ‖x‖² ≤ c² * 1_A + ‖x‖⁴` with `c = 2 (d + 2)`.
  set c : ℝ := 2 * (d + 2)
  have hc_pos : 0 < c := by positivity
  have hpt : ∀ x : E, 2 * c * A.indicator (fun y => ‖y‖ ^ 2) x ≤
      c ^ 2 * A.indicator (fun _ => (1 : ℝ)) x + ‖x‖ ^ 4 := fun x => by
    by_cases hx : x ∈ A
    · simp only [indicator_of_mem hx]
      nlinarith [sq_nonneg (c - ‖x‖ ^ 2)]
    · simp only [indicator_of_notMem hx, mul_zero, zero_add]
      positivity
  have h_ind_sq : Integrable (A.indicator (fun y : E => ‖y‖ ^ 2)) (stdGaussian E) :=
    integrable_norm_sq_stdGaussian.indicator hAm
  have h_ind_one : Integrable (A.indicator (fun _ : E => (1 : ℝ))) (stdGaussian E) :=
    (integrable_const (1 : ℝ)).indicator hAm
  have hint_le := integral_mono (h_ind_sq.const_mul (2 * c))
    ((h_ind_one.const_mul (c ^ 2)).add integrable_norm_pow_four_stdGaussian) hpt
  rw [integral_const_mul, integral_indicator hAm,
    integral_add' (h_ind_one.const_mul (c ^ 2)) integrable_norm_pow_four_stdGaussian,
    integral_const_mul, integral_indicator hAm, setIntegral_const, smul_eq_mul, mul_one,
    integral_norm_pow_four_stdGaussian] at hint_le
  -- `2 c (d / 2) ≤ c² * γ(A) + d (d + 2)` with `c = 2 (d + 2)` gives
  -- `γ(A) ≥ d / (4 (d + 2)) ≥ 1/12` .
  have hreal : (1 / 12 : ℝ) ≤ (stdGaussian E).real A := by
    have h1 : d * (d + 2) ≤ 4 * (d + 2) ^ 2 * (stdGaussian E).real A := by
      have : c * d ≤ c ^ 2 * (stdGaussian E).real A + d * (d + 2) := by nlinarith
      dsimp only [c] at this
      nlinarith
    have h2 : 4 * (d + 2) ^ 2 * (1 / 12 : ℝ) ≤ d * (d + 2) := by nlinarith
    have hpos : 0 < 4 * (d + 2) ^ 2 := by positivity
    nlinarith
  rw [Measure.real] at hreal
  exact (ENNReal.ofReal_le_ofReal hreal).trans (ENNReal.ofReal_toReal (measure_ne_top _ _)).le

/-! #### Gaussian Width and Exact Proportionality to Mean Width -/

/-- **Gaussian width** of a convex body `K : ConvexBody E`:
$$w_G(K) := \int_E h_K(x)\,d\gamma_d(x).$$ -/
@[expose]
noncomputable def gaussianWidth (K : ConvexBody E) : ℝ :=
  ∫ x : E, supportFn K x ∂stdGaussian E

/-- `supportFn K` is integrable with respect to `stdGaussian E`. -/
lemma integrable_supportFn_stdGaussian (K : ConvexBody E) :
    Integrable (fun x : E => supportFn K x) (stdGaussian E) := by
  obtain ⟨R, hKR⟩ := K.isBounded.subset_closedBall (0 : E)
  set M := max R 0
  have hM_nn : 0 ≤ M := le_max_right R 0
  refine (integrable_norm_stdGaussian.const_mul M).mono'
    (continuous_supportFn K).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_le]
  have hupper : ∀ (v : E), ∀ y ∈ (K : Set E), ⟪y, v⟫ ≤ M * ‖v‖ := fun v y hy => by
    have hyM : ‖y‖ ≤ M := (mem_closedBall_zero_iff.mp (hKR hy)).trans (le_max_left R 0)
    exact (real_inner_le_norm y v).trans (mul_le_mul_of_nonneg_right hyM (norm_nonneg v))
  have h1 : supportFn K x ≤ M * ‖x‖ := supportFn_le_iff.mpr (hupper x)
  obtain ⟨y₀, hy₀⟩ := K.nonempty
  have h2 : -(M * ‖x‖) ≤ supportFn K x := by
    have hneg : ⟪y₀, -x⟫ ≤ M * ‖-x‖ := hupper (-x) y₀ hy₀
    rw [inner_neg_right, norm_neg] at hneg
    linarith [inner_le_supportFn hy₀ x]
  exact ⟨h2, h1⟩

/-- **Exact Proportionality of Gaussian Width and Mean Width:**
for every `K : ConvexBody E` in dimension `d ≥ 1`,
$$w_G(K) = \left(\int_E \|x\|\,d\gamma_d(x)\right) \cdot w(K).$$ -/
theorem gaussianWidth_eq_integral_norm_mul_meanWidth [Nontrivial E] (K : ConvexBody E) :
    gaussianWidth K = (∫ x : E, ‖x‖ ∂stdGaussian E) * meanWidth K := by
  have hmp := measurePreserving_homeomorphUnitSphereProd_stdGaussian (E := E)
  have hzero : stdGaussian E ({0} : Set E) = 0 := by
    rw [stdGaussian_eq_withDensity, withDensity_apply _ (measurableSet_singleton 0),
      Measure.restrict_eq_zero.mpr (measure_singleton 0), lintegral_zero_measure]
  have hemb : MeasurableEmbedding (Subtype.val : ({0}ᶜ : Set E) → E) :=
    MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : E)).compl
  have hmp_val : MeasurePreserving (Subtype.val : ({0}ᶜ : Set E) → E)
      ((stdGaussian E).comap (Subtype.val : ({0}ᶜ : Set E) → E))
      ((stdGaussian E).restrict ({0}ᶜ : Set E)) := by
    refine ⟨continuous_subtype_val.measurable, ?_⟩
    ext t ht
    rw [Measure.map_apply continuous_subtype_val.measurable ht, Measure.restrict_apply ht,
      Measure.comap_apply _ Subtype.val_injective (fun u hu => hemb.measurableSet_image.mpr hu) _
        (ht.preimage continuous_subtype_val.measurable)]
    congr 1; ext y; simp [and_comm]
  -- Helper: pull any integral over `stdGaussian E` to `sphere 0 1 × Ioi 0`.
  have hpull : ∀ f : E → ℝ, Continuous f →
      ∫ x : E, f x ∂stdGaussian E =
        ∫ p : sphere (0 : E) 1 × Ioi (0 : ℝ), f ((p.2 : ℝ) • p.1.1)
          ∂((sphereProb (volume : Measure E)).prod (stdGaussianRadial E)) := fun f _hf => by
    have hres_eq : (stdGaussian E).restrict ({0}ᶜ : Set E) = stdGaussian E :=
      Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; simpa using hzero)
    have h1 : ∫ x : E, f x ∂stdGaussian E =
        ∫ x : E, f x ∂((stdGaussian E).restrict ({0}ᶜ : Set E)) := by
      rw [hres_eq]
    rw [h1, ← hmp_val.integral_comp hemb f]
    have h2 := hmp.integral_comp (homeomorphUnitSphereProd E).toMeasurableEquiv.measurableEmbedding
      (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => f ((p.2 : ℝ) • p.1.1))
    rw [← h2]
    refine integral_congr_ae (ae_of_all _ fun ⟨x, hx⟩ => ?_)
    simp only [homeomorphUnitSphereProd_apply_fst_coe, homeomorphUnitSphereProd_apply_snd_coe]
    have hx0 : x ≠ 0 := hx
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx0), one_smul]
  have hG : gaussianWidth K =
      ∫ p : sphere (0 : E) 1 × Ioi (0 : ℝ), (p.2 : ℝ) * supportFn K p.1.1
        ∂((sphereProb (volume : Measure E)).prod (stdGaussianRadial E)) := by
    rw [gaussianWidth, hpull (supportFn K) (continuous_supportFn K)]
    refine integral_congr_ae (ae_of_all _ fun ⟨u, r⟩ => ?_)
    exact supportFn_smul K r.2.out.le u.1
  have hN : ∫ x : E, ‖x‖ ∂stdGaussian E =
      ∫ r : Ioi (0 : ℝ), (r : ℝ) ∂stdGaussianRadial E := by
    rw [hpull norm continuous_norm]
    have hfun : (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => ‖(p.2 : ℝ) • p.1.1‖) =
        fun p => (1 : ℝ) * (p.2 : ℝ) := by
      ext ⟨u, r⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos r.2.out, mem_sphere_zero_iff_norm.mp u.2,
        mul_one, one_mul]
    rw [hfun, integral_prod_mul (f := fun _ : sphere (0 : E) 1 => (1 : ℝ))
      (g := fun r : Ioi (0 : ℝ) => (r : ℝ))]
    simp
  rw [hG, hN, mul_comm, meanWidth]
  have hmul := integral_prod_mul (μ := sphereProb (volume : Measure E))
    (ν := stdGaussianRadial E) (f := fun u : sphere (0 : E) 1 => supportFn K u.1)
    (g := fun r : Ioi (0 : ℝ) => (r : ℝ))
  simpa [mul_comm] using hmul

end PolarAndMoments

/-! ### 3. Gaussian Enlargement and Lipschitz Concentration via Prékopa–Leindler -/

section GaussianConcentration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Gaussian Enlargement Inequality (Two-Set Form, Maurey / Ball Lecture 7):**
if measurable sets `A, B ⊆ E` satisfy `t ≤ ‖x - y‖` for all `x ∈ A` and `y ∈ B` (with `t ≥ 0`),
then
$$\gamma_d(A)\,\gamma_d(B) \le e^{-t^2 / 4}.$$ -/
theorem gaussian_enlargement_two_sets {A B : Set E} (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    {t : ℝ} (ht : 0 ≤ t) (hdist : ∀ x ∈ A, ∀ y ∈ B, t ≤ ‖x - y‖) :
    stdGaussian E A * stdGaussian E B ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / 4)) := by
  let f : E → ℝ≥0∞ := A.indicator (fun x => ENNReal.ofReal (stdGaussianDensity x))
  let g : E → ℝ≥0∞ := B.indicator (fun y => ENNReal.ofReal (stdGaussianDensity y))
  let h : E → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (-(t ^ 2) / 8) * stdGaussianDensity z)
  have hf : Measurable f :=
    (ENNReal.measurable_ofReal.comp measurable_stdGaussianDensity).indicator hAm
  have hg : Measurable g :=
    (ENNReal.measurable_ofReal.comp measurable_stdGaussianDensity).indicator hBm
  have hh : Measurable h :=
    ENNReal.measurable_ofReal.comp (continuous_const.mul continuous_stdGaussianDensity).measurable
  have hcond : ∀ x y : E,
      f x ^ (1 - (1 / 2 : ℝ)) * g y ^ (1 / 2 : ℝ) ≤
        h ((1 - (1 / 2 : ℝ)) • x + (1 / 2 : ℝ) • y) := by
    intro x y
    have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [hhalf]
    by_cases hx : x ∈ A
    · by_cases hy : y ∈ B
      · simp only [f, g, h, indicator_of_mem hx, indicator_of_mem hy]
        rw [ENNReal.ofReal_rpow_of_nonneg (stdGaussianDensity_nonneg x) (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (stdGaussianDensity_nonneg y) (by norm_num),
          ← ENNReal.ofReal_mul (Real.rpow_nonneg (stdGaussianDensity_nonneg x) _)]
        apply ENNReal.ofReal_le_ofReal
        have hpara : ‖x‖ ^ 2 + ‖y‖ ^ 2 =
            2 * ‖(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y‖ ^ 2 + ‖x - y‖ ^ 2 / 2 := by
          have h1 := parallelogram_law_with_norm ℝ x y
          have hmid : x + y = (2 : ℝ) • ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) := by
            rw [smul_add, smul_smul, smul_smul]; norm_num
          rw [hmid, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h1
          nlinarith
        have htsq : t ^ 2 ≤ ‖x - y‖ ^ 2 :=
          pow_le_pow_left₀ ht (hdist x hx y hy) 2
        have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
        unfold stdGaussianDensity
        rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le,
          Real.mul_rpow (by positivity) (Real.exp_pos _).le,
          ← Real.rpow_mul h2pi_pos.le,
          ← Real.exp_mul, ← Real.exp_mul]
        have hcoef : (2 * Real.pi) ^ ((-(Module.finrank ℝ E : ℝ) / 2) * (1 / 2)) *
            (2 * Real.pi) ^ ((-(Module.finrank ℝ E : ℝ) / 2) * (1 / 2)) =
            (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) := by
          rw [← Real.rpow_add h2pi_pos]; congr 1; ring
        have hexp_le : Real.exp (-(‖x‖ ^ 2) / 2 * (1 / 2)) * Real.exp (-(‖y‖ ^ 2) / 2 * (1 / 2)) ≤
            Real.exp (-(t ^ 2) / 8) *
              Real.exp (-(‖(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y‖ ^ 2) / 2) := by
          rw [← Real.exp_add, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          linarith
        calc
          ((2 * Real.pi) ^ ((-(Module.finrank ℝ E : ℝ) / 2) * (1 / 2)) *
              Real.exp (-(‖x‖ ^ 2) / 2 * (1 / 2))) *
            ((2 * Real.pi) ^ ((-(Module.finrank ℝ E : ℝ) / 2) * (1 / 2)) *
              Real.exp (-(‖y‖ ^ 2) / 2 * (1 / 2)))
            = (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
                (Real.exp (-(‖x‖ ^ 2) / 2 * (1 / 2)) * Real.exp (-(‖y‖ ^ 2) / 2 * (1 / 2))) := by
              rw [← hcoef]; ring
          _ ≤ (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
                (Real.exp (-(t ^ 2) / 8) *
                  Real.exp (-(‖(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y‖ ^ 2) / 2)) := by
              gcongr
          _ = Real.exp (-(t ^ 2) / 8) *
                ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
                  Real.exp (-(‖(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y‖ ^ 2) / 2)) := by ring
      · simp [g, indicator_of_notMem hy]
    · simp [f, indicator_of_notMem hx]
  have hpl := prekopa_leindler (t := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hf hg hh hcond
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [hhalf] at hpl
  have hIf : ∫⁻ x, f x = stdGaussian E A := by
    rw [stdGaussian_eq_withDensity, withDensity_apply _ hAm, ← lintegral_indicator hAm]
  have hIg : ∫⁻ y, g y = stdGaussian E B := by
    rw [stdGaussian_eq_withDensity, withDensity_apply _ hBm, ← lintegral_indicator hBm]
  have hIh : ∫⁻ z, h z = ENNReal.ofReal (Real.exp (-(t ^ 2) / 8)) := by
    have hfun : h = fun z => ENNReal.ofReal (Real.exp (-(t ^ 2) / 8)) *
        ENNReal.ofReal (stdGaussianDensity z) := by
      ext z; dsimp only [h]; rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    have hm : Measurable (fun z : E => ENNReal.ofReal (stdGaussianDensity z)) :=
      ENNReal.measurable_ofReal.comp measurable_stdGaussianDensity
    rw [hfun]
    dsimp only
    rw [lintegral_const_mul _ hm, lintegral_stdGaussianDensity_eq_one, mul_one]
  rw [hIf, hIg, hIh] at hpl
  -- Square both sides: `(a^(1/2) * b^(1/2))^2 = a * b`.
  have hsq := ENNReal.rpow_le_rpow hpl (by norm_num : (0 : ℝ) ≤ 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one, ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.exp_mul] at hsq
  simpa [show -(t ^ 2) / 8 * 2 = -(t ^ 2) / 4 by ring] using hsq

/-- **Gaussian Enlargement Inequality (Metric Thickening Form):**
for any measurable `A ⊆ E` and `t > 0`,
$$\gamma_d(A)\,\gamma_d\bigl((\mathrm{thickening}\;t\;A)^c\bigr) \le e^{-t^2 / 4}.$$ -/
theorem gaussian_enlargement_thickening {A : Set E} (hAm : MeasurableSet A) {t : ℝ} (ht : 0 < t) :
    stdGaussian E A * stdGaussian E (Metric.thickening t A)ᶜ ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2) / 4)) := by
  refine gaussian_enlargement_two_sets hAm Metric.isOpen_thickening.measurableSet.compl ht.le
    fun x hx y hy => ?_
  by_contra hlt
  push Not at hlt
  have hmem : y ∈ Metric.thickening t A := by
    rw [Metric.mem_thickening_iff]
    exact ⟨x, hx, by simpa [dist_eq_norm, norm_sub_rev] using hlt⟩
  exact hy hmem

/-- Exponential integrability of any Lipschitz function under `stdGaussian E`. -/
lemma integrable_exp_lipschitz_stdGaussian {L : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith L f) (a : ℝ) :
    Integrable (fun x : E => Real.exp (a * f x)) (stdGaussian E) := by
  rw [integrable_stdGaussian_iff]
  have hmeas : AEStronglyMeasurable (fun x : E =>
    stdGaussianDensity x • Real.exp (a * f x)) volume :=
    (continuous_stdGaussianDensity.mul
      (Real.continuous_exp.comp (continuous_const.mul hf.continuous))).aestronglyMeasurable
  set c : ℝ := |a| * (L : ℝ)
  have hc_nn : 0 ≤ c := by positivity
  -- Dominate `stdGaussianDensity x * exp (a * f x)` by `C * stdGaussianDensity ((1/√2) • x)`.
  have hbase : Integrable (fun x : E => stdGaussianDensity ((1 / Real.sqrt 2 : ℝ) • x)) volume := by
    have h1 : Integrable (stdGaussianDensity : E → ℝ) volume := by
      have h := integrable_stdGaussian_iff.mp (integrable_const (1 : ℝ) (μ := stdGaussian E))
      simpa using h
    have hpos : (1 / Real.sqrt 2 : ℝ) ≠ 0 := by positivity
    simpa [smul_eq_mul] using h1.comp_smul hpos
  refine (hbase.const_mul (Real.exp (|a| * |f 0| + c ^ 2))).mono' hmeas (ae_of_all _ fun x => ?_)
  rw [smul_eq_mul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (stdGaussianDensity_nonneg x) (Real.exp_pos _).le)]
  have hf_bd : a * f x ≤ |a| * |f 0| + c * ‖x‖ := by
    have hlip : |f x - f 0| ≤ (L : ℝ) * ‖x‖ := by
      simpa [dist_eq_norm, Real.dist_eq] using hf.dist_le_mul x 0
    have hfx : |f x| ≤ |f 0| + (L : ℝ) * ‖x‖ := by
      have := abs_sub_abs_le_abs_sub (f x) (f 0)
      linarith
    calc
      a * f x ≤ |a * f x| := le_abs_self _
      _ = |a| * |f x| := abs_mul a (f x)
      _ ≤ |a| * (|f 0| + (L : ℝ) * ‖x‖) := mul_le_mul_of_nonneg_left hfx (abs_nonneg a)
      _ = |a| * |f 0| + c * ‖x‖ := by dsimp only [c]; ring
  have hquad : c * ‖x‖ - ‖x‖ ^ 2 / 2 ≤ c ^ 2 - ‖x‖ ^ 2 / 4 := by
    nlinarith [sq_nonneg (‖x‖ / 2 - c)]
  have hnorm_scale : ‖(1 / Real.sqrt 2 : ℝ) • x‖ ^ 2 = ‖x‖ ^ 2 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.sqrt 2),
      mul_pow, div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  unfold stdGaussianDensity
  rw [hnorm_scale]
  have h2pi_nn : 0 ≤ (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) := by positivity
  calc
    (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (-(‖x‖ ^ 2) / 2) * Real.exp (a * f x)
      = (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (a * f x - ‖x‖ ^ 2 / 2) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
          Real.exp (|a| * |f 0| + c ^ 2 - ‖x‖ ^ 2 / 4) := by
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) h2pi_nn
    _ = Real.exp (|a| * |f 0| + c ^ 2) *
          ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (-(‖x‖ ^ 2 / 2) / 2)) := by
        rw [show Real.exp (|a| * |f 0| + c ^ 2 - ‖x‖ ^ 2 / 4) =
          Real.exp (|a| * |f 0| + c ^ 2) * Real.exp (-(‖x‖ ^ 2 / 2) / 2) by
            rw [← Real.exp_add]; congr 1; ring]
        ring

/-- Any Lipschitz function on `E` is integrable with respect to `stdGaussian E`. -/
lemma integrable_lipschitz_stdGaussian {L : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith L f) :
    Integrable f (stdGaussian E) := by
  refine ((integrable_const |f 0|).add (integrable_norm_stdGaussian.const_mul (L : ℝ))).mono'
    hf.continuous.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs]
  have hlip : |f x - f 0| ≤ (L : ℝ) * ‖x‖ := by
    simpa [dist_eq_norm, Real.dist_eq] using hf.dist_le_mul x 0
  linarith [abs_sub_abs_le_abs_sub (f x) (f 0)]

/-- **Gaussian Sub-Gaussian MGF Bound (Maurey / Bobkov–Ledoux via Prékopa–Leindler):**
for any `L`-Lipschitz `f : E → ℝ` and any `s : ℝ`,
$$\int_E e^{s (f(x) - \mathbb{E}[f])}\,d\gamma_d(x) \le e^{s^2 L^2}.$$ -/
theorem gaussian_lipschitz_mgf_le {L : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith L f) (s : ℝ) :
    ∫ x : E, Real.exp (s * (f x - ∫ y : E, f y ∂stdGaussian E)) ∂stdGaussian E ≤
      Real.exp (s ^ 2 * (L : ℝ) ^ 2) := by
  let F : E → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (s * f x) * stdGaussianDensity x)
  let G : E → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (-s * f y) * stdGaussianDensity y)
  let H : E → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (s ^ 2 * (L : ℝ) ^ 2 / 2) * stdGaussianDensity z)
  have hF : Measurable F := ENNReal.measurable_ofReal.comp
    ((Real.continuous_exp.comp
      (continuous_const.mul hf.continuous)).mul continuous_stdGaussianDensity).measurable
  have hG : Measurable G := ENNReal.measurable_ofReal.comp
    ((Real.continuous_exp.comp
      (continuous_const.mul hf.continuous)).mul continuous_stdGaussianDensity).measurable
  have hH : Measurable H := ENNReal.measurable_ofReal.comp
    (continuous_const.mul continuous_stdGaussianDensity).measurable
  have hcond : ∀ x y : E,
      F x ^ (1 - (1 / 2 : ℝ)) * G y ^ (1 / 2 : ℝ) ≤
        H ((1 - (1 / 2 : ℝ)) • x + (1 / 2 : ℝ) • y) := by
    intro x y
    have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [hhalf]
    dsimp only [F, G, H]
    rw [ENNReal.ofReal_rpow_of_nonneg
        (mul_nonneg (Real.exp_pos _).le (stdGaussianDensity_nonneg x)) (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg
        (mul_nonneg (Real.exp_pos _).le (stdGaussianDensity_nonneg y)) (by norm_num),
      ← ENNReal.ofReal_mul
        (Real.rpow_nonneg (mul_nonneg (Real.exp_pos _).le (stdGaussianDensity_nonneg x)) _)]
    apply ENNReal.ofReal_le_ofReal
    have hpara : ‖x‖ ^ 2 + ‖y‖ ^ 2 =
        2 * ‖(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y‖ ^ 2 + ‖x - y‖ ^ 2 / 2 := by
      have h1 := parallelogram_law_with_norm ℝ x y
      have hmid : x + y = (2 : ℝ) • ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) := by
        rw [smul_add, smul_smul, smul_smul]; norm_num
      rw [hmid, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h1
      nlinarith
    have hlip : s * (f x - f y) ≤ |s| * (L : ℝ) * ‖x - y‖ := by
      have h1 : |f x - f y| ≤ (L : ℝ) * ‖x - y‖ := by
        simpa [dist_eq_norm, Real.dist_eq] using hf.dist_le_mul x y
      calc
        s * (f x - f y) ≤ |s * (f x - f y)| := le_abs_self _
        _ = |s| * |f x - f y| := abs_mul _ _
        _ ≤ |s| * ((L : ℝ) * ‖x - y‖) := mul_le_mul_of_nonneg_left h1 (abs_nonneg s)
        _ = |s| * (L : ℝ) * ‖x - y‖ := by ring
    have hcomp_sq : |s| * (L : ℝ) * ‖x - y‖ / 2 - ‖x - y‖ ^ 2 / 8 ≤ s ^ 2 * (L : ℝ) ^ 2 / 2 := by
      have hsq : 0 ≤ (‖x - y‖ - 2 * |s| * (L : ℝ)) ^ 2 := sq_nonneg _
      nlinarith [sq_abs s]
    have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
    unfold stdGaussianDensity
    rw [Real.mul_rpow (Real.exp_pos _).le (by positivity),
      Real.mul_rpow (Real.exp_pos _).le (by positivity),
      Real.mul_rpow (by positivity) (Real.exp_pos _).le,
      Real.mul_rpow (by positivity) (Real.exp_pos _).le,
      ← Real.rpow_mul h2pi_pos.le,
      ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_mul]
    have hcoef : (2 * Real.pi) ^ ((-(Module.finrank ℝ E : ℝ) / 2) * (1 / 2)) *
        (2 * Real.pi) ^ ((-(Module.finrank ℝ E : ℝ) / 2) * (1 / 2)) =
        (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) := by
      rw [← Real.rpow_add h2pi_pos]; congr 1; ring
    have hrearr :
        (Real.exp (s * f x * (1 / 2)) *
            ((2 * Real.pi) ^ ((-(Module.finrank ℝ E : ℝ) / 2) * (1 / 2)) *
              Real.exp (-(‖x‖ ^ 2) / 2 * (1 / 2)))) *
          (Real.exp (-s * f y * (1 / 2)) *
            ((2 * Real.pi) ^ ((-(Module.finrank ℝ E : ℝ) / 2) * (1 / 2)) *
              Real.exp (-(‖y‖ ^ 2) / 2 * (1 / 2)))) =
        (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
          Real.exp (s * (f x - f y) / 2 - (‖x‖ ^ 2 + ‖y‖ ^ 2) / 4) := by
      rw [← hcoef]
      have hexp : Real.exp (s * f x * (1 / 2)) * Real.exp (-(‖x‖ ^ 2) / 2 * (1 / 2)) *
          (Real.exp (-s * f y * (1 / 2)) * Real.exp (-(‖y‖ ^ 2) / 2 * (1 / 2))) =
          Real.exp (s * (f x - f y) / 2 - (‖x‖ ^ 2 + ‖y‖ ^ 2) / 4) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1; ring
      rw [← hexp]; ring
    rw [hrearr]
    have hrhs : Real.exp (s ^ 2 * (L : ℝ) ^ 2 / 2) *
        ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
          Real.exp (-(‖(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y‖ ^ 2) / 2)) =
        (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
          Real.exp (s ^ 2 * (L : ℝ) ^ 2 / 2 - ‖(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y‖ ^ 2 / 2) := by
      rw [← mul_left_comm, ← Real.exp_add]; congr 2; ring
    rw [hrhs]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
  have hpl := prekopa_leindler (t := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hF hG hH hcond
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [hhalf] at hpl
  have hsq := ENNReal.rpow_le_rpow hpl (by norm_num : (0 : ℝ) ≤ 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one, ENNReal.rpow_one] at hsq
  have hIF : ∫⁻ x, F x = ENNReal.ofReal (∫ x, Real.exp (s * f x) ∂stdGaussian E) := by
    rw [integral_stdGaussian]
    have hint := integrable_stdGaussian_iff.mp (integrable_exp_lipschitz_stdGaussian hf s)
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun x => mul_nonneg (stdGaussianDensity_nonneg x) (Real.exp_pos _).le)]
    refine lintegral_congr fun x => by simp [F, smul_eq_mul, mul_comm]
  have hIG : ∫⁻ y, G y = ENNReal.ofReal (∫ y, Real.exp (-s * f y) ∂stdGaussian E) := by
    rw [integral_stdGaussian]
    have hint := integrable_stdGaussian_iff.mp (integrable_exp_lipschitz_stdGaussian hf (-s))
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun y => mul_nonneg (stdGaussianDensity_nonneg y) (Real.exp_pos _).le)]
    refine lintegral_congr fun y => by simp [G, smul_eq_mul, mul_comm]
  have hIH : (∫⁻ z, H z) ^ (2 : ℝ) = ENNReal.ofReal (Real.exp (s ^ 2 * (L : ℝ) ^ 2)) := by
    have hfun : H = fun z => ENNReal.ofReal (Real.exp (s ^ 2 * (L : ℝ) ^ 2 / 2)) *
        ENNReal.ofReal (stdGaussianDensity z) := by
      ext z; dsimp only [H]; rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    have hm : Measurable (fun z : E => ENNReal.ofReal (stdGaussianDensity z)) :=
      ENNReal.measurable_ofReal.comp measurable_stdGaussianDensity
    rw [hfun]
    dsimp only
    rw [lintegral_const_mul _ hm, lintegral_stdGaussianDensity_eq_one, mul_one,
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.exp_mul]
    congr 2; ring
  rw [hIF, hIG, hIH, ← ENNReal.ofReal_mul (integral_nonneg fun _ => (Real.exp_pos _).le)] at hsq
  have hprod : (∫ x, Real.exp (s * f x) ∂stdGaussian E) *
      (∫ y, Real.exp (-s * f y) ∂stdGaussian E) ≤ Real.exp (s ^ 2 * (L : ℝ) ^ 2) :=
    (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).mp hsq
  -- Apply Jensen's inequality to `-s * f`: `exp (-s * E[f]) ≤ ∫ exp (-s * f)`.
  have hjensen : Real.exp (-s * ∫ y : E, f y ∂stdGaussian E) ≤
      ∫ y : E, Real.exp (-s * f y) ∂stdGaussian E := by
    have h1 := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (ae_of_all _ fun _ => mem_univ _)
      ((integrable_lipschitz_stdGaussian hf).const_mul (-s))
      (show Integrable (Real.exp ∘ fun x : E => (-s) * f x) (stdGaussian E) from
        integrable_exp_lipschitz_stdGaussian hf (-s))
    rw [integral_const_mul] at h1
    simpa [Function.comp_def] using h1
  have hshift : ∫ x : E, Real.exp (s * (f x - ∫ y : E, f y ∂stdGaussian E)) ∂stdGaussian E =
      (∫ x : E, Real.exp (s * f x) ∂stdGaussian E) *
        Real.exp (-s * ∫ y : E, f y ∂stdGaussian E) := by
    rw [← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [← Real.exp_add]; congr 1; ring
  rw [hshift]
  exact (mul_le_mul_of_nonneg_left hjensen
    (integral_nonneg fun _ => (Real.exp_pos _).le)).trans hprod

/-- **Gaussian Lipschitz Concentration around the Mean (One-Sided):**
for `L`-Lipschitz `f : E → ℝ` (`L > 0`) and `t ≥ 0`,
$$\gamma_d\bigl\{x : f(x) - \mathbb{E}[f] \ge t\bigr\} \le e^{-t^2 / (4 L^2)}.$$ -/
theorem gaussian_lipschitz_upper_tail {L : ℝ≥0} (hL : 0 < L) {f : E → ℝ} (hf : LipschitzWith L f)
    {t : ℝ} (ht : 0 ≤ t) :
    stdGaussian E {x : E | t ≤ f x - ∫ y : E, f y ∂stdGaussian E} ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2) / (4 * (L : ℝ) ^ 2))) := by
  set μf := ∫ y : E, f y ∂stdGaussian E
  set s : ℝ := t / (2 * (L : ℝ) ^ 2)
  have hL_pos : (0 : ℝ) < L := hL
  have hs_nn : 0 ≤ s := by positivity
  have hsub : {x : E | t ≤ f x - μf} ⊆
      {x : E | ENNReal.ofReal (Real.exp (s * t)) ≤ ENNReal.ofReal (Real.exp (s * (f x - μf)))} := by
    intro x hx
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx hs_nn))
  have hmarkov : ENNReal.ofReal (Real.exp (s * t)) *
      stdGaussian E {x : E | t ≤ f x - μf} ≤
      ∫⁻ x : E, ENNReal.ofReal (Real.exp (s * (f x - μf))) ∂stdGaussian E := by
    calc
      ENNReal.ofReal (Real.exp (s * t)) * stdGaussian E {x : E | t ≤ f x - μf}
        ≤ ENNReal.ofReal (Real.exp (s * t)) *
            stdGaussian E {x : E | ENNReal.ofReal (Real.exp (s * t)) ≤
              ENNReal.ofReal (Real.exp (s * (f x - μf)))} := by gcongr
      _ ≤ ∫⁻ x : E, ENNReal.ofReal (Real.exp (s * (f x - μf))) ∂stdGaussian E :=
          mul_meas_ge_le_lintegral₀
            (ENNReal.measurable_ofReal.comp
              (Real.continuous_exp.comp
                (continuous_const.mul
                  (hf.continuous.sub continuous_const))).measurable).aemeasurable
            _
  have hint : Integrable (fun x : E => Real.exp (s * (f x - μf))) (stdGaussian E) := by
    have hfun : (fun x : E => Real.exp (s * (f x - μf))) =
        fun x => Real.exp (-s * μf) * Real.exp (s * f x) := by
      ext x; rw [← Real.exp_add]; congr 1; ring
    rw [hfun]
    exact (integrable_exp_lipschitz_stdGaussian hf s).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ =>
    (Real.exp_pos _).le)] at hmarkov
  have hmgf := gaussian_lipschitz_mgf_le hf s
  have hle1 : ENNReal.ofReal (Real.exp (s * t)) * stdGaussian E {x : E | t ≤ f x - μf} ≤
      ENNReal.ofReal (Real.exp (s ^ 2 * (L : ℝ) ^ 2)) :=
    hmarkov.trans (ENNReal.ofReal_le_ofReal hmgf)
  have hpos : ENNReal.ofReal (Real.exp (s * t)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hfin : ENNReal.ofReal (Real.exp (s * t)) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc
    stdGaussian E {x : E | t ≤ f x - μf}
      = (ENNReal.ofReal (Real.exp (s * t)))⁻¹ *
          (ENNReal.ofReal (Real.exp (s * t)) * stdGaussian E {x : E | t ≤ f x - μf}) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hpos hfin, one_mul]
    _ ≤ (ENNReal.ofReal (Real.exp (s * t)))⁻¹ *
          ENNReal.ofReal (Real.exp (s ^ 2 * (L : ℝ) ^ 2)) := by gcongr
    _ = ENNReal.ofReal (Real.exp (-(s * t))) *
          ENNReal.ofReal (Real.exp (s ^ 2 * (L : ℝ) ^ 2)) := by
        rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]
    _ = ENNReal.ofReal (Real.exp (s ^ 2 * (L : ℝ) ^ 2 - s * t)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2; ring
    _ = ENNReal.ofReal (Real.exp (-(t ^ 2) / (4 * (L : ℝ) ^ 2))) := by
        congr 2; dsimp only [s]; field_simp [hL_pos.ne']; ring

/-- **Gaussian Lipschitz Concentration around the Mean (Two-Sided):**
for `L`-Lipschitz `f : E → ℝ` (`L > 0`) and `t ≥ 0`,
$$\gamma_d\bigl\{x : |f(x) - \mathbb{E}[f]| \ge t\bigr\} \le 2 e^{-t^2 / (4 L^2)}.$$ -/
theorem gaussian_lipschitz_concentration_mean {L : ℝ≥0} (hL : 0 < L) {f : E → ℝ}
    (hf : LipschitzWith L f) {t : ℝ} (ht : 0 ≤ t) :
    stdGaussian E {x : E | t ≤ |f x - ∫ y : E, f y ∂stdGaussian E|} ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (4 * (L : ℝ) ^ 2))) := by
  set μf := ∫ y : E, f y ∂stdGaussian E
  have hneg_lip : LipschitzWith L (fun x => -f x) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simpa [Real.dist_eq, abs_neg] using hf.dist_le_mul x y
  have hsub : {x : E | t ≤ |f x - μf|} ⊆
      {x : E | t ≤ f x - μf} ∪ {x : E | t ≤ (-f x) - ∫ y : E, (-f y) ∂stdGaussian E} := by
    intro x hx
    rw [mem_ofPred_eq, le_abs] at hx
    rcases hx with h1 | h2
    · exact Or.inl h1
    · right
      simp only [mem_ofPred_eq, integral_neg, sub_neg_eq_add]
      linarith
  have h1 := gaussian_lipschitz_upper_tail hL hf ht
  have h2 := gaussian_lipschitz_upper_tail hL hneg_lip ht
  calc
    stdGaussian E {x : E | t ≤ |f x - μf|}
      ≤ stdGaussian E ({x : E | t ≤ f x - μf} ∪
          {x : E | t ≤ (-f x) - ∫ y : E, (-f y) ∂stdGaussian E}) := measure_mono hsub
    _ ≤ stdGaussian E {x : E | t ≤ f x - μf} +
          stdGaussian E {x : E | t ≤ (-f x) - ∫ y : E, (-f y) ∂stdGaussian E} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / (4 * (L : ℝ) ^ 2))) +
          ENNReal.ofReal (Real.exp (-(t ^ 2) / (4 * (L : ℝ) ^ 2))) := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (4 * (L : ℝ) ^ 2))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, two_mul]

/-- **Gaussian Lipschitz Concentration around a Median:**
if `f : E → ℝ` is `L`-Lipschitz (`L > 0`) and `m : ℝ` is a median of `f` under `stdGaussian E`
(`γ_d {f ≤ m} ≥ 1/2` and `γ_d {m ≤ f} ≥ 1/2`), then for every `t ≥ 0`:
$$\gamma_d\bigl\{x : |f(x) - m| > t\bigr\} \le 4 e^{-t^2 / (4 L^2)}.$$ -/
theorem gaussian_lipschitz_concentration_median {L : ℝ≥0} (hL : 0 < L) {f : E → ℝ}
    (hf : LipschitzWith L f) {m : ℝ}
    (hm_le : ENNReal.ofReal (1 / 2 : ℝ) ≤ stdGaussian E {x : E | f x ≤ m})
    (hm_ge : ENNReal.ofReal (1 / 2 : ℝ) ≤ stdGaussian E {x : E | m ≤ f x})
    {t : ℝ} (ht : 0 ≤ t) :
    stdGaussian E {x : E | t < |f x - m|} ≤
      ENNReal.ofReal (4 * Real.exp (-(t ^ 2) / (4 * (L : ℝ) ^ 2))) := by
  have hL_pos : (0 : ℝ) < L := hL
  -- Upper tail `{m + t < f x}` separated by `t / L` from `{f x ≤ m}`.
  have hupper : stdGaussian E {x : E | m + t < f x} ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (4 * (L : ℝ) ^ 2))) := by
    have hA_m : MeasurableSet {x : E | f x ≤ m} :=
      (isClosed_le hf.continuous continuous_const).measurableSet
    have hB_m : MeasurableSet {x : E | m + t < f x} :=
      (isOpen_lt continuous_const hf.continuous).measurableSet
    have hsep : ∀ x ∈ {x : E | f x ≤ m}, ∀ y ∈ {x : E | m + t < f x},
        t / (L : ℝ) ≤ ‖x - y‖ := fun x hx y hy => by
      have hlip : |f y - f x| ≤ (L : ℝ) * ‖x - y‖ := by
        have h := hf.dist_le_mul y x
        rw [Real.dist_eq, dist_eq_norm, norm_sub_rev] at h
        exact h
      have hgt : t < f y - f x := by linarith [mem_ofPred_eq.mp hx, mem_ofPred_eq.mp hy]
      exact (div_le_iff₀ hL_pos).mpr (by linarith [(le_abs_self (f y - f x)).trans hlip])
    have henl := gaussian_enlargement_two_sets hA_m hB_m (div_nonneg ht hL_pos.le) hsep
    have hmul : ENNReal.ofReal (1 / 2 : ℝ) * stdGaussian E {x : E | m + t < f x} ≤
        ENNReal.ofReal (Real.exp (-(t ^ 2) / (4 * (L : ℝ) ^ 2))) := by
      calc
        ENNReal.ofReal (1 / 2 : ℝ) * stdGaussian E {x : E | m + t < f x}
          ≤ stdGaussian E {x : E | f x ≤ m} * stdGaussian E {x : E | m + t < f x} := by gcongr
        _ ≤ ENNReal.ofReal (Real.exp (-((t / (L : ℝ)) ^ 2) / 4)) := henl
        _ = ENNReal.ofReal (Real.exp (-(t ^ 2) / (4 * (L : ℝ) ^ 2))) := by
            congr 2; rw [div_pow]; ring
    calc
      stdGaussian E {x : E | m + t < f x}
        = ENNReal.ofReal 2 *
          (ENNReal.ofReal (1 / 2 : ℝ) * stdGaussian E {x : E | m + t < f x}) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num),
            show (2 : ℝ) * (1 / 2) = 1 by norm_num,
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (Real.exp (-(t ^ 2) / (4 * (L : ℝ) ^ 2))) := by gcongr
      _ = ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (4 * (L : ℝ) ^ 2))) :=
          (ENNReal.ofReal_mul (by norm_num)).symm
  -- Lower tail `{f x < m - t}` separated by `t / L` from `{m ≤ f x}`.
  have hlower : stdGaussian E {x : E | f x < m - t} ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (4 * (L : ℝ) ^ 2))) := by
    have hA_m : MeasurableSet {x : E | m ≤ f x} :=
      (isClosed_le continuous_const hf.continuous).measurableSet
    have hB_m : MeasurableSet {x : E | f x < m - t} :=
      (isOpen_lt hf.continuous continuous_const).measurableSet
    have hsep : ∀ x ∈ {x : E | m ≤ f x}, ∀ y ∈ {x : E | f x < m - t},
        t / (L : ℝ) ≤ ‖x - y‖ := fun x hx y hy => by
      have hlip : |f x - f y| ≤ (L : ℝ) * ‖x - y‖ := by
        simpa [dist_eq_norm, Real.dist_eq] using hf.dist_le_mul x y
      have hgt : t < f x - f y := by linarith [mem_ofPred_eq.mp hx, mem_ofPred_eq.mp hy]
      exact (div_le_iff₀ hL_pos).mpr (by linarith [(le_abs_self (f x - f y)).trans hlip])
    have henl := gaussian_enlargement_two_sets hA_m hB_m (div_nonneg ht hL_pos.le) hsep
    have hmul : ENNReal.ofReal (1 / 2 : ℝ) * stdGaussian E {x : E | f x < m - t} ≤
        ENNReal.ofReal (Real.exp (-(t ^ 2) / (4 * (L : ℝ) ^ 2))) := by
      calc
        ENNReal.ofReal (1 / 2 : ℝ) * stdGaussian E {x : E | f x < m - t}
          ≤ stdGaussian E {x : E | m ≤ f x} * stdGaussian E {x : E | f x < m - t} := by gcongr
        _ ≤ ENNReal.ofReal (Real.exp (-((t / (L : ℝ)) ^ 2) / 4)) := henl
        _ = ENNReal.ofReal (Real.exp (-(t ^ 2) / (4 * (L : ℝ) ^ 2))) := by
            congr 2; rw [div_pow]; ring
    calc
      stdGaussian E {x : E | f x < m - t}
        = ENNReal.ofReal 2 *
          (ENNReal.ofReal (1 / 2 : ℝ) * stdGaussian E {x : E | f x < m - t}) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num),
            show (2 : ℝ) * (1 / 2) = 1 by norm_num,
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (Real.exp (-(t ^ 2) / (4 * (L : ℝ) ^ 2))) := by gcongr
      _ = ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (4 * (L : ℝ) ^ 2))) :=
          (ENNReal.ofReal_mul (by norm_num)).symm
  have hsub : {x : E | t < |f x - m|} ⊆ {x : E | m + t < f x} ∪ {x : E | f x < m - t} := by
    intro x hx
    rw [mem_ofPred_eq, lt_abs] at hx
    rcases hx with h1 | h2
    · exact Or.inl (show m + t < f x by linarith)
    · exact Or.inr (show f x < m - t by linarith)
  calc
    stdGaussian E {x : E | t < |f x - m|}
      ≤ stdGaussian E ({x : E | m + t < f x} ∪ {x : E | f x < m - t}) := measure_mono hsub
    _ ≤ stdGaussian E {x : E | m + t < f x} + stdGaussian E {x : E | f x < m - t} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (4 * (L : ℝ) ^ 2))) +
          ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (4 * (L : ℝ) ^ 2))) := add_le_add hupper hlower
    _ = ENNReal.ofReal (4 * Real.exp (-(t ^ 2) / (4 * (L : ℝ) ^ 2))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end GaussianConcentration

/-! ### 4. Spherical Concentration of Measure (Ball, Lecture 8) -/

section SphericalConcentration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Spherical Enlargement Inequality (Two-Set Form, Ball Lecture 8):**
in dimension `d = finrank ℝ E ≥ 1`, if measurable subsets `A, B ⊆ sphere (0 : E) 1` satisfy
`ε ≤ ‖u.1 - v.1‖` for all `u ∈ A, v ∈ B` (`ε ≥ 0`), then
$$\sigma(A)\,\sigma(B) \le 144\,e^{-d \varepsilon^2 / 8}.$$ -/
theorem spherical_enlargement_two_sets [Nontrivial E]
    {A B : Set (sphere (0 : E) 1)} (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    {ε : ℝ} (hε : 0 ≤ ε) (hdist : ∀ u ∈ A, ∀ v ∈ B, ε ≤ ‖u.1 - v.1‖) :
    sphereProb (volume : Measure E) A * sphereProb (volume : Measure E) B ≤
      ENNReal.ofReal (144 * Real.exp (-(Module.finrank ℝ E : ℝ) * ε ^ 2 / 8)) := by
  set d : ℝ := (Module.finrank ℝ E : ℝ)
  have hd_pos : 0 < d := Nat.cast_pos.mpr Module.finrank_pos
  set r₀ : ℝ := Real.sqrt (d / 2)
  have hr₀_pos : 0 < r₀ := Real.sqrt_pos.mpr (by linarith)
  let R : Set (Ioi (0 : ℝ)) := Ici ⟨r₀, hr₀_pos⟩
  have hRm : MeasurableSet R := measurableSet_Ici
  have hemb : MeasurableEmbedding (Subtype.val : ({0}ᶜ : Set E) → E) :=
    MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : E)).compl
  let CA : Set E := Subtype.val '' ((homeomorphUnitSphereProd E) ⁻¹' (A ×ˢ R))
  let CB : Set E := Subtype.val '' ((homeomorphUnitSphereProd E) ⁻¹' (B ×ˢ R))
  have hCAm : MeasurableSet CA :=
    hemb.measurableSet_image.mpr
      ((hAm.prod hRm).preimage (homeomorphUnitSphereProd E).continuous.measurable)
  have hCBm : MeasurableSet CB :=
    hemb.measurableSet_image.mpr
      ((hBm.prod hRm).preimage (homeomorphUnitSphereProd E).continuous.measurable)
  -- Distance between points in the truncated radial cones `CA` and `CB` is at least `r₀ * ε`.
  have hsep : ∀ x ∈ CA, ∀ y ∈ CB, r₀ * ε ≤ ‖x - y‖ := by
    rintro x ⟨⟨x', hx'0⟩, ⟨hxA, hxR⟩, rfl⟩ y ⟨⟨y', hy'0⟩, ⟨hyB, hyR⟩, rfl⟩
    set u := (homeomorphUnitSphereProd E ⟨x', hx'0⟩).1
    set v := (homeomorphUnitSphereProd E ⟨y', hy'0⟩).1
    set r : ℝ := ((homeomorphUnitSphereProd E ⟨x', hx'0⟩).2 : ℝ)
    set s : ℝ := ((homeomorphUnitSphereProd E ⟨y', hy'0⟩).2 : ℝ)
    have hx_eq : x' = r • u.1 := by
      simp only [u, r, homeomorphUnitSphereProd_apply_fst_coe,
        homeomorphUnitSphereProd_apply_snd_coe]
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx'0), one_smul]
    have hy_eq : y' = s • v.1 := by
      simp only [v, s, homeomorphUnitSphereProd_apply_fst_coe,
        homeomorphUnitSphereProd_apply_snd_coe]
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy'0), one_smul]
    have hr_ge : r₀ ≤ r := hxR
    have hs_ge : r₀ ≤ s := hyR
    have hu1 : ‖u.1‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
    have hv1 : ‖v.1‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
    -- Euclidean identity: `‖r • u - s • v‖² = (r - s)² + r * s * ‖u - v‖²`.
    have hnorm_sq : ‖x' - y'‖ ^ 2 = (r - s) ^ 2 + r * s * ‖u.1 - v.1‖ ^ 2 := by
      rw [hx_eq, hy_eq, norm_sub_sq_real, norm_sub_sq_real, norm_smul, norm_smul,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < r),
        abs_of_pos (by linarith : 0 < s), hu1, hv1, inner_smul_left, inner_smul_right,
        RCLike.conj_to_real]
      ring
    have huv_sq : ε ^ 2 ≤ ‖u.1 - v.1‖ ^ 2 := pow_le_pow_left₀ hε (hdist u hxA v hyB) 2
    have hsq_ge : (r₀ * ε) ^ 2 ≤ ‖x' - y'‖ ^ 2 := by
      rw [hnorm_sq, mul_pow]
      have hrs : r₀ ^ 2 ≤ r * s := by nlinarith
      have h1 : r₀ ^ 2 * ε ^ 2 ≤ r * s * ‖u.1 - v.1‖ ^ 2 :=
        mul_le_mul hrs huv_sq (sq_nonneg ε) (by nlinarith)
      nlinarith [sq_nonneg (r - s)]
    exact le_of_sq_le_sq hsq_ge (norm_nonneg _)
  have henl := gaussian_enlargement_two_sets hCAm hCBm (mul_nonneg hr₀_pos.le hε) hsep
  rw [stdGaussian_polar_cone hAm hRm, stdGaussian_polar_cone hBm hRm] at henl
  have hp_ge : ENNReal.ofReal (1 / 12 : ℝ) ≤ stdGaussianRadial E R := by
    rw [stdGaussianRadial_Ici hr₀_pos]
    exact stdGaussian_norm_ge_sqrt_half_dim
  have hp2_ge : ENNReal.ofReal (1 / 144 : ℝ) ≤ stdGaussianRadial E R * stdGaussianRadial E R := by
    calc
      ENNReal.ofReal (1 / 144 : ℝ) = ENNReal.ofReal (1 / 12 : ℝ) * ENNReal.ofReal (1 / 12 : ℝ) := by
        rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num
      _ ≤ stdGaussianRadial E R * stdGaussianRadial E R := mul_le_mul' hp_ge hp_ge
  have hmul : ENNReal.ofReal (1 / 144 : ℝ) *
      (sphereProb (volume : Measure E) A * sphereProb (volume : Measure E) B) ≤
      ENNReal.ofReal (Real.exp (-d * ε ^ 2 / 8)) := by
    have hrearr : (sphereProb (volume : Measure E) A * stdGaussianRadial E R) *
        (sphereProb (volume : Measure E) B * stdGaussianRadial E R) =
        (stdGaussianRadial E R * stdGaussianRadial E R) *
          (sphereProb (volume : Measure E) A * sphereProb (volume : Measure E) B) := by ring
    have hexp_eq : -((r₀ * ε) ^ 2) / 4 = -d * ε ^ 2 / 8 := by
      rw [mul_pow, Real.sq_sqrt (by linarith)]; ring
    rw [hrearr, hexp_eq] at henl
    calc
      ENNReal.ofReal (1 / 144 : ℝ) *
          (sphereProb (volume : Measure E) A * sphereProb (volume : Measure E) B)
        ≤ (stdGaussianRadial E R * stdGaussianRadial E R) *
            (sphereProb (volume : Measure E) A * sphereProb (volume : Measure E) B) := by gcongr
      _ ≤ ENNReal.ofReal (Real.exp (-d * ε ^ 2 / 8)) := henl
  calc
    sphereProb (volume : Measure E) A * sphereProb (volume : Measure E) B
      = ENNReal.ofReal 144 * (ENNReal.ofReal (1 / 144 : ℝ) *
          (sphereProb (volume : Measure E) A * sphereProb (volume : Measure E) B)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num),
          show (144 : ℝ) * (1 / 144) = 1 by norm_num, ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal 144 * ENNReal.ofReal (Real.exp (-d * ε ^ 2 / 8)) := by gcongr
    _ = ENNReal.ofReal (144 * Real.exp (-d * ε ^ 2 / 8)) :=
        (ENNReal.ofReal_mul (by norm_num)).symm

/-- **Spherical Enlargement Inequality (Metric Thickening Form):**
for any measurable `A ⊆ sphere (0 : E) 1` and `ε > 0`,
$$\sigma(A)\,\sigma\bigl((\mathrm{thickening}\;\varepsilon\;A)^c\bigr)
  \le 144\,e^{-d \varepsilon^2 / 8}.$$ -/
theorem spherical_enlargement_thickening [Nontrivial E]
    {A : Set (sphere (0 : E) 1)} (hAm : MeasurableSet A) {ε : ℝ} (hε : 0 < ε) :
    sphereProb (volume : Measure E) A *
      sphereProb (volume : Measure E) (Metric.thickening ε A)ᶜ ≤
      ENNReal.ofReal (144 * Real.exp (-(Module.finrank ℝ E : ℝ) * ε ^ 2 / 8)) := by
  refine spherical_enlargement_two_sets hAm Metric.isOpen_thickening.measurableSet.compl hε.le
    fun u hu v hv => ?_
  by_contra hlt
  push Not at hlt
  have hmem : v ∈ Metric.thickening ε A := by
    rw [Metric.mem_thickening_iff]
    exact ⟨u, hu, by simpa [Subtype.dist_eq, dist_eq_norm, norm_sub_rev] using hlt⟩
  exact hv hmem

/-- **Spherical Lipschitz Concentration around a Median (Ball, Lecture 8):**
if `f : sphere (0 : E) 1 → ℝ` is `L`-Lipschitz (`L > 0`) and `m : ℝ` is a median of `f` under
`sphereProb volume`, then for every `t ≥ 0`:
$$\sigma\bigl\{u : |f(u) - m| > t\bigr\} \le 576\,e^{-d t^2 / (8 L^2)}.$$ -/
theorem spherical_lipschitz_concentration_median [Nontrivial E]
    {L : ℝ≥0} (hL : 0 < L) {f : sphere (0 : E) 1 → ℝ} (hf : LipschitzWith L f) {m : ℝ}
    (hm_le : ENNReal.ofReal (1 / 2 : ℝ) ≤ sphereProb (volume : Measure E) {u | f u ≤ m})
    (hm_ge : ENNReal.ofReal (1 / 2 : ℝ) ≤ sphereProb (volume : Measure E) {u | m ≤ f u})
    {t : ℝ} (ht : 0 ≤ t) :
    sphereProb (volume : Measure E) {u | t < |f u - m|} ≤
      ENNReal.ofReal (576 * Real.exp (-(Module.finrank ℝ E : ℝ) * t ^ 2 / (8 * (L : ℝ) ^ 2))) := by
  have hL_pos : (0 : ℝ) < L := hL
  set d : ℝ := (Module.finrank ℝ E : ℝ)
  have hupper : sphereProb (volume : Measure E) {u | m + t < f u} ≤
      ENNReal.ofReal (288 * Real.exp (-d * t ^ 2 / (8 * (L : ℝ) ^ 2))) := by
    have hA_m : MeasurableSet {u : sphere (0 : E) 1 | f u ≤ m} :=
      (isClosed_le hf.continuous continuous_const).measurableSet
    have hB_m : MeasurableSet {u : sphere (0 : E) 1 | m + t < f u} :=
      (isOpen_lt continuous_const hf.continuous).measurableSet
    have hsep : ∀ u ∈ {u : sphere (0 : E) 1 | f u ≤ m}, ∀ v ∈ {u : sphere (0 : E) 1 | m + t < f u},
        t / (L : ℝ) ≤ ‖u.1 - v.1‖ := fun u hu v hv => by
      have hlip : |f v - f u| ≤ (L : ℝ) * ‖u.1 - v.1‖ := by
        have h := hf.dist_le_mul v u
        rw [Real.dist_eq, Subtype.dist_eq, dist_eq_norm, norm_sub_rev] at h
        exact h
      have hgt : t < f v - f u := by linarith [mem_ofPred_eq.mp hu, mem_ofPred_eq.mp hv]
      exact (div_le_iff₀ hL_pos).mpr (by linarith [(le_abs_self (f v - f u)).trans hlip])
    have henl := spherical_enlargement_two_sets hA_m hB_m (div_nonneg ht hL_pos.le) hsep
    have hmul : ENNReal.ofReal (1 / 2 : ℝ) * sphereProb (volume : Measure E) {u | m + t < f u} ≤
        ENNReal.ofReal (144 * Real.exp (-d * t ^ 2 / (8 * (L : ℝ) ^ 2))) := by
      calc
        ENNReal.ofReal (1 / 2 : ℝ) * sphereProb (volume : Measure E) {u | m + t < f u}
          ≤ sphereProb (volume : Measure E) {u | f u ≤ m} *
              sphereProb (volume : Measure E) {u | m + t < f u} := by gcongr
        _ ≤ ENNReal.ofReal (144 * Real.exp (-d * (t / (L : ℝ)) ^ 2 / 8)) := henl
        _ = ENNReal.ofReal (144 * Real.exp (-d * t ^ 2 / (8 * (L : ℝ) ^ 2))) := by
            congr 3; rw [div_pow]; ring
    calc
      sphereProb (volume : Measure E) {u | m + t < f u}
        = ENNReal.ofReal 2 * (ENNReal.ofReal (1 / 2 : ℝ) *
            sphereProb (volume : Measure E) {u | m + t < f u}) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num),
            show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal 2 *
            ENNReal.ofReal (144 * Real.exp (-d * t ^ 2 / (8 * (L : ℝ) ^ 2))) := by gcongr
      _ = ENNReal.ofReal (288 * Real.exp (-d * t ^ 2 / (8 * (L : ℝ) ^ 2))) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
  have hlower : sphereProb (volume : Measure E) {u | f u < m - t} ≤
      ENNReal.ofReal (288 * Real.exp (-d * t ^ 2 / (8 * (L : ℝ) ^ 2))) := by
    have hA_m : MeasurableSet {u : sphere (0 : E) 1 | m ≤ f u} :=
      (isClosed_le continuous_const hf.continuous).measurableSet
    have hB_m : MeasurableSet {u : sphere (0 : E) 1 | f u < m - t} :=
      (isOpen_lt hf.continuous continuous_const).measurableSet
    have hsep : ∀ u ∈ {u : sphere (0 : E) 1 | m ≤ f u}, ∀ v ∈ {u : sphere (0 : E) 1 | f u < m - t},
        t / (L : ℝ) ≤ ‖u.1 - v.1‖ := fun u hu v hv => by
      have hlip : |f u - f v| ≤ (L : ℝ) * ‖u.1 - v.1‖ := by
        simpa [Subtype.dist_eq, dist_eq_norm, Real.dist_eq] using hf.dist_le_mul u v
      have hgt : t < f u - f v := by linarith [mem_ofPred_eq.mp hu, mem_ofPred_eq.mp hv]
      exact (div_le_iff₀ hL_pos).mpr (by linarith [(le_abs_self (f u - f v)).trans hlip])
    have henl := spherical_enlargement_two_sets hA_m hB_m (div_nonneg ht hL_pos.le) hsep
    have hmul : ENNReal.ofReal (1 / 2 : ℝ) * sphereProb (volume : Measure E) {u | f u < m - t} ≤
        ENNReal.ofReal (144 * Real.exp (-d * t ^ 2 / (8 * (L : ℝ) ^ 2))) := by
      calc
        ENNReal.ofReal (1 / 2 : ℝ) * sphereProb (volume : Measure E) {u | f u < m - t}
          ≤ sphereProb (volume : Measure E) {u | m ≤ f u} *
              sphereProb (volume : Measure E) {u | f u < m - t} := by gcongr
        _ ≤ ENNReal.ofReal (144 * Real.exp (-d * (t / (L : ℝ)) ^ 2 / 8)) := henl
        _ = ENNReal.ofReal (144 * Real.exp (-d * t ^ 2 / (8 * (L : ℝ) ^ 2))) := by
            congr 3; rw [div_pow]; ring
    calc
      sphereProb (volume : Measure E) {u | f u < m - t}
        = ENNReal.ofReal 2 * (ENNReal.ofReal (1 / 2 : ℝ) *
            sphereProb (volume : Measure E) {u | f u < m - t}) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num),
            show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal 2 *
            ENNReal.ofReal (144 * Real.exp (-d * t ^ 2 / (8 * (L : ℝ) ^ 2))) := by gcongr
      _ = ENNReal.ofReal (288 * Real.exp (-d * t ^ 2 / (8 * (L : ℝ) ^ 2))) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
  have hsub : {u : sphere (0 : E) 1 | t < |f u - m|} ⊆
      {u | m + t < f u} ∪ {u | f u < m - t} := by
    intro u hu
    rw [mem_ofPred_eq, lt_abs] at hu
    rcases hu with h1 | h2
    · exact Or.inl (show m + t < f u by linarith)
    · exact Or.inr (show f u < m - t by linarith)
  calc
    sphereProb (volume : Measure E) {u | t < |f u - m|}
      ≤ sphereProb (volume : Measure E) ({u | m + t < f u} ∪ {u | f u < m - t}) :=
        measure_mono hsub
    _ ≤ sphereProb (volume : Measure E) {u | m + t < f u} +
          sphereProb (volume : Measure E) {u | f u < m - t} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (288 * Real.exp (-d * t ^ 2 / (8 * (L : ℝ) ^ 2))) +
          ENNReal.ofReal (288 * Real.exp (-d * t ^ 2 / (8 * (L : ℝ) ^ 2))) :=
        add_le_add hupper hlower
    _ = ENNReal.ofReal (576 * Real.exp (-d * t ^ 2 / (8 * (L : ℝ) ^ 2))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end SphericalConcentration

/-! ### 5. Johnson–Lindenstrauss Lemma (Ball, Lecture 8) -/

section JohnsonLindenstrauss

/-- 1D $\chi^2$ MGF: for every `a < 1 / 2`,
`∫ t, exp (a * t²) ∂(gaussianReal 0 1) = (1 - 2 * a) ^ (-1 / 2)`. -/
theorem integral_exp_mul_sq_gaussianReal {a : ℝ} (ha : a < 1 / 2) :
    ∫ t : ℝ, Real.exp (a * t ^ 2) ∂(gaussianReal 0 1) = (1 - 2 * a) ^ (-(1 : ℝ) / 2) := by
  have h12 : 0 < 1 - 2 * a := by linarith
  set c : ℝ := Real.sqrt (1 - 2 * a)
  have hc_pos : 0 < c := Real.sqrt_pos.mpr h12
  have hc_sq : c ^ 2 = 1 - 2 * a := Real.sq_sqrt h12.le
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have hfun : (fun t : ℝ => gaussianPDFReal 0 1 t • Real.exp (a * t ^ 2)) =
      fun t : ℝ => gaussianPDFReal 0 1 (c * t) := by
    ext t
    rw [smul_eq_mul, gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    rw [mul_pow, hc_sq]
    ring
  rw [hfun, Measure.integral_comp_mul_left (gaussianPDFReal 0 1) c,
    integral_gaussianPDFReal_eq_one 0 one_ne_zero, smul_eq_mul, mul_one,
    abs_inv, abs_of_pos hc_pos]
  dsimp only [c]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg h12.le]
  congr 1; ring

private lemma integrable_exp_mul_sq_gaussianReal {a : ℝ} (ha : a < 1 / 2) :
    Integrable (fun t : ℝ => Real.exp (a * t ^ 2)) (gaussianReal 0 1) := by
  have h12 : 0 < 1 - 2 * a := by linarith
  set c : ℝ := Real.sqrt (1 - 2 * a)
  have hc_pos : 0 < c := Real.sqrt_pos.mpr h12
  have hc_sq : c ^ 2 = 1 - 2 * a := Real.sq_sqrt h12.le
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero]
  have h1 := integrable_withDensity_iff_integrable_smul₀' (μ := (volume : Measure ℝ))
    (f := gaussianPDF 0 1) (measurable_gaussianPDF 0 1).aemeasurable
    (ae_of_all _ fun _ => gaussianPDF_lt_top) (g := fun t : ℝ => Real.exp (a * t ^ 2))
  rw [h1]
  refine ((integrable_gaussianPDFReal 0 1).comp_mul_left' hc_pos.ne').congr (ae_of_all _ fun t =>
    ?_)
  dsimp only
  rw [toReal_gaussianPDF, smul_eq_mul, gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  rw [mul_pow, hc_sq]
  ring

private lemma log_one_add_sub_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Real.log (1 + ε) - ε ≤ -(ε ^ 2) / 4 := by
  let g : ℝ → ℝ := fun x => Real.log (1 + x) - x + x ^ 2 / 4
  have hderiv : ∀ x : ℝ, 0 < 1 + x → HasDerivAt g (1 / (1 + x) - 1 + x / 2) x := fun x hpos => by
    have h1 : HasDerivAt (fun t => Real.log (1 + t)) (1 / (1 + x)) x := by
      simpa using ((hasDerivAt_id x).const_add 1).log hpos.ne'
    have h2 : HasDerivAt (fun t => t ^ 2 / 4) (x / 2) x := by
      convert (hasDerivAt_pow 2 x).div_const 4 using 1; ring
    exact (h1.sub (hasDerivAt_id x)).add h2
  have hanti : AntitoneOn g (Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · refine ContinuousOn.add (ContinuousOn.sub ?_ continuousOn_id)
        (continuousOn_pow 2 |>.div_const 4)
      exact (continuousOn_const.add continuousOn_id).log fun x hx => by
        change 1 + x ≠ 0; linarith [hx.1]
    · intro x hx
      rw [interior_Icc] at hx
      exact (hderiv x (by linarith [hx.1])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hpos : (0 : ℝ) < 1 + x := by linarith [hx.1]
      rw [(hderiv x hpos).deriv]
      have hnum : 1 / (1 + x) - 1 + x / 2 = x * (x - 1) / (2 * (1 + x)) := by
        field_simp [hpos.ne']; ring
      rw [hnum]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hx.1.le (by linarith [hx.2]))
        (by positivity)
  have hle : g ε ≤ g 0 := hanti (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc 0 1) ⟨hε0, hε1⟩ hε0
  simp only [g, add_zero, Real.log_one, sub_zero, zero_pow two_ne_zero, zero_div] at hle
  linarith

private lemma log_one_sub_add_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    Real.log (1 - ε) + ε ≤ -(ε ^ 2) / 4 := by
  let g : ℝ → ℝ := fun x => Real.log (1 - x) + x + x ^ 2 / 2
  have hderiv : ∀ x : ℝ, 0 < 1 - x → HasDerivAt g (-1 / (1 - x) + 1 + x) x := fun x hpos => by
    have h1 : HasDerivAt (fun t => Real.log (1 - t)) (-1 / (1 - x)) x := by
      simpa using ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).log hpos.ne'
    have h2 : HasDerivAt (fun t => t ^ 2 / 2) x x := by
      convert (hasDerivAt_pow 2 x).div_const 2 using 1; ring
    exact (h1.add (hasDerivAt_id x)).add h2
  have hanti : AntitoneOn g (Ico 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ico 0 1)
    · refine ContinuousOn.add (ContinuousOn.add ?_ continuousOn_id)
        (continuousOn_pow 2 |>.div_const 2)
      exact (continuousOn_const.sub continuousOn_id).log fun x hx => by
        change 1 - x ≠ 0; linarith [hx.2]
    · intro x hx
      rw [interior_Ico] at hx
      exact (hderiv x (by linarith [hx.2])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      have hpos : (0 : ℝ) < 1 - x := by linarith [hx.2]
      rw [(hderiv x hpos).deriv]
      have hnum : -1 / (1 - x) + 1 + x = -(x ^ 2) / (1 - x) := by
        field_simp [hpos.ne']; ring
      rw [hnum]
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hpos.le
  have hle : g ε ≤ g 0 := hanti (⟨le_rfl, zero_lt_one⟩ : (0 : ℝ) ∈ Ico 0 1) ⟨hε0, hε1⟩ hε0
  simp only [g, sub_zero, Real.log_one, add_zero, zero_pow two_ne_zero, zero_div] at hle
  nlinarith [sq_nonneg ε]

/-- **$\chi^2_k$ Upper-Tail Bound** for `k` i.i.d. standard Gaussians:
for `0 < ε < 1`, `P(∑_{m : Fin k} g_m² > (1 + ε) * k) ≤ exp (-k * ε² / 8)`. -/
theorem chi_sq_upper_tail (k : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Measure.pi (fun _ : Fin k => gaussianReal 0 1)
      {v : Fin k → ℝ | (1 + ε) * (k : ℝ) < ∑ m : Fin k, v m ^ 2} ≤
      ENNReal.ofReal (Real.exp (-(k : ℝ) * ε ^ 2 / 8)) := by
  let μ := Measure.pi (fun _ : Fin k => gaussianReal 0 1)
  set a : ℝ := ε / (2 * (1 + ε))
  have ha_pos : 0 < a := by positivity
  have ha_lt : a < 1 / 2 := by
    dsimp only [a]; rw [div_lt_div_iff₀ (by positivity) two_pos]; linarith
  have h12a : 1 - 2 * a = (1 + ε)⁻¹ := by
    dsimp only [a]; field_simp [show (1 : ℝ) + ε ≠ 0 by linarith]; ring
  have hsub : {v : Fin k → ℝ | (1 + ε) * (k : ℝ) < ∑ m : Fin k, v m ^ 2} ⊆
      {v : Fin k → ℝ | ENNReal.ofReal (Real.exp (a * ((1 + ε) * (k : ℝ)))) ≤
        ENNReal.ofReal (Real.exp (a * ∑ m : Fin k, v m ^ 2))} := fun v hv =>
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hv.le ha_pos.le))
  have hmeas_exp : Measurable (fun v : Fin k → ℝ =>
      ENNReal.ofReal (Real.exp (a * ∑ m : Fin k, v m ^ 2))) :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul
        (continuous_finsetSum Finset.univ fun m _ => (continuous_apply m).pow 2))).measurable
  have hmarkov : ENNReal.ofReal (Real.exp (a * ((1 + ε) * (k : ℝ)))) *
      μ {v : Fin k → ℝ | (1 + ε) * (k : ℝ) < ∑ m : Fin k, v m ^ 2} ≤
      ∫⁻ v : Fin k → ℝ, ENNReal.ofReal (Real.exp (a * ∑ m : Fin k, v m ^ 2)) ∂μ := by
    calc
      ENNReal.ofReal (Real.exp (a * ((1 + ε) * (k : ℝ)))) *
          μ {v : Fin k → ℝ | (1 + ε) * (k : ℝ) < ∑ m : Fin k, v m ^ 2}
        ≤ ENNReal.ofReal (Real.exp (a * ((1 + ε) * (k : ℝ)))) *
            μ {v : Fin k → ℝ | ENNReal.ofReal (Real.exp (a * ((1 + ε) * (k : ℝ)))) ≤
              ENNReal.ofReal (Real.exp (a * ∑ m : Fin k, v m ^ 2))} := by gcongr
      _ ≤ ∫⁻ v : Fin k → ℝ, ENNReal.ofReal (Real.exp (a * ∑ m : Fin k, v m ^ 2)) ∂μ :=
          mul_meas_ge_le_lintegral₀ hmeas_exp.aemeasurable _
  have hlint : ∫⁻ v : Fin k → ℝ, ENNReal.ofReal (Real.exp (a * ∑ m : Fin k, v m ^ 2)) ∂μ =
      ENNReal.ofReal (((1 + ε) ^ ((1 : ℝ) / 2)) ^ k) := by
    have hint_prod : Integrable (fun v : Fin k → ℝ => ∏ m : Fin k, Real.exp (a * v m ^ 2)) μ := by
      have h1 := integrable_exp_mul_sq_gaussianReal ha_lt
      have hfin : ∫⁻ v : Fin k → ℝ,
        ENNReal.ofReal (∏ m : Fin k, Real.exp (a * v m ^ 2)) ∂μ < ⊤ := by
        have hfact : ∀ v : Fin k → ℝ,
            ENNReal.ofReal (∏ m : Fin k, Real.exp (a * v m ^ 2)) =
              ∏ m : Fin k, ENNReal.ofReal (Real.exp (a * v m ^ 2)) := fun v =>
          ENNReal.ofReal_prod_of_nonneg fun _ _ => (Real.exp_pos _).le
        simp_rw [hfact]
        have hstep : ∀ (n : ℕ),
            ∫⁻ v : Fin n → ℝ, ∏ m : Fin n, ENNReal.ofReal (Real.exp (a * v m ^ 2))
              ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
              (∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (a * t ^ 2)) ∂gaussianReal 0 1) ^ n := by
          intro n
          induction n with
          | zero => simp
          | succ n ih =>
              have hmp := MeasureTheory.measurePreserving_piFinSuccAbove
                (fun _ : Fin (n + 1) => gaussianReal 0 1) (0 : Fin (n + 1))
              have hcomp := hmp.lintegral_comp_emb
                (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).measurableEmbedding
                (fun p : ℝ × (Fin n → ℝ) =>
                  ENNReal.ofReal (Real.exp (a * p.1 ^ 2)) *
                    ∏ j : Fin n, ENNReal.ofReal (Real.exp (a * p.2 j ^ 2)))
              have hfun_eq : (fun v : Fin (n + 1) → ℝ =>
                  ENNReal.ofReal
                    (Real.exp (a * (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 v).1 ^ 2)) *
                    ∏ j : Fin n, ENNReal.ofReal
                      (Real.exp
                        (a * (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 v).2 j ^ 2))) =
                  fun v => ∏ m : Fin (n + 1), ENNReal.ofReal (Real.exp (a * v m ^ 2)) := by
                ext v; rw [Fin.prod_univ_succ];
                simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.tail]
              rw [hfun_eq] at hcomp
              rw [hcomp, lintegral_prod]
              · have hm_prod : Measurable (fun y : Fin n → ℝ =>
                    ∏ j : Fin n, ENNReal.ofReal (Real.exp (a * y j ^ 2))) :=
                  Finset.measurable_fun_prod Finset.univ fun j _ =>
                    ENNReal.measurable_ofReal.comp
                      (Real.continuous_exp.comp
                        (continuous_const.mul ((continuous_apply j).pow 2))).measurable
                have hm1 : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (a * x ^ 2))) :=
                  ENNReal.measurable_ofReal.comp
                    (Real.continuous_exp.comp (continuous_const.mul (continuous_pow 2))).measurable
                simp_rw [lintegral_const_mul _ hm_prod]
                rw [lintegral_mul_const _ hm1, ih, pow_succ']
              · exact ((ENNReal.measurable_ofReal.comp
                  (Real.continuous_exp.comp
                    (continuous_const.mul (continuous_fst.pow 2))).measurable).mul
                  (Finset.measurable_fun_prod Finset.univ fun j _ =>
                    ENNReal.measurable_ofReal.comp
                      (Real.continuous_exp.comp
                        (continuous_const.mul
                          (((continuous_apply j).comp continuous_snd).pow 2))).measurable
                  )).aemeasurable
        rw [hstep k,
          ← ofReal_integral_eq_lintegral_ofReal h1 (ae_of_all _ fun _ => (Real.exp_pos _).le)]
        exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
      exact ⟨(Finset.measurable_fun_prod Finset.univ fun m _ =>
        (Real.continuous_exp.comp
          (continuous_const.mul ((continuous_apply m).pow 2))).measurable).aestronglyMeasurable,
        by simpa [HasFiniteIntegral,
          Real.eNorm_eq_ofReal (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)] using hfin⟩
    simp_rw [Finset.mul_sum, Real.exp_sum]
    rw [← ofReal_integral_eq_lintegral_ofReal hint_prod
      (ae_of_all _ fun _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)]
    dsimp only [μ]
    rw [integral_fintype_prod_eq_pow (f := fun t : ℝ => Real.exp (a * t ^ 2)), Fintype.card_fin,
      integral_exp_mul_sq_gaussianReal ha_lt, h12a]
    congr 2
    rw [Real.inv_rpow (by linarith : (0 : ℝ) ≤ 1 + ε),
      ← Real.rpow_neg (by linarith : (0 : ℝ) ≤ 1 + ε)]
    ring_nf
  rw [hlint] at hmarkov
  have hpos : ENNReal.ofReal (Real.exp (a * ((1 + ε) * (k : ℝ)))) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hfin : ENNReal.ofReal (Real.exp (a * ((1 + ε) * (k : ℝ)))) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc
    μ {v : Fin k → ℝ | (1 + ε) * (k : ℝ) < ∑ m : Fin k, v m ^ 2}
      = (ENNReal.ofReal (Real.exp (a * ((1 + ε) * (k : ℝ)))))⁻¹ *
          (ENNReal.ofReal (Real.exp (a * ((1 + ε) * (k : ℝ)))) *
            μ {v : Fin k → ℝ | (1 + ε) * (k : ℝ) < ∑ m : Fin k, v m ^ 2}) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hpos hfin, one_mul]
    _ ≤ (ENNReal.ofReal (Real.exp (a * ((1 + ε) * (k : ℝ)))))⁻¹ *
          ENNReal.ofReal (((1 + ε) ^ ((1 : ℝ) / 2)) ^ k) := by gcongr
    _ = ENNReal.ofReal (Real.exp (-(a * ((1 + ε) * (k : ℝ)))) *
          ((1 + ε) ^ ((1 : ℝ) / 2)) ^ k) := by
        rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ ≤ ENNReal.ofReal (Real.exp (-(k : ℝ) * ε ^ 2 / 8)) := by
        apply ENNReal.ofReal_le_ofReal
        have h1ε : 0 < 1 + ε := by linarith
        have hpow_exp : ((1 + ε) ^ ((1 : ℝ) / 2)) ^ k =
            Real.exp (((k : ℝ) / 2) * Real.log (1 + ε)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul h1ε.le, Real.rpow_def_of_pos h1ε]
          congr 1; ring
        have ha_simp : a * ((1 + ε) * (k : ℝ)) = ((k : ℝ) / 2) * ε := by
          dsimp only [a]; field_simp [h1ε.ne']
        rw [hpow_exp, ha_simp, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hlog := log_one_add_sub_le hε0.le hε1.le
        have hk_nn : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
        nlinarith

/-- **$\chi^2_k$ Lower-Tail Bound** for `k` i.i.d. standard Gaussians:
for `0 < ε < 1`, `P(∑_{m : Fin k} g_m² < (1 - ε) * k) ≤ exp (-k * ε² / 8)`. -/
theorem chi_sq_lower_tail (k : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Measure.pi (fun _ : Fin k => gaussianReal 0 1)
      {v : Fin k → ℝ | ∑ m : Fin k, v m ^ 2 < (1 - ε) * (k : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(k : ℝ) * ε ^ 2 / 8)) := by
  let μ := Measure.pi (fun _ : Fin k => gaussianReal 0 1)
  set a : ℝ := -ε / (2 * (1 - ε))
  have h1ε : 0 < 1 - ε := by linarith
  have ha_neg : a < 0 := div_neg_of_neg_of_pos (by linarith) (by positivity)
  have ha_lt : a < 1 / 2 := ha_neg.trans (by norm_num)
  have h12a : 1 - 2 * a = (1 - ε)⁻¹ := by
    dsimp only [a]; field_simp [h1ε.ne']; ring
  have hsub : {v : Fin k → ℝ | ∑ m : Fin k, v m ^ 2 < (1 - ε) * (k : ℝ)} ⊆
      {v : Fin k → ℝ | ENNReal.ofReal (Real.exp (a * ((1 - ε) * (k : ℝ)))) ≤
        ENNReal.ofReal (Real.exp (a * ∑ m : Fin k, v m ^ 2))} := fun v hv =>
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hv.le ha_neg.le))
  have hmeas_exp : Measurable (fun v : Fin k → ℝ =>
      ENNReal.ofReal (Real.exp (a * ∑ m : Fin k, v m ^ 2))) :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul
        (continuous_finsetSum Finset.univ fun m _ => (continuous_apply m).pow 2))).measurable
  have hmarkov : ENNReal.ofReal (Real.exp (a * ((1 - ε) * (k : ℝ)))) *
      μ {v : Fin k → ℝ | ∑ m : Fin k, v m ^ 2 < (1 - ε) * (k : ℝ)} ≤
      ∫⁻ v : Fin k → ℝ, ENNReal.ofReal (Real.exp (a * ∑ m : Fin k, v m ^ 2)) ∂μ := by
    calc
      ENNReal.ofReal (Real.exp (a * ((1 - ε) * (k : ℝ)))) *
          μ {v : Fin k → ℝ | ∑ m : Fin k, v m ^ 2 < (1 - ε) * (k : ℝ)}
        ≤ ENNReal.ofReal (Real.exp (a * ((1 - ε) * (k : ℝ)))) *
            μ {v : Fin k → ℝ | ENNReal.ofReal (Real.exp (a * ((1 - ε) * (k : ℝ)))) ≤
              ENNReal.ofReal (Real.exp (a * ∑ m : Fin k, v m ^ 2))} := by gcongr
      _ ≤ ∫⁻ v : Fin k → ℝ, ENNReal.ofReal (Real.exp (a * ∑ m : Fin k, v m ^ 2)) ∂μ :=
          mul_meas_ge_le_lintegral₀ hmeas_exp.aemeasurable _
  have hlint : ∫⁻ v : Fin k → ℝ, ENNReal.ofReal (Real.exp (a * ∑ m : Fin k, v m ^ 2)) ∂μ =
      ENNReal.ofReal (((1 - ε) ^ ((1 : ℝ) / 2)) ^ k) := by
    have hint_prod : Integrable (fun v : Fin k → ℝ => ∏ m : Fin k, Real.exp (a * v m ^ 2)) μ := by
      have h1 := integrable_exp_mul_sq_gaussianReal ha_lt
      have hstep : ∀ (n : ℕ),
          ∫⁻ v : Fin n → ℝ, ∏ m : Fin n, ENNReal.ofReal (Real.exp (a * v m ^ 2))
            ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
            (∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (a * t ^ 2)) ∂gaussianReal 0 1) ^ n := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
            have hmp := MeasureTheory.measurePreserving_piFinSuccAbove
              (fun _ : Fin (n + 1) => gaussianReal 0 1) (0 : Fin (n + 1))
            have hcomp := hmp.lintegral_comp_emb
              (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).measurableEmbedding
              (fun p : ℝ × (Fin n → ℝ) =>
                ENNReal.ofReal (Real.exp (a * p.1 ^ 2)) *
                  ∏ j : Fin n, ENNReal.ofReal (Real.exp (a * p.2 j ^ 2)))
            have hfun_eq : (fun v : Fin (n + 1) → ℝ =>
                ENNReal.ofReal
                  (Real.exp (a * (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 v).1 ^ 2)) *
                  ∏ j : Fin n, ENNReal.ofReal
                    (Real.exp
                      (a * (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 v).2 j ^ 2))) =
                fun v => ∏ m : Fin (n + 1), ENNReal.ofReal (Real.exp (a * v m ^ 2)) := by
              ext v; rw [Fin.prod_univ_succ]; simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.tail]
            rw [hfun_eq] at hcomp
            rw [hcomp, lintegral_prod]
            · have hm_prod : Measurable (fun y : Fin n → ℝ =>
                  ∏ j : Fin n, ENNReal.ofReal (Real.exp (a * y j ^ 2))) :=
                Finset.measurable_fun_prod Finset.univ fun j _ =>
                  ENNReal.measurable_ofReal.comp
                    (Real.continuous_exp.comp
                      (continuous_const.mul ((continuous_apply j).pow 2))).measurable
              have hm1 : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (a * x ^ 2))) :=
                ENNReal.measurable_ofReal.comp
                  (Real.continuous_exp.comp (continuous_const.mul (continuous_pow 2))).measurable
              simp_rw [lintegral_const_mul _ hm_prod]
              rw [lintegral_mul_const _ hm1, ih, pow_succ']
            · exact ((ENNReal.measurable_ofReal.comp
                (Real.continuous_exp.comp
                  (continuous_const.mul (continuous_fst.pow 2))).measurable).mul
                (Finset.measurable_fun_prod Finset.univ fun j _ =>
                  ENNReal.measurable_ofReal.comp
                    (Real.continuous_exp.comp
                      (continuous_const.mul
                        (((continuous_apply j).comp continuous_snd).pow 2))).measurable
                )).aemeasurable
      have hfin : ∫⁻ v : Fin k → ℝ,
        ENNReal.ofReal (∏ m : Fin k, Real.exp (a * v m ^ 2)) ∂μ < ⊤ := by
        simp_rw [ENNReal.ofReal_prod_of_nonneg fun _ _ => (Real.exp_pos _).le]
        rw [hstep k,
          ← ofReal_integral_eq_lintegral_ofReal h1 (ae_of_all _ fun _ => (Real.exp_pos _).le)]
        exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
      exact ⟨(Finset.measurable_fun_prod Finset.univ fun m _ =>
        (Real.continuous_exp.comp
          (continuous_const.mul ((continuous_apply m).pow 2))).measurable).aestronglyMeasurable,
        by simpa [HasFiniteIntegral,
          Real.eNorm_eq_ofReal (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)] using hfin⟩
    simp_rw [Finset.mul_sum, Real.exp_sum]
    rw [← ofReal_integral_eq_lintegral_ofReal hint_prod
      (ae_of_all _ fun _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)]
    dsimp only [μ]
    rw [integral_fintype_prod_eq_pow (f := fun t : ℝ => Real.exp (a * t ^ 2)), Fintype.card_fin,
      integral_exp_mul_sq_gaussianReal ha_lt, h12a]
    congr 2
    rw [Real.inv_rpow h1ε.le, ← Real.rpow_neg h1ε.le]
    ring_nf
  rw [hlint] at hmarkov
  have hpos : ENNReal.ofReal (Real.exp (a * ((1 - ε) * (k : ℝ)))) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hfin : ENNReal.ofReal (Real.exp (a * ((1 - ε) * (k : ℝ)))) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc
    μ {v : Fin k → ℝ | ∑ m : Fin k, v m ^ 2 < (1 - ε) * (k : ℝ)}
      = (ENNReal.ofReal (Real.exp (a * ((1 - ε) * (k : ℝ)))))⁻¹ *
          (ENNReal.ofReal (Real.exp (a * ((1 - ε) * (k : ℝ)))) *
            μ {v : Fin k → ℝ | ∑ m : Fin k, v m ^ 2 < (1 - ε) * (k : ℝ)}) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hpos hfin, one_mul]
    _ ≤ (ENNReal.ofReal (Real.exp (a * ((1 - ε) * (k : ℝ)))))⁻¹ *
          ENNReal.ofReal (((1 - ε) ^ ((1 : ℝ) / 2)) ^ k) := by gcongr
    _ = ENNReal.ofReal (Real.exp (-(a * ((1 - ε) * (k : ℝ)))) *
          ((1 - ε) ^ ((1 : ℝ) / 2)) ^ k) := by
        rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ ≤ ENNReal.ofReal (Real.exp (-(k : ℝ) * ε ^ 2 / 8)) := by
        apply ENNReal.ofReal_le_ofReal
        have hpow_exp : ((1 - ε) ^ ((1 : ℝ) / 2)) ^ k =
            Real.exp (((k : ℝ) / 2) * Real.log (1 - ε)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul h1ε.le, Real.rpow_def_of_pos h1ε]
          congr 1; ring
        have ha_simp : -(a * ((1 - ε) * (k : ℝ))) = ((k : ℝ) / 2) * ε := by
          dsimp only [a]; field_simp [h1ε.ne']
        rw [hpow_exp, ha_simp, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hlog := log_one_sub_add_le hε0.le hε1
        have hk_nn : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
        nlinarith

/-- **Johnson–Lindenstrauss Lemma (Ball, Lecture 8):**
for any `N` points `x : Fin N → E` in a finite-dimensional real inner product space `E`, any
`ε ∈ (0, 1)`, and any target dimension `k ≥ 16 * log N / ε²`, there exists a linear map
`L : E →ₗ[ℝ] EuclideanSpace ℝ (Fin k)` preserving all pairwise squared distances up to `1 ± ε`:
$$(1 - \varepsilon)\|x_i - x_j\|^2
  \le \|L(x_i) - L(x_j)\|^2
  \le (1 + \varepsilon)\|x_i - x_j\|^2.$$ -/
theorem johnson_lindenstrauss {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {N k : ℕ} (x : Fin N → E) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hk : (16 : ℝ) * Real.log (N : ℝ) / ε ^ 2 ≤ (k : ℝ)) :
    ∃ L : E →ₗ[ℝ] EuclideanSpace ℝ (Fin k),
      ∀ i j : Fin N,
        (1 - ε) * ‖x i - x j‖ ^ 2 ≤ ‖L (x i) - L (x j)‖ ^ 2 ∧
        ‖L (x i) - L (x j)‖ ^ 2 ≤ (1 + ε) * ‖x i - x j‖ ^ 2 := by
  by_cases hN : N ≤ 1
  · refine ⟨0, fun i j => ?_⟩
    have hij : i = j := Fin.ext (by omega)
    subst hij; simp
  push Not at hN
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hk_rpos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le (by positivity) hk
  have hk_pos : 0 < k := Nat.cast_pos.mp hk_rpos
  -- Install the Borel σ-algebra on `E` locally to use `stdGaussian E`.
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  let μ := Measure.pi (fun _ : Fin k => stdGaussian E)
  -- For each Gaussian matrix `g : Fin k → E`, define the scaled linear projection `L_g`.
  let L_of : (Fin k → E) → (E →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) := fun g =>
    { toFun := fun v => WithLp.toLp 2 fun m : Fin k => (Real.sqrt (k : ℝ))⁻¹ * ⟪g m, v⟫
      map_add' := fun v w => by
        apply WithLp.ofLp_injective 2; ext m
        simp [inner_add_right, mul_add]
      map_smul' := fun c v => by
        apply WithLp.ofLp_injective 2; ext m
        simp [inner_smul_right]; ring }
  have hnorm_L : ∀ (g : Fin k → E) (v : E),
      ‖L_of g v‖ ^ 2 = (k : ℝ)⁻¹ * ∑ m : Fin k, ⟪g m, v⟫ ^ 2 := fun g v => by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [L_of, LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs, sq_abs, mul_pow,
      inv_pow, Real.sq_sqrt hk_rpos.le, ← Finset.mul_sum]
  -- Bad event for an ordered pair `p = (i, j)` with `i < j`.
  let pairs : Finset (Fin N × Fin N) := Finset.univ.filter fun p => p.1 < p.2
  let bad : Fin N × Fin N → Set (Fin k → E) := fun p =>
    {g : Fin k → E |
      ‖L_of g (x p.1 - x p.2)‖ ^ 2 < (1 - ε) * ‖x p.1 - x p.2‖ ^ 2 ∨
      (1 + ε) * ‖x p.1 - x p.2‖ ^ 2 < ‖L_of g (x p.1 - x p.2)‖ ^ 2}
  have hbad_le : ∀ p : Fin N × Fin N,
      μ (bad p) ≤ ENNReal.ofReal (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) := fun p => by
    by_cases h0 : x p.1 - x p.2 = 0
    · have hemp : bad p = ∅ := by
        ext g; simp only [bad, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rw [h0, map_zero, norm_zero]
        simp
      rw [hemp, measure_empty]; exact zero_le
    · set v := x p.1 - x p.2
      have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr h0
      set u : E := ‖v‖⁻¹ • v
      have hu : ‖u‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hv_pos),
          inv_mul_cancel₀ hv_pos.ne']
      have hmp_u : MeasurePreserving (fun g : Fin k → E => fun m : Fin k => ⟪g m, u⟫)
          μ (Measure.pi (fun _ : Fin k => gaussianReal 0 1)) := by
        have h1 : ∀ m : Fin k, MeasurePreserving (fun y : E => ⟪y, u⟫)
            (stdGaussian E) (gaussianReal 0 1) := fun _ => measurePreserving_inner_stdGaussian hu
        refine ⟨(continuous_pi fun m =>
          (continuous_inner.comp ((continuous_apply m).prodMk continuous_const))).measurable, ?_⟩
        rw [Measure.pi_map_pi fun m => (h1 m).measurable.aemeasurable]
        congr 1; funext m; exact (h1 m).map_eq
      -- Rewrite `bad p` as the preimage of the union of lower and upper χ² tails.
      let Slo : Set (Fin k → ℝ) := {w | ∑ m : Fin k, w m ^ 2 < (1 - ε) * (k : ℝ)}
      let Shi : Set (Fin k → ℝ) := {w | (1 + ε) * (k : ℝ) < ∑ m : Fin k, w m ^ 2}
      have hbad_eq : bad p = (fun g : Fin k → E => fun m : Fin k => ⟪g m, u⟫) ⁻¹' (Slo ∪ Shi) := by
        ext g
        have hsum_v : ∑ m : Fin k, ⟪g m, v⟫ ^ 2 = ‖v‖ ^ 2 * ∑ m : Fin k, ⟪g m, u⟫ ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          dsimp only [u]
          rw [inner_smul_right, mul_pow, inv_pow]
          field_simp [hv_pos.ne']
        have hnorm_eq : ‖L_of g (x p.1 - x p.2)‖ ^ 2 =
            ((k : ℝ)⁻¹ * ‖v‖ ^ 2) * ∑ m : Fin k, ⟪g m, u⟫ ^ 2 := by
          change ‖L_of g v‖ ^ 2 = _
          rw [hnorm_L, hsum_v, mul_assoc]
        have hlo_eq : (1 - ε) * ‖x p.1 - x p.2‖ ^ 2 =
            ((k : ℝ)⁻¹ * ‖v‖ ^ 2) * ((1 - ε) * (k : ℝ)) := by
          change (1 - ε) * ‖v‖ ^ 2 = _
          field_simp [hk_rpos.ne']
        have hhi_eq : (1 + ε) * ‖x p.1 - x p.2‖ ^ 2 =
            ((k : ℝ)⁻¹ * ‖v‖ ^ 2) * ((1 + ε) * (k : ℝ)) := by
          change (1 + ε) * ‖v‖ ^ 2 = _
          field_simp [hk_rpos.ne']
        simp only [bad, mem_ofPred_eq, mem_preimage, mem_union, Slo, Shi, hnorm_eq, hlo_eq, hhi_eq]
        have hpos_kv : 0 < (k : ℝ)⁻¹ * ‖v‖ ^ 2 := by positivity
        rw [mul_lt_mul_iff_right₀ hpos_kv, mul_lt_mul_iff_right₀ hpos_kv]
      have hS_meas : MeasurableSet (Slo ∪ Shi) :=
        (isOpen_lt (continuous_finsetSum Finset.univ fun m _ => (continuous_apply m).pow 2)
          continuous_const).measurableSet.union
          (isOpen_lt continuous_const
            (continuous_finsetSum Finset.univ fun m _ => (continuous_apply m).pow 2)).measurableSet
      rw [hbad_eq, hmp_u.measure_preimage hS_meas.nullMeasurableSet]
      calc
        Measure.pi (fun _ : Fin k => gaussianReal 0 1) (Slo ∪ Shi)
          ≤ Measure.pi (fun _ : Fin k => gaussianReal 0 1) Slo +
              Measure.pi (fun _ : Fin k => gaussianReal 0 1) Shi := measure_union_le _ _
        _ ≤ ENNReal.ofReal (Real.exp (-(k : ℝ) * ε ^ 2 / 8)) +
              ENNReal.ofReal (Real.exp (-(k : ℝ) * ε ^ 2 / 8)) :=
            add_le_add (chi_sq_lower_tail k hε0 hε1) (chi_sq_upper_tail k hε0 hε1)
        _ = ENNReal.ofReal (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) := by
            rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, two_mul]
  -- Count ordered pairs `i < j`: `2 * pairs.card = N * (N - 1) < N²`.
  have hcard : 2 * pairs.card ≤ N * (N - 1) := by
    have hdisj : Disjoint pairs (Finset.univ.filter fun p : Fin N × Fin N => p.2 < p.1) := by
      rw [Finset.disjoint_filter]
      intro p _ h1 h2; exact lt_asymm h1 h2
    have hcard_swap : (Finset.univ.filter fun p : Fin N × Fin N => p.2 < p.1).card =
      pairs.card := by
      refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
      · intro p hp; simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢;
        exact hp
      · intro p₁ _ p₂ _ h
        exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      · intro q hq
        refine ⟨(q.2, q.1), ?_, rfl⟩
        simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢; exact hq
    have hsub : pairs ∪ (Finset.univ.filter fun p : Fin N × Fin N => p.2 < p.1) ⊆
        Finset.univ.filter fun p : Fin N × Fin N => p.1 ≠ p.2 := by
      intro p hp
      simp only [Finset.mem_union, pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rcases hp with h | h
      · exact ne_of_lt h
      · exact ne_of_gt h
    have hcard_off : (Finset.univ.filter fun p : Fin N × Fin N => p.1 ≠ p.2).card = N * N - N := by
      have hdiag : (Finset.univ.filter fun p : Fin N × Fin N => p.1 = p.2).card = N := by
        refine Finset.card_bij (fun p _ => p.1) (fun _ _ =>
          Finset.mem_univ _) ?_ ?_ |>.trans (by simp)
        · intro p₁ hp₁ p₂ hp₂ h
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
          exact Prod.ext h (hp₁.symm.trans (h.trans hp₂))
        · intro i _; exact ⟨(i, i), by simp, rfl⟩
      have htot : (Finset.univ.filter fun p : Fin N × Fin N => p.1 = p.2).card +
          (Finset.univ.filter fun p : Fin N × Fin N => p.1 ≠ p.2).card = N * N := by
        rw [← Finset.card_union_of_disjoint]
        · have hun : (Finset.univ.filter fun p : Fin N × Fin N => p.1 = p.2) ∪
              (Finset.univ.filter fun p : Fin N × Fin N => p.1 ≠ p.2) = Finset.univ := by
            ext p; simp [em]
          rw [hun, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
        · rw [Finset.disjoint_filter]; intro p _ h1 h2; exact h2 h1
      omega
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, hcard_swap, hcard_off] at h1
    have hmul : N * (N - 1) = N * N - N := by rw [Nat.mul_sub, mul_one]
    omega
  -- Union bound gives `μ (⋃ p ∈ pairs, bad p) < 1`.
  have hunion_lt : μ (⋃ p ∈ pairs, bad p) < 1 := by
    have h1 : μ (⋃ p ∈ pairs, bad p) ≤ ∑ p ∈ pairs, μ (bad p) := measure_biUnion_finset_le _ _
    have h2 : ∑ p ∈ pairs, μ (bad p) ≤
        (pairs.card : ℝ≥0∞) * ENNReal.ofReal (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) := by
      calc
        ∑ p ∈ pairs, μ (bad p)
          ≤ ∑ _p ∈ pairs, ENNReal.ofReal (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) :=
            Finset.sum_le_sum fun p _ => hbad_le p
        _ = (pairs.card : ℝ≥0∞) * ENNReal.ofReal (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hexp_le : Real.exp (-(k : ℝ) * ε ^ 2 / 8) ≤ ((N : ℝ) ^ 2)⁻¹ := by
      have hk_mul : 2 * Real.log (N : ℝ) ≤ (k : ℝ) * ε ^ 2 / 8 := by
        have hε2 : 0 < ε ^ 2 := by positivity
        have := (div_le_iff₀ hε2).mp hk
        linarith
      calc
        Real.exp (-(k : ℝ) * ε ^ 2 / 8)
          ≤ Real.exp (-(2 * Real.log (N : ℝ))) := Real.exp_le_exp.mpr (by linarith)
        _ = (Real.exp (2 * Real.log (N : ℝ)))⁻¹ := Real.exp_neg _
        _ = ((N : ℝ) ^ 2)⁻¹ := by
            rw [mul_comm, Real.exp_mul, Real.exp_log (by linarith : (0 : ℝ) < N)]
            norm_cast
    have hreal_lt : (pairs.card : ℝ) * (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) < 1 := by
      have hcard_r : (2 : ℝ) * (pairs.card : ℝ) ≤ (N : ℝ) * ((N : ℝ) - 1) := by
        have hcast : ((2 * pairs.card : ℕ) : ℝ) ≤ ((N * (N - 1) : ℕ) : ℝ) := by exact_mod_cast hcard
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ N)] at hcast
        simpa using hcast
      have hNpos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
      calc
        (pairs.card : ℝ) * (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8))
          = (2 * (pairs.card : ℝ)) * Real.exp (-(k : ℝ) * ε ^ 2 / 8) := by ring
        _ ≤ ((N : ℝ) * ((N : ℝ) - 1)) * ((N : ℝ) ^ 2)⁻¹ :=
            mul_le_mul hcard_r hexp_le (Real.exp_pos _).le (by nlinarith)
        _ < ((N : ℝ) * (N : ℝ)) * ((N : ℝ) ^ 2)⁻¹ := by
            have : (N : ℝ) * ((N : ℝ) - 1) < (N : ℝ) * (N : ℝ) := by nlinarith
            exact mul_lt_mul_of_pos_right this (inv_pos.mpr hNpos)
        _ = 1 := by rw [← sq, mul_inv_cancel₀ hNpos.ne']
    calc
      μ (⋃ p ∈ pairs, bad p)
        ≤ (pairs.card : ℝ≥0∞) * ENNReal.ofReal (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) := h1.trans h2
      _ = ENNReal.ofReal ((pairs.card : ℝ) * (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8))) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ < ENNReal.ofReal 1 := ENNReal.ofReal_lt_ofReal_iff zero_lt_one |>.mpr hreal_lt
      _ = 1 := ENNReal.ofReal_one
  -- Therefore the complement of the bad union is nonempty.
  have hne : ((⋃ p ∈ pairs, bad p)ᶜ).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty, compl_empty_iff] at hemp
    rw [hemp, measure_univ] at hunion_lt
    exact lt_irrefl 1 hunion_lt
  obtain ⟨g, hg⟩ := hne
  refine ⟨L_of g, fun i j => ?_⟩
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hnot : g ∉ bad (i, j) := fun hmem =>
      hg (Set.mem_biUnion (show (i, j) ∈ pairs by simp [pairs, hij]) hmem)
    simp only [bad, mem_ofPred_eq, not_or, not_lt] at hnot
    simpa [map_sub] using hnot
  · simp
  · have hnot : g ∉ bad (j, i) := fun hmem =>
      hg (Set.mem_biUnion (show (j, i) ∈ pairs by simp [pairs, hji]) hmem)
    simp only [bad, mem_ofPred_eq, not_or, not_lt] at hnot
    simpa [map_sub, norm_sub_rev] using hnot

end JohnsonLindenstrauss

/-! ### 6. Dvoretzky's Theorem (Ball, Lecture 9) -/

section Dvoretzky

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Elementary 1D Gaussian interval complement lower bound:
for every `r ≥ 0`, `∫ t in Icc (-r) r, gaussianPDFReal 0 1 t ≤ 1 - (1 / 5) * exp (-r²)`. -/
private lemma integral_Icc_gaussianPDFReal_le {r : ℝ} (hr : 0 ≤ r) :
    ∫ t in Icc (-r) r, gaussianPDFReal 0 1 t ≤ 1 - (1 / 5 : ℝ) * Real.exp (-(r ^ 2)) := by
  have hint := integrable_gaussianPDFReal 0 1
  -- Lower bound the upper tail on `[r, r + 1]`.
  have htail_hi : (1 / 10 : ℝ) * Real.exp (-(r ^ 2)) ≤ ∫ t in Ioi r, gaussianPDFReal 0 1 t := by
    have hsub : Icc r (r + 1) ⊆ Ioi r ∪ {r} := fun t ht => by
      rcases lt_or_eq_of_le ht.1 with h | h
      · exact Or.inl h
      · exact Or.inr h.symm
    have h1 : ∫ t in Icc r (r + 1), gaussianPDFReal 0 1 t ≤ ∫ t in Ioi r,
      gaussianPDFReal 0 1 t := by
      rw [← setIntegral_congr_set (Ioo_ae_eq_Icc (a := r) (b := r + 1))]
      exact setIntegral_mono_set hint.integrableOn
        (ae_of_all _ fun t => gaussianPDFReal_nonneg 0 1 t)
        (ae_of_all _ fun t ht => ht.1)
    have hpt : ∀ t ∈ Icc r (r + 1),
        (1 / 10 : ℝ) * Real.exp (-(r ^ 2)) ≤ gaussianPDFReal 0 1 t := fun t ht => by
      rw [gaussianPDFReal_def]
      simp only [NNReal.coe_one, mul_one, sub_zero]
      have hsqrt : Real.sqrt (2 * Real.pi) < 3 := by
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 3)]
        linarith [Real.pi_lt_d2]
      have hinv : (1 / 3 : ℝ) < (Real.sqrt (2 * Real.pi))⁻¹ := by
        rw [one_div]
        exact (inv_lt_inv₀ (by norm_num) (by positivity)).mpr hsqrt
      have hexp1 : (1 / 3 : ℝ) < Real.exp (-1) := by
        rw [Real.exp_neg, one_div]
        exact (inv_lt_inv₀ (by norm_num) (Real.exp_pos 1)).mpr (by linarith [Real.exp_one_lt_d9])
      have ht_sq : -(r ^ 2) - 1 ≤ -(t ^ 2) / 2 := by
        have h1 : t ≤ r + 1 := ht.2
        have h2 : 0 ≤ t := hr.trans ht.1
        nlinarith [sq_nonneg (r - 1)]
      calc
        (1 / 10 : ℝ) * Real.exp (-(r ^ 2))
          ≤ ((1 / 3 : ℝ) * (1 / 3 : ℝ)) * Real.exp (-(r ^ 2)) := by
            gcongr; norm_num
        _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-1) * Real.exp (-(r ^ 2)) := by
            gcongr
        _ = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(r ^ 2) - 1) := by
            rw [mul_assoc, ← Real.exp_add]; congr 2; ring
        _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2) / 2) := by
            gcongr
    have h2 : (1 / 10 : ℝ) * Real.exp (-(r ^ 2)) ≤ ∫ t in Icc r (r + 1), gaussianPDFReal 0 1 t := by
      calc
        (1 / 10 : ℝ) * Real.exp (-(r ^ 2))
          = ∫ _t in Icc r (r + 1), ((1 / 10 : ℝ) * Real.exp (-(r ^ 2))) := by
            rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by linarith)]
            ring
        _ ≤ ∫ t in Icc r (r + 1), gaussianPDFReal 0 1 t :=
            setIntegral_mono_on (integrableOn_const (by simp)) hint.integrableOn
              measurableSet_Icc hpt
    exact h2.trans h1
  -- By symmetry `gaussianPDFReal 0 1 (-t) = gaussianPDFReal 0 1 t` , the lower tail equals the
  -- upper tail.
  have htail_lo : ∫ t in Iio (-r), gaussianPDFReal 0 1 t = ∫ t in Ioi r, gaussianPDFReal 0 1 t := by
    rw [← integral_Iic_eq_integral_Iio, ← integral_comp_neg_Ioi]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp [gaussianPDFReal_def]
  -- Partition `ℝ = Iio (-r) ∪ Icc (-r) r ∪ Ioi r`.
  have hpart : (∫ t in Iio (-r), gaussianPDFReal 0 1 t) +
      (∫ t in Icc (-r) r, gaussianPDFReal 0 1 t) +
      (∫ t in Ioi r, gaussianPDFReal 0 1 t) = 1 := by
    have hdisj1 : Disjoint (Iio (-r)) (Icc (-r) r) := by
      rw [Set.disjoint_left]; intro t ht1 ht2
      have h1 := mem_Iio.mp ht1; have h2 := mem_Icc.mp ht2; linarith
    have hdisj2 : Disjoint (Iio (-r) ∪ Icc (-r) r) (Ioi r) := by
      rw [Set.disjoint_left]; intro t ht1 ht2
      have h2 := mem_Ioi.mp ht2
      rcases ht1 with h | h
      · have h1 := mem_Iio.mp h; linarith
      · have h1 := mem_Icc.mp h; linarith
    have hunion : (Iio (-r) ∪ Icc (-r) r) ∪ Ioi r = Set.univ := by
      ext t; simp only [mem_union, mem_Iio, mem_Icc, mem_Ioi, mem_univ, iff_true]
      by_cases h1 : t < -r
      · exact Or.inl (Or.inl h1)
      · by_cases h2 : t ≤ r
        · exact Or.inl (Or.inr ⟨not_lt.mp h1, h2⟩)
        · exact Or.inr (not_le.mp h2)
    rw [← setIntegral_union hdisj1 measurableSet_Icc hint.integrableOn hint.integrableOn,
      ← setIntegral_union hdisj2 measurableSet_Ioi
        (hint.integrableOn.union hint.integrableOn) hint.integrableOn,
      hunion, setIntegral_univ, integral_gaussianPDFReal_eq_one 0 one_ne_zero]
  linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For an origin-symmetric convex body `K` with `closedBall 0 1 ⊆ K`, `gauge K` is 1-Lipschitz. -/
lemma lipschitzWith_gauge_of_closedBall_subset (K : ConvexBody E)
    (hsym : IsOriginSymmetric (K : Set E)) (hball : closedBall (0 : E) 1 ⊆ (K : Set E)) :
    LipschitzWith 1 (fun x : E => gauge (K : Set E) x) := by
  have h0 : (0 : E) ∈ interior (K : Set E) := by
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : E) zero_lt_one) hball
  have habs : Absorbent ℝ (K : Set E) := absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp h0)
  have hle_norm : ∀ z : E, gauge (K : Set E) z ≤ ‖z‖ := fun z => by
    by_cases hz : z = 0
    · simp [hz]
    · have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have hmem : z ∈ ‖z‖ • (K : Set E) := by
        refine ⟨‖z‖⁻¹ • z, hball ?_, ?_⟩
        · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hnorm_pos), inv_mul_cancel₀ hnorm_pos.ne']
        · dsimp only; rw [smul_smul, mul_inv_cancel₀ hnorm_pos.ne', one_smul]
      exact gauge_le_of_mem hnorm_pos.le hmem
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm, abs_le]
  have h1 : gauge (K : Set E) x ≤ gauge (K : Set E) y + gauge (K : Set E) (x - y) := by
    have := gauge_add_le K.convex habs y (x - y)
    simpa [add_sub_cancel] using this
  have h2 : gauge (K : Set E) y ≤ gauge (K : Set E) x + gauge (K : Set E) (x - y) := by
    have := gauge_add_le K.convex habs x (y - x)
    rw [add_sub_cancel, show y - x = -(x - y) by abel,
      gauge_neg_of_isOriginSymmetric hsym] at this
    exact this
  exact ⟨by linarith [hle_norm (x - y)], by linarith [hle_norm (x - y)]⟩

/-- **John-Position Gaussian Gauge Lower Bound (Ball, Lecture 9):**
for any origin-symmetric convex body `K : ConvexBody E` in John's position in dimension `d ≥ 2`,
$$\int_E \|x\|_K\,d\gamma_d(x) \ge \frac{1}{4}\sqrt{\log d}.$$ -/
theorem john_position_gaussian_gauge_lower_bound
    (K : ConvexBody E) (hsym : IsOriginSymmetric (K : Set E))
    (hJ : IsJohnPosition (K : Set E)) (hd2 : 2 ≤ Module.finrank ℝ E) :
    (1 / 4 : ℝ) * Real.sqrt (Real.log (Module.finrank ℝ E : ℝ)) ≤
      ∫ x : E, gauge (K : Set E) x ∂stdGaussian E := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
  set d : ℕ := Module.finrank ℝ E
  set M : ℝ := ∫ x : E, gauge (K : Set E) x ∂stdGaussian E
  have hlip : LipschitzWith 1 (fun x : E => gauge (K : Set E) x) :=
    lipschitzWith_gauge_of_closedBall_subset K hsym hJ.1
  have hint_g : Integrable (fun x : E => gauge (K : Set E) x) (stdGaussian E) :=
    integrable_lipschitz_stdGaussian hlip
  by_cases hd16 : 16 ≤ d
  · -- Large dimension `d ≥ 16`: use `john_position_gaussian_measure_le` at `r = (1/2) * √(log d)`.
    have hd_r : (16 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd16
    have hlog_pos : 0 < Real.log (d : ℝ) := Real.log_pos (by linarith)
    set r : ℝ := (1 / 2 : ℝ) * Real.sqrt (Real.log (d : ℝ))
    have hr_pos : 0 < r := by positivity
    -- `{x | gauge K x < r} ⊆ r • K`.
    have hsub_rK : {x : E | gauge (K : Set E) x < r} ⊆ r • (K : Set E) := by
      intro x hx
      have h0 : (0 : E) ∈ interior (K : Set E) := by
        rw [mem_interior_iff_mem_nhds]
        exact Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : E) zero_lt_one) hJ.1
      have hlt1 : gauge (K : Set E) (r⁻¹ • x) < 1 := by
        rw [gauge_smul_of_nonneg (inv_nonneg.mpr hr_pos.le), smul_eq_mul]
        exact (inv_mul_lt_one₀ hr_pos).mpr hx
      have hmemK : r⁻¹ • x ∈ (K : Set E) :=
        interior_subset
          ((gauge_lt_one_iff_mem_interior K.convex (mem_interior_iff_mem_nhds.mp h0)).mp hlt1)
      exact ⟨r⁻¹ • x, hmemK, by dsimp only; rw [smul_smul, mul_inv_cancel₀ hr_pos.ne', one_smul]⟩
    -- Apply `john_position_gaussian_measure_le` from `BrascampLieb`.
    have hbl := john_position_gaussian_measure_le K hsym hJ hr_pos
    have hmeas_rK : stdGaussian E (r • (K : Set E)) ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [stdGaussian_eq_withDensity,
        withDensity_apply _ (K.isCompact.smul r).isClosed.measurableSet]
      refine hbl.trans ?_
      have hI_le := integral_Icc_gaussianPDFReal_le hr_pos.le
      have hI_nn : 0 ≤ ∫ t in Icc (-r) r, gaussianPDFReal 0 1 t :=
        setIntegral_nonneg measurableSet_Icc fun _ _ => gaussianPDFReal_nonneg 0 1 _
      rw [← ENNReal.ofReal_pow hI_nn]
      apply ENNReal.ofReal_le_ofReal
      have hexp1 : ∫ t in Icc (-r) r, gaussianPDFReal 0 1 t ≤
          Real.exp (-((1 / 5 : ℝ) * Real.exp (-(r ^ 2)))) :=
        hI_le.trans (by linarith [Real.add_one_le_exp (-((1 / 5 : ℝ) * Real.exp (-(r ^ 2))))])
      have hpow_le : (∫ t in Icc (-r) r, gaussianPDFReal 0 1 t) ^ d ≤
          Real.exp (-((d : ℝ) / 5) * Real.exp (-(r ^ 2))) := by
        calc
          (∫ t in Icc (-r) r, gaussianPDFReal 0 1 t) ^ d
            ≤ (Real.exp (-((1 / 5 : ℝ) * Real.exp (-(r ^ 2))))) ^ d :=
              pow_le_pow_left₀ hI_nn hexp1 d
          _ = Real.exp ((d : ℝ) * -((1 / 5 : ℝ) * Real.exp (-(r ^ 2)))) := by
              rw [← Real.exp_nat_mul]
          _ = Real.exp (-((d : ℝ) / 5) * Real.exp (-(r ^ 2))) := by congr 1; ring
      refine hpow_le.trans ?_
      -- Compute `exp (-r²) = d^(-1/4)` so `(d / 5) * exp (-r²) = d^(3/4) / 5 ≥ 8 / 5 ≥ 1`.
      have hr_sq : r ^ 2 = (1 / 4 : ℝ) * Real.log (d : ℝ) := by
        dsimp only [r]; rw [mul_pow, Real.sq_sqrt hlog_pos.le]; ring
      have hexp_r : Real.exp (-(r ^ 2)) = (d : ℝ) ^ (-(1 : ℝ) / 4) := by
        rw [hr_sq, Real.rpow_def_of_pos (by linarith : (0 : ℝ) < d)]
        congr 1; ring
      have hd34 : (8 : ℝ) ≤ (d : ℝ) ^ ((3 : ℝ) / 4) := by
        have h16 : (8 : ℝ) = (16 : ℝ) ^ ((3 : ℝ) / 4) := by
          have : (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by norm_num
          rw [this, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
        rw [h16]
        exact Real.rpow_le_rpow (by norm_num) hd_r (by norm_num)
      have hprod_ge : (1 : ℝ) ≤ ((d : ℝ) / 5) * Real.exp (-(r ^ 2)) := by
        rw [hexp_r, div_mul_eq_mul_div]
        have hmul : (d : ℝ) * (d : ℝ) ^ (-(1 : ℝ) / 4) = (d : ℝ) ^ ((3 : ℝ) / 4) := by
          conv_lhs => arg 1; rw [← Real.rpow_one (d : ℝ)]
          rw [← Real.rpow_add (by linarith : (0 : ℝ) < d)]
          congr 1; ring
        rw [hmul]; linarith
      have hexp_half : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg, one_div]
        exact (inv_le_inv₀ (Real.exp_pos 1) two_pos).mpr (by linarith [Real.add_one_le_exp (1 : ℝ)])
      exact (Real.exp_le_exp.mpr (by linarith)).trans hexp_half
    -- Now Markov's inequality on `{x | r ≤ gauge K x}` (which has measure ≥ 1/2).
    set S : Set E := {x : E | r ≤ gauge (K : Set E) x}
    have hSm : MeasurableSet S := (isClosed_le continuous_const hlip.continuous).measurableSet
    have hSc_le : stdGaussian E Sᶜ ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
      have hSc_eq : Sᶜ = {x : E | gauge (K : Set E) x < r} := by ext x; simp [S]
      rw [hSc_eq]
      exact (measure_mono hsub_rK).trans hmeas_rK
    have hS_ge : (1 / 2 : ℝ) ≤ (stdGaussian E).real S := by
      have hsum : stdGaussian E S + stdGaussian E Sᶜ = 1 := by
        rw [measure_add_measure_compl hSm, measure_univ]
      have h1 : (stdGaussian E).real S + (stdGaussian E).real Sᶜ = 1 := by
        have := congrArg ENNReal.toReal hsum
        rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
          ENNReal.toReal_one] at this
        exact this
      have h2 : (stdGaussian E).real Sᶜ ≤ 1 / 2 := by
        rw [Measure.real]
        exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hSc_le).trans_eq
          (ENNReal.toReal_ofReal (by norm_num))
      linarith
    have hM_ge : r * (stdGaussian E).real S ≤ M := by
      have h1 : r * (stdGaussian E).real S = ∫ _x in S, r ∂stdGaussian E := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
      rw [h1]
      calc
        ∫ _x in S, r ∂stdGaussian E
          ≤ ∫ x in S, gauge (K : Set E) x ∂stdGaussian E :=
            setIntegral_mono_on (integrable_const r).integrableOn hint_g.integrableOn hSm
              fun x hx => hx
        _ ≤ ∫ x : E, gauge (K : Set E) x ∂stdGaussian E :=
            setIntegral_le_integral hint_g (ae_of_all _ fun x => gauge_nonneg x)
    calc
      (1 / 4 : ℝ) * Real.sqrt (Real.log (d : ℝ)) = r * (1 / 2) := by dsimp only [r]; ring
      _ ≤ r * (stdGaussian E).real S := by gcongr
      _ ≤ M := hM_ge
  · -- Small dimension `2 ≤ d < 16`: use `K ⊆ √d • B₂` so `gauge K x ≥ ‖x‖ / √d`.
    push Not at hd16
    have hd_lt16 : (d : ℝ) < 16 := by exact_mod_cast hd16
    have hd_ge2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
    have hK_sub : (K : Set E) ⊆ Real.sqrt (d : ℝ) • closedBall (0 : E) 1 :=
      subset_sqrt_finrank_smul_of_john_position K hsym hJ
    have hgauge_ge : ∀ x : E, ‖x‖ / Real.sqrt (d : ℝ) ≤ gauge (K : Set E) x := fun x => by
      have hsqrt_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by linarith)
      have hball_eq : Real.sqrt (d : ℝ) • closedBall (0 : E) 1 =
        closedBall (0 : E) (Real.sqrt (d : ℝ)) := by
        ext y
        simp only [mem_smul_set, mem_closedBall_zero_iff]
        constructor
        · rintro ⟨z, hz, rfl⟩
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsqrt_pos]
          nlinarith
        · intro hy
          refine ⟨(Real.sqrt (d : ℝ))⁻¹ • y, ?_,
            by rw [smul_smul, mul_inv_cancel₀ hsqrt_pos.ne', one_smul]⟩
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsqrt_pos)]
          exact (inv_mul_le_one₀ hsqrt_pos).mpr hy
      have hK_sub' : (K : Set E) ⊆ closedBall (0 : E) (Real.sqrt (d : ℝ)) := hball_eq ▸ hK_sub
      have h0 : (0 : E) ∈ interior (K : Set E) := by
        rw [mem_interior_iff_mem_nhds]
        exact Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : E) zero_lt_one) hJ.1
      have h1 := gauge_mono (absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp h0)) hK_sub' x
      have hball_gauge : gauge (closedBall (0 : E) (Real.sqrt (d : ℝ))) x =
        ‖x‖ / Real.sqrt (d : ℝ) :=
        gauge_closedBall (Real.sqrt_nonneg _) x
      linarith
    have hM_ge : (d : ℝ) / (Real.sqrt (d : ℝ) * Real.sqrt ((d : ℝ) + 2)) ≤ M := by
      have h1 :=
        integral_mono (integrable_norm_stdGaussian.div_const (Real.sqrt (d : ℝ))) hint_g hgauge_ge
      rw [integral_div] at h1
      have hnorm := div_sqrt_le_integral_norm_stdGaussian (E := E)
      calc
        (d : ℝ) / (Real.sqrt (d : ℝ) * Real.sqrt ((d : ℝ) + 2))
          = ((d : ℝ) / Real.sqrt ((d : ℝ) + 2)) / Real.sqrt (d : ℝ) := by
            rw [div_div, mul_comm]
        _ ≤ (∫ x : E, ‖x‖ ∂stdGaussian E) / Real.sqrt (d : ℝ) :=
            div_le_div_of_nonneg_right hnorm (Real.sqrt_nonneg _)
        _ ≤ M := h1
    have hhalf_le : (1 / 2 : ℝ) ≤ (d : ℝ) / (Real.sqrt (d : ℝ) * Real.sqrt ((d : ℝ) + 2)) := by
      rw [le_div_iff₀ (by positivity)]
      have hsq : ((1 / 2 : ℝ) * (Real.sqrt (d : ℝ) * Real.sqrt ((d : ℝ) + 2))) ^ 2 ≤
        (d : ℝ) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
        nlinarith
      exact le_of_sq_le_sq hsq (by linarith)
    have hlog_lt4 : Real.log (d : ℝ) < 4 := by
      rw [Real.log_lt_iff_lt_exp (by linarith)]
      have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have he4 : (16 : ℝ) ≤ Real.exp 4 := by
        calc
          (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
          _ ≤ (Real.exp 1) ^ (4 : ℕ) := pow_le_pow_left₀ (by norm_num) he2 4
          _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
      linarith
    have hsqrt_lt2 : Real.sqrt (Real.log (d : ℝ)) < 2 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
      linarith
    linarith

/-- **Milman's Gaussian Dvoretzky Theorem (Ball, Lecture 9):**
for any origin-symmetric convex body `K : ConvexBody E` with `closedBall 0 1 ⊆ K`,
`M := ∫ x, gauge K x ∂stdGaussian E`, `ε ∈ (0, 1)`, and `k ≥ 1` satisfying
`512 * k * log (48 / ε) ≤ (ε * M)²`, there exists a `k`-dimensional subspace `F : Submodule ℝ E`
and a linear equivalence `T : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] F` such that for every
`w : EuclideanSpace ℝ (Fin k)`:
$$\|w\| \le \|T w\|_K \le (1 + \varepsilon)\|w\|.$$ -/
theorem milman_gaussian_dvoretzky
    (K : ConvexBody E) (hsym : IsOriginSymmetric (K : Set E))
    (hball : closedBall (0 : E) 1 ⊆ (K : Set E))
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {k : ℕ} (hk1 : 1 ≤ k)
    (hk_bd : (512 : ℝ) * (k : ℝ) * Real.log (48 / ε) ≤
      (ε * ∫ x : E, gauge (K : Set E) x ∂stdGaussian E) ^ 2) :
    ∃ (F : Submodule ℝ E) (T : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] F),
      Module.finrank ℝ F = k ∧
      ∀ w : EuclideanSpace ℝ (Fin k),
        ‖w‖ ≤ gauge (K : Set E) (T w : E) ∧ gauge (K : Set E) (T w : E) ≤ (1 + ε) * ‖w‖ := by
  set M : ℝ := ∫ x : E, gauge (K : Set E) x ∂stdGaussian E
  have hlog48_pos : 0 < Real.log (48 / ε) := Real.log_pos (by
    rw [one_lt_div hε0]; linarith)
  have hM_nn : 0 ≤ M := integral_nonneg fun _ => gauge_nonneg _
  have hM_pos : 0 < M := by
    by_contra hM0
    have hMeq : M = 0 := le_antisymm (not_lt.mp hM0) hM_nn
    rw [hMeq, mul_zero, zero_pow two_ne_zero] at hk_bd
    have hk_r : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hpos : (0 : ℝ) < 512 * (k : ℝ) * Real.log (48 / ε) := by positivity
    linarith
  have hlip : LipschitzWith 1 (fun x : E => gauge (K : Set E) x) :=
    lipschitzWith_gauge_of_closedBall_subset K hsym hball
  -- Step 1: Extract a finite `δ` -net `N ⊆ sphere 0 1` in `EuclideanSpace ℝ (Fin k)` with
  -- `δ = ε / 8` .
  set δ : ℝ := ε / 8
  have hδ_pos : 0 < δ := by positivity
  have hδ_lt : δ < 1 / 8 := by dsimp only [δ]; linarith
  let δnn : ℝ≥0 := ⟨δ, hδ_pos.le⟩
  let S : Set (EuclideanSpace ℝ (Fin k)) := sphere (0 : EuclideanSpace ℝ (Fin k)) 1
  have hcov_le : (Metric.coveringNumber δnn S : ℝ≥0∞) ≤ ENNReal.ofReal ((48 / ε) ^ k) := by
    have h1 : Metric.coveringNumber δnn S ≤
        Metric.coveringNumber (δnn / 2) (closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) :=
      Metric.coveringNumber_subset_le Metric.sphere_subset_closedBall
    have hδ2_pos : (0 : ℝ≥0) < δnn / 2 := by
      change (0 : ℝ) < δ / 2; positivity
    have hδ2_le1 : δnn / 2 ≤ 1 := by
      change δ / 2 ≤ 1; linarith
    have h2 := coveringNumber_closedBall_le_three_div (E := EuclideanSpace ℝ (Fin k))
      volume hδ2_pos hδ2_le1
    rw [finrank_euclideanSpace_fin] at h2
    have hcast : (Metric.coveringNumber δnn S : ℝ≥0∞) ≤
        (Metric.coveringNumber (δnn / 2) (closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) : ℝ≥0∞) := by
      exact_mod_cast h1
    refine hcast.trans (h2.trans ?_)
    apply ENNReal.ofReal_le_ofReal
    have hratio : 3 / ((δnn / 2 : ℝ≥0) : ℝ) = 48 / ε := by
      change 3 / (δ / 2) = 48 / ε
      dsimp only [δ]; field_simp [hε0.ne']; ring
    rw [hratio]
  have hcov_ne_top : Metric.coveringNumber δnn S ≠ ⊤ := by
    intro htop
    rw [htop] at hcov_le
    simp at hcov_le
  obtain ⟨Nset, hNsub, hNfin, hNcov, hNcard⟩ :=
    Metric.exists_set_encard_eq_coveringNumber hcov_ne_top
  let N : Finset (EuclideanSpace ℝ (Fin k)) := hNfin.toFinset
  have hN_card_le : (N.card : ℝ) ≤ (48 / ε) ^ k := by
    have h1 : (N.card : ℝ≥0∞) ≤ ENNReal.ofReal ((48 / ε) ^ k) := by
      have hcard_eq : (N.card : ℕ∞) = Nset.encard := by
        simpa [N] using hNfin.encard_eq_coe_toFinset_card.symm
      have hcard_enn : (N.card : ℝ≥0∞) = (Metric.coveringNumber δnn S : ℝ≥0∞) := by
        rw [← hNcard, ← hcard_eq]; simp
      rwa [hcard_enn]
    rw [← ENNReal.ofReal_natCast] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  -- Step 2: Probabilistic union bound on `μ = Measure.pi (fun _ : Fin k => stdGaussian E)`.
  let μ := Measure.pi (fun _ : Fin k => stdGaussian E)
  let G_of : (Fin k → E) → (EuclideanSpace ℝ (Fin k) →ₗ[ℝ] E) := fun g =>
    { toFun := fun w => ∑ j : Fin k, WithLp.ofLp w j • g j
      map_add' := fun w₁ w₂ => by
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c w => by
        simp [smul_smul, Finset.smul_sum] }
  let bad : EuclideanSpace ℝ (Fin k) → Set (Fin k → E) := fun z =>
    {g : Fin k → E | δ * M ≤ |gauge (K : Set E) (G_of g z) - M|}
  have hbad_le : ∀ z ∈ N, μ (bad z) ≤ ENNReal.ofReal (2 * Real.exp (-((δ * M) ^ 2) / 4)) :=
    fun z hz => by
    have hzS : z ∈ S := hNsub (hNfin.mem_toFinset.mp hz)
    have hz_sum : ∑ j : Fin k, WithLp.ofLp z j ^ 2 = 1 := by
      have h1 : ‖z‖ ^ 2 = 1 := by rw [mem_sphere_zero_iff_norm.mp hzS, one_pow]
      rw [EuclideanSpace.norm_sq_eq] at h1
      simpa [Real.norm_eq_abs, sq_abs] using h1
    have hmp_z : MeasurePreserving (fun g : Fin k → E => G_of g z) μ (stdGaussian E) :=
      measurePreserving_linearComb_stdGaussian hz_sum
    have hmeas_set : MeasurableSet {x : E | δ * M ≤ |gauge (K : Set E) x - M|} :=
      (isClosed_le continuous_const (hlip.continuous.sub continuous_const).abs).measurableSet
    have hpre : bad z =
      (fun g : Fin k → E => G_of g z) ⁻¹' {x : E | δ * M ≤ |gauge (K : Set E) x - M|} := rfl
    rw [hpre, hmp_z.measure_preimage hmeas_set.nullMeasurableSet]
    have hconc := gaussian_lipschitz_concentration_mean (L :=
      1) zero_lt_one hlip (mul_nonneg hδ_pos.le hM_pos.le)
    simpa [M] using hconc
  have hunion_lt : μ (⋃ z ∈ N, bad z) < 1 := by
    have h1 : μ (⋃ z ∈ N, bad z) ≤ ∑ z ∈ N, μ (bad z) := measure_biUnion_finset_le _ _
    have h2 : ∑ z ∈ N, μ (bad z) ≤
        (N.card : ℝ≥0∞) * ENNReal.ofReal (2 * Real.exp (-((δ * M) ^ 2) / 4)) := by
      calc
        ∑ z ∈ N, μ (bad z)
          ≤ ∑ _z ∈ N, ENNReal.ofReal (2 * Real.exp (-((δ * M) ^ 2) / 4)) :=
            Finset.sum_le_sum fun z hz => hbad_le z hz
        _ = (N.card : ℝ≥0∞) * ENNReal.ofReal (2 * Real.exp (-((δ * M) ^ 2) / 4)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hreal_lt : (N.card : ℝ) * (2 * Real.exp (-((δ * M) ^ 2) / 4)) < 1 := by
      have hlog2_lt : Real.log 2 < Real.log (48 / ε) :=
        Real.log_lt_log two_pos (by rw [lt_div_iff₀ hε0]; linarith)
      have hk_r : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      have hlog_sum : (k : ℝ) * Real.log (48 / ε) + Real.log 2 < (δ * M) ^ 2 / 4 := by
        have hδ_eq : (δ * M) ^ 2 / 4 = (ε * M) ^ 2 / 256 := by dsimp only [δ]; ring
        rw [hδ_eq]
        have : Real.log 2 < (k : ℝ) * Real.log (48 / ε) :=
          hlog2_lt.trans_le (le_mul_of_one_le_left hlog48_pos.le hk_r)
        linarith
      have hprod_lt : (48 / ε) ^ k * (2 * Real.exp (-((δ * M) ^ 2) / 4)) < 1 := by
        have hpos48 : 0 < 48 / ε := by positivity
        have hrewrite : (48 / ε) ^ k * (2 * Real.exp (-((δ * M) ^ 2) / 4)) =
            Real.exp ((k : ℝ) * Real.log (48 / ε) + Real.log 2 - (δ * M) ^ 2 / 4) := by
          rw [Real.exp_sub, Real.exp_add, Real.exp_log two_pos, mul_comm (k : ℝ),
            Real.exp_mul, Real.exp_log hpos48, Real.rpow_natCast,
            show -(δ * M) ^ 2 / 4 = -((δ * M) ^ 2 / 4) by ring, Real.exp_neg, div_eq_mul_inv]
          ring
        rw [hrewrite, Real.exp_lt_one_iff]
        linarith
      exact (mul_le_mul_of_nonneg_right hN_card_le (by positivity)).trans_lt hprod_lt
    calc
      μ (⋃ z ∈ N, bad z)
        ≤ (N.card : ℝ≥0∞) * ENNReal.ofReal (2 * Real.exp (-((δ * M) ^ 2) / 4)) := h1.trans h2
      _ = ENNReal.ofReal ((N.card : ℝ) * (2 * Real.exp (-((δ * M) ^ 2) / 4))) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ < ENNReal.ofReal 1 := ENNReal.ofReal_lt_ofReal_iff zero_lt_one |>.mpr hreal_lt
      _ = 1 := ENNReal.ofReal_one
  have hne_good : ((⋃ z ∈ N, bad z)ᶜ).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty, compl_empty_iff] at hemp
    rw [hemp, measure_univ] at hunion_lt
    exact lt_irrefl 1 hunion_lt
  obtain ⟨g, hg⟩ := hne_good
  have hnet_good : ∀ z ∈ N, |gauge (K : Set E) (G_of g z) - M| < δ * M := fun z hz => by
    have hnot : g ∉ bad z := fun hmem => hg (Set.mem_biUnion hz hmem)
    exact not_le.mp hnot
  -- Step 3: Successive approximation from the `δ`-net `N` to the entire unit sphere `S`.
  have h0 : (0 : E) ∈ interior (K : Set E) := by
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : E) zero_lt_one) hball
  have habs : Absorbent ℝ (K : Set E) := absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp h0)
  have hG_cont : Continuous (fun w : EuclideanSpace ℝ (Fin k) => gauge (K : Set E) (G_of g w)) :=
    hlip.continuous.comp (LinearMap.continuous_of_finiteDimensional (G_of g))
  have hS_ne : S.Nonempty := by
    let e0 : EuclideanSpace ℝ (Fin k) := EuclideanSpace.single ⟨0, hk1⟩ 1
    exact ⟨e0, by simp [S, e0]⟩
  obtain ⟨w0, hw0S, hw0_max⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin k)) 1).exists_isMaxOn
    hS_ne hG_cont.continuousOn
  set A : ℝ := gauge (K : Set E) (G_of g w0)
  have hA_bound : ∀ v : EuclideanSpace ℝ (Fin k), gauge (K : Set E) (G_of g v) ≤ A * ‖v‖ :=
    fun v => by
    by_cases hv : v = 0
    · simp [hv]
    · have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have huS : (‖v‖⁻¹ • v) ∈ S := by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hv_pos), inv_mul_cancel₀ hv_pos.ne']
      have hmax : gauge (K : Set E) (G_of g (‖v‖⁻¹ • v)) ≤ A := hw0_max huS
      rw [map_smul, gauge_smul_of_nonneg (inv_nonneg.mpr hv_pos.le), smul_eq_mul] at hmax
      have := mul_le_mul_of_nonneg_right hmax hv_pos.le
      rwa [mul_comm, ← mul_assoc, mul_inv_cancel₀ hv_pos.ne', one_mul] at this
  have hcover_dist : ∀ w ∈ S, ∃ z ∈ N, ‖w - z‖ ≤ δ := fun w hw => by
    obtain ⟨z, hzN, hdz⟩ := hNcov hw
    refine ⟨z, hNfin.mem_toFinset.mpr hzN, ?_⟩
    rw [← dist_eq_norm]
    exact (edist_le_coe.mp hdz)
  -- Upper bound on `A`: `A ≤ ((1 + δ) / (1 - δ)) * M`.
  have hA_le : A ≤ ((1 + δ) / (1 - δ)) * M := by
    obtain ⟨z0, hz0N, hz0_dist⟩ := hcover_dist w0 hw0S
    have htri : A ≤ gauge (K : Set E) (G_of g z0) + gauge (K : Set E) (G_of g (w0 - z0)) := by
      have h := gauge_add_le K.convex habs (G_of g z0) (G_of g (w0 - z0))
      rw [← map_add, add_sub_cancel] at h
      exact h
    have hz0_hi : gauge (K : Set E) (G_of g z0) ≤ (1 + δ) * M := by
      linarith [(abs_lt.mp (hnet_good z0 hz0N)).2]
    have hdiff_le : gauge (K : Set E) (G_of g (w0 - z0)) ≤ A * δ :=
      (hA_bound (w0 - z0)).trans (mul_le_mul_of_nonneg_left hz0_dist (gauge_nonneg _))
    have h1δ_pos : 0 < 1 - δ := by linarith
    have h1 : (1 - δ) * A ≤ (1 + δ) * M := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ h1δ_pos]
    linarith
  -- Lower bound on the entire sphere `S`: `((1 - 3 δ) / (1 - δ)) * M ≤ gauge K (G_of g w)`.
  set r : ℝ := ((1 - 3 * δ) / (1 - δ)) * M
  have hr_pos : 0 < r := by
    have h1 : 0 < 1 - 3 * δ := by linarith
    have h2 : 0 < 1 - δ := by linarith
    positivity
  have hS_lo : ∀ w ∈ S, r ≤ gauge (K : Set E) (G_of g w) := fun w hw => by
    obtain ⟨z, hzN, hz_dist⟩ := hcover_dist w hw
    have htri : gauge (K : Set E) (G_of g z) ≤
        gauge (K : Set E) (G_of g w) + gauge (K : Set E) (G_of g (z - w)) := by
      have h := gauge_add_le K.convex habs (G_of g w) (G_of g (z - w))
      rw [← map_add, add_sub_cancel] at h
      exact h
    have hz_lo : (1 - δ) * M ≤ gauge (K : Set E) (G_of g z) := by
      linarith [(abs_lt.mp (hnet_good z hzN)).1]
    have hdiff_le : gauge (K : Set E) (G_of g (z - w)) ≤ A * δ := by
      have hzw : ‖z - w‖ ≤ δ := by rwa [norm_sub_rev]
      exact (hA_bound (z - w)).trans (mul_le_mul_of_nonneg_left hzw (gauge_nonneg _))
    have hAδ : A * δ ≤ (((1 + δ) / (1 - δ)) * M) * δ :=
      mul_le_mul_of_nonneg_right hA_le hδ_pos.le
    have halg : (1 - δ) * M - (((1 + δ) / (1 - δ)) * M) * δ = r := by
      dsimp only [r]
      have h1δ : 1 - δ ≠ 0 := by linarith
      field_simp [h1δ]; ring
    linarith
  -- Ratio bound: `A ≤ (1 + ε) * r` for `δ = ε / 8` and `0 < ε < 1`.
  have hratio : A ≤ (1 + ε) * r := by
    refine hA_le.trans ?_
    dsimp only [r]
    have h1δ_pos : 0 < 1 - δ := by linarith
    have hcoeff : (1 + δ) / (1 - δ) ≤ (1 + ε) * ((1 - 3 * δ) / (1 - δ)) := by
      rw [mul_div_assoc', div_le_div_iff_of_pos_right h1δ_pos]
      dsimp only [δ]
      nlinarith
    have := mul_le_mul_of_nonneg_right hcoeff hM_pos.le
    simpa [mul_assoc] using this
  -- Step 4: Scale `G_of g` by `r⁻¹` so `‖w‖ ≤ gauge K (G' w) ≤ (1 + ε) * ‖w‖` for all `w`.
  let G' : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] E := r⁻¹ • G_of g
  have hG'_bounds : ∀ w : EuclideanSpace ℝ (Fin k),
      ‖w‖ ≤ gauge (K : Set E) (G' w) ∧ gauge (K : Set E) (G' w) ≤ (1 + ε) * ‖w‖ := fun w => by
    by_cases hw : w = 0
    · simp [hw]
    · have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw
      set u : EuclideanSpace ℝ (Fin k) := ‖w‖⁻¹ • w
      have huS : u ∈ S := by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hw_pos), inv_mul_cancel₀ hw_pos.ne']
      have hscale : gauge (K : Set E) (G' w) = (‖w‖ / r) * gauge (K : Set E) (G_of g u) := by
        have h1 : G' w = (‖w‖ / r) • G_of g u := by
          dsimp only [G', u]
          rw [LinearMap.smul_apply, map_smul, smul_smul]
          congr 1; field_simp [hr_pos.ne', hw_pos.ne']
        rw [h1, gauge_smul_of_nonneg (div_nonneg hw_pos.le hr_pos.le), smul_eq_mul]
      rw [hscale]
      constructor
      · calc
          ‖w‖ = (‖w‖ / r) * r := by field_simp [hr_pos.ne']
          _ ≤ (‖w‖ / r) * gauge (K : Set E) (G_of g u) :=
              mul_le_mul_of_nonneg_left (hS_lo u huS) (div_nonneg hw_pos.le hr_pos.le)
      · calc
          (‖w‖ / r) * gauge (K : Set E) (G_of g u)
            ≤ (‖w‖ / r) * A :=
              mul_le_mul_of_nonneg_left (hw0_max huS) (div_nonneg hw_pos.le hr_pos.le)
          _ ≤ (‖w‖ / r) * ((1 + ε) * r) :=
              mul_le_mul_of_nonneg_left hratio (div_nonneg hw_pos.le hr_pos.le)
          _ = (1 + ε) * ‖w‖ := by field_simp [hr_pos.ne']
  have hG'_inj : Function.Injective G' := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    have hlo := (hG'_bounds w).1
    rw [hw, gauge_zero] at hlo
    exact norm_le_zero_iff.mp hlo
  let F : Submodule ℝ E := LinearMap.range G'
  let T : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] F := LinearEquiv.ofInjective G' hG'_inj
  refine ⟨F, T, ?_, fun w => ?_⟩
  · rw [← T.finrank_eq, finrank_euclideanSpace_fin]
  · exact hG'_bounds w

/-- **Dvoretzky's Theorem (Ball, Lecture 9):**
for every origin-symmetric convex body `K : ConvexBody E` with `0 ∈ interior K` in a
finite-dimensional real inner product space `E` of dimension `d ≥ 2`, every `ε ∈ (0, 1)`, and
every target dimension `k : ℕ` satisfying
$$8192\,k\,\log(48 / \varepsilon) \le \varepsilon^2 \log d,$$
there exists a `k`-dimensional subspace `F : Submodule ℝ E` and a linear equivalence
`T : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] F` such that:
1. For every `w : EuclideanSpace ℝ (Fin k)`, `‖w‖ ≤ gauge K (T w) ≤ (1 + ε) * ‖w‖`;
2. Equivalently, letting `E_F := (F.subtype.comp T.toLinearMap) '' closedBall 0 1` be the
   corresponding `k`-dimensional ellipsoid inside `F`,
   $$(1 + \varepsilon)^{-1} E_F \subseteq K \cap F \subseteq E_F.$$ -/
theorem dvoretzky_theorem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : ConvexBody E) (hsym : IsOriginSymmetric (K : Set E))
    (h0 : (0 : E) ∈ interior (K : Set E)) (hd2 : 2 ≤ Module.finrank ℝ E)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {k : ℕ}
    (hk_bd : (8192 : ℝ) * (k : ℝ) * Real.log (48 / ε) ≤
      ε ^ 2 * Real.log (Module.finrank ℝ E : ℝ)) :
    ∃ (F : Submodule ℝ E) (T : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] F),
      Module.finrank ℝ F = k ∧
      (∀ w : EuclideanSpace ℝ (Fin k),
        ‖w‖ ≤ gauge (K : Set E) (T w : E) ∧ gauge (K : Set E) (T w : E) ≤ (1 + ε) * ‖w‖) ∧
      ((1 + ε)⁻¹ • ((F.subtype.comp T.toLinearMap) '' closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) ⊆
          (K : Set E) ∩ (F : Set E) ∧
        (K : Set E) ∩ (F : Set E) ⊆
          (F.subtype.comp T.toLinearMap) '' closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) := by
  -- Helper deriving the geometric ellipsoid inclusion from the gauge sandwich.
  have hgeom : ∀ (F : Submodule ℝ E) (T : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] F),
      (∀ w : EuclideanSpace ℝ (Fin k),
        ‖w‖ ≤ gauge (K : Set E) (T w : E) ∧ gauge (K : Set E) (T w : E) ≤ (1 + ε) * ‖w‖) →
      (1 + ε)⁻¹ • ((F.subtype.comp T.toLinearMap) '' closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) ⊆
          (K : Set E) ∩ (F : Set E) ∧
        (K : Set E) ∩ (F : Set E) ⊆
          (F.subtype.comp T.toLinearMap) '' closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 := by
    intro F T hbounds
    have h1ε_pos : 0 < 1 + ε := by linarith
    constructor
    · rintro x ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      have hTwF : (1 + ε)⁻¹ • ((T w : F) : E) ∈ (F : Set E) := F.smul_mem _ (T w).2
      refine ⟨?_, hTwF⟩
      have hg_le : gauge (K : Set E) ((1 + ε)⁻¹ • ((T w : F) : E)) ≤ 1 := by
        rw [gauge_smul_of_nonneg (inv_nonneg.mpr h1ε_pos.le), smul_eq_mul]
        have hw1 : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.mp hw
        have h2 := (hbounds w).2
        calc
          (1 + ε)⁻¹ * gauge (K : Set E) (T w : E)
            ≤ (1 + ε)⁻¹ * ((1 + ε) * ‖w‖) :=
              mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr h1ε_pos.le)
          _ = ‖w‖ := by field_simp [h1ε_pos.ne']
          _ ≤ 1 := hw1
      -- Since `K` is closed convex with `0 ∈ interior K`, `gauge K y ≤ 1 → y ∈ K`.
      have hmemK : ∀ y : E, gauge (K : Set E) y ≤ 1 → y ∈ (K : Set E) := fun y hy => by
        have hnhds : (K : Set E) ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.mp h0
        have htend : Tendsto (fun n : ℕ => ((n : ℝ) / ((n : ℝ) + 1)) • y) atTop (𝓝 y) := by
          have h1 : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (1 : ℝ)) := by
            have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) :=
              tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
            have heq : (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) = fun n : ℕ =>
              1 - ((n : ℝ) + 1)⁻¹ := by
              ext n; field_simp [show (n : ℝ) + 1 ≠ 0 by positivity]; ring
            rw [heq]; simpa using tendsto_const_nhds.sub hinv
          simpa [one_smul] using h1.smul_const y
        refine K.isClosed.mem_of_tendsto htend (Eventually.of_forall fun n => ?_)
        have hlt1 : gauge (K : Set E) (((n : ℝ) / ((n : ℝ) + 1)) • y) < 1 := by
          rw [gauge_smul_of_nonneg (by positivity), smul_eq_mul]
          have hfrac : (n : ℝ) / ((n : ℝ) + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
          calc
            (n : ℝ) / ((n : ℝ) + 1) * gauge (K : Set E) y
              ≤ (n : ℝ) / ((n : ℝ) + 1) * 1 := mul_le_mul_of_nonneg_left hy (by positivity)
            _ < 1 := by linarith
        exact interior_subset ((gauge_lt_one_iff_mem_interior K.convex hnhds).mp hlt1)
      exact hmemK _ hg_le
    · rintro x ⟨hxK, hxF⟩
      let w : EuclideanSpace ℝ (Fin k) := T.symm ⟨x, hxF⟩
      refine ⟨w, ?_, ?_⟩
      · rw [mem_closedBall_zero_iff]
        have hlo := (hbounds w).1
        have hTw : (T w : E) = x := congrArg Subtype.val (T.apply_symm_apply ⟨x, hxF⟩)
        rw [hTw] at hlo
        exact hlo.trans (gauge_le_one_of_mem hxK)
      · exact congrArg Subtype.val (T.apply_symm_apply ⟨x, hxF⟩)
  -- Handle trivial `k = 0` separately.
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · let F : Submodule ℝ E := ⊥
    let T : EuclideanSpace ℝ (Fin 0) ≃ₗ[ℝ] F :=
      { toFun := fun _ => 0
        invFun := fun _ => 0
        left_inv := fun w => by apply WithLp.ofLp_injective 2; ext i; exact Fin.elim0 i
        right_inv := fun ⟨v, hv⟩ => Subtype.ext ((Submodule.mem_bot ℝ).mp hv).symm
        map_add' := fun _ _ => by simp
        map_smul' := fun _ _ => by simp }
    have hbounds : ∀ w : EuclideanSpace ℝ (Fin 0),
        ‖w‖ ≤ gauge (K : Set E) (T w : E) ∧ gauge (K : Set E) (T w : E) ≤ (1 + ε) * ‖w‖ :=
          fun w => by
      have hw0 : w = 0 := by apply WithLp.ofLp_injective 2; ext i; exact Fin.elim0 i
      subst hw0; simp [T]
    refine ⟨F, T, ?_, hbounds, hgeom F T hbounds⟩
    simp [F]
  -- Main case `k ≥ 1`: install Borel structure, transform `K` to John's position, and apply Milman.
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  have _ : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
  obtain ⟨S, hJ⟩ := exists_linearEquiv_isJohnPosition_of_isOriginSymmetric K hsym h0
  let KJ : ConvexBody E := mapLinear S.toLinearMap.toContinuousLinearMap K
  have hKJ_coe : (KJ : Set E) = S '' (K : Set E) := by simp [KJ]
  have hKJ_sym : IsOriginSymmetric (KJ : Set E) := by
    rw [hKJ_coe]; exact isOriginSymmetric_linearMap_image S.toLinearMap hsym
  have hKJ_J : IsJohnPosition (KJ : Set E) := hKJ_coe ▸ hJ
  have hM_ge := john_position_gaussian_gauge_lower_bound KJ hKJ_sym hKJ_J hd2
  have hk_milman : (512 : ℝ) * (k : ℝ) * Real.log (48 / ε) ≤
      (ε * ∫ x : E, gauge (KJ : Set E) x ∂stdGaussian E) ^ 2 := by
    have hlogd_nn : 0 ≤ Real.log (Module.finrank ℝ E : ℝ) := by
      have : (2 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hd2
      exact Real.log_nonneg (by linarith)
    have hM_sq : (1 / 16 : ℝ) * Real.log (Module.finrank ℝ E : ℝ) ≤
        (∫ x : E, gauge (KJ : Set E) x ∂stdGaussian E) ^ 2 := by
      have h1 := pow_le_pow_left₀ (by positivity) hM_ge 2
      rw [mul_pow, Real.sq_sqrt hlogd_nn] at h1
      linarith
    have hεM : (1 / 16 : ℝ) * (ε ^ 2 * Real.log (Module.finrank ℝ E : ℝ)) ≤
        (ε * ∫ x : E, gauge (KJ : Set E) x ∂stdGaussian E) ^ 2 := by
      rw [mul_pow]
      nlinarith [sq_nonneg ε]
    linarith
  obtain ⟨FJ, TJ, hFJ_dim, hTJ_bounds⟩ :=
    milman_gaussian_dvoretzky KJ hKJ_sym hKJ_J.1 hε0 hε1 hk1 hk_milman
  -- Pull back `(FJ, TJ)` via `S.symm`.
  let F : Submodule ℝ E := FJ.map S.symm.toLinearMap
  let eF : FJ ≃ₗ[ℝ] F := S.symm.submoduleMap FJ
  let T : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] F := TJ.trans eF
  have hgauge_pull : ∀ x : E, gauge (KJ : Set E) (S x) = gauge (K : Set E) x := fun x => by
    have heq : {r : ℝ | 0 < r ∧ S x ∈ r • (KJ : Set E)} =
      {r : ℝ | 0 < r ∧ x ∈ r • (K : Set E)} := by
      ext r
      simp only [mem_ofPred_eq, hKJ_coe, mem_smul_set, mem_image, and_congr_right_iff]
      intro _
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, hyx⟩
        refine ⟨y, hy, S.injective ?_⟩
        rw [map_smul, hyx]
      · rintro ⟨y, hy, hyx⟩
        exact ⟨S y, ⟨y, hy, rfl⟩, by rw [← map_smul, hyx]⟩
    change sInf {r : ℝ | 0 < r ∧ S x ∈ r • (KJ : Set E)} =
      sInf {r : ℝ | 0 < r ∧ x ∈ r • (K : Set E)}
    rw [heq]
  have hT_bounds : ∀ w : EuclideanSpace ℝ (Fin k),
      ‖w‖ ≤ gauge (K : Set E) (T w : E) ∧ gauge (K : Set E) (T w : E) ≤ (1 + ε) * ‖w‖ := fun w => by
    have hST : S (T w : E) = (TJ w : E) := by
      change S (S.symm (TJ w : E)) = (TJ w : E)
      exact S.apply_symm_apply _
    rw [← hgauge_pull (T w : E), hST]
    exact hTJ_bounds w
  refine ⟨F, T, ?_, hT_bounds, hgeom F T hT_bounds⟩
  rw [← T.finrank_eq, finrank_euclideanSpace_fin]

end Dvoretzky

end

end ConvexGeom
