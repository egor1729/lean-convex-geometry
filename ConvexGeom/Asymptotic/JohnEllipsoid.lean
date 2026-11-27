/-
Copyright (c) 2026 Yegor Gorodzha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yegor Gorodzha
-/
module

public import ConvexGeom.Asymptotic.BanachMazur
public import ConvexGeom.Metric.Blaschke
public import ConvexGeom.Metric.Projection
public import ConvexGeom.Polytope.Combinatorial
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.LinearAlgebra.Trace

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Fritz John's Theorem, John's Decomposition, and the Banach–Mazur Compactum

This module develops the theory of maximal-volume inscribed ellipsoids, John's decomposition of the
identity, and the Banach–Mazur compactum on finite-dimensional real inner product spaces
(Ball, *An Elementary Introduction to Modern Convex Geometry*, Lectures 3–4;
Artstein-Avidan–Giannopoulos–Milman, *Asymptotic Geometric Analysis I*, Ch. 2):

1. **Rank-One Operators, Spectral Formulas & Positive-Semidefinite Ellipsoids:**
   - `rankOne u v`: the rank-one linear map `x ↦ ⟪x, v⟫ • u` (`u ⊗ v`), with trace `⟪u, v⟫`.
   - `det_eq_prod_eigenvalues`, `trace_eq_sum_eigenvalues`, `det_id_add_smul_eq_prod`, and
     first-order determinant increase `exists_det_id_add_smul_gt_one`.
   - `exists_posSemidef_ellipsoid_eq`: every linear image `T '' closedBall 0 1` equals
     `P '' closedBall 0 1` for a symmetric positive-semidefinite operator `P` with
     `det P = |det T|`.
2. **John's Decomposition of the Identity, Ball's Determinant Inequality & Dvoretzky–Rogers:**
   - `IsJohnDecomposition u c`: `‖u i‖ = 1`, `0 < c i`, and `∑ i, c i • (u i ⊗ u i) = id`.
   - `det_sum_rankOne_ge_prod`: **Ball's Determinant Inequality**
     `∏ i, a i ^ c i ≤ det (∑ i, (c i * a i) • (u i ⊗ u i))` for all `a i > 0`.
   - `dvoretzky_rogers_lemma`: existence of orthonormal vectors `e_1, …, e_m` (`m ≤ d`) with
     `√((d - j) / d) ≤ gauge K (e j)` in John's position.
3. **Maximal-Volume Inscribed Ellipsoid & John's Position (`IsJohnPosition`):**
   - `exists_max_det_inscribed_ellipsoid` (general bodies with nonempty interior) and
     `exists_max_det_centered_ellipsoid` (origin-symmetric bodies).
   - `exists_affineEquiv_isJohnPosition` and `exists_linearEquiv_isJohnPosition_of_isOriginSymmetric`.
4. **Fritz John's Theorem & Löwner's Theorem:**
   - `john_decomposition_of_john_position`: contact points `u_i ∈ sphere 0 1` with `supportFn K u_i = 1`,
     `IsJohnDecomposition u c`, and `∑ i, c i • u i = 0`.
   - `subset_finrank_smul_of_john_position` (`K ⊆ d • B₁`),
     `subset_sqrt_finrank_smul_of_john_position` (`K ⊆ √d • B₁` for origin-symmetric `K`),
     `john_theorem`, `john_theorem_symmetric`, and `loewner_theorem_symmetric`.
5. **Banach–Mazur Distance Bounds, Attainment & Compactness:**
   - `banachMazurDist_closedBall_le_sqrt_finrank` (`≤ √d`), `banachMazurDist_le_finrank` (`≤ d`),
     `affineBanachMazurDist_closedBall_le_finrank` (`≤ d`),
     `affineBanachMazurDist_le_finrank_sq` (`≤ d²`).
   - `banachMazurDist_attained`, `affineBanachMazurDist_attained`.
   - Sequential compactness of the Banach–Mazur compactum
     (`exists_subseq_banachMazurDist_tendsto_one`,
      `exists_subseq_affineBanachMazurDist_tendsto_one`).
-/

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace Pointwise ENNReal Topology

namespace ConvexGeom

public section

/-! ### 1. Rank-One Operators, Spectral Identities, and Positive-Semidefinite Ellipsoids -/

section RankOneAndSpectrum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Rank-one linear operator `u ⊗ v : E →ₗ[ℝ] E`, mapping `x ↦ ⟪x, v⟫ • u`. -/
@[expose]
noncomputable def rankOne (u v : E) : E →ₗ[ℝ] E where
  toFun x := ⟪x, v⟫ • u
  map_add' x y := by rw [inner_add_left, add_smul]
  map_smul' c x := by simp [inner_smul_left, mul_smul]

@[simp]
lemma rankOne_apply (u v x : E) : rankOne u v x = ⟪x, v⟫ • u := rfl

/-- Continuous rank-one linear operator `u ⊗ v : E →L[ℝ] E`. -/
@[expose]
noncomputable def rankOneCLM (u v : E) : E →L[ℝ] E :=
  (innerSL ℝ v).smulRight u

@[simp]
lemma rankOneCLM_apply (u v x : E) : rankOneCLM u v x = ⟪v, x⟫ • u := rfl

@[simp]
lemma rankOneCLM_toLinearMap (u v : E) :
    (rankOneCLM u v : E →ₗ[ℝ] E) = rankOne u v := by
  ext x
  simp [rankOneCLM_apply, rankOne_apply, real_inner_comm]

lemma continuous_rankOneCLM :
    Continuous (fun u : E => rankOneCLM u u) := by
  rw [Metric.continuous_iff]
  intro u ε hε
  refine ⟨min 1 (ε / (2 * (2 * ‖u‖ + 2))), lt_min one_pos (by positivity), fun v hv => ?_⟩
  rw [dist_eq_norm] at hv ⊢
  have hv1 : ‖v - u‖ < 1 := lt_of_lt_of_le hv (min_le_left _ _)
  have hv_norm : ‖v‖ ≤ ‖u‖ + 1 := by
    have := norm_sub_norm_le v u
    linarith
  have hop : ‖rankOneCLM v v - rankOneCLM u u‖ ≤ (‖v‖ + ‖u‖) * ‖v - u‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    change ‖⟪v, x⟫ • v - ⟪u, x⟫ • u‖ ≤ (‖v‖ + ‖u‖) * ‖v - u‖ * ‖x‖
    have hsplit : ⟪v, x⟫ • v - ⟪u, x⟫ • u = ⟪v - u, x⟫ • v + ⟪u, x⟫ • (v - u) := by
      rw [inner_sub_left, sub_smul, smul_sub]; abel
    rw [hsplit]
    calc
      ‖⟪v - u, x⟫ • v + ⟪u, x⟫ • (v - u)‖
        ≤ ‖⟪v - u, x⟫ • v‖ + ‖⟪u, x⟫ • (v - u)‖ := norm_add_le _ _
      _ = |⟪v - u, x⟫| * ‖v‖ + |⟪u, x⟫| * ‖v - u‖ := by simp [norm_smul]
      _ ≤ (‖v - u‖ * ‖x‖) * ‖v‖ + (‖u‖ * ‖x‖) * ‖v - u‖ :=
          add_le_add (mul_le_mul_of_nonneg_right (abs_real_inner_le_norm _ _) (norm_nonneg _))
            (mul_le_mul_of_nonneg_right (abs_real_inner_le_norm _ _) (norm_nonneg _))
      _ = (‖v‖ + ‖u‖) * ‖v - u‖ * ‖x‖ := by ring
  have hden_pos : 0 < 2 * (2 * ‖u‖ + 2) := by positivity
  have hv2 : ‖v - u‖ < ε / (2 * (2 * ‖u‖ + 2)) := lt_of_lt_of_le hv (min_le_right _ _)
  calc
    ‖rankOneCLM v v - rankOneCLM u u‖ ≤ (‖v‖ + ‖u‖) * ‖v - u‖ := hop
    _ ≤ (2 * ‖u‖ + 2) * ‖v - u‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (2 * ‖u‖ + 2) * (ε / (2 * (2 * ‖u‖ + 2))) :=
        mul_lt_mul_of_pos_left hv2 (by positivity)
    _ = ε / 2 := by field_simp [show 2 * ‖u‖ + 2 ≠ 0 by positivity]
    _ < ε := half_lt_self hε

lemma rankOne_isSymmetric (u : E) : (rankOne u u).IsSymmetric := by
  intro x y
  simp only [rankOne_apply, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  rw [real_inner_comm y u]
  ring

lemma inner_rankOne_self (u x : E) : ⟪rankOne u u x, x⟫ = ⟪x, u⟫ ^ 2 := by
  rw [rankOne_apply, inner_smul_left, RCLike.conj_to_real, real_inner_comm u x, sq]

lemma trace_rankOne [FiniteDimensional ℝ E] (u v : E) :
    LinearMap.trace ℝ E (rankOne u v) = ⟪u, v⟫ := by
  let b := stdOrthonormalBasis ℝ E
  rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis, Matrix.trace]
  have hdiag : ∀ i, LinearMap.toMatrix b.toBasis b.toBasis (rankOne u v) i i =
      ⟪b i, v⟫ * ⟪u, b i⟫ := fun i => by
    rw [LinearMap.toMatrix_apply, rankOne_apply, map_smul, Finsupp.smul_apply, smul_eq_mul,
      OrthonormalBasis.coe_toBasis]
    have hcoord : b.toBasis.repr u i = ⟪u, b i⟫ := by
      rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
        real_inner_comm]
    rw [hcoord]
  simp_rw [Matrix.diag_apply, hdiag]
  have hsum := b.sum_inner_mul_inner u v
  refine (Finset.sum_congr rfl fun i _ => ?_).trans hsum
  ring

lemma linearMap_id_eq_sum_rankOne
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E) :
    (LinearMap.id : E →ₗ[ℝ] E) = ∑ i, rankOne (b i) (b i) := by
  ext x
  simp only [LinearMap.id_apply, LinearMap.sum_apply, rankOne_apply]
  have h := b.sum_repr' x
  simpa [real_inner_comm] using h.symm

lemma sum_rankOne_isSymmetric {ι : Type*} (s : Finset ι) (u : ι → E) (c : ι → ℝ) :
    (∑ i ∈ s, c i • rankOne (u i) (u i)).IsSymmetric := by
  intro x y
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, inner_sum, sum_inner,
    inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rankOne_isSymmetric (u i) x y]

/-- Determinant of a symmetric endomorphism equals the product of its eigenvalues. -/
theorem isSymmetric_det_eq_prod_eigenvalues [FiniteDimensional ℝ E]
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) :
    LinearMap.det T = ∏ i : Fin (Module.finrank ℝ E), hT.eigenvalues rfl i := by
  rw [← LinearMap.det_toMatrix (hT.eigenvectorBasis rfl).toBasis,
    hT.toMatrix_eigenvectorBasis rfl, Matrix.det_diagonal]
  simp

/-- Trace of a symmetric endomorphism equals the sum of its eigenvalues. -/
theorem isSymmetric_trace_eq_sum_eigenvalues [FiniteDimensional ℝ E]
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) :
    LinearMap.trace ℝ E T = ∑ i : Fin (Module.finrank ℝ E), hT.eigenvalues rfl i := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (hT.eigenvectorBasis rfl).toBasis,
    hT.toMatrix_eigenvectorBasis rfl, Matrix.trace_diagonal]
  simp

/-- Determinant of `id + ε • H` for a symmetric endomorphism `H`:
`det (id + ε • H) = ∏ i, (1 + ε * λ_i)`. -/
theorem isSymmetric_det_id_add_smul [FiniteDimensional ℝ E]
    {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (ε : ℝ) :
    LinearMap.det (LinearMap.id + ε • H) =
      ∏ i : Fin (Module.finrank ℝ E), (1 + ε * hH.eigenvalues rfl i) := by
  let b := (hH.eigenvectorBasis rfl).toBasis
  rw [← LinearMap.det_toMatrix b, map_add, map_smul, LinearMap.toMatrix_id,
    hH.toMatrix_eigenvectorBasis rfl]
  have hmat : (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) +
      ε • Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues rfl) =
      Matrix.diagonal (fun i => 1 + ε * hH.eigenvalues rfl i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Matrix.diagonal]
    · simp [Matrix.diagonal, Matrix.one_apply_ne hij, hij]
  rw [hmat, Matrix.det_diagonal]

/-- First-order determinant increase: if `H` is symmetric with strictly positive trace, then
`det (id + ε • H) > 1` for all sufficiently small `ε > 0`. -/
theorem exists_det_id_add_smul_gt_one [FiniteDimensional ℝ E]
    {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (htr : 0 < LinearMap.trace ℝ E H) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      1 < LinearMap.det (LinearMap.id + ε • H) := by
  set d := Module.finrank ℝ E
  let lam : Fin d → ℝ := hH.eigenvalues rfl
  have hsum : 0 < ∑ i : Fin d, lam i := by
    rwa [← isSymmetric_trace_eq_sum_eigenvalues hH]
  let f : ℝ → ℝ := fun ε => ∏ i : Fin d, (1 + ε * lam i)
  have hf_deriv_finset : ∀ s : Finset (Fin d),
      HasDerivAt (fun ε : ℝ => ∏ i ∈ s, (1 + ε * lam i)) (∑ i ∈ s, lam i) 0 := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => simpa using hasDerivAt_const (0 : ℝ) (1 : ℝ)
    | insert a s ha ih =>
      simp_rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have ha_d : HasDerivAt (fun ε : ℝ => 1 + ε * lam a) (lam a) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (lam a)).const_add 1
      have hmul := ha_d.fun_mul ih
      simpa using hmul
  have hf_deriv : HasDerivAt f (∑ i : Fin d, lam i) 0 := hf_deriv_finset Finset.univ
  have hslope : Tendsto (fun ε : ℝ => (f ε - f 0) / ε) (𝓝[>] (0 : ℝ))
      (𝓝 (∑ i : Fin d, lam i)) := by
    have h := (hasDerivAt_iff_tendsto_slope_zero.mp hf_deriv).mono_left
      (nhdsWithin_mono (0 : ℝ) (show Ioi (0 : ℝ) ⊆ ({0} : Set ℝ)ᶜ from fun _ hx => ne_of_gt hx))
    simpa [smul_eq_mul, inv_mul_eq_div] using h
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (0 : ℝ) < (f ε - f 0) / ε :=
    hslope.eventually (Ioi_mem_nhds hsum)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε₀, hε₀, hprop⟩ := hev
  refine ⟨ε₀, hε₀, fun ε hε0 hεlt => ?_⟩
  have hdist : dist ε 0 < ε₀ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε0]
    exact hεlt
  have hpos : 0 < (f ε - f 0) / ε := hprop hdist hε0
  have hf0 : f 0 = 1 := by simp [f]
  have hlt : 1 < f ε := by
    rw [hf0, div_pos_iff_of_pos_right hε0] at hpos
    linarith
  rwa [isSymmetric_det_id_add_smul hH ε]

/-- **Positive-semidefinite canonical form of an ellipsoid:**
for any linear map `T : E →ₗ[ℝ] E` in finite dimensions, there exists a symmetric
positive-semidefinite operator `P : E →ₗ[ℝ] E` such that
`P '' closedBall 0 1 = T '' closedBall 0 1` and `det P = |det T|`. -/
theorem exists_posSemidef_ellipsoid_eq [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) :
    ∃ P : E →ₗ[ℝ] E, P.IsSymmetric ∧ (∀ x : E, 0 ≤ ⟪P x, x⟫) ∧
      P '' closedBall (0 : E) 1 = T '' closedBall (0 : E) 1 ∧
      LinearMap.det P = |LinearMap.det T| := by
  let S : E →ₗ[ℝ] E := T.comp (LinearMap.adjoint T)
  have hS_symm : S.IsSymmetric := by
    intro x y
    change ⟪T (LinearMap.adjoint T x), y⟫ = ⟪x, T (LinearMap.adjoint T y)⟫
    rw [← LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_left]
  have hS_nn : ∀ x : E, 0 ≤ ⟪S x, x⟫ := fun x => by
    change 0 ≤ ⟪T (LinearMap.adjoint T x), x⟫
    rw [← LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
    exact sq_nonneg _
  let b := hS_symm.eigenvectorBasis rfl
  let lam := hS_symm.eigenvalues rfl
  have hlam_nn : ∀ i, 0 ≤ lam i := fun i => by
    have h := hS_nn (b i)
    rw [hS_symm.apply_eigenvectorBasis rfl i, inner_smul_left, RCLike.conj_to_real,
      real_inner_self_eq_norm_sq, b.orthonormal.1 i, one_pow, mul_one] at h
    exact h
  let P : E →ₗ[ℝ] E := Matrix.toLin b.toBasis b.toBasis (Matrix.diagonal (fun i => Real.sqrt (lam i)))
  have hP_apply : ∀ i, P (b i) = Real.sqrt (lam i) • b i := fun i => by
    change Matrix.toLin b.toBasis b.toBasis (Matrix.diagonal (fun i => Real.sqrt (lam i))) (b.toBasis i) = _
    rw [Matrix.toLin_self]
    simp [Matrix.diagonal_apply]
  have hP_symm : P.IsSymmetric := by
    intro x y
    have hinner : ∀ u v : E, ⟪P u, v⟫ = ∑ i, Real.sqrt (lam i) * ⟪b i, u⟫ * ⟪b i, v⟫ := fun u v => by
      have hu := (b.sum_repr' u).symm
      have hv := (b.sum_repr' v).symm
      conv_lhs => rw [hu, hv]
      simp only [map_sum, map_smul, hP_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
        RCLike.conj_to_real]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i]
      · rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i, one_pow, mul_one]; ring
      · intro j _ hji
        rw [b.orthonormal.2 hji, mul_zero, mul_zero]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [hinner x y, real_inner_comm (P y) x, hinner y x]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hP_nn : ∀ x : E, 0 ≤ ⟪P x, x⟫ := fun x => by
    have hinner : ⟪P x, x⟫ = ∑ i, Real.sqrt (lam i) * ⟪b i, x⟫ ^ 2 := by
      have hx := (b.sum_repr' x).symm
      conv_lhs => rw [hx]
      simp only [map_sum, map_smul, hP_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
        RCLike.conj_to_real]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i]
      · rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i, one_pow, mul_one]; ring
      · intro j _ hji
        rw [b.orthonormal.2 hji, mul_zero, mul_zero]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [hinner]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
  have hP_sq : P.comp P = S := by
    apply b.toBasis.ext
    intro i
    change P (P (b i)) = S (b i)
    rw [hP_apply, map_smul, hP_apply, smul_smul, Real.mul_self_sqrt (hlam_nn i),
      hS_symm.apply_eigenvectorBasis rfl i]
    rfl
  have hnorm_eq : ∀ y : E, ‖P y‖ = ‖LinearMap.adjoint T y‖ := fun y => by
    have hsq : ‖P y‖ ^ 2 = ‖LinearMap.adjoint T y‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← hP_symm (P y) y]
      change ⟪(P.comp P) y, y⟫ = _
      rw [hP_sq]
      change ⟪T (LinearMap.adjoint T y), y⟫ = _
      rw [← LinearMap.adjoint_inner_right]
    nlinarith [norm_nonneg (P y), norm_nonneg (LinearMap.adjoint T y)]
  have himg_eq : P '' closedBall (0 : E) 1 = T '' closedBall (0 : E) 1 := by
    let KP : ConvexBody E := mapLinear P.toContinuousLinearMap (bodyClosedBall (0 : E) zero_le_one)
    let KT : ConvexBody E := mapLinear T.toContinuousLinearMap (bodyClosedBall (0 : E) zero_le_one)
    have hbody : KP = KT := by
      apply supportFn_injective
      ext y
      have hsup : ∀ A : E →ₗ[ℝ] E,
          supportFn (mapLinear A.toContinuousLinearMap (bodyClosedBall (0 : E) zero_le_one)) y =
            ‖LinearMap.adjoint A y‖ := fun A => by
        apply le_antisymm
        · rw [supportFn_le_iff]
          intro z hz
          rw [← SetLike.mem_coe, coe_mapLinear, coe_bodyClosedBall] at hz
          rcases hz with ⟨x, hx, rfl⟩
          have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
          change ⟪A x, y⟫ ≤ ‖LinearMap.adjoint A y‖
          rw [← LinearMap.adjoint_inner_right]
          exact (real_inner_le_norm x _).trans (by nlinarith [norm_nonneg (LinearMap.adjoint A y)])
        · by_cases hy : LinearMap.adjoint A y = 0
          · rw [hy, norm_zero]
            have h0 : (0 : E) ∈ mapLinear A.toContinuousLinearMap
                (bodyClosedBall (0 : E) zero_le_one) := by
              rw [← SetLike.mem_coe, coe_mapLinear, coe_bodyClosedBall]
              exact ⟨0, mem_closedBall_self zero_le_one, map_zero A⟩
            simpa using inner_le_supportFn h0 y
          · have hpos : 0 < ‖LinearMap.adjoint A y‖ := norm_pos_iff.mpr hy
            let x : E := ‖LinearMap.adjoint A y‖⁻¹ • LinearMap.adjoint A y
            have hx : x ∈ closedBall (0 : E) 1 := by
              rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
                abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
            have hmem : A x ∈ mapLinear A.toContinuousLinearMap
                (bodyClosedBall (0 : E) zero_le_one) := by
              rw [← SetLike.mem_coe, coe_mapLinear, coe_bodyClosedBall]
              exact ⟨x, hx, rfl⟩
            have hval : ⟪A x, y⟫ = ‖LinearMap.adjoint A y‖ := by
              rw [← LinearMap.adjoint_inner_right]
              dsimp only [x]
              rw [inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq]
              field_simp [hpos.ne']
            rw [← hval]
            exact inner_le_supportFn hmem y
      have hPadj : LinearMap.adjoint P = P := hP_symm.adjoint_eq
      rw [hsup P, hsup T, hPadj, hnorm_eq y]
    simpa [KP, KT, coe_mapLinear, coe_bodyClosedBall] using congrArg SetLike.coe hbody
  have hdet_P_nn : 0 ≤ LinearMap.det P := by
    rw [← LinearMap.det_toMatrix b.toBasis]
    simp only [P, LinearMap.toMatrix_toLin, Matrix.det_diagonal]
    exact Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _
  have hdet_sq : LinearMap.det P ^ 2 = LinearMap.det T ^ 2 := by
    rw [sq, ← LinearMap.det_comp, hP_sq]
    change LinearMap.det (T.comp (LinearMap.adjoint T)) = _
    rw [LinearMap.det_comp, det_adjoint_eq_det, sq]
  have hdet_eq : LinearMap.det P = |LinearMap.det T| := by
    nlinarith [sq_abs (LinearMap.det T), abs_nonneg (LinearMap.det T)]
  exact ⟨P, hP_symm, hP_nn, himg_eq, hdet_eq⟩

/-- The determinant is continuous on `E →L[ℝ] E` in finite dimensions. -/
lemma continuous_det_clm [FiniteDimensional ℝ E] :
    Continuous (fun T : E →L[ℝ] E => LinearMap.det (T : E →ₗ[ℝ] E)) := by
  let b := stdOrthonormalBasis ℝ E
  have heq : (fun T : E →L[ℝ] E => LinearMap.det (T : E →ₗ[ℝ] E)) =
      fun T => Matrix.det (fun i j => ⟪T (b j), b i⟫) := by
    ext T
    rw [← LinearMap.det_toMatrix b.toBasis]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply, real_inner_comm]
    rfl
  rw [heq]
  refine Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j => ?_)
  exact ((ContinuousLinearMap.apply ℝ E (b j)).continuous).inner continuous_const

end RankOneAndSpectrum

/-! ### 2. John's Decomposition of the Identity, Ball's Determinant Inequality & Dvoretzky–Rogers -/

section JohnDecomposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **John's decomposition of the identity:** a finite family of unit vectors `u : ι → E` and
strictly positive weights `c : ι → ℝ` satisfying `∑ i, c i • (u i ⊗ u i) = id`. -/
@[expose]
def IsJohnDecomposition {ι : Type*} [Fintype ι] (u : ι → E) (c : ι → ℝ) : Prop :=
  (∀ i, ‖u i‖ = 1) ∧ (∀ i, 0 < c i) ∧
    ∑ i, c i • rankOne (u i) (u i) = (LinearMap.id : E →ₗ[ℝ] E)

namespace IsJohnDecomposition

variable {ι : Type*} [Fintype ι] {u : ι → E} {c : ι → ℝ}

lemma norm_eq_one (h : IsJohnDecomposition u c) (i : ι) : ‖u i‖ = 1 := h.1 i

lemma weight_pos (h : IsJohnDecomposition u c) (i : ι) : 0 < c i := h.2.1 i

lemma sum_rankOne (h : IsJohnDecomposition u c) :
    ∑ i, c i • rankOne (u i) (u i) = (LinearMap.id : E →ₗ[ℝ] E) := h.2.2

lemma sum_smul_inner (h : IsJohnDecomposition u c) (x : E) :
    ∑ i, (c i * ⟪x, u i⟫) • u i = x := by
  have hx := congrArg (fun f : E →ₗ[ℝ] E => f x) h.sum_rankOne
  simpa [LinearMap.sum_apply, LinearMap.smul_apply, rankOne_apply, smul_smul] using hx

lemma inner_eq_sum (h : IsJohnDecomposition u c) (x y : E) :
    ⟪x, y⟫ = ∑ i, c i * ⟪x, u i⟫ * ⟪y, u i⟫ := by
  conv_lhs => rw [← h.sum_smul_inner x]
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, RCLike.conj_to_real, real_inner_comm (u i) y]

lemma norm_sq_eq_sum (h : IsJohnDecomposition u c) (x : E) :
    ‖x‖ ^ 2 = ∑ i, c i * ⟪x, u i⟫ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, h.inner_eq_sum x x]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- The weights of a John decomposition sum to `finrank ℝ E`. -/
theorem sum_weights [FiniteDimensional ℝ E] (h : IsJohnDecomposition u c) :
    ∑ i, c i = (Module.finrank ℝ E : ℝ) := by
  have htr := congrArg (LinearMap.trace ℝ E) h.sum_rankOne
  rw [map_sum, LinearMap.trace_id] at htr
  have hterm : ∀ i, LinearMap.trace ℝ E (c i • rankOne (u i) (u i)) = c i := fun i => by
    rw [map_smul, smul_eq_mul, trace_rankOne, real_inner_self_eq_norm_sq, h.norm_eq_one i,
      one_pow, mul_one]
  simp_rw [hterm] at htr
  simpa using htr

/-- Dual Bessel inequality for a John decomposition:
`‖∑ i, (c i * s i) • u i‖² ≤ ∑ i, c i * s i ^ 2` for every scalar family `s : ι → ℝ`. -/
theorem norm_sum_smul_sq_le (h : IsJohnDecomposition u c) (s : ι → ℝ) :
    ‖∑ i, (c i * s i) • u i‖ ^ 2 ≤ ∑ i, c i * s i ^ 2 := by
  set w : E := ∑ i, (c i * s i) • u i
  have hinner : ‖w‖ ^ 2 = ∑ i, (Real.sqrt (c i) * s i) * (Real.sqrt (c i) * ⟪w, u i⟫) := by
    have h1 : ‖w‖ ^ 2 = ⟪∑ i, (c i * s i) • u i, w⟫ := by
      rw [← real_inner_self_eq_norm_sq]
    rw [h1, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, RCLike.conj_to_real, real_inner_comm w (u i)]
    have hsq : Real.sqrt (c i) * Real.sqrt (c i) = c i := Real.mul_self_sqrt (h.weight_pos i).le
    calc
      c i * s i * ⟪w, u i⟫ = (Real.sqrt (c i) * Real.sqrt (c i)) * s i * ⟪w, u i⟫ := by rw [hsq]
      _ = (Real.sqrt (c i) * s i) * (Real.sqrt (c i) * ⟪w, u i⟫) := by ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (c i) * s i) (fun i => Real.sqrt (c i) * ⟪w, u i⟫)
  have h1 : ∑ i, (Real.sqrt (c i) * s i) ^ 2 = ∑ i, c i * s i ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [mul_pow, Real.sq_sqrt (h.weight_pos i).le]
  have h2 : ∑ i, (Real.sqrt (c i) * ⟪w, u i⟫) ^ 2 = ‖w‖ ^ 2 := by
    rw [h.norm_sq_eq_sum w]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_pow, Real.sq_sqrt (h.weight_pos i).le]
  rw [← hinner, h1, h2] at hcs
  by_cases hw : ‖w‖ = 0
  · rw [hw, zero_pow two_ne_zero]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (h.weight_pos i).le (sq_nonneg _)
  · have hw_pos : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw))
    have hcs' : (‖w‖ ^ 2) * (‖w‖ ^ 2) ≤ (∑ i, c i * s i ^ 2) * (‖w‖ ^ 2) := by
      simpa [sq] using hcs
    exact le_of_mul_le_mul_right hcs' hw_pos

/-- **Ball's Determinant Inequality (Ball, Lecture 6):**
for any John decomposition `∑ i, c i • (u i ⊗ u i) = id` and positive weights `a : ι → ℝ`:
$$\prod_{i} a_i^{c_i} \le \det\!\left(\sum_{i} c_i a_i (u_i \otimes u_i)\right).$$ -/
theorem det_sum_rankOne_ge_prod [FiniteDimensional ℝ E]
    (h : IsJohnDecomposition u c) {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    ∏ i, a i ^ c i ≤
      LinearMap.det (∑ i, (c i * a i) • rankOne (u i) (u i)) := by
  let A : E →ₗ[ℝ] E := ∑ i, (c i * a i) • rankOne (u i) (u i)
  have hA_symm : A.IsSymmetric := sum_rankOne_isSymmetric Finset.univ u (fun i => c i * a i)
  let b := hA_symm.eigenvectorBasis rfl
  let lam := hA_symm.eigenvalues rfl
  let w : Fin (Module.finrank ℝ E) → ι → ℝ := fun k i => c i * ⟪b k, u i⟫ ^ 2
  have hw_nn : ∀ k i, 0 ≤ w k i := fun k i => mul_nonneg (h.weight_pos i).le (sq_nonneg _)
  have hw_sum_i : ∀ k, ∑ i, w k i = 1 := fun k => by
    dsimp only [w]
    rw [← h.norm_sq_eq_sum (b k), b.orthonormal.1 k, one_pow]
  have hw_sum_k : ∀ i, ∑ k, w k i = c i := fun i => by
    dsimp only [w]
    rw [← Finset.mul_sum]
    have hnorm := b.sum_sq_inner_right (u i)
    rw [h.norm_eq_one i, one_pow] at hnorm
    rw [hnorm, mul_one]
  have hlam_eq : ∀ k, lam k = ∑ i, w k i * a i := fun k => by
    have heig : ⟪A (b k), b k⟫ = lam k := by
      rw [hA_symm.apply_eigenvectorBasis rfl k, inner_smul_left, RCLike.conj_to_real,
        real_inner_self_eq_norm_sq, b.orthonormal.1 k, one_pow, mul_one]
      rfl
    rw [← heig]
    simp only [A, LinearMap.sum_apply, LinearMap.smul_apply, rankOne_apply, sum_inner,
      inner_smul_left, RCLike.conj_to_real]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only [w]
    rw [real_inner_comm (u i) (b k)]
    ring
  have hlam_ge : ∀ k, ∏ i, a i ^ w k i ≤ lam k := fun k => by
    rw [hlam_eq k]
    exact Real.geom_mean_le_arith_mean_weighted Finset.univ (w k) a
      (fun i _ => hw_nn k i) (hw_sum_i k) (fun i _ => (ha i).le)
  have hprod_nonneg : ∀ k, 0 ≤ ∏ i, a i ^ w k i := fun k =>
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (ha i).le _
  rw [isSymmetric_det_eq_prod_eigenvalues hA_symm]
  calc
    ∏ i, a i ^ c i = ∏ i, a i ^ (∑ k, w k i) := by
        refine Finset.prod_congr rfl fun i _ => by rw [hw_sum_k i]
    _ = ∏ i, ∏ k, a i ^ w k i := by
        refine Finset.prod_congr rfl fun i _ => Real.rpow_sum_of_pos (ha i) _ _
    _ = ∏ k, ∏ i, a i ^ w k i := Finset.prod_comm
    _ ≤ ∏ k, lam k := by
        have hstep : ∀ s : Finset (Fin (Module.finrank ℝ E)),
            ∏ k ∈ s, ∏ i, a i ^ w k i ≤ ∏ k ∈ s, lam k := by
          intro s
          classical
          induction s using Finset.induction_on with
          | empty => simp
          | insert k s hk ih =>
            rw [Finset.prod_insert hk, Finset.prod_insert hk]
            exact mul_le_mul (hlam_ge k) ih
              (Finset.prod_nonneg fun j _ => hprod_nonneg j)
              ((hprod_nonneg k).trans (hlam_ge k))
        exact hstep Finset.univ

/-- **Projection lower bound (Dvoretzky–Rogers step):**
for any subspace `H : Submodule ℝ E`, some vector `u i` of a John decomposition has
squared orthogonal projection onto `H` at least `finrank H / finrank E`. -/
theorem exists_sq_norm_proj_ge [FiniteDimensional ℝ E] [Nontrivial E]
    (h : IsJohnDecomposition u c) (H : Submodule ℝ E) :
    ∃ i : ι, (Module.finrank ℝ H : ℝ) / (Module.finrank ℝ E : ℝ) ≤
      ‖H.orthogonalProjectionOnto (u i)‖ ^ 2 := by
  set d := Module.finrank ℝ E
  set r := Module.finrank ℝ H
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr Module.finrank_pos
  have hsum : ∑ i, c i * ‖H.orthogonalProjectionOnto (u i)‖ ^ 2 = (r : ℝ) := by
    let bH := stdOrthonormalBasis ℝ H
    have hproj_sq : ∀ x : E,
        ‖H.orthogonalProjectionOnto x‖ ^ 2 = ∑ j : Fin r, ⟪x, (bH j : E)⟫ ^ 2 := fun x => by
      have h1 := bH.sum_sq_inner_right (H.orthogonalProjectionOnto x)
      rw [← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h2 := H.inner_orthogonalProjectionOnto_eq_of_mem_left (bH j) x
      rw [h2, real_inner_comm]
    simp_rw [hproj_sq, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hinner_j : ∀ j : Fin r, ∑ i, c i * ⟪u i, (bH j : E)⟫ ^ 2 = 1 := fun j => by
      have hnorm := h.norm_sq_eq_sum (bH j : E)
      have hb1 : ‖(bH j : E)‖ = 1 := bH.orthonormal.1 j
      rw [hb1, one_pow] at hnorm
      have hcomm : ∑ i, c i * ⟪u i, (bH j : E)⟫ ^ 2 = ∑ i, c i * ⟪(bH j : E), u i⟫ ^ 2 :=
        Finset.sum_congr rfl fun i _ => by rw [real_inner_comm]
      rw [hcomm, ← hnorm]
    simp_rw [hinner_j]
    simp
  by_contra hnot
  push Not at hnot
  have hne : Nonempty ι := by
    by_contra hemp
    have : IsEmpty ι := not_nonempty_iff.mp hemp
    have hsw := h.sum_weights
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsw
    linarith
  have hlt : ∑ i, c i * ‖H.orthogonalProjectionOnto (u i)‖ ^ 2 <
      ∑ i, c i * ((r : ℝ) / (d : ℝ)) := by
    refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => ?_
    exact mul_lt_mul_of_pos_left (hnot i) (h.weight_pos i)
  rw [← Finset.sum_mul, h.sum_weights, mul_div_cancel₀ _ hd_pos.ne'] at hlt
  linarith

end IsJohnDecomposition

end JohnDecomposition

/-! ### 3. Maximal-Volume Inscribed Ellipsoid and John's Position -/

section JohnPosition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A set `K ⊆ E` is in **John's position** if the unit closed ball `closedBall 0 1` is inscribed
in `K` and maximizes `|det T|` among all affine ellipsoids `c + T(closedBall 0 1) ⊆ K`. -/
@[expose]
def IsJohnPosition (K : Set E) : Prop :=
  closedBall (0 : E) 1 ⊆ K ∧
    ∀ (T : E →ₗ[ℝ] E) (c : E),
      (fun x => T x + c) '' closedBall (0 : E) 1 ⊆ K → |LinearMap.det T| ≤ 1

/-- **Existence of a maximal-volume inscribed ellipsoid (John ellipsoid):**
every convex body `K : ConvexBody E` with nonempty interior admits an invertible linear map
`T : E ≃ₗ[ℝ] E` and center `c ∈ E` such that `c + T(B₁) ⊆ K` maximizes `|det S|` among all
inscribed affine ellipsoids `b + S(B₁) ⊆ K`. -/
theorem exists_max_det_inscribed_ellipsoid [FiniteDimensional ℝ E]
    (K : ConvexBody E) (hint : (interior (K : Set E)).Nonempty) :
    ∃ (T : E ≃ₗ[ℝ] E) (c : E),
      (fun x => T x + c) '' closedBall (0 : E) 1 ⊆ (K : Set E) ∧
      ∀ (S : E →ₗ[ℝ] E) (b : E),
        (fun x => S x + b) '' closedBall (0 : E) 1 ⊆ (K : Set E) →
          |LinearMap.det S| ≤ |LinearMap.det (T : E →ₗ[ℝ] E)| := by
  let F : Set ((E →L[ℝ] E) × E) :=
    {p | (fun x => p.1 x + p.2) '' closedBall (0 : E) 1 ⊆ (K : Set E)}
  -- Compactness of `F`: closed and bounded in finite-dimensional `(E →L[ℝ] E) × E`.
  have hF_closed : IsClosed F := by
    have heq : F = ⋂ x ∈ closedBall (0 : E) 1, {p : (E →L[ℝ] E) × E | p.1 x + p.2 ∈ (K : Set E)} := by
      ext p
      simp [F, Set.subset_def]
    rw [heq]
    refine isClosed_biInter fun x _ => K.isClosed.preimage ?_
    exact (((ContinuousLinearMap.apply ℝ E x).continuous.comp continuous_fst).add continuous_snd)
  obtain ⟨R, hKR⟩ := K.isBounded.subset_closedBall (0 : E)
  have hR_nn : 0 ≤ R := by
    obtain ⟨x₀, hx₀⟩ := K.nonempty
    exact (norm_nonneg x₀).trans (mem_closedBall_zero_iff.mp (hKR hx₀))
  have hF_bdd : Bornology.IsBounded F := by
    refine (Metric.isBounded_iff_subset_closedBall (0 : (E →L[ℝ] E) × E)).mpr ⟨2 * R, fun p hp => ?_⟩
    have hc_mem : p.2 ∈ (K : Set E) := hp ⟨0, mem_closedBall_self zero_le_one, by simp⟩
    have hc_norm : ‖p.2‖ ≤ R := mem_closedBall_zero_iff.mp (hKR hc_mem)
    have hop : ‖p.1‖ ≤ 2 * R := by
      refine ContinuousLinearMap.opNorm_le_bound p.1 (by linarith) fun x => ?_
      by_cases hx : x = 0
      · simp [hx]
      · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
        let u : E := ‖x‖⁻¹ • x
        have hu : u ∈ closedBall (0 : E) 1 := by
          rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hxn), inv_mul_cancel₀ hxn.ne']
        have hmem : p.1 u + p.2 ∈ (K : Set E) := hp ⟨u, hu, rfl⟩
        have hnorm1 : ‖p.1 u + p.2‖ ≤ R := mem_closedBall_zero_iff.mp (hKR hmem)
        have hnormu : ‖p.1 u‖ ≤ 2 * R := by
          calc
            ‖p.1 u‖ = ‖(p.1 u + p.2) - p.2‖ := by congr 1; abel
            _ ≤ ‖p.1 u + p.2‖ + ‖p.2‖ := norm_sub_le _ _
            _ ≤ R + R := add_le_add hnorm1 hc_norm
            _ = 2 * R := by ring
        have hscale : ‖p.1 u‖ = ‖x‖⁻¹ * ‖p.1 x‖ := by
          dsimp only [u]
          rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxn)]
        rw [hscale, inv_mul_le_iff₀ hxn] at hnormu
        linarith
    rw [mem_closedBall_zero_iff, Prod.norm_def]
    exact max_le hop (by linarith)
  have hF_compact : IsCompact F := Metric.isCompact_of_isClosed_isBounded hF_closed hF_bdd
  -- Nonemptiness with strictly positive determinant using `hint`.
  obtain ⟨c₀, hc₀⟩ := hint
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hc₀)
  let r' := r / 2
  have hr' : 0 < r' := half_pos hr
  have hp₀_mem : ((r' • ContinuousLinearMap.id ℝ E), c₀) ∈ F := by
    rintro _ ⟨x, hx, rfl⟩
    apply hball
    rw [mem_ball, dist_eq_norm]
    have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    have hsub : (r' • ContinuousLinearMap.id ℝ E) x + c₀ - c₀ = r' • x := by simp
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hr']
    dsimp only [r']
    nlinarith
  have hF_ne : F.Nonempty := ⟨_, hp₀_mem⟩
  let obj : (E →L[ℝ] E) × E → ℝ := fun p => |LinearMap.det (p.1 : E →ₗ[ℝ] E)|
  have hobj_cont : Continuous obj := continuous_abs.comp (continuous_det_clm.comp continuous_fst)
  obtain ⟨⟨T₀, c⟩, hp_mem, hp_max⟩ := hF_compact.exists_isMaxOn hF_ne hobj_cont.continuousOn
  have hdet_pos : 0 < |LinearMap.det (T₀ : E →ₗ[ℝ] E)| := by
    have h0 : |LinearMap.det ((r' • ContinuousLinearMap.id ℝ E : E →L[ℝ] E) : E →ₗ[ℝ] E)| ≤
        |LinearMap.det (T₀ : E →ₗ[ℝ] E)| := hp_max hp₀_mem
    have hval : LinearMap.det ((r' • ContinuousLinearMap.id ℝ E : E →L[ℝ] E) : E →ₗ[ℝ] E) =
        r' ^ Module.finrank ℝ E := by
      change LinearMap.det (r' • (LinearMap.id : E →ₗ[ℝ] E)) = _
      rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
    rw [hval, abs_of_pos (pow_pos hr' _)] at h0
    exact lt_of_lt_of_le (pow_pos hr' _) h0
  have hdet_ne : LinearMap.det (T₀ : E →ₗ[ℝ] E) ≠ 0 := abs_pos.mp hdet_pos
  let T : E ≃ₗ[ℝ] E := LinearMap.equivOfDetNeZero (T₀ : E →ₗ[ℝ] E) hdet_ne
  refine ⟨T, c, hp_mem, fun S b hSb => ?_⟩
  have hSb' : (S.toContinuousLinearMap, b) ∈ F := hSb
  exact hp_max hSb'

/-- For an origin-symmetric convex body `K` with `0 ∈ interior K`, there exists a **centered**
maximal-volume inscribed ellipsoid `T(B₁) ⊆ K` which maximizes `|det S|` over ALL (including
translated!) inscribed affine ellipsoids `b + S(B₁) ⊆ K`. -/
theorem exists_max_det_centered_ellipsoid [FiniteDimensional ℝ E]
    (K : ConvexBody E) (hsym : IsOriginSymmetric (K : Set E))
    (h0 : (0 : E) ∈ interior (K : Set E)) :
    ∃ T : E ≃ₗ[ℝ] E,
      ellipsoid T ⊆ (K : Set E) ∧
      ∀ (S : E →ₗ[ℝ] E) (b : E),
        (fun x => S x + b) '' closedBall (0 : E) 1 ⊆ (K : Set E) →
          |LinearMap.det S| ≤ |LinearMap.det (T : E →ₗ[ℝ] E)| := by
  obtain ⟨T, c, hTc, hmax⟩ := exists_max_det_inscribed_ellipsoid K ⟨0, h0⟩
  refine ⟨T, ?_, hmax⟩
  rintro _ ⟨x, hx, rfl⟩
  have h1 : T x + c ∈ (K : Set E) := hTc ⟨x, hx, rfl⟩
  have hnegx : -x ∈ closedBall (0 : E) 1 := isOriginSymmetric_closedBall 1 x hx
  have h2 : T (-x) + c ∈ (K : Set E) := hTc ⟨-x, hnegx, rfl⟩
  have h3 : T x - c ∈ (K : Set E) := by
    have := hsym _ h2
    rw [map_neg] at this
    simpa [sub_eq_add_neg, neg_add, add_comm] using this
  have hmid := K.convex h1 h3 (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have heq : (1 / 2 : ℝ) • (T x + c) + (1 / 2 : ℝ) • (T x - c) = T x := by module
  rwa [heq] at hmid

/-- Every convex body `K` with nonempty interior has an affine image `A '' K` in John's position. -/
theorem exists_affineEquiv_isJohnPosition [FiniteDimensional ℝ E]
    (K : ConvexBody E) (hint : (interior (K : Set E)).Nonempty) :
    ∃ A : E ≃ᵃ[ℝ] E, IsJohnPosition (A '' (K : Set E)) := by
  obtain ⟨T, c, hTc, hmax⟩ := exists_max_det_inscribed_ellipsoid K hint
  let B : E ≃ᵃ[ℝ] E := (T.toAffineEquiv).trans (AffineEquiv.vaddConst ℝ c)
  let A : E ≃ᵃ[ℝ] E := B.symm
  have hB_apply : ∀ x : E, B x = T x + c := fun x => by
    simp [B, vadd_eq_add, add_comm]
  refine ⟨A, ?_, ?_⟩
  · intro x hx
    refine ⟨B x, ?_, B.symm_apply_apply x⟩
    rw [hB_apply]
    exact hTc ⟨x, hx, rfl⟩
  · intro S b hSb
    have hcomp : (fun x => (T.toLinearMap.comp S) x + (T b + c)) '' closedBall (0 : E) 1 ⊆
        (K : Set E) := by
      rintro _ ⟨x, hx, rfl⟩
      have hmem : S x + b ∈ A '' (K : Set E) := hSb ⟨x, hx, rfl⟩
      rcases hmem with ⟨k, hk, hAk⟩
      have hk_eq : k = B (S x + b) := by
        have := congrArg B hAk
        simpa [A] using this
      rw [hB_apply, map_add] at hk_eq
      change T (S x) + (T b + c) ∈ (K : Set E)
      rw [← add_assoc, ← hk_eq]
      exact hk
    have hle := hmax (T.toLinearMap.comp S) (T b + c) hcomp
    rw [LinearMap.det_comp, abs_mul] at hle
    have hTpos : 0 < |LinearMap.det (T : E →ₗ[ℝ] E)| := abs_pos.mpr T.isUnit_det'.ne_zero
    exact le_of_mul_le_mul_left (by simpa [mul_one] using hle) hTpos

/-- Every origin-symmetric convex body `K` with `0 ∈ interior K` has a linear image `T '' K`
in John's position (which remains origin-symmetric). -/
theorem exists_linearEquiv_isJohnPosition_of_isOriginSymmetric [FiniteDimensional ℝ E]
    (K : ConvexBody E) (hsym : IsOriginSymmetric (K : Set E))
    (h0 : (0 : E) ∈ interior (K : Set E)) :
    ∃ T : E ≃ₗ[ℝ] E, IsJohnPosition (T '' (K : Set E)) := by
  obtain ⟨S, hSK, hmax⟩ := exists_max_det_centered_ellipsoid K hsym h0
  refine ⟨S.symm, ?_, ?_⟩
  · intro x hx
    exact ⟨S x, hSK ⟨x, hx, rfl⟩, S.symm_apply_apply x⟩
  · intro U b hUb
    have hcomp : (fun x => (S.toLinearMap.comp U) x + S b) '' closedBall (0 : E) 1 ⊆ (K : Set E) := by
      rintro _ ⟨x, hx, rfl⟩
      rcases hUb ⟨x, hx, rfl⟩ with ⟨k, hk, hSk⟩
      have hk_eq : k = S (U x + b) := by
        have := congrArg S hSk
        simpa using this
      rw [map_add] at hk_eq
      change S (U x) + S b ∈ (K : Set E)
      rwa [← hk_eq]
    have hle := hmax (S.toLinearMap.comp U) (S b) hcomp
    rw [LinearMap.det_comp, abs_mul] at hle
    have hSpos : 0 < |LinearMap.det (S : E →ₗ[ℝ] E)| := abs_pos.mpr S.isUnit_det'.ne_zero
    exact le_of_mul_le_mul_left (by simpa [mul_one] using hle) hSpos

end JohnPosition

/-! ### 4. Fritz John's Theorem and Löwner's Theorem -/

section FritzJohn

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper: every continuous linear functional `f₁ : (E →L[ℝ] E) →L[ℝ] ℝ` is represented on
rank-one operators `u ⊗ u` and on `id` by a symmetric operator `H : E →ₗ[ℝ] E`:
`f₁ (u ⊗ u) = ⟪H u, u⟫` and `f₁ id = trace H`. -/
private lemma exists_symmetric_representing_clm [FiniteDimensional ℝ E]
    (f₁ : (E →L[ℝ] E) →L[ℝ] ℝ) :
    ∃ H : E →ₗ[ℝ] E, H.IsSymmetric ∧
      (∀ u : E, f₁ (rankOneCLM u u) = ⟪H u, u⟫) ∧
      f₁ (ContinuousLinearMap.id ℝ E) = LinearMap.trace ℝ E H := by
  let b := stdOrthonormalBasis ℝ E
  let a : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => (f₁ (rankOneCLM (b i) (b j)) + f₁ (rankOneCLM (b j) (b i))) / 2
  let H : E →ₗ[ℝ] E :=
    Matrix.toLin b.toBasis b.toBasis (Matrix.of a)
  have hH_entry : ∀ i j, ⟪H (b j), b i⟫ = a i j := fun i j => by
    change ⟪Matrix.toLin b.toBasis b.toBasis (Matrix.of a) (b.toBasis j), b i⟫ = a i j
    rw [Matrix.toLin_self, sum_inner]
    rw [Finset.sum_eq_single i]
    · rw [inner_smul_left, RCLike.conj_to_real, OrthonormalBasis.coe_toBasis,
        real_inner_self_eq_norm_sq, b.orthonormal.1 i, one_pow, mul_one]
      rfl
    · intro k _ hki
      rw [inner_smul_left, RCLike.conj_to_real, OrthonormalBasis.coe_toBasis,
        b.orthonormal.2 hki, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hH_symm : H.IsSymmetric := by
    intro x y
    have hinner : ∀ u v : E, ⟪H u, v⟫ = ∑ i, ∑ j, ⟪b i, v⟫ * ⟪b j, u⟫ * a i j := fun u v => by
      have hu := (b.sum_repr' u).symm
      have hv := (b.sum_repr' v).symm
      conv_lhs => rw [hu, hv]
      simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
        RCLike.conj_to_real]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hH_entry i j]; ring
    rw [hinner x y, real_inner_comm (H y) x, hinner y x, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have ha : a i j = a j i := by dsimp only [a]; ring
    rw [ha]; ring
  have hH_rankOne : ∀ u : E, f₁ (rankOneCLM u u) = ⟪H u, u⟫ := fun u => by
    have hu : rankOneCLM u u =
        ∑ i, ∑ j, (⟪b i, u⟫ * ⟪b j, u⟫) • rankOneCLM (b i) (b j) := by
      ext x
      simp only [rankOneCLM_apply, sum_apply, smul_apply]
      have hxu : ⟪u, x⟫ = ∑ j, ⟪b j, u⟫ * ⟪b j, x⟫ := by
        simpa [real_inner_comm] using (b.sum_inner_mul_inner u x).symm
      have hu_exp := (b.sum_repr' u).symm
      rw [hxu]
      conv_lhs => rw [hu_exp]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, smul_smul]
      congr 1
      have hju : ⟪b j, ∑ k, ⟪b k, u⟫ • b k⟫ = ⟪b j, u⟫ := by rw [← hu_exp]
      rw [hju]
      ring
    have hf : f₁ (rankOneCLM u u) =
        ∑ i, ∑ j, (⟪b i, u⟫ * ⟪b j, u⟫) * f₁ (rankOneCLM (b i) (b j)) := by
      rw [hu, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]
    have hsym_sum :
        ∑ i, ∑ j, (⟪b i, u⟫ * ⟪b j, u⟫) * f₁ (rankOneCLM (b i) (b j)) =
          ∑ i, ∑ j, (⟪b i, u⟫ * ⟪b j, u⟫) * a i j := by
      have hswap :
          ∑ i, ∑ j, (⟪b i, u⟫ * ⟪b j, u⟫) * f₁ (rankOneCLM (b i) (b j)) =
            ∑ i, ∑ j, (⟪b i, u⟫ * ⟪b j, u⟫) * f₁ (rankOneCLM (b j) (b i)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      have hdouble :
          2 * ∑ i, ∑ j, (⟪b i, u⟫ * ⟪b j, u⟫) * a i j =
            (∑ i, ∑ j, (⟪b i, u⟫ * ⟪b j, u⟫) * f₁ (rankOneCLM (b i) (b j))) +
              (∑ i, ∑ j, (⟪b i, u⟫ * ⟪b j, u⟫) * f₁ (rankOneCLM (b j) (b i))) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => by dsimp only [a]; ring
      linarith
    have hinner : ⟪H u, u⟫ = ∑ i, ∑ j, (⟪b i, u⟫ * ⟪b j, u⟫) * a i j := by
      have hu_exp := (b.sum_repr' u).symm
      conv_lhs => rw [hu_exp]
      simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
        RCLike.conj_to_real]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hH_entry i j]; ring
    rw [hf, hsym_sum, hinner]
  have hH_trace : f₁ (ContinuousLinearMap.id ℝ E) = LinearMap.trace ℝ E H := by
    have hid : ContinuousLinearMap.id ℝ E = ∑ i, rankOneCLM (b i) (b i) := by
      ext x
      simp only [ContinuousLinearMap.id_apply, sum_apply, rankOneCLM_apply]
      exact (b.sum_repr' x).symm
    rw [hid, map_sum, LinearMap.trace_eq_matrix_trace ℝ b.toBasis,
      LinearMap.toMatrix_toLin, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.diag_apply, a]
  exact ⟨H, hH_symm, hH_rankOne, hH_trace⟩

/-- **John's Decomposition of the Identity (Ball, Lecture 3):**
if `K : ConvexBody E` is in John's position in dimension `d = finrank ℝ E ≥ 1`, then there exist
finitely many contact points `u : Fin m → E` (with `u i ∈ sphere 0 1` and `supportFn K (u i) = 1`)
and strictly positive weights `c : Fin m → ℝ` satisfying:
1. `IsJohnDecomposition u c` (`∑ i, c i • (u i ⊗ u i) = id`),
2. `∑ i, c i • u i = 0`. -/
theorem john_decomposition_of_john_position [FiniteDimensional ℝ E] [Nontrivial E]
    (K : ConvexBody E) (hJ : IsJohnPosition (K : Set E)) :
    ∃ (m : ℕ) (u : Fin m → E) (c : Fin m → ℝ),
      IsJohnDecomposition u c ∧
      (∑ i, c i • u i = 0) ∧
      (∀ i, supportFn K (u i) = 1) := by
  set d := Module.finrank ℝ E
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr Module.finrank_pos
  have hsup_ge_one : ∀ w : E, ‖w‖ = 1 → 1 ≤ supportFn K w := fun w hw => by
    have hwK : w ∈ (K : Set E) := hJ.1 (by rw [mem_closedBall_zero_iff, hw])
    have h1 := inner_le_supportFn hwK w
    rwa [real_inner_self_eq_norm_sq, hw, one_pow] at h1
  -- Contact set `C = {u ∈ S^{d-1} | supportFn K u = 1}` is compact.
  let C : Set E := {u : E | ‖u‖ = 1 ∧ supportFn K u = 1}
  have hC_compact : IsCompact C := by
    have hsub : C ⊆ sphere (0 : E) 1 := fun u hu => by rw [mem_sphere_zero_iff_norm]; exact hu.1
    have hclosed : IsClosed C :=
      (isClosed_eq continuous_norm continuous_const).inter
        (isClosed_eq (continuous_supportFn K) continuous_const)
    exact (isCompact_sphere (0 : E) 1).of_isClosed_subset hclosed hsub
  let φ : E → (E →L[ℝ] E) × E := fun u => (rankOneCLM u u, u)
  have hφ_cont : Continuous φ := continuous_rankOneCLM.prodMk continuous_id
  let M : Set ((E →L[ℝ] E) × E) := φ '' C
  have hM_compact : IsCompact M := hC_compact.image hφ_cont
  have hconvM_compact : IsCompact (convexHull ℝ M) := isCompact_convexHull_of_isCompact hM_compact
  let target : (E →L[ℝ] E) × E := ((d : ℝ)⁻¹ • ContinuousLinearMap.id ℝ E, 0)
  -- Core separation step: `target ∈ convexHull ℝ M`.
  have htarget : target ∈ convexHull ℝ M := by
    by_contra hnot
    obtain ⟨f, s, hMs, hst⟩ :=
      geometric_hahn_banach_closed_point (convex_convexHull ℝ M) hconvM_compact.isClosed hnot
    let f₁ : (E →L[ℝ] E) →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ (E →L[ℝ] E) E)
    let f₂ : E →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inr ℝ (E →L[ℝ] E) E)
    obtain ⟨H, hH_symm, hH_rankOne, hH_trace⟩ := exists_symmetric_representing_clm f₁
    let v : E := (InnerProductSpace.toDual ℝ E).symm f₂
    have hv : ∀ w : E, f₂ w = ⟪v, w⟫ := fun w => by
      dsimp only [v]; rw [InnerProductSpace.toDual_symm_apply]
    have hf_split : ∀ (A : E →L[ℝ] E) (w : E), f (A, w) = f₁ A + f₂ w := fun A w => by
      have hpair : (A, w) = ContinuousLinearMap.inl ℝ (E →L[ℝ] E) E A +
          ContinuousLinearMap.inr ℝ (E →L[ℝ] E) E w := by ext <;> simp
      rw [hpair, map_add]; rfl
    have hf_u : ∀ u : E, f (φ u) = ⟪H u, u⟫ + ⟪v, u⟫ := fun u => by
      rw [hf_split, hH_rankOne, hv]
    have hf_target : f target = (d : ℝ)⁻¹ * LinearMap.trace ℝ E H := by
      dsimp only [target]
      rw [hf_split, map_smul, map_zero, add_zero, smul_eq_mul, hH_trace]
    -- Shift `H` to `H' = H - s • id` so `trace H' > 0` and `⟪H' u, u⟫ + ⟪v, u⟫ < 0` on `C`.
    let H' : E →ₗ[ℝ] E := H - s • LinearMap.id
    have hH'_symm : H'.IsSymmetric := by
      intro x y
      simp only [H', LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
      rw [hH_symm x y]
    have hH'_trace : 0 < LinearMap.trace ℝ E H' := by
      simp only [H', map_sub, map_smul, LinearMap.trace_id, smul_eq_mul]
      rw [hf_target] at hst
      have h1 : s * (d : ℝ) < LinearMap.trace ℝ E H := by
        have := mul_lt_mul_of_pos_left hst hd_pos
        rw [← mul_assoc, mul_inv_cancel₀ hd_pos.ne', one_mul] at this
        linarith
      linarith
    have hH'_neg_C : ∀ u ∈ C, ⟪H' u, u⟫ + ⟪v, u⟫ < 0 := fun u hu => by
      have h1 : f (φ u) < s := hMs (φ u) (subset_convexHull ℝ M ⟨u, hu, rfl⟩)
      rw [hf_u u] at h1
      have hval : ⟪H' u, u⟫ = ⟪H u, u⟫ - s := by
        simp only [H', LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
          inner_sub_left, inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq,
          hu.1, one_pow, mul_one]
      linarith
    -- Uniform negative margin `-δ` on `C`.
    let g : E → ℝ := fun w => ⟪H' w, w⟫ + ⟪v, w⟫
    have hg_cont : Continuous g :=
      ((H'.toContinuousLinearMap.continuous.inner continuous_id).add
        (continuous_const.inner continuous_id))
    have hδ_ex : ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ C, g u ≤ -2 * δ := by
      by_cases hCne : C.Nonempty
      · obtain ⟨u₀, hu₀, hmax⟩ := hC_compact.exists_isMaxOn hCne hg_cont.continuousOn
        have hlt0 : g u₀ < 0 := hH'_neg_C u₀ hu₀
        refine ⟨-g u₀ / 2, by linarith, fun u hu => ?_⟩
        have hle : g u ≤ g u₀ := hmax hu
        linarith
      · refine ⟨1, one_pos, fun u hu => False.elim (hCne ⟨u, hu⟩)⟩
    obtain ⟨δ, hδ_pos, hδ_C⟩ := hδ_ex
    -- Outside `U = {w ∈ S^{d-1} | g w < -δ}`, `supportFn K` has a uniform gap `1 + η`.
    let Sbad : Set E := {w : E | w ∈ sphere (0 : E) 1 ∧ -δ ≤ g w}
    have hSbad_compact : IsCompact Sbad :=
      (isCompact_sphere (0 : E) 1).of_isClosed_subset
        (isClosed_sphere.inter (isClosed_le continuous_const hg_cont))
        (fun _ hw => hw.1)
    have hη_ex : ∃ η : ℝ, 0 < η ∧ ∀ w ∈ Sbad, 1 + η ≤ supportFn K w := by
      by_cases hne : Sbad.Nonempty
      · obtain ⟨w₀, hw₀, hmin⟩ := hSbad_compact.exists_isMinOn hne (continuous_supportFn K).continuousOn
        have hw0_norm : ‖w₀‖ = 1 := mem_sphere_zero_iff_norm.mp hw₀.1
        have hw0_notC : w₀ ∉ C := fun hC => by linarith [hδ_C w₀ hC, hw₀.2]
        have hgt1 : 1 < supportFn K w₀ :=
          lt_of_le_of_ne (hsup_ge_one w₀ hw0_norm) fun heq => hw0_notC ⟨hw0_norm, heq.symm⟩
        refine ⟨supportFn K w₀ - 1, sub_pos.mpr hgt1, fun w hw => ?_⟩
        have hle : supportFn K w₀ ≤ supportFn K w := hmin hw
        linarith
      · refine ⟨1, one_pos, fun w hw => False.elim (hne ⟨w, hw⟩)⟩
    obtain ⟨η, hη_pos, hη_bad⟩ := hη_ex
    -- Pick `ε > 0` small enough that `det(id + ε H') > 1` AND `(id + ε H')(B₁) + ε v ⊆ K`.
    obtain ⟨ε₀, hε₀_pos, hdet_gt⟩ := exists_det_id_add_smul_gt_one hH'_symm hH'_trace
    set M_op : ℝ := ‖H'.toContinuousLinearMap‖
    have hM_nn : 0 ≤ M_op := norm_nonneg _
    set B_lin : ℝ := M_op + ‖v‖ + 1
    have hB_pos : 0 < B_lin := by positivity
    set ε : ℝ := min (ε₀ / 2) (min (η / B_lin) (min (δ / (M_op ^ 2 + 1)) (1 / (2 * (M_op + 1)))))
    have hε_pos : 0 < ε := by
      refine lt_min (half_pos hε₀_pos) (lt_min (div_pos hη_pos hB_pos)
        (lt_min (div_pos hδ_pos (by positivity)) (by positivity)))
    have hε_lt_ε₀ : ε < ε₀ := (min_le_left _ _).trans_lt (half_lt_self hε₀_pos)
    have hε_le_η : ε ≤ η / B_lin := (min_le_right _ _).trans (min_le_left _ _)
    have hε_le_δ : ε ≤ δ / (M_op ^ 2 + 1) :=
      ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
    have hε_le_half : ε ≤ 1 / (2 * (M_op + 1)) :=
      ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
    let Aε : E →ₗ[ℝ] E := LinearMap.id + ε • H'
    have hdet1 : 1 < LinearMap.det Aε := hdet_gt ε hε_pos hε_lt_ε₀
    -- Show `Aε(B₁) + ε v ⊆ K` using `mem_iff_forall_norm_le_one_inner_le_supportFn`.
    have hsubK : (fun x => Aε x + ε • v) '' closedBall (0 : E) 1 ⊆
        (K : Set E) := by
      rintro _ ⟨x, hx, rfl⟩
      change Aε x + ε • v ∈ K
      rw [mem_iff_forall_norm_le_one_inner_le_supportFn]
      intro w hw_le
      by_cases hw0 : w = 0
      · simp [hw0]
      · have hwn_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
        let w₁ : E := ‖w‖⁻¹ • w
        have hw₁_norm : ‖w₁‖ = 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwn_pos),
            inv_mul_cancel₀ hwn_pos.ne']
        have hw_eq : w = ‖w‖ • w₁ := by
          dsimp only [w₁]; rw [smul_smul, mul_inv_cancel₀ hwn_pos.ne', one_smul]
        rw [hw_eq, inner_smul_right, supportFn_smul K hwn_pos.le w₁]
        refine mul_le_mul_of_nonneg_left ?_ hwn_pos.le
        have hstep : ⟪Aε x + ε • v, w₁⟫ ≤ ‖Aε w₁‖ + ε * ⟪v, w₁⟫ := by
          rw [inner_add_left, inner_smul_left, RCLike.conj_to_real]
          have hsym_id : Aε.IsSymmetric := by
            intro a b
            simp only [Aε, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply,
              inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
              RCLike.conj_to_real]
            rw [hH'_symm a b]
          rw [hsym_id x w₁]
          have hcs := real_inner_le_norm x (Aε w₁)
          have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
          have h1 : ⟪x, Aε w₁⟫ ≤ ‖Aε w₁‖ :=
            hcs.trans ((mul_le_mul_of_nonneg_right hx1 (norm_nonneg (Aε w₁))).trans_eq (one_mul _))
          linarith
        refine hstep.trans ?_
        by_cases hbad : -δ ≤ g w₁
        · have hw₁_bad : w₁ ∈ Sbad := ⟨mem_sphere_zero_iff_norm.mpr hw₁_norm, hbad⟩
          have hsup_w₁ : 1 + η ≤ supportFn K w₁ := hη_bad w₁ hw₁_bad
          have hnorm_le : ‖Aε w₁‖ ≤ 1 + ε * M_op := by
            change ‖w₁ + ε • H' w₁‖ ≤ 1 + ε * M_op
            calc
              ‖w₁ + ε • H' w₁‖ ≤ ‖w₁‖ + ‖ε • H' w₁‖ := norm_add_le _ _
              _ = 1 + ε * ‖H' w₁‖ := by
                  rw [hw₁_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hε_pos]
              _ ≤ 1 + ε * (M_op * ‖w₁‖) := by
                  gcongr
                  exact H'.toContinuousLinearMap.le_opNorm w₁
              _ = 1 + ε * M_op := by rw [hw₁_norm, mul_one]
          have hv_le : ⟪v, w₁⟫ ≤ ‖v‖ := by
            calc
              ⟪v, w₁⟫ ≤ ‖v‖ * ‖w₁‖ := real_inner_le_norm v w₁
              _ = ‖v‖ := by rw [hw₁_norm, mul_one]
          have hεB : ε * B_lin ≤ η := (le_div_iff₀ hB_pos).mp hε_le_η
          have hlin : ε * M_op + ε * ⟪v, w₁⟫ ≤ ε * B_lin := by
            have h1 : ε * ⟪v, w₁⟫ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_left hv_le hε_pos.le
            have h2 : ε * (M_op + ‖v‖) ≤ ε * (M_op + ‖v‖ + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) hε_pos.le
            dsimp only [B_lin]; linarith
          linarith
        · push Not at hbad
          have hH'w_le : ‖H' w₁‖ ≤ M_op := by
            simpa [hw₁_norm] using H'.toContinuousLinearMap.le_opNorm w₁
          have hsq_exp : ‖Aε w₁‖ ^ 2 ≤
              1 + 2 * ε * ⟪H' w₁, w₁⟫ + ε ^ 2 * M_op ^ 2 := by
            change ‖w₁ + ε • H' w₁‖ ^ 2 ≤ _
            rw [norm_add_sq_real, hw₁_norm, one_pow, norm_smul, Real.norm_eq_abs,
              abs_of_pos hε_pos, mul_pow, inner_smul_right, real_inner_comm w₁ (H' w₁)]
            have hsq_le : ε ^ 2 * ‖H' w₁‖ ^ 2 ≤ ε ^ 2 * M_op ^ 2 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hH'w_le 2) (sq_nonneg ε)
            linarith
          have hinner_ge : -M_op ≤ ⟪H' w₁, w₁⟫ := by
            have h := abs_real_inner_le_norm (H' w₁) w₁
            rw [hw₁_norm, mul_one] at h
            linarith [(abs_le.mp h).1]
          set rhs : ℝ := 1 + ε * ⟪H' w₁, w₁⟫ + ε ^ 2 * M_op ^ 2 / 2
          have hrhs_nn : 0 ≤ rhs := by
            have h1 : ε * (M_op + 1) ≤ 1 / 2 := by
              have hpos : 0 < 2 * (M_op + 1) := by positivity
              have := (le_div_iff₀ hpos).mp hε_le_half
              linarith
            have h2 : -(ε * M_op) ≤ ε * ⟪H' w₁, w₁⟫ := by
              have := mul_le_mul_of_nonneg_left hinner_ge hε_pos.le
              linarith
            have h3 : ε * M_op ≤ ε * (M_op + 1) := mul_le_mul_of_nonneg_left (by linarith) hε_pos.le
            have h4 : 0 ≤ ε ^ 2 * M_op ^ 2 / 2 := by positivity
            dsimp only [rhs]; linarith
          have hnorm_le_rhs : ‖Aε w₁‖ ≤ rhs := by
            have hrhs_sq : 1 + 2 * ε * ⟪H' w₁, w₁⟫ + ε ^ 2 * M_op ^ 2 ≤ rhs ^ 2 := by
              have hmagic : rhs ^ 2 - (1 + 2 * ε * ⟪H' w₁, w₁⟫ + ε ^ 2 * M_op ^ 2) =
                  (ε * ⟪H' w₁, w₁⟫ + ε ^ 2 * M_op ^ 2 / 2) ^ 2 := by
                dsimp only [rhs]; ring
              have hsq_nn : 0 ≤ (ε * ⟪H' w₁, w₁⟫ + ε ^ 2 * M_op ^ 2 / 2) ^ 2 := sq_nonneg _
              linarith
            have hsq_le : ‖Aε w₁‖ ^ 2 ≤ rhs ^ 2 := hsq_exp.trans hrhs_sq
            exact (le_abs_self (‖Aε w₁‖)).trans ((sq_le_sq.mp hsq_le).trans_eq (abs_of_nonneg hrhs_nn))
          have hεM2 : ε * (M_op ^ 2 + 1) ≤ δ := (le_div_iff₀ (by positivity)).mp hε_le_δ
          have hsum_le1 : rhs + ε * ⟪v, w₁⟫ ≤ 1 := by
            have h1 : ε * g w₁ ≤ ε * (-δ) := mul_le_mul_of_nonneg_left hbad.le hε_pos.le
            have h2 : ε ^ 2 * M_op ^ 2 ≤ ε * (ε * (M_op ^ 2 + 1)) := by
              have hle : M_op ^ 2 ≤ M_op ^ 2 + 1 := by linarith
              have hmul := mul_le_mul_of_nonneg_left hle (sq_nonneg ε)
              linarith
            have h3 : ε * (ε * (M_op ^ 2 + 1)) ≤ ε * δ :=
              mul_le_mul_of_nonneg_left hεM2 hε_pos.le
            have h4 : 0 ≤ ε ^ 2 * M_op ^ 2 := by positivity
            have hg_eq : ⟪H' w₁, w₁⟫ + ⟪v, w₁⟫ = g w₁ := rfl
            have h5 : ε * ⟪H' w₁, w₁⟫ + ε * ⟪v, w₁⟫ = ε * g w₁ := by rw [← mul_add, hg_eq]
            dsimp only [rhs]
            linarith
          have hsup := hsup_ge_one w₁ hw₁_norm
          linarith
    have hle1 := hJ.2 Aε (ε • v) hsubK
    have hlt1 : 1 < |LinearMap.det Aε| := hdet1.trans_le (le_abs_self _)
    linarith
  -- Extract finite convex combination from `target ∈ convexHull ℝ M`, then scale weights by `d`.
  rw [convexHull_eq_union] at htarget
  rcases Set.mem_iUnion.mp htarget with ⟨t, ht⟩
  rcases Set.mem_iUnion.mp ht with ⟨htM, hmem⟩
  rcases Set.mem_iUnion.mp hmem with ⟨_, hmem_t⟩
  rw [Finset.convexHull_eq] at hmem_t
  rcases hmem_t with ⟨w, hw_nn, hw_sum, hw_comb⟩
  -- Restrict to the strictly positive support `s = {p ∈ t | 0 < w p}`.
  classical
  let s : Finset ((E →L[ℝ] E) × E) := t.filter (fun p => 0 < w p)
  have hsum_s : ∑ p ∈ s, w p • p = target := by
    rw [← hw_comb, Finset.centerMass_eq_of_sum_1 t id hw_sum]
    refine Finset.sum_subset (Finset.filter_subset _ t) fun p hp hnot => ?_
    have hw0 : w p = 0 := le_antisymm (not_lt.mp (by simpa [s, hp] using hnot)) (hw_nn p hp)
    simp [hw0]
  have hs_sub : (s : Set ((E →L[ℝ] E) × E)) ⊆ M :=
    (Finset.coe_subset.mpr (Finset.filter_subset _ t)).trans htM
  -- Choose a contact point `u₀ p ∈ C` for each `p ∈ s`.
  have hex_u : ∀ p : s, ∃ u : E, u ∈ C ∧ φ u = p.1 := fun p => hs_sub p.2
  choose u₀ hu₀_C hu₀_eq using hex_u
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let u : Fin (Fintype.card s) → E := fun i => u₀ (e i)
  let c : Fin (Fintype.card s) → ℝ := fun i => (d : ℝ) * w (e i).1
  refine ⟨Fintype.card s, u, c, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i; exact (hu₀_C (e i)).1
  · intro i
    have hwi : 0 < w (e i).1 := (Finset.mem_filter.mp (e i).2).2
    exact mul_pos hd_pos hwi
  · -- `∑ i, c i • rankOne (u i) (u i) = id`
    have h1 := congrArg Prod.fst hsum_s
    simp only [Prod.fst_sum, Prod.smul_fst, target] at h1
    have h1_fin : ∑ i : Fin (Fintype.card s), w (e i).1 • rankOneCLM (u i) (u i) =
        (d : ℝ)⁻¹ • ContinuousLinearMap.id ℝ E := by
      have hsum_coe : ∑ p : s, w p.1 • p.1.1 = (d : ℝ)⁻¹ • ContinuousLinearMap.id ℝ E := by
        rw [← h1]
        exact Finset.sum_coe_sort s (fun p => w p • p.1)
      rw [← hsum_coe, ← e.sum_comp]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hfst := congrArg Prod.fst (hu₀_eq (e i))
      dsimp only [φ, u] at hfst ⊢
      rw [hfst]
    ext x
    have hx := congrArg (fun L : E →L[ℝ] E => (d : ℝ) • L x) h1_fin
    simp only [sum_apply, smul_apply, ContinuousLinearMap.id_apply, Finset.smul_sum, smul_smul,
      mul_inv_cancel₀ hd_pos.ne', one_smul] at hx
    simpa [LinearMap.sum_apply, LinearMap.smul_apply, rankOne_apply, rankOneCLM_apply,
      real_inner_comm, c, smul_smul] using hx
  · -- `∑ i, c i • u i = 0`
    have h2 := congrArg Prod.snd hsum_s
    simp only [Prod.snd_sum, Prod.smul_snd, target] at h2
    have h2_fin : ∑ i : Fin (Fintype.card s), w (e i).1 • u i = 0 := by
      have hsum_coe : ∑ p : s, w p.1 • p.1.2 = 0 := by
        rw [← h2]
        exact Finset.sum_coe_sort s (fun p => w p • p.2)
      rw [← hsum_coe, ← e.sum_comp]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hsnd := congrArg Prod.snd (hu₀_eq (e i))
      dsimp only [φ, u] at hsnd ⊢
      rw [hsnd]
    calc
      ∑ i : Fin (Fintype.card s), c i • u i =
          ∑ i : Fin (Fintype.card s), (d : ℝ) • (w (e i).1 • u i) := by
          refine Finset.sum_congr rfl fun i _ => by dsimp only [c]; rw [smul_smul]
      _ = (d : ℝ) • ∑ i : Fin (Fintype.card s), w (e i).1 • u i := (Finset.smul_sum).symm
      _ = 0 := by rw [h2_fin, smul_zero]
  · intro i; exact (hu₀_C (e i)).2

/-- **General containment in John's position (Ball, Lecture 3):**
if `K : ConvexBody E` is in John's position in dimension `d = finrank ℝ E ≥ 1`, then
`K ⊆ d • closedBall 0 1` (i.e. `∀ x ∈ K, ‖x‖ ≤ d`). -/
theorem subset_finrank_smul_of_john_position [FiniteDimensional ℝ E] [Nontrivial E]
    (K : ConvexBody E) (hJ : IsJohnPosition (K : Set E)) :
    (K : Set E) ⊆ (Module.finrank ℝ E : ℝ) • closedBall (0 : E) 1 := by
  set d := Module.finrank ℝ E
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr Module.finrank_pos
  obtain ⟨m, u, c, hJD, hcenter, hsup⟩ := john_decomposition_of_john_position K hJ
  have hcb_eq : (d : ℝ) • closedBall (0 : E) 1 = closedBall (0 : E) (d : ℝ) := by
    ext y
    simp only [Set.mem_smul_set, mem_closedBall_zero_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd_pos]
      exact (mul_le_mul_of_nonneg_left hz hd_pos.le).trans_eq (mul_one _)
    · intro hy
      refine ⟨(d : ℝ)⁻¹ • y, ?_, by rw [smul_smul, mul_inv_cancel₀ hd_pos.ne', one_smul]⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd_pos),
        inv_mul_le_iff₀ hd_pos, mul_one]
      exact hy
  rw [hcb_eq]
  intro y hy
  rw [mem_closedBall_zero_iff]
  by_cases hy0 : y = 0
  · rw [hy0, norm_zero]; exact hd_pos.le
  · have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    let v : E := -(‖y‖⁻¹ • y)
    have hv_norm : ‖v‖ = 1 := by
      dsimp only [v]
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hyn),
        inv_mul_cancel₀ hyn.ne']
    have hyv : ⟪y, v⟫ = -‖y‖ := by
      dsimp only [v]
      rw [inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp [hyn.ne']
    have hterm : ∀ i, c i * (1 - ⟪y, u i⟫) * ⟪v, u i⟫ ≤ c i * (1 - ⟪y, u i⟫) := fun i => by
      have h1 : 0 ≤ 1 - ⟪y, u i⟫ := by
        have := inner_le_supportFn hy (u i)
        rw [hsup i] at this
        linarith
      have h2 : ⟪v, u i⟫ ≤ 1 := by
        calc
          ⟪v, u i⟫ ≤ ‖v‖ * ‖u i‖ := real_inner_le_norm v (u i)
          _ = 1 := by rw [hv_norm, hJD.norm_eq_one i, mul_one]
      have hnn : 0 ≤ c i * (1 - ⟪y, u i⟫) := mul_nonneg (hJD.weight_pos i).le h1
      simpa [mul_one] using mul_le_mul_of_nonneg_left h2 hnn
    have hsum_le : ∑ i, c i * (1 - ⟪y, u i⟫) * ⟪v, u i⟫ ≤ ∑ i, c i * (1 - ⟪y, u i⟫) :=
      Finset.sum_le_sum fun i _ => hterm i
    have hlhs : ∑ i, c i * (1 - ⟪y, u i⟫) * ⟪v, u i⟫ = ‖y‖ := by
      have hsplit : ∑ i, c i * (1 - ⟪y, u i⟫) * ⟪v, u i⟫ =
          (∑ i, c i * ⟪v, u i⟫) - ∑ i, c i * ⟪y, u i⟫ * ⟪v, u i⟫ := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => by ring
      have h1 : ∑ i, c i * ⟪v, u i⟫ = 0 := by
        have := congrArg (fun z : E => ⟪v, z⟫) hcenter
        rw [inner_sum, inner_zero_right] at this
        simpa [inner_smul_right] using this
      rw [hsplit, h1, zero_sub, ← hJD.inner_eq_sum y v, hyv, neg_neg]
    have hrhs : ∑ i, c i * (1 - ⟪y, u i⟫) = (d : ℝ) := by
      have hsplit : ∑ i, c i * (1 - ⟪y, u i⟫) = (∑ i, c i) - ∑ i, c i * ⟪y, u i⟫ := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => by ring
      have h1 : ∑ i, c i * ⟪y, u i⟫ = 0 := by
        have := congrArg (fun z : E => ⟪y, z⟫) hcenter
        rw [inner_sum, inner_zero_right] at this
        simpa [inner_smul_right] using this
      rw [hsplit, h1, sub_zero, hJD.sum_weights]
    linarith

/-- **Origin-symmetric containment in John's position (Ball, Lecture 3):**
if `K : ConvexBody E` is origin-symmetric and in John's position in dimension `d ≥ 1`, then
`K ⊆ √d • closedBall 0 1` (i.e. `∀ x ∈ K, ‖x‖ ≤ √d`). -/
theorem subset_sqrt_finrank_smul_of_john_position [FiniteDimensional ℝ E] [Nontrivial E]
    (K : ConvexBody E) (hsym : IsOriginSymmetric (K : Set E))
    (hJ : IsJohnPosition (K : Set E)) :
    (K : Set E) ⊆ Real.sqrt (Module.finrank ℝ E : ℝ) • closedBall (0 : E) 1 := by
  set d := Module.finrank ℝ E
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr Module.finrank_pos
  have hsd_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd_pos
  obtain ⟨m, u, c, hJD, _, hsup⟩ := john_decomposition_of_john_position K hJ
  have hcb_eq : Real.sqrt (d : ℝ) • closedBall (0 : E) 1 = closedBall (0 : E) (Real.sqrt (d : ℝ)) := by
    ext y
    simp only [Set.mem_smul_set, mem_closedBall_zero_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsd_pos]
      exact (mul_le_mul_of_nonneg_left hz hsd_pos.le).trans_eq (mul_one _)
    · intro hy
      refine ⟨(Real.sqrt (d : ℝ))⁻¹ • y, ?_,
        by rw [smul_smul, mul_inv_cancel₀ hsd_pos.ne', one_smul]⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsd_pos),
        inv_mul_le_iff₀ hsd_pos, mul_one]
      exact hy
  rw [hcb_eq]
  intro x hx
  rw [mem_closedBall_zero_iff]
  have hsq : ‖x‖ ^ 2 ≤ (d : ℝ) := by
    rw [hJD.norm_sq_eq_sum x]
    calc
      ∑ i, c i * ⟪x, u i⟫ ^ 2 ≤ ∑ i, c i * 1 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hpos : ⟪x, u i⟫ ≤ 1 := by rw [← hsup i]; exact inner_le_supportFn hx (u i)
        have hneg : -⟪x, u i⟫ ≤ 1 := by
          have := inner_le_supportFn (hsym x hx) (u i)
          rw [inner_neg_left, hsup i] at this
          exact this
        have habs : |⟪x, u i⟫| ≤ 1 := abs_le.mpr ⟨by linarith, hpos⟩
        have hsq1 : ⟪x, u i⟫ ^ 2 ≤ 1 := by
          rw [← sq_abs]; nlinarith [abs_nonneg ⟪x, u i⟫]
        exact mul_le_mul_of_nonneg_left hsq1 (hJD.weight_pos i).le
      _ = (d : ℝ) := by simp [hJD.sum_weights, d]
  calc
    ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
    _ ≤ Real.sqrt (d : ℝ) := Real.sqrt_le_sqrt hsq

/-- **Dvoretzky–Rogers Lemma (Ball, Lecture 4):**
if `K : ConvexBody E` is in John's position (`IsJohnPosition K`) in dimension `d ≥ 1`, then for any
`m ≤ d` there exist orthonormal vectors `e : Fin m → E` such that
`√((d - j) / d) ≤ gauge K (e j)`. -/
theorem dvoretzky_rogers_lemma [FiniteDimensional ℝ E] [Nontrivial E]
    (K : ConvexBody E) (hJ : IsJohnPosition (K : Set E)) (m : ℕ) (hm : m ≤ Module.finrank ℝ E) :
    ∃ e : Fin m → E, Orthonormal ℝ e ∧
      ∀ j : Fin m, Real.sqrt (((Module.finrank ℝ E - j.1 : ℕ) : ℝ) / (Module.finrank ℝ E : ℝ)) ≤
        gauge (K : Set E) (e j) := by
  set d := Module.finrank ℝ E
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr Module.finrank_pos
  have h0K : (0 : E) ∈ interior (K : Set E) :=
    mem_interior.mpr ⟨ball (0 : E) 1, ball_subset_closedBall.trans hJ.1, isOpen_ball,
      mem_ball_self zero_lt_one⟩
  obtain ⟨k, u, c, hJD, _, hsup⟩ := john_decomposition_of_john_position K hJ
  have hu_polar : ∀ i, u i ∈ polarBody (K : Set E) := fun i x hx => by
    rw [← hsup i]; exact inner_le_supportFn hx (u i)
  have hgauge_ge : ∀ (x : E) (i : Fin k), ⟪x, u i⟫ ≤ gauge (K : Set E) x := fun x i => by
    rw [← supportFn_bodyPolar_eq_gauge K h0K]
    have hmem : u i ∈ bodyPolar (K : Set E) h0K := by
      rw [← SetLike.mem_coe, coe_bodyPolar]; exact hu_polar i
    rw [real_inner_comm]
    exact inner_le_supportFn hmem x
  -- Construct `e : Fin n → E` by induction on `n ≤ d`.
  suffices ∀ n : ℕ, n ≤ d →
      ∃ e : Fin n → E, Orthonormal ℝ e ∧
        ∀ j : Fin n, Real.sqrt (((d - j.1 : ℕ) : ℝ) / (d : ℝ)) ≤ gauge (K : Set E) (e j) from
    this m hm
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩, fun j => j.elim0⟩
  | succ n ih =>
    intro hn
    obtain ⟨e, horth, hge⟩ := ih (Nat.le_of_succ_le hn)
    let S : Submodule ℝ E := Submodule.span ℝ (Set.range e)
    let H : Submodule ℝ E := Sᗮ
    have hS_fin : Module.finrank ℝ S = n := by
      have hli : LinearIndependent ℝ e := horth.linearIndependent
      simpa [S, Fintype.card_fin] using finrank_span_eq_card hli
    have hH_fin : Module.finrank ℝ H = d - n := by
      have hadd : Module.finrank ℝ S + Module.finrank ℝ H = d :=
        Submodule.finrank_add_finrank_orthogonal S
      omega
    obtain ⟨i, hi⟩ := hJD.exists_sq_norm_proj_ge H
    rw [hH_fin] at hi
    set p : E := (H.orthogonalProjectionOnto (u i) : E)
    have hpos_ratio : (0 : ℝ) < ((d - n : ℕ) : ℝ) / (d : ℝ) :=
      div_pos (Nat.cast_pos.mpr (by omega)) hd_pos
    have hp_pos : 0 < ‖p‖ := by
      have hsq : 0 < ‖p‖ ^ 2 := lt_of_lt_of_le hpos_ratio hi
      nlinarith [norm_nonneg p]
    let v : E := ‖p‖⁻¹ • p
    have hv_norm : ‖v‖ = 1 := by
      dsimp only [v]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp_pos), inv_mul_cancel₀ hp_pos.ne']
    have hv_mem_H : v ∈ H := H.smul_mem _ (H.orthogonalProjectionOnto (u i)).2
    have hv_orth : ∀ j : Fin n, ⟪e j, v⟫ = 0 := fun j => by
      have heS : e j ∈ S := Submodule.subset_span ⟨j, rfl⟩
      exact Submodule.inner_right_of_mem_orthogonal heS hv_mem_H
    have hv_gauge : Real.sqrt (((d - n : ℕ) : ℝ) / (d : ℝ)) ≤ gauge (K : Set E) v := by
      have hinner : ⟪v, u i⟫ = ‖p‖ := by
        have hproj : ⟪p, u i⟫ = ‖p‖ ^ 2 := by
          have h := H.inner_orthogonalProjectionOnto_eq_of_mem_left
            (H.orthogonalProjectionOnto (u i)) (u i)
          have h1 : ⟪p, p⟫ = ⟪p, u i⟫ := h
          rw [← h1, real_inner_self_eq_norm_sq]
        dsimp only [v]
        rw [inner_smul_left, RCLike.conj_to_real, hproj]
        field_simp [hp_pos.ne']
      calc
        Real.sqrt (((d - n : ℕ) : ℝ) / (d : ℝ)) ≤ Real.sqrt (‖p‖ ^ 2) := Real.sqrt_le_sqrt hi
        _ = ‖p‖ := Real.sqrt_sq (norm_nonneg p)
        _ = ⟪v, u i⟫ := hinner.symm
        _ ≤ gauge (K : Set E) v := hgauge_ge v i
    let e' : Fin (n + 1) → E := Fin.snoc e v
    refine ⟨e', ⟨?_, ?_⟩, ?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa [e'] using hv_norm
      · simpa [e'] using horth.1 k
    · intro j₁ j₂
      refine Fin.lastCases ?_ (fun k₁ => ?_) j₁
      · refine Fin.lastCases (fun h => absurd rfl h) (fun k₂ _ => ?_) j₂
        simp only [e', Fin.snoc_last, Fin.snoc_castSucc]
        rw [real_inner_comm]
        exact hv_orth k₂
      · refine Fin.lastCases (fun _ => ?_) (fun k₂ hk => ?_) j₂
        · simp only [e', Fin.snoc_last, Fin.snoc_castSucc]
          exact hv_orth k₁
        · simp only [e', Fin.snoc_castSucc]
          exact horth.2 fun h => hk (congrArg Fin.castSucc h)
    · intro j
      refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa [e'] using hv_gauge
      · simpa [e'] using hge k

/-- **Fritz John's Theorem (General Convex Bodies, Ball Lecture 3):**
for every `K : ConvexBody E` with nonempty interior in dimension `d ≥ 1`, there exists an affine
equivalence `A : E ≃ᵃ[ℝ] E` such that `A '' K` is in John's position and
`closedBall 0 1 ⊆ A '' K ⊆ d • closedBall 0 1`. -/
theorem john_theorem [FiniteDimensional ℝ E] [Nontrivial E]
    (K : ConvexBody E) (hint : (interior (K : Set E)).Nonempty) :
    ∃ A : E ≃ᵃ[ℝ] E,
      IsJohnPosition (A '' (K : Set E)) ∧
      closedBall (0 : E) 1 ⊆ A '' (K : Set E) ∧
      A '' (K : Set E) ⊆ (Module.finrank ℝ E : ℝ) • closedBall (0 : E) 1 := by
  obtain ⟨A, hJ⟩ := exists_affineEquiv_isJohnPosition K hint
  let KA : ConvexBody E :=
    mapLinear A.linear.toContinuousLinearMap K + bodySingleton (A 0)
  have hKA_coe : (KA : Set E) = A '' (K : Set E) := by
    ext y
    simp only [KA, ConvexBody.coe_add, coe_mapLinear, coe_bodySingleton, Set.mem_add,
      Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, rfl, rfl⟩
      refine ⟨x, hx, ?_⟩
      have h := A.map_vadd 0 x
      simp only [vadd_eq_add, add_zero] at h
      change A x = A.linear x + A 0
      rw [h, add_comm]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨A.linear x, ⟨x, hx, rfl⟩, A 0, rfl, ?_⟩
      have h := A.map_vadd 0 x
      simp only [vadd_eq_add, add_zero] at h
      change A.linear x + A 0 = A x
      rw [h, add_comm]
  have hKA_J : IsJohnPosition (KA : Set E) := hKA_coe.symm ▸ hJ
  have hsub := subset_finrank_smul_of_john_position KA hKA_J
  rw [hKA_coe] at hsub
  exact ⟨A, hJ, hJ.1, hsub⟩

/-- **Fritz John's Theorem (Origin-Symmetric Convex Bodies, Ball Lecture 3):**
for every origin-symmetric `K : ConvexBody E` with `0 ∈ interior K` in dimension `d ≥ 1`, there
exists `T : E ≃ₗ[ℝ] E` such that `T '' K` is in John's position and
`closedBall 0 1 ⊆ T '' K ⊆ √d • closedBall 0 1`. -/
theorem john_theorem_symmetric [FiniteDimensional ℝ E] [Nontrivial E]
    (K : ConvexBody E) (hsym : IsOriginSymmetric (K : Set E))
    (h0 : (0 : E) ∈ interior (K : Set E)) :
    ∃ T : E ≃ₗ[ℝ] E,
      IsJohnPosition (T '' (K : Set E)) ∧
      closedBall (0 : E) 1 ⊆ T '' (K : Set E) ∧
      T '' (K : Set E) ⊆ Real.sqrt (Module.finrank ℝ E : ℝ) • closedBall (0 : E) 1 := by
  obtain ⟨T, hJ⟩ := exists_linearEquiv_isJohnPosition_of_isOriginSymmetric K hsym h0
  let KT : ConvexBody E := mapLinear T.toContinuousLinearMap K
  have hKT_coe : (KT : Set E) = T '' (K : Set E) := coe_mapLinear _ K
  have hKT_sym : IsOriginSymmetric (KT : Set E) := by
    rw [hKT_coe]; exact isOriginSymmetric_linearMap_image T.toLinearMap hsym
  have hKT_J : IsJohnPosition (KT : Set E) := hKT_coe.symm ▸ hJ
  have hsub := subset_sqrt_finrank_smul_of_john_position KT hKT_sym hKT_J
  rw [hKT_coe] at hsub
  exact ⟨T, hJ, hJ.1, hsub⟩

/-- **Löwner's Theorem (Minimal-Volume Enclosing Ellipsoid for Origin-Symmetric Bodies):**
for every origin-symmetric `K : ConvexBody E` with `0 ∈ interior K` in dimension `d ≥ 1`, there
exists `T : E ≃ₗ[ℝ] E` such that `(√d)⁻¹ • closedBall 0 1 ⊆ T '' K ⊆ closedBall 0 1` and
`polarBody (T '' K)` is in John's position. -/
theorem loewner_theorem_symmetric [FiniteDimensional ℝ E] [Nontrivial E]
    (K : ConvexBody E) (hsym : IsOriginSymmetric (K : Set E))
    (h0 : (0 : E) ∈ interior (K : Set E)) :
    ∃ T : E ≃ₗ[ℝ] E,
      IsJohnPosition (polarBody (T '' (K : Set E))) ∧
      (Real.sqrt (Module.finrank ℝ E : ℝ))⁻¹ • closedBall (0 : E) 1 ⊆ T '' (K : Set E) ∧
      T '' (K : Set E) ⊆ closedBall (0 : E) 1 := by
  set d := Module.finrank ℝ E
  have hsd_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr Module.finrank_pos)
  let Kpol : ConvexBody E := bodyPolar (K : Set E) h0
  have hKpol_sym : IsOriginSymmetric (Kpol : Set E) := by
    rw [coe_bodyPolar]; exact isOriginSymmetric_polarBody hsym
  have hKpol_0 : (0 : E) ∈ interior (Kpol : Set E) := by
    rw [coe_bodyPolar]; exact zero_mem_interior_polarBody_of_isBounded K.isBounded
  obtain ⟨S, hSJ, hBsub, hsubB⟩ := john_theorem_symmetric Kpol hKpol_sym hKpol_0
  let T : E ≃ₗ[ℝ] E := (adjointLinearEquiv S).symm
  have hpol_eq : polarBody (T '' (K : Set E)) = S '' (Kpol : Set E) := by
    rw [polarBody_linearEquiv_image, coe_bodyPolar]
    congr 1
    ext x
    have hinner : ∀ y : E, ⟪adjointLinearEquiv T.symm x, y⟫ = ⟪S x, y⟫ := fun y => by
      rw [adjointLinearEquiv_apply, LinearMap.adjoint_inner_left]
      have hTsym : (T.symm : E →ₗ[ℝ] E) = LinearMap.adjoint (S : E →ₗ[ℝ] E) := by
        dsimp only [T]
        rw [LinearEquiv.symm_symm, adjointLinearEquiv_toLinearMap]
      rw [hTsym, LinearMap.adjoint_inner_right]
      rfl
    exact ext_inner_right ℝ hinner
  have hbipolar : T '' (K : Set E) = polarBody (S '' (Kpol : Set E)) := by
    rw [← hpol_eq]
    exact (polarBody_polarBody (K.convex.linear_image T.toLinearMap)
      (K.isCompact.image T.toContinuousLinearEquiv.continuous).isClosed
      ⟨0, interior_subset h0, map_zero T⟩).symm
  refine ⟨T, hpol_eq.symm ▸ hSJ, ?_, ?_⟩
  · rw [hbipolar]
    have h1 := polarBody_antitone hsubB
    rwa [polarBody_smul hsd_pos, polarBody_closedBall one_pos, inv_one] at h1
  · rw [hbipolar]
    have h1 := polarBody_antitone hBsub
    rwa [polarBody_closedBall one_pos, inv_one] at h1

end FritzJohn

/-! ### 5. Banach–Mazur Bounds, Attainment, and Compactness -/

section BanachMazurCompactum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper: joint convergence of continuous linear operator application `A n (x n) → A x`. -/
private lemma tendsto_clm_apply {A : ℕ → (E →L[ℝ] E)} {A₀ : E →L[ℝ] E} {x : ℕ → E} {x₀ : E}
    (hA : Tendsto A atTop (𝓝 A₀)) (hx : Tendsto x atTop (𝓝 x₀)) :
    Tendsto (fun n => A n (x n)) atTop (𝓝 (A₀ x₀)) := by
  rw [Metric.tendsto_atTop] at hA hx ⊢
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := hx 1 one_pos
  set M : ℝ := ‖x₀‖ + 1
  have hM : 0 < M := by positivity
  obtain ⟨N₁, hN₁⟩ := hA (ε / (2 * M)) (by positivity)
  obtain ⟨N₂, hN₂⟩ := hx (ε / (2 * (‖A₀‖ + 1))) (by positivity)
  refine ⟨max N₀ (max N₁ N₂), fun n hn => ?_⟩
  have hn0 : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hxn : ‖x n‖ ≤ M := by
    have h1 : ‖x n - x₀‖ < 1 := by simpa [dist_eq_norm] using hN₀ n hn0
    have h2 := norm_sub_norm_le (x n) x₀
    dsimp only [M]; linarith
  have hAn : ‖A n - A₀‖ < ε / (2 * M) := by simpa [dist_eq_norm] using hN₁ n hn1
  have hx2 : ‖x n - x₀‖ < ε / (2 * (‖A₀‖ + 1)) := by simpa [dist_eq_norm] using hN₂ n hn2
  rw [dist_eq_norm]
  have hsplit : A n (x n) - A₀ x₀ = (A n - A₀) (x n) + A₀ (x n - x₀) := by
    simp [map_sub]
  rw [hsplit]
  have hterm1 : ‖(A n - A₀) (x n)‖ < ε / 2 := by
    calc
      ‖(A n - A₀) (x n)‖ ≤ ‖A n - A₀‖ * ‖x n‖ := (A n - A₀).le_opNorm (x n)
      _ ≤ ‖A n - A₀‖ * M := mul_le_mul_of_nonneg_left hxn (norm_nonneg _)
      _ < (ε / (2 * M)) * M := mul_lt_mul_of_pos_right hAn hM
      _ = ε / 2 := by field_simp [hM.ne']
  have hterm2 : ‖A₀ (x n - x₀)‖ < ε / 2 := by
    have hden : 0 < ‖A₀‖ + 1 := by positivity
    calc
      ‖A₀ (x n - x₀)‖ ≤ ‖A₀‖ * ‖x n - x₀‖ := A₀.le_opNorm _
      _ ≤ (‖A₀‖ + 1) * ‖x n - x₀‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (‖A₀‖ + 1) * (ε / (2 * (‖A₀‖ + 1))) := mul_lt_mul_of_pos_left hx2 hden
      _ = ε / 2 := by field_simp [hden.ne']
  exact (norm_add_le _ _).trans_lt (by linarith)

/-- **John's Banach–Mazur Bound (Origin-Symmetric Bodies, Ball Lecture 3):**
for every origin-symmetric `K : ConvexBody E` with `0 ∈ interior K` in dimension `d ≥ 1`:
`banachMazurDist K (closedBall 0 1) ≤ √d`. -/
theorem banachMazurDist_closedBall_le_sqrt_finrank [FiniteDimensional ℝ E] [Nontrivial E]
    (K : ConvexBody E) (hsym : IsOriginSymmetric (K : Set E))
    (h0 : (0 : E) ∈ interior (K : Set E)) :
    banachMazurDist (K : Set E) (closedBall (0 : E) 1) ≤
      Real.sqrt (Module.finrank ℝ E : ℝ) := by
  set d := Module.finrank ℝ E
  have hd_ge1 : (1 : ℝ) ≤ d := by exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E))
  have hsd_ge1 : 1 ≤ Real.sqrt (d : ℝ) := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hd_ge1
  have hsd_pos : 0 < Real.sqrt (d : ℝ) := lt_of_lt_of_le zero_lt_one hsd_ge1
  obtain ⟨T, _, hBsub, hsubB⟩ := john_theorem_symmetric K hsym h0
  let S : E ≃ₗ[ℝ] E := (smulLinearEquiv hsd_pos.ne').trans T.symm
  have hmem : Real.sqrt (d : ℝ) ∈ banachMazurSet (K : Set E) (closedBall (0 : E) 1) := by
    refine ⟨hsd_ge1, S, ?_, ?_⟩
    · intro x hx
      have hTx : T x ∈ Real.sqrt (d : ℝ) • closedBall (0 : E) 1 := hsubB ⟨x, hx, rfl⟩
      rcases hTx with ⟨u, hu, huTx⟩
      refine ⟨u, hu, ?_⟩
      dsimp only [S]
      rw [LinearEquiv.trans_apply, smulLinearEquiv_apply,
        show Real.sqrt (d : ℝ) • u = T x from huTx, T.symm_apply_apply]
    · rintro _ ⟨u, hu, rfl⟩
      rcases hBsub hu with ⟨x, hx, hTx⟩
      refine ⟨x, hx, ?_⟩
      dsimp only [S]
      rw [LinearEquiv.trans_apply, smulLinearEquiv_apply, ← hTx, ← map_smul, T.symm_apply_apply]
  exact csInf_le (bddBelow_banachMazurSet _ _) hmem

/-- **John's Banach–Mazur Diameter Bound (Origin-Symmetric Bodies, Ball Lecture 4):**
for any two origin-symmetric `K, L : ConvexBody E` with `0` in their interiors in dimension `d ≥ 1`:
`banachMazurDist K L ≤ d`. -/
theorem banachMazurDist_le_finrank [FiniteDimensional ℝ E] [Nontrivial E]
    (K L : ConvexBody E)
    (hKsym : IsOriginSymmetric (K : Set E)) (hK0 : (0 : E) ∈ interior (K : Set E))
    (hLsym : IsOriginSymmetric (L : Set E)) (hL0 : (0 : E) ∈ interior (L : Set E)) :
    banachMazurDist (K : Set E) (L : Set E) ≤ (Module.finrank ℝ E : ℝ) := by
  set d := Module.finrank ℝ E
  have hB0 : (0 : E) ∈ interior (closedBall (0 : E) 1) :=
    mem_interior.mpr ⟨ball (0 : E) 1, ball_subset_closedBall, isOpen_ball,
      mem_ball_self zero_lt_one⟩
  have hKB := banachMazurSet_nonempty hK0 K.isBounded hB0 isBounded_closedBall
  have hBL := banachMazurSet_nonempty hB0 isBounded_closedBall hL0 L.isBounded
  have h1 := banachMazurDist_closedBall_le_sqrt_finrank K hKsym hK0
  have h2 := banachMazurDist_closedBall_le_sqrt_finrank L hLsym hL0
  rw [banachMazurDist_symm (L : Set E)] at h2
  calc
    banachMazurDist (K : Set E) (L : Set E)
      ≤ banachMazurDist (K : Set E) (closedBall (0 : E) 1) *
          banachMazurDist (closedBall (0 : E) 1) (L : Set E) :=
        banachMazurDist_mul_triangle hKB hBL
    _ ≤ Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) :=
        mul_le_mul h1 h2 (le_trans zero_le_one (one_le_banachMazurDist hBL)) (Real.sqrt_nonneg _)
    _ = (d : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg d)

/-- **John's Affine Banach–Mazur Bound (General Convex Bodies, Ball Lecture 3):**
for every `K : ConvexBody E` with nonempty interior in dimension `d ≥ 1`:
`affineBanachMazurDist K (closedBall 0 1) ≤ d`. -/
theorem affineBanachMazurDist_closedBall_le_finrank [FiniteDimensional ℝ E] [Nontrivial E]
    (K : ConvexBody E) (hint : (interior (K : Set E)).Nonempty) :
    affineBanachMazurDist (K : Set E) (closedBall (0 : E) 1) ≤ (Module.finrank ℝ E : ℝ) := by
  set d := Module.finrank ℝ E
  have hd_ge1 : (1 : ℝ) ≤ d := by exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E))
  have hd_pos : (0 : ℝ) < d := lt_of_lt_of_le zero_lt_one hd_ge1
  obtain ⟨A, _, hBsub, hsubB⟩ := john_theorem K hint
  let x₀ : E := A.symm 0
  have hshift : (fun z => z - x₀) '' (K : Set E) = A.linear.symm '' (A '' (K : Set E)) := by
    ext y
    simp only [mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨A z, ⟨z, hz, rfl⟩, ?_⟩
      have hsub : A z - A x₀ = A.linear (z - x₀) := by
        have h := A.map_vadd x₀ (z - x₀)
        simp only [vadd_eq_add, sub_add_cancel] at h
        rw [h, add_sub_cancel_right]
      have hAx₀ : A x₀ = 0 := A.apply_symm_apply 0
      rw [hAx₀, sub_zero] at hsub
      rw [hsub, LinearEquiv.symm_apply_apply]
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨z, hz, ?_⟩
      have hsub : A z - A x₀ = A.linear (z - x₀) := by
        have h := A.map_vadd x₀ (z - x₀)
        simp only [vadd_eq_add, sub_add_cancel] at h
        rw [h, add_sub_cancel_right]
      have hAx₀ : A x₀ = 0 := A.apply_symm_apply 0
      rw [hAx₀, sub_zero] at hsub
      rw [hsub, LinearEquiv.symm_apply_apply]
  let S : E ≃ₗ[ℝ] E := (smulLinearEquiv hd_pos.ne').trans A.linear.symm
  have hmem : (d : ℝ) ∈ affineBanachMazurSet (K : Set E) (closedBall (0 : E) 1) := by
    refine ⟨hd_ge1, S, x₀, 0, ?_, ?_⟩
    · rw [hshift]
      rintro _ ⟨w, hw, rfl⟩
      rcases hsubB hw with ⟨u, hu, huw⟩
      refine ⟨u, ⟨u, hu, sub_zero u⟩, ?_⟩
      dsimp only [S]
      rw [LinearEquiv.trans_apply, smulLinearEquiv_apply, show (d : ℝ) • u = w from huw]
    · rw [hshift]
      rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨A.linear.symm u, ⟨u, hBsub hu, rfl⟩, ?_⟩
      dsimp only [S]
      rw [LinearEquiv.trans_apply, smulLinearEquiv_apply, sub_zero, map_smul]
  exact csInf_le (bddBelow_affineBanachMazurSet _ _) hmem

/-- **John's Affine Banach–Mazur Diameter Bound (General Convex Bodies):**
for any two `K, L : ConvexBody E` with nonempty interiors in dimension `d ≥ 1`:
`affineBanachMazurDist K L ≤ d ^ 2`. -/
theorem affineBanachMazurDist_le_finrank_sq [FiniteDimensional ℝ E] [Nontrivial E]
    (K L : ConvexBody E)
    (hKint : (interior (K : Set E)).Nonempty) (hLint : (interior (L : Set E)).Nonempty) :
    affineBanachMazurDist (K : Set E) (L : Set E) ≤ (Module.finrank ℝ E : ℝ) ^ 2 := by
  set d := Module.finrank ℝ E
  have hBint : (interior (closedBall (0 : E) 1)).Nonempty :=
    ⟨0, mem_interior.mpr ⟨ball (0 : E) 1, ball_subset_closedBall, isOpen_ball,
      mem_ball_self zero_lt_one⟩⟩
  have hKB := affineBanachMazurSet_nonempty hKint K.isBounded hBint isBounded_closedBall
  have hBL := affineBanachMazurSet_nonempty hBint isBounded_closedBall hLint L.isBounded
  have h1 := affineBanachMazurDist_closedBall_le_finrank K hKint
  have h2 := affineBanachMazurDist_closedBall_le_finrank L hLint
  rw [affineBanachMazurDist_symm (L : Set E)] at h2
  calc
    affineBanachMazurDist (K : Set E) (L : Set E)
      ≤ affineBanachMazurDist (K : Set E) (closedBall (0 : E) 1) *
          affineBanachMazurDist (closedBall (0 : E) 1) (L : Set E) :=
        affineBanachMazurDist_mul_triangle hKB hBL
    _ ≤ (d : ℝ) * (d : ℝ) :=
        mul_le_mul h1 h2 (le_trans zero_le_one (one_le_affineBanachMazurDist hBL)) (Nat.cast_nonneg d)
    _ = (d : ℝ) ^ 2 := (sq _).symm

/-- **Attainment of Linear Banach–Mazur Distance:**
if `K, L : ConvexBody E` contain `0` in their interiors, then `banachMazurDist K L` is attained
by an actual linear equivalence `T : E ≃ₗ[ℝ] E`. -/
theorem banachMazurDist_attained [FiniteDimensional ℝ E]
    (K L : ConvexBody E)
    (hK0 : (0 : E) ∈ interior (K : Set E)) (hL0 : (0 : E) ∈ interior (L : Set E)) :
    ∃ T : E ≃ₗ[ℝ] E,
      (K : Set E) ⊆ T '' (L : Set E) ∧
      T '' (L : Set E) ⊆ banachMazurDist (K : Set E) (L : Set E) • (K : Set E) := by
  have hne := banachMazurSet_nonempty hK0 K.isBounded hL0 L.isBounded
  set d₀ := banachMazurDist (K : Set E) (L : Set E)
  have hd₀_ge1 : 1 ≤ d₀ := one_le_banachMazurDist hne
  have hex_seq : ∀ n : ℕ, ∃ r ∈ banachMazurSet (K : Set E) (L : Set E),
      r < d₀ + 1 / ((n : ℝ) + 1) := fun n =>
    Real.lt_sInf_add_pos hne (by positivity)
  choose r hr_mem hr_lt using hex_seq
  have hex_T : ∀ n : ℕ, ∃ T : E ≃ₗ[ℝ] E,
      (K : Set E) ⊆ T '' (L : Set E) ∧ T '' (L : Set E) ⊆ r n • (K : Set E) :=
    fun n => (hr_mem n).2
  choose T hKT hTL using hex_T
  obtain ⟨rK, hrK, hballK⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hK0)
  obtain ⟨rL, hrL, hballL⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hL0)
  obtain ⟨RK, hRK⟩ := K.isBounded.subset_closedBall (0 : E)
  obtain ⟨RL, hRL⟩ := L.isBounded.subset_closedBall (0 : E)
  have hRK_nn : 0 ≤ RK := (norm_nonneg (0 : E)).trans (mem_closedBall_zero_iff.mp (hRK (interior_subset hK0)))
  have hRL_nn : 0 ≤ RL := (norm_nonneg (0 : E)).trans (mem_closedBall_zero_iff.mp (hRL (interior_subset hL0)))
  set aK := rK / 2
  set aL := rL / 2
  have haK : 0 < aK := half_pos hrK
  have haL : 0 < aL := half_pos hrL
  have hcbK : closedBall (0 : E) aK ⊆ (K : Set E) := (closedBall_subset_ball (half_lt_self hrK)).trans hballK
  have hcbL : closedBall (0 : E) aL ⊆ (L : Set E) := (closedBall_subset_ball (half_lt_self hrL)).trans hballL
  have hr_bdd : ∀ n, r n ≤ d₀ + 1 := fun n => by
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by positivity)
    linarith [hr_lt n]
  set C₁ := (d₀ + 1) * RK / aL
  set C₂ := RL / aK
  have hT_bdd : ∀ n, ‖(T n).toContinuousLinearMap‖ ≤ C₁ := fun n => by
    refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (mul_nonneg (by linarith) hRK_nn) haL.le) fun x => ?_
    by_cases hx : x = 0
    · simp [hx]
    · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      let y : E := (aL / ‖x‖) • x
      have hyL : y ∈ (L : Set E) := hcbL (by
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
          abs_of_pos (div_pos haL hxn), div_mul_cancel₀ _ hxn.ne'])
      rcases hTL n ⟨y, hyL, rfl⟩ with ⟨k, hk, hkn⟩
      have hk_norm : ‖k‖ ≤ RK := mem_closedBall_zero_iff.mp (hRK hk)
      have hr_nn : 0 ≤ r n := le_trans zero_le_one (hr_mem n).1
      have hTy_norm : ‖T n y‖ ≤ (d₀ + 1) * RK := by
        change r n • k = T n y at hkn
        rw [← hkn, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr_nn]
        exact mul_le_mul (hr_bdd n) hk_norm (norm_nonneg k) (by linarith)
      have hscale : ‖T n y‖ = (aL / ‖x‖) * ‖T n x‖ := by
        dsimp only [y]; rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos haL hxn)]
      rw [hscale] at hTy_norm
      have h1 : aL * ‖T n x‖ ≤ (d₀ + 1) * RK * ‖x‖ := by
        have := mul_le_mul_of_nonneg_right hTy_norm hxn.le
        rw [mul_comm (aL / ‖x‖), mul_assoc, div_mul_cancel₀ _ hxn.ne', mul_comm] at this
        linarith
      calc
        ‖(T n).toContinuousLinearMap x‖ = (aL * ‖T n x‖) / aL := by
          change ‖T n x‖ = _; field_simp [haL.ne']
        _ ≤ ((d₀ + 1) * RK * ‖x‖) / aL := div_le_div_of_nonneg_right h1 haL.le
        _ = C₁ * ‖x‖ := by dsimp only [C₁]; ring
  have hTinv_bdd : ∀ n, ‖(T n).symm.toContinuousLinearMap‖ ≤ C₂ := fun n => by
    refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hRL_nn haK.le) fun x => ?_
    by_cases hx : x = 0
    · simp [hx]
    · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      let y : E := (aK / ‖x‖) • x
      have hyK : y ∈ (K : Set E) := hcbK (by
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
          abs_of_pos (div_pos haK hxn), div_mul_cancel₀ _ hxn.ne'])
      rcases hKT n hyK with ⟨l, hl, hTl⟩
      have hl_norm : ‖l‖ ≤ RL := mem_closedBall_zero_iff.mp (hRL hl)
      have hS_norm : ‖(T n).symm y‖ ≤ RL := by
        have : (T n).symm y = l := by rw [← hTl, (T n).symm_apply_apply]
        rwa [this]
      have hscale : ‖(T n).symm y‖ = (aK / ‖x‖) * ‖(T n).symm x‖ := by
        dsimp only [y]; rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos haK hxn)]
      rw [hscale] at hS_norm
      have h1 : aK * ‖(T n).symm x‖ ≤ RL * ‖x‖ := by
        have := mul_le_mul_of_nonneg_right hS_norm hxn.le
        rw [mul_comm (aK / ‖x‖), mul_assoc, div_mul_cancel₀ _ hxn.ne', mul_comm] at this
        linarith
      calc
        ‖(T n).symm.toContinuousLinearMap x‖ = (aK * ‖(T n).symm x‖) / aK := by
          change ‖(T n).symm x‖ = _; field_simp [haK.ne']
        _ ≤ (RL * ‖x‖) / aK := div_le_div_of_nonneg_right h1 haK.le
        _ = C₂ * ‖x‖ := by dsimp only [C₂]; ring
  let seq : ℕ → (E →L[ℝ] E) × (E →L[ℝ] E) :=
    fun n => ((T n).toContinuousLinearMap, (T n).symm.toContinuousLinearMap)
  have hcomp : IsCompact (closedBall (0 : E →L[ℝ] E) C₁ ×ˢ closedBall (0 : E →L[ℝ] E) C₂) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hmem_seq : ∀ n, seq n ∈ closedBall (0 : E →L[ℝ] E) C₁ ×ˢ closedBall (0 : E →L[ℝ] E) C₂ :=
    fun n => ⟨mem_closedBall_zero_iff.mpr (hT_bdd n), mem_closedBall_zero_iff.mpr (hTinv_bdd n)⟩
  obtain ⟨⟨A, B⟩, _, φ, hφ_mono, htend⟩ := hcomp.tendsto_subseq hmem_seq
  have htA : Tendsto (fun n => (T (φ n)).toContinuousLinearMap) atTop (𝓝 A) :=
    continuous_fst.continuousAt.tendsto.comp htend
  have htB : Tendsto (fun n => (T (φ n)).symm.toContinuousLinearMap) atTop (𝓝 B) :=
    continuous_snd.continuousAt.tendsto.comp htend
  have hAB : ∀ x, A (B x) = x := fun x => by
    have hBx : Tendsto (fun n => (T (φ n)).symm.toContinuousLinearMap x) atTop (𝓝 (B x)) :=
      (ContinuousLinearMap.apply ℝ E x).continuous.continuousAt.tendsto.comp htB
    have hcomp_t : Tendsto (fun n => (T (φ n)).toContinuousLinearMap ((T (φ n)).symm.toContinuousLinearMap x))
        atTop (𝓝 (A (B x))) := tendsto_clm_apply htA hBx
    have hconst : (fun n => (T (φ n)).toContinuousLinearMap ((T (φ n)).symm.toContinuousLinearMap x)) =
        fun _ => x := funext fun n => (T (φ n)).apply_symm_apply x
    rw [hconst] at hcomp_t
    exact tendsto_nhds_unique hcomp_t tendsto_const_nhds
  have hBA : ∀ x, B (A x) = x := fun x => by
    have hAx : Tendsto (fun n => (T (φ n)).toContinuousLinearMap x) atTop (𝓝 (A x)) :=
      (ContinuousLinearMap.apply ℝ E x).continuous.continuousAt.tendsto.comp htA
    have hcomp_t : Tendsto (fun n => (T (φ n)).symm.toContinuousLinearMap ((T (φ n)).toContinuousLinearMap x))
        atTop (𝓝 (B (A x))) := tendsto_clm_apply htB hAx
    have hconst : (fun n => (T (φ n)).symm.toContinuousLinearMap ((T (φ n)).toContinuousLinearMap x)) =
        fun _ => x := funext fun n => (T (φ n)).symm_apply_apply x
    rw [hconst] at hcomp_t
    exact tendsto_nhds_unique hcomp_t tendsto_const_nhds
  let Teq : E ≃ₗ[ℝ] E :=
    { toFun := A, invFun := B, left_inv := hBA, right_inv := hAB,
      map_add' := A.map_add, map_smul' := A.map_smul }
  have htr : Tendsto (fun n => r (φ n)) atTop (𝓝 d₀) := by
    have ht_zero : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ_mono.tendsto_atTop
    have ht_upper : Tendsto (fun n : ℕ => d₀ + 1 / ((φ n : ℝ) + 1)) atTop (𝓝 d₀) := by
      simpa [add_zero] using (tendsto_const_nhds (x := d₀)).add ht_zero
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht_upper
      (fun n => csInf_le (bddBelow_banachMazurSet _ _) (hr_mem (φ n)))
      (fun n => (hr_lt (φ n)).le)
  refine ⟨Teq, ?_, ?_⟩
  · intro x hx
    refine ⟨B x, ?_, hAB x⟩
    have hBx_mem : ∀ n, (T (φ n)).symm x ∈ (L : Set E) := fun n => by
      rcases hKT (φ n) hx with ⟨l, hl, hTl⟩
      have : (T (φ n)).symm x = l := by rw [← hTl, (T (φ n)).symm_apply_apply]
      rwa [this]
    have htBx : Tendsto (fun n => (T (φ n)).symm x) atTop (𝓝 (B x)) :=
      (ContinuousLinearMap.apply ℝ E x).continuous.continuousAt.tendsto.comp htB
    exact L.isClosed.mem_of_tendsto htBx (Filter.Eventually.of_forall hBx_mem)
  · rintro _ ⟨y, hy, rfl⟩
    have hd₀_pos : 0 < d₀ := lt_of_lt_of_le zero_lt_one hd₀_ge1
    refine ⟨d₀⁻¹ • A y, ?_, by dsimp only; rw [smul_smul, mul_inv_cancel₀ hd₀_pos.ne', one_smul]; rfl⟩
    have hmem_n : ∀ n, (r (φ n))⁻¹ • T (φ n) y ∈ (K : Set E) := fun n => by
      rcases hTL (φ n) ⟨y, hy, rfl⟩ with ⟨k, hk, hkn⟩
      have hrpos : 0 < r (φ n) := lt_of_lt_of_le zero_lt_one (hr_mem (φ n)).1
      change r (φ n) • k = T (φ n) y at hkn
      rw [← hkn, smul_smul, inv_mul_cancel₀ hrpos.ne', one_smul]
      exact hk
    have ht_inv : Tendsto (fun n => (r (φ n))⁻¹ • T (φ n) y) atTop (𝓝 (d₀⁻¹ • A y)) :=
      (htr.inv₀ hd₀_pos.ne').smul
        ((ContinuousLinearMap.apply ℝ E y).continuous.continuousAt.tendsto.comp htA)
    exact K.isClosed.mem_of_tendsto ht_inv (Filter.Eventually.of_forall hmem_n)

/-- **Attainment of Affine Banach–Mazur Distance:**
if `K, L : ConvexBody E` have nonempty interiors, then `affineBanachMazurDist K L` is attained
by an actual linear equivalence `T : E ≃ₗ[ℝ] E` and centers `x, y ∈ E`. -/
theorem affineBanachMazurDist_attained [FiniteDimensional ℝ E]
    (K L : ConvexBody E)
    (hKint : (interior (K : Set E)).Nonempty) (hLint : (interior (L : Set E)).Nonempty) :
    ∃ (T : E ≃ₗ[ℝ] E) (x y : E),
      (fun z => z - x) '' (K : Set E) ⊆ T '' ((fun z => z - y) '' (L : Set E)) ∧
      T '' ((fun z => z - y) '' (L : Set E)) ⊆
        affineBanachMazurDist (K : Set E) (L : Set E) • ((fun z => z - x) '' (K : Set E)) := by
  have hne := affineBanachMazurSet_nonempty hKint K.isBounded hLint L.isBounded
  set d₀ := affineBanachMazurDist (K : Set E) (L : Set E)
  have hd₀_ge1 : 1 ≤ d₀ := one_le_affineBanachMazurDist hne
  have hd₀_pos : 0 < d₀ := lt_of_lt_of_le zero_lt_one hd₀_ge1
  have hcenter_mem : ∀ {r : ℝ} {T : E ≃ₗ[ℝ] E} {x y : E},
      1 < r →
      (fun z => z - x) '' (K : Set E) ⊆ T '' ((fun z => z - y) '' (L : Set E)) →
      T '' ((fun z => z - y) '' (L : Set E)) ⊆ r • ((fun z => z - x) '' (K : Set E)) →
      x ∈ (K : Set E) ∧ y ∈ (L : Set E) := by
    intro r T x y hr1 h1 h2
    have hr_pos : 0 < r := lt_trans zero_lt_one hr1
    have hKsub : (fun z => z - x) '' (K : Set E) ⊆ r • ((fun z => z - x) '' (K : Set E)) :=
      h1.trans h2
    have h0_Kx : (0 : E) ∈ (fun z => z - x) '' (K : Set E) := by
      obtain ⟨k₀, hk₀⟩ := K.nonempty
      have hpow : ∀ m : ℕ, (r⁻¹) ^ m • (k₀ - x) ∈ (fun z => z - x) '' (K : Set E) := by
        intro m
        induction m with
        | zero =>
          simp only [pow_zero, one_smul]
          exact ⟨k₀, hk₀, rfl⟩
        | succ m ihm =>
          rcases hKsub ihm with ⟨w, hw, hw_eq⟩
          have heq : (r⁻¹) ^ (m + 1) • (k₀ - x) = w := by
            have h1' : r • w = (r⁻¹) ^ m • (k₀ - x) := hw_eq
            calc
              (r⁻¹) ^ (m + 1) • (k₀ - x) = r⁻¹ • ((r⁻¹) ^ m • (k₀ - x)) := by
                rw [pow_succ', mul_smul]
              _ = r⁻¹ • (r • w) := by rw [← h1']
              _ = w := by rw [smul_smul, inv_mul_cancel₀ hr_pos.ne', one_smul]
          rwa [heq]
      have htend : Tendsto (fun m : ℕ => (r⁻¹) ^ m • (k₀ - x)) atTop (𝓝 (0 : E)) := by
        have hlt1 : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr1
        have h0 : Tendsto (fun m : ℕ => (r⁻¹) ^ m) atTop (𝓝 (0 : ℝ)) :=
          tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hr_pos.le) hlt1
        simpa using h0.smul_const (k₀ - x)
      have hcl : IsClosed ((fun z => z - x) '' (K : Set E)) :=
        (K.isCompact.image (continuous_id.sub continuous_const)).isClosed
      exact hcl.mem_of_tendsto htend (Filter.Eventually.of_forall hpow)
    have hxK : x ∈ (K : Set E) := by
      rcases h0_Kx with ⟨z, hz, hzx⟩
      have : z = x := sub_eq_zero.mp hzx
      rwa [← this]
    have hyL : y ∈ (L : Set E) := by
      rcases h1 h0_Kx with ⟨_, ⟨z, hz, rfl⟩, hTz⟩
      have : z - y = 0 := T.injective (by rw [map_zero]; exact hTz)
      have hzy : z = y := sub_eq_zero.mp this
      rwa [← hzy]
    exact ⟨hxK, hyL⟩
  have hex_seq : ∀ n : ℕ, ∃ r ∈ affineBanachMazurSet (K : Set E) (L : Set E),
      1 < r ∧ r < d₀ + 1 / ((n : ℝ) + 1) := fun n => by
    obtain ⟨r₀, hr₀, hr₀_lt⟩ := Real.lt_sInf_add_pos hne (show 0 < 1 / (2 * ((n : ℝ) + 1)) by positivity)
    by_cases h1 : 1 < r₀
    · refine ⟨r₀, hr₀, h1, hr₀_lt.trans (by
        have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have : 1 / (2 * ((n : ℝ) + 1)) < 1 / ((n : ℝ) + 1) := by
          rw [div_lt_div_iff₀ (by positivity) hpos]; linarith
        change sInf (affineBanachMazurSet (K : Set E) (L : Set E)) + 1 / (2 * ((n : ℝ) + 1)) <
          sInf (affineBanachMazurSet (K : Set E) (L : Set E)) + 1 / ((n : ℝ) + 1)
        linarith)⟩
    · have hr₀1 : r₀ = 1 := le_antisymm (not_lt.mp h1) hr₀.1
      set ε := 1 / (2 * ((n : ℝ) + 1))
      have hε : 0 < ε := by positivity
      rcases hr₀ with ⟨_, T, x, y, hsub1, hsub2⟩
      obtain ⟨k₀, hk₀⟩ := K.nonempty
      rcases hsub1 ⟨k₀, hk₀, rfl⟩ with ⟨_, ⟨l₀, hl₀, rfl⟩, hkl⟩
      dsimp only at hkl
      have h1ε : (1 + ε) ∈ affineBanachMazurSet (K : Set E) (L : Set E) := by
        refine ⟨by linarith, T, k₀, l₀, ?_, ?_⟩
        · rintro _ ⟨k, hk, rfl⟩
          rcases hsub1 ⟨k, hk, rfl⟩ with ⟨_, ⟨l, hl, rfl⟩, hTkl⟩
          dsimp only at hTkl
          refine ⟨l - l₀, ⟨l, hl, rfl⟩, ?_⟩
          have hsub : l - l₀ = (l - y) - (l₀ - y) := by abel
          dsimp only
          rw [hsub, map_sub, hTkl, hkl]; abel
        · rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
          rcases hsub2 ⟨l - y, ⟨l, hl, rfl⟩, rfl⟩ with ⟨_, ⟨k, hk, rfl⟩, hTlk⟩
          dsimp only at hTlk
          rw [hr₀1, one_smul] at hTlk
          have hTll : T (l - l₀) = k - k₀ := by
            have hsub : l - l₀ = (l - y) - (l₀ - y) := by abel
            rw [hsub, map_sub, ← hTlk, hkl]; abel
          have hmem_conv : (1 + ε)⁻¹ • (k - k₀) ∈ (fun z => z - k₀) '' (K : Set E) := by
            have hconv := K.convex hk hk₀ (a := (1 + ε)⁻¹) (b := 1 - (1 + ε)⁻¹)
              (inv_nonneg.mpr (by linarith))
              (sub_nonneg.mpr (inv_le_one_of_one_le₀ (by linarith)))
              (add_sub_cancel _ _)
            refine ⟨(1 + ε)⁻¹ • k + (1 - (1 + ε)⁻¹) • k₀, hconv, ?_⟩
            dsimp only
            rw [sub_smul, one_smul, smul_sub]; abel
          refine ⟨(1 + ε)⁻¹ • (k - k₀), hmem_conv, ?_⟩
          change (1 + ε) • ((1 + ε)⁻¹ • (k - k₀)) = T (l - l₀)
          rw [hTll, smul_smul, mul_inv_cancel₀ (by linarith), one_smul]
      refine ⟨1 + ε, h1ε, by linarith, ?_⟩
      have hlt_eps : ε < 1 / ((n : ℝ) + 1) := by
        dsimp only [ε]
        have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        rw [div_lt_div_iff₀ (by positivity) hpos]; linarith
      linarith
  choose r hr_mem hr_gt1 hr_lt using hex_seq
  have hex_data : ∀ n : ℕ, ∃ (T : E ≃ₗ[ℝ] E) (x y : E),
      (fun z => z - x) '' (K : Set E) ⊆ T '' ((fun z => z - y) '' (L : Set E)) ∧
      T '' ((fun z => z - y) '' (L : Set E)) ⊆ r n • ((fun z => z - x) '' (K : Set E)) :=
    fun n => (hr_mem n).2
  choose T x y hsub1 hsub2 using hex_data
  have hxy_mem : ∀ n, x n ∈ (K : Set E) ∧ y n ∈ (L : Set E) :=
    fun n => hcenter_mem (hr_gt1 n) (hsub1 n) (hsub2 n)
  obtain ⟨cK, hcK⟩ := hKint
  obtain ⟨cL, hcL⟩ := hLint
  obtain ⟨rK, hrK, hballK⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hcK)
  obtain ⟨rL, hrL, hballL⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hcL)
  set DK : ℝ := Metric.diam (K : Set E)
  set DL : ℝ := Metric.diam (L : Set E)
  set aK := rK / 2
  set aL := rL / 2
  have haK : 0 < aK := half_pos hrK
  have haL : 0 < aL := half_pos hrL
  have hr_bdd : ∀ n, r n ≤ d₀ + 1 := fun n => by
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by positivity)
    linarith [hr_lt n]
  set C₁ := (d₀ + 1) * DK / aL
  set C₂ := DL / aK
  have hT_bdd : ∀ n, ‖(T n).toContinuousLinearMap‖ ≤ C₁ := fun n => by
    refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (mul_nonneg (by linarith) Metric.diam_nonneg) haL.le) fun w => ?_
    by_cases hw : w = 0
    · simp [hw]
    · have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
      let u : E := (aL / ‖w‖) • w
      have hu_norm : ‖u‖ = aL := by
        dsimp only [u]; rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos haL hwn), div_mul_cancel₀ _ hwn.ne']
      have hcL_mem : cL ∈ (L : Set E) := interior_subset hcL
      have hcu_mem : cL + u ∈ (L : Set E) := hballL (by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hu_norm]; exact half_lt_self hrL)
      rcases hsub2 n ⟨cL - y n, ⟨cL, hcL_mem, rfl⟩, rfl⟩ with ⟨_, ⟨k₁, hk₁, rfl⟩, h1⟩
      rcases hsub2 n ⟨(cL + u) - y n, ⟨cL + u, hcu_mem, rfl⟩, rfl⟩ with ⟨_, ⟨k₂, hk₂, rfl⟩, h2⟩
      have hTu : T n u = r n • (k₂ - k₁) := by
        have hdiff : u = ((cL + u) - y n) - (cL - y n) := by abel
        rw [hdiff, map_sub]
        change r n • (k₁ - x n) = T n (cL - y n) at h1
        change r n • (k₂ - x n) = T n (cL + u - y n) at h2
        rw [← h1, ← h2, ← smul_sub]
        congr 1; abel
      have hk_dist : ‖k₂ - k₁‖ ≤ DK := by
        simpa [dist_eq_norm] using Metric.dist_le_diam_of_mem K.isBounded hk₂ hk₁
      have hTu_norm : ‖T n u‖ ≤ (d₀ + 1) * DK := by
        rw [hTu, norm_smul, Real.norm_eq_abs, abs_of_pos (lt_trans zero_lt_one (hr_gt1 n))]
        exact mul_le_mul (hr_bdd n) hk_dist (norm_nonneg _) (by linarith)
      have hscale : ‖T n u‖ = (aL / ‖w‖) * ‖T n w‖ := by
        dsimp only [u]; rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos haL hwn)]
      rw [hscale] at hTu_norm
      have hmul : aL * ‖T n w‖ ≤ (d₀ + 1) * DK * ‖w‖ := by
        have := mul_le_mul_of_nonneg_right hTu_norm hwn.le
        rw [mul_comm (aL / ‖w‖), mul_assoc, div_mul_cancel₀ _ hwn.ne', mul_comm] at this
        linarith
      calc
        ‖(T n).toContinuousLinearMap w‖ = (aL * ‖T n w‖) / aL := by
          change ‖T n w‖ = _; field_simp [haL.ne']
        _ ≤ ((d₀ + 1) * DK * ‖w‖) / aL := div_le_div_of_nonneg_right hmul haL.le
        _ = C₁ * ‖w‖ := by dsimp only [C₁]; ring
  have hTinv_bdd : ∀ n, ‖(T n).symm.toContinuousLinearMap‖ ≤ C₂ := fun n => by
    refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg Metric.diam_nonneg haK.le) fun w => ?_
    by_cases hw : w = 0
    · simp [hw]
    · have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
      let u : E := (aK / ‖w‖) • w
      have hu_norm : ‖u‖ = aK := by
        dsimp only [u]; rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos haK hwn), div_mul_cancel₀ _ hwn.ne']
      have hcK_mem : cK ∈ (K : Set E) := interior_subset hcK
      have hcu_mem : cK + u ∈ (K : Set E) := hballK (by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hu_norm]; exact half_lt_self hrK)
      rcases hsub1 n ⟨cK, hcK_mem, rfl⟩ with ⟨_, ⟨l₁, hl₁, rfl⟩, h1⟩
      rcases hsub1 n ⟨cK + u, hcu_mem, rfl⟩ with ⟨_, ⟨l₂, hl₂, rfl⟩, h2⟩
      dsimp only at h1 h2
      have hSu : (T n).symm u = l₂ - l₁ := by
        have hdiff : u = ((cK + u) - x n) - (cK - x n) := by abel
        rw [hdiff, map_sub]
        have h1' : (T n).symm (cK - x n) = l₁ - y n := by rw [← h1, (T n).symm_apply_apply]
        have h2' : (T n).symm ((cK + u) - x n) = l₂ - y n := by rw [← h2, (T n).symm_apply_apply]
        rw [h1', h2']; abel
      have hl_dist : ‖l₂ - l₁‖ ≤ DL := by
        simpa [dist_eq_norm] using Metric.dist_le_diam_of_mem L.isBounded hl₂ hl₁
      have hSu_norm : ‖(T n).symm u‖ ≤ DL := by rwa [hSu]
      have hscale : ‖(T n).symm u‖ = (aK / ‖w‖) * ‖(T n).symm w‖ := by
        dsimp only [u]; rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos haK hwn)]
      rw [hscale] at hSu_norm
      have hmul : aK * ‖(T n).symm w‖ ≤ DL * ‖w‖ := by
        have := mul_le_mul_of_nonneg_right hSu_norm hwn.le
        rw [mul_comm (aK / ‖w‖), mul_assoc, div_mul_cancel₀ _ hwn.ne', mul_comm] at this
        linarith
      calc
        ‖(T n).symm.toContinuousLinearMap w‖ = (aK * ‖(T n).symm w‖) / aK := by
          change ‖(T n).symm w‖ = _; field_simp [haK.ne']
        _ ≤ (DL * ‖w‖) / aK := div_le_div_of_nonneg_right hmul haK.le
        _ = C₂ * ‖w‖ := by dsimp only [C₂]; ring
  let seq : ℕ → ((E →L[ℝ] E) × (E →L[ℝ] E)) × (E × E) :=
    fun n => (((T n).toContinuousLinearMap, (T n).symm.toContinuousLinearMap), (x n, y n))
  have hcomp : IsCompact ((closedBall (0 : E →L[ℝ] E) C₁ ×ˢ closedBall (0 : E →L[ℝ] E) C₂) ×ˢ
      ((K : Set E) ×ˢ (L : Set E))) :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).prod (K.isCompact.prod L.isCompact)
  have hmem_seq : ∀ n, seq n ∈ (closedBall (0 : E →L[ℝ] E) C₁ ×ˢ closedBall (0 : E →L[ℝ] E) C₂) ×ˢ
      ((K : Set E) ×ˢ (L : Set E)) :=
    fun n => ⟨⟨mem_closedBall_zero_iff.mpr (hT_bdd n), mem_closedBall_zero_iff.mpr (hTinv_bdd n)⟩,
      ⟨(hxy_mem n).1, (hxy_mem n).2⟩⟩
  obtain ⟨⟨⟨A, B⟩, ⟨x₀, y₀⟩⟩, _, φ, hφ_mono, htend⟩ := hcomp.tendsto_subseq hmem_seq
  have htA : Tendsto (fun n => (T (φ n)).toContinuousLinearMap) atTop (𝓝 A) :=
    (continuous_fst.comp continuous_fst).continuousAt.tendsto.comp htend
  have htB : Tendsto (fun n => (T (φ n)).symm.toContinuousLinearMap) atTop (𝓝 B) :=
    (continuous_snd.comp continuous_fst).continuousAt.tendsto.comp htend
  have htx : Tendsto (fun n => x (φ n)) atTop (𝓝 x₀) :=
    (continuous_fst.comp continuous_snd).continuousAt.tendsto.comp htend
  have hty : Tendsto (fun n => y (φ n)) atTop (𝓝 y₀) :=
    (continuous_snd.comp continuous_snd).continuousAt.tendsto.comp htend
  have hAB : ∀ w, A (B w) = w := fun w => by
    have hBw : Tendsto (fun n => (T (φ n)).symm.toContinuousLinearMap w) atTop (𝓝 (B w)) :=
      (ContinuousLinearMap.apply ℝ E w).continuous.continuousAt.tendsto.comp htB
    have hcomp_t := tendsto_clm_apply htA hBw
    have hconst : (fun n => (T (φ n)).toContinuousLinearMap ((T (φ n)).symm.toContinuousLinearMap w)) =
        fun _ => w := funext fun n => (T (φ n)).apply_symm_apply w
    rw [hconst] at hcomp_t
    exact tendsto_nhds_unique hcomp_t tendsto_const_nhds
  have hBA : ∀ w, B (A w) = w := fun w => by
    have hAw : Tendsto (fun n => (T (φ n)).toContinuousLinearMap w) atTop (𝓝 (A w)) :=
      (ContinuousLinearMap.apply ℝ E w).continuous.continuousAt.tendsto.comp htA
    have hcomp_t := tendsto_clm_apply htB hAw
    have hconst : (fun n => (T (φ n)).symm.toContinuousLinearMap ((T (φ n)).toContinuousLinearMap w)) =
        fun _ => w := funext fun n => (T (φ n)).symm_apply_apply w
    rw [hconst] at hcomp_t
    exact tendsto_nhds_unique hcomp_t tendsto_const_nhds
  let Teq : E ≃ₗ[ℝ] E :=
    { toFun := A, invFun := B, left_inv := hBA, right_inv := hAB,
      map_add' := A.map_add, map_smul' := A.map_smul }
  have htr : Tendsto (fun n => r (φ n)) atTop (𝓝 d₀) := by
    have ht_zero : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ_mono.tendsto_atTop
    have ht_upper : Tendsto (fun n : ℕ => d₀ + 1 / ((φ n : ℝ) + 1)) atTop (𝓝 d₀) := by
      simpa [add_zero] using (tendsto_const_nhds (x := d₀)).add ht_zero
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht_upper
      (fun n => csInf_le (bddBelow_affineBanachMazurSet _ _) (hr_mem (φ n)))
      (fun n => (hr_lt (φ n)).le)
  refine ⟨Teq, x₀, y₀, ?_, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩
    refine ⟨B (k - x₀), ⟨B (k - x₀) + y₀, ?_, add_sub_cancel_right _ _⟩, hAB (k - x₀)⟩
    have hmem_n : ∀ n, (T (φ n)).symm (k - x (φ n)) + y (φ n) ∈ (L : Set E) := fun n => by
      rcases hsub1 (φ n) ⟨k, hk, rfl⟩ with ⟨_, ⟨l, hl, rfl⟩, hTl⟩
      dsimp only at hTl
      have : (T (φ n)).symm (k - x (φ n)) = l - y (φ n) := by
        rw [← hTl, (T (φ n)).symm_apply_apply]
      rw [this, sub_add_cancel]
      exact hl
    have ht_arg : Tendsto (fun n => k - x (φ n)) atTop (𝓝 (k - x₀)) := tendsto_const_nhds.sub htx
    have ht_B := tendsto_clm_apply htB ht_arg
    exact L.isClosed.mem_of_tendsto (ht_B.add hty) (Filter.Eventually.of_forall hmem_n)
  · rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    refine ⟨d₀⁻¹ • A (l - y₀), ⟨d₀⁻¹ • A (l - y₀) + x₀, ?_, add_sub_cancel_right _ _⟩,
      by dsimp only; rw [smul_smul, mul_inv_cancel₀ hd₀_pos.ne', one_smul]; rfl⟩
    have hmem_n : ∀ n, (r (φ n))⁻¹ • T (φ n) (l - y (φ n)) + x (φ n) ∈ (K : Set E) := fun n => by
      rcases hsub2 (φ n) ⟨l - y (φ n), ⟨l, hl, rfl⟩, rfl⟩ with ⟨_, ⟨k, hk, rfl⟩, hTk⟩
      have hrpos : 0 < r (φ n) := lt_trans zero_lt_one (hr_gt1 (φ n))
      change r (φ n) • (k - x (φ n)) = T (φ n) (l - y (φ n)) at hTk
      rw [← hTk, smul_smul, inv_mul_cancel₀ hrpos.ne', one_smul, sub_add_cancel]
      exact hk
    have ht_arg : Tendsto (fun n => l - y (φ n)) atTop (𝓝 (l - y₀)) := tendsto_const_nhds.sub hty
    have ht_A := tendsto_clm_apply htA ht_arg
    have ht_all := ((htr.inv₀ hd₀_pos.ne').smul ht_A).add htx
    exact K.isClosed.mem_of_tendsto ht_all (Filter.Eventually.of_forall hmem_n)

/-- Helper: evaluation `K ↦ supportFn K u` is continuous on `ConvexBody E`. -/
private lemma continuous_supportFn_eval [FiniteDimensional ℝ E] (u : E) :
    Continuous (fun B : ConvexBody E => supportFn B u) := by
  by_cases hu : u = 0
  · simp only [hu, supportFn_zero]; exact continuous_const
  · have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
    refine (LipschitzWith.of_dist_le_mul (K := ⟨‖u‖, norm_nonneg u⟩) fun A B => ?_).continuous
    rw [Real.dist_eq]
    let u₁ : E := ‖u‖⁻¹ • u
    have hu₁ : ‖u₁‖ ≤ 1 := by
      dsimp only [u₁]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hun), inv_mul_cancel₀ hun.ne']
    have hu_eq : u = ‖u‖ • u₁ := by
      dsimp only [u₁]; rw [smul_smul, mul_inv_cancel₀ hun.ne', one_smul]
    calc
      |supportFn A u - supportFn B u|
        = |‖u‖ * supportFn A u₁ - ‖u‖ * supportFn B u₁| := by
            conv_lhs => rw [hu_eq, supportFn_smul A hun.le, supportFn_smul B hun.le]
      _ = ‖u‖ * |supportFn A u₁ - supportFn B u₁| := by
            rw [← mul_sub, abs_mul, abs_of_pos hun]
      _ ≤ ‖u‖ * dist A B :=
            mul_le_mul_of_nonneg_left
              ((dist_le_iff_supportFn_sub_le dist_nonneg).mp le_rfl u₁ hu₁) hun.le

/-- Helper: Hausdorff convergence of bodies containing `closedBall 0 1` implies Banach–Mazur
distance converges to `1`. -/
lemma tendsto_banachMazurDist_one_of_tendsto_convexBody [FiniteDimensional ℝ E]
    {K : ℕ → ConvexBody E} {K₀ : ConvexBody E}
    (hB : ∀ n, closedBall (0 : E) 1 ⊆ (K n : Set E))
    (hB₀ : closedBall (0 : E) 1 ⊆ (K₀ : Set E))
    (htend : Tendsto K atTop (𝓝 K₀)) :
    Tendsto (fun n => banachMazurDist (K n : Set E) (K₀ : Set E)) atTop (𝓝 1) := by
  have hle : ∀ n, banachMazurDist (K n : Set E) (K₀ : Set E) ≤ (1 + dist (K n) K₀) ^ 2 := fun n => by
    set δ := dist (K n) K₀
    have hδ : 0 ≤ δ := dist_nonneg
    have h1δ : 1 ≤ 1 + δ := by linarith
    have h1δ_pos : 0 < 1 + δ := by linarith
    have hsub1 : (K n : Set E) ⊆ (1 + δ) • (K₀ : Set E) := by
      have hsup : ∀ u : E, supportFn (K n) u ≤ supportFn ((1 + δ) • K₀) u := fun u => by
        rw [supportFn_body_smul K₀ h1δ_pos.le]
        by_cases hu : u = 0
        · simp [hu]
        · have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
          let u₁ : E := ‖u‖⁻¹ • u
          have hu₁ : ‖u₁‖ = 1 := by
            dsimp only [u₁]
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hun), inv_mul_cancel₀ hun.ne']
          have hu_eq : u = ‖u‖ • u₁ := by
            dsimp only [u₁]; rw [smul_smul, mul_inv_cancel₀ hun.ne', one_smul]
          rw [hu_eq, supportFn_smul (K n) hun.le, supportFn_smul K₀ hun.le, mul_left_comm]
          refine mul_le_mul_of_nonneg_left ?_ hun.le
          have hdiff : |supportFn (K n) u₁ - supportFn K₀ u₁| ≤ δ :=
            (dist_le_iff_supportFn_sub_le dist_nonneg).mp le_rfl u₁ hu₁.le
          have hge1 : 1 ≤ supportFn K₀ u₁ := by
            have := inner_le_supportFn (hB₀ (mem_closedBall_zero_iff.mpr hu₁.le)) u₁
            rwa [real_inner_self_eq_norm_sq, hu₁, one_pow] at this
          have hmul : δ ≤ δ * supportFn K₀ u₁ := by
            simpa [mul_one] using mul_le_mul_of_nonneg_left hge1 hδ
          linarith [(abs_le.mp hdiff).2]
      have := (supportFn_le_iff_subset (K := K n) (L := (1 + δ) • K₀)).mp hsup
      simpa [ConvexBody.coe_smul] using this
    have hsub2 : (K₀ : Set E) ⊆ (1 + δ) • (K n : Set E) := by
      have hsup : ∀ u : E, supportFn K₀ u ≤ supportFn ((1 + δ) • K n) u := fun u => by
        rw [supportFn_body_smul (K n) h1δ_pos.le]
        by_cases hu : u = 0
        · simp [hu]
        · have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
          let u₁ : E := ‖u‖⁻¹ • u
          have hu₁ : ‖u₁‖ = 1 := by
            dsimp only [u₁]
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hun), inv_mul_cancel₀ hun.ne']
          have hu_eq : u = ‖u‖ • u₁ := by
            dsimp only [u₁]; rw [smul_smul, mul_inv_cancel₀ hun.ne', one_smul]
          rw [hu_eq, supportFn_smul K₀ hun.le, supportFn_smul (K n) hun.le, mul_left_comm]
          refine mul_le_mul_of_nonneg_left ?_ hun.le
          have hdiff : |supportFn (K n) u₁ - supportFn K₀ u₁| ≤ δ :=
            (dist_le_iff_supportFn_sub_le dist_nonneg).mp le_rfl u₁ hu₁.le
          have hge1 : 1 ≤ supportFn (K n) u₁ := by
            have := inner_le_supportFn (hB n (mem_closedBall_zero_iff.mpr hu₁.le)) u₁
            rwa [real_inner_self_eq_norm_sq, hu₁, one_pow] at this
          have hmul : δ ≤ δ * supportFn (K n) u₁ := by
            simpa [mul_one] using mul_le_mul_of_nonneg_left hge1 hδ
          linarith [(abs_le.mp hdiff).1]
      have := (supportFn_le_iff_subset (K := K₀) (L := (1 + δ) • K n)).mp hsup
      simpa [ConvexBody.coe_smul] using this
    have hmem : (1 + δ) ^ 2 ∈ banachMazurSet (K n : Set E) (K₀ : Set E) := by
      refine ⟨by nlinarith, smulLinearEquiv h1δ_pos.ne', ?_, ?_⟩
      · rwa [smulLinearEquiv_image]
      · rw [smulLinearEquiv_image]
        calc
          (1 + δ) • (K₀ : Set E) ⊆ (1 + δ) • ((1 + δ) • (K n : Set E)) := Set.smul_set_mono hsub2
          _ = (1 + δ) ^ 2 • (K n : Set E) := by rw [smul_smul, sq]
    exact csInf_le (bddBelow_banachMazurSet _ _) hmem
  have hge : ∀ n, 1 ≤ banachMazurDist (K n : Set E) (K₀ : Set E) := fun n => by
    have h0n : (0 : E) ∈ interior (K n : Set E) :=
      mem_interior.mpr ⟨ball (0 : E) 1, ball_subset_closedBall.trans (hB n), isOpen_ball,
        mem_ball_self zero_lt_one⟩
    have h00 : (0 : E) ∈ interior (K₀ : Set E) :=
      mem_interior.mpr ⟨ball (0 : E) 1, ball_subset_closedBall.trans hB₀, isOpen_ball,
        mem_ball_self zero_lt_one⟩
    exact one_le_banachMazurDist (banachMazurSet_nonempty h0n (K n).isBounded h00 K₀.isBounded)
  have ht_rhs : Tendsto (fun n => (1 + dist (K n) K₀) ^ 2) atTop (𝓝 (1 : ℝ)) := by
    have hdist : Tendsto (fun n => dist (K n) K₀) atTop (𝓝 (0 : ℝ)) :=
      tendsto_iff_dist_tendsto_zero.mp htend
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add hdist).pow 2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht_rhs hge hle

/-- **Compactness of the Origin-Symmetric Banach–Mazur Compactum (Ball, Lecture 4):**
every sequence of origin-symmetric convex bodies `K : ℕ → ConvexBody E` with `0 ∈ interior (K n)`
in dimension `d ≥ 1` has a subsequence converging in linear Banach–Mazur distance to an
origin-symmetric convex body `K₀` with `0 ∈ interior K₀`. -/
theorem exists_subseq_banachMazurDist_tendsto_one [FiniteDimensional ℝ E] [Nontrivial E]
    (K : ℕ → ConvexBody E)
    (hsym : ∀ n, IsOriginSymmetric (K n : Set E))
    (h0 : ∀ n, (0 : E) ∈ interior (K n : Set E)) :
    ∃ (K₀ : ConvexBody E) (φ : ℕ → ℕ),
      IsOriginSymmetric (K₀ : Set E) ∧ (0 : E) ∈ interior (K₀ : Set E) ∧
      StrictMono φ ∧
      Tendsto (fun n => banachMazurDist (K (φ n) : Set E) (K₀ : Set E)) atTop (𝓝 1) := by
  set d := Module.finrank ℝ E
  have hjohn : ∀ n, ∃ T : E ≃ₗ[ℝ] E,
      closedBall (0 : E) 1 ⊆ T '' (K n : Set E) ∧
      T '' (K n : Set E) ⊆ Real.sqrt (d : ℝ) • closedBall (0 : E) 1 := fun n => by
    obtain ⟨T, _, h1, h2⟩ := john_theorem_symmetric (K n) (hsym n) (h0 n)
    exact ⟨T, h1, h2⟩
  choose T hBsub hsubB using hjohn
  let L : ℕ → ConvexBody E := fun n => mapLinear (T n).toContinuousLinearMap (K n)
  have hL_sub : ∀ n, (L n : Set E) ⊆ closedBall (0 : E) (Real.sqrt (d : ℝ)) := fun n x hx => by
    have hx' : x ∈ Real.sqrt (d : ℝ) • closedBall (0 : E) 1 := hsubB n (by simpa [L] using hx)
    rcases hx' with ⟨u, hu, rfl⟩
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hu) (Real.sqrt_nonneg _)).trans_eq
      (mul_one _)
  obtain ⟨K₀, _, φ, hφ_mono, htend⟩ :=
    (isCompact_subset_closedBall (E := E) (Real.sqrt (d : ℝ))).tendsto_subseq hL_sub
  have hB_K₀ : closedBall (0 : E) 1 ⊆ (K₀ : Set E) := by
    have hsup : ∀ u : E, supportFn (bodyClosedBall (0 : E) zero_le_one) u ≤ supportFn K₀ u := fun u => by
      have ht_sup : Tendsto (fun n => supportFn (L (φ n)) u) atTop (𝓝 (supportFn K₀ u)) :=
        (continuous_supportFn_eval u).continuousAt.tendsto.comp htend
      exact ge_of_tendsto ht_sup (Filter.Eventually.of_forall fun n =>
        supportFn_mono (by simpa [L, coe_bodyClosedBall] using hBsub (φ n)) u)
    simpa [coe_bodyClosedBall] using
      (supportFn_le_iff_subset (K := bodyClosedBall (0 : E) zero_le_one) (L := K₀)).mp hsup
  have hK₀_sym : IsOriginSymmetric (K₀ : Set E) := by
    rw [isOriginSymmetric_convexBody_iff_supportFn]
    intro u
    have h1 : Tendsto (fun n => supportFn (L (φ n)) (-u)) atTop (𝓝 (supportFn K₀ (-u))) :=
      (continuous_supportFn_eval (-u)).continuousAt.tendsto.comp htend
    have h2 : Tendsto (fun n => supportFn (L (φ n)) u) atTop (𝓝 (supportFn K₀ u)) :=
      (continuous_supportFn_eval u).continuousAt.tendsto.comp htend
    have heq : (fun n => supportFn (L (φ n)) (-u)) = fun n => supportFn (L (φ n)) u := by
      ext n
      exact supportFn_neg_of_isOriginSymmetric
        (by rw [coe_mapLinear]; exact isOriginSymmetric_linearMap_image (T (φ n)).toLinearMap (hsym (φ n))) u
    rw [heq] at h1
    exact tendsto_nhds_unique h1 h2
  have hK₀_0 : (0 : E) ∈ interior (K₀ : Set E) :=
    mem_interior.mpr ⟨ball (0 : E) 1, ball_subset_closedBall.trans hB_K₀, isOpen_ball,
      mem_ball_self zero_lt_one⟩
  have ht_L := tendsto_banachMazurDist_one_of_tendsto_convexBody
    (K := fun n => L (φ n)) (K₀ := K₀)
    (fun n => by simpa [L] using hBsub (φ n)) hB_K₀ htend
  refine ⟨K₀, φ, hK₀_sym, hK₀_0, hφ_mono, ?_⟩
  refine ht_L.congr fun n => ?_
  have hLcoe : (L (φ n) : Set E) = (T (φ n)) '' (K (φ n) : Set E) := coe_mapLinear _ _
  rw [hLcoe]
  exact banachMazurDist_linearEquiv_left (K (φ n) : Set E) (K₀ : Set E) (T (φ n))

/-- **Compactness of the General Affine Banach–Mazur Compactum:**
every sequence of convex bodies `K : ℕ → ConvexBody E` with nonempty interiors in dimension `d ≥ 1`
has a subsequence converging in affine Banach–Mazur distance to a convex body `K₀` with nonempty
interior. -/
theorem exists_subseq_affineBanachMazurDist_tendsto_one [FiniteDimensional ℝ E] [Nontrivial E]
    (K : ℕ → ConvexBody E) (hint : ∀ n, (interior (K n : Set E)).Nonempty) :
    ∃ (K₀ : ConvexBody E) (φ : ℕ → ℕ),
      (interior (K₀ : Set E)).Nonempty ∧ StrictMono φ ∧
      Tendsto (fun n => affineBanachMazurDist (K (φ n) : Set E) (K₀ : Set E)) atTop (𝓝 1) := by
  set d := Module.finrank ℝ E
  have hjohn : ∀ n, ∃ A : E ≃ᵃ[ℝ] E,
      closedBall (0 : E) 1 ⊆ A '' (K n : Set E) ∧
      A '' (K n : Set E) ⊆ (d : ℝ) • closedBall (0 : E) 1 := fun n => by
    obtain ⟨A, _, h1, h2⟩ := john_theorem (K n) (hint n)
    exact ⟨A, h1, h2⟩
  choose A hBsub hsubB using hjohn
  let L : ℕ → ConvexBody E :=
    fun n => mapLinear (A n).linear.toContinuousLinearMap (K n) + bodySingleton ((A n) 0)
  have hL_coe : ∀ n, (L n : Set E) = (A n) '' (K n : Set E) := fun n => by
    ext y
    simp only [L, ConvexBody.coe_add, coe_mapLinear, coe_bodySingleton, Set.mem_add,
      Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, rfl, rfl⟩
      refine ⟨x, hx, ?_⟩
      have h := (A n).map_vadd 0 x
      simp only [vadd_eq_add, add_zero] at h
      change (A n) x = (A n).linear x + (A n) 0
      rw [h, add_comm]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(A n).linear x, ⟨x, hx, rfl⟩, (A n) 0, rfl, ?_⟩
      have h := (A n).map_vadd 0 x
      simp only [vadd_eq_add, add_zero] at h
      change (A n).linear x + (A n) 0 = (A n) x
      rw [h, add_comm]
  have hL_sub : ∀ n, (L n : Set E) ⊆ closedBall (0 : E) (d : ℝ) := fun n x hx => by
    rw [hL_coe n] at hx
    rcases hsubB n hx with ⟨u, hu, rfl⟩
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg d)]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hu) (Nat.cast_nonneg d)).trans_eq
      (mul_one _)
  obtain ⟨K₀, _, φ, hφ_mono, htend⟩ :=
    (isCompact_subset_closedBall (E := E) (d : ℝ)).tendsto_subseq hL_sub
  have hB_K₀ : closedBall (0 : E) 1 ⊆ (K₀ : Set E) := by
    have hsup : ∀ u : E, supportFn (bodyClosedBall (0 : E) zero_le_one) u ≤ supportFn K₀ u := fun u => by
      have ht_sup : Tendsto (fun n => supportFn (L (φ n)) u) atTop (𝓝 (supportFn K₀ u)) :=
        (continuous_supportFn_eval u).continuousAt.tendsto.comp htend
      exact ge_of_tendsto ht_sup
        (Filter.Eventually.of_forall fun n =>
          supportFn_mono (by rw [coe_bodyClosedBall, hL_coe]; exact hBsub (φ n)) u)
    simpa [coe_bodyClosedBall] using
      (supportFn_le_iff_subset (K := bodyClosedBall (0 : E) zero_le_one) (L := K₀)).mp hsup
  have hK₀_0 : (0 : E) ∈ interior (K₀ : Set E) :=
    mem_interior.mpr ⟨ball (0 : E) 1, ball_subset_closedBall.trans hB_K₀, isOpen_ball,
      mem_ball_self zero_lt_one⟩
  have ht_L := tendsto_banachMazurDist_one_of_tendsto_convexBody
    (K := fun n => L (φ n)) (K₀ := K₀)
    (fun n => by rw [hL_coe]; exact hBsub (φ n)) hB_K₀ htend
  refine ⟨K₀, φ, ⟨0, hK₀_0⟩, hφ_mono, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht_L ?_ ?_
  · intro n
    exact one_le_affineBanachMazurDist
      (affineBanachMazurSet_nonempty (hint (φ n)) (K (φ n)).isBounded ⟨0, hK₀_0⟩ K₀.isBounded)
  · intro n
    have h0n : (0 : E) ∈ interior (L (φ n) : Set E) :=
      mem_interior.mpr ⟨ball (0 : E) 1, ball_subset_closedBall.trans (by rw [hL_coe]; exact hBsub (φ n)),
        isOpen_ball, mem_ball_self zero_lt_one⟩
    have hne_lin := banachMazurSet_nonempty h0n (L (φ n)).isBounded hK₀_0 K₀.isBounded
    have hle := affineBanachMazurDist_le_banachMazurDist hne_lin
    have haff : affineBanachMazurDist (L (φ n) : Set E) (K₀ : Set E) =
        affineBanachMazurDist (K (φ n) : Set E) (K₀ : Set E) := by
      rw [hL_coe, affineBanachMazurDist_affineEquiv_left]
    rwa [haff] at hle

end BanachMazurCompactum

end

end ConvexGeom
