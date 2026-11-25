module

public import ConvexGeom.Polarity
public import ConvexGeom.Symmetrization
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Origin-Symmetric Bodies, Ellipsoids, Mahler Volume, and Banach–Mazur Distance

This module provides the linear-invariant geometric foundations used throughout asymptotic
geometric analysis (Ball, Lectures 3–4; Klartag; Artstein-Avidan–Giannopoulos–Milman, Ch. 1–4):

1. **Origin-Symmetric Sets (`IsOriginSymmetric`):**
   Closure under polarity, linear images, scaling, Minkowski sums, and symmetrizations;
   support-function characterization (`isOriginSymmetric_convexBody_iff_supportFn`);
   evenness and absolute homogeneity of the Minkowski gauge (`gauge_smul_abs_of_isOriginSymmetric`)
   and equivalence of one-sided and absolute polarity (`mem_polarBody_iff_abs_inner_le_one`).
2. **Adjoint Determinant & Polarity under `GL(E)`:**
   - `det_adjoint_eq_det`: `(LinearMap.adjoint f).det = f.det` on any finite-dimensional real
     inner product space.
   - `adjointLinearEquiv`: the adjoint equivalence `T† : E ≃ₗ[ℝ] E`.
   - `polarBody_linearEquiv_image`: `(T '' S)° = (T⁻¹)† '' S°`.
3. **Ellipsoids & Affine Invariance of Mahler Volume:**
   - `ellipsoid T := T '' closedBall 0 1`: compactness, convexity, symmetry, `0 ∈ interior`,
     polarity (`polarBody_ellipsoid`), and add-Haar volume (`addHaar_ellipsoid`).
   - `mahlerVolume μ S := μ S * μ (polarBody S)`:
     - `mahlerVolume_linearEquiv`: **GL-invariance** `mahlerVolume μ (T '' S) = mahlerVolume μ S`.
     - `mahlerVolume_ellipsoid`: `mahlerVolume μ (ellipsoid T) = μ (closedBall 0 1) ^ 2`.
4. **Multiplicative Banach–Mazur Distance (`banachMazurDist`):**
   $$d_{\mathrm{BM}}(K, L) := \inf \{ r \ge 1 \mid \exists T \in \mathrm{GL}(E),\; K \subseteq T(L) \subseteq r K \}.$$
   - Reflexivity (`banachMazurDist_self`), symmetry (`banachMazurDist_symm`), lower bound `≥ 1`
     (`one_le_banachMazurDist`), and multiplicative triangle inequality (`banachMazurDist_mul_triangle`).
   - Full `GL(E)`- and positive-scale invariance on both arguments.
   - **Polarity invariance** (`banachMazurDist_polar`): `d_BM(K°, L°) = d_BM(K, L)` via the
     Bipolar Theorem.
   - **Mahler volume comparison** (`mahlerVolume_le_banachMazurDist_pow_mul`):
     `mahlerVolume μ L ≤ d_BM(K, L)^d * mahlerVolume μ K`.
-/

open MeasureTheory Set Metric
open scoped RealInnerProductSpace Pointwise ENNReal

namespace ConvexGeom

public section

/-! ### 1. Origin-Symmetric Sets -/

section OriginSymmetricBasic

variable {E : Type*} [NormedAddCommGroup E]

/-- A set `S ⊆ E` is **origin-symmetric** if `x ∈ S → -x ∈ S`. -/
def IsOriginSymmetric (S : Set E) : Prop :=
  ∀ x ∈ S, -x ∈ S

lemma isOriginSymmetric_iff_neg_eq {S : Set E} :
    IsOriginSymmetric S ↔ -S = S := by
  constructor
  · intro h
    ext x
    simp only [Set.mem_neg]
    exact ⟨fun hx => by simpa using h (-x) hx, fun hx => h x hx⟩
  · intro h x hx
    rw [← h]
    simpa using hx

lemma isOriginSymmetric_closedBall (r : ℝ) :
    IsOriginSymmetric (closedBall (0 : E) r) := by
  intro x hx
  simpa [mem_closedBall_zero_iff] using hx

lemma isOriginSymmetric_ball (r : ℝ) :
    IsOriginSymmetric (ball (0 : E) r) := by
  intro x hx
  simpa [mem_ball_zero_iff] using hx

lemma isOriginSymmetric_add {S T : Set E} (hS : IsOriginSymmetric S) (hT : IsOriginSymmetric T) :
    IsOriginSymmetric (S + T) := by
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact ⟨-x, hS x hx, -y, hT y hy, (neg_add x y).symm⟩

end OriginSymmetricBasic

section OriginSymmetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma isOriginSymmetric_polarBody {S : Set E} (hS : IsOriginSymmetric S) :
    IsOriginSymmetric (polarBody S) := by
  intro y hy
  rw [mem_polarBody] at hy ⊢
  intro x hx
  have h1 := hy (-x) (hS x hx)
  simpa [inner_neg_left, inner_neg_right] using h1

lemma isOriginSymmetric_linearMap_image {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : E →ₗ[ℝ] F) {S : Set E} (hS : IsOriginSymmetric S) :
    IsOriginSymmetric (f '' S) := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨-x, hS x hx, map_neg f x⟩

lemma isOriginSymmetric_smul (c : ℝ) {S : Set E} (hS : IsOriginSymmetric S) :
    IsOriginSymmetric (c • S) := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨-x, hS x hx, smul_neg c x⟩

lemma zero_mem_of_isOriginSymmetric {S : Set E} (hconv : Convex ℝ S) (hne : S.Nonempty)
    (hsym : IsOriginSymmetric S) : (0 : E) ∈ S := by
  obtain ⟨x, hx⟩ := hne
  have hmid := hconv hx (hsym x hx) (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  simpa [smul_neg, add_neg_cancel] using hmid

lemma supportFn_neg_of_isOriginSymmetric {K : ConvexBody E}
    (hK : IsOriginSymmetric (K : Set E)) (u : E) :
    supportFn K (-u) = supportFn K u := by
  apply le_antisymm
  · rw [supportFn_le_iff]
    intro x hx
    simpa [inner_neg_left, inner_neg_right] using inner_le_supportFn (hK x hx) u
  · rw [supportFn_le_iff]
    intro x hx
    simpa [inner_neg_left, inner_neg_right] using inner_le_supportFn (hK x hx) (-u)

/-- A convex body in a Hilbert space is origin-symmetric iff its support function is even. -/
theorem isOriginSymmetric_convexBody_iff_supportFn [CompleteSpace E] (K : ConvexBody E) :
    IsOriginSymmetric (K : Set E) ↔ ∀ u : E, supportFn K (-u) = supportFn K u := by
  constructor
  · exact supportFn_neg_of_isOriginSymmetric
  · intro heven
    have hbody : ((-1 : ℝ) • K : ConvexBody E) = K := by
      apply supportFn_injective
      ext u
      rw [supportFn_neg_one_smul, heven u]
    intro x hx
    have hmem : (-1 : ℝ) • x ∈ ((-1 : ℝ) • K : ConvexBody E) := by
      rw [← SetLike.mem_coe, ConvexBody.coe_smul]
      exact ⟨x, hx, rfl⟩
    rw [hbody] at hmem
    simpa using hmem

lemma isOriginSymmetric_centralSymm [CompleteSpace E] (K : ConvexBody E) :
    IsOriginSymmetric (centralSymm K : Set E) := by
  rw [isOriginSymmetric_convexBody_iff_supportFn]
  intro u
  rw [supportFn_centralSymm, supportFn_centralSymm, width_eq_supportFn_diff,
    width_eq_supportFn_diff, supportFn_minkowski_add, supportFn_minkowski_add,
    supportFn_neg_one_smul, supportFn_neg_one_smul, neg_neg, add_comm]

lemma isOriginSymmetric_minkowskiSymm [CompleteSpace E] {u : E} (hu : ‖u‖ = 1) (K : ConvexBody E)
    (hK : IsOriginSymmetric (K : Set E)) :
    IsOriginSymmetric (minkowskiSymm hu K : Set E) := by
  rw [isOriginSymmetric_convexBody_iff_supportFn]
  intro v
  rw [supportFn_minkowskiSymm, supportFn_minkowskiSymm, map_neg,
    supportFn_neg_of_isOriginSymmetric hK v,
    supportFn_neg_of_isOriginSymmetric hK (reflectHyperplane hu v)]

/-- For an origin-symmetric set `S`, the Minkowski gauge is even: `gauge S (-x) = gauge S x`. -/
lemma gauge_neg_of_isOriginSymmetric {S : Set E} (hS : IsOriginSymmetric S) (x : E) :
    gauge S (-x) = gauge S x := by
  have heq : {r : ℝ | 0 < r ∧ -x ∈ r • S} = {r : ℝ | 0 < r ∧ x ∈ r • S} := by
    ext r
    simp only [mem_ofPred_eq, and_congr_right_iff]
    intro _
    constructor
    · rintro ⟨y, hy, hyx⟩
      refine ⟨-y, hS y hy, ?_⟩
      dsimp only at hyx ⊢
      rw [smul_neg, hyx, neg_neg]
    · rintro ⟨y, hy, hyx⟩
      refine ⟨-y, hS y hy, ?_⟩
      dsimp only at hyx ⊢
      rw [smul_neg, hyx]
  simp only [gauge, heq]

/-- For an origin-symmetric set `S`, the Minkowski gauge is positively and negatively homogeneous:
`gauge S (c • x) = |c| * gauge S x` for all `c : ℝ`. -/
theorem gauge_smul_abs_of_isOriginSymmetric {S : Set E} (hS : IsOriginSymmetric S)
    (c : ℝ) (x : E) :
    gauge S (c • x) = |c| * gauge S x := by
  rcases le_total 0 c with hc | hc
  · rw [abs_of_nonneg hc, gauge_smul_of_nonneg hc, smul_eq_mul]
  · rw [abs_of_nonpos hc]
    have hneg : c • x = (-c) • (-x) := by simp [smul_neg, neg_smul]
    rw [hneg, gauge_smul_of_nonneg (neg_nonneg.mpr hc), gauge_neg_of_isOriginSymmetric hS,
      smul_eq_mul]

/-- For an origin-symmetric set `S`, one-sided polarity coincides with the absolute polar:
`y ∈ polarBody S ↔ ∀ x ∈ S, |⟪x, y⟫| ≤ 1`. -/
theorem mem_polarBody_iff_abs_inner_le_one {S : Set E} (hS : IsOriginSymmetric S) (y : E) :
    y ∈ polarBody S ↔ ∀ x ∈ S, |⟪x, y⟫| ≤ 1 := by
  rw [mem_polarBody]
  constructor
  · intro hy x hx
    rw [abs_le]
    refine ⟨?_, hy x hx⟩
    have := hy (-x) (hS x hx)
    rw [inner_neg_left] at this
    linarith
  · intro h x hx
    exact (le_abs_self _).trans (h x hx)

end OriginSymmetric

/-! ### 2. Adjoint Determinant and Linear Equivalence Law for Polar Bodies -/

section AdjointAndPolar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Scalar multiplication by a nonzero real number as a `LinearEquiv`. -/
noncomputable def smulLinearEquiv {c : ℝ} (hc : c ≠ 0) : E ≃ₗ[ℝ] E where
  toFun x := c • x
  invFun x := c⁻¹ • x
  left_inv x := by dsimp only; rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  right_inv x := by dsimp only; rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  map_add' x y := smul_add c x y
  map_smul' a x := smul_comm c a x

@[simp]
lemma smulLinearEquiv_apply {c : ℝ} (hc : c ≠ 0) (x : E) :
    smulLinearEquiv hc x = c • x := by
  rfl

@[simp]
lemma smulLinearEquiv_image {c : ℝ} (hc : c ≠ 0) (S : Set E) :
    (smulLinearEquiv hc) '' S = c • S := by
  ext x
  simp only [mem_image, mem_smul_set, smulLinearEquiv_apply]

/-- On a finite-dimensional real inner product space, the adjoint has the same determinant:
`det (f†) = det f`. -/
theorem det_adjoint_eq_det [FiniteDimensional ℝ E] (f : E →ₗ[ℝ] E) :
    LinearMap.det (LinearMap.adjoint f) = LinearMap.det f := by
  let b := stdOrthonormalBasis ℝ E
  rw [← LinearMap.det_toMatrix b.toBasis, ← LinearMap.det_toMatrix b.toBasis,
    LinearMap.toMatrix_adjoint b b, Matrix.det_conjTranspose]
  simp

/-- The adjoint of a linear equivalence `T : E ≃ₗ[ℝ] E` as a linear equivalence `T† : E ≃ₗ[ℝ] E`. -/
noncomputable def adjointLinearEquiv [FiniteDimensional ℝ E] (T : E ≃ₗ[ℝ] E) : E ≃ₗ[ℝ] E where
  toFun := LinearMap.adjoint (T : E →ₗ[ℝ] E)
  invFun := LinearMap.adjoint (T.symm : E →ₗ[ℝ] E)
  left_inv x := by
    have hcomp : LinearMap.adjoint (T.symm : E →ₗ[ℝ] E) ∘ₗ LinearMap.adjoint (T : E →ₗ[ℝ] E) =
        LinearMap.id := by
      rw [← LinearMap.adjoint_comp]
      have hTT : (T : E →ₗ[ℝ] E) ∘ₗ (T.symm : E →ₗ[ℝ] E) = LinearMap.id := by
        ext y; simp
      rw [hTT, LinearMap.adjoint_id]
    exact congrArg (fun f : E →ₗ[ℝ] E => f x) hcomp
  right_inv x := by
    have hcomp : LinearMap.adjoint (T : E →ₗ[ℝ] E) ∘ₗ LinearMap.adjoint (T.symm : E →ₗ[ℝ] E) =
        LinearMap.id := by
      rw [← LinearMap.adjoint_comp]
      have hTT : (T.symm : E →ₗ[ℝ] E) ∘ₗ (T : E →ₗ[ℝ] E) = LinearMap.id := by
        ext y; simp
      rw [hTT, LinearMap.adjoint_id]
    exact congrArg (fun f : E →ₗ[ℝ] E => f x) hcomp
  map_add' x y := map_add (LinearMap.adjoint (T : E →ₗ[ℝ] E)) x y
  map_smul' c x := map_smul (LinearMap.adjoint (T : E →ₗ[ℝ] E)) c x

@[simp]
lemma adjointLinearEquiv_apply [FiniteDimensional ℝ E] (T : E ≃ₗ[ℝ] E) (x : E) :
    adjointLinearEquiv T x = LinearMap.adjoint (T : E →ₗ[ℝ] E) x := by
  rfl

@[simp]
lemma adjointLinearEquiv_toLinearMap [FiniteDimensional ℝ E] (T : E ≃ₗ[ℝ] E) :
    (adjointLinearEquiv T : E →ₗ[ℝ] E) = LinearMap.adjoint (T : E →ₗ[ℝ] E) := by
  ext x; rfl

@[simp]
lemma adjointLinearEquiv_symm_apply [FiniteDimensional ℝ E] (T : E ≃ₗ[ℝ] E) (x : E) :
    (adjointLinearEquiv T).symm x = LinearMap.adjoint (T.symm : E →ₗ[ℝ] E) x := by
  rfl

/-- **Linear equivalence law for polar bodies:**
for any invertible linear map `T : E ≃ₗ[ℝ] E` in finite dimensions,
`(T '' S)° = (T⁻¹)† '' S°`. -/
theorem polarBody_linearEquiv_image [FiniteDimensional ℝ E] (T : E ≃ₗ[ℝ] E) (S : Set E) :
    polarBody (T '' S) = (adjointLinearEquiv T.symm) '' polarBody S := by
  ext y
  simp only [mem_polarBody, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · intro hy
    refine ⟨adjointLinearEquiv T y, fun x hx => ?_, ?_⟩
    · rw [adjointLinearEquiv_apply, LinearMap.adjoint_inner_right]
      exact hy x hx
    · exact (adjointLinearEquiv T).left_inv y
  · rintro ⟨z, hz, rfl⟩ x hx
    have hinner : ⟪T x, adjointLinearEquiv T.symm z⟫ = ⟪x, z⟫ := by
      rw [adjointLinearEquiv_apply, LinearMap.adjoint_inner_right]
      simp
    rw [hinner]
    exact hz x hx

end AdjointAndPolar

/-! ### 3. Ellipsoids and Affine Invariance of Mahler Volume -/

section EllipsoidAndMahler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A centered ellipsoid in `E`: the image of the closed unit ball under `T : E ≃ₗ[ℝ] E`. -/
def ellipsoid (T : E ≃ₗ[ℝ] E) : Set E :=
  T '' closedBall (0 : E) 1

lemma convex_ellipsoid (T : E ≃ₗ[ℝ] E) : Convex ℝ (ellipsoid T) :=
  (convex_closedBall (0 : E) 1).linear_image T.toLinearMap

lemma isOriginSymmetric_ellipsoid (T : E ≃ₗ[ℝ] E) : IsOriginSymmetric (ellipsoid T) :=
  isOriginSymmetric_linearMap_image T.toLinearMap (isOriginSymmetric_closedBall 1)

lemma isCompact_ellipsoid [FiniteDimensional ℝ E] (T : E ≃ₗ[ℝ] E) :
    IsCompact (ellipsoid T) :=
  (isCompact_closedBall (0 : E) 1).image T.toContinuousLinearEquiv.continuous

lemma zero_mem_interior_ellipsoid [FiniteDimensional ℝ E] (T : E ≃ₗ[ℝ] E) :
    (0 : E) ∈ interior (ellipsoid T) := by
  let hT : E ≃ₜ E := T.toContinuousLinearEquiv.toHomeomorph
  have heq : ellipsoid T = hT '' closedBall (0 : E) 1 := rfl
  rw [heq, ← hT.image_interior]
  refine ⟨0, ?_, map_zero T⟩
  exact mem_interior.mpr ⟨ball (0 : E) 1, ball_subset_closedBall, isOpen_ball,
    mem_ball_self zero_lt_one⟩

/-- The polar of an ellipsoid is the dual ellipsoid:
`(T(B₁))° = (T⁻¹)†(B₁)`. -/
theorem polarBody_ellipsoid [FiniteDimensional ℝ E] (T : E ≃ₗ[ℝ] E) :
    polarBody (ellipsoid T) = ellipsoid (adjointLinearEquiv T.symm) := by
  rw [ellipsoid, polarBody_linearEquiv_image, polarBody_closedBall one_pos, inv_one, ellipsoid]

/-- Add-Haar volume of an ellipsoid: `μ (T(B₁)) = |det T| * μ (B₁)`. -/
theorem addHaar_ellipsoid [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (T : E ≃ₗ[ℝ] E) :
    μ (ellipsoid T) =
      ENNReal.ofReal |LinearMap.det (T : E →ₗ[ℝ] E)| * μ (closedBall (0 : E) 1) := by
  change μ ((T : E →ₗ[ℝ] E) '' closedBall (0 : E) 1) = _
  exact Measure.addHaar_image_linearMap μ (T : E →ₗ[ℝ] E) (closedBall (0 : E) 1)

/-- The **Mahler volume** (volume product) of a set `S ⊆ E` with respect to a measure `μ`:
`mahlerVolume μ S := μ S * μ (polarBody S)`. -/
noncomputable def mahlerVolume [MeasurableSpace E] (μ : Measure E) (S : Set E) : ℝ≥0∞ :=
  μ S * μ (polarBody S)

/-- **Linear (`GL(E)`) invariance of Mahler volume:**
for every invertible linear map `T : E ≃ₗ[ℝ] E` and every additive Haar measure `μ`,
`mahlerVolume μ (T '' S) = mahlerVolume μ S`. -/
theorem mahlerVolume_linearEquiv [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (T : E ≃ₗ[ℝ] E) (S : Set E) :
    mahlerVolume μ (T '' S) = mahlerVolume μ S := by
  unfold mahlerVolume
  rw [polarBody_linearEquiv_image]
  change μ ((T : E →ₗ[ℝ] E) '' S) *
      μ ((adjointLinearEquiv T.symm : E →ₗ[ℝ] E) '' polarBody S) = _
  rw [Measure.addHaar_image_linearMap, Measure.addHaar_image_linearMap,
    adjointLinearEquiv_toLinearMap, det_adjoint_eq_det, LinearEquiv.det_coe_symm]
  have hd : LinearMap.det (T : E →ₗ[ℝ] E) ≠ 0 := T.isUnit_det'.ne_zero
  have hmul : ENNReal.ofReal |LinearMap.det (T : E →ₗ[ℝ] E)| *
      ENNReal.ofReal |(LinearMap.det (T : E →ₗ[ℝ] E))⁻¹| = 1 := by
    rw [← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, mul_inv_cancel₀ hd, abs_one,
      ENNReal.ofReal_one]
  calc
    ENNReal.ofReal |LinearMap.det (T : E →ₗ[ℝ] E)| * μ S *
        (ENNReal.ofReal |(LinearMap.det (T : E →ₗ[ℝ] E))⁻¹| * μ (polarBody S))
      = (ENNReal.ofReal |LinearMap.det (T : E →ₗ[ℝ] E)| *
          ENNReal.ofReal |(LinearMap.det (T : E →ₗ[ℝ] E))⁻¹|) * (μ S * μ (polarBody S)) := by
          ring
    _ = μ S * μ (polarBody S) := by rw [hmul, one_mul]

/-- Scale invariance of Mahler volume for any nonzero scalar `c`. -/
theorem mahlerVolume_smul [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {c : ℝ} (hc : c ≠ 0) (S : Set E) :
    mahlerVolume μ (c • S) = mahlerVolume μ S := by
  rw [← smulLinearEquiv_image hc]
  exact mahlerVolume_linearEquiv μ (smulLinearEquiv hc) S

/-- Every centered ellipsoid has the same Mahler volume as the Euclidean unit ball:
`mahlerVolume μ (ellipsoid T) = μ (closedBall 0 1) ^ 2`. -/
theorem mahlerVolume_ellipsoid [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (T : E ≃ₗ[ℝ] E) :
    mahlerVolume μ (ellipsoid T) = μ (closedBall (0 : E) 1) ^ 2 := by
  rw [ellipsoid, mahlerVolume_linearEquiv, mahlerVolume, polarBody_closedBall one_pos, inv_one, sq]

end EllipsoidAndMahler

/-! ### 4. Multiplicative Banach–Mazur Distance -/

section BanachMazur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The set of multiplicative distortion factors `r ≥ 1` admitting an invertible linear map
`T : E ≃ₗ[ℝ] E` with `K ⊆ T '' L ⊆ r • K`. -/
def banachMazurSet (K L : Set E) : Set ℝ :=
  {r : ℝ | 1 ≤ r ∧ ∃ T : E ≃ₗ[ℝ] E, K ⊆ T '' L ∧ T '' L ⊆ r • K}

/-- The multiplicative **Banach–Mazur distance** between sets `K, L ⊆ E`:
$$d_{\mathrm{BM}}(K, L) := \inf \{ r \ge 1 \mid \exists T \in \mathrm{GL}(E),\; K \subseteq T(L) \subseteq r K \}.$$ -/
noncomputable def banachMazurDist (K L : Set E) : ℝ :=
  sInf (banachMazurSet K L)

lemma bddBelow_banachMazurSet (K L : Set E) : BddBelow (banachMazurSet K L) :=
  ⟨1, fun _ hr => hr.1⟩

/-- Whenever `K` and `L` are bounded and contain `0` in their interiors, their Banach–Mazur
distortion set is nonempty. -/
lemma banachMazurSet_nonempty {K L : Set E}
    (hK0 : (0 : E) ∈ interior K) (hKb : Bornology.IsBounded K)
    (hL0 : (0 : E) ∈ interior L) (hLb : Bornology.IsBounded L) :
    (banachMazurSet K L).Nonempty := by
  obtain ⟨r₁, hr₁, hballK⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hK0)
  obtain ⟨r₂, hr₂, hballL⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hL0)
  obtain ⟨R₁, hKR₁⟩ := hKb.subset_closedBall (0 : E)
  obtain ⟨R₂, hLR₂⟩ := hLb.subset_closedBall (0 : E)
  set a₁ := r₁ / 2
  set a₂ := r₂ / 2
  set b₁ := max R₁ 1
  set b₂ := max R₂ 1
  have ha₁ : 0 < a₁ := half_pos hr₁
  have ha₂ : 0 < a₂ := half_pos hr₂
  have hb₁ : 0 < b₁ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hb₂ : 0 < b₂ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hcbK : closedBall (0 : E) a₁ ⊆ K :=
    (closedBall_subset_ball (half_lt_self hr₁)).trans hballK
  have hcbL : closedBall (0 : E) a₂ ⊆ L :=
    (closedBall_subset_ball (half_lt_self hr₂)).trans hballL
  have hKb₁ : K ⊆ closedBall (0 : E) b₁ :=
    hKR₁.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hLb₂ : L ⊆ closedBall (0 : E) b₂ :=
    hLR₂.trans (closedBall_subset_closedBall (le_max_left _ _))
  set c := b₁ / a₂
  have hc : 0 < c := div_pos hb₁ ha₂
  set r := max 1 (c * b₂ / a₁)
  have hr1 : 1 ≤ r := le_max_left _ _
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  refine ⟨r, hr1, smulLinearEquiv hc.ne', ?_, ?_⟩
  · intro x hx
    rw [smulLinearEquiv_image]
    refine ⟨c⁻¹ • x, hcbL ?_, by dsimp only; rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]⟩
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
    have hxnorm : ‖x‖ ≤ b₁ := mem_closedBall_zero_iff.mp (hKb₁ hx)
    calc
      c⁻¹ * ‖x‖ ≤ c⁻¹ * b₁ := mul_le_mul_of_nonneg_left hxnorm (inv_nonneg.mpr hc.le)
      _ = a₂ := by dsimp only [c]; field_simp [hb₁.ne', ha₂.ne']
  · intro y hy
    rw [smulLinearEquiv_image] at hy
    rcases hy with ⟨z, hz, rfl⟩
    refine ⟨r⁻¹ • (c • z), hcbK ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hr_pos), abs_of_pos hc]
      have hznorm : ‖z‖ ≤ b₂ := mem_closedBall_zero_iff.mp (hLb₂ hz)
      have hrge : c * b₂ / a₁ ≤ r := le_max_right _ _
      have hcb_le : c * b₂ ≤ r * a₁ := (div_le_iff₀ ha₁).mp hrge
      calc
        r⁻¹ * (c * ‖z‖) ≤ r⁻¹ * (c * b₂) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hznorm hc.le) (inv_nonneg.mpr hr_pos.le)
        _ ≤ r⁻¹ * (r * a₁) := mul_le_mul_of_nonneg_left hcb_le (inv_nonneg.mpr hr_pos.le)
        _ = a₁ := by field_simp [hr_pos.ne']
    · dsimp only
      rw [smul_smul, mul_inv_cancel₀ hr_pos.ne', one_smul]

/-- `1 ≤ banachMazurDist K L` whenever the distortion set is nonempty. -/
theorem one_le_banachMazurDist {K L : Set E} (hne : (banachMazurSet K L).Nonempty) :
    1 ≤ banachMazurDist K L :=
  le_csInf hne fun _ hr => hr.1

/-- Reflexivity: `banachMazurDist K K = 1`. -/
theorem banachMazurDist_self (K : Set E) : banachMazurDist K K = 1 := by
  have h1 : (1 : ℝ) ∈ banachMazurSet K K :=
    ⟨le_rfl, LinearEquiv.refl ℝ E,
      fun x hx => ⟨x, hx, rfl⟩,
      by rintro _ ⟨x, hx, rfl⟩; exact ⟨x, hx, one_smul ℝ x⟩⟩
  exact le_antisymm (csInf_le (bddBelow_banachMazurSet K K) h1)
    (one_le_banachMazurDist ⟨1, h1⟩)

lemma banachMazurSet_symm (K L : Set E) :
    banachMazurSet K L = banachMazurSet L K := by
  have hsub : ∀ A B : Set E, banachMazurSet A B ⊆ banachMazurSet B A := by
    intro A B r ⟨hr1, T, h1, h2⟩
    have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
    refine ⟨hr1, (smulLinearEquiv hr_pos.ne').trans T.symm, ?_, ?_⟩
    · intro y hy
      have hTy : T y ∈ r • A := h2 ⟨y, hy, rfl⟩
      rcases hTy with ⟨x, hx, hrx⟩
      dsimp only at hrx
      refine ⟨x, hx, ?_⟩
      change T.symm (r • x) = y
      rw [hrx, T.symm_apply_apply]
    · rintro _ ⟨x, hx, rfl⟩
      rcases h1 hx with ⟨y, hy, hTy⟩
      refine ⟨y, hy, ?_⟩
      change r • y = T.symm (r • x)
      rw [← hTy, ← map_smul, T.symm_apply_apply]
  exact Set.Subset.antisymm (hsub K L) (hsub L K)

/-- Symmetry: `banachMazurDist K L = banachMazurDist L K`. -/
theorem banachMazurDist_symm (K L : Set E) :
    banachMazurDist K L = banachMazurDist L K := by
  rw [banachMazurDist, banachMazurSet_symm, banachMazurDist]

lemma banachMazurSet_linearEquiv_right (K L : Set E) (A : E ≃ₗ[ℝ] E) :
    banachMazurSet K (A '' L) = banachMazurSet K L := by
  ext r
  simp only [banachMazurSet, mem_ofPred_eq, and_congr_right_iff]
  intro _
  constructor
  · rintro ⟨T, h1, h2⟩
    have himg : (A.trans T) '' L = T '' (A '' L) := by
      ext x; simp [LinearEquiv.trans_apply]
    exact ⟨A.trans T, himg.symm ▸ h1, himg.symm ▸ h2⟩
  · rintro ⟨T, h1, h2⟩
    have himg : (A.symm.trans T) '' (A '' L) = T '' L := by
      ext x; simp [LinearEquiv.trans_apply]
    exact ⟨A.symm.trans T, himg.symm ▸ h1, himg.symm ▸ h2⟩

/-- Right `GL(E)`-invariance of Banach–Mazur distance. -/
theorem banachMazurDist_linearEquiv_right (K L : Set E) (A : E ≃ₗ[ℝ] E) :
    banachMazurDist K (A '' L) = banachMazurDist K L := by
  rw [banachMazurDist, banachMazurSet_linearEquiv_right, banachMazurDist]

/-- Left `GL(E)`-invariance of Banach–Mazur distance. -/
theorem banachMazurDist_linearEquiv_left (K L : Set E) (A : E ≃ₗ[ℝ] E) :
    banachMazurDist (A '' K) L = banachMazurDist K L := by
  rw [banachMazurDist_symm, banachMazurDist_linearEquiv_right, banachMazurDist_symm]

/-- Scale invariance of Banach–Mazur distance on both arguments. -/
theorem banachMazurDist_smul_right (K L : Set E) {c : ℝ} (hc : c ≠ 0) :
    banachMazurDist K (c • L) = banachMazurDist K L := by
  rw [← smulLinearEquiv_image hc, banachMazurDist_linearEquiv_right]

theorem banachMazurDist_smul_left (K L : Set E) {c : ℝ} (hc : c ≠ 0) :
    banachMazurDist (c • K) L = banachMazurDist K L := by
  rw [← smulLinearEquiv_image hc, banachMazurDist_linearEquiv_left]

/-- **Multiplicative Triangle Inequality:**
`banachMazurDist K M ≤ banachMazurDist K L * banachMazurDist L M`
(so `log ∘ banachMazurDist` is a pseudometric). -/
theorem banachMazurDist_mul_triangle {K L M : Set E}
    (hKL : (banachMazurSet K L).Nonempty) (hLM : (banachMazurSet L M).Nonempty) :
    banachMazurDist K M ≤ banachMazurDist K L * banachMazurDist L M := by
  have hmul_mem : ∀ r₁ ∈ banachMazurSet K L, ∀ r₂ ∈ banachMazurSet L M,
      r₁ * r₂ ∈ banachMazurSet K M := by
    rintro r₁ ⟨hr₁, T₁, hK1, h1K⟩ r₂ ⟨hr₂, T₂, hL2, h2L⟩
    refine ⟨by nlinarith, T₂.trans T₁, ?_, ?_⟩
    · intro x hx
      rcases hK1 hx with ⟨y, hy, rfl⟩
      rcases hL2 hy with ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      have hT2 : T₂ z ∈ r₂ • L := h2L ⟨z, hz, rfl⟩
      rcases hT2 with ⟨y, hy, hyz⟩
      have hT1 : T₁ y ∈ r₁ • K := h1K ⟨y, hy, rfl⟩
      rcases hT1 with ⟨x, hx, hxy⟩
      refine ⟨x, hx, ?_⟩
      change (r₁ * r₂) • x = T₁ (T₂ z)
      rw [← hyz, map_smul, ← hxy, smul_smul, mul_comm]
  have hstep1 : ∀ r₁ ∈ banachMazurSet K L, banachMazurDist K M ≤ r₁ * banachMazurDist L M := by
    intro r₁ hr₁
    have hr₁_pos : 0 < r₁ := lt_of_lt_of_le zero_lt_one hr₁.1
    rw [← div_le_iff₀' hr₁_pos]
    refine le_csInf hLM fun r₂ hr₂ => ?_
    rw [div_le_iff₀' hr₁_pos]
    exact csInf_le (bddBelow_banachMazurSet K M) (hmul_mem r₁ hr₁ r₂ hr₂)
  have hdLM_pos : 0 < banachMazurDist L M := lt_of_lt_of_le zero_lt_one (one_le_banachMazurDist hLM)
  rw [← div_le_iff₀ hdLM_pos]
  refine le_csInf hKL fun r₁ hr₁ => ?_
  rw [div_le_iff₀ hdLM_pos]
  exact hstep1 r₁ hr₁

/-- **Polarity Invariance of Banach–Mazur Distance:**
in finite dimensions, for closed convex sets `K, L` containing `0`,
`banachMazurDist (polarBody K) (polarBody L) = banachMazurDist K L`. -/
theorem banachMazurDist_polar [FiniteDimensional ℝ E] {K L : Set E}
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hK0 : (0 : E) ∈ K)
    (hLc : Convex ℝ L) (hLcl : IsClosed L) (hL0 : (0 : E) ∈ L) :
    banachMazurDist (polarBody K) (polarBody L) = banachMazurDist K L := by
  have hsub : ∀ A B : Set E, banachMazurSet A B ⊆ banachMazurSet (polarBody A) (polarBody B) := by
    intro A B r ⟨hr1, T, h1, h2⟩
    have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
    let S : E ≃ₗ[ℝ] E := (adjointLinearEquiv T.symm).trans (smulLinearEquiv hr_pos.ne')
    have hSimg : S '' polarBody B = r • polarBody (T '' B) := by
      rw [polarBody_linearEquiv_image, ← smulLinearEquiv_image hr_pos.ne', ← Set.image_comp]
      rfl
    refine ⟨hr1, S, ?_, ?_⟩
    · rw [hSimg]
      have hpol2 : r⁻¹ • polarBody A ⊆ polarBody (T '' B) := by
        rw [← polarBody_smul hr_pos]; exact polarBody_antitone h2
      intro y hy
      have hy' : r⁻¹ • y ∈ polarBody (T '' B) := hpol2 ⟨y, hy, rfl⟩
      refine ⟨r⁻¹ • y, hy', ?_⟩
      dsimp only
      rw [smul_smul, mul_inv_cancel₀ hr_pos.ne', one_smul]
    · rw [hSimg]
      exact Set.smul_set_mono (polarBody_antitone h1)
  have heq : banachMazurSet (polarBody K) (polarBody L) = banachMazurSet K L := by
    apply Set.Subset.antisymm _ (hsub K L)
    calc
      banachMazurSet (polarBody K) (polarBody L)
        ⊆ banachMazurSet (polarBody (polarBody K)) (polarBody (polarBody L)) :=
          hsub (polarBody K) (polarBody L)
      _ = banachMazurSet K L := by
          rw [polarBody_polarBody hKc hKcl hK0, polarBody_polarBody hLc hLcl hL0]
  rw [banachMazurDist, heq, banachMazurDist]

/-- **Mahler Volume Comparison via Banach–Mazur Distance:**
for any additive Haar measure `μ` and any sets `K, L` with nonempty distortion set,
$$\mathcal{P}_\mu(L) \le d_{\mathrm{BM}}(K, L)^d\,\mathcal{P}_\mu(K).$$ -/
theorem mahlerVolume_le_banachMazurDist_pow_mul [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {K L : Set E} (hne : (banachMazurSet K L).Nonempty) :
    mahlerVolume μ L ≤
      ENNReal.ofReal (banachMazurDist K L ^ Module.finrank ℝ E) * mahlerVolume μ K := by
  set d := Module.finrank ℝ E
  have hbound : ∀ r ∈ banachMazurSet K L,
      mahlerVolume μ L ≤ ENNReal.ofReal (r ^ d) * mahlerVolume μ K := by
    rintro r ⟨hr1, T, hKsub, hsubrK⟩
    have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
    rw [← mahlerVolume_linearEquiv μ T L, mahlerVolume, mahlerVolume]
    have hvol1 : μ (T '' L) ≤ ENNReal.ofReal (r ^ d) * μ K := by
      calc
        μ (T '' L) ≤ μ (r • K) := measure_mono hsubrK
        _ = ENNReal.ofReal (r ^ d) * μ K := Measure.addHaar_smul_of_nonneg μ hr_pos.le K
    have hvol2 : μ (polarBody (T '' L)) ≤ μ (polarBody K) :=
      measure_mono (polarBody_antitone hKsub)
    calc
      μ (T '' L) * μ (polarBody (T '' L))
        ≤ (ENNReal.ofReal (r ^ d) * μ K) * μ (polarBody K) := mul_le_mul' hvol1 hvol2
      _ = ENNReal.ofReal (r ^ d) * (μ K * μ (polarBody K)) := by ring
  rcases eq_or_ne (mahlerVolume μ K) ⊤ with hKtop | hKfin
  · have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (banachMazurDist K L ^ d) := by
      rw [ENNReal.ofReal_pos]
      exact pow_pos (lt_of_lt_of_le zero_lt_one (one_le_banachMazurDist hne)) d
    rw [hKtop, ENNReal.mul_top hpos.ne']
    exact le_top
  · have ⟨r₀, hr₀⟩ := hne
    have hLfin : mahlerVolume μ L ≠ ⊤ := by
      have h1 := hbound r₀ hr₀
      exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKfin) h1
    have hreal : (mahlerVolume μ L).toReal ≤
        banachMazurDist K L ^ d * (mahlerVolume μ K).toReal := by
      have hfor : ∀ ε : ℝ, 0 < ε →
          (mahlerVolume μ L).toReal ≤
            (banachMazurDist K L + ε) ^ d * (mahlerVolume μ K).toReal := by
        intro ε hε
        obtain ⟨r, hr_mem, hr_lt⟩ := Real.lt_sInf_add_pos hne hε
        have h1 := hbound r hr_mem
        have hto : (mahlerVolume μ L).toReal ≤ r ^ d * (mahlerVolume μ K).toReal := by
          have hrnn : 0 ≤ r ^ d := pow_nonneg (le_trans zero_le_one hr_mem.1) d
          have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKfin) h1
          rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hrnn] at this
        have hpow : r ^ d ≤ (banachMazurDist K L + ε) ^ d :=
          pow_le_pow_left₀ (le_trans zero_le_one hr_mem.1) hr_lt.le d
        exact hto.trans (mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg)
      have htend : Filter.Tendsto
          (fun ε : ℝ => (banachMazurDist K L + ε) ^ d * (mahlerVolume μ K).toReal)
          (nhdsWithin 0 (Ioi 0))
          (nhds (banachMazurDist K L ^ d * (mahlerVolume μ K).toReal)) := by
        have hcont : Continuous (fun ε : ℝ =>
            (banachMazurDist K L + ε) ^ d * (mahlerVolume μ K).toReal) :=
          ((continuous_const.add continuous_id).pow d).mul continuous_const
        simpa [add_zero] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
      exact ge_of_tendsto htend (Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => hfor ε hε)
    rw [← ENNReal.ofReal_toReal hLfin, ← ENNReal.ofReal_toReal hKfin,
      ← ENNReal.ofReal_mul (pow_nonneg (le_trans zero_le_one (one_le_banachMazurDist hne)) d)]
    exact ENNReal.ofReal_le_ofReal hreal

/-- Specialization to the Euclidean unit ball:
$$\mathcal{P}_\mu(L) \le d_{\mathrm{BM}}(B_2^d, L)^d\,\mu(B_2^d)^2.$$ -/
theorem mahlerVolume_le_banachMazurDist_ball_pow_mul [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {L : Set E} (hL0 : (0 : E) ∈ interior L) (hLb : Bornology.IsBounded L) :
    mahlerVolume μ L ≤
      ENNReal.ofReal (banachMazurDist (closedBall (0 : E) 1) L ^ Module.finrank ℝ E) *
        μ (closedBall (0 : E) 1) ^ 2 := by
  have hB0 : (0 : E) ∈ interior (closedBall (0 : E) 1) :=
    mem_interior.mpr ⟨ball (0 : E) 1, ball_subset_closedBall, isOpen_ball,
      mem_ball_self zero_lt_one⟩
  have hne := banachMazurSet_nonempty hB0 isBounded_closedBall hL0 hLb
  have hball : mahlerVolume μ (closedBall (0 : E) 1) = μ (closedBall (0 : E) 1) ^ 2 := by
    rw [mahlerVolume, polarBody_closedBall one_pos, inv_one, sq]
  simpa [hball] using mahlerVolume_le_banachMazurDist_pow_mul μ hne

end BanachMazur

end

end ConvexGeom
