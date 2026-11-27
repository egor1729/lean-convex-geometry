/-
Copyright (c) 2026 Yegor Gorodzha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yegor Gorodzha
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# General Spherical Trigonometry, Dihedral Angles, and Spherical Caps

Dimension-independent spherical and dihedral geometry in any real inner product space `E`.

## Main definitions

* `ConvexGeom.sphericalTangent`: orthogonal projection `u - ⟪u, w⟫ • w` onto `w⊥`.
* `ConvexGeom.sphericalAngle`: interior spherical angle at `w` between great-circle arcs.
* `ConvexGeom.gramDet3`: symmetric `3 × 3` Gram determinant formula for unit triples (linked to
  Mathlib's `Matrix.gram` via `gramDet3_eq_det_gram`).
* `ConvexGeom.dihedralAngle`: interior dihedral angle `π - angle n₁ n₂`.
* `ConvexGeom.sphericalCap`: closed spherical cap `{v ∈ sphere 0 1 | t ≤ ⟪v, u⟫}`.

## Main statements

* `ConvexGeom.spherical_law_of_cosines`, `ConvexGeom.spherical_triangle_inequality` (delegating
  to Mathlib's `InnerProductGeometry.angle_le_angle_add_angle`), `ConvexGeom.gramDet3_eq_det_gram`,
  `ConvexGeom.spherical_law_of_sines_mul`, and `ConvexGeom.spherical_law_of_sines`.
* `ConvexGeom.sphericalCap_eq_closedBall_inter_sphere`, `ConvexGeom.isCompact_sphericalCap`.
-/

open Real Set
open scoped RealInnerProductSpace

namespace ConvexGeom

public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### 1. Spherical Tangent Projections and Spherical Angles -/

/-- Orthogonal projection of `u` onto `w⊥` (when `‖w‖ = 1`): the initial tangent vector at `w`
pointing toward `u` along the great circle. -/
@[expose]
def sphericalTangent (w u : E) : E :=
  u - ⟪u, w⟫ • w

lemma inner_sphericalTangent_right {w : E} (hw : ‖w‖ = 1) (u : E) :
    ⟪sphericalTangent w u, w⟫ = 0 := by
  unfold sphericalTangent
  rw [inner_sub_left, inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq, hw]
  ring

lemma inner_sphericalTangent {w : E} (hw : ‖w‖ = 1) (u v : E) :
    ⟪sphericalTangent w u, sphericalTangent w v⟫ = ⟪u, v⟫ - ⟪u, w⟫ * ⟪v, w⟫ := by
  unfold sphericalTangent
  rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_smul_left, inner_smul_left,
    inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq, hw, real_inner_comm w v]
  simp only [RCLike.conj_to_real]
  ring

lemma norm_sq_sphericalTangent {w u : E} (hw : ‖w‖ = 1) (hu : ‖u‖ = 1) :
    ‖sphericalTangent w u‖ ^ 2 = 1 - ⟪w, u⟫ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_sphericalTangent hw, real_inner_self_eq_norm_sq, hu,
    real_inner_comm u w]
  ring

lemma norm_sphericalTangent {w u : E} (hw : ‖w‖ = 1) (hu : ‖u‖ = 1) :
    ‖sphericalTangent w u‖ = Real.sin (InnerProductGeometry.angle w u) := by
  have h1 : Real.cos (InnerProductGeometry.angle w u) = ⟪w, u⟫ := by
    rw [InnerProductGeometry.cos_angle, hw, hu, mul_one, div_one]
  have hsq : ‖sphericalTangent w u‖ ^ 2 = Real.sin (InnerProductGeometry.angle w u) ^ 2 := by
    rw [norm_sq_sphericalTangent hw hu, ← h1]
    linarith [Real.sin_sq_add_cos_sq (InnerProductGeometry.angle w u)]
  have hsin : 0 ≤ Real.sin (InnerProductGeometry.angle w u) :=
    InnerProductGeometry.sin_angle_nonneg w u
  nlinarith [norm_nonneg (sphericalTangent w u)]

/-- The interior spherical angle at `w` between the great-circle arcs from `w` to `u` and `v`. -/
@[expose]
noncomputable def sphericalAngle (u w v : E) : ℝ :=
  InnerProductGeometry.angle (sphericalTangent w u) (sphericalTangent w v)

lemma sphericalAngle_comm (u w v : E) : sphericalAngle u w v = sphericalAngle v w u :=
  InnerProductGeometry.angle_comm _ _

lemma sphericalAngle_nonneg (u w v : E) : 0 ≤ sphericalAngle u w v :=
  InnerProductGeometry.angle_nonneg _ _

lemma sphericalAngle_le_pi (u w v : E) : sphericalAngle u w v ≤ π :=
  InnerProductGeometry.angle_le_pi _ _

lemma sin_sphericalAngle_nonneg (u w v : E) : 0 ≤ Real.sin (sphericalAngle u w v) :=
  InnerProductGeometry.sin_angle_nonneg _ _

/-! ### 2. Spherical Law of Cosines, Triangle Inequality, and Law of Sines -/

/-- **Spherical Law of Cosines:**
For any three unit vectors `u, v, w` in a real inner product space,
`cos(angle u v) = cos(angle w u) * cos(angle w v) + sin(angle w u) * sin(angle w v) * cos(sphericalAngle u w v)`. -/
theorem spherical_law_of_cosines {u v w : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    Real.cos (InnerProductGeometry.angle u v) =
      Real.cos (InnerProductGeometry.angle w u) * Real.cos (InnerProductGeometry.angle w v) +
        Real.sin (InnerProductGeometry.angle w u) * Real.sin (InnerProductGeometry.angle w v) *
          Real.cos (sphericalAngle u w v) := by
  have hcos_uv : Real.cos (InnerProductGeometry.angle u v) = ⟪u, v⟫ := by
    rw [InnerProductGeometry.cos_angle, hu, hv, mul_one, div_one]
  have hcos_wu : Real.cos (InnerProductGeometry.angle w u) = ⟪w, u⟫ := by
    rw [InnerProductGeometry.cos_angle, hw, hu, mul_one, div_one]
  have hcos_wv : Real.cos (InnerProductGeometry.angle w v) = ⟪w, v⟫ := by
    rw [InnerProductGeometry.cos_angle, hw, hv, mul_one, div_one]
  have htan := InnerProductGeometry.cos_angle_mul_norm_mul_norm
    (sphericalTangent w u) (sphericalTangent w v)
  rw [norm_sphericalTangent hw hu, norm_sphericalTangent hw hv, inner_sphericalTangent hw] at htan
  rw [hcos_uv, hcos_wu, hcos_wv, real_inner_comm u w, real_inner_comm v w]
  unfold sphericalAngle
  linarith

/-- **Spherical Triangle Inequality:**
Geodesic distance `InnerProductGeometry.angle` satisfies the triangle inequality. Delegates to
Mathlib's `InnerProductGeometry.angle_le_angle_add_angle`. -/
theorem spherical_triangle_inequality (u v w : E) :
    InnerProductGeometry.angle u v ≤
      InnerProductGeometry.angle u w + InnerProductGeometry.angle w v :=
  InnerProductGeometry.angle_le_angle_add_angle u w v

/-- The symmetric `3 × 3` Gram determinant of three unit vectors `u, v, w`:
`1 + 2 ⟪u, v⟫ ⟪v, w⟫ ⟪w, u⟫ - ⟪u, v⟫² - ⟪v, w⟫² - ⟪w, u⟫²`.
See `gramDet3_eq_det_gram` for the identification with `(Matrix.gram ℝ ![u, v, w]).det`. -/
@[expose]
def gramDet3 (u v w : E) : ℝ :=
  1 + 2 * ⟪u, v⟫ * ⟪v, w⟫ * ⟪w, u⟫ - ⟪u, v⟫ ^ 2 - ⟪v, w⟫ ^ 2 - ⟪w, u⟫ ^ 2

/-- For unit vectors `u, v, w`, `gramDet3 u v w` equals the determinant of Mathlib's Gram matrix
`Matrix.gram ℝ ![u, v, w]`. -/
theorem gramDet3_eq_det_gram {u v w : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    gramDet3 u v w = (Matrix.gram ℝ ![u, v, w]).det := by
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hvv : ⟪v, v⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hv, one_pow]
  have hww : ⟪w, w⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hw, one_pow]
  rw [Matrix.det_fin_three]
  simp only [Matrix.gram_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, huu, hvv, hww, real_inner_comm v u,
    real_inner_comm w v, real_inner_comm u w, gramDet3]
  ring

lemma gramDet3_cyc (u v w : E) : gramDet3 u v w = gramDet3 v w u := by
  unfold gramDet3; ring

lemma gramDet3_swap (u v w : E) : gramDet3 u v w = gramDet3 v u w := by
  unfold gramDet3
  rw [real_inner_comm v u, real_inner_comm u w, real_inner_comm w v]
  ring

/-- Identity expressing `gramDet3 u v w` as
`(sin(angle w u) * sin(angle w v) * sin(sphericalAngle u w v))²`. -/
theorem gramDet3_eq_sq_sin_mul {u v w : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    gramDet3 u v w =
      (Real.sin (InnerProductGeometry.angle w u) * Real.sin (InnerProductGeometry.angle w v) *
        Real.sin (sphericalAngle u w v)) ^ 2 := by
  have hlaw := spherical_law_of_cosines hu hv hw
  have hcos_uv : Real.cos (InnerProductGeometry.angle u v) = ⟪u, v⟫ := by
    rw [InnerProductGeometry.cos_angle, hu, hv, mul_one, div_one]
  have hcos_wu : Real.cos (InnerProductGeometry.angle w u) = ⟪w, u⟫ := by
    rw [InnerProductGeometry.cos_angle, hw, hu, mul_one, div_one]
  have hcos_wv : Real.cos (InnerProductGeometry.angle w v) = ⟪w, v⟫ := by
    rw [InnerProductGeometry.cos_angle, hw, hv, mul_one, div_one]
  have h1 : Real.cos (InnerProductGeometry.angle w u) ^ 2 =
      1 - Real.sin (InnerProductGeometry.angle w u) ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq (InnerProductGeometry.angle w u)]
  have h2 : Real.cos (InnerProductGeometry.angle w v) ^ 2 =
      1 - Real.sin (InnerProductGeometry.angle w v) ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq (InnerProductGeometry.angle w v)]
  have h3 : Real.cos (sphericalAngle u w v) ^ 2 =
      1 - Real.sin (sphericalAngle u w v) ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq (sphericalAngle u w v)]
  have hinner_vw : ⟪v, w⟫ = ⟪w, v⟫ := real_inner_comm w v
  unfold gramDet3
  rw [hinner_vw, ← hcos_uv, ← hcos_wu, ← hcos_wv, hlaw]
  set ca := Real.cos (InnerProductGeometry.angle w u)
  set cb := Real.cos (InnerProductGeometry.angle w v)
  set sa := Real.sin (InnerProductGeometry.angle w u)
  set sb := Real.sin (InnerProductGeometry.angle w v)
  set cg := Real.cos (sphericalAngle u w v)
  set sg := Real.sin (sphericalAngle u w v)
  calc
    1 + 2 * (ca * cb + sa * sb * cg) * cb * ca - (ca * cb + sa * sb * cg) ^ 2 - cb ^ 2 - ca ^ 2
      = (1 - ca ^ 2) * (1 - cb ^ 2) - sa ^ 2 * sb ^ 2 * cg ^ 2 := by ring
    _ = sa ^ 2 * sb ^ 2 * (1 - cg ^ 2) := by rw [h1, h2]; ring
    _ = (sa * sb * sg) ^ 2 := by rw [h3]; ring

theorem gramDet3_nonneg {u v w : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    0 ≤ gramDet3 u v w := by
  rw [gramDet3_eq_sq_sin_mul hu hv hw]
  exact sq_nonneg _

theorem sin_mul_sin_mul_sin_sphericalAngle {u v w : E}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    Real.sin (InnerProductGeometry.angle w u) * Real.sin (InnerProductGeometry.angle w v) *
      Real.sin (sphericalAngle u w v) = Real.sqrt (gramDet3 u v w) := by
  rw [gramDet3_eq_sq_sin_mul hu hv hw, Real.sqrt_sq]
  exact mul_nonneg
    (mul_nonneg (InnerProductGeometry.sin_angle_nonneg w u)
      (InnerProductGeometry.sin_angle_nonneg w v))
    (sin_sphericalAngle_nonneg u w v)

/-- **Spherical Law of Sines (multiplicative form):**
For any three unit vectors `u, v, w` in a real inner product space,
`sin(sphericalAngle u w v) * sin(angle v w) * sin(angle w u) =
  sin(sphericalAngle v u w) * sin(angle u v) * sin(angle w u)`.
Dividing by `sin(angle w u)` (when nonzero) yields `spherical_law_of_sines`. -/
theorem spherical_law_of_sines_mul {u v w : E}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    Real.sin (sphericalAngle u w v) * Real.sin (InnerProductGeometry.angle v w) *
        Real.sin (InnerProductGeometry.angle w u) =
      Real.sin (sphericalAngle v u w) * Real.sin (InnerProductGeometry.angle u v) *
        Real.sin (InnerProductGeometry.angle w u) := by
  have h1 := sin_mul_sin_mul_sin_sphericalAngle hu hv hw
  have h2 := sin_mul_sin_mul_sin_sphericalAngle hv hw hu
  have hg : gramDet3 u v w = gramDet3 v w u := gramDet3_cyc u v w
  have hcomm1 : InnerProductGeometry.angle u w = InnerProductGeometry.angle w u :=
    InnerProductGeometry.angle_comm u w
  have hcomm2 : InnerProductGeometry.angle w v = InnerProductGeometry.angle v w :=
    InnerProductGeometry.angle_comm w v
  rw [hcomm1] at h2
  rw [hcomm2] at h1
  rw [← hg] at h2
  linarith

theorem spherical_law_of_sines {u v w : E}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : Real.sin (InnerProductGeometry.angle u v) ≠ 0)
    (hvw : Real.sin (InnerProductGeometry.angle v w) ≠ 0)
    (hwu : Real.sin (InnerProductGeometry.angle w u) ≠ 0) :
    Real.sin (sphericalAngle u w v) / Real.sin (InnerProductGeometry.angle u v) =
      Real.sin (sphericalAngle v u w) / Real.sin (InnerProductGeometry.angle v w) := by
  have hmul := spherical_law_of_sines_mul hu hv hw
  have hcancel : Real.sin (sphericalAngle u w v) * Real.sin (InnerProductGeometry.angle v w) =
      Real.sin (sphericalAngle v u w) * Real.sin (InnerProductGeometry.angle u v) :=
    mul_right_cancel₀ hwu hmul
  rw [div_eq_div_iff huv hvw]
  exact hcancel

/-! ### 3. Dihedral Angles -/

/-- The interior **dihedral angle** between two half-spaces `{x | ⟪x, n₁⟫ ≤ 0}` and
`{x | ⟪x, n₂⟫ ≤ 0}` with outer normals `n₁, n₂`, defined as `π - angle n₁ n₂`. -/
@[expose]
noncomputable def dihedralAngle (n₁ n₂ : E) : ℝ :=
  π - InnerProductGeometry.angle n₁ n₂

lemma dihedralAngle_comm (n₁ n₂ : E) : dihedralAngle n₁ n₂ = dihedralAngle n₂ n₁ := by
  simp [dihedralAngle, InnerProductGeometry.angle_comm]

lemma dihedralAngle_nonneg (n₁ n₂ : E) : 0 ≤ dihedralAngle n₁ n₂ := by
  unfold dihedralAngle; linarith [InnerProductGeometry.angle_le_pi n₁ n₂]

lemma dihedralAngle_le_pi (n₁ n₂ : E) : dihedralAngle n₁ n₂ ≤ π := by
  unfold dihedralAngle; linarith [InnerProductGeometry.angle_nonneg n₁ n₂]

lemma cos_dihedralAngle (n₁ n₂ : E) :
    Real.cos (dihedralAngle n₁ n₂) = -⟪n₁, n₂⟫ / (‖n₁‖ * ‖n₂‖) := by
  unfold dihedralAngle
  rw [Real.cos_pi_sub, InnerProductGeometry.cos_angle, neg_div]

lemma dihedralAngle_neg_left (n₁ n₂ : E) :
    dihedralAngle (-n₁) n₂ = InnerProductGeometry.angle n₁ n₂ := by
  unfold dihedralAngle
  rw [InnerProductGeometry.angle_neg_left]
  ring

/-! ### 4. Spherical Caps -/

/-- The closed **spherical cap** centered at `u` of height threshold `t`:
`sphericalCap u t = {v ∈ Metric.sphere 0 1 | t ≤ ⟪v, u⟫}`. -/
@[expose]
def sphericalCap (u : E) (t : ℝ) : Set E :=
  {v ∈ Metric.sphere (0 : E) 1 | t ≤ ⟪v, u⟫}

lemma mem_sphericalCap {u v : E} {t : ℝ} :
    v ∈ sphericalCap u t ↔ ‖v‖ = 1 ∧ t ≤ ⟪v, u⟫ := by
  simp [sphericalCap]

lemma sphericalCap_antitone (u : E) : Antitone (sphericalCap u) := fun _ _ hle _ hv =>
  ⟨hv.1, hle.trans hv.2⟩

lemma isClosed_sphericalCap (u : E) (t : ℝ) : IsClosed (sphericalCap u t) := by
  change IsClosed (Metric.sphere (0 : E) 1 ∩ {v : E | t ≤ ⟪v, u⟫})
  exact Metric.isClosed_sphere.inter
    (isClosed_le continuous_const (continuous_id.inner continuous_const))

lemma isCompact_sphericalCap [ProperSpace E] (u : E) (t : ℝ) : IsCompact (sphericalCap u t) :=
  (isCompact_sphere (0 : E) 1).of_isClosed_subset (isClosed_sphericalCap u t) fun _ hv => hv.1

/-- Ball characterization of a spherical cap: for `‖u‖ = 1` and `t ≤ 1`,
`sphericalCap u t = Metric.closedBall u (√(2 * (1 - t))) ∩ Metric.sphere 0 1`. -/
theorem sphericalCap_eq_closedBall_inter_sphere {u : E} (hu : ‖u‖ = 1) {t : ℝ} (ht : t ≤ 1) :
    sphericalCap u t = Metric.closedBall u (Real.sqrt (2 * (1 - t))) ∩ Metric.sphere (0 : E) 1 := by
  ext v
  simp only [mem_sphericalCap, Set.mem_inter_iff, Metric.mem_closedBall, Metric.mem_sphere,
    dist_eq_norm, sub_zero]
  constructor
  · rintro ⟨hv, hvu⟩
    refine ⟨?_, hv⟩
    have hsq : ‖v - u‖ ^ 2 ≤ 2 * (1 - t) := by
      rw [norm_sub_sq_real, hv, hu]; linarith
    calc
      ‖v - u‖ = Real.sqrt (‖v - u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (2 * (1 - t)) := Real.sqrt_le_sqrt hsq
  · rintro ⟨hball, hv⟩
    refine ⟨hv, ?_⟩
    have hsq : ‖v - u‖ ^ 2 ≤ 2 * (1 - t) := by
      calc
        ‖v - u‖ ^ 2 ≤ (Real.sqrt (2 * (1 - t))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hball 2
        _ = 2 * (1 - t) := Real.sq_sqrt (by linarith)
    rw [norm_sub_sq_real, hv, hu] at hsq
    linarith

/-- Geodesic-radius characterization of a spherical cap: for `‖u‖ = 1` and `θ ∈ [0, π]`,
`sphericalCap u (cos θ) = {v ∈ sphere 0 1 | angle v u ≤ θ}`. -/
theorem sphericalCap_cos_eq_angle_le {u : E} (hu : ‖u‖ = 1) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθpi : θ ≤ π) :
    sphericalCap u (Real.cos θ) =
      {v ∈ Metric.sphere (0 : E) 1 | InnerProductGeometry.angle v u ≤ θ} := by
  ext v
  simp only [mem_sphericalCap, Set.mem_ofPred_eq, Metric.mem_sphere, dist_zero_right]
  refine and_congr_right fun hv => ?_
  have hcos : Real.cos (InnerProductGeometry.angle v u) = ⟪v, u⟫ := by
    rw [InnerProductGeometry.cos_angle, hv, hu, mul_one, div_one]
  rw [← hcos]
  exact Real.strictAntiOn_cos.le_iff_ge ⟨hθ0, hθpi⟩
    ⟨InnerProductGeometry.angle_nonneg v u, InnerProductGeometry.angle_le_pi v u⟩

/-- Orthogonal isometry equivariance of spherical caps. -/
theorem image_sphericalCap_linearIsometry {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (U : E ≃ₗᵢ[ℝ] F) (u : E) (t : ℝ) :
    U '' sphericalCap u t = sphericalCap (U u) t := by
  ext y
  simp only [Set.mem_image, mem_sphericalCap]
  constructor
  · rintro ⟨x, ⟨hx, hxu⟩, rfl⟩
    exact ⟨by rw [U.norm_map, hx], by rw [U.inner_map_map]; exact hxu⟩
  · rintro ⟨hy, hyu⟩
    refine ⟨U.symm y, ⟨by rw [U.symm.norm_map, hy], ?_⟩, U.apply_symm_apply y⟩
    have h := U.inner_map_map (U.symm y) u
    rw [U.apply_symm_apply] at h
    rwa [← h]

/-- Hemisphere decomposition of the unit sphere. -/
theorem sphericalCap_zero_union_neg (u : E) :
    sphericalCap u 0 ∪ sphericalCap (-u) 0 = Metric.sphere (0 : E) 1 := by
  ext v
  simp only [Set.mem_union, mem_sphericalCap, inner_neg_right, Metric.mem_sphere, dist_zero_right]
  constructor
  · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
  · intro hv
    rcases le_total 0 ⟪v, u⟫ with h | h
    · exact Or.inl ⟨hv, h⟩
    · exact Or.inr ⟨hv, neg_nonneg.mpr h⟩

end

end ConvexGeom
