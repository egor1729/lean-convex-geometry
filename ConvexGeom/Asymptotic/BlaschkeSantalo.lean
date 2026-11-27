/-
Copyright (c) 2026 Yegor Gorodzha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yegor Gorodzha
-/
module

public import ConvexGeom.Asymptotic.GaussianConcentration
public import ConvexGeom.Asymptotic.JohnEllipsoid
public import ConvexGeom.Asymptotic.SphericalIntegration
public import ConvexGeom.Metric.Blaschke
public import ConvexGeom.Metric.Projection
public import ConvexGeom.Volume.BrunnConcavity
public import ConvexGeom.Volume.Continuity
public import ConvexGeom.Volume.Symmetrization

import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Blaschke–Santaló Inequality and Urysohn's Inequality

This module establishes arbitrary-direction Steiner symmetrization, the existence of the Santaló
point, the Meyer–Pajor slice proof of the Blaschke–Santaló inequality, and Urysohn's inequality
in any nontrivial finite-dimensional real inner product space `E`.

## Main definitions

* `ConvexGeom.orthoHyperplane`: the orthogonal hyperplane `(ℝ ∙ u)ᗮ`.
* `ConvexGeom.steinerSymmDir`, `ConvexGeom.bodySteinerSymmDir`: arbitrary-direction Steiner
  symmetrization across `u⊥`.
* `ConvexGeom.secondMoment`: second moment `∫ x in (K : Set E), ‖x‖ ^ 2`.
* `ConvexGeom.polarVolAt`: polar volume functional `z ↦ volume.real (polarBody ((· - z) '' K))`.

## Main statements

* `ConvexGeom.reflectBody_bodySteinerSymmDir`, `ConvexGeom.volume_bodySteinerSymmDir`,
  `ConvexGeom.bodySteinerSymmDir_mono`: core properties of arbitrary-direction Steiner
  symmetrization.
* `ConvexGeom.continuous_secondMoment`, `ConvexGeom.secondMoment_bodySteinerSymmDir_lt`:
  Hausdorff continuity and strict decrease of the second moment under Steiner symmetrization.
* `ConvexGeom.exists_santaloPoint`,
  `ConvexGeom.mahlerVolume_eq_santaloMahlerVolume_of_isOriginSymmetric`,
  `ConvexGeom.upperSemicontinuousOn_santaloMahlerVolume`: Santaló point existence and upper
  semicontinuity of the Santaló Mahler volume.
* `ConvexGeom.santaloMahlerVolume_le_bodySteinerSymmDir`: Meyer–Pajor inequality
  `𝒫*(K) ≤ 𝒫*(S_u K)`.
* `ConvexGeom.blaschke_santalo`, `ConvexGeom.blaschke_santalo_symmetric`: general and
  origin-symmetric Blaschke–Santaló inequalities.
* `ConvexGeom.urysohn_inequality`: Urysohn's volume–mean-width inequality.

## References

* M. Meyer and A. Pajor, *On the Blaschke–Santaló inequality*, Arch. Math. 55 (1990), 82–93
  [meyerpajor1990].
* K. Ball, *An Elementary Introduction to Modern Convex Geometry*, Lectures 2 & 5 [ball1997].
* R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory* [schneider2014].
* S. Artstein-Avidan, A. Giannopoulos, and V. D. Milman, *Asymptotic Geometric Analysis, Part I*
  [agm2015].
-/

open MeasureTheory Set Metric Filter Topology
open scoped RealInnerProductSpace Pointwise ENNReal NNReal

namespace ConvexGeom

public section

/-! ### 1. Arbitrary-Direction Steiner Symmetrization -/

section SteinerDir

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The orthogonal hyperplane `(ℝ ∙ u)ᗮ` associated to a vector `u : E`. -/
noncomputable abbrev orthoHyperplane (u : E) : Submodule ℝ E :=
  (Submodule.span ℝ ({u} : Set E))ᗮ

lemma mem_orthoHyperplane_iff {u x : E} :
    x ∈ orthoHyperplane u ↔ ⟪x, u⟫ = 0 := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h
    rw [real_inner_comm]
    exact h u (Submodule.subset_span (mem_singleton u))
  · intro h y hy
    rcases Submodule.mem_span_singleton.mp hy with ⟨c, rfl⟩
    rw [inner_smul_left, RCLike.conj_to_real, real_inner_comm, h, mul_zero]

/-- Explicit linear isometry splitting `E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × (ℝ ∙ u)ᗮ)` along a unit vector
`u : E` (`‖u‖ = 1`). -/
private noncomputable def orthoSplit {u : E} (hu : ‖u‖ = 1) :
    E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × orthoHyperplane u) where
  toFun x := WithLp.toLp 2 (⟪x, u⟫, ⟨x - ⟪x, u⟫ • u, by
    rw [mem_orthoHyperplane_iff, inner_sub_left, inner_smul_left, RCLike.conj_to_real,
      real_inner_self_eq_norm_sq, hu, one_pow, mul_one, sub_self]⟩)
  invFun p := (WithLp.ofLp p).1 • u + ((WithLp.ofLp p).2 : E)
  left_inv x := by
    change ⟪x, u⟫ • u + (x - ⟪x, u⟫ • u) = x
    abel
  right_inv p := by
    apply WithLp.ofLp_injective 2
    rcases p with ⟨⟨t, ⟨y, hy⟩⟩⟩
    have hyu : ⟪y, u⟫ = 0 := mem_orthoHyperplane_iff.mp hy
    have hinner : ⟪t • u + y, u⟫ = t := by
      rw [inner_add_left, inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq,
        hu, one_pow, mul_one, hyu, add_zero]
    ext
    · exact hinner
    · change t • u + y - ⟪t • u + y, u⟫ • u = y
      rw [hinner]; abel
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    ext
    · exact inner_add_left x y u
    · change (x + y) - ⟪x + y, u⟫ • u = (x - ⟪x, u⟫ • u) + (y - ⟪y, u⟫ • u)
      rw [inner_add_left, add_smul]; abel
  map_smul' c x := by
    apply WithLp.ofLp_injective 2
    ext
    · simp [inner_smul_left]
    · change c • x - ⟪c • x, u⟫ • u = c • (x - ⟪x, u⟫ • u)
      rw [inner_smul_left, RCLike.conj_to_real, smul_sub, smul_smul]
  norm_map' x := by
    have hsq : ‖WithLp.toLp 2 (⟪x, u⟫, (⟨x - ⟪x, u⟫ • u, by
        rw [mem_orthoHyperplane_iff, inner_sub_left, inner_smul_left, RCLike.conj_to_real,
          real_inner_self_eq_norm_sq, hu, one_pow, mul_one, sub_self]⟩ : orthoHyperplane u))‖ ^ 2 =
        ‖x‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2]
      change ‖⟪x, u⟫‖ ^ 2 + ‖x - ⟪x, u⟫ • u‖ ^ 2 = ‖x‖ ^ 2
      rw [Real.norm_eq_abs, sq_abs, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, hu, mul_one,
        sq_abs, inner_smul_right]
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Coordinate-splitting linear equivalence `E ≃ₗ[ℝ] ℝ × (ℝ ∙ u)ᗮ` (for interfacing with
`steinerSymm` on `ℝ × H`). -/
private noncomputable def orthoSplitProd {u : E} (hu : ‖u‖ = 1) :
    E ≃ₗ[ℝ] ℝ × orthoHyperplane u :=
  (orthoSplit hu).toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ (ℝ × orthoHyperplane u))

private lemma orthoSplitProd_apply {u : E} (hu : ‖u‖ = 1) (x : E) :
    orthoSplitProd hu x = (⟪x, u⟫, ⟨x - ⟪x, u⟫ • u, by
      rw [mem_orthoHyperplane_iff, inner_sub_left, inner_smul_left, RCLike.conj_to_real,
        real_inner_self_eq_norm_sq, hu, one_pow, mul_one, sub_self]⟩) := by
  simp [orthoSplitProd, orthoSplit]

private lemma orthoSplitProd_symm_apply {u : E} (hu : ‖u‖ = 1) (p : ℝ × orthoHyperplane u) :
    (orthoSplitProd hu).symm p = p.1 • u + (p.2 : E) := by
  simp [orthoSplitProd, orthoSplit]

private lemma orthoSplitProd_norm_sq {u : E} (hu : ‖u‖ = 1) (x : E) :
    ‖x‖ ^ 2 = (orthoSplitProd hu x).1 ^ 2 + ‖(orthoSplitProd hu x).2‖ ^ 2 := by
  have h := congrArg (fun r : ℝ => r ^ 2) ((orthoSplit hu).norm_map x)
  rw [WithLp.prod_norm_sq_eq_of_L2] at h
  simpa [orthoSplitProd_apply, orthoSplit, Real.norm_eq_abs, sq_abs] using h.symm

private lemma orthoSplitProd_inner {u : E} (hu : ‖u‖ = 1) (x y : E) :
    ⟪x, y⟫ = (orthoSplitProd hu x).1 * (orthoSplitProd hu y).1 +
      ⟪(orthoSplitProd hu x).2, (orthoSplitProd hu y).2⟫ := by
  have h := (orthoSplit hu).inner_map_map x y
  rw [WithLp.prod_inner_apply] at h
  simpa [orthoSplitProd_apply, orthoSplit, RCLike.inner_apply, mul_comm] using h.symm

private lemma orthoSplitProd_reflectHyperplane {u : E} (hu : ‖u‖ = 1) (x : E) :
    orthoSplitProd hu (reflectHyperplane hu x) =
      (-(orthoSplitProd hu x).1, (orthoSplitProd hu x).2) := by
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  ext
  · simp only [orthoSplitProd_apply, reflectHyperplane_apply, inner_sub_left, inner_smul_left,
      RCLike.conj_to_real, huu, mul_one]
    ring
  · simp only [orthoSplitProd_apply, reflectHyperplane_apply]
    rw [inner_sub_left, inner_smul_left, RCLike.conj_to_real, huu, mul_one]
    have hc : ⟪x, u⟫ - 2 * ⟪x, u⟫ = -⟪x, u⟫ := by ring
    rw [hc, neg_smul, sub_neg_eq_add]
    have h2 : (2 * ⟪x, u⟫) • u = ⟪x, u⟫ • u + ⟪x, u⟫ • u := by rw [two_mul, add_smul]
    rw [h2]; abel

/-- `orthoSplitProd hu` as a homeomorphism `E ≃ₜ ℝ × orthoHyperplane u`. -/
private noncomputable def orthoSplitHomeomorph {u : E} (hu : ‖u‖ = 1) :
    E ≃ₜ ℝ × orthoHyperplane u where
  toEquiv := (orthoSplitProd hu).toEquiv
  continuous_toFun := by
    change Continuous (fun x : E => orthoSplitProd hu x)
    have heq : (fun x : E => orthoSplitProd hu x) =
        fun x : E => (⟪x, u⟫, (⟨x - ⟪x, u⟫ • u, by
          rw [mem_orthoHyperplane_iff, inner_sub_left, inner_smul_left, RCLike.conj_to_real,
            real_inner_self_eq_norm_sq, hu, one_pow, mul_one, sub_self]⟩ : orthoHyperplane u)) :=
      funext (orthoSplitProd_apply hu)
    rw [heq]
    exact (continuous_id.inner continuous_const).prodMk
      (Continuous.subtype_mk
        (continuous_id.sub ((continuous_id.inner continuous_const).smul continuous_const)) _)
  continuous_invFun := by
    change Continuous (fun p : ℝ × orthoHyperplane u => (orthoSplitProd hu).symm p)
    have heq : (fun p : ℝ × orthoHyperplane u => (orthoSplitProd hu).symm p) =
        fun p : ℝ × orthoHyperplane u => p.1 • u + (p.2 : E) :=
      funext (orthoSplitProd_symm_apply hu)
    rw [heq]
    exact (continuous_fst.smul continuous_const).add (continuous_subtype_val.comp continuous_snd)

private lemma orthoSplitHomeomorph_coe {u : E} (hu : ‖u‖ = 1) (x : E) :
    orthoSplitHomeomorph hu x = orthoSplitProd hu x := by
  simp [orthoSplitHomeomorph]

private lemma orthoSplitHomeomorph_symm_coe {u : E} (hu : ‖u‖ = 1) (p : ℝ × orthoHyperplane u) :
    (orthoSplitHomeomorph hu).symm p = (orthoSplitProd hu).symm p := by
  simp [orthoSplitHomeomorph]

private lemma continuous_orthoSplitProd {u : E} (hu : ‖u‖ = 1) :
    Continuous (orthoSplitProd hu) := by
  have heq : (orthoSplitProd hu : E → ℝ × orthoHyperplane u) = orthoSplitHomeomorph hu :=
    funext fun x => (orthoSplitHomeomorph_coe hu x).symm
  rw [heq]
  exact (orthoSplitHomeomorph hu).continuous

private lemma measurableEmbedding_orthoSplitProd [MeasurableSpace E] [BorelSpace E]
    {u : E} (hu : ‖u‖ = 1) :
    MeasurableEmbedding (orthoSplitProd hu) := by
  have heq : (orthoSplitProd hu : E → ℝ × orthoHyperplane u) = orthoSplitHomeomorph hu :=
    funext fun x => (orthoSplitHomeomorph_coe hu x).symm
  rw [heq]
  exact (orthoSplitHomeomorph hu).measurableEmbedding

private lemma measurePreserving_orthoSplitProd [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {u : E} (hu : ‖u‖ = 1) :
    MeasurePreserving (orthoSplitProd hu) (volume : Measure E)
      (volume : Measure (ℝ × orthoHyperplane u)) :=
  (WithLp.volume_preserving_ofLp (U := ℝ) (V := orthoHyperplane u)).comp
    (orthoSplit hu).measurePreserving

/-- **Arbitrary-direction Steiner symmetrization** of `S ⊆ E` across the hyperplane `u⊥`:
conjugates `steinerSymm` on `ℝ × u⊥` by `orthoSplitProd hu`. -/
noncomputable def steinerSymmDir {u : E} (hu : ‖u‖ = 1) (S : Set E) : Set E :=
  (orthoSplitProd hu) ⁻¹' steinerSymm (orthoSplitProd hu '' S)

private lemma mem_steinerSymmDir_iff {u : E} (hu : ‖u‖ = 1) {S : Set E} {x : E} :
    x ∈ steinerSymmDir hu S ↔ orthoSplitProd hu x ∈ steinerSymm (orthoSplitProd hu '' S) :=
  Iff.rfl

private lemma image_steinerSymmDir {u : E} (hu : ‖u‖ = 1) (S : Set E) :
    orthoSplitProd hu '' steinerSymmDir hu S = steinerSymm (orthoSplitProd hu '' S) :=
  Set.image_preimage_eq _ (orthoSplitProd hu).surjective

/-- Coordinate-free membership characterization of `steinerSymmDir hu S`: `x` belongs to the
Steiner symmetrization across `u⊥` iff the line fiber through `x` in direction `u` intersects `S`
and `|⟪x, u⟫|` is at most half the fiber span. -/
lemma mem_steinerSymmDir {u : E} (hu : ‖u‖ = 1) {S : Set E} {x : E} :
    x ∈ steinerSymmDir hu S ↔
      let F : Set ℝ := {t : ℝ | t • u + (x - ⟪x, u⟫ • u) ∈ S}
      F.Nonempty ∧ |⟪x, u⟫| ≤ (sSup F - sInf F) / 2 := by
  have hfib : steinerFiber (orthoSplitProd hu '' S) (orthoSplitProd hu x).2 =
      {t : ℝ | t • u + (x - ⟪x, u⟫ • u) ∈ S} := by
    ext t
    simp only [steinerFiber, mem_ofPred_eq, mem_image]
    constructor
    · rintro ⟨z, hz, hzp⟩
      have hzs : z = (orthoSplitProd hu).symm (t, (orthoSplitProd hu x).2) := by
        rw [← hzp, (orthoSplitProd hu).symm_apply_apply]
      rw [orthoSplitProd_symm_apply, orthoSplitProd_apply] at hzs
      rwa [← hzs]
    · intro ht
      refine ⟨t • u + (x - ⟪x, u⟫ • u), ht, ?_⟩
      have heq : t • u + (x - ⟪x, u⟫ • u) =
          (orthoSplitProd hu).symm (t, (orthoSplitProd hu x).2) := by
        rw [orthoSplitProd_symm_apply, orthoSplitProd_apply]
      rw [heq, (orthoSplitProd hu).apply_symm_apply]
  change (steinerFiber (orthoSplitProd hu '' S) (orthoSplitProd hu x).2).Nonempty ∧
      |(orthoSplitProd hu x).1| ≤
        (sSup (steinerFiber (orthoSplitProd hu '' S) (orthoSplitProd hu x).2) -
          sInf (steinerFiber (orthoSplitProd hu '' S) (orthoSplitProd hu x).2)) / 2 ↔ _
  rw [hfib, orthoSplitProd_apply]

/-- Bundled arbitrary-direction Steiner symmetrization on `ConvexBody E`. -/
noncomputable def bodySteinerSymmDir {u : E} (hu : ‖u‖ = 1) (K : ConvexBody E) : ConvexBody E where
  carrier := steinerSymmDir hu (K : Set E)
  convex' := by
    have hKc : IsCompact (orthoSplitProd hu '' (K : Set E)) :=
      K.isCompact.image (continuous_orthoSplitProd hu)
    have hKconv : Convex ℝ (orthoSplitProd hu '' (K : Set E)) :=
      K.convex.linear_image (orthoSplitProd hu).toLinearMap
    exact (convex_steinerSymm hKconv hKc).linear_preimage (orthoSplitProd hu).toLinearMap
  isCompact' := by
    have hKc : IsCompact (orthoSplitProd hu '' (K : Set E)) :=
      K.isCompact.image (continuous_orthoSplitProd hu)
    have heq : steinerSymmDir hu (K : Set E) =
        (orthoSplitHomeomorph hu).symm '' steinerSymm (orthoSplitProd hu '' (K : Set E)) := by
      ext x
      simp only [steinerSymmDir, mem_preimage, mem_image, orthoSplitHomeomorph_symm_coe]
      exact ⟨fun hx => ⟨orthoSplitProd hu x, hx, (orthoSplitProd hu).symm_apply_apply x⟩,
        fun ⟨p, hp, hpx⟩ => by rw [← hpx, (orthoSplitProd hu).apply_symm_apply]; exact hp⟩
    rw [heq]
    exact (isCompact_steinerSymm hKc).image (orthoSplitHomeomorph hu).symm.continuous
  nonempty' := by
    let hK' : ConvexBody (ℝ × orthoHyperplane u) :=
      { carrier := orthoSplitProd hu '' (K : Set E)
        convex' := K.convex.linear_image (orthoSplitProd hu).toLinearMap
        isCompact' := K.isCompact.image (continuous_orthoSplitProd hu)
        nonempty' := K.nonempty.image _ }
    obtain ⟨p, hp⟩ := (bodySteinerSymm hK').nonempty
    rw [coe_bodySteinerSymm] at hp
    exact ⟨(orthoSplitProd hu).symm p, by
      rw [mem_steinerSymmDir_iff, (orthoSplitProd hu).apply_symm_apply]
      exact hp⟩

@[simp]
lemma coe_bodySteinerSymmDir {u : E} (hu : ‖u‖ = 1) (K : ConvexBody E) :
    (bodySteinerSymmDir hu K : Set E) = steinerSymmDir hu (K : Set E) := by
  rw [bodySteinerSymmDir]
  rfl

/-- `bodySteinerSymmDir hu K` is invariant under reflection across `u⊥`. -/
theorem reflectBody_bodySteinerSymmDir {u : E} (hu : ‖u‖ = 1) (K : ConvexBody E) :
    reflectBody hu (bodySteinerSymmDir hu K) = bodySteinerSymmDir hu K := by
  apply ConvexBody.ext
  ext x
  rw [coe_reflectBody, coe_bodySteinerSymmDir]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_steinerSymmDir_iff, orthoSplitProd_reflectHyperplane]
    exact (steinerSymm_symm _ _ _).mpr hy
  · intro hx
    refine ⟨reflectHyperplane hu x, ?_, reflectHyperplane_involutive hu x⟩
    rw [mem_steinerSymmDir_iff, orthoSplitProd_reflectHyperplane]
    exact (steinerSymm_symm _ _ _).mpr hx

/-- Monotonicity of arbitrary-direction Steiner symmetrization. -/
theorem bodySteinerSymmDir_mono {u : E} (hu : ‖u‖ = 1) {K L : ConvexBody E}
    (hKL : (K : Set E) ⊆ L) :
    (bodySteinerSymmDir hu K : Set E) ⊆ bodySteinerSymmDir hu L := by
  intro x hx
  have hLc : IsCompact (orthoSplitProd hu '' (L : Set E)) :=
    L.isCompact.image (continuous_orthoSplitProd hu)
  exact steinerSymm_mono hLc (Set.image_mono hKL) hx

/-- If `K` is already symmetric across `u⊥`, Steiner symmetrization across `u⊥` leaves `K` fixed. -/
theorem bodySteinerSymmDir_eq_self_of_reflectBody {u : E} (hu : ‖u‖ = 1) {K : ConvexBody E}
    (hrefl : reflectBody hu K = K) :
    bodySteinerSymmDir hu K = K := by
  let K' : Set (ℝ × orthoHyperplane u) := orthoSplitProd hu '' (K : Set E)
  have hK'c : IsCompact K' := K.isCompact.image (continuous_orthoSplitProd hu)
  have hK'conv : Convex ℝ K' := K.convex.linear_image (orthoSplitProd hu).toLinearMap
  have hK'sym : ∀ t y, (-t, y) ∈ K' ↔ (t, y) ∈ K' := fun t y => by
    constructor
    · rintro ⟨x, hx, hxp⟩
      refine ⟨reflectHyperplane hu x, ?_, ?_⟩
      · have : reflectHyperplane hu x ∈ (reflectBody hu K : Set E) := by
          rw [coe_reflectBody]; exact ⟨x, hx, rfl⟩
        rwa [hrefl] at this
      · rw [orthoSplitProd_reflectHyperplane, hxp]; simp
    · rintro ⟨x, hx, hxp⟩
      refine ⟨reflectHyperplane hu x, ?_, ?_⟩
      · have : reflectHyperplane hu x ∈ (reflectBody hu K : Set E) := by
          rw [coe_reflectBody]; exact ⟨x, hx, rfl⟩
        rwa [hrefl] at this
      · rw [orthoSplitProd_reflectHyperplane, hxp]
  apply ConvexBody.ext
  ext x
  rw [coe_bodySteinerSymmDir, mem_steinerSymmDir_iff]
  set p := orthoSplitProd hu x
  have hxK : x ∈ (K : Set E) ↔ p ∈ K' :=
    ⟨fun h => ⟨x, h, rfl⟩, fun ⟨z, hz, hzx⟩ => (orthoSplitProd hu).injective hzx ▸ hz⟩
  rw [hxK]
  by_cases hne : (steinerFiber K' p.2).Nonempty
  · have hfib := steinerFiber_eq_Icc hK'conv hK'c hne
    set a := steinerLower K' p.2
    set b := steinerUpper K' p.2
    have ha_mem : (a, p.2) ∈ K' := (isCompact_steinerFiber hK'c p.2).sInf_mem hne
    have hb_mem : (b, p.2) ∈ K' := (isCompact_steinerFiber hK'c p.2).sSup_mem hne
    have hneg_a : -a ∈ Icc a b := hfib ▸ ((hK'sym a p.2).mpr ha_mem)
    have hneg_b : -b ∈ Icc a b := hfib ▸ ((hK'sym b p.2).mpr hb_mem)
    have hab_eq : a = -b := by linarith [hneg_a.2, hneg_b.1]
    have hhalf : (b - a) / 2 = b := by linarith
    have hp_iff : p ∈ K' ↔ p.1 ∈ Icc a b := by
      have : p ∈ K' ↔ p.1 ∈ steinerFiber K' p.2 := Iff.rfl
      rw [this, hfib]
    rw [hp_iff, hab_eq]
    change (steinerFiber K' p.2).Nonempty ∧ |p.1| ≤ (b - a) / 2 ↔ p.1 ∈ Icc (-b) b
    rw [hhalf, abs_le, mem_Icc]
    simp [hne]
  · constructor
    · intro h; exact absurd h.1 hne
    · intro hp; exact absurd ⟨p.1, hp⟩ hne

/-- Steiner symmetrization leaves every origin-centered closed ball fixed. -/
theorem bodySteinerSymmDir_bodyClosedBall [ProperSpace E] {u : E} (hu : ‖u‖ = 1)
    {r : ℝ} (hr : 0 ≤ r) :
    bodySteinerSymmDir hu (bodyClosedBall (0 : E) hr) = bodyClosedBall (0 : E) hr := by
  apply bodySteinerSymmDir_eq_self_of_reflectBody
  apply ConvexBody.ext
  ext x
  rw [coe_reflectBody, coe_bodyClosedBall]
  simp only [mem_image, mem_closedBall_zero_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩; rwa [(reflectHyperplane hu).norm_map]
  · intro hx
    refine ⟨reflectHyperplane hu x, ?_, reflectHyperplane_involutive hu x⟩
    rwa [(reflectHyperplane hu).norm_map]

/-- **Arbitrary-direction Steiner symmetrization preserves Lebesgue volume.** -/
theorem volume_bodySteinerSymmDir [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E} (hu : ‖u‖ = 1) (K : ConvexBody E) :
    volume (bodySteinerSymmDir hu K : Set E) = volume (K : Set E) := by
  have hmp := measurePreserving_orthoSplitProd hu
  let K' : Set (ℝ × orthoHyperplane u) := orthoSplitProd hu '' (K : Set E)
  have hK'c : IsCompact K' := K.isCompact.image (continuous_orthoSplitProd hu)
  have hK'conv : Convex ℝ K' := K.convex.linear_image (orthoSplitProd hu).toLinearMap
  have hpreK : (orthoSplitProd hu) ⁻¹' K' = (K : Set E) :=
    Set.preimage_image_eq _ (orthoSplitProd hu).injective
  have hSm : MeasurableSet (steinerSymm K') := (isCompact_steinerSymm hK'c).isClosed.measurableSet
  rw [coe_bodySteinerSymmDir, steinerSymmDir,
    hmp.measure_preimage hSm.nullMeasurableSet,
    volume_steinerSymm hK'conv hK'c,
    ← hmp.measure_preimage hK'c.isClosed.measurableSet.nullMeasurableSet, hpreK]

/-- Translation by a vector orthogonal to `u` commutes with `bodySteinerSymmDir hu`. -/
theorem bodySteinerSymmDir_translate_orth {u : E} (hu : ‖u‖ = 1) (K : ConvexBody E)
    {v : E} (hv : ⟪v, u⟫ = 0) :
    bodySteinerSymmDir hu (K + bodySingleton v) = bodySteinerSymmDir hu K + bodySingleton v := by
  let vH : orthoHyperplane u := ⟨v, mem_orthoHyperplane_iff.mpr hv⟩
  have hsplit_v : orthoSplitProd hu v = (0, vH) := by
    ext
    · rw [orthoSplitProd_apply]; exact hv
    · simp only [orthoSplitProd_apply, vH, hv, zero_smul, sub_zero]
  have hfib_shift : ∀ y : orthoHyperplane u,
      steinerFiber (orthoSplitProd hu '' ((K + bodySingleton v : ConvexBody E) : Set E)) y =
        steinerFiber (orthoSplitProd hu '' (K : Set E)) (y - vH) := fun y => by
    ext t
    simp only [steinerFiber, mem_ofPred_eq, mem_image, ConvexBody.coe_add, coe_bodySingleton,
      Set.mem_add, mem_singleton_iff]
    constructor
    · rintro ⟨_, ⟨x, hx, z, hzv, rfl⟩, htx⟩
      rw [hzv] at htx
      refine ⟨x, hx, ?_⟩
      rw [map_add, hsplit_v, Prod.mk_add_mk, add_zero] at htx
      have h1 := congrArg Prod.fst htx
      have h2 := congrArg Prod.snd htx
      dsimp only at h1 h2
      exact Prod.ext h1 (eq_sub_of_add_eq h2)
    · rintro ⟨x, hx, htx⟩
      refine ⟨x + v, ⟨x, hx, v, rfl, rfl⟩, ?_⟩
      rw [map_add, hsplit_v, htx, Prod.mk_add_mk, add_zero, sub_add_cancel]
  apply ConvexBody.ext
  ext x
  rw [ConvexBody.coe_add, coe_bodySingleton, coe_bodySteinerSymmDir, coe_bodySteinerSymmDir]
  simp only [Set.mem_add, mem_singleton_iff]
  constructor
  · intro hx
    refine ⟨x - v, ?_, v, rfl, sub_add_cancel x v⟩
    rw [mem_steinerSymmDir_iff] at hx ⊢
    have hxv : orthoSplitProd hu (x - v) = ((orthoSplitProd hu x).1, (orthoSplitProd hu x).2 - vH) := by
      rw [map_sub, hsplit_v, Prod.mk_sub_mk, sub_zero]
    rw [hxv]
    have hfib := hfib_shift (orthoSplitProd hu x).2
    simpa only [steinerSymm, mem_ofPred_eq, steinerUpper, steinerLower, hfib] using hx
  · rintro ⟨w, hw, z, hzv, rfl⟩
    rw [hzv]
    rw [mem_steinerSymmDir_iff] at hw ⊢
    have hwv : orthoSplitProd hu (w + v) = ((orthoSplitProd hu w).1, (orthoSplitProd hu w).2 + vH) := by
      rw [map_add, hsplit_v, Prod.mk_add_mk, add_zero]
    rw [hwv]
    have hfib := hfib_shift ((orthoSplitProd hu w).2 + vH)
    rw [add_sub_cancel_right] at hfib
    simpa only [steinerSymm, mem_ofPred_eq, steinerUpper, steinerLower, hfib] using hw

end SteinerDir

/-! ### 2. Second Moment Functional and Strict Decrease under Steiner Symmetrization -/

section SecondMoment

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The **second moment** (moment of inertia) of a convex body `K`: `∫ x in K, ‖x‖²`. -/
@[expose]
noncomputable def secondMoment (K : ConvexBody E) : ℝ :=
  ∫ x in (K : Set E), ‖x‖ ^ 2

/-- Hausdorff continuity of `secondMoment` on `ConvexBody E`. -/
theorem continuous_secondMoment : Continuous (secondMoment (E := E)) := by
  rw [continuous_iff_continuousAt]
  intro K
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨R₀, hKR₀⟩ := K.isBounded.subset_closedBall (0 : E)
  set R : ℝ := max R₀ 0 + 1
  have hR_pos : 0 < R := by positivity
  have hR2_pos : 0 < R ^ 2 := by positivity
  have hsymm := Metric.tendsto_nhds.mp (tendsto_symmDiffVolReal_self (volume : Measure E) K)
    (ε / R ^ 2) (div_pos hε hR2_pos)
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.eventually_nhds_iff.mp hsymm
  refine ⟨min δ 1, lt_min hδ_pos zero_lt_one, fun L hLK => ?_⟩
  have hLK1 : dist L K < 1 := hLK.trans_le (min_le_right _ _)
  have hLR : (L : Set E) ⊆ closedBall (0 : E) R := fun x hxL => by
    obtain ⟨y, hyK, hxy⟩ := K.isCompact.exists_infDist_eq_dist K.nonempty x
    have hdist_xy : dist x y ≤ dist L K := by
      rw [← hxy]
      exact (Metric.infDist_le_hausdorffDist_of_mem hxL ConvexBody.hausdorffEDist_ne_top).trans
        (by rw [ConvexBody.hausdorffDist_coe])
    have hyR₀ : ‖y‖ ≤ R₀ := by simpa [mem_closedBall_zero_iff] using hKR₀ hyK
    have hxy' : ‖x - y‖ < 1 := by simpa [dist_eq_norm] using hdist_xy.trans_lt hLK1
    rw [mem_closedBall_zero_iff]
    have htri : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by simpa [sub_add_cancel] using norm_add_le (x - y) y
    have : R₀ ≤ max R₀ 0 := le_max_left _ _
    dsimp only [R]; linarith
  have hKR : (K : Set E) ⊆ closedBall (0 : E) R :=
    hKR₀.trans (closedBall_subset_closedBall (by dsimp only [R]; linarith [le_max_left R₀ 0]))
  have hint_fn : ∀ A : ConvexBody E,
      Integrable ((A : Set E).indicator fun x : E => ‖x‖ ^ 2) volume := fun A =>
    (integrable_indicator_iff A.isClosed.measurableSet).mpr
      ((continuous_norm.pow 2).continuousOn.integrableOn_compact A.isCompact)
  have hdiff_eq : secondMoment L - secondMoment K =
      ∫ x : E, ((L : Set E).indicator (fun y => ‖y‖ ^ 2) x -
        (K : Set E).indicator (fun y => ‖y‖ ^ 2) x) := by
    rw [secondMoment, secondMoment, ← integral_indicator L.isClosed.measurableSet,
      ← integral_indicator K.isClosed.measurableSet, ← integral_sub (hint_fn L) (hint_fn K)]
  have hpt_le : ∀ x : E,
      |(L : Set E).indicator (fun y => ‖y‖ ^ 2) x - (K : Set E).indicator (fun y => ‖y‖ ^ 2) x| ≤
        (symmDiff (K : Set E) (L : Set E)).indicator (fun _ => R ^ 2) x := fun x => by
    by_cases hxL : x ∈ (L : Set E) <;> by_cases hxK : x ∈ (K : Set E)
    · simp [indicator_of_mem hxL, indicator_of_mem hxK,
        indicator_of_notMem (show x ∉ symmDiff (K : Set E) (L : Set E) by simp [symmDiff, hxK, hxL])]
    · have hxS : x ∈ symmDiff (K : Set E) (L : Set E) := Or.inr ⟨hxL, hxK⟩
      rw [indicator_of_mem hxL, indicator_of_notMem hxK, indicator_of_mem hxS, sub_zero,
        abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg x) (mem_closedBall_zero_iff.mp (hLR hxL)) 2
    · have hxS : x ∈ symmDiff (K : Set E) (L : Set E) := Or.inl ⟨hxK, hxL⟩
      rw [indicator_of_notMem hxL, indicator_of_mem hxK, indicator_of_mem hxS, zero_sub, abs_neg,
        abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg x) (mem_closedBall_zero_iff.mp (hKR hxK)) 2
    · simp [indicator_of_notMem hxL, indicator_of_notMem hxK,
        indicator_of_notMem (show x ∉ symmDiff (K : Set E) (L : Set E) by simp [symmDiff, hxK, hxL])]
  have hSD_meas : MeasurableSet (symmDiff (K : Set E) (L : Set E)) :=
    (K.isClosed.measurableSet.diff L.isClosed.measurableSet).union
      (L.isClosed.measurableSet.diff K.isClosed.measurableSet)
  have hSD_fin : volume (symmDiff (K : Set E) (L : Set E)) < ⊤ :=
    (measure_mono (symmDiff_subset_union)).trans_lt
      (K.isCompact.union L.isCompact).measure_lt_top
  have hint_rhs : Integrable ((symmDiff (K : Set E) (L : Set E)).indicator fun _ : E => R ^ 2) volume :=
    (integrable_indicator_iff hSD_meas).mpr (integrableOn_const (C := R ^ 2) hSD_fin.ne)
  have hvol_lt : symmDiffVolReal (volume : Measure E) (K : Set E) (L : Set E) < ε / R ^ 2 := by
    have h1 := hδ (hLK.trans_le (min_le_left _ _))
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (symmDiffVolReal_nonneg _ _ _)] at h1
  rw [Real.dist_eq, hdiff_eq]
  calc
    |∫ x : E, ((L : Set E).indicator (fun y => ‖y‖ ^ 2) x -
        (K : Set E).indicator (fun y => ‖y‖ ^ 2) x)|
      ≤ ∫ x : E, |(L : Set E).indicator (fun y => ‖y‖ ^ 2) x -
          (K : Set E).indicator (fun y => ‖y‖ ^ 2) x| := abs_integral_le_integral_abs
    _ ≤ ∫ x : E, (symmDiff (K : Set E) (L : Set E)).indicator (fun _ => R ^ 2) x :=
        integral_mono ((hint_fn L).sub (hint_fn K)).abs hint_rhs hpt_le
    _ = R ^ 2 * symmDiffVolReal (volume : Measure E) (K : Set E) (L : Set E) := by
        rw [integral_indicator hSD_meas, setIntegral_const, smul_eq_mul, mul_comm]
        rfl
    _ < R ^ 2 * (ε / R ^ 2) := mul_lt_mul_of_pos_left hvol_lt hR2_pos
    _ = ε := mul_div_cancel₀ ε hR2_pos.ne'

/-- Exact 1D fiber identity: `∫ t in Icc a b, t² - ∫ t in Icc (-(b-a)/2) ((b-a)/2), t² = (b - a) * ((a + b) / 2)²`. -/
private lemma integral_sq_Icc_sub_symm {a b : ℝ} (hab : a ≤ b) :
    (∫ t in Icc a b, t ^ 2) -
        (∫ t in Icc (-((b - a) / 2)) ((b - a) / 2), t ^ 2) =
      (b - a) * ((a + b) / 2) ^ 2 := by
  have hIcc_int : ∀ c d : ℝ, c ≤ d → ∫ t in Icc c d, t ^ 2 = (d ^ 3 - c ^ 3) / 3 := fun c d hcd => by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hcd,
      integral_pow]
    norm_num
  have h1 := hIcc_int a b hab
  have h2 := hIcc_int (-((b - a) / 2)) ((b - a) / 2) (by linarith)
  rw [h1, h2]
  ring

/-- **Strict Decrease of Second Moment under Non-Trivial Steiner Symmetrization:**
if `K : ConvexBody E` has nonempty interior and is not symmetric across `u⊥`, then
`secondMoment (bodySteinerSymmDir hu K) < secondMoment K`. -/
theorem secondMoment_bodySteinerSymmDir_lt {u : E} (hu : ‖u‖ = 1) {K : ConvexBody E}
    (hne : (interior (K : Set E)).Nonempty) (hnsym : reflectBody hu K ≠ K) :
    secondMoment (bodySteinerSymmDir hu K) < secondMoment K := by
  classical
  let H := orthoHyperplane u
  let Φ := orthoSplitProd hu
  have hmp : MeasurePreserving Φ (volume : Measure E) (volume : Measure (ℝ × H)) :=
    measurePreserving_orthoSplitProd hu
  have hemb : MeasurableEmbedding Φ := measurableEmbedding_orthoSplitProd hu
  let K' : Set (ℝ × H) := Φ '' (K : Set E)
  let S' : Set (ℝ × H) := steinerSymm K'
  have hK'c : IsCompact K' := K.isCompact.image (continuous_orthoSplitProd hu)
  have hK'conv : Convex ℝ K' := K.convex.linear_image Φ.toLinearMap
  have hS'c : IsCompact S' := isCompact_steinerSymm hK'c
  -- Rewrite both second moments as integrals on `ℝ × H`.
  have hsec_eq : ∀ (A : ConvexBody E),
      secondMoment A = ∫ p : ℝ × H, (Φ '' (A : Set E)).indicator (fun q => q.1 ^ 2 + ‖q.2‖ ^ 2) p := by
    intro A
    rw [secondMoment, ← integral_indicator A.isClosed.measurableSet,
      ← hmp.integral_comp hemb]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have hmem : x ∈ (A : Set E) ↔ Φ x ∈ Φ '' (A : Set E) :=
      ⟨fun h => ⟨x, h, rfl⟩, fun ⟨z, hz, hzx⟩ => Φ.injective hzx ▸ hz⟩
    dsimp only
    by_cases hx : x ∈ (A : Set E)
    · rw [indicator_of_mem hx, indicator_of_mem (hmem.mp hx)]
      exact orthoSplitProd_norm_sq hu x
    · rw [indicator_of_notMem hx, indicator_of_notMem (mt hmem.mpr hx)]
  have hK_sec : secondMoment K = ∫ p : ℝ × H, K'.indicator (fun q => q.1 ^ 2 + ‖q.2‖ ^ 2) p :=
    hsec_eq K
  have hS_sec : secondMoment (bodySteinerSymmDir hu K) =
      ∫ p : ℝ × H, S'.indicator (fun q => q.1 ^ 2 + ‖q.2‖ ^ 2) p := by
    rw [hsec_eq (bodySteinerSymmDir hu K), coe_bodySteinerSymmDir, image_steinerSymmDir]
  have hint_K' : Integrable (K'.indicator fun q : ℝ × H => q.1 ^ 2 + ‖q.2‖ ^ 2)
      ((volume : Measure ℝ).prod (volume : Measure H)) := by
    have hcont : Continuous (fun q : ℝ × H => q.1 ^ 2 + ‖q.2‖ ^ 2) :=
      (continuous_fst.pow 2).add (continuous_snd.norm.pow 2)
    rw [← Measure.volume_eq_prod]
    exact (integrable_indicator_iff hK'c.isClosed.measurableSet).mpr
      (hcont.continuousOn.integrableOn_compact hK'c)
  have hint_S' : Integrable (S'.indicator fun q : ℝ × H => q.1 ^ 2 + ‖q.2‖ ^ 2)
      ((volume : Measure ℝ).prod (volume : Measure H)) := by
    have hcont : Continuous (fun q : ℝ × H => q.1 ^ 2 + ‖q.2‖ ^ 2) :=
      (continuous_fst.pow 2).add (continuous_snd.norm.pow 2)
    rw [← Measure.volume_eq_prod]
    exact (integrable_indicator_iff hS'c.isClosed.measurableSet).mpr
      (hcont.continuousOn.integrableOn_compact hS'c)
  -- Apply Fubini (`integral_prod_symm`) to compute the difference fiber by fiber.
  have hdiff_fib : secondMoment K - secondMoment (bodySteinerSymmDir hu K) =
      ∫ y : H, ((∫ t : ℝ, K'.indicator (fun q => q.1 ^ 2 + ‖q.2‖ ^ 2) (t, y)) -
        (∫ t : ℝ, S'.indicator (fun q => q.1 ^ 2 + ‖q.2‖ ^ 2) (t, y))) := by
    rw [hK_sec, hS_sec, Measure.volume_eq_prod,
      integral_prod_symm _ hint_K', integral_prod_symm _ hint_S',
      ← integral_sub hint_K'.integral_prod_right hint_S'.integral_prod_right]
  -- Evaluate each fiber difference explicitly: `(b - a) * ((a + b) / 2)²` when nonempty, `0` when empty.
  have hfib_val : ∀ y : H,
      (∫ t : ℝ, K'.indicator (fun q => q.1 ^ 2 + ‖q.2‖ ^ 2) (t, y)) -
        (∫ t : ℝ, S'.indicator (fun q => q.1 ^ 2 + ‖q.2‖ ^ 2) (t, y)) =
      if (steinerFiber K' y).Nonempty then
        (steinerUpper K' y - steinerLower K' y) *
          ((steinerLower K' y + steinerUpper K' y) / 2) ^ 2
      else 0 := fun y => by
    by_cases hne_y : (steinerFiber K' y).Nonempty
    · simp only [hne_y, ite_true]
      set a := steinerLower K' y
      set b := steinerUpper K' y
      have hfc := isCompact_steinerFiber hK'c y
      have hab : a ≤ b := csInf_le hfc.bddBelow (hfc.sSup_mem hne_y)
      have hfibK := steinerFiber_eq_Icc hK'conv hK'c hne_y
      have hfibS : {t : ℝ | (t, y) ∈ S'} = Icc (-((b - a) / 2)) ((b - a) / 2) := by
        ext t; simp [S', steinerSymm, hne_y, a, b, abs_le]
      have h1 : (∫ t : ℝ, K'.indicator (fun q => q.1 ^ 2 + ‖q.2‖ ^ 2) (t, y)) =
          (∫ t in Icc a b, t ^ 2) + (b - a) * ‖y‖ ^ 2 := by
        have hind : (fun t : ℝ => K'.indicator (fun q => q.1 ^ 2 + ‖q.2‖ ^ 2) (t, y)) =
            (Icc a b).indicator (fun t : ℝ => t ^ 2 + ‖y‖ ^ 2) := by
          ext t
          have ht : (t, y) ∈ K' ↔ t ∈ Icc a b := by
            change t ∈ steinerFiber K' y ↔ _; rw [hfibK]
          by_cases h : (t, y) ∈ K'
          · rw [indicator_of_mem h, indicator_of_mem (ht.mp h)]
          · rw [indicator_of_notMem h, indicator_of_notMem (mt ht.mpr h)]
        rw [hind, integral_indicator measurableSet_Icc,
          integral_add ((continuous_pow 2).continuousOn.integrableOn_compact isCompact_Icc)
            (integrableOn_const (by simp)),
          setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le hab]
      have h2 : (∫ t : ℝ, S'.indicator (fun q => q.1 ^ 2 + ‖q.2‖ ^ 2) (t, y)) =
          (∫ t in Icc (-((b - a) / 2)) ((b - a) / 2), t ^ 2) + (b - a) * ‖y‖ ^ 2 := by
        have hind : (fun t : ℝ => S'.indicator (fun q => q.1 ^ 2 + ‖q.2‖ ^ 2) (t, y)) =
            (Icc (-((b - a) / 2)) ((b - a) / 2)).indicator (fun t : ℝ => t ^ 2 + ‖y‖ ^ 2) := by
          ext t
          have ht : (t, y) ∈ S' ↔ t ∈ Icc (-((b - a) / 2)) ((b - a) / 2) := by
            have := Set.ext_iff.mp hfibS t; simpa using this
          by_cases h : (t, y) ∈ S'
          · rw [indicator_of_mem h, indicator_of_mem (ht.mp h)]
          · rw [indicator_of_notMem h, indicator_of_notMem (mt ht.mpr h)]
        rw [hind, integral_indicator measurableSet_Icc,
          integral_add ((continuous_pow 2).continuousOn.integrableOn_compact isCompact_Icc)
            (integrableOn_const (by simp)),
          setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by linarith)]
        congr 1; ring
      rw [h1, h2]
      linarith [integral_sq_Icc_sub_symm hab]
    · simp only [hne_y, ite_false]
      have h1 : ∀ t : ℝ, K'.indicator (fun q => q.1 ^ 2 + ‖q.2‖ ^ 2) (t, y) = 0 := fun t =>
        indicator_of_notMem (s := K') (fun h => hne_y ⟨t, h⟩) _
      have h2 : ∀ t : ℝ, S'.indicator (fun q => q.1 ^ 2 + ‖q.2‖ ^ 2) (t, y) = 0 := fun t =>
        indicator_of_notMem (s := S') (fun h => hne_y h.1) _
      simp only [h1, h2, integral_zero, sub_self]
  have hfib_nn : ∀ y : H,
      0 ≤ (∫ t : ℝ, K'.indicator (fun q => q.1 ^ 2 + ‖q.2‖ ^ 2) (t, y)) -
        (∫ t : ℝ, S'.indicator (fun q => q.1 ^ 2 + ‖q.2‖ ^ 2) (t, y)) := fun y => by
    rw [hfib_val y]
    split_ifs with hne_y
    · have hfc := isCompact_steinerFiber hK'c y
      have hab : steinerLower K' y ≤ steinerUpper K' y := csInf_le hfc.bddBelow (hfc.sSup_mem hne_y)
      exact mul_nonneg (sub_nonneg.mpr hab) (sq_nonneg _)
    · exact le_rfl
  -- Find a point `p' ∈ interior K` whose reflection lies outside `K`.
  have hexists_asym : ∃ p : E, p ∈ (K : Set E) ∧ reflectHyperplane hu p ∉ (K : Set E) := by
    by_contra hall
    push Not at hall
    apply hnsym
    apply ConvexBody.ext
    ext x
    rw [coe_reflectBody]
    constructor
    · rintro ⟨z, hz, rfl⟩; exact hall z hz
    · intro hx
      exact ⟨reflectHyperplane hu x, hall x hx, reflectHyperplane_involutive hu x⟩
  obtain ⟨p, hpK, hpr⟩ := hexists_asym
  obtain ⟨q, hq_int⟩ := hne
  have htend : Tendsto (fun ε : ℝ => reflectHyperplane hu (p + ε • (q - p))) (𝓝 0)
      (𝓝 (reflectHyperplane hu p)) := by
    have h1 : Tendsto (fun ε : ℝ => p + ε • (q - p)) (𝓝 0) (𝓝 p) := by
      simpa using (tendsto_const_nhds (x := p)).add ((tendsto_id (x := 𝓝 (0 : ℝ))).smul_const (q - p))
    exact (reflectHyperplane hu).continuous.continuousAt.tendsto.comp h1
  have hev_out : ∀ᶠ ε : ℝ in 𝓝 0, reflectHyperplane hu (p + ε • (q - p)) ∈ (K : Set E)ᶜ :=
    htend.eventually (K.isClosed.isOpen_compl.mem_nhds hpr)
  obtain ⟨η, hη_pos, hη⟩ := Metric.eventually_nhds_iff.mp hev_out
  set ε₀ : ℝ := min (η / 2) (1 / 2)
  have hε₀_pos : 0 < ε₀ := lt_min (half_pos hη_pos) (by norm_num)
  have hε₀_lt1 : ε₀ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  set p' : E := p + ε₀ • (q - p)
  have hp'_int : p' ∈ interior (K : Set E) :=
    K.convex.add_smul_sub_mem_interior hpK hq_int ⟨hε₀_pos, hε₀_lt1.le⟩
  have hp'_out : reflectHyperplane hu p' ∉ (K : Set E) := by
    have hdist : dist ε₀ 0 < η := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hε₀_pos]
      exact (min_le_left _ _).trans_lt (half_lt_self hη_pos)
    exact hη hdist
  obtain ⟨δ₁, hδ₁_pos, hball_in⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp'_int)
  obtain ⟨δ₂, hδ₂_pos, hball_out⟩ := Metric.mem_nhds_iff.mp
    (K.isClosed.isOpen_compl.mem_nhds hp'_out)
  set δ : ℝ := min δ₁ δ₂
  have hδ_pos : 0 < δ := lt_min hδ₁_pos hδ₂_pos
  have hbin : ball p' δ ⊆ (K : Set E) := (ball_subset_ball (min_le_left _ _)).trans hball_in
  have hbout : ball (reflectHyperplane hu p') δ ⊆ (K : Set E)ᶜ :=
    (ball_subset_ball (min_le_right _ _)).trans hball_out
  set t₀ : ℝ := (Φ p').1
  set y₀ : H := (Φ p').2
  -- Show that on the open ball `ball y₀ (δ / 2)` in `H`, the fiber difference is ≥ `δ³ / 64`.
  have hlower_on_ball : ∀ y ∈ ball y₀ (δ / 2),
      δ ^ 3 / 64 ≤ (∫ t : ℝ, K'.indicator (fun q => q.1 ^ 2 + ‖q.2‖ ^ 2) (t, y)) -
        (∫ t : ℝ, S'.indicator (fun q => q.1 ^ 2 + ‖q.2‖ ^ 2) (t, y)) := fun y hy => by
    have hy_lt : ‖y - y₀‖ < δ / 2 := by simpa [dist_eq_norm] using mem_ball.mp hy
    have hmem_in : ∀ t : ℝ, |t - t₀| ≤ δ / 2 → (t, y) ∈ K' := fun t ht => by
      refine ⟨Φ.symm (t, y), hbin ?_, Φ.apply_symm_apply _⟩
      rw [mem_ball, dist_eq_norm]
      have hsq : ‖Φ.symm (t, y) - p'‖ ^ 2 < δ ^ 2 := by
        rw [orthoSplitProd_norm_sq hu (Φ.symm (t, y) - p')]
        have hsub : Φ (Φ.symm (t, y) - p') = (t - t₀, y - y₀) := by
          rw [map_sub, Φ.apply_symm_apply]; rfl
        rw [hsub]
        have h1 : (t - t₀) ^ 2 ≤ (δ / 2) ^ 2 := by
          rw [← sq_abs (t - t₀)]; exact pow_le_pow_left₀ (abs_nonneg _) ht 2
        have h2 : ‖y - y₀‖ ^ 2 < (δ / 2) ^ 2 :=
          pow_lt_pow_left₀ hy_lt (norm_nonneg _) two_ne_zero
        nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 hδ_pos.le hsq
    have hmem_out : (-t₀, y) ∉ K' := by
      rintro ⟨z, hzK, hzp⟩
      have hz_eq : z = Φ.symm (-t₀, y) := by rw [← hzp, Φ.symm_apply_apply]
      have hdist_lt : ‖z - reflectHyperplane hu p'‖ < δ := by
        have hsq : ‖z - reflectHyperplane hu p'‖ ^ 2 < δ ^ 2 := by
          rw [orthoSplitProd_norm_sq hu (z - reflectHyperplane hu p')]
          have hsub : Φ (z - reflectHyperplane hu p') = (0, y - y₀) := by
            rw [map_sub, hzp, orthoSplitProd_reflectHyperplane]
            ext
            · change -t₀ - (-t₀) = 0; ring
            · rfl
          rw [hsub]
          have h2 : ‖y - y₀‖ ^ 2 < (δ / 2) ^ 2 :=
            pow_lt_pow_left₀ hy_lt (norm_nonneg _) two_ne_zero
          nlinarith
        exact lt_of_pow_lt_pow_left₀ 2 hδ_pos.le hsq
      exact hbout (by simpa [mem_ball, dist_eq_norm] using hdist_lt) hzK
    have ht_lo_mem : t₀ - δ / 2 ∈ steinerFiber K' y := hmem_in (t₀ - δ / 2) (by
      rw [show t₀ - δ / 2 - t₀ = -(δ / 2) by ring, abs_neg, abs_of_pos (half_pos hδ_pos)])
    have ht_hi_mem : t₀ + δ / 2 ∈ steinerFiber K' y := hmem_in (t₀ + δ / 2) (by
      rw [show t₀ + δ / 2 - t₀ = δ / 2 by ring, abs_of_pos (half_pos hδ_pos)])
    have hne_y : (steinerFiber K' y).Nonempty := ⟨t₀ - δ / 2, ht_lo_mem⟩
    have hfc := isCompact_steinerFiber hK'c y
    set a := steinerLower K' y
    set b := steinerUpper K' y
    have ha_le : a ≤ t₀ - δ / 2 := csInf_le hfc.bddBelow ht_lo_mem
    have hb_ge : t₀ + δ / 2 ≤ b := le_csSup hfc.bddAbove ht_hi_mem
    have hlen_ge : δ ≤ b - a := by linarith
    have hnot_Icc : -t₀ ∉ Icc a b := by
      rw [← steinerFiber_eq_Icc hK'conv hK'c hne_y]
      exact hmem_out
    have hsum_abs : δ / 2 ≤ |a + b| := by
      rcases le_or_gt 0 t₀ with ht0 | ht0
      · have ha_gt : -t₀ < a := by
          by_contra hle; push Not at hle
          exact hnot_Icc ⟨hle, by linarith⟩
        rw [abs_of_pos (by linarith : 0 < a + b)]; linarith
      · have hb_lt : b < -t₀ := by
          by_contra hle; push Not at hle
          exact hnot_Icc ⟨by linarith, hle⟩
        rw [abs_of_neg (by linarith : a + b < 0)]; linarith
    simp only [hfib_val y, hne_y, ite_true]
    have hsq_ge : (δ / 4) ^ 2 ≤ ((a + b) / 2) ^ 2 := by
      rw [← sq_abs ((a + b) / 2), abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact pow_le_pow_left₀ (by positivity) (by linarith) 2
    calc
      δ ^ 3 / 64 ≤ δ * (δ / 4) ^ 2 := by nlinarith
      _ ≤ (b - a) * ((a + b) / 2) ^ 2 :=
          mul_le_mul hlen_ge hsq_ge (sq_nonneg _) (by linarith)
  -- Integrate the positive lower bound over `ball y₀ (δ / 2)`.
  have hball_pos : 0 < volume.real (ball y₀ (δ / 2)) := by
    rw [Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨isOpen_ball.measure_pos volume ⟨y₀, mem_ball_self (half_pos hδ_pos)⟩,
      (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall y₀ (δ / 2)).measure_lt_top⟩
  have hint_diff := hint_K'.integral_prod_right.sub hint_S'.integral_prod_right
  have hpos_diff : 0 < secondMoment K - secondMoment (bodySteinerSymmDir hu K) := by
    rw [hdiff_fib]
    calc
      0 < volume.real (ball y₀ (δ / 2)) * (δ ^ 3 / 64) := mul_pos hball_pos (by positivity)
      _ = ∫ _y in ball y₀ (δ / 2), (δ ^ 3 / 64) := by rw [setIntegral_const, smul_eq_mul]
      _ ≤ ∫ y in ball y₀ (δ / 2),
            ((∫ t : ℝ, K'.indicator (fun q => q.1 ^ 2 + ‖q.2‖ ^ 2) (t, y)) -
              (∫ t : ℝ, S'.indicator (fun q => q.1 ^ 2 + ‖q.2‖ ^ 2) (t, y))) :=
          setIntegral_mono_on (integrableOn_const
            ((measure_mono ball_subset_closedBall).trans_lt
              (isCompact_closedBall y₀ (δ / 2)).measure_lt_top).ne)
            hint_diff.integrableOn isOpen_ball.measurableSet hlower_on_ball
      _ ≤ ∫ y : H,
            ((∫ t : ℝ, K'.indicator (fun q => q.1 ^ 2 + ‖q.2‖ ^ 2) (t, y)) -
              (∫ t : ℝ, S'.indicator (fun q => q.1 ^ 2 + ‖q.2‖ ^ 2) (t, y))) :=
          setIntegral_le_integral hint_diff (ae_of_all _ hfib_nn)
  linarith

end SecondMoment

/-! ### 3. Polar Volume Convexity, Santaló Point, and Upper Semicontinuity -/

section SantaloPoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Real volume of the polar body of `K` recentered at `z`:
`polarVolAt K z = volume.real (polarBody ((· - z) '' K))`. -/
@[expose]
noncomputable def polarVolAt (K : ConvexBody E) (z : E) : ℝ :=
  volume.real (polarBody ((fun x : E => x - z) '' (K : Set E)))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Helper: `(K + bodySingleton (-z) : Set E) = (· - z) '' K`. -/
private lemma coe_translate_neg (K : ConvexBody E) (z : E) :
    ((K + bodySingleton (-z) : ConvexBody E) : Set E) = (fun x : E => x - z) '' (K : Set E) := by
  ext y
  rw [ConvexBody.coe_add, coe_bodySingleton]
  simp only [Set.mem_add, mem_singleton_iff, mem_image]
  constructor
  · rintro ⟨x, hx, _, rfl, rfl⟩; exact ⟨x, hx, by abel⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, -z, rfl, by abel⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Helper: `z ∈ interior K ↔ 0 ∈ interior ((· - z) '' K)`. -/
private lemma zero_mem_interior_translate_neg {S : Set E} {z : E} (hz : z ∈ interior S) :
    (0 : E) ∈ interior ((fun x : E => x - z) '' S) := by
  let e : E ≃ₜ E := Homeomorph.addRight (-z)
  have himg : (fun x : E => x - z) '' S = e '' S := by ext y; simp [e, sub_eq_add_neg]
  rw [himg, ← e.image_interior]
  exact ⟨z, hz, by simp [e]⟩

/-- Polar-coordinate integral formula for `polarVolAt K z` when `z ∈ interior K`. -/
theorem polarVolAt_eq_integral [Nontrivial E] (K : ConvexBody E) {z : E}
    (hz : z ∈ interior (K : Set E)) :
    polarVolAt K z = volume.real (closedBall (0 : E) 1) *
      ∫ u : sphere (0 : E) 1,
        (supportFn K u.1 - ⟪z, u.1⟫)⁻¹ ^ Module.finrank ℝ E
        ∂(sphereProb (volume : Measure E)) := by
  let Kz : ConvexBody E := K + bodySingleton (-z)
  have hKz_coe : (Kz : Set E) = (fun x : E => x - z) '' (K : Set E) := coe_translate_neg K z
  have h0z : (0 : E) ∈ interior (Kz : Set E) := hKz_coe ▸ zero_mem_interior_translate_neg hz
  have hpol := addHaar_real_polarBody_eq_integral_supportFn_inv_pow (volume : Measure E) Kz h0z
  rw [polarVolAt, ← hKz_coe, hpol]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  have hsup : supportFn Kz u.1 = supportFn K u.1 - ⟪z, u.1⟫ := by
    rw [show Kz = K + bodySingleton (-z) from rfl, supportFn_minkowski_add, supportFn_bodySingleton,
      inner_neg_left, sub_eq_add_neg]
  dsimp only
  rw [hsup]

/-- Helper: `x ↦ (x⁻¹) ^ d` is convex on `Ioi 0`. -/
private lemma convexOn_inv_pow_Ioi (d : ℕ) :
    ConvexOn ℝ (Ioi (0 : ℝ)) (fun x : ℝ => x⁻¹ ^ d) := by
  refine ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab => ?_⟩
  have hx_pos : 0 < x := hx
  have hy_pos : 0 < y := hy
  have hxy_pos : 0 < a * x + b * y := by
    rcases ha.eq_or_lt with rfl | ha_pos
    · have hb1 : b = 1 := by linarith
      subst hb1; simpa using hy_pos
    · exact add_pos_of_pos_of_nonneg (mul_pos ha_pos hx_pos) (mul_nonneg hb hy_pos.le)
  have hinv : (a * x + b * y)⁻¹ ≤ a * x⁻¹ + b * y⁻¹ := by
    have hnum : x * y ≤ (a * x + b * y) * (a * y + b * x) := by
      have hid : (a * x + b * y) * (a * y + b * x) - x * y =
          ((a + b) ^ 2 - 1) * (x * y) + a * b * (x - y) ^ 2 := by ring
      rw [hab] at hid
      have hsq : 0 ≤ a * b * (x - y) ^ 2 := by positivity
      linarith
    have hprod : 0 < (a * x + b * y) * (x * y) := mul_pos hxy_pos (mul_pos hx_pos hy_pos)
    have hdiv := div_le_div_of_nonneg_right hnum hprod.le
    have hlhs : x * y / ((a * x + b * y) * (x * y)) = (a * x + b * y)⁻¹ := by
      field_simp [hxy_pos.ne', hx_pos.ne', hy_pos.ne']
    have hrhs : (a * x + b * y) * (a * y + b * x) / ((a * x + b * y) * (x * y)) =
        a * x⁻¹ + b * y⁻¹ := by
      field_simp [hxy_pos.ne', hx_pos.ne', hy_pos.ne']
    linarith
  have hpow_conv := (convexOn_pow d).2 (inv_nonneg.mpr hx_pos.le) (inv_nonneg.mpr hy_pos.le) ha hb hab
  simpa [smul_eq_mul] using
    (pow_le_pow_left₀ (inv_nonneg.mpr hxy_pos.le) hinv d).trans hpow_conv

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For `z ∈ interior K` and `u ∈ sphere 0 1`, `supportFn K u - ⟪z, u⟫ > 0`. -/
private lemma supportFn_sub_inner_pos (K : ConvexBody E) {z : E} (hz : z ∈ interior (K : Set E))
    {u : E} (hu : ‖u‖ = 1) : 0 < supportFn K u - ⟪z, u⟫ := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
  have hmem : z + (r / 2) • u ∈ (K : Set E) := hball (by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (half_pos hr), hu, mul_one]
    exact half_lt_self hr)
  have h1 := inner_le_supportFn hmem u
  rw [inner_add_left, inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq, hu,
    one_pow, mul_one] at h1
  linarith

/-- **Convexity of Polar Volume:** `z ↦ volume.real ((K - z)°)` is convex on `interior K`. -/
theorem convexOn_polarVolAt [Nontrivial E] (K : ConvexBody E) :
    ConvexOn ℝ (interior (K : Set E)) (polarVolAt K) := by
  refine ⟨K.convex.interior, fun z₁ hz₁ z₂ hz₂ a b ha hb hab => ?_⟩
  have hmid : a • z₁ + b • z₂ ∈ interior (K : Set E) := K.convex.interior hz₁ hz₂ ha hb hab
  rw [polarVolAt_eq_integral K hz₁, polarVolAt_eq_integral K hz₂, polarVolAt_eq_integral K hmid]
  have hint : ∀ z ∈ interior (K : Set E),
      Integrable (fun u : sphere (0 : E) 1 => (supportFn K u.1 - ⟪z, u.1⟫)⁻¹ ^ Module.finrank ℝ E)
        (sphereProb (volume : Measure E)) := fun z hz => by
    have hcont : Continuous (fun u : sphere (0 : E) 1 =>
        (supportFn K u.1 - ⟪z, u.1⟫)⁻¹ ^ Module.finrank ℝ E) :=
      ((((continuous_supportFn K).comp continuous_subtype_val).sub
        (continuous_const.inner continuous_subtype_val)).inv₀ fun u =>
          (supportFn_sub_inner_pos K hz (mem_sphere_zero_iff_norm.mp u.2)).ne').pow _
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpt : ∀ u : sphere (0 : E) 1,
      (supportFn K u.1 - ⟪a • z₁ + b • z₂, u.1⟫)⁻¹ ^ Module.finrank ℝ E ≤
        a * ((supportFn K u.1 - ⟪z₁, u.1⟫)⁻¹ ^ Module.finrank ℝ E) +
        b * ((supportFn K u.1 - ⟪z₂, u.1⟫)⁻¹ ^ Module.finrank ℝ E) := fun u => by
    have hu1 : ‖u.1‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
    have hcomb : supportFn K u.1 - ⟪a • z₁ + b • z₂, u.1⟫ =
        a * (supportFn K u.1 - ⟪z₁, u.1⟫) + b * (supportFn K u.1 - ⟪z₂, u.1⟫) := by
      rw [inner_add_left, inner_smul_left, inner_smul_left, RCLike.conj_to_real, RCLike.conj_to_real]
      have h1 : (a + b) * supportFn K u.1 = supportFn K u.1 := by rw [hab, one_mul]
      linarith
    rw [hcomb]
    exact (convexOn_inv_pow_Ioi (Module.finrank ℝ E)).2
      (supportFn_sub_inner_pos K hz₁ hu1) (supportFn_sub_inner_pos K hz₂ hu1) ha hb hab
  have hI_le := integral_mono (hint _ hmid)
    (((hint z₁ hz₁).const_mul a).add ((hint z₂ hz₂).const_mul b)) hpt
  dsimp only [Pi.add_apply] at hI_le
  rw [integral_add ((hint z₁ hz₁).const_mul a) ((hint z₂ hz₂).const_mul b),
    integral_const_mul, integral_const_mul] at hI_le
  have hB_nn : 0 ≤ volume.real (closedBall (0 : E) 1) := measureReal_nonneg
  calc
    volume.real (closedBall (0 : E) 1) *
        ∫ u : sphere (0 : E) 1, (supportFn K u.1 - ⟪a • z₁ + b • z₂, u.1⟫)⁻¹ ^ Module.finrank ℝ E
          ∂(sphereProb (volume : Measure E))
      ≤ volume.real (closedBall (0 : E) 1) *
          (a * (∫ u : sphere (0 : E) 1, (supportFn K u.1 - ⟪z₁, u.1⟫)⁻¹ ^ Module.finrank ℝ E
              ∂(sphereProb (volume : Measure E))) +
            b * (∫ u : sphere (0 : E) 1, (supportFn K u.1 - ⟪z₂, u.1⟫)⁻¹ ^ Module.finrank ℝ E
              ∂(sphereProb (volume : Measure E)))) := mul_le_mul_of_nonneg_left hI_le hB_nn
    _ = a • (volume.real (closedBall (0 : E) 1) *
          ∫ u : sphere (0 : E) 1, (supportFn K u.1 - ⟪z₁, u.1⟫)⁻¹ ^ Module.finrank ℝ E
            ∂(sphereProb (volume : Measure E))) +
        b • (volume.real (closedBall (0 : E) 1) *
          ∫ u : sphere (0 : E) 1, (supportFn K u.1 - ⟪z₂, u.1⟫)⁻¹ ^ Module.finrank ℝ E
            ∂(sphereProb (volume : Measure E))) := by simp only [smul_eq_mul]; ring

/-- Continuity of `polarVolAt K` on `interior K` (follows immediately from convexity on an open set). -/
theorem continuousOn_polarVolAt [Nontrivial E] (K : ConvexBody E) :
    ContinuousOn (polarVolAt K) (interior (K : Set E)) :=
  (convexOn_polarVolAt K).continuousOn isOpen_interior

/-- **Cylinder Lower Bound for Polar Volume (Boundary Blow-Up):**
if `S ⊆ closedBall 0 M` (`M > 0`) and `∀ x ∈ S, ⟪x, v⟫ ≤ ε` for a unit vector `v` and `ε > 0`,
then `(2 * ε)⁻¹ * volume_H (closedBall 0 (2 * M)⁻¹) ≤ volume.real (polarBody S)` where `H = v⊥`. -/
lemma polarBody_cylinder_lower_bound {S : Set E} {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε)
    {v : E} (hv : ‖v‖ = 1) (hS_bdd : S ⊆ closedBall (0 : E) M)
    (hS_half : ∀ x ∈ S, ⟪x, v⟫ ≤ ε) :
    ENNReal.ofReal (2 * ε)⁻¹ * volume (closedBall (0 : orthoHyperplane v) (2 * M)⁻¹) ≤
      volume (polarBody S) := by
  let H := orthoHyperplane v
  let Φ := orthoSplitProd hv
  have hmp : MeasurePreserving Φ (volume : Measure E) (volume : Measure (ℝ × H)) :=
    measurePreserving_orthoSplitProd hv
  let C : Set (ℝ × H) := Icc (0 : ℝ) (2 * ε)⁻¹ ×ˢ closedBall (0 : H) (2 * M)⁻¹
  have hC_sub : Φ ⁻¹' C ⊆ polarBody S := by
    intro y hy x hxS
    have hΦy : Φ y ∈ C := hy
    have ht0 : 0 ≤ (Φ y).1 := hΦy.1.1
    have ht1 : (Φ y).1 ≤ (2 * ε)⁻¹ := hΦy.1.2
    have hw : ‖(Φ y).2‖ ≤ (2 * M)⁻¹ := mem_closedBall_zero_iff.mp hΦy.2
    have hxv : (Φ x).1 ≤ ε := by
      dsimp only [Φ]; rw [orthoSplitProd_apply]; exact hS_half x hxS
    have hxM : ‖(Φ x).2‖ ≤ M := by
      have hsq : ‖x‖ ^ 2 = (Φ x).1 ^ 2 + ‖(Φ x).2‖ ^ 2 := orthoSplitProd_norm_sq hv x
      have hxnorm : ‖x‖ ≤ M := mem_closedBall_zero_iff.mp (hS_bdd hxS)
      have hnorm_sq : ‖x‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxnorm 2
      have h1 : ‖(Φ x).2‖ ^ 2 ≤ M ^ 2 := by linarith [sq_nonneg (Φ x).1]
      exact le_of_sq_le_sq h1 hM.le
    rw [orthoSplitProd_inner hv x y]
    have hterm1 : (Φ x).1 * (Φ y).1 ≤ 1 / 2 := by
      calc
        (Φ x).1 * (Φ y).1 ≤ ε * (Φ y).1 := mul_le_mul_of_nonneg_right hxv ht0
        _ ≤ ε * (2 * ε)⁻¹ := mul_le_mul_of_nonneg_left ht1 hε.le
        _ = 1 / 2 := by field_simp [hε.ne']
    have hterm2 : ⟪(Φ x).2, (Φ y).2⟫ ≤ 1 / 2 := by
      calc
        ⟪(Φ x).2, (Φ y).2⟫ ≤ ‖(Φ x).2‖ * ‖(Φ y).2‖ := real_inner_le_norm _ _
        _ ≤ M * (2 * M)⁻¹ := mul_le_mul hxM hw (norm_nonneg _) hM.le
        _ = 1 / 2 := by field_simp [hM.ne']
    linarith
  have hC_meas : MeasurableSet C := measurableSet_Icc.prod measurableSet_closedBall
  calc
    ENNReal.ofReal (2 * ε)⁻¹ * volume (closedBall (0 : H) (2 * M)⁻¹)
      = volume (Icc (0 : ℝ) (2 * ε)⁻¹) * volume (closedBall (0 : H) (2 * M)⁻¹) := by
          rw [Real.volume_Icc, sub_zero]
    _ = volume C := by rw [Measure.volume_eq_prod, Measure.prod_prod]
    _ = volume (Φ ⁻¹' C) := (hmp.measure_preimage hC_meas.nullMeasurableSet).symm
    _ ≤ volume (polarBody S) := measure_mono hC_sub

/-- **Existence of the Santaló Point:**
for every convex body `K : ConvexBody E` with nonempty interior in a nontrivial finite-dimensional
real inner product space `E`, there exists an interior point `z ∈ interior K` minimizing
`mahlerVolumeAt volume K` (equivalently minimizing `polarVolAt K`), so
`mahlerVolumeAt volume K z = santaloMahlerVolume volume K`. -/
theorem exists_santaloPoint [Nontrivial E] (K : ConvexBody E)
    (hne : (interior (K : Set E)).Nonempty) :
    ∃ z ∈ interior (K : Set E),
      mahlerVolumeAt (volume : Measure E) (K : Set E) z =
        santaloMahlerVolume (volume : Measure E) (K : Set E) := by
  obtain ⟨z₀, hz₀⟩ := hne
  obtain ⟨R₀, hKR₀⟩ := K.isBounded.subset_closedBall (0 : E)
  set R : ℝ := max R₀ 1
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hKR : (K : Set E) ⊆ closedBall (0 : E) R :=
    hKR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  set M : ℝ := 2 * R
  have hM_pos : 0 < M := by positivity
  -- Compute a universal positive `(d - 1)`-dimensional ball volume constant `c_H`.
  -- Any hyperplane `v⊥` is linearly isometric to `(ℝ ∙ u₀)ᗮ` for a fixed unit vector `u₀`, so all
  -- hyperplanes assign the same volume to `closedBall 0 (2 * M)⁻¹`!
  obtain ⟨e₀, he₀⟩ : ∃ u : E, ‖u‖ = 1 := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    refine ⟨‖x‖⁻¹ • x, ?_⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hx)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  set cH : ℝ := volume.real (closedBall (0 : orthoHyperplane e₀) (2 * M)⁻¹)
  have hcH_pos : 0 < cH := by
    dsimp only [cH]
    rw [Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨(isOpen_ball.measure_pos volume ⟨0, mem_ball_self (by positivity)⟩).trans_le
        (measure_mono ball_subset_closedBall),
      (isCompact_closedBall _ _).measure_lt_top⟩
  have hvol_H_eq : ∀ {v : E} (hv : ‖v‖ = 1),
      volume (closedBall (0 : orthoHyperplane v) (2 * M)⁻¹) =
        ENNReal.ofReal cH := fun {v} hv => by
    obtain ⟨Q, hQv, _⟩ := exists_selfAdjoint_linearIsometryEquiv_map_eq he₀ hv
    -- `Q` restricts to a linear isometry `orthoHyperplane e₀ ≃ₗᵢ[ℝ] orthoHyperplane v`.
    let Q_H : orthoHyperplane e₀ ≃ₗᵢ[ℝ] orthoHyperplane v :=
      { toFun := fun x => ⟨Q x.1, by
          rw [mem_orthoHyperplane_iff, ← hQv, Q.inner_map_map, mem_orthoHyperplane_iff.mp x.2]⟩
        invFun := fun y => ⟨Q.symm y.1, by
          rw [mem_orthoHyperplane_iff]
          have h1 := Q.inner_map_map (Q.symm y.1) e₀
          rw [Q.apply_symm_apply, hQv, mem_orthoHyperplane_iff.mp y.2] at h1
          exact h1.symm⟩
        left_inv := fun x => Subtype.ext (Q.symm_apply_apply x.1)
        right_inv := fun y => Subtype.ext (Q.apply_symm_apply y.1)
        map_add' := fun x y => Subtype.ext (map_add Q x.1 y.1)
        map_smul' := fun c x => Subtype.ext (map_smul Q c x.1)
        norm_map' := fun x => Q.norm_map x.1 }
    have hpre : Q_H ⁻¹' closedBall (0 : orthoHyperplane v) (2 * M)⁻¹ =
        closedBall (0 : orthoHyperplane e₀) (2 * M)⁻¹ := by
      ext x; simp
    rw [← Q_H.measurePreserving.measure_preimage measurableSet_closedBall.nullMeasurableSet, hpre]
    dsimp only [cH]
    rw [Measure.real, ENNReal.ofReal_toReal (isCompact_closedBall _ _).measure_lt_top.ne]
  -- Choose `ε₀ > 0` small enough that any interior point within `ε₀` of `frontier K` has
  -- `polarVolAt K z > polarVolAt K z₀ + 1`.
  set V₀ : ℝ := polarVolAt K z₀ + 1
  have hV₀_pos : 0 < V₀ := by linarith [show 0 ≤ polarVolAt K z₀ from measureReal_nonneg]
  set ε₀ : ℝ := cH / (4 * V₀)
  have hε₀_pos : 0 < ε₀ := by positivity
  have hblow : ∀ z ∈ interior (K : Set E),
      (∃ y ∈ frontier (K : Set E), dist z y ≤ ε₀) → V₀ < polarVolAt K z := fun z hz ⟨y, hy, hzy⟩ => by
    obtain ⟨v, hv, hsup_v⟩ := exists_unit_supportFn_eq_of_mem_frontier K hy
    let Sz : Set E := (fun x : E => x - z) '' (K : Set E)
    have hSz_bdd : Sz ⊆ closedBall (0 : E) M := by
      rintro _ ⟨x, hxK, rfl⟩
      rw [mem_closedBall_zero_iff]
      have hxR : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp (hKR hxK)
      have hzR : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp (hKR (interior_subset hz))
      calc
        ‖x - z‖ ≤ ‖x‖ + ‖z‖ := norm_sub_le x z
        _ ≤ R + R := add_le_add hxR hzR
        _ = M := by dsimp only [M]; ring
    have hSz_half : ∀ w ∈ Sz, ⟪w, v⟫ ≤ ε₀ := by
      rintro _ ⟨x, hxK, rfl⟩
      rw [inner_sub_left]
      have hx_le : ⟪x, v⟫ ≤ ⟪y, v⟫ := hsup_v ▸ inner_le_supportFn hxK v
      have hyz : ⟪y - z, v⟫ ≤ ε₀ := by
        calc
          ⟪y - z, v⟫ ≤ ‖y - z‖ * ‖v‖ := real_inner_le_norm _ _
          _ = dist z y := by rw [hv, mul_one, dist_eq_norm, norm_sub_rev]
          _ ≤ ε₀ := hzy
      rw [inner_sub_left] at hyz
      linarith
    have hcyl := polarBody_cylinder_lower_bound hM_pos hε₀_pos hv hSz_bdd hSz_half
    rw [hvol_H_eq hv, ← ENNReal.ofReal_mul (by positivity)] at hcyl
    have hpol_fin : volume (polarBody Sz) ≠ ⊤ :=
      (isCompact_polarBody_of_zero_mem_interior (zero_mem_interior_translate_neg hz)).measure_lt_top.ne
    have hreal : (2 * ε₀)⁻¹ * cH ≤ polarVolAt K z := by
      rw [polarVolAt, Measure.real]
      have h1 := ENNReal.toReal_mono hpol_fin hcyl
      rwa [ENNReal.toReal_ofReal (by positivity)] at h1
    have hval : (2 * ε₀)⁻¹ * cH = 2 * V₀ := by
      dsimp only [ε₀]; field_simp [hV₀_pos.ne', hcH_pos.ne']; ring
    linarith
  -- Compact subset `S := {z ∈ K | ∀ y ∈ frontier K, ε₀ ≤ dist z y} ⊆ interior K`.
  let S : Set E := (K : Set E) ∩ ⋂ y ∈ frontier (K : Set E), {z : E | ε₀ ≤ dist z y}
  have hS_closed : IsClosed S :=
    K.isClosed.inter (isClosed_biInter fun y _ => isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hS_compact : IsCompact S := K.isCompact.of_isClosed_subset hS_closed inter_subset_left
  have hS_sub_int : S ⊆ interior (K : Set E) := fun z ⟨hzK, hz_dist⟩ => by
    by_contra hz_not_int
    have hz_fr : z ∈ frontier (K : Set E) := ⟨K.isClosed.closure_eq.symm ▸ hzK, hz_not_int⟩
    have h1 : ε₀ ≤ dist z z := by
      have := mem_iInter₂.mp hz_dist z hz_fr
      exact this
    rw [dist_self] at h1
    linarith
  have hz₀_mem_S : z₀ ∈ S := by
    refine ⟨interior_subset hz₀, mem_iInter₂.mpr fun y hy => ?_⟩
    change ε₀ ≤ dist z₀ y
    by_contra hlt; push Not at hlt
    have := hblow z₀ hz₀ ⟨y, hy, hlt.le⟩
    linarith
  -- Minimize the continuous function `polarVolAt K` on the nonempty compact set `S`.
  obtain ⟨z_min, hz_min_S, hz_min⟩ :=
    hS_compact.exists_isMinOn ⟨z₀, hz₀_mem_S⟩ ((continuousOn_polarVolAt K).mono hS_sub_int)
  have hz_min_int : z_min ∈ interior (K : Set E) := hS_sub_int hz_min_S
  have hz_min_all : ∀ w ∈ interior (K : Set E), polarVolAt K z_min ≤ polarVolAt K w := fun w hw => by
    by_cases hwS : w ∈ S
    · exact hz_min hwS
    · have hex : ∃ y ∈ frontier (K : Set E), dist w y ≤ ε₀ := by
        by_contra hno; push Not at hno
        exact hwS ⟨interior_subset hw, mem_iInter₂.mpr fun y hy => (hno y hy).le⟩
      have h1 : polarVolAt K z_min ≤ polarVolAt K z₀ := hz_min hz₀_mem_S
      have h2 : V₀ < polarVolAt K w := hblow w hw hex
      linarith
  -- Conclude `mahlerVolumeAt volume K z_min = santaloMahlerVolume volume K`.
  refine ⟨z_min, hz_min_int, le_antisymm ?_ (santaloMahlerVolume_le_mahlerVolumeAt volume hz_min_int)⟩
  refine le_iInf fun ⟨w, hw⟩ => ?_
  have hvol_eq : ∀ z : E, volume ((fun x : E => x - z) '' (K : Set E)) = volume (K : Set E) := fun z => by
    have hpre : (fun x : E => x - z) '' (K : Set E) = (fun x : E => z + x) ⁻¹' (K : Set E) := by
      ext y; simp only [mem_image, mem_preimage]
      exact ⟨fun ⟨x, hx, hxy⟩ => by rw [← hxy]; simpa [add_sub_cancel] using hx,
        fun hy => ⟨z + y, hy, by abel⟩⟩
    rw [hpre, measure_preimage_add]
  unfold mahlerVolumeAt mahlerVolume
  rw [hvol_eq z_min, hvol_eq w]
  refine mul_le_mul' le_rfl ?_
  have hfin_min : volume (polarBody ((fun x : E => x - z_min) '' (K : Set E))) ≠ ⊤ :=
    (isCompact_polarBody_of_zero_mem_interior (zero_mem_interior_translate_neg hz_min_int)).measure_lt_top.ne
  have hfin_w : volume (polarBody ((fun x : E => x - w) '' (K : Set E))) ≠ ⊤ :=
    (isCompact_polarBody_of_zero_mem_interior (zero_mem_interior_translate_neg hw)).measure_lt_top.ne
  rw [← ENNReal.ofReal_toReal hfin_min, ← ENNReal.ofReal_toReal hfin_w]
  exact ENNReal.ofReal_le_ofReal (hz_min_all w hw)

/-- For an origin-symmetric convex body `K` with `0 ∈ interior K`, the origin is a Santaló point:
`mahlerVolume volume K = santaloMahlerVolume volume K`. -/
theorem mahlerVolume_eq_santaloMahlerVolume_of_isOriginSymmetric [Nontrivial E]
    (K : ConvexBody E) (hsym : IsOriginSymmetric (K : Set E))
    (h0 : (0 : E) ∈ interior (K : Set E)) :
    mahlerVolume (volume : Measure E) (K : Set E) =
      santaloMahlerVolume (volume : Measure E) (K : Set E) := by
  apply le_antisymm _ (santaloMahlerVolume_le_mahlerVolume volume h0)
  rw [← mahlerVolumeAt_zero]
  refine le_iInf fun ⟨z, hz⟩ => ?_
  have hneg_z : -z ∈ interior (K : Set E) := by
    let e : E ≃ₜ E := Homeomorph.neg E
    have himg : e '' (K : Set E) = (K : Set E) := by
      ext x
      simp only [mem_image, e, Homeomorph.coe_neg]
      exact ⟨fun ⟨y, hy, hyx⟩ => by rw [← hyx]; exact hsym y hy,
        fun hx => ⟨-x, hsym x hx, neg_neg x⟩⟩
    have hmem : -z ∈ e '' interior (K : Set E) := ⟨z, hz, rfl⟩
    rwa [e.image_interior, himg] at hmem
  have hpol_neg : polarVolAt K (-z) = polarVolAt K z := by
    have hpre : polarBody ((fun x : E => x - (-z)) '' (K : Set E)) =
        (fun y : E => -y) ⁻¹' polarBody ((fun x : E => x - z) '' (K : Set E)) := by
      ext y
      simp only [mem_polarBody, mem_image, mem_preimage, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      constructor
      · intro h x hx
        have h1 := h (-x) (hsym x hx)
        simp only [sub_neg_eq_add, inner_neg_right, inner_sub_left, inner_add_left,
          inner_neg_left] at h1 ⊢
        linarith
      · intro h x hx
        have h1 := h (-x) (hsym x hx)
        simp only [sub_neg_eq_add, inner_neg_right, inner_sub_left, inner_add_left,
          inner_neg_left] at h1 ⊢
        linarith
    rw [polarVolAt, polarVolAt, Measure.real, Measure.real, hpre, Measure.measure_preimage_neg]
  have h0_le : polarVolAt K 0 ≤ polarVolAt K z := by
    have hconv := (convexOn_polarVolAt K).2 hz hneg_z
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
    have hmid : (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • (-z) = 0 := by simp [smul_neg]
    rw [hmid, smul_eq_mul, smul_eq_mul, hpol_neg] at hconv
    linarith
  have hvol_eq : volume ((fun x : E => x - z) '' (K : Set E)) = volume (K : Set E) := by
    have hpre : (fun x : E => x - z) '' (K : Set E) = (fun x : E => z + x) ⁻¹' (K : Set E) := by
      ext y; simp only [mem_image, mem_preimage]
      exact ⟨fun ⟨x, hx, hxy⟩ => by rw [← hxy]; simpa [add_sub_cancel] using hx,
        fun hy => ⟨z + y, hy, by abel⟩⟩
    rw [hpre, measure_preimage_add]
  unfold mahlerVolumeAt mahlerVolume
  simp only [sub_zero, image_id']
  rw [hvol_eq]
  refine mul_le_mul' le_rfl ?_
  have hfin0 : volume (polarBody (K : Set E)) ≠ ⊤ :=
    (isCompact_polarBody_of_zero_mem_interior h0).measure_lt_top.ne
  have hfinz : volume (polarBody ((fun x : E => x - z) '' (K : Set E))) ≠ ⊤ :=
    (isCompact_polarBody_of_zero_mem_interior (zero_mem_interior_translate_neg hz)).measure_lt_top.ne
  rw [← ENNReal.ofReal_toReal hfin0, ← ENNReal.ofReal_toReal hfinz]
  apply ENNReal.ofReal_le_ofReal
  simpa [polarVolAt, Measure.real] using h0_le

/-- **Upper Semicontinuity of the Santaló Mahler Volume** on the family of convex bodies with
nonempty interior. -/
theorem upperSemicontinuousOn_santaloMahlerVolume [Nontrivial E] :
    UpperSemicontinuousOn
      (fun K : ConvexBody E => santaloMahlerVolume (volume : Measure E) (K : Set E))
      {K : ConvexBody E | (interior (K : Set E)).Nonempty} := by
  intro K hK_ne y hy
  -- Find `z ∈ interior K` with `mahlerVolumeAt volume K z < y`.
  obtain ⟨⟨z, hz⟩, hlt⟩ := iInf_lt_iff.mp hy
  obtain ⟨r₀, hr₀_pos, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
  set r : ℝ := r₀ / 3
  have hr_pos : 0 < r := by positivity
  have hcb2r : closedBall z (2 * r) ⊆ (K : Set E) :=
    (closedBall_subset_ball (by dsimp only [r]; linarith)).trans hball
  -- For any `L` with `dist L K < r`, `closedBall z r ⊆ L` and `supportFn L u - ⟪z, u⟫ ≥ r`.
  have hL_ball : ∀ L : ConvexBody E, dist L K < r →
      closedBall z r ⊆ (L : Set E) ∧
        ∀ u : sphere (0 : E) 1, r ≤ supportFn L u.1 - ⟪z, u.1⟫ := fun L hLK => by
    have hsup_ge : ∀ u : sphere (0 : E) 1, r ≤ supportFn L u.1 - ⟪z, u.1⟫ := fun u => by
      have hu1 : ‖u.1‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
      have hK_ge : ⟪z, u.1⟫ + 2 * r ≤ supportFn K u.1 := by
        have h1 := supportFn_mono (K := bodyClosedBall z (by positivity : 0 ≤ 2 * r)) (L := K)
          (by rw [coe_bodyClosedBall]; exact hcb2r) u.1
        rw [supportFn_bodyClosedBall, hu1, mul_one] at h1
        exact h1
      have hdiff : |supportFn L u.1 - supportFn K u.1| ≤ dist L K := by
        have hmem : u.1 ∈ closedBall (0 : E) 1 := by rw [mem_closedBall_zero_iff, hu1]
        have h1 := BoundedContinuousFunction.dist_coe_le_dist
          (f := supportFnOnBall L) (g := supportFnOnBall K) ⟨u.1, hmem⟩
        rw [← dist_eq_dist_supportFnOnBall] at h1
        simpa [supportFnOnBall_apply, Real.dist_eq] using h1
      linarith [(abs_le.mp hdiff).1]
    refine ⟨?_, hsup_ge⟩
    rw [← coe_bodyClosedBall z hr_pos.le, ← supportFn_le_iff_subset]
    intro v
    by_cases hv : v = 0
    · subst hv; simp
    · have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
      let u : sphere (0 : E) 1 := ⟨‖v‖⁻¹ • v, by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hv_pos), inv_mul_cancel₀ hv_pos.ne']⟩
      have h1 := hsup_ge u
      have hv_eq : v = ‖v‖ • u.1 := by
        dsimp only [u]; rw [smul_smul, mul_inv_cancel₀ hv_pos.ne', one_smul]
      rw [supportFn_bodyClosedBall, hv_eq, inner_smul_right,
        supportFn_smul L hv_pos.le, norm_smul, Real.norm_eq_abs, abs_of_pos hv_pos,
        mem_sphere_zero_iff_norm.mp u.2, mul_one]
      nlinarith
  -- Show `mahlerVolumeAt volume L z → mahlerVolumeAt volume K z` as `L → K`.
  have htend_pol : Tendsto (fun L : ConvexBody E => polarVolAt L z) (𝓝 K) (𝓝 (polarVolAt K z)) := by
    have htend_int : Tendsto
        (fun L : ConvexBody E =>
          ∫ u : sphere (0 : E) 1, (supportFn L u.1 - ⟪z, u.1⟫)⁻¹ ^ Module.finrank ℝ E
            ∂(sphereProb (volume : Measure E)))
        (𝓝 K)
        (𝓝 (∫ u : sphere (0 : E) 1, (supportFn K u.1 - ⟪z, u.1⟫)⁻¹ ^ Module.finrank ℝ E
            ∂(sphereProb (volume : Measure E)))) := by
      refine tendsto_integral_filter_of_dominated_convergence
        (fun _ : sphere (0 : E) 1 => r⁻¹ ^ Module.finrank ℝ E) ?_ ?_ (integrable_const _) ?_
      · filter_upwards [Metric.ball_mem_nhds K hr_pos] with L hL
        have hsup := (hL_ball L (mem_ball.mp hL)).2
        exact (((((continuous_supportFn L).comp continuous_subtype_val).sub
          (continuous_const.inner continuous_subtype_val)).inv₀ fun u =>
            (lt_of_lt_of_le hr_pos (hsup u)).ne').pow _).aestronglyMeasurable
      · filter_upwards [Metric.ball_mem_nhds K hr_pos] with L hL
        have hsup := (hL_ball L (mem_ball.mp hL)).2
        exact ae_of_all _ fun u => by
          have hpos := lt_of_lt_of_le hr_pos (hsup u)
          rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hpos.le) _)]
          exact pow_le_pow_left₀ (inv_nonneg.mpr hpos.le)
            ((inv_le_inv₀ hpos hr_pos).mpr (hsup u)) _
      · exact ae_of_all _ fun u => by
          have hsup_tend : Tendsto (fun L : ConvexBody E => supportFn L u.1) (𝓝 K)
              (𝓝 (supportFn K u.1)) := by
            have hlip : LipschitzWith 1 (fun L : ConvexBody E => supportFn L u.1) :=
              LipschitzWith.of_dist_le_mul fun L₁ L₂ => by
                have hmem : u.1 ∈ closedBall (0 : E) 1 := by
                  rw [mem_closedBall_zero_iff, mem_sphere_zero_iff_norm.mp u.2]
                have h1 := BoundedContinuousFunction.dist_coe_le_dist
                  (f := supportFnOnBall L₁) (g := supportFnOnBall L₂) ⟨u.1, hmem⟩
                rw [← dist_eq_dist_supportFnOnBall] at h1
                simpa [supportFnOnBall_apply] using h1
            exact hlip.continuous.continuousAt.tendsto
          exact ((hsup_tend.sub tendsto_const_nhds).inv₀
            (supportFn_sub_inner_pos K hz (mem_sphere_zero_iff_norm.mp u.2)).ne').pow _
    have hev_eq : (fun L : ConvexBody E => polarVolAt L z) =ᶠ[𝓝 K]
        (fun L : ConvexBody E => volume.real (closedBall (0 : E) 1) *
          ∫ u : sphere (0 : E) 1, (supportFn L u.1 - ⟪z, u.1⟫)⁻¹ ^ Module.finrank ℝ E
            ∂(sphereProb (volume : Measure E))) := by
      filter_upwards [Metric.ball_mem_nhds K hr_pos] with L hL
      have hzL : z ∈ interior (L : Set E) :=
        mem_interior_iff_mem_nhds.mpr
          (Filter.mem_of_superset (closedBall_mem_nhds z hr_pos) (hL_ball L (mem_ball.mp hL)).1)
      exact polarVolAt_eq_integral L hzL
    rw [polarVolAt_eq_integral K hz]
    exact (htend_int.const_mul _).congr' hev_eq.symm
  have htend_mahler : Tendsto (fun L : ConvexBody E => mahlerVolumeAt (volume : Measure E) (L : Set E) z)
      (𝓝 K) (𝓝 (mahlerVolumeAt (volume : Measure E) (K : Set E) z)) := by
    have hvol_eq : ∀ L : ConvexBody E,
        volume ((fun x : E => x - z) '' (L : Set E)) = volume (L : Set E) := fun L => by
      have hpre : (fun x : E => x - z) '' (L : Set E) = (fun x : E => z + x) ⁻¹' (L : Set E) := by
        ext x; simp only [mem_image, mem_preimage]
        exact ⟨fun ⟨w, hw, hwx⟩ => by rw [← hwx]; simpa [add_sub_cancel] using hw,
          fun hx => ⟨z + x, hx, by abel⟩⟩
      rw [hpre, measure_preimage_add]
    have htend_vol : Tendsto (fun L : ConvexBody E => volume (L : Set E)) (𝓝 K) (𝓝 (volume (K : Set E))) :=
      (continuous_addHaar_convexBody (volume : Measure E)).continuousAt.tendsto
    have htend_pol_enn : Tendsto
        (fun L : ConvexBody E => volume (polarBody ((fun x : E => x - z) '' (L : Set E))))
        (𝓝 K) (𝓝 (volume (polarBody ((fun x : E => x - z) '' (K : Set E))))) := by
      have hKfin : volume (polarBody ((fun x : E => x - z) '' (K : Set E))) ≠ ⊤ :=
        (isCompact_polarBody_of_zero_mem_interior (zero_mem_interior_translate_neg hz)).measure_lt_top.ne
      have hev : (fun L : ConvexBody E => ENNReal.ofReal (polarVolAt L z)) =ᶠ[𝓝 K]
          (fun L : ConvexBody E => volume (polarBody ((fun x : E => x - z) '' (L : Set E)))) := by
        filter_upwards [Metric.ball_mem_nhds K hr_pos] with L hL
        have hzL : z ∈ interior (L : Set E) :=
          mem_interior_iff_mem_nhds.mpr
            (Filter.mem_of_superset (closedBall_mem_nhds z hr_pos) (hL_ball L (mem_ball.mp hL)).1)
        exact ENNReal.ofReal_toReal
          (isCompact_polarBody_of_zero_mem_interior (zero_mem_interior_translate_neg hzL)).measure_lt_top.ne
      rw [← ENNReal.ofReal_toReal hKfin]
      exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp htend_pol).congr' hev
    have hmul : Tendsto
        (fun L : ConvexBody E =>
          volume (L : Set E) * volume (polarBody ((fun x : E => x - z) '' (L : Set E))))
        (𝓝 K)
        (𝓝 (volume (K : Set E) * volume (polarBody ((fun x : E => x - z) '' (K : Set E))))) :=
      ENNReal.Tendsto.mul htend_vol (Or.inr
        (isCompact_polarBody_of_zero_mem_interior (zero_mem_interior_translate_neg hz)).measure_lt_top.ne)
        htend_pol_enn (Or.inr K.isCompact.measure_lt_top.ne)
    simpa only [mahlerVolumeAt, mahlerVolume, hvol_eq] using hmul
  have hev_lt : ∀ᶠ L : ConvexBody E in 𝓝 K,
      mahlerVolumeAt (volume : Measure E) (L : Set E) z < y :=
    htend_mahler.eventually (Iio_mem_nhds hlt)
  have hev_nhds : ∀ᶠ L : ConvexBody E in 𝓝 K,
      santaloMahlerVolume (volume : Measure E) (L : Set E) < y := by
    filter_upwards [Metric.ball_mem_nhds K hr_pos, hev_lt] with L hL hLlt
    have hzL : z ∈ interior (L : Set E) :=
      mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset (closedBall_mem_nhds z hr_pos) (hL_ball L (mem_ball.mp hL)).1)
    exact (santaloMahlerVolume_le_mahlerVolumeAt volume hzL).trans_lt hLlt
  exact nhdsWithin_le_nhds hev_nhds

end SantaloPoint

/-! ### 4. Meyer–Pajor (1990) Steiner Symmetrization Inequality -/

section MeyerPajor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- If `0 ∈ interior (bodySteinerSymmDir hu K)`, then `a₀ < b₀` on the vertical fiber of `K` over
`0 ∈ u⊥`, and EVERY point `t • u` with `a₀ < t < b₀` lies in `interior K`. -/
private lemma mem_interior_along_fiber_of_zero_mem_interior_steinerSymmDir
    {u : E} (hu : ‖u‖ = 1) (K : ConvexBody E)
    (h0S : (0 : E) ∈ interior (bodySteinerSymmDir hu K : Set E)) :
    let K' : Set (ℝ × orthoHyperplane u) := orthoSplitProd hu '' (K : Set E)
    steinerLower K' 0 < steinerUpper K' 0 ∧
      ∀ t : ℝ, steinerLower K' 0 < t → t < steinerUpper K' 0 → t • u ∈ interior (K : Set E) := by
  let H := orthoHyperplane u
  let Φ := orthoSplitProd hu
  let K' : Set (ℝ × H) := Φ '' (K : Set E)
  have hK'c : IsCompact K' := K.isCompact.image (continuous_orthoSplitProd hu)
  have hK'conv : Convex ℝ K' := K.convex.linear_image Φ.toLinearMap
  have h0S' : ((0 : ℝ), (0 : H)) ∈ interior (steinerSymm K') := by
    have himg : (orthoSplitHomeomorph hu) '' (bodySteinerSymmDir hu K : Set E) = steinerSymm K' := by
      have h1 : (orthoSplitHomeomorph hu : E → ℝ × H) = Φ := funext (orthoSplitHomeomorph_coe hu)
      rw [h1, coe_bodySteinerSymmDir]
      exact image_steinerSymmDir hu (K : Set E)
    rw [← himg, ← (orthoSplitHomeomorph hu).image_interior]
    exact ⟨0, h0S, by rw [orthoSplitHomeomorph_coe, map_zero]; rfl⟩
  obtain ⟨r₀, hr₀_pos, hballS⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0S')
  set r : ℝ := r₀ / 2
  have hr_pos : 0 < r := half_pos hr₀_pos
  have hboxS : ∀ s : ℝ, ∀ y : H, |s| ≤ r → ‖y‖ ≤ r → (s, y) ∈ steinerSymm K' := fun s y hs hy =>
    hballS (by
      rw [mem_ball, Prod.dist_eq, dist_zero_right, dist_zero_right, Real.norm_eq_abs]
      exact max_lt (hs.trans_lt (half_lt_self hr₀_pos)) (hy.trans_lt (half_lt_self hr₀_pos)))
  have hne0 : (steinerFiber K' 0).Nonempty := (hboxS 0 0 (by simp [hr_pos.le]) (by simp [hr_pos.le])).1
  have hlen0 : r ≤ (steinerUpper K' 0 - steinerLower K' 0) / 2 := by
    have h := (hboxS r 0 (by rw [abs_of_pos hr_pos]) (by simp [hr_pos.le])).2
    rwa [abs_of_pos hr_pos] at h
  have hab : steinerLower K' 0 < steinerUpper K' 0 := by linarith
  refine ⟨hab, fun t ht_lo ht_hi => ?_⟩
  -- Prove `(t, 0) ∈ interior K'` by building an explicit box around `(t, 0)` inside `K'`.
  obtain ⟨R₀, hK'R₀⟩ := hK'c.isBounded.subset_closedBall ((0 : ℝ), (0 : H))
  set R : ℝ := max R₀ 1
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hfib_bdd : ∀ s : ℝ, ∀ y : H, (s, y) ∈ K' → |s| ≤ R := fun s y hsy => by
    have h := hK'R₀ hsy
    rw [mem_closedBall, dist_eq_norm, Prod.mk_sub_mk, sub_zero, sub_zero, Prod.norm_def] at h
    exact ((le_max_left _ _).trans h).trans (le_max_left _ _)
  set ρ : ℝ := min (t - steinerLower K' 0) (steinerUpper K' 0 - t)
  have hρ_pos : 0 < ρ := lt_min (sub_pos.mpr ht_lo) (sub_pos.mpr ht_hi)
  set η : ℝ := ρ / 4
  set δ : ℝ := min (r / 2) (r * ρ / (8 * (R + |t| + 1)))
  have hη_pos : 0 < η := by positivity
  have hδ_pos : 0 < δ := lt_min (half_pos hr_pos) (by positivity)
  have hball_in : ball ((t, (0 : H)) : ℝ × H) (min η δ) ⊆ K' := by
    rintro ⟨s, y⟩ hsy
    rw [mem_ball, Prod.dist_eq, Real.dist_eq, dist_zero_right] at hsy
    have hs_lt : |s - t| < η := (le_max_left _ _).trans_lt (hsy.trans_le (min_le_left _ _))
    have hy_lt : ‖y‖ < δ := (le_max_right _ _).trans_lt (hsy.trans_le (min_le_right _ _))
    have hfib0 := steinerFiber_eq_Icc hK'conv hK'c hne0
    by_cases hy0 : y = 0
    · subst hy0
      have hs_Icc : s ∈ Icc (steinerLower K' 0) (steinerUpper K' 0) := by
        have habs := abs_lt.mp hs_lt
        have h1 : ρ ≤ t - steinerLower K' 0 := min_le_left _ _
        have h2 : ρ ≤ steinerUpper K' 0 - t := min_le_right _ _
        dsimp only [η] at habs
        exact ⟨by linarith, by linarith⟩
      exact show s ∈ steinerFiber K' 0 from hfib0.symm ▸ hs_Icc
    · have hy_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
      set lam : ℝ := ‖y‖ / r
      have hlam_pos : 0 < lam := div_pos hy_pos hr_pos
      have hlam_lt : lam < 1 / 2 := by
        dsimp only [lam]
        rw [div_lt_iff₀ hr_pos]
        exact hy_lt.trans_le ((min_le_left _ _).trans_eq (by ring))
      set y' : H := (r / ‖y‖) • y
      have hy'_norm : ‖y'‖ = r := by
        dsimp only [y']
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr_pos hy_pos),
          div_mul_cancel₀ r hy_pos.ne']
      have hne_y' : (steinerFiber K' y').Nonempty :=
        (hboxS 0 y' (by simp [hr_pos.le]) hy'_norm.le).1
      obtain ⟨t', ht'⟩ := hne_y'
      have ht'_R : |t'| ≤ R := hfib_bdd t' y' ht'
      set s' : ℝ := (s - lam * t') / (1 - lam)
      have h1lam_pos : 0 < 1 - lam := by linarith
      have h1lam_ge : (1 / 2 : ℝ) ≤ 1 - lam := by linarith
      have hs'_diff : |s' - t| < ρ := by
        have heq : s' - t = ((s - t) + lam * (t - t')) / (1 - lam) := by
          dsimp only [s']; field_simp [h1lam_pos.ne']; ring
        rw [heq, abs_div, abs_of_pos h1lam_pos]
        have hlam_bd : lam * |t - t'| ≤ ρ / 8 := by
          have hlam_le : lam ≤ ρ / (8 * (R + |t| + 1)) := by
            dsimp only [lam]
            rw [div_le_iff₀ hr_pos]
            calc
              ‖y‖ ≤ δ := hy_lt.le
              _ ≤ r * ρ / (8 * (R + |t| + 1)) := min_le_right _ _
              _ = ρ / (8 * (R + |t| + 1)) * r := by ring
          have htdiff : |t - t'| ≤ R + |t| + 1 := by
            have := abs_sub t t'
            linarith
          calc
            lam * |t - t'| ≤ (ρ / (8 * (R + |t| + 1))) * (R + |t| + 1) :=
              mul_le_mul hlam_le htdiff (abs_nonneg _) (by positivity)
            _ = ρ / 8 := by field_simp [show R + |t| + 1 ≠ 0 by positivity]
        have hnum : |(s - t) + lam * (t - t')| < 3 * ρ / 8 := by
          calc
            |(s - t) + lam * (t - t')| ≤ |s - t| + |lam * (t - t')| := abs_add_le _ _
            _ = |s - t| + lam * |t - t'| := by rw [abs_mul, abs_of_pos hlam_pos]
            _ < η + ρ / 8 := by linarith
            _ = 3 * ρ / 8 := by dsimp only [η]; ring
        rw [div_lt_iff₀ h1lam_pos]
        nlinarith
      have hs'_mem : (s', (0 : H)) ∈ K' := by
        have habs := abs_lt.mp hs'_diff
        have h1 : ρ ≤ t - steinerLower K' 0 := min_le_left _ _
        have h2 : ρ ≤ steinerUpper K' 0 - t := min_le_right _ _
        exact show s' ∈ steinerFiber K' 0 from
          hfib0.symm ▸ (⟨by linarith, by linarith⟩ : s' ∈ Icc (steinerLower K' 0) (steinerUpper K' 0))
      have hconv := hK'conv ht' hs'_mem hlam_pos.le h1lam_pos.le (by ring)
      have heq : lam • (t', y') + (1 - lam) • (s', (0 : H)) = (s, y) := by
        apply Prod.ext
        · change lam * t' + (1 - lam) * s' = s
          dsimp only [s']; field_simp [h1lam_pos.ne']; ring
        · change (lam • y' + (1 - lam) • (0 : H) : H) = y
          simp only [smul_zero, add_zero, y', lam, smul_smul]
          rw [show (‖y‖ / r) * (r / ‖y‖) = 1 by field_simp [hr_pos.ne', hy_pos.ne'], one_smul]
      rwa [heq] at hconv
  have hmem_int' : ((t, (0 : H)) : ℝ × H) ∈ interior K' :=
    mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨min η δ, lt_min hη_pos hδ_pos, hball_in⟩)
  have hpre_eq : (orthoSplitHomeomorph hu).symm '' interior K' = interior (K : Set E) := by
    rw [(orthoSplitHomeomorph hu).symm.image_interior]
    congr 1
    ext x
    simp only [mem_image, orthoSplitHomeomorph_symm_coe, K']
    exact ⟨fun ⟨_, ⟨z, hz, rfl⟩, hzx⟩ => by rw [← hzx, Φ.symm_apply_apply]; exact hz,
      fun hx => ⟨Φ x, ⟨x, hx, rfl⟩, Φ.symm_apply_apply x⟩⟩
  rw [← hpre_eq]
  refine ⟨(t, 0), hmem_int', ?_⟩
  rw [orthoSplitHomeomorph_symm_coe, orthoSplitProd_symm_apply]
  simp

/-- Helper: `Measure.volumeIoiPow n (Iic x) = ENNReal.ofReal (x.1 ^ (n + 1) / (n + 1))`. -/
private lemma volumeIoiPow_apply_Iic (n : ℕ) (x : Ioi (0 : ℝ)) :
    Measure.volumeIoiPow n (Iic x) = ENNReal.ofReal ((x : ℝ) ^ (n + 1) / (n + 1)) := by
  have hsingle : Measure.volumeIoiPow n ({x} : Set (Ioi (0 : ℝ))) = 0 := by
    rw [Measure.volumeIoiPow, withDensity_apply _ (measurableSet_singleton x),
      lintegral_singleton]
    have hzero : Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) volume ({x} : Set (Ioi (0 : ℝ))) = 0 := by
      have hemb : MeasurableEmbedding (Subtype.val : Ioi (0 : ℝ) → ℝ) :=
        MeasurableEmbedding.subtype_coe measurableSet_Ioi
      rw [Measure.comap_apply _ Subtype.val_injective (fun s hs => hemb.measurableSet_image.mpr hs) _
        (measurableSet_singleton x), Set.image_singleton, Real.volume_singleton]
    rw [hzero, mul_zero]
  rw [← Set.Iio_union_right, measure_union (Set.disjoint_singleton_right.mpr self_notMem_Iio)
    (measurableSet_singleton x), hsingle, add_zero, Measure.volumeIoiPow_apply_Iio]

/-- Spherical polar volume formula for the intersection of `(K - z)°` with the positive cone over a
measurable subset `s ⊆ S^{d-1}` when `z ∈ interior K`. -/
private lemma polarBody_cone_volumeReal [Nontrivial E] (K : ConvexBody E) {z : E}
    (hz : z ∈ interior (K : Set E)) {s : Set (sphere (0 : E) 1)} (hs : MeasurableSet s) :
    volume.real (polarBody ((fun x : E => x - z) '' (K : Set E)) ∩
        {y : E | ∃ (r : ℝ) (w : sphere (0 : E) 1), 0 < r ∧ w ∈ s ∧ y = r • w.1}) =
      volume.real (closedBall (0 : E) 1) *
        ∫ w in s, (supportFn K w.1 - ⟪z, w.1⟫)⁻¹ ^ Module.finrank ℝ E
          ∂(sphereProb (volume : Measure E)) := by
  let Kt : ConvexBody E := K + bodySingleton (-z)
  have hKt_coe : (Kt : Set E) = (fun x : E => x - z) '' (K : Set E) := coe_translate_neg K z
  have h0t : (0 : E) ∈ interior (Kt : Set E) := hKt_coe ▸ zero_mem_interior_translate_neg hz
  let Q : ConvexBody E := bodyPolar (Kt : Set E) h0t
  have hQ_coe : (Q : Set E) = polarBody ((fun x : E => x - z) '' (K : Set E)) := by
    rw [coe_bodyPolar, hKt_coe]
  have h0Q : (0 : E) ∈ interior (Q : Set E) := by
    rw [coe_bodyPolar]; exact zero_mem_interior_polarBody_of_isBounded Kt.isBounded
  let cone_s : Set E := {y : E | ∃ (r : ℝ) (w : sphere (0 : E) 1), 0 < r ∧ w ∈ s ∧ y = r • w.1}
  have hcone_eq : (Q : Set E) ∩ cone_s =
      Subtype.val '' ((homeomorphUnitSphereProd E) ⁻¹'
        {p : sphere (0 : E) 1 × Ioi (0 : ℝ) | p.1 ∈ s ∧ (p.2 : ℝ) ≤ (gauge (Q : Set E) p.1.1)⁻¹}) := by
    ext y
    simp only [mem_inter_iff, cone_s, mem_ofPred_eq, mem_image, mem_preimage]
    constructor
    · rintro ⟨hyQ, r, w, hr, hws, rfl⟩
      have hy0 : r • w.1 ∈ ({0}ᶜ : Set E) :=
        Set.mem_compl_singleton_iff.mpr (smul_ne_zero hr.ne' (ne_of_mem_sphere w.2 one_ne_zero))
      refine ⟨⟨r • w.1, hy0⟩, ?_, rfl⟩
      have hpol_eq : homeomorphUnitSphereProd E ⟨r • w.1, hy0⟩ = (w, ⟨r, hr⟩) := by
        have h : (homeomorphUnitSphereProd E).symm (w, ⟨r, hr⟩) = ⟨r • w.1, hy0⟩ := Subtype.ext rfl
        rw [← h, (homeomorphUnitSphereProd E).apply_symm_apply]
      rw [hpol_eq]
      refine ⟨hws, ?_⟩
      have hg_pos : 0 < gauge (Q : Set E) w.1 := gauge_pos_of_mem_sphere Q h0Q w.2
      have hle1 : gauge (Q : Set E) (r • w.1) ≤ 1 := gauge_le_one_of_mem hyQ
      rw [gauge_smul_of_nonneg hr.le, smul_eq_mul] at hle1
      rw [inv_eq_one_div, le_div_iff₀ hg_pos]
      exact hle1
    · rintro ⟨⟨x, hx0⟩, ⟨hws, hr_le⟩, rfl⟩
      set w : sphere (0 : E) 1 := (homeomorphUnitSphereProd E ⟨x, hx0⟩).1
      set r : ℝ := ((homeomorphUnitSphereProd E ⟨x, hx0⟩).2 : ℝ)
      have hr_pos : 0 < r := (homeomorphUnitSphereProd E ⟨x, hx0⟩).2.2
      have hx_eq : x = r • w.1 := by
        have h := (homeomorphUnitSphereProd E).symm_apply_apply ⟨x, hx0⟩
        exact (congrArg Subtype.val h).symm
      refine ⟨?_, r, w, hr_pos, hws, hx_eq⟩
      have hg_pos : 0 < gauge (Q : Set E) w.1 := gauge_pos_of_mem_sphere Q h0Q w.2
      have hgle1 : gauge (Q : Set E) x ≤ 1 := by
        rw [hx_eq, gauge_smul_of_nonneg hr_pos.le, smul_eq_mul]
        rw [inv_eq_one_div, le_div_iff₀ hg_pos] at hr_le
        exact hr_le
      have hnhds : (Q : Set E) ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.mp h0Q
      have htend : Tendsto (fun n : ℕ => ((n : ℝ) / ((n : ℝ) + 1)) • x) atTop (𝓝 x) := by
        have h1 : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (1 : ℝ)) := by
          have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) :=
            tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
          have heq : (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) = fun n : ℕ => 1 - ((n : ℝ) + 1)⁻¹ := by
            ext n; field_simp [show (n : ℝ) + 1 ≠ 0 by positivity]; ring
          rw [heq]; simpa using tendsto_const_nhds.sub hinv
        simpa [one_smul] using h1.smul_const x
      refine Q.isClosed.mem_of_tendsto htend (Eventually.of_forall fun n => ?_)
      have hlt1 : gauge (Q : Set E) (((n : ℝ) / ((n : ℝ) + 1)) • x) < 1 := by
        rw [gauge_smul_of_nonneg (by positivity), smul_eq_mul]
        have hfrac : (n : ℝ) / ((n : ℝ) + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
        calc
          (n : ℝ) / ((n : ℝ) + 1) * gauge (Q : Set E) x
            ≤ (n : ℝ) / ((n : ℝ) + 1) * 1 := mul_le_mul_of_nonneg_left hgle1 (by positivity)
          _ < 1 := by linarith
      exact interior_subset ((gauge_lt_one_iff_mem_interior Q.convex hnhds).mp hlt1)
  set d : ℕ := Module.finrank ℝ E
  have hd_pos : 0 < d := Module.finrank_pos
  have hmp := (volume : Measure E).measurePreserving_homeomorphUnitSphereProd
  have hemb : MeasurableEmbedding (Subtype.val : ({0}ᶜ : Set E) → E) :=
    MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : E)).compl
  let A : Set (sphere (0 : E) 1 × Ioi (0 : ℝ)) :=
    {p | p.1 ∈ s ∧ (p.2 : ℝ) ≤ (gauge (Q : Set E) p.1.1)⁻¹}
  have hgauge_eq : ∀ w : sphere (0 : E) 1, gauge (Q : Set E) w.1 = supportFn K w.1 - ⟪z, w.1⟫ :=
    fun w => by
      rw [hQ_coe, ← hKt_coe, gauge_polarBody_eq_supportFn Kt (interior_subset h0t)]
      change supportFn (K + bodySingleton (-z)) w.1 = _
      rw [supportFn_minkowski_add, supportFn_bodySingleton, inner_neg_left, sub_eq_add_neg]
  have hcont_g : Continuous (fun w : sphere (0 : E) 1 => (gauge (Q : Set E) w.1)⁻¹) := by
    simp_rw [hgauge_eq]
    exact (((continuous_supportFn K).comp continuous_subtype_val).sub
      (continuous_const.inner continuous_subtype_val)).inv₀ fun w =>
        (supportFn_sub_inner_pos K hz (mem_sphere_zero_iff_norm.mp w.2)).ne'
  have hAm : MeasurableSet A :=
    (hs.preimage measurable_fst).inter
      (isClosed_le (continuous_subtype_val.comp continuous_snd)
        (hcont_g.comp continuous_fst)).measurableSet
  have hvol_enn : volume (polarBody ((fun x : E => x - z) '' (K : Set E)) ∩ cone_s) =
      volume (closedBall (0 : E) 1) *
        ∫⁻ w in s, ENNReal.ofReal ((supportFn K w.1 - ⟪z, w.1⟫)⁻¹ ^ d)
          ∂(sphereProb (volume : Measure E)) := by
    rw [← hQ_coe, hcone_eq]
    have hpre_m : MeasurableSet ((homeomorphUnitSphereProd E) ⁻¹' A) :=
      hAm.preimage (homeomorphUnitSphereProd E).continuous.measurable
    rw [← Measure.comap_apply _ Subtype.val_injective
        (fun t ht => hemb.measurableSet_image.mpr ht) _ hpre_m,
      hmp.measure_preimage hAm.nullMeasurableSet, Measure.prod_apply hAm]
    have hfib : ∀ w : sphere (0 : E) 1,
        Measure.volumeIoiPow (Module.finrank ℝ E - 1) (Prod.mk w ⁻¹' A) =
          s.indicator (fun w => ENNReal.ofReal ((d : ℝ)⁻¹ * (gauge (Q : Set E) w.1)⁻¹ ^ d)) w :=
      fun w => by
        by_cases hws : w ∈ s
        · rw [indicator_of_mem hws]
          have hg_inv_pos : 0 < (gauge (Q : Set E) w.1)⁻¹ :=
            inv_pos.mpr (gauge_pos_of_mem_sphere Q h0Q w.2)
          have hpre_w : Prod.mk w ⁻¹' A =
              Iic (⟨(gauge (Q : Set E) w.1)⁻¹, hg_inv_pos⟩ : Ioi (0 : ℝ)) := by
            ext ⟨r, hr⟩; simp [A, hws, Subtype.mk_le_mk]
          have hd_cast : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by
            exact_mod_cast Nat.sub_add_cancel hd_pos
          rw [hpre_w, volumeIoiPow_apply_Iic (d - 1), Nat.sub_add_cancel hd_pos, hd_cast]
          congr 1; ring
        · rw [indicator_of_notMem hws]
          have hpre_w : Prod.mk w ⁻¹' A = ∅ := by ext ⟨r, hr⟩; simp [A, hws]
          rw [hpre_w, measure_empty]
    simp_rw [hfib]
    have hsph_eq : (volume : Measure E).toSphere =
        ((d : ℝ≥0∞) * volume (closedBall (0 : E) 1)) • sphereProb (volume : Measure E) := by
      rw [sphereProb, Measure.toSphere_apply_univ,
        Measure.addHaar_closedBall_eq_addHaar_ball volume (0 : E) 1, smul_smul]
      have hpos : (d : ℝ≥0∞) * volume (ball (0 : E) 1) ≠ 0 :=
        mul_ne_zero (Nat.cast_ne_zero.mpr hd_pos.ne')
          (isOpen_ball.measure_pos volume ⟨0, mem_ball_self zero_lt_one⟩).ne'
      have hfin : (d : ℝ≥0∞) * volume (ball (0 : E) 1) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
          ((measure_mono ball_subset_closedBall).trans_lt
            (isCompact_closedBall (0 : E) 1).measure_lt_top).ne
      rw [ENNReal.mul_inv_cancel hpos hfin, one_smul]
    rw [hsph_eq, lintegral_smul_measure, smul_eq_mul, lintegral_indicator hs]
    have hfactor : ∀ w : sphere (0 : E) 1,
        ENNReal.ofReal ((d : ℝ)⁻¹ * (gauge (Q : Set E) w.1)⁻¹ ^ d) =
          (d : ℝ≥0∞)⁻¹ * ENNReal.ofReal ((supportFn K w.1 - ⟪z, w.1⟫)⁻¹ ^ d) := fun w => by
      rw [hgauge_eq w, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr hd_pos), ENNReal.ofReal_natCast]
    simp_rw [hfactor]
    rw [lintegral_const_mul' (d : ℝ≥0∞)⁻¹ _
        (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr hd_pos.ne')),
      mul_comm (d : ℝ≥0∞) (volume (closedBall (0 : E) 1)),
      mul_assoc (volume (closedBall (0 : E) 1)), ← mul_assoc (d : ℝ≥0∞),
      ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr hd_pos.ne') (ENNReal.natCast_ne_top _), one_mul]
  have hint_s : IntegrableOn (fun w : sphere (0 : E) 1 => (supportFn K w.1 - ⟪z, w.1⟫)⁻¹ ^ d)
      s (sphereProb (volume : Measure E)) := by
    have hcont : Continuous (fun w : sphere (0 : E) 1 => (supportFn K w.1 - ⟪z, w.1⟫)⁻¹ ^ d) := by
      convert hcont_g.pow d using 1
      ext w; simp [hgauge_eq]
    exact (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).integrableOn
  have hnn : 0 ≤ᵐ[(sphereProb (volume : Measure E)).restrict s]
      fun w : sphere (0 : E) 1 => (supportFn K w.1 - ⟪z, w.1⟫)⁻¹ ^ d :=
    ae_of_all _ fun w =>
      pow_nonneg (inv_nonneg.mpr (supportFn_sub_inner_pos K hz (mem_sphere_zero_iff_norm.mp w.2)).le) d
  rw [Measure.real, hvol_enn, ← ofReal_integral_eq_lintegral_ofReal hint_s hnn, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (setIntegral_nonneg hs fun w _ =>
      pow_nonneg (inv_nonneg.mpr
        (supportFn_sub_inner_pos K hz (mem_sphere_zero_iff_norm.mp w.2)).le) d)]
  rfl

/-- Continuity of the spherical polar cone-volume integral along an interior line segment
`t ↦ t • u` via Dominated Convergence. -/
private lemma continuousOn_polarBody_cone_volumeReal [Nontrivial E]
    {u : E} (hu : ‖u‖ = 1) (K : ConvexBody E) {a₀ b₀ : ℝ}
    (hint_t : ∀ t ∈ Ioo a₀ b₀, t • u ∈ interior (K : Set E))
    {s : Set (sphere (0 : E) 1)} :
    ContinuousOn (fun t : ℝ =>
      volume.real (closedBall (0 : E) 1) *
        ∫ w in s, (supportFn K w.1 - t * ⟪u, w.1⟫)⁻¹ ^ Module.finrank ℝ E
          ∂(sphereProb (volume : Measure E))) (Ioo a₀ b₀) := by
  rw [continuousOn_iff_continuous_domRestrict, continuous_iff_continuousAt]
  rintro ⟨t, ht⟩
  obtain ⟨r₁, hr₁_pos, hball_t⟩ :=
    Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp (hint_t t ht))
  set δ : ℝ := min (r₁ / 4) (min ((t - a₀) / 2) ((b₀ - t) / 2))
  have hδ_pos : 0 < δ := lt_min (by positivity) (lt_min (by linarith [ht.1]) (by linarith [ht.2]))
  have hsup_lb : ∀ t' : ℝ, |t' - t| < δ → ∀ w : sphere (0 : E) 1,
      r₁ / 4 ≤ supportFn K w.1 - t' * ⟪u, w.1⟫ := fun t' htt' w => by
    have hw1 : ‖w.1‖ = 1 := mem_sphere_zero_iff_norm.mp w.2
    have hmem : t • u + (r₁ / 2) • w.1 ∈ (K : Set E) := hball_t (by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (half_pos hr₁_pos), hw1, mul_one]; exact half_lt_self hr₁_pos)
    have h1 := inner_le_supportFn hmem w.1
    rw [inner_add_left, inner_smul_left, inner_smul_left, RCLike.conj_to_real, RCLike.conj_to_real,
      real_inner_self_eq_norm_sq, hw1, one_pow, mul_one] at h1
    have hdiff : |(t' - t) * ⟪u, w.1⟫| ≤ r₁ / 4 := by
      rw [abs_mul]
      have huw : |⟪u, w.1⟫| ≤ 1 := by
        calc
          |⟪u, w.1⟫| ≤ ‖u‖ * ‖w.1‖ := abs_real_inner_le_norm u w.1
          _ = 1 := by rw [hu, hw1, mul_one]
      calc
        |t' - t| * |⟪u, w.1⟫| ≤ δ * 1 := mul_le_mul htt'.le huw (abs_nonneg _) hδ_pos.le
        _ = δ := mul_one δ
        _ ≤ r₁ / 4 := min_le_left _ _
    linarith [(abs_le.mp hdiff).2]
  have htend_int : Tendsto
      (fun x : Ioo a₀ b₀ =>
        ∫ w in s, (supportFn K w.1 - x.1 * ⟪u, w.1⟫)⁻¹ ^ Module.finrank ℝ E
          ∂(sphereProb (volume : Measure E)))
      (𝓝 ⟨t, ht⟩)
      (𝓝 (∫ w in s, (supportFn K w.1 - t * ⟪u, w.1⟫)⁻¹ ^ Module.finrank ℝ E
          ∂(sphereProb (volume : Measure E)))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun _ : sphere (0 : E) 1 => (r₁ / 4)⁻¹ ^ Module.finrank ℝ E) ?_ ?_ (integrable_const _) ?_
    · refine Eventually.of_forall fun ⟨x, hx⟩ => ?_
      have hcont_w : Continuous (fun w : sphere (0 : E) 1 =>
          (supportFn K w.1 - x * ⟪u, w.1⟫)⁻¹ ^ Module.finrank ℝ E) :=
        ((((continuous_supportFn K).comp continuous_subtype_val).sub
          (continuous_const.mul (continuous_const.inner continuous_subtype_val))).inv₀ fun w => by
            have := supportFn_sub_inner_pos K (hint_t x hx) (mem_sphere_zero_iff_norm.mp w.2)
            rw [inner_smul_left, RCLike.conj_to_real] at this
            exact this.ne').pow _
      exact hcont_w.aestronglyMeasurable
    · have hev : ∀ᶠ x : Ioo a₀ b₀ in 𝓝 ⟨t, ht⟩, |x.1 - t| < δ := by
        have h1 : Tendsto (fun x : Ioo a₀ b₀ => |x.1 - t|) (𝓝 ⟨t, ht⟩) (𝓝 0) := by
          simpa using ((continuous_subtype_val.sub (continuous_const (y := t))).abs).continuousAt
            (x := (⟨t, ht⟩ : Ioo a₀ b₀)).tendsto
        exact h1.eventually (Iio_mem_nhds hδ_pos)
      filter_upwards [hev] with x hx
      exact ae_of_all _ fun w => by
        have hlb := hsup_lb x.1 hx w
        have hpos : 0 < supportFn K w.1 - x.1 * ⟪u, w.1⟫ := lt_of_lt_of_le (by positivity) hlb
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hpos.le) _)]
        exact pow_le_pow_left₀ (inv_nonneg.mpr hpos.le)
          ((inv_le_inv₀ hpos (by positivity)).mpr hlb) _
    · exact ae_of_all _ fun w => by
        have hpos : 0 < supportFn K w.1 - t * ⟪u, w.1⟫ := by
          have := supportFn_sub_inner_pos K (hint_t t ht) (mem_sphere_zero_iff_norm.mp w.2)
          rw [inner_smul_left, RCLike.conj_to_real] at this
          exact this
        exact (((tendsto_const_nhds.sub
          (continuous_subtype_val.continuousAt.tendsto.mul tendsto_const_nhds)).inv₀ hpos.ne').pow _)
  exact htend_int.const_mul _

/-- Uniform upper bound on the positive half-volume of `(K - t • v)°` when `t ≤ c` and
`closedBall (c • v) r₁ ⊆ K`. -/
private lemma polarBody_half_le_closedBall_of_ball_subset {K : Set E} {v : E} {c t r₁ : ℝ}
    (hr₁_pos : 0 < r₁) (hcb : closedBall (c • v) r₁ ⊆ K) (htc : t ≤ c) :
    volume.real (polarBody ((fun x : E => x - t • v) '' K) ∩ {y : E | 0 < ⟪y, v⟫}) ≤
      volume.real (closedBall (0 : E) r₁⁻¹) := by
  have hsub : polarBody ((fun x : E => x - t • v) '' K) ∩ {y : E | 0 < ⟪y, v⟫} ⊆
      closedBall (0 : E) r₁⁻¹ := by
    rintro y ⟨hyP, hy_pos_v⟩
    rw [mem_closedBall_zero_iff]
    by_cases hy0 : y = 0
    · simp [hy0, inv_nonneg.mpr hr₁_pos.le]
    · have hy_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
      let w : E := (r₁ / ‖y‖) • y
      have hw_mem : c • v + w ∈ K := hcb (by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos (div_pos hr₁_pos hy_pos), div_mul_cancel₀ r₁ hy_pos.ne'])
      have h1 : ⟪(c • v + w) - t • v, y⟫ ≤ 1 := hyP _ ⟨c • v + w, hw_mem, rfl⟩
      have h2 : ⟪(c • v + w) - t • v, y⟫ = (c - t) * ⟪v, y⟫ + r₁ * ‖y‖ := by
        rw [show (c • v + w) - t • v = (c - t) • v + w by rw [sub_smul]; abel,
          inner_add_left, inner_smul_left, RCLike.conj_to_real]
        congr 1
        dsimp only [w]
        rw [inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq]
        field_simp [hy_pos.ne']
      rw [h2, real_inner_comm y v] at h1
      have hct_nonneg : 0 ≤ (c - t) * ⟪y, v⟫ := mul_nonneg (by linarith) hy_pos_v.le
      have hr1y : r₁ * ‖y‖ ≤ 1 := by linarith
      rw [inv_eq_one_div, le_div_iff₀ hr₁_pos]
      linarith
  exact measureReal_mono hsub (isCompact_closedBall _ _).measure_lt_top.ne

/-- **Half-Space Cylinder Blow-Up:** near a boundary endpoint `b • v ∈ frontier K` of an interior
segment `(a, b) • v ⊆ interior K`, the positive half-volume of `(K - t • v)°` exceeds any
prescribed threshold `B + 1`. -/
private lemma exists_polar_halfVol_ge_of_dir [Nontrivial E]
    {v : E} (hv : ‖v‖ = 1) (K : ConvexBody E) {a b c r₁ : ℝ}
    (hc : c ∈ Ioo a b) (hr₁_pos : 0 < r₁) (hcb : closedBall (c • v) r₁ ⊆ (K : Set E))
    (hint_t : ∀ t ∈ Ioo a b, t • v ∈ interior (K : Set E))
    (hb_fr : b • v ∈ frontier (K : Set E)) {B : ℝ} (hB : 0 ≤ B) :
    ∃ t ∈ Ioo c b,
      B + 1 ≤ volume.real (polarBody ((fun x : E => x - t • v) '' (K : Set E)) ∩
        {y : E | 0 < ⟪y, v⟫}) := by
  obtain ⟨R₀, hKR₀⟩ := K.isBounded.subset_closedBall (0 : E)
  set M : ℝ := max R₀ 1 + max |a| |b| + 1
  have hM_pos : 0 < M := by positivity
  have hKt_bdd : ∀ t ∈ Icc a b, (fun x : E => x - t • v) '' (K : Set E) ⊆ closedBall (0 : E) M := by
    rintro t ht _ ⟨x, hxK, rfl⟩
    rw [mem_closedBall_zero_iff]
    have hxR : ‖x‖ ≤ max R₀ 1 := (mem_closedBall_zero_iff.mp (hKR₀ hxK)).trans (le_max_left _ _)
    have ht_bd : |t| ≤ max |a| |b| := by
      rcases le_total 0 t with ht0 | ht0
      · rw [abs_of_nonneg ht0]; exact (ht.2.trans (le_abs_self b)).trans (le_max_right _ _)
      · rw [abs_of_nonpos ht0]
        exact ((by linarith [ht.1] : -t ≤ -a).trans (neg_le_abs a)).trans (le_max_left _ _)
    calc
      ‖x - t • v‖ ≤ ‖x‖ + ‖t • v‖ := norm_sub_le x (t • v)
      _ = ‖x‖ + |t| := by rw [norm_smul, Real.norm_eq_abs, hv, mul_one]
      _ ≤ M := by dsimp only [M]; linarith
  obtain ⟨n, hn, hsup_n⟩ := exists_unit_supportFn_eq_of_mem_frontier K hb_fr
  have hn_v_pos : 0 < ⟪n, v⟫ := by
    have hmem_c : c • v + (r₁ / 2) • n ∈ (K : Set E) := hcb (by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (half_pos hr₁_pos), hn, mul_one]; exact half_le_self hr₁_pos.le)
    have h1 := inner_le_supportFn hmem_c n
    rw [hsup_n, inner_add_left, inner_smul_left, inner_smul_left, inner_smul_left,
      RCLike.conj_to_real, RCLike.conj_to_real, RCLike.conj_to_real,
      real_inner_self_eq_norm_sq, hn, one_pow, mul_one, real_inner_comm n v] at h1
    have hbc : 0 < b - c := by linarith [hc.2]
    nlinarith
  set cN : ℝ := volume.real (closedBall (0 : orthoHyperplane n) (2 * M)⁻¹)
  have hcN_pos : 0 < cN := by
    dsimp only [cN]
    rw [Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨(isOpen_ball.measure_pos volume ⟨0, mem_ball_self (by positivity)⟩).trans_le
        (measure_mono ball_subset_closedBall),
      (isCompact_closedBall _ _).measure_lt_top⟩
  set δ₀ : ℝ := min ((b - c) / 2) (min (M / 4) (cN / (4 * (B + 1) * ⟪n, v⟫)))
  have hδ₀_pos : 0 < δ₀ :=
    lt_min (by linarith [hc.2]) (lt_min (by positivity) (by positivity))
  set t : ℝ := b - δ₀
  have ht_c : c < t := by
    have : δ₀ ≤ (b - c) / 2 := min_le_left _ _
    dsimp only [t]; linarith [hc.2]
  have ht_b : t < b := by dsimp only [t]; linarith
  have ht_ab : t ∈ Ioo a b := ⟨hc.1.trans ht_c, ht_b⟩
  refine ⟨t, ⟨ht_c, ht_b⟩, ?_⟩
  set ε : ℝ := δ₀ * ⟪n, v⟫
  have hε_pos : 0 < ε := mul_pos hδ₀_pos hn_v_pos
  let Φn := orthoSplitProd hn
  let C : Set (ℝ × orthoHyperplane n) :=
    Icc (1 / (4 * ε)) (1 / (2 * ε)) ×ˢ closedBall (0 : orthoHyperplane n) (2 * M)⁻¹
  have hC_sub : Φn ⁻¹' C ⊆
      polarBody ((fun x : E => x - t • v) '' (K : Set E)) ∩ {y : E | 0 < ⟪y, v⟫} := by
    intro y hy
    have hs_lo : 1 / (4 * ε) ≤ (Φn y).1 := hy.1.1
    have hs_hi : (Φn y).1 ≤ 1 / (2 * ε) := hy.1.2
    have hw : ‖(Φn y).2‖ ≤ (2 * M)⁻¹ := mem_closedBall_zero_iff.mp hy.2
    constructor
    · rintro _ ⟨x, hxK, rfl⟩
      have hx_n : (Φn (x - t • v)).1 ≤ ε := by
        simp only [Φn, orthoSplitProd_apply]
        rw [inner_sub_left, inner_smul_left, RCLike.conj_to_real]
        have h1 := inner_le_supportFn hxK n
        rw [hsup_n, inner_smul_left, RCLike.conj_to_real] at h1
        rw [real_inner_comm n v] at h1 ⊢
        dsimp only [ε, t]; linarith
      have hx_M : ‖(Φn (x - t • v)).2‖ ≤ M := by
        have hsq : ‖x - t • v‖ ^ 2 = (Φn (x - t • v)).1 ^ 2 + ‖(Φn (x - t • v)).2‖ ^ 2 :=
          orthoSplitProd_norm_sq hn (x - t • v)
        have hnorm : ‖x - t • v‖ ≤ M :=
          mem_closedBall_zero_iff.mp (hKt_bdd t ⟨ht_ab.1.le, ht_ab.2.le⟩ ⟨x, hxK, rfl⟩)
        have hnorm_sq : ‖x - t • v‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
        have h1 : ‖(Φn (x - t • v)).2‖ ^ 2 ≤ M ^ 2 := by linarith [sq_nonneg (Φn (x - t • v)).1]
        exact le_of_sq_le_sq h1 hM_pos.le
      rw [orthoSplitProd_inner hn (x - t • v) y]
      have h1 : (Φn (x - t • v)).1 * (Φn y).1 ≤ 1 / 2 := by
        have hs_nn : 0 ≤ (Φn y).1 := (by positivity : (0 : ℝ) ≤ 1 / (4 * ε)).trans hs_lo
        calc
          (Φn (x - t • v)).1 * (Φn y).1 ≤ ε * (Φn y).1 := mul_le_mul_of_nonneg_right hx_n hs_nn
          _ ≤ ε * (1 / (2 * ε)) := mul_le_mul_of_nonneg_left hs_hi hε_pos.le
          _ = 1 / 2 := by field_simp [hε_pos.ne']
      have h2 : ⟪(Φn (x - t • v)).2, (Φn y).2⟫ ≤ 1 / 2 := by
        calc
          ⟪(Φn (x - t • v)).2, (Φn y).2⟫ ≤ ‖(Φn (x - t • v)).2‖ * ‖(Φn y).2‖ :=
            real_inner_le_norm _ _
          _ ≤ M * (2 * M)⁻¹ := mul_le_mul hx_M hw (norm_nonneg _) hM_pos.le
          _ = 1 / 2 := by field_simp [hM_pos.ne']
      linarith
    · have hy_eq : y = (Φn y).1 • n + ((Φn y).2 : E) := by
        have := Φn.symm_apply_apply y
        dsimp only [Φn] at this
        rw [orthoSplitProd_symm_apply] at this
        exact this.symm
      change 0 < ⟪y, v⟫
      rw [hy_eq, inner_add_left, inner_smul_left, RCLike.conj_to_real]
      have hwu : |⟪((Φn y).2 : E), v⟫| ≤ (2 * M)⁻¹ := by
        calc
          |⟪((Φn y).2 : E), v⟫| ≤ ‖((Φn y).2 : E)‖ * ‖v‖ := abs_real_inner_le_norm _ _
          _ ≤ (2 * M)⁻¹ * 1 := by rw [hv]; exact mul_le_mul_of_nonneg_right hw zero_le_one
          _ = (2 * M)⁻¹ := mul_one _
      have hmain : (2 * M)⁻¹ < (Φn y).1 * ⟪n, v⟫ := by
        have h1 : (2 * M)⁻¹ < (1 / (4 * ε)) * ⟪n, v⟫ := by
          have heq : (1 / (4 * ε)) * ⟪n, v⟫ = (4 * δ₀)⁻¹ := by
            dsimp only [ε]; field_simp [hδ₀_pos.ne', hn_v_pos.ne']
          rw [heq]
          have h4δ : 4 * δ₀ < 2 * M := by
            have : δ₀ ≤ M / 4 := (min_le_right _ _).trans (min_le_left _ _)
            linarith
          exact (inv_lt_inv₀ (by positivity) (by positivity)).mpr h4δ
        exact h1.trans_le (mul_le_mul_of_nonneg_right hs_lo hn_v_pos.le)
      linarith [(abs_le.mp hwu).1]
  have hC_meas : MeasurableSet C := measurableSet_Icc.prod measurableSet_closedBall
  have hmpn := measurePreserving_orthoSplitProd hn
  have hvol_C : volume (Φn ⁻¹' C) = ENNReal.ofReal (cN / (4 * ε)) := by
    rw [hmpn.measure_preimage hC_meas.nullMeasurableSet, Measure.volume_eq_prod, Measure.prod_prod,
      Real.volume_Icc,
      show 1 / (2 * ε) - 1 / (4 * ε) = 1 / (4 * ε) by field_simp [hε_pos.ne']; ring,
      ← ENNReal.ofReal_toReal (isCompact_closedBall _ _).measure_lt_top.ne,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    change 1 / (4 * ε) * cN = cN / (4 * ε)
    ring
  have hfin_pos :
      volume (polarBody ((fun x : E => x - t • v) '' (K : Set E)) ∩ {y : E | 0 < ⟪y, v⟫}) ≠ ⊤ :=
    ((measure_mono inter_subset_left).trans_lt
      (isCompact_polarBody_of_zero_mem_interior
        (zero_mem_interior_translate_neg (hint_t t ht_ab))).measure_lt_top).ne
  have hpos_ge : cN / (4 * ε) ≤
      volume.real (polarBody ((fun x : E => x - t • v) '' (K : Set E)) ∩ {y : E | 0 < ⟪y, v⟫}) := by
    rw [Measure.real]
    have h1 := ENNReal.toReal_mono hfin_pos (hvol_C ▸ measure_mono hC_sub)
    rwa [ENNReal.toReal_ofReal (by positivity)] at h1
  have hge_B : B + 1 ≤ cN / (4 * ε) := by
    have hδ_le : δ₀ ≤ cN / (4 * (B + 1) * ⟪n, v⟫) :=
      (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)]
    have hmul := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (B + 1) * ⟪n, v⟫)).mp hδ_le
    dsimp only [ε]; linarith
  exact hge_B.trans hpos_ge

/-- **Balanced Half-Volume Shift (Meyer–Pajor IVT Step):**
under the hypotheses of `mem_interior_along_fiber_of_zero_mem_interior_steinerSymmDir`, there
exists `t₀ ∈ Ioo a₀ b₀` such that the positive and negative half-volumes of `(K - t₀ • u)°` across
`u⊥` are equal. -/
private lemma exists_balanced_polar_slice_shift
    {u : E} (hu : ‖u‖ = 1) (hd2 : 2 ≤ Module.finrank ℝ E) (K : ConvexBody E)
    (h0S : (0 : E) ∈ interior (bodySteinerSymmDir hu K : Set E)) :
    let K' : Set (ℝ × orthoHyperplane u) := orthoSplitProd hu '' (K : Set E)
    ∃ t₀ : ℝ, steinerLower K' 0 < t₀ ∧ t₀ < steinerUpper K' 0 ∧
      volume.real (polarBody ((fun x : E => x - t₀ • u) '' (K : Set E)) ∩ {y : E | 0 < ⟪y, u⟫}) =
        volume.real (polarBody ((fun x : E => x - t₀ • u) '' (K : Set E)) ∩ {y : E | ⟪y, u⟫ < 0}) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
  let H := orthoHyperplane u
  let Φ := orthoSplitProd hu
  let K' : Set (ℝ × H) := Φ '' (K : Set E)
  have hK'c : IsCompact K' := K.isCompact.image (continuous_orthoSplitProd hu)
  have hfib := mem_interior_along_fiber_of_zero_mem_interior_steinerSymmDir hu K h0S
  set a₀ : ℝ := steinerLower K' 0
  set b₀ : ℝ := steinerUpper K' 0
  have hab : a₀ < b₀ := hfib.1
  have hint_t : ∀ t ∈ Ioo a₀ b₀, t • u ∈ interior (K : Set E) := fun t ht => hfib.2 t ht.1 ht.2
  let P_of : ℝ → Set E := fun t => polarBody ((fun x : E => x - t • u) '' (K : Set E))
  let volPos : ℝ → ℝ := fun t => volume.real (P_of t ∩ {y : E | 0 < ⟪y, u⟫})
  let volNeg : ℝ → ℝ := fun t => volume.real (P_of t ∩ {y : E | ⟪y, u⟫ < 0})
  let D : ℝ → ℝ := fun t => volPos t - volNeg t
  -- Step 1: Continuity of `D = volPos - volNeg` on `Ioo a₀ b₀`.
  let Spos : Set (sphere (0 : E) 1) := {w | 0 < ⟪w.1, u⟫}
  let Sneg : Set (sphere (0 : E) 1) := {w | ⟪w.1, u⟫ < 0}
  have hSpos_m : MeasurableSet Spos :=
    (isOpen_lt continuous_const (continuous_subtype_val.inner continuous_const)).measurableSet
  have hSneg_m : MeasurableSet Sneg :=
    (isOpen_lt (continuous_subtype_val.inner continuous_const) continuous_const).measurableSet
  have hcone_half : ∀ (v : E), {y : E | 0 < ⟪y, v⟫} =
      {y : E | ∃ (r : ℝ) (w : sphere (0 : E) 1), 0 < r ∧ w ∈ {w : sphere (0 : E) 1 | 0 < ⟪w.1, v⟫} ∧
        y = r • w.1} := fun v => by
    ext y
    simp only [mem_ofPred_eq]
    constructor
    · intro hy
      have hy0 : y ≠ 0 := by intro h; simp [h] at hy
      have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy0
      refine ⟨‖y‖, ⟨‖y‖⁻¹ • y, by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr),
          inv_mul_cancel₀ hr.ne']⟩, hr, ?_, by rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]⟩
      rw [inner_smul_left, RCLike.conj_to_real]
      exact mul_pos (inv_pos.mpr hr) hy
    · rintro ⟨r, w, hr, hw, rfl⟩
      rw [inner_smul_left, RCLike.conj_to_real]
      exact mul_pos hr hw
  have hD_cont : ContinuousOn D (Ioo a₀ b₀) := by
    have hpos_eq : Set.EqOn volPos
        (fun t : ℝ => volume.real (closedBall (0 : E) 1) *
          ∫ w in Spos, (supportFn K w.1 - t * ⟪u, w.1⟫)⁻¹ ^ Module.finrank ℝ E
            ∂(sphereProb (volume : Measure E))) (Ioo a₀ b₀) := fun t ht => by
      dsimp only [volPos]
      rw [hcone_half u, polarBody_cone_volumeReal K (hint_t t ht) hSpos_m]
      simp_rw [inner_smul_left, RCLike.conj_to_real]
    have hneg_eq : Set.EqOn volNeg
        (fun t : ℝ => volume.real (closedBall (0 : E) 1) *
          ∫ w in Sneg, (supportFn K w.1 - t * ⟪u, w.1⟫)⁻¹ ^ Module.finrank ℝ E
            ∂(sphereProb (volume : Measure E))) (Ioo a₀ b₀) := fun t ht => by
      have hneg_set : {y : E | ⟪y, u⟫ < 0} = {y : E | 0 < ⟪y, -u⟫} := by
        ext y; simp [inner_neg_right]
      have hSneg_eq : {w : sphere (0 : E) 1 | 0 < ⟪w.1, -u⟫} = Sneg := by
        ext w; simp [Sneg, inner_neg_right]
      dsimp only [volNeg]
      rw [hneg_set, hcone_half (-u), hSneg_eq, polarBody_cone_volumeReal K (hint_t t ht) hSneg_m]
      simp_rw [inner_smul_left, RCLike.conj_to_real]
    exact ((continuousOn_polarBody_cone_volumeReal hu K hint_t).congr hpos_eq).sub
      ((continuousOn_polarBody_cone_volumeReal hu K hint_t).congr hneg_eq)
  -- Step 2: Uniform bound on opposite half-volumes from an interior ball around `c • u`.
  set c : ℝ := (a₀ + b₀) / 2
  have hc_mem : c ∈ Ioo a₀ b₀ := ⟨by dsimp only [c]; linarith, by dsimp only [c]; linarith⟩
  obtain ⟨r_c, hr_c_pos, hball_c⟩ :=
    Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp (hint_t c hc_mem))
  set r₁ : ℝ := r_c / 2
  have hr₁_pos : 0 < r₁ := half_pos hr_c_pos
  have hcb_c : closedBall (c • u) r₁ ⊆ (K : Set E) :=
    (closedBall_subset_ball (half_lt_self hr_c_pos)).trans hball_c
  set B_opp : ℝ := volume.real (closedBall (0 : E) r₁⁻¹)
  have hne0 : (steinerFiber K' 0).Nonempty := by
    have h0S' : ((0 : ℝ), (0 : H)) ∈ steinerSymm K' :=
      image_steinerSymmDir hu (K : Set E) ▸ ⟨0, interior_subset h0S, map_zero Φ⟩
    exact h0S'.1
  -- Step 3: Endpoint frontier checks at `b₀ • u` and `a₀ • u` + cylinder blow-up in `±u`.
  have hb_fr : b₀ • u ∈ frontier (K : Set E) := by
    have hb_mem : b₀ • u ∈ (K : Set E) := by
      have hbK' : (b₀, (0 : H)) ∈ K' := (isCompact_steinerFiber hK'c 0).sSup_mem hne0
      rcases hbK' with ⟨x, hxK, hxp⟩
      have hx_eq : x = b₀ • u := by
        have := congrArg Φ.symm hxp
        rw [Φ.symm_apply_apply] at this; dsimp only [Φ] at this
        rw [orthoSplitProd_symm_apply] at this; simpa using this
      rwa [← hx_eq]
    refine ⟨K.isClosed.closure_eq.symm ▸ hb_mem, fun hb_int => ?_⟩
    obtain ⟨δ, hδ_pos, hball_b⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hb_int)
    have hmem' : (b₀ + δ / 2) • u ∈ (K : Set E) := hball_b (by
      rw [mem_ball, dist_eq_norm, show (b₀ + δ / 2) • u - b₀ • u = (δ / 2) • u by rw [add_smul]; abel,
        norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hδ_pos), hu, mul_one]
      exact half_lt_self hδ_pos)
    have hfib_mem : b₀ + δ / 2 ∈ steinerFiber K' 0 := by
      refine ⟨(b₀ + δ / 2) • u, hmem', ?_⟩
      ext
      · simp [Φ, orthoSplitProd_apply, hu]
      · simp [Φ, orthoSplitProd_apply, hu]
    have hle : b₀ + δ / 2 ≤ b₀ := le_csSup (isCompact_steinerFiber hK'c 0).bddAbove hfib_mem
    linarith
  have ha_fr : a₀ • u ∈ frontier (K : Set E) := by
    have ha_mem : a₀ • u ∈ (K : Set E) := by
      have haK' : (a₀, (0 : H)) ∈ K' := (isCompact_steinerFiber hK'c 0).sInf_mem hne0
      rcases haK' with ⟨x, hxK, hxp⟩
      have hx_eq : x = a₀ • u := by
        have := congrArg Φ.symm hxp
        rw [Φ.symm_apply_apply] at this; dsimp only [Φ] at this
        rw [orthoSplitProd_symm_apply] at this; simpa using this
      rwa [← hx_eq]
    refine ⟨K.isClosed.closure_eq.symm ▸ ha_mem, fun ha_int => ?_⟩
    obtain ⟨δ, hδ_pos, hball_a⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp ha_int)
    have hmem' : (a₀ - δ / 2) • u ∈ (K : Set E) := hball_a (by
      rw [mem_ball, dist_eq_norm,
        show (a₀ - δ / 2) • u - a₀ • u = (-(δ / 2)) • u by rw [sub_smul, neg_smul]; abel,
        norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (half_pos hδ_pos), hu, mul_one]
      exact half_lt_self hδ_pos)
    have hfib_mem : a₀ - δ / 2 ∈ steinerFiber K' 0 := by
      refine ⟨(a₀ - δ / 2) • u, hmem', ?_⟩
      ext
      · simp [Φ, orthoSplitProd_apply, hu]
      · simp [Φ, orthoSplitProd_apply, hu]
    have hge : a₀ ≤ a₀ - δ / 2 := csInf_le (isCompact_steinerFiber hK'c 0).bddBelow hfib_mem
    linarith
  obtain ⟨t₂, ht₂_cb, ht₂_ge⟩ :=
    exists_polar_halfVol_ge_of_dir hu K hc_mem hr₁_pos hcb_c hint_t hb_fr (B := B_opp)
      measureReal_nonneg
  have ht₂_mem : t₂ ∈ Ioo a₀ b₀ := ⟨hc_mem.1.trans ht₂_cb.1, ht₂_cb.2⟩
  have hDt₂ : 0 ≤ D t₂ := by
    have hneg_le : volNeg t₂ ≤ B_opp := by
      have hcb_neg : closedBall ((-c) • (-u)) r₁ ⊆ (K : Set E) := by simpa [neg_smul, smul_neg] using hcb_c
      have hle := polarBody_half_le_closedBall_of_ball_subset hr₁_pos hcb_neg (t := -t₂) (by linarith [ht₂_cb.1])
      simpa [volNeg, P_of, neg_smul, smul_neg, inner_neg_right] using hle
    dsimp only [D, volPos, P_of] at ht₂_ge ⊢
    linarith
  have hnu : ‖-u‖ = 1 := by rw [norm_neg, hu]
  have hint_neg : ∀ s ∈ Ioo (-b₀) (-a₀), s • (-u) ∈ interior (K : Set E) := fun s hs => by
    rw [smul_neg, ← neg_smul]
    exact hint_t (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
  obtain ⟨s₁, hs₁_ca, hs₁_ge⟩ :=
    exists_polar_halfVol_ge_of_dir hnu K (a := -b₀) (b := -a₀) (c := -c)
      ⟨by linarith [hc_mem.2], by linarith [hc_mem.1]⟩ hr₁_pos
      (by simpa [neg_smul, smul_neg] using hcb_c) hint_neg
      (by simpa [neg_smul, smul_neg] using ha_fr) (B := B_opp) measureReal_nonneg
  set t₁ : ℝ := -s₁
  have ht₁_mem : t₁ ∈ Ioo a₀ b₀ := ⟨by dsimp only [t₁]; linarith [hs₁_ca.2],
    by dsimp only [t₁]; linarith [hs₁_ca.1, hc_mem.2]⟩
  have hDt₁ : D t₁ ≤ 0 := by
    have hpos_le : volPos t₁ ≤ B_opp :=
      polarBody_half_le_closedBall_of_ball_subset hr₁_pos hcb_c (by dsimp only [t₁]; linarith [hs₁_ca.1])
    have hneg_ge : B_opp + 1 ≤ volNeg t₁ := by
      simpa [volNeg, P_of, t₁, neg_smul, smul_neg, inner_neg_right] using hs₁_ge
    dsimp only [D]; linarith
  -- Step 4: Apply the Intermediate Value Theorem to `D` on `[min t₁ t₂, max t₁ t₂] ⊆ Ioo a₀ b₀`.
  rcases le_total t₁ t₂ with h12 | h21
  · have hsub : Icc t₁ t₂ ⊆ Ioo a₀ b₀ := fun t ht => ⟨ht₁_mem.1.trans_le ht.1, ht.2.trans_lt ht₂_mem.2⟩
    obtain ⟨t₀, ht₀_Icc, hDt₀⟩ := intermediate_value_Icc h12 (hD_cont.mono hsub) ⟨hDt₁, hDt₂⟩
    exact ⟨t₀, (hsub ht₀_Icc).1, (hsub ht₀_Icc).2, sub_eq_zero.mp hDt₀⟩
  · have hsub : Icc t₂ t₁ ⊆ Ioo a₀ b₀ := fun t ht => ⟨ht₂_mem.1.trans_le ht.1, ht.2.trans_lt ht₁_mem.2⟩
    obtain ⟨t₀, ht₀_Icc, hDt₀⟩ := intermediate_value_Icc' h21 (hD_cont.mono hsub) ⟨hDt₁, hDt₂⟩
    exact ⟨t₀, (hsub ht₀_Icc).1, (hsub ht₀_Icc).2, sub_eq_zero.mp hDt₀⟩

/-- **1D Quantile Function Lemma:**
given a bounded measurable density `f : ℝ → ℝ` that is continuous and strictly positive on `Ioo 0 M`
with integral `V = ∫ t in Ioo 0 M, f t`, there exists a differentiable inverse `s : ℝ → ℝ` on
`Ioo 0 V` mapping into `Ioo 0 M` with `∫ t in 0..s r, f t = r` and `s'(r) = (f (s r))⁻¹`. -/
private lemma exists_cdf_quantile_inverse {M C : ℝ} (hM : 0 < M) (hC : 0 ≤ C)
    {f : ℝ → ℝ} (hf_meas : Measurable f)
    (hf_bdd : ∀ t : ℝ, 0 ≤ f t ∧ f t ≤ C)
    (hf_cont : ContinuousOn f (Ioo 0 M))
    (hf_pos : ∀ t ∈ Ioo 0 M, 0 < f t) :
    let V : ℝ := ∫ t in Ioo 0 M, f t
    0 < V ∧ ∃ s : ℝ → ℝ,
      (∀ r ∈ Ioo 0 V, s r ∈ Ioo 0 M) ∧
      (∀ r ∈ Ioo 0 V, (∫ t in (0 : ℝ)..(s r), f t) = r) ∧
      (∀ r ∈ Ioo 0 V, HasDerivAt s (f (s r))⁻¹ r) := by
  let F : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, f t
  have hf_int : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b => by
    rw [intervalIntegrable_iff]
    refine (integrableOn_const (C := C) (by simp : volume (uIoc a b) ≠ ⊤)).mono'
      hf_meas.aestronglyMeasurable (ae_of_all _ fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf_bdd t).1]
    exact (hf_bdd t).2
  have hF_deriv : ∀ x ∈ Ioo 0 M, HasDerivAt F (f x) x := fun x hx =>
    intervalIntegral.integral_hasDerivAt_right (hf_int 0 x)
      hf_meas.stronglyMeasurable.stronglyMeasurableAtFilter
      (hf_cont.continuousAt (isOpen_Ioo.mem_nhds hx))
  have hF_lip : ∀ x y : ℝ, |F y - F x| ≤ C * |y - x| := fun x y => by
    have hdiff : F y - F x = ∫ t in x..y, f t := by
      dsimp only [F]
      have h := intervalIntegral.integral_add_adjacent_intervals (hf_int 0 x) (hf_int x y)
      linarith
    rw [hdiff]
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := y) (C := C)
      fun t _ => by rw [Real.norm_eq_abs, abs_of_nonneg (hf_bdd t).1]; exact (hf_bdd t).2
    simpa [Real.norm_eq_abs] using hnorm
  have hF_cont : Continuous F :=
    (LipschitzWith.of_dist_le_mul (K := (⟨C, hC⟩ : ℝ≥0)) fun x y => by
      change |F x - F y| ≤ C * |x - y|
      exact hF_lip y x).continuous
  have hF_mono : StrictMonoOn F (Icc 0 M) :=
    strictMonoOn_of_deriv_pos (convex_Icc 0 M) hF_cont.continuousOn fun x hx => by
      rw [interior_Icc] at hx
      rw [(hF_deriv x hx).deriv]
      exact hf_pos x hx
  have hF0 : F 0 = 0 := by simp [F]
  have hFM : F M = ∫ t in Ioo 0 M, f t := by
    dsimp only [F]
    rw [intervalIntegral.integral_of_le hM.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  set V : ℝ := ∫ t in Ioo 0 M, f t
  have hV_pos : 0 < V := by
    rw [← hFM, ← hF0]
    exact hF_mono ⟨le_rfl, hM.le⟩ ⟨hM.le, le_rfl⟩ hM
  -- Construct `s` via IVT on `Ioo 0 V`.
  have hex : ∀ r ∈ Ioo 0 V, ∃ x ∈ Ioo 0 M, F x = r := fun r hr => by
    have hr_Icc : r ∈ Icc (F 0) (F M) := by rw [hF0, hFM]; exact ⟨hr.1.le, hr.2.le⟩
    obtain ⟨x, hx_Icc, hFx⟩ := intermediate_value_Icc hM.le hF_cont.continuousOn hr_Icc
    refine ⟨x, ⟨?_, ?_⟩, hFx⟩
    · rcases eq_or_lt_of_le hx_Icc.1 with rfl | hlt
      · linarith [hF0, hFx, hr.1]
      · exact hlt
    · rcases eq_or_lt_of_le hx_Icc.2 with rfl | hlt
      · linarith [hFM, hFx, hr.2]
      · exact hlt
  classical
  let s : ℝ → ℝ := fun r => if hr : r ∈ Ioo 0 V then (hex r hr).choose else 0
  have hs_mem : ∀ r ∈ Ioo 0 V, s r ∈ Ioo 0 M := fun r hr => by
    simp only [s, hr, ↓reduceDIte]; exact (hex r hr).choose_spec.1
  have hs_inv : ∀ r ∈ Ioo 0 V, F (s r) = r := fun r hr => by
    simp only [s, hr, ↓reduceDIte]; exact (hex r hr).choose_spec.2
  -- Prove continuity of `s` at every `r ∈ Ioo 0 V` from strict monotonicity of `F`.
  have hs_cont : ∀ r ∈ Ioo 0 V, ContinuousAt s r := fun r hr => by
    rw [Metric.continuousAt_iff]
    intro ε hε
    have hx := hs_mem r hr
    set δ : ℝ := min (ε / 2) (min (s r / 2) ((M - s r) / 2))
    have hδ_pos : 0 < δ := lt_min (half_pos hε) (lt_min (half_pos hx.1) (by linarith [hx.2]))
    set a : ℝ := s r - δ
    set b : ℝ := s r + δ
    have ha_Icc : a ∈ Icc 0 M := ⟨by have : δ ≤ s r / 2 := (min_le_right _ _).trans (min_le_left _ _); dsimp only [a]; linarith [hx.1],
      by dsimp only [a]; linarith [hx.2]⟩
    have hb_Icc : b ∈ Icc 0 M := ⟨by dsimp only [b]; linarith [hx.1],
      by have : δ ≤ (M - s r) / 2 := (min_le_right _ _).trans (min_le_right _ _); dsimp only [b]; linarith [hx.2]⟩
    have ha_lt_r : F a < r := by
      rw [← hs_inv r hr]
      exact hF_mono ha_Icc ⟨hx.1.le, hx.2.le⟩ (by dsimp only [a]; linarith)
    have hr_lt_b : r < F b := by
      rw [← hs_inv r hr]
      exact hF_mono ⟨hx.1.le, hx.2.le⟩ hb_Icc (by dsimp only [b]; linarith)
    set η : ℝ := min (min (r - F a) (F b - r)) (min r (V - r))
    have hη_pos : 0 < η :=
      lt_min (lt_min (sub_pos.mpr ha_lt_r) (sub_pos.mpr hr_lt_b))
        (lt_min hr.1 (sub_pos.mpr hr.2))
    refine ⟨η, hη_pos, fun y hy => ?_⟩
    rw [Real.dist_eq] at hy ⊢
    have hy_Ioo : y ∈ Ioo 0 V := by
      have h1 : |y - r| < r := hy.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      have h2 : |y - r| < V - r := hy.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      exact ⟨by linarith [(abs_lt.mp h1).1], by linarith [(abs_lt.mp h2).2]⟩
    have hFy_gt : F a < F (s y) := by
      rw [hs_inv y hy_Ioo]
      have h1 : |y - r| < r - F a := hy.trans_le ((min_le_left _ _).trans (min_le_left _ _))
      linarith [(abs_lt.mp h1).1]
    have hFy_lt : F (s y) < F b := by
      rw [hs_inv y hy_Ioo]
      have h1 : |y - r| < F b - r := hy.trans_le ((min_le_left _ _).trans (min_le_right _ _))
      linarith [(abs_lt.mp h1).2]
    have hsy_Icc : s y ∈ Icc 0 M := ⟨(hs_mem y hy_Ioo).1.le, (hs_mem y hy_Ioo).2.le⟩
    have hsy_gt : a < s y := by
      by_contra hle; push Not at hle
      exact not_lt.mpr (hF_mono.monotoneOn hsy_Icc ha_Icc hle) hFy_gt
    have hsy_lt : s y < b := by
      by_contra hle; push Not at hle
      exact not_lt.mpr (hF_mono.monotoneOn hb_Icc hsy_Icc hle) hFy_lt
    have hδ_lt : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
    rw [abs_lt]
    dsimp only [a, b] at hsy_gt hsy_lt
    exact ⟨by linarith, by linarith⟩
  have hs_deriv : ∀ r ∈ Ioo 0 V, HasDerivAt s (f (s r))⁻¹ r := fun r hr =>
    (hF_deriv (s r) (hs_mem r hr)).of_local_left_inverse (hs_cont r hr)
      (hf_pos (s r) (hs_mem r hr)).ne'
      (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hr) hs_inv)
  exact ⟨hV_pos, s, hs_mem, hs_inv, hs_deriv⟩

/-- Helper: `1 ≤ 2 * λ^λ * (1 - λ)^(1 - λ)` for all `λ ∈ (0, 1)`. -/
private lemma one_le_two_mul_rpow_self {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    1 ≤ 2 * (lam ^ lam * (1 - lam) ^ (1 - lam)) := by
  have h1lam : 0 < 1 - lam := sub_pos.mpr h1
  have hlog1 := Real.log_le_sub_one_of_pos (show 0 < 1 / (2 * lam) by positivity)
  have hlog2 := Real.log_le_sub_one_of_pos (show 0 < 1 / (2 * (1 - lam)) by positivity)
  rw [one_div, Real.log_inv, Real.log_mul two_ne_zero h0.ne'] at hlog1
  rw [one_div, Real.log_inv, Real.log_mul two_ne_zero h1lam.ne'] at hlog2
  have hm1 : lam * -(Real.log 2 + Real.log lam) ≤ lam * ((2 * lam)⁻¹ - 1) :=
    mul_le_mul_of_nonneg_left (by simpa [one_div] using hlog1) h0.le
  have hm2 : (1 - lam) * -(Real.log 2 + Real.log (1 - lam)) ≤ (1 - lam) * ((2 * (1 - lam))⁻¹ - 1) :=
    mul_le_mul_of_nonneg_left (by simpa [one_div] using hlog2) h1lam.le
  have hr1 : lam * ((2 * lam)⁻¹ - 1) = 1 / 2 - lam := by field_simp [h0.ne']
  have hr2 : (1 - lam) * ((2 * (1 - lam))⁻¹ - 1) = 1 / 2 - (1 - lam) := by
    field_simp [h1lam.ne']
  rw [hr1] at hm1
  rw [hr2] at hm2
  have hsum : 0 ≤ Real.log 2 + (Real.log lam * lam + Real.log (1 - lam) * (1 - lam)) := by linarith
  have hexp := Real.exp_le_exp.mpr hsum
  rw [Real.exp_zero, Real.exp_add, Real.exp_log two_pos, Real.exp_add,
    ← Real.rpow_def_of_pos h0, ← Real.rpow_def_of_pos h1lam] at hexp
  exact hexp

/-- If `K` is reflection-symmetric across `u⊥`, then `K` admits a Santaló point lying on `u⊥`. -/
private lemma exists_santaloPoint_orth [Nontrivial E]
    {u : E} (hu : ‖u‖ = 1) (KS : ConvexBody E) (hKS_ne : (interior (KS : Set E)).Nonempty)
    (hrefl : reflectBody hu KS = KS) :
    ∃ z₀ ∈ interior (KS : Set E), ⟪z₀, u⟫ = 0 ∧
      mahlerVolumeAt (volume : Measure E) (KS : Set E) z₀ =
        santaloMahlerVolume (volume : Measure E) (KS : Set E) := by
  obtain ⟨zS, hzS_int, hzS_min⟩ := exists_santaloPoint KS hKS_ne
  set z₀ : E := (1 / 2 : ℝ) • zS + (1 / 2 : ℝ) • reflectHyperplane hu zS
  have hz₀_orth : ⟪z₀, u⟫ = 0 := by
    simp only [z₀, inner_add_left, inner_smul_left, RCLike.conj_to_real, reflectHyperplane_apply,
      inner_sub_left, real_inner_self_eq_norm_sq, hu, one_pow, mul_one]
    ring
  have hzS_refl_int : reflectHyperplane hu zS ∈ interior (KS : Set E) := by
    have himg : (reflectHyperplane hu).toHomeomorph '' (KS : Set E) = (KS : Set E) := by
      have h1 : (reflectBody hu KS : Set E) = (KS : Set E) := congrArg SetLike.coe hrefl
      simpa [coe_reflectBody] using h1
    have hmem :
        reflectHyperplane hu zS ∈ (reflectHyperplane hu).toHomeomorph '' interior (KS : Set E) :=
      ⟨zS, hzS_int, rfl⟩
    rwa [(reflectHyperplane hu).toHomeomorph.image_interior, himg] at hmem
  have hz₀_int : z₀ ∈ interior (KS : Set E) :=
    KS.convex.interior hzS_int hzS_refl_int (by norm_num) (by norm_num) (by norm_num)
  have hpol_refl : polarVolAt KS (reflectHyperplane hu zS) = polarVolAt KS zS := by
    have hpre : polarBody ((fun x : E => x - reflectHyperplane hu zS) '' (KS : Set E)) =
        (reflectHyperplane hu) ⁻¹' polarBody ((fun x : E => x - zS) '' (KS : Set E)) := by
      have hKS_img : ∀ x : E, x ∈ (KS : Set E) ↔ reflectHyperplane hu x ∈ (KS : Set E) :=
        fun x => by
          have h1 : (reflectBody hu KS : Set E) = (KS : Set E) := congrArg SetLike.coe hrefl
          constructor
          · intro hx; rw [← h1, coe_reflectBody]; exact ⟨x, hx, rfl⟩
          · intro hrx
            have : reflectHyperplane hu (reflectHyperplane hu x) ∈ (KS : Set E) := by
              rw [← h1, coe_reflectBody]; exact ⟨reflectHyperplane hu x, hrx, rfl⟩
            rwa [reflectHyperplane_involutive] at this
      ext y
      simp only [mem_polarBody, mem_image, mem_preimage, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      constructor
      · intro h x hx
        have h1 := h (reflectHyperplane hu x) ((hKS_img x).mp hx)
        rwa [← map_sub, inner_reflectHyperplane] at h1
      · intro h x hx
        have h1 := h (reflectHyperplane hu x) ((hKS_img x).mp hx)
        rwa [← inner_reflectHyperplane, map_sub, reflectHyperplane_involutive] at h1
    rw [polarVolAt, polarVolAt, Measure.real, Measure.real, hpre,
      (reflectHyperplane hu).measurePreserving.measure_preimage
        (isClosed_polarBody _).measurableSet.nullMeasurableSet]
  have hz₀_pol_le : polarVolAt KS z₀ ≤ polarVolAt KS zS := by
    have hconv := (convexOn_polarVolAt KS).2 hzS_int hzS_refl_int
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
    rw [smul_eq_mul, smul_eq_mul, hpol_refl] at hconv
    linarith
  refine ⟨z₀, hz₀_int, hz₀_orth, le_antisymm ?_ (santaloMahlerVolume_le_mahlerVolumeAt volume hz₀_int)⟩
  rw [← hzS_min]
  have hvol_eq : ∀ z : E, volume ((fun x : E => x - z) '' (KS : Set E)) = volume (KS : Set E) :=
    fun z => by
      have hpre : (fun x : E => x - z) '' (KS : Set E) = (fun x : E => z + x) ⁻¹' (KS : Set E) := by
        ext y; simp only [mem_image, mem_preimage]
        exact ⟨fun ⟨x, hx, hxy⟩ => by rw [← hxy]; simpa [add_sub_cancel] using hx,
          fun hy => ⟨z + y, hy, by abel⟩⟩
      rw [hpre, measure_preimage_add]
  unfold mahlerVolumeAt mahlerVolume
  rw [hvol_eq z₀, hvol_eq zS]
  refine mul_le_mul' le_rfl ?_
  have hfin0 : volume (polarBody ((fun x : E => x - z₀) '' (KS : Set E))) ≠ ⊤ :=
    (isCompact_polarBody_of_zero_mem_interior
      (zero_mem_interior_translate_neg hz₀_int)).measure_lt_top.ne
  have hfinS : volume (polarBody ((fun x : E => x - zS) '' (KS : Set E))) ≠ ⊤ :=
    (isCompact_polarBody_of_zero_mem_interior
      (zero_mem_interior_translate_neg hzS_int)).measure_lt_top.ne
  rw [← ENNReal.ofReal_toReal hfin0, ← ENNReal.ofReal_toReal hfinS]
  exact ENNReal.ofReal_le_ofReal hz₀_pol_le

/-- Slice-volume regularity for a compact convex set `P ⊆ ℝ × H` containing `(0, 0)` in its
interior: positive extent `M = sSup (Prod.fst '' P)`, uniform bound, measurability, strict
positivity and Brunn-concavity continuity on `Ioo 0 M`, and Fubini half-volume identity. -/
private lemma convex_prod_posSlice_properties {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [Nontrivial H]
    [MeasurableSpace H] [BorelSpace H]
    {P : Set (ℝ × H)} (hPc : IsCompact P) (hPconv : Convex ℝ P)
    (h0P : ((0 : ℝ), (0 : H)) ∈ interior P) :
    let f : ℝ → ℝ := fun s => volume.real {y : H | (s, y) ∈ P}
    let M : ℝ := sSup (Prod.fst '' P)
    0 < M ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ f s ∧ f s ≤ C) ∧ Measurable f ∧
      (∀ s ∈ Ioo 0 M, 0 < f s) ∧ ContinuousOn f (Ioo 0 M) ∧
      ∫ t in Ioo 0 M, f t = volume.real (P ∩ {p : ℝ × H | 0 < p.1}) := by
  let sliceP : ℝ → Set H := fun s => {y : H | (s, y) ∈ P}
  let f : ℝ → ℝ := fun s => volume.real (sliceP s)
  set M : ℝ := sSup (Prod.fst '' P)
  obtain ⟨RP, hPR⟩ := hPc.isBounded.subset_closedBall ((0 : ℝ), (0 : H))
  set C_H : ℝ := volume.real (closedBall (0 : H) (max RP 1))
  have hsliceP_sub : ∀ s : ℝ, sliceP s ⊆ closedBall (0 : H) (max RP 1) := fun s y hy => by
    have h1 := hPR hy
    rw [mem_closedBall, dist_eq_norm, Prod.mk_sub_mk, sub_zero, sub_zero, Prod.norm_def] at h1
    exact mem_closedBall_zero_iff.mpr (((le_max_right _ _).trans h1).trans (le_max_left _ _))
  have hsliceP_compact : ∀ s : ℝ, IsCompact (sliceP s) := fun s =>
    (isCompact_closedBall (0 : H) (max RP 1)).of_isClosed_subset
      (hPc.isClosed.preimage (continuous_const.prodMk continuous_id)) (hsliceP_sub s)
  have hf_bdd : ∀ s : ℝ, 0 ≤ f s ∧ f s ≤ C_H := fun s =>
    ⟨measureReal_nonneg, measureReal_mono (hsliceP_sub s) (isCompact_closedBall _ _).measure_lt_top.ne⟩
  have hf_meas : Measurable f :=
    ENNReal.measurable_toReal.comp
      (measurable_measure_prodMk_left (ν := (volume : Measure H)) hPc.isClosed.measurableSet)
  obtain ⟨δ₀, hδ₀_pos, hball0P⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0P)
  have hM_pos : 0 < M := by
    have hmem : δ₀ / 2 ∈ Prod.fst '' P :=
      ⟨(δ₀ / 2, 0), hball0P (by
        rw [mem_ball, Prod.dist_eq, dist_zero_right, dist_zero_right, Real.norm_eq_abs,
          abs_of_pos (half_pos hδ₀_pos), norm_zero]
        exact max_lt (half_lt_self hδ₀_pos) hδ₀_pos), rfl⟩
    exact (half_pos hδ₀_pos).trans_le (le_csSup (hPc.image continuous_fst).bddAbove hmem)
  have hf_pos : ∀ s ∈ Ioo 0 M, 0 < f s := fun s hs => by
    have hex : ∃ s₁ ∈ Prod.fst '' P, s < s₁ :=
      exists_lt_of_lt_csSup ⟨0, ⟨(0, 0), interior_subset h0P, rfl⟩⟩ hs.2
    rcases hex with ⟨s₁, ⟨⟨t₁, y₁⟩, hp₁, ht₁⟩, hs_lt⟩
    dsimp only at ht₁; subst t₁
    have hs₁_pos : 0 < s₁ := hs.1.trans hs_lt
    set lam : ℝ := s / s₁
    have hlam0 : 0 < lam := div_pos hs.1 hs₁_pos
    have hlam1 : lam < 1 := (div_lt_one hs₁_pos).mpr hs_lt
    have hball_sub : ball (lam • y₁) ((1 - lam) * (δ₀ / 2)) ⊆ sliceP s := fun w hw => by
      set z : H := (1 - lam)⁻¹ • (w - lam • y₁)
      have hz_lt : ‖z‖ < δ₀ / 2 := by
        dsimp only [z]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (sub_pos.mpr hlam1))]
        rw [mem_ball, dist_eq_norm] at hw
        exact (inv_mul_lt_iff₀ (sub_pos.mpr hlam1)).mpr (by linarith)
      have h0z : ((0 : ℝ), z) ∈ P := hball0P (by
        rw [mem_ball, Prod.dist_eq, dist_zero_right, dist_zero_right, Real.norm_eq_abs, abs_zero]
        exact max_lt hδ₀_pos (hz_lt.trans (half_lt_self hδ₀_pos)))
      have hcomb := hPconv h0z hp₁ (sub_pos.mpr hlam1).le hlam0.le (by ring)
      have heq : (1 - lam) • ((0 : ℝ), z) + lam • (s₁, y₁) = (s, w) := by
        apply Prod.ext
        · change (1 - lam) * 0 + lam * s₁ = s
          dsimp only [lam]; field_simp [hs₁_pos.ne']; ring
        · change (1 - lam) • z + lam • y₁ = w
          dsimp only [z]
          rw [smul_smul, mul_inv_cancel₀ (sub_pos.mpr hlam1).ne', one_smul, sub_add_cancel]
      rwa [heq] at hcomb
    have hpos_ball : 0 < volume.real (ball (lam • y₁) ((1 - lam) * (δ₀ / 2))) := by
      rw [Measure.real, ENNReal.toReal_pos_iff]
      exact ⟨isOpen_ball.measure_pos volume
          ⟨_, mem_ball_self (mul_pos (sub_pos.mpr hlam1) (half_pos hδ₀_pos))⟩,
        (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall _ _).measure_lt_top⟩
    exact hpos_ball.trans_le (measureReal_mono hball_sub (hsliceP_compact s).measure_lt_top.ne)
  set m : ℕ := Module.finrank ℝ H
  have hm_rpos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  have hf_concave : ConcaveOn ℝ (Ioo 0 M) (fun s : ℝ => f s ^ ((1 : ℝ) / (m : ℝ))) := by
    refine ⟨convex_Ioo 0 M, fun s₁ hs₁ s₂ hs₂ a b ha hb hab => ?_⟩
    rcases ha.eq_or_lt with rfl | ha_pos
    · have hb1 : b = 1 := by linarith
      subst hb1; simp
    rcases hb.eq_or_lt with rfl | hb_pos
    · have ha1 : a = 1 := by linarith
      subst ha1; simp
    have hne1 : (sliceP s₁).Nonempty := by
      by_contra hemp; rw [Set.not_nonempty_iff_eq_empty] at hemp
      have : f s₁ = 0 := by simp [f, hemp]
      linarith [hf_pos s₁ hs₁]
    have hne2 : (sliceP s₂).Nonempty := by
      by_contra hemp; rw [Set.not_nonempty_iff_eq_empty] at hemp
      have : f s₂ = 0 := by simp [f, hemp]
      linarith [hf_pos s₂ hs₂]
    have hsub_add : a • sliceP s₁ + b • sliceP s₂ ⊆ sliceP (a * s₁ + b * s₂) := by
      rintro _ ⟨_, ⟨y₁, hy₁, rfl⟩, _, ⟨y₂, hy₂, rfl⟩, rfl⟩
      change (a * s₁ + b * s₂, a • y₁ + b • y₂) ∈ P
      simpa [Prod.smul_mk, Prod.mk_add_mk] using hPconv hy₁ hy₂ ha hb hab
    have hbm := (brunn_minkowski_compact (E := H) ((hsliceP_compact s₁).smul a)
      (hne1.smul_set) ((hsliceP_compact s₂).smul b) (hne2.smul_set)).trans
      (ENNReal.rpow_le_rpow (measure_mono hsub_add) (by positivity))
    rw [addHaar_smul_rpow_inv_finrank volume ha (sliceP s₁),
      addHaar_smul_rpow_inv_finrank volume hb (sliceP s₂)] at hbm
    have hconv_enn : ∀ s : ℝ, volume (sliceP s) ^ ((1 : ℝ) / (m : ℝ)) =
        ENNReal.ofReal (f s ^ ((1 : ℝ) / (m : ℝ))) := fun s => by
      rw [← ENNReal.ofReal_rpow_of_nonneg measureReal_nonneg (by positivity),
        Measure.real, ENNReal.ofReal_toReal (hsliceP_compact s).measure_lt_top.ne]
    rw [hconv_enn s₁, hconv_enn s₂, hconv_enn _, ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hb,
      ← ENNReal.ofReal_add (by positivity) (by positivity)] at hbm
    simpa [smul_eq_mul] using (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbm
  have hf_cont : ContinuousOn f (Ioo 0 M) := by
    have hcont_rpow : ContinuousOn (fun s : ℝ => f s ^ ((1 : ℝ) / (m : ℝ))) (Ioo 0 M) := by
      simpa using (hf_concave.neg.continuousOn isOpen_Ioo).neg
    refine (hcont_rpow.pow m).congr fun s _ => ?_
    dsimp only [Pi.pow_apply]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hf_bdd s).1, one_div_mul_cancel hm_rpos.ne',
      Real.rpow_one]
  have hf_int : ∫ t in Ioo 0 M, f t = volume.real (P ∩ {p : ℝ × H | 0 < p.1}) := by
    have hm_set : MeasurableSet (P ∩ {p : ℝ × H | 0 < p.1}) :=
      hPc.isClosed.measurableSet.inter (isOpen_lt continuous_const continuous_fst).measurableSet
    have hvol_enn : volume (P ∩ {p : ℝ × H | 0 < p.1}) = ∫⁻ t in Ioo 0 M, ENNReal.ofReal (f t) := by
      rw [Measure.volume_eq_prod, Measure.prod_apply hm_set]
      have hfib : ∀ t : ℝ, volume (Prod.mk t ⁻¹' (P ∩ {p : ℝ × H | 0 < p.1})) =
          (Ioi (0 : ℝ)).indicator (fun s => ENNReal.ofReal (f s)) t := fun t => by
        by_cases ht : 0 < t
        · rw [indicator_of_mem ht]
          have hpre : Prod.mk t ⁻¹' (P ∩ {p : ℝ × H | 0 < p.1}) = sliceP t := by
            ext y; simp [sliceP, ht]
          rw [hpre]
          dsimp only [f]
          rw [Measure.real, ENNReal.ofReal_toReal (hsliceP_compact t).measure_lt_top.ne]
        · rw [indicator_of_notMem ht]
          have hpre : Prod.mk t ⁻¹' (P ∩ {p : ℝ × H | 0 < p.1}) = ∅ := by ext y; simp [ht]
          rw [hpre, measure_empty]
      simp_rw [hfib]
      rw [lintegral_indicator measurableSet_Ioi]
      have hzero_gt : ∀ t : ℝ, M < t → ENNReal.ofReal (f t) = 0 := fun t ht => by
        have hemp : sliceP t = ∅ := by
          ext y; simp only [sliceP, mem_ofPred_eq, mem_empty_iff_false, iff_false]
          intro hp
          linarith [le_csSup (hPc.image continuous_fst).bddAbove ⟨(t, y), hp, rfl⟩]
        simp [f, hemp]
      have hsplit : Ioi (0 : ℝ) = Ioo 0 M ∪ {M} ∪ Ioi M := by
        ext t; simp only [mem_union, mem_Ioi, mem_Ioo, mem_singleton_iff]
        constructor
        · intro ht
          rcases lt_trichotomy t M with hlt | rfl | hgt
          · exact Or.inl (Or.inl ⟨ht, hlt⟩)
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr hgt
        · rintro ((⟨h1, _⟩ | rfl) | hgt)
          · exact h1
          · exact hM_pos
          · exact hM_pos.trans hgt
      rw [hsplit]
      have h1 : ∫⁻ t in (Ioo 0 M ∪ {M}) ∪ Ioi M, ENNReal.ofReal (f t) =
          ∫⁻ t in Ioo 0 M ∪ {M}, ENNReal.ofReal (f t) := by
        rw [lintegral_union measurableSet_Ioi (by
          rw [Set.disjoint_left]; rintro t (⟨_, h2⟩ | rfl) hgt <;> linarith [mem_Ioi.mp hgt])]
        rw [setLIntegral_congr_fun measurableSet_Ioi fun t ht => hzero_gt t ht, lintegral_zero,
          add_zero]
      rw [h1, lintegral_union (measurableSet_singleton M) (by
        rw [Set.disjoint_left]; intro t ht htm; simp only [mem_singleton_iff] at htm; linarith [ht.2]),
        lintegral_singleton, Real.volume_singleton, mul_zero, add_zero]
    have hint_f : IntegrableOn f (Ioo 0 M) volume :=
      (integrableOn_const (C := C_H) (by simp : volume (Ioo 0 M) ≠ ⊤)).mono'
        hf_meas.aestronglyMeasurable (ae_of_all _ fun t => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hf_bdd t).1]; exact (hf_bdd t).2)
    rw [Measure.real, hvol_enn,
      ← ofReal_integral_eq_lintegral_ofReal hint_f (ae_of_all _ fun t => (hf_bdd t).1),
      ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioo fun t _ => (hf_bdd t).1)]
  exact ⟨hM_pos, ⟨C_H, measureReal_nonneg, hf_bdd⟩, hf_meas, hf_pos, hf_cont, hf_int⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Meyer–Pajor Geometric Slice Inclusion:** for `s₁, s₂ > 0`, `λ = s₂ / (s₁ + s₂)`, and harmonic
mean `τ = 2 s₁ s₂ / (s₁ + s₂)`, the weighted Minkowski combination of the `s₁`-slice and `(-s₂)`-slice
of `(K₁ - t₀ • u)°` lies inside the `τ`-slice of `(S_u K₁)°`. -/
private lemma meyer_pajor_slice_subset {u : E} (hu : ‖u‖ = 1) (K₁ : ConvexBody E) (t₀ : ℝ)
    {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) :
    let Φ := orthoSplitProd hu
    let K₀ : Set E := (fun x : E => x - t₀ • u) '' (K₁ : Set E)
    let lam : ℝ := s₂ / (s₁ + s₂)
    let τ : ℝ := 2 * s₁ * s₂ / (s₁ + s₂)
    lam • {y : orthoHyperplane u | (s₁, y) ∈ Φ '' polarBody K₀} +
      (1 - lam) • {y : orthoHyperplane u | (-s₂, y) ∈ Φ '' polarBody K₀} ⊆
        {y : orthoHyperplane u | (τ, y) ∈ Φ '' polarBody (bodySteinerSymmDir hu K₁ : Set E)} := by
  intro Φ K₀ lam τ
  have hsum : 0 < s₁ + s₂ := add_pos hs₁ hs₂
  have hlam0 : 0 < lam := div_pos hs₂ hsum
  have hlam1 : lam < 1 := (div_lt_one hsum).mpr (by linarith)
  have h1lam : 1 - lam = s₁ / (s₁ + s₂) := by dsimp only [lam]; field_simp [hsum.ne']; ring
  have hτ_pos : 0 < τ := by dsimp only [τ]; positivity
  rintro _ ⟨_, ⟨y₁, hy₁, rfl⟩, _, ⟨y₂, hy₂, rfl⟩, rfl⟩
  rcases hy₁ with ⟨z₁, hz₁, hz₁_eq⟩
  rcases hy₂ with ⟨z₂, hz₂, hz₂_eq⟩
  refine ⟨Φ.symm (τ, lam • y₁ + (1 - lam) • y₂), ?_, Φ.apply_symm_apply _⟩
  intro x hxKS₁
  let K₁' : Set (ℝ × orthoHyperplane u) := Φ '' (K₁ : Set E)
  have hK₁'c : IsCompact K₁' := K₁.isCompact.image (continuous_orthoSplitProd hu)
  have hxS' : Φ x ∈ steinerSymm K₁' := hxKS₁
  set t : ℝ := (Φ x).1
  set w : orthoHyperplane u := (Φ x).2
  have hne_w : (steinerFiber K₁' w).Nonempty := hxS'.1
  set a : ℝ := steinerLower K₁' w
  set b : ℝ := steinerUpper K₁' w
  rcases (isCompact_steinerFiber hK₁'c w).sInf_mem hne_w with ⟨xa, hxaK₁, hxa_eq⟩
  rcases (isCompact_steinerFiber hK₁'c w).sSup_mem hne_w with ⟨xb, hxbK₁, hxb_eq⟩
  have hshift_Φ : ∀ {z : E} {r : ℝ}, Φ z = (r, w) → Φ (z - t₀ • u) = (r - t₀, w) := by
    intro z r hzeq
    rw [map_sub, hzeq]
    apply Prod.ext
    · dsimp only [Φ]; rw [orthoSplitProd_apply]
      simp only [Prod.fst_sub, inner_smul_left, RCLike.conj_to_real,
        real_inner_self_eq_norm_sq, hu, one_pow, mul_one]
    · apply Subtype.ext
      dsimp only [Φ]; rw [orthoSplitProd_apply]
      simp only [Prod.snd_sub, AddSubgroupClass.coe_sub, inner_smul_left, RCLike.conj_to_real,
        real_inner_self_eq_norm_sq, hu, one_pow, mul_one, sub_self, sub_zero]
  have h1 : (b - t₀) * s₁ + ⟪w, y₁⟫ ≤ 1 := by
    have hpol := hz₁ (xb - t₀ • u) ⟨xb, hxbK₁, rfl⟩
    rw [orthoSplitProd_inner hu (xb - t₀ • u) z₁, hshift_Φ hxb_eq, hz₁_eq] at hpol
    exact hpol
  have h2 : (t₀ - a) * s₂ + ⟪w, y₂⟫ ≤ 1 := by
    have hpol := hz₂ (xa - t₀ • u) ⟨xa, hxaK₁, rfl⟩
    rw [orthoSplitProd_inner hu (xa - t₀ • u) z₂, hshift_Φ hxa_eq, hz₂_eq] at hpol
    change (a - t₀) * (-s₂) + ⟪w, y₂⟫ ≤ 1 at hpol
    linarith
  have hcomb : ((b - a) / 2) * τ + ⟪w, lam • y₁ + (1 - lam) • y₂⟫ ≤ 1 := by
    have hm1 : lam * ((b - t₀) * s₁ + ⟪w, y₁⟫) ≤ lam := by nlinarith
    have hm2 : (1 - lam) * ((t₀ - a) * s₂ + ⟪w, y₂⟫) ≤ 1 - lam := by nlinarith
    have hlam_s1 : lam * s₁ = τ / 2 := by dsimp only [lam, τ]; field_simp [hsum.ne']
    have h1lam_s2 : (1 - lam) * s₂ = τ / 2 := by rw [h1lam]; dsimp only [τ]; field_simp [hsum.ne']
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    have halg : lam * ((b - t₀) * s₁) + (1 - lam) * ((t₀ - a) * s₂) = ((b - a) / 2) * τ := by
      calc
        lam * ((b - t₀) * s₁) + (1 - lam) * ((t₀ - a) * s₂)
          = (b - t₀) * (lam * s₁) + (t₀ - a) * ((1 - lam) * s₂) := by ring
        _ = (b - t₀) * (τ / 2) + (t₀ - a) * (τ / 2) := by rw [hlam_s1, h1lam_s2]
        _ = ((b - a) / 2) * τ := by ring
    linarith
  rw [orthoSplitProd_inner hu x (Φ.symm (τ, lam • y₁ + (1 - lam) • y₂)), Φ.apply_symm_apply]
  have ht_le : t ≤ (b - a) / 2 := (le_abs_self t).trans hxS'.2
  linarith [mul_le_mul_of_nonneg_right ht_le hτ_pos.le]

/-- **Meyer–Pajor Polar Volume Inequality (Balanced Shift):** given `t₀ • u ∈ interior K₁` whose
shifted polar `K₀°` has equal positive and negative half-volumes across `u⊥`, and
`0 ∈ interior (S_u K₁)`, we have `volume (K₀°) ≤ volume ((S_u K₁)°)`. -/
private lemma meyer_pajor_polar_volume_le
    {u : E} (hu : ‖u‖ = 1) (hd2 : 2 ≤ Module.finrank ℝ E)
    (K₁ : ConvexBody E) {t₀ : ℝ}
    (ht₀_int : t₀ • u ∈ interior (K₁ : Set E))
    (h0S₁ : (0 : E) ∈ interior (bodySteinerSymmDir hu K₁ : Set E))
    (hbal : volume.real (polarBody ((fun x : E => x - t₀ • u) '' (K₁ : Set E)) ∩
        {y : E | 0 < ⟪y, u⟫}) =
      volume.real (polarBody ((fun x : E => x - t₀ • u) '' (K₁ : Set E)) ∩
        {y : E | ⟪y, u⟫ < 0})) :
    volume (polarBody ((fun x : E => x - t₀ • u) '' (K₁ : Set E))) ≤
      volume (polarBody (bodySteinerSymmDir hu K₁ : Set E)) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
  let H := orthoHyperplane u
  have hH_dim : Module.finrank ℝ H = Module.finrank ℝ E - 1 := by
    have hsplit := (orthoSplitProd hu).finrank_eq
    rw [Module.finrank_prod, Module.finrank_self] at hsplit
    change Module.finrank ℝ E = 1 + Module.finrank ℝ H at hsplit
    omega
  have : Nontrivial H := Module.nontrivial_of_finrank_pos (R := ℝ) (M := H) (by omega)
  let KS₁ : ConvexBody E := bodySteinerSymmDir hu K₁
  let K₀ : Set E := (fun x : E => x - t₀ • u) '' (K₁ : Set E)
  have h0K₀ : (0 : E) ∈ interior K₀ := zero_mem_interior_translate_neg ht₀_int
  let Φ := orthoSplitProd hu
  have hmp : MeasurePreserving Φ (volume : Measure E) (volume : Measure (ℝ × H)) :=
    measurePreserving_orthoSplitProd hu
  let P : Set (ℝ × H) := Φ '' polarBody K₀
  let Q : Set (ℝ × H) := Φ '' polarBody (KS₁ : Set E)
  have hPc : IsCompact P :=
    (isCompact_polarBody_of_zero_mem_interior h0K₀).image (continuous_orthoSplitProd hu)
  have hPconv : Convex ℝ P := (convex_polarBody K₀).linear_image Φ.toLinearMap
  have hQc : IsCompact Q :=
    (isCompact_polarBody_of_zero_mem_interior h0S₁).image (continuous_orthoSplitProd hu)
  have h0P : ((0 : ℝ), (0 : H)) ∈ interior P := by
    have hK₀_bdd : Bornology.IsBounded K₀ := by
      obtain ⟨R, hR⟩ := K₁.isBounded.subset_closedBall (0 : E)
      rw [Metric.isBounded_iff_subset_closedBall (0 : E)]
      refine ⟨R + ‖t₀ • u‖, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_closedBall_zero_iff]
      linarith [norm_sub_le x (t₀ • u), mem_closedBall_zero_iff.mp (hR hx)]
    have h0pol : (0 : E) ∈ interior (polarBody K₀) := zero_mem_interior_polarBody_of_isBounded hK₀_bdd
    have h1 : (orthoSplitHomeomorph hu : E → ℝ × H) = Φ := funext (orthoSplitHomeomorph_coe hu)
    have himg : Φ '' interior (polarBody K₀) = interior P := by
      rw [← h1]; exact (orthoSplitHomeomorph hu).image_interior (polarBody K₀)
    rw [← himg]; exact ⟨0, h0pol, map_zero Φ⟩
  -- Apply `convex_prod_posSlice_properties` once to `P` and once to its reflection `Pneg`.
  let swapH : ℝ × H ≃ₜ ℝ × H := (Homeomorph.neg ℝ).prodCongr (Homeomorph.refl H)
  let swapL : ℝ × H →ₗ[ℝ] ℝ × H := LinearMap.prod (-LinearMap.fst ℝ ℝ H) (LinearMap.snd ℝ ℝ H)
  have hswap_eq : (swapH : ℝ × H → ℝ × H) = swapL := by ext ⟨s, y⟩ <;> rfl
  let Pneg : Set (ℝ × H) := swapH '' P
  have hPneg_c : IsCompact Pneg := hPc.image swapH.continuous
  have hPneg_conv : Convex ℝ Pneg := by rw [show Pneg = swapL '' P by rw [← hswap_eq]]; exact hPconv.linear_image swapL
  have h0Pneg : ((0 : ℝ), (0 : H)) ∈ interior Pneg := by
    rw [show Pneg = swapH '' P from rfl, ← swapH.image_interior]
    exact ⟨(0, 0), h0P, by simp [swapH]⟩
  have hmp_swap : MeasurePreserving (swapH : ℝ × H → ℝ × H)
      (volume : Measure (ℝ × H)) (volume : Measure (ℝ × H)) := by
    rw [Measure.volume_eq_prod]
    exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
      (MeasurePreserving.id (volume : Measure H))
  let sliceP : ℝ → Set H := fun s => {y : H | (s, y) ∈ P}
  let sliceQ : ℝ → Set H := fun s => {y : H | (s, y) ∈ Q}
  let f : ℝ → ℝ := fun s => volume.real (sliceP s)
  let g : ℝ → ℝ := fun s => volume.real (sliceP (-s))
  let h : ℝ → ℝ := fun τ => volume.real (sliceQ τ)
  have hsliceP_compact : ∀ s : ℝ, IsCompact (sliceP s) := fun s => by
    obtain ⟨RP, hPR⟩ := hPc.isBounded.subset_closedBall ((0 : ℝ), (0 : H))
    refine (isCompact_closedBall (0 : H) RP).of_isClosed_subset
      (hPc.isClosed.preimage (continuous_const.prodMk continuous_id)) fun y hy => ?_
    have h1 := hPR hy
    rw [mem_closedBall, dist_eq_norm, Prod.mk_sub_mk, sub_zero, sub_zero, Prod.norm_def] at h1
    exact mem_closedBall_zero_iff.mpr ((le_max_right _ _).trans h1)
  have hslice_neg : ∀ s : ℝ, {y : H | (s, y) ∈ Pneg} = sliceP (-s) := fun s => by
    ext y
    simp only [mem_ofPred_eq, Pneg, mem_image, sliceP]
    constructor
    · rintro ⟨⟨t, z⟩, hp, htz⟩
      have h1 : -t = s ∧ z = y := Prod.mk.inj htz
      simpa [← h1.1, ← h1.2] using hp
    · intro hp; exact ⟨(-s, y), hp, by simp [swapH]⟩
  obtain ⟨hM_f_pos, ⟨C_f, hCf_nn, hf_bdd⟩, hf_meas, hf_pos, hf_cont, hPos_int⟩ :=
    convex_prod_posSlice_properties hPc hPconv h0P
  obtain ⟨hM_g_pos, ⟨C_g, hCg_nn, hg_bdd'⟩, hg_meas', hg_pos', hg_cont', hNeg_int'⟩ :=
    convex_prod_posSlice_properties hPneg_c hPneg_conv h0Pneg
  have hg_eq_fn : (fun s : ℝ => volume.real {y : H | (s, y) ∈ Pneg}) = g :=
    funext fun s => by dsimp only [g]; rw [hslice_neg s]
  rw [hg_eq_fn] at hg_bdd' hg_meas' hg_pos' hg_cont' hNeg_int'
  set M_f : ℝ := sSup (Prod.fst '' P)
  set M_g : ℝ := sSup (Prod.fst '' Pneg)
  have hP_pos_vol : volume.real (P ∩ {p : ℝ × H | 0 < p.1}) =
      volume.real (polarBody K₀ ∩ {y : E | 0 < ⟪y, u⟫}) := by
    have hset_eq : polarBody K₀ ∩ {y : E | 0 < ⟪y, u⟫} = Φ ⁻¹' (P ∩ {p : ℝ × H | 0 < p.1}) := by
      ext y; simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, P, mem_image]
      constructor
      · rintro ⟨hy, hyu⟩; exact ⟨⟨y, hy, rfl⟩, by dsimp only [Φ]; rw [orthoSplitProd_apply]; exact hyu⟩
      · rintro ⟨⟨z, hz, hzy⟩, hyu⟩
        refine ⟨Φ.injective hzy ▸ hz, ?_⟩
        dsimp only [Φ] at hyu; rw [orthoSplitProd_apply] at hyu; exact hyu
    have hm_set : MeasurableSet (P ∩ {p : ℝ × H | 0 < p.1}) :=
      hPc.isClosed.measurableSet.inter (isOpen_lt continuous_const continuous_fst).measurableSet
    rw [Measure.real, Measure.real, hset_eq, hmp.measure_preimage hm_set.nullMeasurableSet]
  have hPneg_pos_vol : volume.real (Pneg ∩ {p : ℝ × H | 0 < p.1}) =
      volume.real (polarBody K₀ ∩ {y : E | ⟪y, u⟫ < 0}) := by
    have hswap_app : ∀ p : ℝ × H, swapH p = (-p.1, p.2) := fun _ => rfl
    have hpre1 : swapH ⁻¹' (Pneg ∩ {p : ℝ × H | 0 < p.1}) = P ∩ {p : ℝ × H | p.1 < 0} := by
      ext ⟨s, y⟩
      simp only [mem_preimage, mem_inter_iff, Pneg, mem_image, mem_ofPred_eq, hswap_app,
        Left.neg_pos_iff]
      exact ⟨fun ⟨⟨p, hp, hpeq⟩, hs⟩ => ⟨by
          have h1 := Prod.mk.inj hpeq
          have : p = (s, y) := Prod.ext (by linarith [h1.1]) h1.2
          rwa [← this], hs⟩,
        fun ⟨hp, hs⟩ => ⟨⟨(s, y), hp, rfl⟩, hs⟩⟩
    have hset_eq : polarBody K₀ ∩ {y : E | ⟪y, u⟫ < 0} = Φ ⁻¹' (P ∩ {p : ℝ × H | p.1 < 0}) := by
      ext y; simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, P, mem_image]
      constructor
      · rintro ⟨hy, hyu⟩; exact ⟨⟨y, hy, rfl⟩, by dsimp only [Φ]; rw [orthoSplitProd_apply]; exact hyu⟩
      · rintro ⟨⟨z, hz, hzy⟩, hyu⟩
        refine ⟨Φ.injective hzy ▸ hz, ?_⟩
        dsimp only [Φ] at hyu; rw [orthoSplitProd_apply] at hyu; exact hyu
    have hm_pneg : MeasurableSet (Pneg ∩ {p : ℝ × H | 0 < p.1}) :=
      hPneg_c.isClosed.measurableSet.inter (isOpen_lt continuous_const continuous_fst).measurableSet
    have hm_neg : MeasurableSet (P ∩ {p : ℝ × H | p.1 < 0}) :=
      hPc.isClosed.measurableSet.inter (isOpen_lt continuous_fst continuous_const).measurableSet
    rw [Measure.real, Measure.real, ← hmp_swap.measure_preimage hm_pneg.nullMeasurableSet, hpre1,
      hset_eq, hmp.measure_preimage hm_neg.nullMeasurableSet]
  set V2 : ℝ := ∫ t in Ioo 0 M_f, f t
  have hVg_eq : ∫ t in Ioo 0 M_g, g t = V2 := by
    rw [hNeg_int', hPneg_pos_vol, ← hbal, ← hP_pos_vol, ← hPos_int]
  -- Extract quantile inverses `s₁` (for `f`) and `s₂` (for `g`) on `Ioo 0 V2`.
  obtain ⟨hV2_pos, s₁, hs₁_mem, _, hs₁_deriv⟩ :=
    exists_cdf_quantile_inverse hM_f_pos hCf_nn hf_meas hf_bdd hf_cont hf_pos
  obtain ⟨_, s₂, hs₂_mem, _, hs₂_deriv⟩ :=
    exists_cdf_quantile_inverse hM_g_pos hCg_nn hg_meas' hg_bdd' hg_cont' hg_pos'
  rw [hVg_eq] at hs₂_mem hs₂_deriv
  -- Harmonic-mean transport `τ(r) = 2 * s₁(r) * s₂(r) / (s₁(r) + s₂(r))` and its derivative `τ'`.
  let τ : ℝ → ℝ := fun r => 2 * s₁ r * s₂ r / (s₁ r + s₂ r)
  let τ' : ℝ → ℝ := fun r =>
    2 * ((s₂ r / (s₁ r + s₂ r)) ^ 2 * (f (s₁ r))⁻¹ +
      (s₁ r / (s₁ r + s₂ r)) ^ 2 * (g (s₂ r))⁻¹)
  have hτ_deriv : ∀ r ∈ Ioo 0 V2, HasDerivAt τ (τ' r) r := fun r hr => by
    have hsum : 0 < s₁ r + s₂ r := add_pos (hs₁_mem r hr).1 (hs₂_mem r hr).1
    have hnum : HasDerivAt (fun x => 2 * s₁ x * s₂ x)
        (2 * (f (s₁ r))⁻¹ * s₂ r + 2 * s₁ r * (g (s₂ r))⁻¹) r :=
      ((hs₁_deriv r hr).const_mul 2).mul (hs₂_deriv r hr)
    have hden : HasDerivAt (fun x => s₁ x + s₂ x) ((f (s₁ r))⁻¹ + (g (s₂ r))⁻¹) r :=
      (hs₁_deriv r hr).add (hs₂_deriv r hr)
    convert hnum.div hden hsum.ne' using 1
    dsimp only [τ']; field_simp [hsum.ne']; ring
  have hτ'_pos : ∀ r ∈ Ioo 0 V2, 0 < τ' r := fun r hr => by
    have hs1 : 0 < s₁ r := (hs₁_mem r hr).1
    have hs2 : 0 < s₂ r := (hs₂_mem r hr).1
    have hf1 : 0 < f (s₁ r) := hf_pos _ (hs₁_mem r hr)
    have hg2 : 0 < g (s₂ r) := hg_pos' _ (hs₂_mem r hr)
    dsimp only [τ']; positivity
  have hτ_mono : StrictMonoOn τ (Ioo 0 V2) :=
    strictMonoOn_of_deriv_pos (convex_Ioo 0 V2)
      (fun r hr => (hτ_deriv r hr).continuousAt.continuousWithinAt)
      (fun r hr => by rw [isOpen_Ioo.interior_eq] at hr; rw [(hτ_deriv r hr).deriv]; exact hτ'_pos r hr)
  -- Pointwise inequality `1 ≤ τ'(r) * h(τ(r))` via slice inclusion + Brunn–Minkowski + AM–GM.
  have hkey_pt : ∀ r ∈ Ioo 0 V2, 1 ≤ τ' r * h (τ r) := fun r hr => by
    have hs1 : 0 < s₁ r := (hs₁_mem r hr).1
    have hs2 : 0 < s₂ r := (hs₂_mem r hr).1
    have hsum : 0 < s₁ r + s₂ r := add_pos hs1 hs2
    set lam : ℝ := s₂ r / (s₁ r + s₂ r)
    have hlam0 : 0 < lam := div_pos hs2 hsum
    have hlam1 : lam < 1 := (div_lt_one hsum).mpr (by linarith)
    have h1lam : 1 - lam = s₁ r / (s₁ r + s₂ r) := by dsimp only [lam]; field_simp [hsum.ne']; ring
    have hslice_sub : lam • sliceP (s₁ r) + (1 - lam) • sliceP (-s₂ r) ⊆ sliceQ (τ r) :=
      meyer_pajor_slice_subset hu K₁ t₀ hs1 hs2
    have hf1_pos : 0 < f (s₁ r) := hf_pos _ (hs₁_mem r hr)
    have hg2_pos : 0 < g (s₂ r) := hg_pos' _ (hs₂_mem r hr)
    have hbm_real : f (s₁ r) ^ lam * g (s₂ r) ^ (1 - lam) ≤ h (τ r) := by
      have hbm := brunn_minkowski_mul_compact (E := H) (hsliceP_compact (s₁ r))
        (hsliceP_compact (-s₂ r)) (t := 1 - lam) (sub_pos.mpr hlam1) (by linarith)
      rw [show (1 : ℝ) - (1 - lam) = lam by ring] at hbm
      have hbm' := hbm.trans (measure_mono hslice_sub)
      have hfin1 : volume (sliceP (s₁ r)) ≠ ⊤ := (hsliceP_compact (s₁ r)).measure_lt_top.ne
      have hfin2 : volume (sliceP (-s₂ r)) ≠ ⊤ := (hsliceP_compact (-s₂ r)).measure_lt_top.ne
      have hfinQ : volume (sliceQ (τ r)) ≠ ⊤ := by
        obtain ⟨RQ, hQR⟩ := hQc.isBounded.subset_closedBall ((0 : ℝ), (0 : H))
        have hsubQ : sliceQ (τ r) ⊆ closedBall (0 : H) RQ := fun y hy => by
          have h1 := hQR hy
          rw [mem_closedBall, dist_eq_norm, Prod.mk_sub_mk, sub_zero, sub_zero, Prod.norm_def] at h1
          exact mem_closedBall_zero_iff.mpr ((le_max_right _ _).trans h1)
        exact ((measure_mono hsubQ).trans_lt (isCompact_closedBall _ _).measure_lt_top).ne
      rw [← ENNReal.ofReal_toReal hfin1, ← ENNReal.ofReal_toReal hfin2, ← ENNReal.ofReal_toReal hfinQ,
        ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hlam0.le,
        ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (sub_pos.mpr hlam1).le,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg ENNReal.toReal_nonneg _)] at hbm'
      exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hbm'
    have hderiv_lb : (f (s₁ r) ^ lam * g (s₂ r) ^ (1 - lam))⁻¹ ≤ τ' r := by
      have hgm := Real.geom_mean_le_arith_mean2_weighted hlam0.le (sub_pos.mpr hlam1).le
        (by positivity : (0 : ℝ) ≤ lam * (f (s₁ r))⁻¹)
        (by positivity : (0 : ℝ) ≤ (1 - lam) * (g (s₂ r))⁻¹) (by ring)
      rw [Real.mul_rpow hlam0.le (inv_nonneg.mpr hf1_pos.le),
        Real.mul_rpow (sub_pos.mpr hlam1).le (inv_nonneg.mpr hg2_pos.le),
        Real.inv_rpow hf1_pos.le, Real.inv_rpow hg2_pos.le] at hgm
      have htau_eq : τ' r = 2 * (lam * (lam * (f (s₁ r))⁻¹) + (1 - lam) * ((1 - lam) * (g (s₂ r))⁻¹)) := by
        dsimp only [τ']; rw [← h1lam]; ring
      have h2lam := one_le_two_mul_rpow_self hlam0 hlam1
      have hinv_nn : 0 ≤ (f (s₁ r) ^ lam)⁻¹ * (g (s₂ r) ^ (1 - lam))⁻¹ := by positivity
      calc
        (f (s₁ r) ^ lam * g (s₂ r) ^ (1 - lam))⁻¹
          = 1 * ((f (s₁ r) ^ lam)⁻¹ * (g (s₂ r) ^ (1 - lam))⁻¹) := by rw [mul_inv, one_mul]
        _ ≤ (2 * (lam ^ lam * (1 - lam) ^ (1 - lam))) *
              ((f (s₁ r) ^ lam)⁻¹ * (g (s₂ r) ^ (1 - lam))⁻¹) :=
            mul_le_mul_of_nonneg_right h2lam hinv_nn
        _ = 2 * ((lam ^ lam * (f (s₁ r) ^ lam)⁻¹) *
              ((1 - lam) ^ (1 - lam) * (g (s₂ r) ^ (1 - lam))⁻¹)) := by ring
        _ ≤ 2 * (lam * (lam * (f (s₁ r))⁻¹) + (1 - lam) * ((1 - lam) * (g (s₂ r))⁻¹)) :=
            mul_le_mul_of_nonneg_left hgm (by norm_num)
        _ = τ' r := htau_eq.symm
    have hprod_pos : 0 < f (s₁ r) ^ lam * g (s₂ r) ^ (1 - lam) := by positivity
    calc
      (1 : ℝ) = (f (s₁ r) ^ lam * g (s₂ r) ^ (1 - lam))⁻¹ * (f (s₁ r) ^ lam * g (s₂ r) ^ (1 - lam)) :=
        (inv_mul_cancel₀ hprod_pos.ne').symm
      _ ≤ τ' r * h (τ r) := mul_le_mul hderiv_lb hbm_real hprod_pos.le (hτ'_pos r hr).le
  -- 1D change of variables gives `V2 ≤ volume (Q ∩ {p.1 > 0})`, then double both sides.
  have hcov_ineq : ENNReal.ofReal V2 ≤ volume (Q ∩ {p : ℝ × H | 0 < p.1}) := by
    have hhalf_Q : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (h t) = volume (Q ∩ {p : ℝ × H | 0 < p.1}) := by
      have hm_set : MeasurableSet (Q ∩ {p : ℝ × H | 0 < p.1}) :=
        hQc.isClosed.measurableSet.inter (isOpen_lt continuous_const continuous_fst).measurableSet
      rw [Measure.volume_eq_prod, Measure.prod_apply hm_set]
      have hfib : ∀ t : ℝ, volume (Prod.mk t ⁻¹' (Q ∩ {p : ℝ × H | 0 < p.1})) =
          (Ioi (0 : ℝ)).indicator (fun s => ENNReal.ofReal (h s)) t := fun t => by
        by_cases ht : 0 < t
        · rw [indicator_of_mem ht]
          have hpre : Prod.mk t ⁻¹' (Q ∩ {p : ℝ × H | 0 < p.1}) = sliceQ t := by
            ext y; simp [sliceQ, ht]
          have hfinQ : volume (sliceQ t) ≠ ⊤ := by
            obtain ⟨RQ, hQR⟩ := hQc.isBounded.subset_closedBall ((0 : ℝ), (0 : H))
            have hsubQ : sliceQ t ⊆ closedBall (0 : H) RQ := fun y hy => by
              have h1 := hQR hy
              rw [mem_closedBall, dist_eq_norm, Prod.mk_sub_mk, sub_zero, sub_zero, Prod.norm_def] at h1
              exact mem_closedBall_zero_iff.mpr ((le_max_right _ _).trans h1)
            exact ((measure_mono hsubQ).trans_lt (isCompact_closedBall _ _).measure_lt_top).ne
          rw [hpre]; dsimp only [h]; rw [Measure.real, ENNReal.ofReal_toReal hfinQ]
        · rw [indicator_of_notMem ht]
          have hpre : Prod.mk t ⁻¹' (Q ∩ {p : ℝ × H | 0 < p.1}) = ∅ := by ext y; simp [ht]
          rw [hpre, measure_empty]
      simp_rw [hfib]
      rw [lintegral_indicator measurableSet_Ioi]
    have himg_sub : τ '' Ioo 0 V2 ⊆ Ioi (0 : ℝ) := by
      rintro _ ⟨r, hr, rfl⟩
      have hs1 : 0 < s₁ r := (hs₁_mem r hr).1
      have hs2 : 0 < s₂ r := (hs₂_mem r hr).1
      change 0 < τ r; dsimp only [τ]; positivity
    have hcov := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
      (fun r hr => (hτ_deriv r hr).hasDerivWithinAt) hτ_mono.injOn
      (fun t : ℝ => ENNReal.ofReal (h t))
    calc
      ENNReal.ofReal V2 = ∫⁻ _r in Ioo 0 V2, (1 : ℝ≥0∞) := by
          rw [setLIntegral_const, one_mul, Real.volume_Ioo, sub_zero]
      _ ≤ ∫⁻ r in Ioo 0 V2, ENNReal.ofReal |τ' r| * ENNReal.ofReal (h (τ r)) := by
          refine setLIntegral_mono' measurableSet_Ioo fun r hr => ?_
          rw [abs_of_pos (hτ'_pos r hr), ← ENNReal.ofReal_mul (hτ'_pos r hr).le, ← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (hkey_pt r hr)
      _ = ∫⁻ t in τ '' Ioo 0 V2, ENNReal.ofReal (h t) := hcov.symm
      _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (h t) := lintegral_mono_set himg_sub
      _ = volume (Q ∩ {p : ℝ × H | 0 < p.1}) := hhalf_Q
  have hvol_P_eq : volume (polarBody K₀) = ENNReal.ofReal (2 * V2) := by
    have hhyper_zero : volume ({y : E | ⟪y, u⟫ = 0}) = 0 := by
      have heq : {y : E | ⟪y, u⟫ = 0} = (orthoHyperplane u : Set E) := by
        ext y; exact mem_orthoHyperplane_iff.symm
      have hne_top : orthoHyperplane u ≠ ⊤ := by
        intro htop
        have := mem_orthoHyperplane_iff.mp (htop.symm ▸ Submodule.mem_top : u ∈ orthoHyperplane u)
        rw [real_inner_self_eq_norm_sq, hu, one_pow] at this
        exact one_ne_zero this
      rw [heq]; exact Measure.addHaar_submodule volume _ hne_top
    have hpart : polarBody K₀ =
        (polarBody K₀ ∩ {y : E | 0 < ⟪y, u⟫}) ∪ (polarBody K₀ ∩ {y : E | ⟪y, u⟫ < 0}) ∪
          (polarBody K₀ ∩ {y : E | ⟪y, u⟫ = 0}) := by
      ext y; simp only [mem_union, mem_inter_iff, mem_ofPred_eq]
      constructor
      · intro hy
        rcases lt_trichotomy ⟪y, u⟫ 0 with hlt | heq | hgt
        · exact Or.inl (Or.inr ⟨hy, hlt⟩)
        · exact Or.inr ⟨hy, heq⟩
        · exact Or.inl (Or.inl ⟨hy, hgt⟩)
      · rintro ((⟨hy, _⟩ | ⟨hy, _⟩) | ⟨hy, _⟩) <;> exact hy
    have hm_neg : MeasurableSet (polarBody K₀ ∩ {y : E | ⟪y, u⟫ < 0}) :=
      (isClosed_polarBody K₀).measurableSet.inter
        (isOpen_lt (continuous_id.inner continuous_const) continuous_const).measurableSet
    have hm_eq0 : MeasurableSet (polarBody K₀ ∩ {y : E | ⟪y, u⟫ = 0}) :=
      (isClosed_polarBody K₀).measurableSet.inter
        (isClosed_eq (continuous_id.inner continuous_const) continuous_const).measurableSet
    have hdisj1 : Disjoint (polarBody K₀ ∩ {y : E | 0 < ⟪y, u⟫})
        (polarBody K₀ ∩ {y : E | ⟪y, u⟫ < 0}) := by
      rw [Set.disjoint_left]; rintro y ⟨_, h1⟩ ⟨_, h2⟩; simp only [mem_ofPred_eq] at h1 h2; linarith
    have hdisj2 : Disjoint ((polarBody K₀ ∩ {y : E | 0 < ⟪y, u⟫}) ∪
        (polarBody K₀ ∩ {y : E | ⟪y, u⟫ < 0})) (polarBody K₀ ∩ {y : E | ⟪y, u⟫ = 0}) := by
      rw [Set.disjoint_left]; rintro y (⟨_, h1⟩ | ⟨_, h1⟩) ⟨_, h2⟩ <;>
        (simp only [mem_ofPred_eq] at h1 h2; linarith)
    rw [hpart, measure_union hdisj2 hm_eq0, measure_mono_null inter_subset_right hhyper_zero,
      add_zero, measure_union hdisj1 hm_neg]
    have hfinP : volume (polarBody K₀) ≠ ⊤ :=
      (isCompact_polarBody_of_zero_mem_interior h0K₀).measure_lt_top.ne
    have hfin1 : volume (polarBody K₀ ∩ {y : E | 0 < ⟪y, u⟫}) ≠ ⊤ :=
      ((measure_mono inter_subset_left).trans_lt (lt_top_iff_ne_top.mpr hfinP)).ne
    have hfin2 : volume (polarBody K₀ ∩ {y : E | ⟪y, u⟫ < 0}) ≠ ⊤ :=
      ((measure_mono inter_subset_left).trans_lt (lt_top_iff_ne_top.mpr hfinP)).ne
    rw [← ENNReal.ofReal_toReal hfin1, ← ENNReal.ofReal_toReal hfin2]
    change ENNReal.ofReal (volume.real (polarBody K₀ ∩ {y : E | 0 < ⟪y, u⟫})) +
      ENNReal.ofReal (volume.real (polarBody K₀ ∩ {y : E | ⟪y, u⟫ < 0})) = ENNReal.ofReal (2 * V2)
    rw [← hbal, ← hP_pos_vol, ← hPos_int, ← ENNReal.ofReal_add hV2_pos.le hV2_pos.le, two_mul]
  have hQ_sym : ∀ s : ℝ, ∀ y : H, (-s, y) ∈ Q ↔ (s, y) ∈ Q := fun s y => by
    have hKS₁_refl : (reflectBody hu KS₁ : Set E) = (KS₁ : Set E) :=
      congrArg SetLike.coe (reflectBody_bodySteinerSymmDir hu K₁)
    have hpol_refl' : ∀ z : E, z ∈ polarBody (KS₁ : Set E) ↔
        reflectHyperplane hu z ∈ polarBody (KS₁ : Set E) := fun z => by
      constructor
      · intro hz x hx
        have hrx : reflectHyperplane hu x ∈ (KS₁ : Set E) := by
          rw [← hKS₁_refl, coe_reflectBody]; exact ⟨x, hx, rfl⟩
        rw [← inner_reflectHyperplane]; exact hz _ hrx
      · intro hrz x hx
        have hrx : reflectHyperplane hu x ∈ (KS₁ : Set E) := by
          rw [← hKS₁_refl, coe_reflectBody]; exact ⟨x, hx, rfl⟩
        have := hrz (reflectHyperplane hu x) hrx
        rwa [inner_reflectHyperplane, reflectHyperplane_involutive] at this
    constructor
    · rintro ⟨z, hz, hzp⟩
      refine ⟨reflectHyperplane hu z, (hpol_refl' z).mp hz, ?_⟩
      rw [orthoSplitProd_reflectHyperplane, hzp]; simp
    · rintro ⟨z, hz, hzp⟩
      refine ⟨reflectHyperplane hu z, (hpol_refl' z).mp hz, ?_⟩
      rw [orthoSplitProd_reflectHyperplane, hzp]
  have hvol_Q_ge : 2 * volume (Q ∩ {p : ℝ × H | 0 < p.1}) ≤ volume (polarBody (KS₁ : Set E)) := by
    have hQ_neg_eq : volume (Q ∩ {p : ℝ × H | p.1 < 0}) = volume (Q ∩ {p : ℝ × H | 0 < p.1}) := by
      have hpre : swapH ⁻¹' (Q ∩ {p : ℝ × H | 0 < p.1}) = Q ∩ {p : ℝ × H | p.1 < 0} := by
        ext ⟨s, y⟩; simp [swapH, hQ_sym]
      have hm_pos : MeasurableSet (Q ∩ {p : ℝ × H | 0 < p.1}) :=
        hQc.isClosed.measurableSet.inter (isOpen_lt continuous_const continuous_fst).measurableSet
      rw [← hpre, hmp_swap.measure_preimage hm_pos.nullMeasurableSet]
    have hdisj : Disjoint (Q ∩ {p : ℝ × H | 0 < p.1}) (Q ∩ {p : ℝ × H | p.1 < 0}) := by
      rw [Set.disjoint_left]; rintro p ⟨_, h1⟩ ⟨_, h2⟩; simp only [mem_ofPred_eq] at h1 h2; linarith
    have hm_neg : MeasurableSet (Q ∩ {p : ℝ × H | p.1 < 0}) :=
      hQc.isClosed.measurableSet.inter (isOpen_lt continuous_fst continuous_const).measurableSet
    have hpreQ : Φ ⁻¹' Q = polarBody (KS₁ : Set E) := Set.preimage_image_eq _ Φ.injective
    calc
      2 * volume (Q ∩ {p : ℝ × H | 0 < p.1})
        = volume (Q ∩ {p : ℝ × H | 0 < p.1}) + volume (Q ∩ {p : ℝ × H | p.1 < 0}) := by
            rw [hQ_neg_eq, two_mul]
      _ = volume ((Q ∩ {p : ℝ × H | 0 < p.1}) ∪ (Q ∩ {p : ℝ × H | p.1 < 0})) :=
            (measure_union hdisj hm_neg).symm
      _ ≤ volume Q := measure_mono (union_subset inter_subset_left inter_subset_left)
      _ = volume (polarBody (KS₁ : Set E)) := by
            rw [← hpreQ, hmp.measure_preimage hQc.isClosed.measurableSet.nullMeasurableSet]
  calc
    volume (polarBody K₀) = ENNReal.ofReal (2 * V2) := hvol_P_eq
    _ = 2 * ENNReal.ofReal V2 := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    _ ≤ 2 * volume (Q ∩ {p : ℝ × H | 0 < p.1}) := by gcongr
    _ ≤ volume (polarBody (KS₁ : Set E)) := hvol_Q_ge

/-- **Meyer–Pajor (1990) Steiner Symmetrization Inequality:**
in dimension `d ≥ 2`, Steiner symmetrization in any unit direction `u` does not decrease the
Santaló Mahler volume:
$$\mathcal{P}^*(K) \le \mathcal{P}^*(S_u K).$$ -/
theorem santaloMahlerVolume_le_bodySteinerSymmDir
    {u : E} (hu : ‖u‖ = 1) (hd2 : 2 ≤ Module.finrank ℝ E)
    (K : ConvexBody E) (hne : (interior (K : Set E)).Nonempty) :
    santaloMahlerVolume (volume : Measure E) (K : Set E) ≤
      santaloMahlerVolume (volume : Measure E) (bodySteinerSymmDir hu K : Set E) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
  let KS : ConvexBody E := bodySteinerSymmDir hu K
  have hKS_ne : (interior (KS : Set E)).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hvol0 : volume (KS : Set E) = 0 := by
      have hfr : (KS : Set E) = frontier (KS : Set E) := by
        rw [frontier, KS.isClosed.closure_eq, hemp, sdiff_empty]
      rw [hfr]; exact KS.convex.addHaar_frontier volume
    have hvol_pos : 0 < volume (K : Set E) :=
      (isOpen_interior.measure_pos volume hne).trans_le (measure_mono interior_subset)
    rw [show KS = bodySteinerSymmDir hu K from rfl, volume_bodySteinerSymmDir] at hvol0
    exact hvol_pos.ne' hvol0
  obtain ⟨z₀, hz₀_int, hz₀_orth, hz₀_mahler_eq⟩ :=
    exists_santaloPoint_orth hu KS hKS_ne (reflectBody_bodySteinerSymmDir hu K)
  let K₁ : ConvexBody E := K + bodySingleton (-z₀)
  let KS₁ : ConvexBody E := bodySteinerSymmDir hu K₁
  have hKS₁_eq : KS₁ = KS + bodySingleton (-z₀) :=
    bodySteinerSymmDir_translate_orth hu K (by rw [inner_neg_left, hz₀_orth, neg_zero])
  have h0S₁ : (0 : E) ∈ interior (KS₁ : Set E) := by
    rw [hKS₁_eq, coe_translate_neg]; exact zero_mem_interior_translate_neg hz₀_int
  have hK₁_sant : santaloMahlerVolume (volume : Measure E) (K₁ : Set E) =
      santaloMahlerVolume (volume : Measure E) (K : Set E) := by
    have hcoe : (K₁ : Set E) = (fun x : E => x + (-z₀)) '' (K : Set E) := by
      rw [coe_translate_neg]; ext y; simp [sub_eq_add_neg]
    rw [hcoe, santaloMahlerVolume_translate]
  have hKS₁_mahler : mahlerVolume (volume : Measure E) (KS₁ : Set E) =
      santaloMahlerVolume (volume : Measure E) (KS : Set E) := by
    rw [← hz₀_mahler_eq, mahlerVolumeAt, ← coe_translate_neg, ← hKS₁_eq]
  rw [← hK₁_sant, ← hKS₁_mahler]
  obtain ⟨t₀, ht₀_lo, ht₀_hi, hbal⟩ := exists_balanced_polar_slice_shift hu hd2 K₁ h0S₁
  have hfib₁ := mem_interior_along_fiber_of_zero_mem_interior_steinerSymmDir hu K₁ h0S₁
  have ht₀_int : t₀ • u ∈ interior (K₁ : Set E) := hfib₁.2 t₀ ht₀_lo ht₀_hi
  let K₀ : Set E := (fun x : E => x - t₀ • u) '' (K₁ : Set E)
  have hpol_le : volume (polarBody K₀) ≤ volume (polarBody (KS₁ : Set E)) :=
    meyer_pajor_polar_volume_le hu hd2 K₁ ht₀_int h0S₁ hbal
  have hvol_K₀ : volume K₀ = volume (KS₁ : Set E) := by
    have h1 : volume K₀ = volume (K₁ : Set E) := by
      have hpre : K₀ = (fun x : E => t₀ • u + x) ⁻¹' (K₁ : Set E) := by
        ext y; simp only [K₀, mem_image, mem_preimage]
        exact ⟨fun ⟨x, hx, hxy⟩ => by rw [← hxy]; simpa [add_sub_cancel] using hx,
          fun hy => ⟨t₀ • u + y, hy, by abel⟩⟩
      rw [hpre, measure_preimage_add]
    rw [h1, show KS₁ = bodySteinerSymmDir hu K₁ from rfl, volume_bodySteinerSymmDir]
  calc
    santaloMahlerVolume (volume : Measure E) (K₁ : Set E)
      ≤ mahlerVolumeAt (volume : Measure E) (K₁ : Set E) (t₀ • u) :=
          santaloMahlerVolume_le_mahlerVolumeAt volume ht₀_int
    _ = volume K₀ * volume (polarBody K₀) := rfl
    _ ≤ volume (KS₁ : Set E) * volume (polarBody (KS₁ : Set E)) := by
          rw [hvol_K₀]; exact mul_le_mul' le_rfl hpol_le

end MeyerPajor

/-! ### 5. The Blaschke–Santaló Inequality -/

section BlaschkeSantalo

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **The Blaschke–Santaló Inequality (General Convex Bodies):**
for every convex body `K : ConvexBody E` with nonempty interior in any nontrivial
finite-dimensional real inner product space `E`,
$$\mathcal{P}^*(K) = \inf_{z \in \mathrm{int}(K)} \mathrm{vol}(K)\,\mathrm{vol}((K - z)^\circ)
  \le \mathrm{vol}(\overline{B}(0, 1))^2.$$ -/
theorem blaschke_santalo [Nontrivial E] (K : ConvexBody E)
    (hne : (interior (K : Set E)).Nonempty) :
    santaloMahlerVolume (volume : Measure E) (K : Set E) ≤
      volume (closedBall (0 : E) 1) ^ 2 := by
  set d : ℕ := Module.finrank ℝ E
  have hd_pos : 1 ≤ d := Module.finrank_pos
  -- Handle `d = 1` directly: every 1D compact convex body with nonempty interior is a closed ball!
  by_cases hd1 : d = 1
  · let b : OrthonormalBasis (Fin 1) ℝ E :=
      (stdOrthonormalBasis ℝ E).reindex (finCongr hd1)
    let e : E ≃ₗᵢ[ℝ] ℝ :=
      { toFun := fun x => (b.repr x).ofLp 0
        invFun := fun t => t • b 0
        left_inv := fun x => by
          have h := b.sum_repr' x
          simp only [Fin.sum_univ_one] at h
          simpa [OrthonormalBasis.repr_apply_apply] using h
        right_inv := fun t => by
          simp [map_smul, b.repr_self]
        map_add' := fun x y => by simp
        map_smul' := fun c x => by simp
        norm_map' := fun x => by
          have h := b.repr.norm_map x
          rw [EuclideanSpace.norm_eq] at h
          simp only [Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs] at h
          simpa [Real.norm_eq_abs] using h }
    let I : Set ℝ := e '' (K : Set E)
    have hIc : IsCompact I := K.isCompact.image e.continuous
    have hIconv : Convex ℝ I := K.convex.linear_image e.toLinearMap
    have hIne : I.Nonempty := K.nonempty.image e
    set a := sInf I
    set c := sSup I
    have hI_eq : I = Icc a c := by
      apply Subset.antisymm
      · exact fun t ht => ⟨csInf_le hIc.bddBelow ht, le_csSup hIc.bddAbove ht⟩
      · exact hIconv.ordConnected.out (hIc.sInf_mem hIne) (hIc.sSup_mem hIne)
    have hI_int_ne : (interior I).Nonempty := by
      rw [show I = e.toHomeomorph '' (K : Set E) from rfl, ← e.toHomeomorph.image_interior]
      exact hne.image _
    have hac : a < c := by
      rw [hI_eq, interior_Icc] at hI_int_ne
      obtain ⟨t, ht1, ht2⟩ := hI_int_ne
      linarith
    set mid : ℝ := (a + c) / 2
    set rad : ℝ := (c - a) / 2
    have hrad_pos : 0 < rad := by dsimp only [rad]; linarith
    set z : E := e.symm mid
    have hz_int : z ∈ interior (K : Set E) := by
      have hmid_int : mid ∈ interior I := by
        rw [hI_eq, interior_Icc]; dsimp only [mid]; constructor <;> linarith
      rw [show I = e.toHomeomorph '' (K : Set E) from rfl, ← e.toHomeomorph.image_interior] at hmid_int
      rcases hmid_int with ⟨x, hx, hxe⟩
      have hxz : x = z := by
        dsimp only [z]
        rw [← hxe]
        exact (e.symm_apply_apply x).symm
      rwa [← hxz]
    have hshift : (fun x : E => x - z) '' (K : Set E) = closedBall (0 : E) rad := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [mem_closedBall_zero_iff, ← e.norm_map, map_sub, e.apply_symm_apply, Real.norm_eq_abs, abs_le]
        have hxI : e x ∈ Icc a c := hI_eq ▸ ⟨x, hx, rfl⟩
        dsimp only [mid, rad]; constructor <;> linarith [hxI.1, hxI.2]
      · intro hy
        rw [mem_closedBall_zero_iff, ← e.norm_map, Real.norm_eq_abs, abs_le] at hy
        have hmemI : e y + mid ∈ I := by
          rw [hI_eq]; dsimp only [mid, rad] at hy ⊢; constructor <;> linarith [hy.1, hy.2]
        rcases hmemI with ⟨x, hxK, hxe⟩
        refine ⟨x, hxK, e.injective ?_⟩
        rw [map_sub, e.apply_symm_apply, hxe, add_sub_cancel_right]
    have hAt : mahlerVolumeAt (volume : Measure E) (K : Set E) z = volume (closedBall (0 : E) 1) ^ 2 := by
      rw [mahlerVolumeAt, hshift]
      have hsmul : closedBall (0 : E) rad = rad • closedBall (0 : E) 1 := by
        ext y; simp only [mem_closedBall_zero_iff, mem_smul_set]
        constructor
        · intro hy
          refine ⟨rad⁻¹ • y, ?_, by rw [smul_smul, mul_inv_cancel₀ hrad_pos.ne', one_smul]⟩
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hrad_pos),
            inv_mul_le_iff₀ hrad_pos, mul_one]
          exact hy
        · rintro ⟨w, hw, rfl⟩
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrad_pos]; nlinarith
      rw [hsmul, mahlerVolume_smul volume hrad_pos.ne', mahlerVolume, polarBody_closedBall one_pos,
        inv_one, sq]
    exact (santaloMahlerVolume_le_mahlerVolumeAt volume hz_int).trans_eq hAt
  -- Main case `d ≥ 2`: reduce to John's position inside the compact family `𝒞` and optimize!
  have hd2 : 2 ≤ d := by omega
  let 𝒞 : Set (ConvexBody E) :=
    {L : ConvexBody E | closedBall (0 : E) 1 ⊆ (L : Set E) ∧ (L : Set E) ⊆ closedBall (0 : E) (d : ℝ)}
  -- 1. Show `𝒞` is nonempty and compact in the Hausdorff metric.
  have hB1_mem : bodyClosedBall (0 : E) zero_le_one ∈ 𝒞 := by
    refine ⟨by rw [coe_bodyClosedBall], ?_⟩
    rw [coe_bodyClosedBall]
    exact closedBall_subset_closedBall (by exact_mod_cast hd_pos)
  have h𝒞_compact : IsCompact 𝒞 := by
    have hsub_closed : IsClosed {L : ConvexBody E | closedBall (0 : E) 1 ⊆ (L : Set E)} := by
      have heq : {L : ConvexBody E | closedBall (0 : E) 1 ⊆ (L : Set E)} =
          ⋂ u : sphere (0 : E) 1, {L : ConvexBody E | 1 ≤ supportFn L u.1} := by
        ext L
        simp only [mem_ofPred_eq, mem_iInter]
        rw [← coe_bodyClosedBall (0 : E) zero_le_one, ← supportFn_le_iff_subset]
        constructor
        · intro h u
          have := h u.1
          rwa [supportFn_bodyClosedBall, inner_zero_left, zero_add, one_mul,
            mem_sphere_zero_iff_norm.mp u.2] at this
        · intro h v
          rw [supportFn_bodyClosedBall, inner_zero_left, zero_add, one_mul]
          by_cases hv : v = 0
          · subst hv; simp
          · have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
            let u : sphere (0 : E) 1 := ⟨‖v‖⁻¹ • v, by
              rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
                abs_of_pos (inv_pos.mpr hv_pos), inv_mul_cancel₀ hv_pos.ne']⟩
            have h1 := h u
            have hv_eq : v = ‖v‖ • u.1 := by
              dsimp only [u]; rw [smul_smul, mul_inv_cancel₀ hv_pos.ne', one_smul]
            rw [hv_eq, supportFn_smul L hv_pos.le, norm_smul, Real.norm_eq_abs, abs_of_pos hv_pos,
              mem_sphere_zero_iff_norm.mp u.2, mul_one]
            nlinarith
      rw [heq]
      refine isClosed_iInter fun u => isClosed_le continuous_const ?_
      refine (LipschitzWith.of_dist_le_mul (K := 1) fun L₁ L₂ => ?_).continuous
      have hmem : u.1 ∈ closedBall (0 : E) 1 := by
        rw [mem_closedBall_zero_iff, mem_sphere_zero_iff_norm.mp u.2]
      have h1 := BoundedContinuousFunction.dist_coe_le_dist
        (f := supportFnOnBall L₁) (g := supportFnOnBall L₂) ⟨u.1, hmem⟩
      rw [← dist_eq_dist_supportFnOnBall] at h1
      simpa [supportFnOnBall_apply] using h1
    exact (isCompact_subset_closedBall (E := E) (d : ℝ)).of_isClosed_subset
      (hsub_closed.inter (isCompact_subset_closedBall (E := E) (d : ℝ)).isClosed)
      (fun _ h => h.2)
  have h𝒞_int_ne : ∀ L ∈ 𝒞, (interior (L : Set E)).Nonempty := fun L hL =>
    ⟨0, mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (closedBall_mem_nhds 0 zero_lt_one) hL.1)⟩
  -- 2. Maximize the upper semicontinuous function `santaloMahlerVolume` on compact `𝒞`.
  have husc : UpperSemicontinuousOn
      (fun L : ConvexBody E => santaloMahlerVolume (volume : Measure E) (L : Set E)) 𝒞 :=
    upperSemicontinuousOn_santaloMahlerVolume.mono h𝒞_int_ne
  obtain ⟨K_max, hK_max_𝒞, hK_max⟩ := husc.exists_isMaxOn ⟨_, hB1_mem⟩ h𝒞_compact
  set S_max : ℝ≥0∞ := santaloMahlerVolume (volume : Measure E) (K_max : Set E)
  -- 3. The maximizer set `ℳ := {L ∈ 𝒞 | santaloMahlerVolume L = S_max}` is nonempty and compact.
  let ℳ : Set (ConvexBody E) := {L ∈ 𝒞 | S_max ≤ santaloMahlerVolume (volume : Measure E) (L : Set E)}
  have hℳ_compact : IsCompact ℳ := by
    -- By upper semicontinuity, `{L ∈ 𝒞 | santaloMahlerVolume L < S_max}` is open in `𝒞`,
    -- so its complement `ℳ` in `𝒞` is closed in `𝒞`, hence compact!
    rw [isCompact_iff_isSeqCompact]
    intro Ln hLn
    obtain ⟨L₀, hL₀𝒞, φ, hφ, htend⟩ := h𝒞_compact.isSeqCompact (fun n => (hLn n).1)
    refine ⟨L₀, ⟨hL₀𝒞, ?_⟩, φ, hφ, htend⟩
    by_contra hlt
    push Not at hlt
    have hev := husc L₀ hL₀𝒞 S_max hlt
    have htend_within : Tendsto (Ln ∘ φ) atTop (𝓝[𝒞] L₀) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ htend
        (Eventually.of_forall fun n => (hLn (φ n)).1)
    have hev_n := htend_within.eventually hev
    obtain ⟨n, hn⟩ := hev_n.exists
    exact not_lt.mpr (hLn (φ n)).2 hn
  -- 4. Minimize `secondMoment` on the nonempty compact set `ℳ` to obtain `K₀`.
  obtain ⟨K₀, hK₀ℳ, hK₀_min⟩ :=
    hℳ_compact.exists_isMinOn ⟨K_max, hK_max_𝒞, le_rfl⟩ continuous_secondMoment.continuousOn
  -- 5. Show `reflectBody hu K₀ = K₀` for EVERY unit vector `u`.
  have hK₀_refl : ∀ {u : E} (hu : ‖u‖ = 1), reflectBody hu K₀ = K₀ := fun {u} hu => by
    by_contra hnsym
    let KS₀ : ConvexBody E := bodySteinerSymmDir hu K₀
    have hKS₀_𝒞 : KS₀ ∈ 𝒞 := by
      refine ⟨?_, ?_⟩
      · have h1 := bodySteinerSymmDir_mono hu (K := bodyClosedBall (0 : E) zero_le_one) (L := K₀)
          (by rw [coe_bodyClosedBall]; exact hK₀ℳ.1.1)
        rwa [bodySteinerSymmDir_bodyClosedBall hu zero_le_one, coe_bodyClosedBall] at h1
      · have h1 := bodySteinerSymmDir_mono hu (K := K₀) (L := bodyClosedBall (0 : E) (Nat.cast_nonneg d))
          (by rw [coe_bodyClosedBall]; exact hK₀ℳ.1.2)
        rwa [bodySteinerSymmDir_bodyClosedBall hu (Nat.cast_nonneg d), coe_bodyClosedBall] at h1
    have hKS₀_ℳ : KS₀ ∈ ℳ :=
      ⟨hKS₀_𝒞, hK₀ℳ.2.trans (santaloMahlerVolume_le_bodySteinerSymmDir hu hd2 K₀ (h𝒞_int_ne K₀ hK₀ℳ.1))⟩
    have hsec_le : secondMoment K₀ ≤ secondMoment KS₀ := hK₀_min hKS₀_ℳ
    have hsec_lt : secondMoment KS₀ < secondMoment K₀ :=
      secondMoment_bodySteinerSymmDir_lt hu (h𝒞_int_ne K₀ hK₀ℳ.1) hnsym
    linarith
  -- 6. Reflection invariance across every hyperplane forces `K₀ = bodyClosedBall 0 R`!
  obtain ⟨u₀, hu₀⟩ : ∃ u : E, ‖u‖ = 1 := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    refine ⟨‖x‖⁻¹ • x, ?_⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hx)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  set R : ℝ := supportFn K₀ u₀
  have hR_ge1 : 1 ≤ R := by
    have h1 := supportFn_mono (K := bodyClosedBall (0 : E) zero_le_one) (L := K₀)
      (by rw [coe_bodyClosedBall]; exact hK₀ℳ.1.1) u₀
    rwa [supportFn_bodyClosedBall, inner_zero_left, zero_add, one_mul, hu₀] at h1
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one hR_ge1
  have hK₀_eq_ball : K₀ = bodyClosedBall (0 : E) hR_pos.le := by
    apply supportFn_injective
    ext v
    rw [supportFn_bodyClosedBall, inner_zero_left, zero_add]
    by_cases hv : v = 0
    · subst hv; simp
    · have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
      set w : E := ‖v‖⁻¹ • v
      have hw : ‖w‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hv_pos), inv_mul_cancel₀ hv_pos.ne']
      have hsup_w : supportFn K₀ w = R := by
        by_cases hwu : w = u₀
        · rw [hwu]
        · have hne_wu : w - u₀ ≠ 0 := sub_ne_zero.mpr hwu
          have hnorm_pos : 0 < ‖w - u₀‖ := norm_pos_iff.mpr hne_wu
          set z : E := ‖w - u₀‖⁻¹ • (w - u₀)
          have hz : ‖z‖ = 1 := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm_pos),
              inv_mul_cancel₀ hnorm_pos.ne']
          have hrefl_w : reflectHyperplane hz w = u₀ := by
            rw [reflectHyperplane_apply]
            have hinner : 2 * ⟪w, w - u₀⟫ = ‖w - u₀‖ ^ 2 := by
              rw [norm_sub_sq_real, hw, hu₀, inner_sub_right, real_inner_self_eq_norm_sq, hw]; ring
            have hcoeff : 2 * ⟪w, z⟫ = ‖w - u₀‖ := by
              dsimp only [z]; rw [inner_smul_right, ← mul_assoc, mul_comm 2 ‖w - u₀‖⁻¹, mul_assoc, hinner]
              field_simp [hnorm_pos.ne']
            rw [hcoeff]; dsimp only [z]
            rw [smul_smul, mul_inv_cancel₀ hnorm_pos.ne', one_smul, sub_sub_cancel]
          calc
            supportFn K₀ w = supportFn (reflectBody hz K₀) w := by rw [hK₀_refl hz]
            _ = supportFn K₀ (reflectHyperplane hz w) := supportFn_reflectBody hz K₀ w
            _ = R := by rw [hrefl_w]
      have hv_eq : v = ‖v‖ • w := by
        dsimp only [w]; rw [smul_smul, mul_inv_cancel₀ hv_pos.ne', one_smul]
      rw [hv_eq, supportFn_smul K₀ hv_pos.le, hsup_w, norm_smul, Real.norm_eq_abs,
        abs_of_pos hv_pos, hw, mul_one, mul_comm]
  -- 7. Compute `S_max ≤ volume (closedBall 0 1) ^ 2` on `K₀ = bodyClosedBall 0 R`.
  have hS_max_le : S_max ≤ volume (closedBall (0 : E) 1) ^ 2 := by
    have hsmul : (K₀ : Set E) = R • closedBall (0 : E) 1 := by
      rw [hK₀_eq_ball, coe_bodyClosedBall]
      ext y; simp only [mem_closedBall_zero_iff, mem_smul_set]
      constructor
      · intro hy
        refine ⟨R⁻¹ • y, ?_, by rw [smul_smul, mul_inv_cancel₀ hR_pos.ne', one_smul]⟩
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR_pos),
          inv_mul_le_iff₀ hR_pos, mul_one]
        exact hy
      · rintro ⟨w, hw, rfl⟩
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR_pos]; nlinarith
    have h0K₀ : (0 : E) ∈ interior (K₀ : Set E) :=
      mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (closedBall_mem_nhds 0 zero_lt_one) hK₀ℳ.1.1)
    calc
      S_max ≤ santaloMahlerVolume (volume : Measure E) (K₀ : Set E) := hK₀ℳ.2
      _ ≤ mahlerVolume (volume : Measure E) (K₀ : Set E) :=
          santaloMahlerVolume_le_mahlerVolume volume h0K₀
      _ = volume (closedBall (0 : E) 1) ^ 2 := by
          rw [hsmul, mahlerVolume_smul volume hR_pos.ne', mahlerVolume, polarBody_closedBall one_pos,
            inv_one, sq]
  -- 8. Transform arbitrary `K` to John's position inside `𝒞` via `exists_affineEquiv_isJohnPosition`.
  obtain ⟨A, hJ⟩ := exists_affineEquiv_isJohnPosition K hne
  have hA_cont : Continuous A := by
    have heq : (A : E → E) = fun x => A.linear x + A 0 := funext fun x => by
      have h := A.map_vadd 0 x
      simpa [vadd_eq_add] using h
    rw [heq]
    exact A.linear.toContinuousLinearEquiv.continuous.add continuous_const
  let KJ : ConvexBody E :=
    { carrier := A '' (K : Set E)
      convex' := K.convex.affine_image A.toAffineMap
      isCompact' := K.isCompact.image hA_cont
      nonempty' := K.nonempty.image A }
  have hKJ_𝒞 : KJ ∈ 𝒞 := by
    refine ⟨hJ.1, ?_⟩
    have hsub := subset_finrank_smul_of_john_position KJ hJ
    refine hsub.trans ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg d)]
    have hw1 : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.mp hw
    nlinarith
  calc
    santaloMahlerVolume (volume : Measure E) (K : Set E)
      = santaloMahlerVolume (volume : Measure E) (KJ : Set E) :=
          (santaloMahlerVolume_affineEquiv volume A (K : Set E)).symm
    _ ≤ S_max := hK_max hKJ_𝒞
    _ ≤ volume (closedBall (0 : E) 1) ^ 2 := hS_max_le

/-- **The Blaschke–Santaló Inequality (Origin-Symmetric Convex Bodies):**
for every origin-symmetric convex body `K : ConvexBody E` with `0 ∈ interior K`,
$$\mathrm{vol}(K)\,\mathrm{vol}(K^\circ) \le \mathrm{vol}(\overline{B}(0, 1))^2.$$ -/
theorem blaschke_santalo_symmetric [Nontrivial E] (K : ConvexBody E)
    (hsym : IsOriginSymmetric (K : Set E)) (h0 : (0 : E) ∈ interior (K : Set E)) :
    mahlerVolume (volume : Measure E) (K : Set E) ≤
      volume (closedBall (0 : E) 1) ^ 2 := by
  rw [mahlerVolume_eq_santaloMahlerVolume_of_isOriginSymmetric K hsym h0]
  exact blaschke_santalo K ⟨0, h0⟩

/-- Real-valued **Blaschke–Santaló Inequality** at a Santaló point `z ∈ interior K`. -/
theorem blaschke_santalo_real [Nontrivial E] (K : ConvexBody E)
    (hne : (interior (K : Set E)).Nonempty) :
    ∃ z ∈ interior (K : Set E),
      volume.real (K : Set E) * volume.real (polarBody ((fun x : E => x - z) '' (K : Set E))) ≤
        volume.real (closedBall (0 : E) 1) ^ 2 := by
  obtain ⟨z, hz, hmin⟩ := exists_santaloPoint K hne
  refine ⟨z, hz, ?_⟩
  have hle : mahlerVolumeAt (volume : Measure E) (K : Set E) z ≤
      volume (closedBall (0 : E) 1) ^ 2 := hmin.trans_le (blaschke_santalo K hne)
  have hvol_eq : volume ((fun x : E => x - z) '' (K : Set E)) = volume (K : Set E) := by
    have hpre : (fun x : E => x - z) '' (K : Set E) = (fun x : E => z + x) ⁻¹' (K : Set E) := by
      ext y; simp only [mem_image, mem_preimage]
      exact ⟨fun ⟨x, hx, hxy⟩ => by rw [← hxy]; simpa [add_sub_cancel] using hx,
        fun hy => ⟨z + y, hy, by abel⟩⟩
    rw [hpre, measure_preimage_add]
  have hfinB : volume (closedBall (0 : E) 1) ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top (isCompact_closedBall (0 : E) 1).measure_lt_top.ne
  have htoReal := ENNReal.toReal_mono hfinB hle
  unfold mahlerVolumeAt mahlerVolume at htoReal
  rw [hvol_eq, ENNReal.toReal_mul, ENNReal.toReal_pow] at htoReal
  exact htoReal

/-- Real-valued **Blaschke–Santaló Inequality** for origin-symmetric convex bodies. -/
theorem blaschke_santalo_symmetric_real [Nontrivial E] (K : ConvexBody E)
    (hsym : IsOriginSymmetric (K : Set E)) (h0 : (0 : E) ∈ interior (K : Set E)) :
    volume.real (K : Set E) * volume.real (polarBody (K : Set E)) ≤
      volume.real (closedBall (0 : E) 1) ^ 2 := by
  have hle := blaschke_santalo_symmetric K hsym h0
  have hfinB : volume (closedBall (0 : E) 1) ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top (isCompact_closedBall (0 : E) 1).measure_lt_top.ne
  have htoReal := ENNReal.toReal_mono hfinB hle
  unfold mahlerVolume at htoReal
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow] at htoReal
  exact htoReal

end BlaschkeSantalo

/-! ### 6. Urysohn's Inequality -/

section Urysohn

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Urysohn's Inequality:**
for EVERY convex body `K : ConvexBody E` (with or without interior points) in any nontrivial
finite-dimensional real inner product space `E` of dimension `d = finrank ℝ E ≥ 1`,
$$\left(\frac{\mathrm{vol}(K)}{\mathrm{vol}(\overline{B}(0, 1))}\right)^{1/d} \le w(K),$$
where `w(K) = meanWidth K` is the half mean breadth (`w(B(c, r)) = r`). -/
theorem urysohn_inequality [Nontrivial E] (K : ConvexBody E) :
    (volume.real (K : Set E) / volume.real (closedBall (0 : E) 1)) ^
        (1 / (Module.finrank ℝ E : ℝ)) ≤
      meanWidth K := by
  by_cases hne : (interior (K : Set E)).Nonempty
  · obtain ⟨z, hz, hsant⟩ := blaschke_santalo_real K hne
    exact urysohn_of_santalo_at K hz hsant
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have hvol0 : volume (K : Set E) = 0 := by
      have hfr : (K : Set E) = frontier (K : Set E) := by
        rw [frontier, K.isClosed.closure_eq, hne, sdiff_empty]
      rw [hfr]; exact K.convex.addHaar_frontier volume
    have hd_pos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
    rw [Measure.real, hvol0, ENNReal.toReal_zero, zero_div,
      Real.zero_rpow (one_div_ne_zero hd_pos.ne')]
    exact meanWidth_nonneg K

end Urysohn

end

end ConvexGeom

