/-
Copyright (c) 2026 Yegor Gorodzha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yegor Gorodzha
-/
module

public import ConvexGeom.Volume.BrunnMinkowski
public import ConvexGeom.Metric.SupportFunction

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Minkowski and Steiner Symmetrization

Hyperplane reflection, Minkowski and central symmetrization, and Steiner symmetrization on `ℝ × E`
(Klartag, Lecture 2; Schneider, *Convex Bodies*, §10.3):

1. **Hyperplane reflection & Minkowski / central symmetrization** (finite-dimensional inner product space `E`):
   - `reflectHyperplane`, `reflectBody`, `minkowskiSymm`, `centralSymm`.
   - Support formulas, reflection invariance, volume non-decrease (`volume_le_volume_minkowskiSymm`,
     `volume_le_volume_centralSymm`), and diameter non-increase (`diam_minkowskiSymm_le`).
2. **Steiner symmetrization** (along the first coordinate on `ℝ × E`):
   - `steinerSymm`: interval-hull symmetrization, replacing each nonempty line fiber `steinerFiber K y`
     by `[-(b - a)/2, (b - a)/2] × {y}` (`a = sInf`, `b = sSup`). Agrees with measure-theoretic
     Steiner symmetrization on compact convex sets; `bodySteinerSymm` packages it on `ConvexBody (ℝ × E)`.
   - `steinerSymm_symm`, `steinerSymm_mono`, `convex_steinerSymm`, `isCompact_steinerSymm`,
     `volume_steinerSymm`, `volume_bodySteinerSymm`, `steinerSymm_dist_le_diam` (Euclidean squared distance;
     `ℝ × E` itself carries Mathlib's product max-norm).
-/

open MeasureTheory Set
open scoped RealInnerProductSpace Pointwise ENNReal

namespace ConvexGeom

public section

/-! ### 1. Hyperplane Reflection and Minkowski Symmetrization -/

section MinkowskiSymm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Orthogonal reflection across the hyperplane `u⊥` for a unit vector `u` (`‖u‖ = 1`):
`reflectHyperplane hu x = x - (2 * ⟪x, u⟫) • u`. -/
noncomputable def reflectHyperplane {u : E} (hu : ‖u‖ = 1) : E ≃ₗᵢ[ℝ] E :=
  have hinvol : ∀ x : E, (x - (2 * ⟪x, u⟫) • u) - (2 * ⟪x - (2 * ⟪x, u⟫) • u, u⟫) • u = x := by
    intro x
    have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
    rw [inner_sub_left, inner_smul_left, RCLike.conj_to_real, huu, mul_one]
    have hcoeff : (2 * (⟪x, u⟫ - 2 * ⟪x, u⟫)) = -(2 * ⟪x, u⟫) := by ring
    rw [hcoeff, neg_smul, sub_neg_eq_add, sub_add_cancel]
  { toFun := fun x => x - (2 * ⟪x, u⟫) • u
    invFun := fun x => x - (2 * ⟪x, u⟫) • u
    left_inv := hinvol
    right_inv := hinvol
    map_add' := fun x y => by
      rw [inner_add_left, mul_add, add_smul]
      abel
    map_smul' := fun c x => by
      simp only [inner_smul_left, RCLike.conj_to_real, RingHom.id_apply, smul_sub, smul_smul]
      congr 2; ring
    norm_map' := fun x => by
      have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
      have hsq : ‖x - (2 * ⟪x, u⟫) • u‖ ^ 2 = ‖x‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
          inner_sub_left, inner_sub_right, inner_sub_right,
          inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
          RCLike.conj_to_real, huu, real_inner_comm u x]
        ring
      have h1 : 0 ≤ ‖x - (2 * ⟪x, u⟫) • u‖ := norm_nonneg _
      have h2 : 0 ≤ ‖x‖ := norm_nonneg _
      change ‖x - (2 * ⟪x, u⟫) • u‖ = ‖x‖
      nlinarith }

@[simp]
lemma reflectHyperplane_apply {u : E} (hu : ‖u‖ = 1) (x : E) :
    reflectHyperplane hu x = x - (2 * ⟪x, u⟫) • u := by
  simp [reflectHyperplane]

lemma reflectHyperplane_involutive {u : E} (hu : ‖u‖ = 1) (x : E) :
    reflectHyperplane hu (reflectHyperplane hu x) = x :=
  (reflectHyperplane hu).left_inv x

@[simp]
lemma reflectHyperplane_symm {u : E} (hu : ‖u‖ = 1) :
    (reflectHyperplane hu).symm = reflectHyperplane hu := by
  ext x
  exact (reflectHyperplane hu).symm_apply_eq.mpr (reflectHyperplane_involutive hu x).symm

lemma inner_reflectHyperplane {u : E} (hu : ‖u‖ = 1) (x y : E) :
    ⟪reflectHyperplane hu x, y⟫ = ⟪x, reflectHyperplane hu y⟫ := by
  have h := (reflectHyperplane hu).inner_map_map x (reflectHyperplane hu y)
  rwa [reflectHyperplane_involutive] at h

/-- Image of a convex body `K` under hyperplane reflection `reflectHyperplane hu`,
defined via generic linear transport `mapLinear`. -/
noncomputable def reflectBody {u : E} (hu : ‖u‖ = 1) (K : ConvexBody E) : ConvexBody E :=
  mapLinear (reflectHyperplane hu).toLinearIsometry.toContinuousLinearMap K

@[simp]
lemma coe_reflectBody {u : E} (hu : ‖u‖ = 1) (K : ConvexBody E) :
    (reflectBody hu K : Set E) = reflectHyperplane hu '' (K : Set E) := by
  simp [reflectBody]

lemma reflectBody_involutive {u : E} (hu : ‖u‖ = 1) (K : ConvexBody E) :
    reflectBody hu (reflectBody hu K) = K := by
  apply ConvexBody.ext
  rw [coe_reflectBody, coe_reflectBody, ← Set.image_comp]
  ext x
  simp only [Set.mem_image, Function.comp_apply, reflectHyperplane_involutive, exists_eq_right]

theorem supportFn_reflectBody {u : E} (hu : ‖u‖ = 1) (K : ConvexBody E) (v : E) :
    supportFn (reflectBody hu K) v = supportFn K (reflectHyperplane hu v) := by
  rw [reflectBody, supportFn_mapLinearIsometry, reflectHyperplane_symm]

/-- **Minkowski symmetrization** of `K : ConvexBody E` across the hyperplane `u⊥`:
`minkowskiSymm hu K = (1 / 2) • (K + reflectBody hu K)`. -/
noncomputable def minkowskiSymm {u : E} (hu : ‖u‖ = 1) (K : ConvexBody E) : ConvexBody E :=
  (1 / 2 : ℝ) • (K + reflectBody hu K)

theorem supportFn_minkowskiSymm {u : E} (hu : ‖u‖ = 1) (K : ConvexBody E) (v : E) :
    supportFn (minkowskiSymm hu K) v =
      (supportFn K v + supportFn K (reflectHyperplane hu v)) / 2 := by
  rw [minkowskiSymm, supportFn_body_smul _ (by norm_num), supportFn_minkowski_add,
    supportFn_reflectBody]
  ring

/-- `minkowskiSymm hu K` is invariant under reflection across `u⊥`. -/
theorem reflectBody_minkowskiSymm [CompleteSpace E] {u : E} (hu : ‖u‖ = 1) (K : ConvexBody E) :
    reflectBody hu (minkowskiSymm hu K) = minkowskiSymm hu K := by
  apply supportFn_injective
  ext v
  rw [supportFn_reflectBody, supportFn_minkowskiSymm, supportFn_minkowskiSymm,
    reflectHyperplane_involutive, add_comm]

/-- **Minkowski symmetrization does not decrease volume** (by Brunn–Minkowski!). -/
theorem volume_le_volume_minkowskiSymm [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E} (hu : ‖u‖ = 1) (K : ConvexBody E) :
    volume (K : Set E) ≤ volume (minkowskiSymm hu K : Set E) := by
  have hrefl_vol : volume (reflectBody hu K : Set E) = volume (K : Set E) := by
    rw [coe_reflectBody]
    have hmp := (reflectHyperplane hu).measurePreserving
    have himg : reflectHyperplane hu '' (K : Set E) = (reflectHyperplane hu) ⁻¹' (K : Set E) := by
      ext x; simp only [mem_image, mem_preimage]
      exact ⟨fun ⟨y, hy, hyx⟩ => by rw [← hyx, reflectHyperplane_involutive]; exact hy,
        fun hx => ⟨reflectHyperplane hu x, hx, reflectHyperplane_involutive hu x⟩⟩
    rw [himg, hmp.measure_preimage K.isClosed.measurableSet.nullMeasurableSet]
  have hhalf : (1 - (1 / 2 : ℝ)) = 1 / 2 := by norm_num
  have hbm := brunn_minkowski_mul_compact K.isCompact (reflectBody hu K).isCompact
    (t := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  rw [hhalf, hrefl_vol,
    ← ENNReal.rpow_add_of_nonneg (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num),
    show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, ENNReal.rpow_one] at hbm
  have hset : ((minkowskiSymm hu K : ConvexBody E) : Set E) =
      (1 / 2 : ℝ) • (K : Set E) + (1 / 2 : ℝ) • (reflectBody hu K : Set E) := by
    rw [minkowskiSymm, ConvexBody.coe_smul, ConvexBody.coe_add, smul_set_add]
  rwa [hset]

/-- **Minkowski symmetrization does not increase diameter:**
`diam (minkowskiSymm hu K) ≤ diam K`. -/
theorem diam_minkowskiSymm_le {u : E} (hu : ‖u‖ = 1) (K : ConvexBody E) :
    Metric.diam (minkowskiSymm hu K : Set E) ≤ Metric.diam (K : Set E) := by
  refine Metric.diam_le_of_forall_dist_le Metric.diam_nonneg fun x hx y hy => ?_
  rw [minkowskiSymm, ConvexBody.coe_smul, ConvexBody.coe_add, smul_set_add] at hx hy
  rcases Set.mem_add.mp hx with ⟨_, ⟨x₁, hx₁, rfl⟩, _, ⟨rx₂, hrx₂, rfl⟩, rfl⟩
  rcases Set.mem_add.mp hy with ⟨_, ⟨y₁, hy₁, rfl⟩, _, ⟨ry₂, hry₂, rfl⟩, rfl⟩
  rw [coe_reflectBody] at hrx₂ hry₂
  rcases hrx₂ with ⟨x₂, hx₂, rfl⟩
  rcases hry₂ with ⟨y₂, hy₂, rfl⟩
  have h1 : ‖x₁ - y₁‖ ≤ Metric.diam (K : Set E) := by
    simpa [dist_eq_norm] using Metric.dist_le_diam_of_mem K.isBounded hx₁ hy₁
  have h2 : ‖reflectHyperplane hu x₂ - reflectHyperplane hu y₂‖ ≤ Metric.diam (K : Set E) := by
    rw [← map_sub, (reflectHyperplane hu).norm_map]
    simpa [dist_eq_norm] using Metric.dist_le_diam_of_mem K.isBounded hx₂ hy₂
  rw [dist_eq_norm]
  have hsplit : ((1 / 2 : ℝ) • x₁ + (1 / 2 : ℝ) • reflectHyperplane hu x₂) -
      ((1 / 2 : ℝ) • y₁ + (1 / 2 : ℝ) • reflectHyperplane hu y₂) =
      (1 / 2 : ℝ) • (x₁ - y₁) + (1 / 2 : ℝ) • (reflectHyperplane hu x₂ - reflectHyperplane hu y₂) := by
    rw [smul_sub, smul_sub]; abel
  rw [hsplit]
  calc
    ‖(1 / 2 : ℝ) • (x₁ - y₁) + (1 / 2 : ℝ) • (reflectHyperplane hu x₂ - reflectHyperplane hu y₂)‖
      ≤ ‖(1 / 2 : ℝ) • (x₁ - y₁)‖ +
          ‖(1 / 2 : ℝ) • (reflectHyperplane hu x₂ - reflectHyperplane hu y₂)‖ := norm_add_le _ _
    _ = (1 / 2 : ℝ) * ‖x₁ - y₁‖ +
          (1 / 2 : ℝ) * ‖reflectHyperplane hu x₂ - reflectHyperplane hu y₂‖ := by
        simp [norm_smul]
    _ ≤ (1 / 2 : ℝ) * Metric.diam (K : Set E) + (1 / 2 : ℝ) * Metric.diam (K : Set E) := by
        linarith
    _ = Metric.diam (K : Set E) := by ring

/-- **Central symmetrization** of a convex body `K`: `(K - K) / 2 = (1/2) • (K + (-1) • K)`. -/
noncomputable def centralSymm (K : ConvexBody E) : ConvexBody E :=
  (1 / 2 : ℝ) • (K + (-1 : ℝ) • K)

theorem supportFn_centralSymm (K : ConvexBody E) (v : E) :
    supportFn (centralSymm K) v = width K v / 2 := by
  rw [centralSymm, supportFn_body_smul _ (by norm_num), ← width_eq_supportFn_diff]
  ring

theorem volume_le_volume_centralSymm [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (K : ConvexBody E) :
    volume (K : Set E) ≤ volume (centralSymm K : Set E) := by
  have hneg_vol : volume (((-1 : ℝ) • K : ConvexBody E) : Set E) = volume (K : Set E) := by
    rw [ConvexBody.coe_smul, Measure.addHaar_smul]; simp
  have hhalf : (1 - (1 / 2 : ℝ)) = 1 / 2 := by norm_num
  have hbm := brunn_minkowski_mul_compact K.isCompact ((-1 : ℝ) • K).isCompact
    (t := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  rw [hhalf, hneg_vol,
    ← ENNReal.rpow_add_of_nonneg (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num),
    show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, ENNReal.rpow_one] at hbm
  have hset : ((centralSymm K : ConvexBody E) : Set E) =
      (1 / 2 : ℝ) • (K : Set E) + (1 / 2 : ℝ) • (((-1 : ℝ) • K : ConvexBody E) : Set E) := by
    rw [centralSymm, ConvexBody.coe_smul, ConvexBody.coe_add, smul_set_add]
  rwa [hset]

end MinkowskiSymm

/-! ### 2. Steiner Symmetrization on `ℝ × E` -/

section SteinerSymm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The vertical fiber of `K ⊆ ℝ × E` over `y : E`: `{t : ℝ | (t, y) ∈ K}`. -/
@[expose]
def steinerFiber (K : Set (ℝ × E)) (y : E) : Set ℝ :=
  {t : ℝ | (t, y) ∈ K}

/-- Upper endpoint `b(y) = sSup {t | (t, y) ∈ K}` of the vertical fiber over `y`.
By `Real.sSup_empty`/`Real.sSup_of_not_bddAbove`, this defaults to `0` on empty or
unbounded-above fibers; intended for compact sets `K`. -/
@[expose]
noncomputable def steinerUpper (K : Set (ℝ × E)) (y : E) : ℝ :=
  sSup (steinerFiber K y)

/-- Lower endpoint `a(y) = sInf {t | (t, y) ∈ K}` of the vertical fiber over `y`.
Defaults to `0` on empty or unbounded-below fibers; intended for compact sets `K`. -/
@[expose]
noncomputable def steinerLower (K : Set (ℝ × E)) (y : E) : ℝ :=
  sInf (steinerFiber K y)

/-- **Interval-hull Steiner symmetrization** of `K ⊆ ℝ × E` about the hyperplane `{0} × E`:
replaces every nonempty fiber `steinerFiber K y` by the centered closed interval
`[-(b(y) - a(y)) / 2, (b(y) - a(y)) / 2]` where `a(y) = sInf` and `b(y) = sSup`.

On compact convex sets every nonempty fiber is already the closed interval `[a(y), b(y)]`
(`steinerFiber_eq_Icc`), so this agrees with measure-theoretic Steiner symmetrization.
On disconnected sets it replaces each fiber by the symmetrization of its interval hull
(filling gaps). For the bundled `ConvexBody (ℝ × E)` operator, see `bodySteinerSymm`. -/
@[expose]
def steinerSymm (K : Set (ℝ × E)) : Set (ℝ × E) :=
  {p : ℝ × E | (steinerFiber K p.2).Nonempty ∧
    |p.1| ≤ (steinerUpper K p.2 - steinerLower K p.2) / 2}

omit [NormedSpace ℝ E] in
lemma isCompact_steinerFiber {K : Set (ℝ × E)} (hKc : IsCompact K) (y : E) :
    IsCompact (steinerFiber K y) := by
  have hclosed : IsClosed (steinerFiber K y) :=
    hKc.isClosed.preimage (continuous_id.prodMk continuous_const)
  have hbdd : Bornology.IsBounded (steinerFiber K y) := by
    obtain ⟨R, hKR⟩ := hKc.isBounded.subset_closedBall (0 : ℝ × E)
    refine Metric.isBounded_iff_subset_closedBall (0 : ℝ) |>.mpr ⟨R, fun t ht => ?_⟩
    have hmem : (t, y) ∈ Metric.closedBall (0 : ℝ × E) R := hKR ht
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at hmem
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (le_max_left _ _).trans hmem
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbdd

lemma steinerFiber_eq_Icc {K : Set (ℝ × E)} (hKconv : Convex ℝ K) (hKc : IsCompact K)
    {y : E} (hne : (steinerFiber K y).Nonempty) :
    steinerFiber K y = Icc (steinerLower K y) (steinerUpper K y) := by
  have hfc := isCompact_steinerFiber hKc y
  have ha : steinerLower K y ∈ steinerFiber K y := hfc.sInf_mem hne
  have hb : steinerUpper K y ∈ steinerFiber K y := hfc.sSup_mem hne
  have hfconv : Convex ℝ (steinerFiber K y) := by
    intro t₁ ht₁ t₂ ht₂ c₁ c₂ hc₁ hc₂ hc12
    have hmem := hKconv ht₁ ht₂ hc₁ hc₂ hc12
    have hy : c₁ • y + c₂ • y = y := by rw [← add_smul, hc12, one_smul]
    simpa [steinerFiber, Prod.smul_mk, Prod.mk_add_mk, hy] using hmem
  ext t
  constructor
  · intro ht
    exact ⟨csInf_le hfc.bddBelow ht, le_csSup hfc.bddAbove ht⟩
  · rintro ⟨h1, h2⟩
    exact hfconv.ordConnected.out ha hb ⟨h1, h2⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Symmetry of Steiner symmetrization: `(t, y) ∈ S(K) ↔ (-t, y) ∈ S(K)`. -/
theorem steinerSymm_symm (K : Set (ℝ × E)) (t : ℝ) (y : E) :
    (-t, y) ∈ steinerSymm K ↔ (t, y) ∈ steinerSymm K := by
  simp [steinerSymm, abs_neg]

omit [NormedSpace ℝ E] in
/-- Monotonicity of Steiner symmetrization for compact sets. -/
theorem steinerSymm_mono {K L : Set (ℝ × E)} (hLc : IsCompact L) (hKL : K ⊆ L) :
    steinerSymm K ⊆ steinerSymm L := by
  rintro ⟨t, y⟩ ⟨hneK, ht⟩
  have hsub : steinerFiber K y ⊆ steinerFiber L y := fun s hs => hKL hs
  have hneL : (steinerFiber L y).Nonempty := hneK.mono hsub
  have hLfc := isCompact_steinerFiber hLc y
  have hup : steinerUpper K y ≤ steinerUpper L y :=
    csSup_le_csSup hLfc.bddAbove hneK hsub
  have hlo : steinerLower L y ≤ steinerLower K y :=
    csInf_le_csInf hLfc.bddBelow hneK hsub
  exact ⟨hneL, ht.trans (by linarith)⟩

/-- **Steiner symmetrization preserves convexity.** -/
theorem convex_steinerSymm {K : Set (ℝ × E)} (hKconv : Convex ℝ K) (hKc : IsCompact K) :
    Convex ℝ (steinerSymm K) := by
  rintro ⟨t₁, y₁⟩ ⟨hne₁, ht₁⟩ ⟨t₂, y₂⟩ ⟨hne₂, ht₂⟩ c₁ c₂ hc₁ hc₂ hc12
  have hfc₁ := isCompact_steinerFiber hKc y₁
  have hfc₂ := isCompact_steinerFiber hKc y₂
  have ha₁ : (steinerLower K y₁, y₁) ∈ K := hfc₁.sInf_mem hne₁
  have hb₁ : (steinerUpper K y₁, y₁) ∈ K := hfc₁.sSup_mem hne₁
  have ha₂ : (steinerLower K y₂, y₂) ∈ K := hfc₂.sInf_mem hne₂
  have hb₂ : (steinerUpper K y₂, y₂) ∈ K := hfc₂.sSup_mem hne₂
  have ha_mem : c₁ * steinerLower K y₁ + c₂ * steinerLower K y₂ ∈
      steinerFiber K (c₁ • y₁ + c₂ • y₂) := by
    simpa [steinerFiber, Prod.smul_mk, Prod.mk_add_mk] using hKconv ha₁ ha₂ hc₁ hc₂ hc12
  have hb_mem : c₁ * steinerUpper K y₁ + c₂ * steinerUpper K y₂ ∈
      steinerFiber K (c₁ • y₁ + c₂ • y₂) := by
    simpa [steinerFiber, Prod.smul_mk, Prod.mk_add_mk] using hKconv hb₁ hb₂ hc₁ hc₂ hc12
  have hne : (steinerFiber K (c₁ • y₁ + c₂ • y₂)).Nonempty := ⟨_, ha_mem⟩
  have hfc := isCompact_steinerFiber hKc (c₁ • y₁ + c₂ • y₂)
  have hlo : steinerLower K (c₁ • y₁ + c₂ • y₂) ≤ c₁ * steinerLower K y₁ + c₂ * steinerLower K y₂ :=
    csInf_le hfc.bddBelow ha_mem
  have hup : c₁ * steinerUpper K y₁ + c₂ * steinerUpper K y₂ ≤ steinerUpper K (c₁ • y₁ + c₂ • y₂) :=
    le_csSup hfc.bddAbove hb_mem
  refine ⟨hne, ?_⟩
  change |c₁ * t₁ + c₂ * t₂| ≤ _
  calc
    |c₁ * t₁ + c₂ * t₂| ≤ |c₁ * t₁| + |c₂ * t₂| := abs_add_le _ _
    _ = c₁ * |t₁| + c₂ * |t₂| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hc₁, abs_of_nonneg hc₂]
    _ ≤ c₁ * ((steinerUpper K y₁ - steinerLower K y₁) / 2) +
          c₂ * ((steinerUpper K y₂ - steinerLower K y₂) / 2) :=
        add_le_add (mul_le_mul_of_nonneg_left ht₁ hc₁) (mul_le_mul_of_nonneg_left ht₂ hc₂)
    _ ≤ (steinerUpper K (c₁ • y₁ + c₂ • y₂) - steinerLower K (c₁ • y₁ + c₂ • y₂)) / 2 := by
        linarith

omit [NormedSpace ℝ E] in
/-- **Steiner symmetrization preserves compactness.** -/
theorem isCompact_steinerSymm {K : Set (ℝ × E)} (hKc : IsCompact K) :
    IsCompact (steinerSymm K) := by
  -- Use sequential compactness: a bounded sequence in `S(K)` has `(a_n, y_n), (b_n, y_n) ∈ K`.
  rw [isCompact_iff_isSeqCompact]
  intro p hp
  have hne : ∀ n, (steinerFiber K (p n).2).Nonempty := fun n => (hp n).1
  let a : ℕ → ℝ := fun n => steinerLower K (p n).2
  let b : ℕ → ℝ := fun n => steinerUpper K (p n).2
  have ha_mem : ∀ n, (a n, (p n).2) ∈ K := fun n => (isCompact_steinerFiber hKc _).sInf_mem (hne n)
  have hb_mem : ∀ n, (b n, (p n).2) ∈ K := fun n => (isCompact_steinerFiber hKc _).sSup_mem (hne n)
  -- Extract a common convergent subsequence of `((a n, y n), (b n, y n))` in the compact `K ×ˢ K`,
  -- and simultaneously of `p n` (since `|(p n).1| ≤ (b n - a n)/2` is bounded!).
  obtain ⟨R, hKR⟩ := hKc.isBounded.subset_closedBall (0 : ℝ × E)
  have hp_bdd : ∀ n, (p n).1 ∈ Icc (-R) R := fun n => by
    have haR : |a n| ≤ R := by
      have := hKR (ha_mem n)
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at this
      simpa [Real.norm_eq_abs] using (le_max_left _ _).trans this
    have hbR : |b n| ≤ R := by
      have := hKR (hb_mem n)
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at this
      simpa [Real.norm_eq_abs] using (le_max_left _ _).trans this
    have ht := (hp n).2
    have h3 : (b n - a n) / 2 ≤ R := by linarith [le_abs_self (b n), neg_abs_le (a n)]
    exact abs_le.mp (ht.trans h3)
  let q : ℕ → (ℝ × E) × (ℝ × E) × ℝ := fun n => ((a n, (p n).2), (b n, (p n).2), (p n).1)
  have hqc : IsCompact (K ×ˢ (K ×ˢ Icc (-R) R)) := hKc.prod (hKc.prod isCompact_Icc)
  have hq_mem : ∀ n, q n ∈ K ×ˢ (K ×ˢ Icc (-R) R) := fun n => ⟨ha_mem n, hb_mem n, hp_bdd n⟩
  obtain ⟨⟨⟨a₀, y₀⟩, ⟨b₀, y₀'⟩, t₀⟩, ⟨ha₀, hb₀, _⟩, φ, hφ, htend⟩ := hqc.tendsto_subseq hq_mem
  have hta : Filter.Tendsto (fun n => a (φ n)) Filter.atTop (nhds a₀) :=
    (continuous_fst.comp continuous_fst).continuousAt.tendsto.comp htend
  have hty₁ : Filter.Tendsto (fun n => (p (φ n)).2) Filter.atTop (nhds y₀) :=
    (continuous_snd.comp continuous_fst).continuousAt.tendsto.comp htend
  have htb : Filter.Tendsto (fun n => b (φ n)) Filter.atTop (nhds b₀) :=
    (continuous_fst.comp (continuous_fst.comp continuous_snd)).continuousAt.tendsto.comp htend
  have hty₂ : Filter.Tendsto (fun n => (p (φ n)).2) Filter.atTop (nhds y₀') :=
    (continuous_snd.comp (continuous_fst.comp continuous_snd)).continuousAt.tendsto.comp htend
  have htt : Filter.Tendsto (fun n => (p (φ n)).1) Filter.atTop (nhds t₀) :=
    (continuous_snd.comp continuous_snd).continuousAt.tendsto.comp htend
  have hy_eq : y₀ = y₀' := tendsto_nhds_unique hty₁ hty₂
  subst hy_eq
  have hfc₀ := isCompact_steinerFiber hKc y₀
  have ha₀_le : steinerLower K y₀ ≤ a₀ := csInf_le hfc₀.bddBelow ha₀
  have hb₀_ge : b₀ ≤ steinerUpper K y₀ := le_csSup hfc₀.bddAbove hb₀
  have ht₀_le : |t₀| ≤ (b₀ - a₀) / 2 :=
    le_of_tendsto_of_tendsto (continuous_abs.continuousAt.tendsto.comp htt)
      ((htb.sub hta).div_const 2) (Filter.Eventually.of_forall fun n => (hp (φ n)).2)
  refine ⟨(t₀, y₀), ⟨⟨a₀, ha₀⟩, ht₀_le.trans (by linarith)⟩, φ, hφ, ?_⟩
  exact htt.prodMk_nhds hty₁

/-- **Steiner symmetrization preserves Lebesgue volume** (by Fubini's theorem!):
for every compact convex `K ⊆ ℝ × E`, `volume (steinerSymm K) = volume K`. -/
theorem volume_steinerSymm [FiniteDimensional ℝ E] [MeasureSpace E]
    [SigmaFinite (volume : Measure E)] [BorelSpace E]
    {K : Set (ℝ × E)} (hKconv : Convex ℝ K) (hKc : IsCompact K) :
    volume (steinerSymm K) = volume K := by
  have hSc : IsCompact (steinerSymm K) := isCompact_steinerSymm hKc
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hSm : MeasurableSet (steinerSymm K) := hSc.isClosed.measurableSet
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hSm, Measure.prod_apply_symm hKm]
  refine lintegral_congr fun y => ?_
  by_cases hne : (steinerFiber K y).Nonempty
  · have hKfib : (fun t : ℝ => (t, y)) ⁻¹' K = Icc (steinerLower K y) (steinerUpper K y) :=
      steinerFiber_eq_Icc hKconv hKc hne
    have hSfib : (fun t : ℝ => (t, y)) ⁻¹' steinerSymm K =
        Icc (-((steinerUpper K y - steinerLower K y) / 2))
          ((steinerUpper K y - steinerLower K y) / 2) := by
      ext t
      simp [steinerSymm, hne, abs_le]
    rw [hKfib, hSfib, Real.volume_Icc, Real.volume_Icc]
    congr 1
    ring
  · have hKempty : (fun t : ℝ => (t, y)) ⁻¹' K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hSempty : (fun t : ℝ => (t, y)) ⁻¹' steinerSymm K = ∅ := by
      ext t; simp [steinerSymm, hne]
    rw [hKempty, hSempty]

omit [NormedSpace ℝ E] in
/-- **Steiner symmetrization does not increase Euclidean pairwise distances (hence diameter):**
for any `(t₁, y₁), (t₂, y₂) ∈ steinerSymm K` (with `K` compact), there exist two points in `K`
whose squared Euclidean distance is at least `(t₁ - t₂)² + ‖y₁ - y₂‖²`. -/
theorem steinerSymm_dist_le_diam {K : Set (ℝ × E)} (hKc : IsCompact K)
    {t₁ t₂ : ℝ} {y₁ y₂ : E}
    (h₁ : (t₁, y₁) ∈ steinerSymm K) (h₂ : (t₂, y₂) ∈ steinerSymm K) :
    ∃ p q : ℝ × E, p ∈ K ∧ q ∈ K ∧
      (t₁ - t₂) ^ 2 + ‖y₁ - y₂‖ ^ 2 ≤ (p.1 - q.1) ^ 2 + ‖p.2 - q.2‖ ^ 2 := by
  have ha₁ : (steinerLower K y₁, y₁) ∈ K := (isCompact_steinerFiber hKc y₁).sInf_mem h₁.1
  have hb₁ : (steinerUpper K y₁, y₁) ∈ K := (isCompact_steinerFiber hKc y₁).sSup_mem h₁.1
  have ha₂ : (steinerLower K y₂, y₂) ∈ K := (isCompact_steinerFiber hKc y₂).sInf_mem h₂.1
  have hb₂ : (steinerUpper K y₂, y₂) ∈ K := (isCompact_steinerFiber hKc y₂).sSup_mem h₂.1
  have hlen : |t₁ - t₂| ≤ ((steinerUpper K y₁ - steinerLower K y₂) +
      (steinerUpper K y₂ - steinerLower K y₁)) / 2 := by
    have habs : |t₁ - t₂| ≤ |t₁| + |t₂| := abs_sub t₁ t₂
    linarith [h₁.2, h₂.2]
  rcases le_total (steinerUpper K y₁ - steinerLower K y₂)
      (steinerUpper K y₂ - steinerLower K y₁) with hle | hle
  · refine ⟨(steinerUpper K y₂, y₂), (steinerLower K y₁, y₁), hb₂, ha₁, ?_⟩
    have hbound : |t₁ - t₂| ≤ steinerUpper K y₂ - steinerLower K y₁ := by linarith
    have hsq : (t₁ - t₂) ^ 2 ≤ (steinerUpper K y₂ - steinerLower K y₁) ^ 2 := by
      rw [← sq_abs (t₁ - t₂)]
      exact pow_le_pow_left₀ (abs_nonneg _) hbound 2
    rw [norm_sub_rev y₂ y₁]
    linarith
  · refine ⟨(steinerUpper K y₁, y₁), (steinerLower K y₂, y₂), hb₁, ha₂, ?_⟩
    have hbound : |t₁ - t₂| ≤ steinerUpper K y₁ - steinerLower K y₂ := by linarith
    have hsq : (t₁ - t₂) ^ 2 ≤ (steinerUpper K y₁ - steinerLower K y₂) ^ 2 := by
      rw [← sq_abs (t₁ - t₂)]
      exact pow_le_pow_left₀ (abs_nonneg _) hbound 2
    linarith

/-- **Bundled Steiner symmetrization on `ConvexBody (ℝ × E)`:**
maps any convex body `K : ConvexBody (ℝ × E)` to its Steiner symmetrization about `{0} × E`. -/
noncomputable def bodySteinerSymm (K : ConvexBody (ℝ × E)) : ConvexBody (ℝ × E) where
  carrier := steinerSymm (K : Set (ℝ × E))
  convex' := convex_steinerSymm K.convex K.isCompact
  isCompact' := isCompact_steinerSymm K.isCompact
  nonempty' := by
    obtain ⟨⟨t, y⟩, hty⟩ := K.nonempty
    have hfc := isCompact_steinerFiber K.isCompact y
    have hlo : steinerLower (K : Set (ℝ × E)) y ≤ t := csInf_le hfc.bddBelow hty
    have hhi : t ≤ steinerUpper (K : Set (ℝ × E)) y := le_csSup hfc.bddAbove hty
    exact ⟨(0, y), ⟨t, hty⟩, by simp only [abs_zero]; linarith⟩

@[simp]
lemma coe_bodySteinerSymm (K : ConvexBody (ℝ × E)) :
    (bodySteinerSymm K : Set (ℝ × E)) = steinerSymm (K : Set (ℝ × E)) := by
  simp [bodySteinerSymm, ConvexBody.coe_mk]

/-- `bodySteinerSymm` preserves Lebesgue volume on `ConvexBody (ℝ × E)`. -/
theorem volume_bodySteinerSymm [FiniteDimensional ℝ E] [MeasureSpace E]
    [SigmaFinite (volume : Measure E)] [BorelSpace E] (K : ConvexBody (ℝ × E)) :
    volume (bodySteinerSymm K : Set (ℝ × E)) = volume (K : Set (ℝ × E)) :=
  volume_steinerSymm K.convex K.isCompact

end SteinerSymm

end

end ConvexGeom
