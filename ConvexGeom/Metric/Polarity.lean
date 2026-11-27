/-
Copyright (c) 2026 Yegor Gorodzha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yegor Gorodzha
-/
module

public import ConvexGeom.Metric.SupportFunction
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.InnerProductSpace.Adjoint

import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Polar Bodies, the Bipolar Theorem, and Gauge–Support Duality

This file defines the geometric (one-sided) **polar body** of a set `S ⊆ E` in a real inner
product space `E`:
$$
  S^\circ := \{ y \in E \mid \forall x \in S,\; \langle x, y \rangle \le 1 \}.
$$

## Main definitions

* `ConvexGeom.polarBody`: one-sided geometric polar `{y | ∀ x ∈ S, ⟪x, y⟫ ≤ 1}`.
* `ConvexGeom.bodyPolar`: packages `polarBody S` as a `ConvexBody E` when `0 ∈ interior S`.

## Main statements

* `ConvexGeom.polarBody_polarBody`: **Bipolar Theorem** — for any closed convex set `K` containing
  `0` in a Hilbert space, `(K°)° = K`.
* `ConvexGeom.isCompact_polarBody_of_zero_mem_interior`,
  `ConvexGeom.zero_mem_interior_polarBody_of_isBounded`: compactness and interior duality.
* `ConvexGeom.gauge_polarBody_eq_supportFn`, `ConvexGeom.supportFn_bodyPolar_eq_gauge`:
  **Gauge–Support Duality** (`gauge (polarBody K) = supportFn K` and
  `supportFn (bodyPolar K h₀) = gauge K`).

## Implementation notes

Unlike Mathlib's `LinearMap.polar` (which uses `|⟪x, y⟫| ≤ 1` for balanced sets), `polarBody` is
the standard one-sided convex-geometric polar and agrees with the absolute polar on
origin-symmetric sets (`mem_polarBody_iff_abs_inner_le_one`).

## References

* [K. Ball, *An Elementary Introduction to Modern Convex Geometry*][ball1997], Lecture 1.
* [R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*][schneider2014], §1.6.
-/

open scoped RealInnerProductSpace Pointwise

namespace ConvexGeom

public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### 1. Definition and Basic Calculus -/

/-- The geometric (one-sided) polar body of a set `S ⊆ E`:
`polarBody S = {y | ∀ x ∈ S, ⟪x, y⟫ ≤ 1}`. -/
@[expose]
def polarBody (S : Set E) : Set E :=
  {y | ∀ x ∈ S, ⟪x, y⟫ ≤ 1}

@[simp]
lemma mem_polarBody {S : Set E} {y : E} :
    y ∈ polarBody S ↔ ∀ x ∈ S, ⟪x, y⟫ ≤ 1 := Iff.rfl

lemma zero_mem_polarBody (S : Set E) : (0 : E) ∈ polarBody S := by
  intro x _; simp

lemma polarBody_nonempty (S : Set E) : (polarBody S).Nonempty :=
  ⟨0, zero_mem_polarBody S⟩

lemma convex_polarBody (S : Set E) : Convex ℝ (polarBody S) := by
  intro y hy z hz a b ha hb hab x hx
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  nlinarith [hy x hx, hz x hx]

lemma isClosed_polarBody (S : Set E) : IsClosed (polarBody S) := by
  have heq : polarBody S = ⋂ x ∈ S, {y : E | ⟪x, y⟫ ≤ 1} := by
    ext y; simp [polarBody]
  rw [heq]
  exact isClosed_biInter fun x _ =>
    isClosed_le (continuous_const.inner continuous_id) continuous_const

lemma polarBody_antitone : Antitone (polarBody (E := E)) :=
  fun _ _ hST _ hy x hx => hy x (hST hx)

lemma subset_polarBody_polarBody (S : Set E) : S ⊆ polarBody (polarBody S) :=
  fun x hx y hy => by rw [real_inner_comm]; exact hy x hx

lemma polarBody_union (S T : Set E) :
    polarBody (S ∪ T) = polarBody S ∩ polarBody T := by
  ext y
  simp only [mem_polarBody, Set.mem_union, Set.mem_inter_iff]
  exact ⟨fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩,
    fun ⟨hS, hT⟩ x hx => hx.elim (hS x) (hT x)⟩

lemma polarBody_closure (S : Set E) : polarBody (closure S) = polarBody S := by
  apply Set.Subset.antisymm (polarBody_antitone subset_closure)
  intro y hy x hx
  have hclosed : IsClosed {z : E | ⟪z, y⟫ ≤ 1} :=
    isClosed_le (continuous_id.inner continuous_const) continuous_const
  exact closure_minimal hy hclosed hx

lemma polarBody_convexHull (S : Set E) : polarBody (convexHull ℝ S) = polarBody S := by
  apply Set.Subset.antisymm (polarBody_antitone (subset_convexHull ℝ S))
  intro y hy x hx
  have hconv : Convex ℝ {z : E | ⟪z, y⟫ ≤ 1} := by
    intro a ha b hb s t hs ht hst
    change ⟪a, y⟫ ≤ 1 at ha
    change ⟪b, y⟫ ≤ 1 at hb
    change ⟪s • a + t • b, y⟫ ≤ 1
    rw [inner_add_left, inner_smul_left, inner_smul_left]
    simp only [RCLike.conj_to_real]
    nlinarith
  exact convexHull_min hy hconv hx

lemma polarBody_smul {c : ℝ} (hc : 0 < c) (S : Set E) :
    polarBody (c • S) = c⁻¹ • polarBody S := by
  ext y
  constructor
  · intro hy
    refine ⟨c • y, fun x hx => ?_, ?_⟩
    · have hcx : c • x ∈ c • S := Set.smul_mem_smul_set hx
      have := hy (c • x) hcx
      rwa [inner_smul_left, RCLike.conj_to_real, ← inner_smul_right] at this
    · dsimp only
      rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  · rintro ⟨z, hz, rfl⟩ x hx
    rcases Set.mem_smul_set.mp hx with ⟨w, hw, rfl⟩
    rw [inner_smul_left, inner_smul_right, RCLike.conj_to_real, ← mul_assoc,
      mul_inv_cancel₀ hc.ne', one_mul]
    exact hz w hw

/-- Polar of a closed ball centered at `0`: `(closedBall 0 r)° = closedBall 0 r⁻¹` for `r > 0`. -/
theorem polarBody_closedBall {r : ℝ} (hr : 0 < r) :
    polarBody (Metric.closedBall (0 : E) r) = Metric.closedBall (0 : E) r⁻¹ := by
  ext y
  simp only [mem_polarBody, Metric.mem_closedBall, dist_zero_right]
  constructor
  · intro hy
    by_cases hy0 : y = 0
    · simpa [hy0] using inv_nonneg.mpr hr.le
    · have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
      let x : E := (r / ‖y‖) • y
      have hx : ‖x‖ ≤ r := by
        simp only [x, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr.le hpos.le)]
        rw [div_mul_cancel₀ r hpos.ne']
      have h1 := hy x hx
      have hval : ⟪x, y⟫ = r * ‖y‖ := by
        simp only [x, inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq]
        field_simp [hpos.ne']
      rw [hval] at h1
      rw [← one_div, le_div_iff₀ hr]
      linarith
  · intro hy x hx
    calc
      ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
      _ ≤ r * r⁻¹ := mul_le_mul hx hy (norm_nonneg y) hr.le
      _ = 1 := mul_inv_cancel₀ hr.ne'

/-- Linear transformation law for polar bodies:
`(A '' S)° = (A†) ⁻¹' S°`. -/
theorem polarBody_image_continuousLinearMap [CompleteSpace E] {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] F) (S : Set E) :
    polarBody (A '' S) = (ContinuousLinearMap.adjoint A) ⁻¹' (polarBody S) := by
  ext y
  simp only [mem_polarBody, Set.mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Set.mem_preimage]
  constructor
  · intro h x hx
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact h x hx
  · intro h x hx
    rw [← ContinuousLinearMap.adjoint_inner_right]
    exact h x hx

/-! ### 2. Boundedness, Compactness, and Interior Duality -/

theorem polarBody_subset_closedBall_of_closedBall_subset {S : Set E} {r : ℝ} (hr : 0 < r)
    (h : Metric.closedBall (0 : E) r ⊆ S) :
    polarBody S ⊆ Metric.closedBall (0 : E) r⁻¹ := by
  rw [← polarBody_closedBall hr]
  exact polarBody_antitone h

theorem closedBall_subset_polarBody_of_subset_closedBall {S : Set E} {R : ℝ} (hR : 0 < R)
    (h : S ⊆ Metric.closedBall (0 : E) R) :
    Metric.closedBall (0 : E) R⁻¹ ⊆ polarBody S := by
  rw [← polarBody_closedBall hR]
  exact polarBody_antitone h

theorem isCompact_polarBody_of_zero_mem_interior [ProperSpace E] {S : Set E}
    (h0 : (0 : E) ∈ interior S) : IsCompact (polarBody S) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
  have hcb : Metric.closedBall (0 : E) (r / 2) ⊆ S :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  exact (isCompact_closedBall (0 : E) (r / 2)⁻¹).of_isClosed_subset (isClosed_polarBody S)
    (polarBody_subset_closedBall_of_closedBall_subset (by linarith) hcb)

theorem zero_mem_interior_polarBody_of_isBounded {S : Set E}
    (hb : Bornology.IsBounded S) : (0 : E) ∈ interior (polarBody S) := by
  obtain ⟨R, hSR⟩ := hb.subset_closedBall (0 : E)
  let R' := max R 1
  have hR' : 0 < R' := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  have hsub : S ⊆ Metric.closedBall (0 : E) R' :=
    hSR.trans (Metric.closedBall_subset_closedBall (le_max_left R 1))
  have hball : Metric.ball (0 : E) R'⁻¹ ⊆ polarBody S :=
    Metric.ball_subset_closedBall.trans (closedBall_subset_polarBody_of_subset_closedBall hR' hsub)
  exact mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨R'⁻¹, inv_pos.mpr hR', hball⟩)

/-- Package the polar of a set `S` with `0 ∈ interior S` as a `ConvexBody E`. -/
def bodyPolar [ProperSpace E] (S : Set E) (h0 : (0 : E) ∈ interior S) : ConvexBody E where
  carrier := polarBody S
  convex' := convex_polarBody S
  isCompact' := isCompact_polarBody_of_zero_mem_interior h0
  nonempty' := polarBody_nonempty S

@[simp]
lemma coe_bodyPolar [ProperSpace E] (S : Set E) (h0 : (0 : E) ∈ interior S) :
    (bodyPolar S h0 : Set E) = polarBody S := by
  simp [bodyPolar, ConvexBody.coe_mk]

/-! ### 3. The Bipolar Theorem -/

/-- **Bipolar Theorem:**
In a real Hilbert space, if `K` is closed, convex, and contains `0`, then `(K°)° = K`. -/
theorem polarBody_polarBody [CompleteSpace E] {K : Set E}
    (hconv : Convex ℝ K) (hclosed : IsClosed K) (h0 : (0 : E) ∈ K) :
    polarBody (polarBody K) = K := by
  apply Set.Subset.antisymm _ (subset_polarBody_polarBody K)
  intro x hx
  by_contra hxK
  obtain ⟨f, s, hKs, hfx⟩ := geometric_hahn_banach_closed_point hconv hclosed hxK
  -- Since `0 ∈ K`, `0 = f 0 < s`, so we can rescale `f` by `s⁻¹` to put it in `K°`.
  have hs_pos : 0 < s := by
    have := hKs 0 h0
    simpa using this
  let u : E := s⁻¹ • (InnerProductSpace.toDual ℝ E).symm f
  have hu_polar : u ∈ polarBody K := by
    intro y hy
    have hfy : ⟪y, u⟫ = s⁻¹ * f y := by
      dsimp only [u]
      rw [inner_smul_right, real_inner_comm, InnerProductSpace.toDual_symm_apply]
    rw [hfy]
    exact (mul_le_mul_of_nonneg_left (hKs y hy).le (inv_nonneg.mpr hs_pos.le)).trans
      (by rw [inv_mul_cancel₀ hs_pos.ne'])
  have h1 : ⟪x, u⟫ ≤ 1 := by
    have := hx u hu_polar
    rwa [real_inner_comm] at this
  have hgt : 1 < ⟪x, u⟫ := by
    have hfx' : ⟪x, u⟫ = s⁻¹ * f x := by
      dsimp only [u]
      rw [inner_smul_right, real_inner_comm, InnerProductSpace.toDual_symm_apply]
    rw [hfx']
    have := mul_lt_mul_of_pos_left hfx (inv_pos.mpr hs_pos)
    rwa [inv_mul_cancel₀ hs_pos.ne'] at this
  linarith

/-! ### 4. Gauge–Support Duality -/

/-- **Gauge–Support Duality (Part I):**
For any convex body `K` containing `0`, the Minkowski gauge of its polar body `K°`
equals the support function of `K`: `gauge (polarBody K) u = supportFn K u`. -/
theorem gauge_polarBody_eq_supportFn (K : ConvexBody E) (h0 : (0 : E) ∈ K) (u : E) :
    gauge (polarBody (K : Set E)) u = supportFn K u := by
  have hnonneg : 0 ≤ supportFn K u := by
    simpa using inner_le_supportFn h0 u
  have hmem_iff : ∀ {r : ℝ}, 0 < r → (u ∈ r • polarBody (K : Set E) ↔ supportFn K u ≤ r) := by
    intro r hr
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [supportFn_le_iff]
      intro x hx
      rw [inner_smul_right]
      exact (mul_le_mul_of_nonneg_left (hy x hx) hr.le).trans (by rw [mul_one])
    · intro hle
      refine ⟨r⁻¹ • u, fun x hx => ?_, ?_⟩
      · rw [inner_smul_right]
        exact (mul_le_mul_of_nonneg_left ((inner_le_supportFn hx u).trans hle)
          (inv_nonneg.mpr hr.le)).trans (by rw [inv_mul_cancel₀ hr.ne'])
      · dsimp only
        rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hne : {r : ℝ | 0 < r ∧ u ∈ r • polarBody (K : Set E)}.Nonempty :=
    ⟨supportFn K u + 1, by linarith, (hmem_iff (by linarith)).mpr (by linarith)⟩
  have hbdd : BddBelow {r : ℝ | 0 < r ∧ u ∈ r • polarBody (K : Set E)} :=
    ⟨0, fun r hr => hr.1.le⟩
  rw [gauge]
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    exact csInf_le hbdd ⟨by linarith, (hmem_iff (by linarith)).mpr (by linarith)⟩
  · refine le_csInf hne ?_
    rintro r ⟨hr, hru⟩
    exact (hmem_iff hr).mp hru

/-- **Gauge–Support Duality (Part II):**
In a finite-dimensional real inner product space, if `K` is a convex body with `0 ∈ interior K`,
then the support function of its polar body `K°` equals the Minkowski gauge of `K`:
`supportFn (bodyPolar K h0) x = gauge K x`. -/
theorem supportFn_bodyPolar_eq_gauge [FiniteDimensional ℝ E] (K : ConvexBody E)
    (h0 : (0 : E) ∈ interior (K : Set E)) (x : E) :
    supportFn (bodyPolar (K : Set E) h0) x = gauge (K : Set E) x := by
  have h0K : (0 : E) ∈ K := interior_subset h0
  have hbipolar : polarBody (bodyPolar (K : Set E) h0 : Set E) = (K : Set E) := by
    rw [coe_bodyPolar]
    exact polarBody_polarBody K.convex K.isClosed h0K
  rw [← gauge_polarBody_eq_supportFn (bodyPolar (K : Set E) h0) (zero_mem_polarBody _), hbipolar]

end

end ConvexGeom
