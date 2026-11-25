module

public import ConvexGeom.SupportFunction

import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology

/-!
# Polytopes and Polytope Approximation of Convex Bodies

This file provides foundational bridges between finite point sets, their convex hulls
(polytopes as `ConvexBody E`), support functions, and Hausdorff approximation:

- `bodyConvexHull`: packages `convexHull ℝ (S : Set E)` of a nonempty `Finset E` as a `ConvexBody E`.
- `supportFn_bodyConvexHull`: the support function of a polytope is the maximum over its vertices:
  `supportFn (bodyConvexHull S hS) u = S.sup' hS (fun x => ⟪x, u⟫)`.
- `hausdorffDist_convexHull_range_le`: **1-Lipschitz continuity of convex hulls** in the Hausdorff
  metric: if `∀ i, dist (v i) (w i) ≤ r`, then `dist (conv v) (conv w) ≤ r`.
- `exists_polytope_dist_lt`: **Polytope Approximation Theorem** — every convex body `K` can be
  approximated arbitrarily closely in Hausdorff distance by an inscribed polytope `P ⊆ K`
  (vertices in `K`).
-/

open scoped RealInnerProductSpace

namespace ConvexGeom

public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The convex hull of a nonempty finite set `S : Finset E`, packaged as a `ConvexBody E`. -/
def bodyConvexHull (S : Finset E) (hS : S.Nonempty) : ConvexBody E where
  carrier := convexHull ℝ (S : Set E)
  convex' := convex_convexHull ℝ (S : Set E)
  isCompact' := S.finite_toSet.isCompact_convexHull ℝ
  nonempty' := hS.to_set.convexHull

@[simp]
lemma coe_bodyConvexHull (S : Finset E) (hS : S.Nonempty) :
    (bodyConvexHull S hS : Set E) = convexHull ℝ (S : Set E) := by
  simp [bodyConvexHull, ConvexBody.coe_mk]

/-- The support function of a polytope `conv(S)` is the maximum of `⟪x, u⟫` over `x ∈ S`. -/
theorem supportFn_bodyConvexHull (S : Finset E) (hS : S.Nonempty) (u : E) :
    supportFn (bodyConvexHull S hS) u = S.sup' hS (fun x => ⟪x, u⟫) := by
  apply le_antisymm
  · rw [supportFn_le_iff]
    intro x hx
    have hconv : Convex ℝ {z : E | ⟪z, u⟫ ≤ S.sup' hS (fun y => ⟪y, u⟫)} := by
      intro a ha b hb s t hs ht hst
      change ⟪a, u⟫ ≤ S.sup' hS (fun y => ⟪y, u⟫) at ha
      change ⟪b, u⟫ ≤ S.sup' hS (fun y => ⟪y, u⟫) at hb
      change ⟪s • a + t • b, u⟫ ≤ _
      rw [inner_add_left, inner_smul_left, inner_smul_left]
      simp only [RCLike.conj_to_real]
      calc
        s * ⟪a, u⟫ + t * ⟪b, u⟫
          ≤ s * S.sup' hS (fun y => ⟪y, u⟫) + t * S.sup' hS (fun y => ⟪y, u⟫) :=
            add_le_add (mul_le_mul_of_nonneg_left ha hs) (mul_le_mul_of_nonneg_left hb ht)
        _ = (s + t) * S.sup' hS (fun y => ⟪y, u⟫) := by ring
        _ = S.sup' hS (fun y => ⟪y, u⟫) := by rw [hst, one_mul]
    have hsub : (S : Set E) ⊆ {z : E | ⟪z, u⟫ ≤ S.sup' hS (fun y => ⟪y, u⟫)} :=
      fun y hy => Finset.le_sup' (f := fun y => ⟪y, u⟫) hy
    exact convexHull_min hsub hconv hx
  · rw [Finset.sup'_le_iff]
    intro x hx
    exact inner_le_supportFn (subset_convexHull ℝ (S : Set E) hx) u

/-- **1-Lipschitz continuity of convex hulls in the Hausdorff metric:**
if `∀ i, dist (v i) (w i) ≤ r`, then `hausdorffDist (convexHull ℝ (range v)) (convexHull ℝ (range w)) ≤ r`. -/
theorem hausdorffDist_convexHull_range_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (v w : ι → E) {r : ℝ} (hr : 0 ≤ r) (hvw : ∀ i, dist (v i) (w i) ≤ r) :
    Metric.hausdorffDist (convexHull ℝ (Set.range v)) (convexHull ℝ (Set.range w)) ≤ r := by
  have h1 : ∀ x ∈ convexHull ℝ (Set.range v),
      ∃ y ∈ convexHull ℝ (Set.range w), dist x y ≤ r := by
    intro x hx
    rw [convexHull_range_eq_exists_affineCombination] at hx
    rcases hx with ⟨s, c, hc0, hc1, rfl⟩
    refine ⟨s.affineCombination ℝ w c, ?_, ?_⟩
    · rw [convexHull_range_eq_exists_affineCombination]
      exact ⟨s, c, hc0, hc1, rfl⟩
    · rw [Finset.affineCombination_eq_linear_combination s v c hc1,
        Finset.affineCombination_eq_linear_combination s w c hc1,
        dist_eq_norm, ← Finset.sum_sub_distrib]
      calc
        ‖∑ i ∈ s, (c i • v i - c i • w i)‖
          ≤ ∑ i ∈ s, ‖c i • v i - c i • w i‖ := norm_sum_le _ _
        _ = ∑ i ∈ s, c i * dist (v i) (w i) := by
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hc0 i hi), dist_eq_norm]
        _ ≤ ∑ i ∈ s, c i * r :=
            Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hvw i) (hc0 i hi)
        _ = (∑ i ∈ s, c i) * r := (Finset.sum_mul _ _ _).symm
        _ = r := by rw [hc1, one_mul]
  have h2 : ∀ y ∈ convexHull ℝ (Set.range w),
      ∃ x ∈ convexHull ℝ (Set.range v), dist y x ≤ r := by
    intro y hy
    rw [convexHull_range_eq_exists_affineCombination] at hy
    rcases hy with ⟨s, c, hc0, hc1, rfl⟩
    refine ⟨s.affineCombination ℝ v c, ?_, ?_⟩
    · rw [convexHull_range_eq_exists_affineCombination]
      exact ⟨s, c, hc0, hc1, rfl⟩
    · rw [Finset.affineCombination_eq_linear_combination s w c hc1,
        Finset.affineCombination_eq_linear_combination s v c hc1,
        dist_eq_norm, ← Finset.sum_sub_distrib]
      calc
        ‖∑ i ∈ s, (c i • w i - c i • v i)‖
          ≤ ∑ i ∈ s, ‖c i • w i - c i • v i‖ := norm_sum_le _ _
        _ = ∑ i ∈ s, c i * dist (w i) (v i) := by
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hc0 i hi), dist_eq_norm]
        _ ≤ ∑ i ∈ s, c i * r :=
            Finset.sum_le_sum fun i hi =>
              mul_le_mul_of_nonneg_left (by rw [dist_comm]; exact hvw i) (hc0 i hi)
        _ = (∑ i ∈ s, c i) * r := (Finset.sum_mul _ _ _).symm
        _ = r := by rw [hc1, one_mul]
  exact Metric.hausdorffDist_le_of_mem_dist hr h1 h2

/-- **Polytope Approximation of Convex Bodies:**
For every `K : ConvexBody E` and `ε > 0`, there is a nonempty finite set `S ⊆ K` whose
convex hull `P = bodyConvexHull S hS` satisfies `P ⊆ K` and `dist P K < ε`. -/
theorem exists_polytope_dist_lt (K : ConvexBody E) {ε : ℝ} (hε : 0 < ε) :
    ∃ (S : Finset E) (hS : S.Nonempty),
      (S : Set E) ⊆ K ∧ (bodyConvexHull S hS : Set E) ⊆ K ∧ dist (bodyConvexHull S hS) K < ε := by
  classical
  have hcover : (K : Set E) ⊆ ⋃ x ∈ (K : Set E), Metric.ball x (ε / 2) :=
    fun x hx => Set.mem_biUnion hx (Metric.mem_ball_self (by linarith))
  obtain ⟨T, hTK, hTfin, hTsub⟩ := K.isCompact.elim_finite_subcover_image
    (fun _ _ => Metric.isOpen_ball) hcover
  let S : Finset E := hTfin.toFinset
  have hS_coe : (S : Set E) = T := hTfin.coe_toFinset
  have hSK : (S : Set E) ⊆ K := hS_coe.symm ▸ hTK
  have hS_ne : S.Nonempty := by
    obtain ⟨x, hx⟩ := K.nonempty
    obtain ⟨y, hyT, _⟩ := Set.mem_iUnion₂.mp (hTsub hx)
    exact ⟨y, hTfin.mem_toFinset.mpr hyT⟩
  let P := bodyConvexHull S hS_ne
  have hPK : (P : Set E) ⊆ K := convexHull_min hSK K.convex
  have hdist : dist P K ≤ ε / 2 := by
    rw [← ConvexBody.hausdorffDist_coe]
    refine Metric.hausdorffDist_le_of_mem_dist (by linarith) ?_ ?_
    · intro x hxP
      exact ⟨x, hPK hxP, by simp [le_of_lt (half_pos hε)]⟩
    · intro x hxK
      obtain ⟨y, hyT, hxy⟩ := Set.mem_iUnion₂.mp (hTsub hxK)
      refine ⟨y, subset_convexHull ℝ (S : Set E) (hTfin.mem_toFinset.mpr hyT), ?_⟩
      exact (Metric.mem_ball.mp hxy).le
  exact ⟨S, hS_ne, hSK, hPK, lt_of_le_of_lt hdist (half_lt_self hε)⟩

end

end ConvexGeom
