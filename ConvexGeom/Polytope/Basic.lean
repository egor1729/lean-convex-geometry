/-
Copyright (c) 2026 Yegor Gorodzha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yegor Gorodzha
-/
module

public import ConvexGeom.Metric.SupportFunction

import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Order.IntermediateValue

/-!
# Polytopes and Polytope Approximation of Convex Bodies

This file provides foundational bridges between finite point sets, their convex hulls
(polytopes as `ConvexBody E`), support functions, Hausdorff approximation, and vertex push-out.

## Main definitions

* `ConvexGeom.bodyConvexHull`: packages `convexHull ℝ (S : Set E)` of a nonempty `Finset E` as a
  `ConvexBody E`.

## Main statements

* `ConvexGeom.supportFn_bodyConvexHull`: the support function of a polytope is the maximum over
  its vertices (`S.sup' hS (fun x => ⟪x, u⟫)`).
* `ConvexGeom.hausdorffDist_convexHull_range_le`: 1-Lipschitz continuity of convex hulls in the
  Hausdorff metric.
* `ConvexGeom.exists_polytope_dist_lt`: every convex body `K` can be approximated arbitrarily
  closely in Hausdorff distance by an inscribed polytope `P ⊆ K`.
* `ConvexGeom.exists_ray_mem_sphere`, `ConvexGeom.exists_pushOut_vertex_sphere`: pushing vertices
  out to a bounding sphere without shrinking the convex hull.

## References

* [R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*][schneider2014], §1.8.
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
theorem hausdorffDist_convexHull_range_le {ι : Type*}
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

/-! ### Vertex Push-Out to a Bounding Sphere -/

/-- Extending the ray from `c` through `v ∈ closedBall 0 R` (`v ≠ c`)
hits `sphere 0 R` at some parameter `t ≥ 1`. -/
theorem exists_ray_mem_sphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} {c v : E} (hv : v ∈ Metric.closedBall (0 : E) R) (hvc : v ≠ c) :
    ∃ t : ℝ, 1 ≤ t ∧ c + t • (v - c) ∈ Metric.sphere (0 : E) R := by
  have hR : 0 ≤ R := (norm_nonneg v).trans (by simpa [Metric.mem_closedBall] using hv)
  have hnorm_pos : 0 < ‖v - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hvc)
  let f : ℝ → ℝ := fun t => ‖c + t • (v - c)‖
  have hf_cont : Continuous f :=
    (continuous_const.add (continuous_id.smul continuous_const)).norm
  have hf1 : f 1 ≤ R := by
    simpa [f, Metric.mem_closedBall] using hv
  let T : ℝ := 1 + (R + ‖c‖) / ‖v - c‖
  have hT_ge : 1 ≤ T := by
    have : 0 ≤ (R + ‖c‖) / ‖v - c‖ := div_nonneg (add_nonneg hR (norm_nonneg c)) hnorm_pos.le
    linarith
  have hfT : R ≤ f T := by
    have h1 : ‖T • (v - c)‖ - ‖c‖ ≤ ‖c + T • (v - c)‖ := by
      have := norm_sub_norm_le (T • (v - c)) (-c)
      simpa [sub_neg_eq_add, add_comm] using this
    have h2 : ‖T • (v - c)‖ = T * ‖v - c‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have h3 : T * ‖v - c‖ = ‖v - c‖ + R + ‖c‖ := by
      dsimp only [T]
      rw [add_mul, one_mul, div_mul_cancel₀ _ hnorm_pos.ne']
      ring
    dsimp only [f]
    linarith
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hT_ge hf_cont.continuousOn ⟨hf1, hfT⟩
  refine ⟨t, ht.1, ?_⟩
  simpa [Metric.mem_sphere, f] using hft

/-- Any vertex `v ∈ closedBall 0 R` can be pushed out to `w ∈ sphere 0 R` without shrinking
`convexHull ℝ (insert v S)` whenever `S` is nonempty (in a nontrivial normed space). -/
theorem exists_pushOut_vertex_sphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] {R : ℝ} {S : Set E} {v : E}
    (hSne : S.Nonempty) (hv : v ∈ Metric.closedBall (0 : E) R) :
    ∃ w ∈ Metric.sphere (0 : E) R,
      convexHull ℝ (insert v S) ⊆ convexHull ℝ (insert w S) := by
  have hR : 0 ≤ R := (norm_nonneg v).trans (by simpa [Metric.mem_closedBall] using hv)
  by_cases hvS : v ∈ S
  · obtain ⟨x, hx⟩ := exists_ne (0 : E)
    refine ⟨R • (‖x‖⁻¹ • x), ?_, ?_⟩
    · rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_smul, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hR, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx), mul_one]
    · rw [Set.insert_eq_of_mem hvS]
      exact convexHull_mono (Set.subset_insert _ S)
  · obtain ⟨c, hcS⟩ := hSne
    have hvc : v ≠ c := fun h => hvS (h ▸ hcS)
    obtain ⟨t, ht1, hwt⟩ := exists_ray_mem_sphere hv hvc
    set w : E := c + t • (v - c)
    refine ⟨w, hwt, convexHull_min ?_ (convex_convexHull ℝ _)⟩
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hxv | hxS
    · rw [hxv]
      have ht_pos : 0 < t := by linarith
      have hv_comb : (1 - t⁻¹) • c + t⁻¹ • w = v := by
        have ht_ne : t ≠ 0 := ht_pos.ne'
        calc
          (1 - t⁻¹) • c + t⁻¹ • (c + t • (v - c))
            = (1 - t⁻¹) • c + t⁻¹ • c + (t⁻¹ * t) • (v - c) := by
                rw [smul_add, smul_smul, add_assoc]
          _ = ((1 - t⁻¹) + t⁻¹) • c + (1 : ℝ) • (v - c) := by
                rw [← add_smul, inv_mul_cancel₀ ht_ne]
          _ = c + (v - c) := by simp
          _ = v := add_sub_cancel c v
      have h1 : 0 ≤ 1 - t⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ ht1)
      have h2 : 0 ≤ t⁻¹ := inv_nonneg.mpr ht_pos.le
      rw [← hv_comb]
      exact (convex_convexHull ℝ _)
        (subset_convexHull ℝ _ (Set.mem_insert_of_mem w hcS))
        (subset_convexHull ℝ _ (Set.mem_insert w S)) h1 h2 (by ring)
    · exact subset_convexHull ℝ _ (Set.mem_insert_of_mem w hxS)

/-- Every configuration of at least `2` points in `closedBall 0 R` is dominated in convex-hull
inclusion by a configuration on `sphere 0 R`. -/
theorem exists_pushOut_range_sphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] {ι : Type*} [Fintype ι] (hcard : 2 ≤ Fintype.card ι) {R : ℝ}
    (v : ι → E) (hv : ∀ i, v i ∈ Metric.closedBall (0 : E) R) :
    ∃ w : ι → E, (∀ i, w i ∈ Metric.sphere (0 : E) R) ∧
      convexHull ℝ (Set.range v) ⊆ convexHull ℝ (Set.range w) := by
  classical
  suffices ∀ n : ℕ, ∀ u : ι → E, (∀ i, u i ∈ Metric.closedBall (0 : E) R) →
      (Finset.univ.filter (fun i => u i ∉ Metric.sphere (0 : E) R)).card ≤ n →
      ∃ w : ι → E, (∀ i, w i ∈ Metric.sphere (0 : E) R) ∧
        convexHull ℝ (Set.range u) ⊆ convexHull ℝ (Set.range w) by
    exact this (Fintype.card ι) v hv (Finset.card_le_univ _)
  intro n
  induction n with
  | zero =>
    intro u _ h0
    refine ⟨u, fun i => ?_, subset_rfl⟩
    by_contra hi
    have hmem : i ∈ Finset.univ.filter (fun j => u j ∉ Metric.sphere (0 : E) R) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    have := Finset.card_pos.mpr ⟨i, hmem⟩
    omega
  | succ n ih =>
    intro u hu hcard_bad
    by_cases hemp : (Finset.univ.filter (fun i => u i ∉ Metric.sphere (0 : E) R)).Nonempty
    · obtain ⟨i₀, hi₀⟩ := hemp
      have hi₀_not : u i₀ ∉ Metric.sphere (0 : E) R := (Finset.mem_filter.mp hi₀).2
      by_cases hdiff : ∃ j : ι, u j ≠ u i₀
      · obtain ⟨j, hj⟩ := hdiff
        obtain ⟨t, ht1, hwt⟩ := exists_ray_mem_sphere (hu i₀) hj.symm
        set q : E := u j + t • (u i₀ - u j)
        let u' : ι → E := Function.update u i₀ q
        have hu'_ball : ∀ i, u' i ∈ Metric.closedBall (0 : E) R := fun i => by
          by_cases hi : i = i₀
          · rw [hi]; simpa [u'] using Metric.sphere_subset_closedBall hwt
          · simp [u', hi, hu i]
        have hu'_bad_sub :
            Finset.univ.filter (fun i => u' i ∉ Metric.sphere (0 : E) R) ⊆
            (Finset.univ.filter (fun i => u i ∉ Metric.sphere (0 : E) R)).erase i₀ := by
          intro i hi
          have hi_not : u' i ∉ Metric.sphere (0 : E) R := (Finset.mem_filter.mp hi).2
          have hne : i ≠ i₀ := by
            intro heq
            rw [heq] at hi_not
            exact hi_not (by simpa [u'] using hwt)
          refine Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩⟩
          simpa [u', hne] using hi_not
        have hu'_card :
            (Finset.univ.filter (fun i => u' i ∉ Metric.sphere (0 : E) R)).card ≤ n := by
          have h1 := Finset.card_le_card hu'_bad_sub
          have h2 := Finset.card_erase_add_one hi₀
          omega
        have hconv_sub : convexHull ℝ (Set.range u) ⊆ convexHull ℝ (Set.range u') := by
          refine convexHull_min ?_ (convex_convexHull ℝ _)
          rintro _ ⟨i, rfl⟩
          by_cases hi : i = i₀
          · rw [hi]
            have ht_pos : 0 < t := by linarith
            have hj_ne : j ≠ i₀ := fun h => hj (congrArg u h)
            have huj_mem : u j ∈ Set.range u' := ⟨j, by simp [u', hj_ne]⟩
            have hq_mem : q ∈ Set.range u' := ⟨i₀, by simp [u']⟩
            have hcomb : (1 - t⁻¹) • u j + t⁻¹ • q = u i₀ := by
              have ht_ne : t ≠ 0 := ht_pos.ne'
              calc
                (1 - t⁻¹) • u j + t⁻¹ • (u j + t • (u i₀ - u j))
                  = (1 - t⁻¹) • u j + t⁻¹ • u j + (t⁻¹ * t) • (u i₀ - u j) := by
                      rw [smul_add, smul_smul, add_assoc]
                _ = ((1 - t⁻¹) + t⁻¹) • u j + (1 : ℝ) • (u i₀ - u j) := by
                      rw [← add_smul, inv_mul_cancel₀ ht_ne]
                _ = u j + (u i₀ - u j) := by simp
                _ = u i₀ := add_sub_cancel _ _
            rw [← hcomb]
            exact (convex_convexHull ℝ _)
              (subset_convexHull ℝ _ huj_mem) (subset_convexHull ℝ _ hq_mem)
              (sub_nonneg.mpr (inv_le_one_of_one_le₀ ht1)) (inv_nonneg.mpr ht_pos.le) (by ring)
          · exact subset_convexHull ℝ _ ⟨i, by simp [u', hi]⟩
        obtain ⟨w, hw_sph, hw_sub⟩ := ih u' hu'_ball hu'_card
        exact ⟨w, hw_sph, hconv_sub.trans hw_sub⟩
      · -- All points equal `p = u i₀`; place `w i₀` and `w j` at the two sphere hits of a line through `p`.
        push Not at hdiff
        set p : E := u i₀
        obtain ⟨x, hx⟩ := exists_ne (0 : E)
        have hne1 : p ≠ p - x := fun h => hx (sub_eq_self.mp h.symm)
        have hne2 : p ≠ p + x := fun h => hx (add_eq_left.mp h.symm)
        obtain ⟨t₁, ht₁, hw₁⟩ := exists_ray_mem_sphere (c := p - x) (hu i₀) hne1
        obtain ⟨t₂, ht₂, hw₂⟩ := exists_ray_mem_sphere (c := p + x) (hu i₀) hne2
        set q₁ : E := (p - x) + t₁ • (p - (p - x))
        set q₂ : E := (p + x) + t₂ • (p - (p + x))
        have hq₁_eq : q₁ = p + (t₁ - 1) • x := by
          dsimp only [q₁]; rw [sub_sub_cancel, sub_smul, one_smul]; abel
        have hq₂_eq : q₂ = p - (t₂ - 1) • x := by
          dsimp only [q₂]; rw [sub_add_cancel_left, smul_neg, sub_smul, one_smul]; abel
        have h1_lt : 1 < t₁ := lt_of_le_of_ne ht₁ fun h => by
          rw [← h, sub_self, zero_smul, add_zero] at hq₁_eq
          exact hi₀_not (hq₁_eq ▸ hw₁)
        have h2_lt : 1 < t₂ := lt_of_le_of_ne ht₂ fun h => by
          rw [← h, sub_self, zero_smul, sub_zero] at hq₂_eq
          exact hi₀_not (hq₂_eq ▸ hw₂)
        let w : ι → E := fun i => if i = i₀ then q₁ else q₂
        have hw_sph : ∀ i, w i ∈ Metric.sphere (0 : E) R := fun i => by
          dsimp only [w]; split_ifs
          · exact hw₁
          · exact hw₂
        have hj_ex : ∃ j : ι, j ≠ i₀ := by
          by_contra hall
          push Not at hall
          have hsub : (Finset.univ : Finset ι) ⊆ {i₀} := fun i _ => Finset.mem_singleton.mpr (hall i)
          have := Finset.card_le_card hsub
          simp only [Finset.card_univ, Finset.card_singleton] at this
          omega
        obtain ⟨j, hj_ne⟩ := hj_ex
        refine ⟨w, hw_sph, convexHull_min ?_ (convex_convexHull ℝ _)⟩
        rintro _ ⟨i, rfl⟩
        rw [hdiff i]
        have ha : 0 < t₁ - 1 := sub_pos.mpr h1_lt
        have hb : 0 < t₂ - 1 := sub_pos.mpr h2_lt
        have hden : 0 < (t₁ - 1) + (t₂ - 1) := add_pos ha hb
        let α : ℝ := (t₂ - 1) / ((t₁ - 1) + (t₂ - 1))
        let β : ℝ := (t₁ - 1) / ((t₁ - 1) + (t₂ - 1))
        have hp_comb : α • q₁ + β • q₂ = p := by
          rw [hq₁_eq, hq₂_eq, smul_add, smul_sub, smul_smul, smul_smul]
          have hαβ : α + β = 1 := by
            dsimp only [α, β]; rw [← add_div, add_comm, div_self hden.ne']
          have hmul : α * (t₁ - 1) = β * (t₂ - 1) := by
            dsimp only [α, β]; ring
          calc
            α • p + (α * (t₁ - 1)) • x + (β • p - (β * (t₂ - 1)) • x)
              = (α + β) • p + (α * (t₁ - 1) - β * (t₂ - 1)) • x := by
                  rw [add_smul, sub_smul]; abel
            _ = p := by rw [hαβ, hmul, sub_self, zero_smul, one_smul, add_zero]
        have hq₁_mem : q₁ ∈ Set.range w := ⟨i₀, by simp [w]⟩
        have hq₂_mem : q₂ ∈ Set.range w := ⟨j, by simp [w, hj_ne]⟩
        rw [← hp_comb]
        exact (convex_convexHull ℝ _)
          (subset_convexHull ℝ _ hq₁_mem)
          (subset_convexHull ℝ _ hq₂_mem)
          (div_nonneg hb.le hden.le) (div_nonneg ha.le hden.le)
          (by dsimp only [α, β]; rw [← add_div, add_comm, div_self hden.ne'])
    · rw [Finset.not_nonempty_iff_eq_empty] at hemp
      refine ⟨u, fun i => ?_, subset_rfl⟩
      by_contra hi
      have hmem : i ∈ Finset.univ.filter (fun j => u j ∉ Metric.sphere (0 : E) R) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      rw [hemp] at hmem
      exact Finset.notMem_empty i hmem

end

end ConvexGeom
