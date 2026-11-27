/-
Copyright (c) 2026 Yegor Gorodzha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yegor Gorodzha
-/
module

public import ConvexGeom.Metric.Projection
public import ConvexGeom.Polytope.Basic
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Radon

import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Combinatorial and Extremal Convex Geometry

Finite-dimensional combinatorial and extremal results built on `ConvexGeom.Metric.Projection`,
`ConvexGeom.Polytope.Basic`, and Mathlib's `Radon`, `Caratheodory`, `Exposed`, and `KreinMilman`.

## Main statements

* `ConvexGeom.radon_partition_card_ge`, `ConvexGeom.radon_partition_fin`: **Radon's Theorem**
  (wrapping Mathlib's `Convex.radon_partition`).
* `ConvexGeom.helly_convexBody`, `ConvexGeom.helly_convexBody_finset`: **Helly's Theorem** for
  `ConvexBody E` (wrapping Mathlib's `Convex.helly_theorem_compact'` / `Convex.helly_theorem`).
* `ConvexGeom.isCompact_convexHull_of_isCompact`, `ConvexGeom.convexHull_extremePoints_eq`:
  **Carathéodory compactness** and **Minkowski–Carathéodory Theorem** (finite-dimensional
  Krein–Milman without closure).
* `ConvexGeom.extremePoints_subset_closure_exposedPoints`,
  `ConvexGeom.closure_convexHull_exposedPoints`: **Straszewicz's Theorem**.
* `ConvexGeom.jung_circumradius_finset`, `ConvexGeom.jung_circumradius`,
  `ConvexGeom.jung_circumradius_convexBody`: **Jung's Circumradius Theorem** with sharp constant
  `√(d / (2 * (d + 1)))`.

## References

* [P. M. Gruber, *Convex and Discrete Geometry*][gruber2007], Ch. 3, 5, 11.
* [R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*][schneider2014], §1.1, §1.4.
-/

open Set Finset
open scoped RealInnerProductSpace

namespace ConvexGeom

public section

/-! ### 1. Radon's Theorem -/

section Radon

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- **Radon's Theorem (general finite index):**
Any family `v : ι → E` of at least `finrank ℝ E + 2` points partitions into two nonempty disjoint
finsets `I, J` (`I ∪ J = univ`) whose convex hulls intersect. -/
theorem radon_partition_card_ge {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Module.finrank ℝ E + 2 ≤ Fintype.card ι) (v : ι → E) :
    ∃ I J : Finset ι, I.Nonempty ∧ J.Nonempty ∧ Disjoint I J ∧ I ∪ J = Finset.univ ∧
      (convexHull ℝ (v '' (I : Set ι)) ∩ convexHull ℝ (v '' (J : Set ι))).Nonempty := by
  have hdep : ¬ AffineIndependent ℝ v := fun h => by
    have h1 := h.card_le_finrank_succ
    have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range v))
    omega
  obtain ⟨I₀, p, hp1, hp2⟩ := Convex.radon_partition hdep
  classical
  let I : Finset ι := I₀.toFinset
  let J : Finset ι := Iᶜ
  have hI_coe : (I : Set ι) = I₀ := Set.coe_toFinset I₀
  have hJ_coe : (J : Set ι) = I₀ᶜ := by
    ext x; simp [J, I]
  have hpI : p ∈ convexHull ℝ (v '' (I : Set ι)) := hI_coe.symm ▸ hp1
  have hpJ : p ∈ convexHull ℝ (v '' (J : Set ι)) := hJ_coe.symm ▸ hp2
  have hI_ne : I.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    simp [hemp] at hpI
  have hJ_ne : J.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    simp [hemp] at hpJ
  exact ⟨I, J, hI_ne, hJ_ne, disjoint_compl_right, Finset.union_compl I, ⟨p, hpI, hpJ⟩⟩

/-- **Radon's Theorem on `Fin (d + 2)`:**
Any `finrank ℝ E + 2` points in `E` partition into two nonempty disjoint subsets whose convex
hulls intersect. -/
theorem radon_partition_fin (v : Fin (Module.finrank ℝ E + 2) → E) :
    ∃ I J : Finset (Fin (Module.finrank ℝ E + 2)),
      I.Nonempty ∧ J.Nonempty ∧ Disjoint I J ∧ I ∪ J = Finset.univ ∧
      (convexHull ℝ (v '' (I : Set _)) ∩ convexHull ℝ (v '' (J : Set _))).Nonempty :=
  radon_partition_card_ge (by simp) v

end Radon

/-! ### 2. Helly's Theorem for `ConvexBody` -/

section Helly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Helly's Theorem for `ConvexBody` (arbitrary family):**
If every subfamily of size at most `finrank ℝ E + 1` has nonempty intersection, then the entire
family has nonempty intersection. -/
theorem helly_convexBody {ι : Type*} (K : ι → ConvexBody E)
    (hinter : ∀ I : Finset ι, I.card ≤ Module.finrank ℝ E + 1 →
      (⋂ i ∈ I, (K i : Set E)).Nonempty) :
    (⋂ i, (K i : Set E)).Nonempty :=
  Convex.helly_theorem_compact' (𝕜 := ℝ) (fun i => (K i).convex) (fun i => (K i).isCompact) hinter

/-- **Helly's Theorem for `ConvexBody` (classical finite form):**
If `F` is a finset of at least `finrank ℝ E + 1` convex bodies and every `(d + 1)`-element
subcollection intersects nontrivially, then all bodies in `F` have a common point. -/
theorem helly_convexBody_finset (F : Finset (ConvexBody E))
    (hcard : Module.finrank ℝ E + 1 ≤ F.card)
    (hinter : ∀ G ⊆ F, G.card = Module.finrank ℝ E + 1 →
      (⋂ K ∈ G, (K : Set E)).Nonempty) :
    (⋂ K ∈ F, (K : Set E)).Nonempty :=
  Convex.helly_theorem (𝕜 := ℝ) (F := fun K : ConvexBody E => (K : Set E))
    hcard (fun K _ => K.convex) hinter

end Helly

/-! ### 3. Compactness of Convex Hull and Minkowski–Carathéodory Theorem -/

section MinkowskiCaratheodory

/-- **Carathéodory compactness:** in a finite-dimensional real normed space, the convex hull of a
compact set is compact. -/
theorem isCompact_convexHull_of_isCompact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} (hSc : IsCompact S) :
    IsCompact (convexHull ℝ S) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  set N : ℕ := Module.finrank ℝ E + 1
  let Δ : Set (Fin N → ℝ) := {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}
  have hΔ_compact : IsCompact Δ := by
    have hΔ_eq :
        Δ = Set.range (fun t : Convexity.StdSimplex ℝ (Fin N) => (t.weights : Fin N → ℝ)) := by
      ext w
      constructor
      · rintro ⟨hnn, hsum⟩
        refine ⟨⟨Finsupp.equivFunOnFinite.symm w, fun i => hnn i, ?_⟩, rfl⟩
        simpa [Finsupp.sum_fintype] using hsum
      · rintro ⟨t, rfl⟩
        exact ⟨t.weights_nonneg, by simp⟩
    rw [hΔ_eq]
    exact isCompact_range
      (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin N)).continuous
  have hSn_compact : IsCompact (Set.univ.pi fun _ : Fin N => S) :=
    isCompact_univ_pi fun _ => hSc
  let Φ : (Fin N → ℝ) × (Fin N → E) → E := fun p => ∑ i : Fin N, p.1 i • p.2 i
  have hΦ_cont : Continuous Φ := by fun_prop
  have himg_eq : Φ '' (Δ ×ˢ (Set.univ.pi fun _ : Fin N => S)) = convexHull ℝ S := by
    apply Set.Subset.antisymm
    · rintro _ ⟨⟨w, x⟩, ⟨hw, hx⟩, rfl⟩
      have hcm : Finset.univ.centerMass w x = ∑ i : Fin N, w i • x i :=
        Finset.univ.centerMass_eq_of_sum_1 x hw.2
      dsimp only [Φ]
      rw [← hcm]
      exact Finset.centerMass_mem_convexHull Finset.univ (fun i _ => hw.1 i)
        (by rw [hw.2]; exact zero_lt_one) (fun i _ => hx i (mem_univ i))
    · intro y hy
      rw [convexHull_eq_union] at hy
      simp only [mem_iUnion, exists_prop] at hy
      obtain ⟨t, htS, ht_ind, hyt⟩ := hy
      rw [t.convexHull_eq] at hyt
      obtain ⟨c, hc0, hc1, rfl⟩ := hyt
      have hcard_le : t.card ≤ N := by
        have h1 := ht_ind.card_le_finrank_succ
        have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : t → E)))
        simp only [Fintype.card_coe] at h1
        omega
      let e : t ≃ Fin t.card := t.equivFin
      let w : Fin N → ℝ := fun i =>
        if hi : i.1 < t.card then c (e.symm ⟨i.1, hi⟩).1 else 0
      let x : Fin N → E := fun i =>
        if hi : i.1 < t.card then (e.symm ⟨i.1, hi⟩).1 else x₀
      have hw_nonneg : ∀ i, 0 ≤ w i := fun i => by
        dsimp only [w]; split_ifs with hi
        · exact hc0 _ (e.symm ⟨i.1, hi⟩).2
        · exact le_rfl
      have hw_sum : ∑ i : Fin N, w i = 1 := by
        have h1 : ∑ i : Fin N, w i = ∑ j : Fin t.card, c (e.symm j).1 := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin N => i.1 < t.card)]
          have hzero : ∑ i ∈ Finset.univ.filter (fun i : Fin N => ¬ i.1 < t.card), w i = 0 :=
            Finset.sum_eq_zero fun i hi => by
              have hnot := (Finset.mem_filter.mp hi).2
              simp [w, hnot]
          rw [hzero, add_zero]
          refine Finset.sum_bij (fun i hi => ⟨i.1, (Finset.mem_filter.mp hi).2⟩) ?_ ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro a _ b _ hab; exact Fin.ext (by simpa using congrArg Fin.val hab)
          · intro j _
            refine ⟨⟨j.1, Nat.lt_of_lt_of_le j.2 hcard_le⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.2⟩, rfl⟩
          · intro i hi
            have hlt := (Finset.mem_filter.mp hi).2
            simp [w, hlt]
        rw [h1, Equiv.sum_comp e.symm (fun a : t => c a.1), Finset.univ_eq_attach,
          Finset.sum_attach t c, hc1]
      have hx_mem : x ∈ Set.univ.pi fun _ : Fin N => S := fun i _ => by
        dsimp only [x]; split_ifs with hi
        · exact htS (e.symm ⟨i.1, hi⟩).2
        · exact hx₀
      refine ⟨(w, x), ⟨⟨hw_nonneg, hw_sum⟩, hx_mem⟩, ?_⟩
      change ∑ i : Fin N, w i • x i = t.centerMass c id
      rw [t.centerMass_eq_of_sum_1 id hc1]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin N => i.1 < t.card)]
      have hzero : ∑ i ∈ Finset.univ.filter (fun i : Fin N => ¬ i.1 < t.card), w i • x i = 0 :=
        Finset.sum_eq_zero fun i hi => by
          have hnot := (Finset.mem_filter.mp hi).2
          simp [w, hnot]
      rw [hzero, add_zero]
      have hbij : ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.1 < t.card), w i • x i =
          ∑ j : Fin t.card, c (e.symm j).1 • (e.symm j).1 := by
        refine Finset.sum_bij (fun i hi => ⟨i.1, (Finset.mem_filter.mp hi).2⟩) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro a _ b _ hab; exact Fin.ext (by simpa using congrArg Fin.val hab)
        · intro j _
          refine ⟨⟨j.1, Nat.lt_of_lt_of_le j.2 hcard_le⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.2⟩, rfl⟩
        · intro i hi
          have hlt := (Finset.mem_filter.mp hi).2
          simp [w, x, hlt]
      rw [hbij, Equiv.sum_comp e.symm (fun a : t => c a.1 • a.1), Finset.univ_eq_attach,
        Finset.sum_attach t (fun a => c a • a)]
      rfl
  rw [← himg_eq]
  exact (hΔ_compact.prod hSn_compact).image hΦ_cont

/-- Helper for Minkowski–Carathéodory: if `y ∈ K` is a boundary point of a compact convex set `K`
along a direction `v ∈ vectorSpan ℝ K` (`y + t • v ∉ K` for all `t > 0`), then `y` lies in a
compact convex extreme subset `F ⊆ K` of strictly smaller affine dimension. -/
private lemma exists_extreme_face_finrank_lt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hKc : IsCompact K) (hKconv : Convex ℝ K)
    {y v : E} (hyK : y ∈ K) (hv_span : v ∈ vectorSpan ℝ K) (hv_ne : v ≠ 0)
    (hray : ∀ t : ℝ, 0 < t → y + t • v ∉ K) :
    ∃ F : Set E, IsCompact F ∧ Convex ℝ F ∧ IsExtreme ℝ K F ∧ y ∈ F ∧
      Module.finrank ℝ (vectorSpan ℝ F) < Module.finrank ℝ (vectorSpan ℝ K) := by
  let W : Submodule ℝ E := vectorSpan ℝ K
  let KW : Set W := {w : W | y + (w : E) ∈ K}
  have hKW_comp : IsCompact KW := by
    have hcont : Continuous (fun w : W => y + (w : E)) :=
      continuous_const.add continuous_subtype_val
    have hclosed : IsClosed KW := hKc.isClosed.preimage hcont
    obtain ⟨R, hR⟩ := hKc.isBounded.subset_closedBall y
    have hsub : KW ⊆ Metric.closedBall (0 : W) R := fun w hw => by
      have hmem : y + (w : E) ∈ Metric.closedBall y R := hR hw
      simpa [Metric.mem_closedBall, dist_eq_norm] using hmem
    exact (isCompact_closedBall (0 : W) R).of_isClosed_subset hclosed hsub
  have hKW_conv : Convex ℝ KW := fun w₁ hw₁ w₂ hw₂ a b ha hb hab => by
    change y + ((a • w₁ + b • w₂ : W) : E) ∈ K
    have heq : y + ((a • w₁ + b • w₂ : W) : E) = a • (y + (w₁ : E)) + b • (y + (w₂ : E)) := by
      simp only [Submodule.coe_add, Submodule.coe_smul_of_tower]
      conv_lhs => rw [show y = (a + b) • y by rw [hab, one_smul]]
      module
    rw [heq]
    exact hKconv hw₁ hw₂ ha hb hab
  have h0_mem : (0 : W) ∈ KW := by simpa [KW] using hyK
  let Kbody : ConvexBody W := ⟨KW, hKW_conv, hKW_comp, ⟨0, h0_mem⟩⟩
  have h0_not_int : (0 : W) ∉ interior (Kbody : Set W) := by
    intro hint
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior (0 : W) hint
    let t : ℝ := (ε / 2) / ‖v‖
    have ht_pos : 0 < t := div_pos (half_pos hε) (norm_pos_iff.mpr hv_ne)
    let w : W := ⟨t • v, W.smul_mem t hv_span⟩
    have hw_ball : w ∈ Metric.ball (0 : W) ε := by
      rw [Metric.mem_ball, dist_zero_right]
      change ‖t • v‖ < ε
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
      dsimp only [t]
      rw [div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hv_ne)]
      linarith
    have hw_mem : w ∈ (Kbody : Set W) := interior_subset (hball hw_ball)
    exact hray t ht_pos hw_mem
  have h0_front : (0 : W) ∈ frontier (Kbody : Set W) :=
    ⟨subset_closure h0_mem, h0_not_int⟩
  obtain ⟨u, hu_norm, hu_nc⟩ := exists_supporting_normal_of_mem_frontier Kbody h0_front
  have hu_ne : (u : E) ≠ 0 := by
    intro h0
    have : ‖u‖ = 0 := by change ‖(u : E)‖ = 0; simp [h0]
    linarith
  let l : StrongDual ℝ E := innerSL ℝ (u : E)
  let F : Set E := l.toExposed K
  have hF_exp : IsExposed ℝ K F := ContinuousLinearMap.toExposed.isExposed
  have hF_ext : IsExtreme ℝ K F := hF_exp.isExtreme
  have hF_comp : IsCompact F := hF_exp.isCompact hKc
  have hF_conv : Convex ℝ F := hF_exp.convex hKconv
  have hle_y : ∀ z ∈ K, ⟪z, (u : E)⟫ ≤ ⟪y, (u : E)⟫ := by
    intro z hz
    have hzy_W : z - y ∈ W := vsub_mem_vectorSpan ℝ hz hyK
    have hmem : (⟨z - y, hzy_W⟩ : W) ∈ Kbody := by
      change y + (z - y) ∈ K; simpa [add_sub_cancel] using hz
    have hle := hu_nc ⟨z - y, hzy_W⟩ hmem
    change ⟪(⟨z - y, hzy_W⟩ : W) - 0, u⟫ ≤ 0 at hle
    rw [sub_zero] at hle
    change ⟪z - y, (u : E)⟫ ≤ 0 at hle
    rw [inner_sub_left] at hle
    linarith
  have hyF : y ∈ F := ⟨hyK, fun z hz => by
    change ⟪(u : E), z⟫ ≤ ⟪(u : E), y⟫
    simpa [real_inner_comm] using hle_y z hz⟩
  have hspan_le : vectorSpan ℝ F ≤ W := vectorSpan_mono ℝ hF_exp.subset
  have hspan_orth : vectorSpan ℝ F ≤ (ℝ ∙ (u : E))ᗮ := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨z₁, hz₁, z₂, hz₂, rfl⟩
    change z₁ -ᵥ z₂ ∈ (ℝ ∙ (u : E))ᗮ
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    have h1 : ⟪(u : E), z₁⟫ = ⟪(u : E), y⟫ :=
      le_antisymm (hyF.2 z₁ hz₁.1) (hz₁.2 y hyK)
    have h2 : ⟪(u : E), z₂⟫ = ⟪(u : E), y⟫ :=
      le_antisymm (hyF.2 z₂ hz₂.1) (hz₂.2 y hyK)
    rw [vsub_eq_sub, inner_sub_right, h1, h2, sub_self]
  have hspan_lt : vectorSpan ℝ F < W := lt_of_le_of_ne hspan_le fun heq => by
    have hu_orth : (u : E) ∈ (ℝ ∙ (u : E))ᗮ := hspan_orth (by rw [heq]; exact u.2)
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_self_eq_norm_sq] at hu_orth
    exact hu_ne (norm_eq_zero.mp (sq_eq_zero_iff.mp hu_orth))
  exact ⟨F, hF_comp, hF_conv, hF_ext, hyF, Submodule.finrank_lt_finrank_of_lt hspan_lt⟩

/-- **Minkowski–Carathéodory Theorem:**
In a finite-dimensional real inner product space, every compact convex set is the convex hull
(without taking closure) of its extreme points. -/
theorem convexHull_extremePoints_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hKc : IsCompact K) (hKconv : Convex ℝ K) :
    convexHull ℝ (K.extremePoints ℝ) = K := by
  apply Set.Subset.antisymm (convexHull_min extremePoints_subset hKconv)
  suffices ∀ n : ℕ, ∀ S : Set E, IsCompact S → Convex ℝ S →
      Module.finrank ℝ (vectorSpan ℝ S) ≤ n → S ⊆ convexHull ℝ (S.extremePoints ℝ) by
    exact this (Module.finrank ℝ (vectorSpan ℝ K)) K hKc hKconv le_rfl
  intro n
  induction n with
  | zero =>
    intro S _ _ hdim x hx
    have hbot : vectorSpan ℝ S = ⊥ := Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hdim)
    have hsub : S ⊆ {x} := fun z hz => by
      have : z -ᵥ x ∈ vectorSpan ℝ S := vsub_mem_vectorSpan ℝ hz hx
      rw [hbot, Submodule.mem_bot, vsub_eq_zero_iff_eq] at this
      exact this
    have hx_ext : x ∈ S.extremePoints ℝ := ⟨hx, fun x₁ hx₁ _ _ _ => hsub hx₁⟩
    exact subset_convexHull ℝ _ hx_ext
  | succ n ih =>
    intro S hSc hSconv hdim x hx
    by_cases hx_ext : x ∈ S.extremePoints ℝ
    · exact subset_convexHull ℝ _ hx_ext
    · rw [mem_extremePoints] at hx_ext
      push Not at hx_ext
      obtain ⟨a, haS, b, hbS, hx_open, hne⟩ := hx_ext hx
      obtain ⟨α, β, hα, hβ, hαβ, hab_eq⟩ := hx_open
      set v : E := b - a
      have hv_ne : v ≠ 0 := by
        intro hv0
        have hab : b = a := sub_eq_zero.mp hv0
        have hax : a = x := by
          rw [← hab_eq, hab, ← add_smul, hαβ, one_smul]
        exact hne hax (hab.trans hax)
      have hv_span : v ∈ vectorSpan ℝ S := vsub_mem_vectorSpan ℝ hbS haS
      let T : Set ℝ := {t : ℝ | x + t • v ∈ S}
      have hT_comp : IsCompact T := by
        have hcont : Continuous (fun t : ℝ => x + t • v) :=
          continuous_const.add (continuous_id.smul continuous_const)
        have hclosed : IsClosed T := hSc.isClosed.preimage hcont
        obtain ⟨R, hR⟩ := hSc.isBounded.subset_closedBall x
        have hsub : T ⊆ Set.Icc (-(R / ‖v‖)) (R / ‖v‖) := fun t ht => by
          have hmem : ‖(x + t • v) - x‖ ≤ R := by
            simpa [Metric.mem_closedBall, dist_eq_norm] using hR ht
          rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at hmem
          have hle : |t| ≤ R / ‖v‖ := (le_div_iff₀ (norm_pos_iff.mpr hv_ne)).mpr hmem
          exact abs_le.mp hle
        exact isCompact_Icc.of_isClosed_subset hclosed hsub
      have h0T : (0 : ℝ) ∈ T := by simpa [T] using hx
      have hposT : α ∈ T := by
        change x + α • (b - a) ∈ S
        have heq : x + α • (b - a) = b := by
          rw [← hab_eq]
          conv_rhs => rw [show b = (α + β) • b by rw [hαβ, one_smul]]
          module
        rw [heq]; exact hbS
      have hnegT : (-β) ∈ T := by
        change x + (-β) • (b - a) ∈ S
        have heq : x + (-β) • (b - a) = a := by
          rw [← hab_eq]
          conv_rhs => rw [show a = (α + β) • a by rw [hαβ, one_smul]]
          module
        rw [heq]; exact haS
      set tMax : ℝ := sSup T
      set tMin : ℝ := sInf T
      have htMax_mem : tMax ∈ T := hT_comp.sSup_mem ⟨0, h0T⟩
      have htMin_mem : tMin ∈ T := hT_comp.sInf_mem ⟨0, h0T⟩
      have htMax_pos : 0 < tMax := lt_of_lt_of_le hα (le_csSup hT_comp.bddAbove hposT)
      have htMin_neg : tMin < 0 :=
        lt_of_le_of_lt (csInf_le hT_comp.bddBelow hnegT) (neg_lt_zero.mpr hβ)
      set y₁ : E := x + tMin • v
      set y₂ : E := x + tMax • v
      have hray₂ : ∀ t : ℝ, 0 < t → y₂ + t • v ∉ S := fun t ht hmem => by
        have htT : tMax + t ∈ T := by
          change x + (tMax + t) • v ∈ S
          rwa [add_smul, ← add_assoc]
        have hle := le_csSup hT_comp.bddAbove htT
        linarith
      have hray₁ : ∀ t : ℝ, 0 < t → y₁ + t • (-v) ∉ S := fun t ht hmem => by
        have htT : tMin - t ∈ T := by
          change x + (tMin - t) • v ∈ S
          have heq : x + (tMin - t) • v = y₁ + t • (-v) := by
            dsimp only [y₁]; rw [sub_smul, smul_neg]; abel
          rwa [heq]
        have hle := csInf_le hT_comp.bddBelow htT
        linarith
      obtain ⟨F₂, hF₂c, hF₂conv, hF₂ext, hy₂F, hF₂dim⟩ :=
        exists_extreme_face_finrank_lt hSc hSconv htMax_mem hv_span hv_ne hray₂
      obtain ⟨F₁, hF₁c, hF₁conv, hF₁ext, hy₁F, hF₁dim⟩ :=
        exists_extreme_face_finrank_lt hSc hSconv htMin_mem (Submodule.neg_mem _ hv_span)
          (neg_ne_zero.mpr hv_ne) hray₁
      have hy₁_mem : y₁ ∈ convexHull ℝ (S.extremePoints ℝ) :=
        convexHull_mono hF₁ext.extremePoints_subset_extremePoints
          (ih F₁ hF₁c hF₁conv (by omega) hy₁F)
      have hy₂_mem : y₂ ∈ convexHull ℝ (S.extremePoints ℝ) :=
        convexHull_mono hF₂ext.extremePoints_subset_extremePoints
          (ih F₂ hF₂c hF₂conv (by omega) hy₂F)
      have hden : 0 < tMax - tMin := by linarith
      let c₁ : ℝ := tMax / (tMax - tMin)
      let c₂ : ℝ := (-tMin) / (tMax - tMin)
      have hx_comb : c₁ • y₁ + c₂ • y₂ = x := by
        dsimp only [y₁, y₂, c₁, c₂]
        rw [smul_add, smul_add, smul_smul, smul_smul]
        have hsum1 : tMax / (tMax - tMin) + -tMin / (tMax - tMin) = 1 := by
          field_simp [hden.ne']; ring
        have hsum2 : tMax / (tMax - tMin) * tMin + -tMin / (tMax - tMin) * tMax = 0 := by
          field_simp [hden.ne']; ring
        calc
          (tMax / (tMax - tMin)) • x + (tMax / (tMax - tMin) * tMin) • v +
              ((-tMin / (tMax - tMin)) • x + (-tMin / (tMax - tMin) * tMax) • v)
            = (tMax / (tMax - tMin) + -tMin / (tMax - tMin)) • x +
              (tMax / (tMax - tMin) * tMin + -tMin / (tMax - tMin) * tMax) • v := by
                rw [add_smul, add_smul]; abel
          _ = x := by rw [hsum1, hsum2, one_smul, zero_smul, add_zero]
      rw [← hx_comb]
      exact (convex_convexHull ℝ _) hy₁_mem hy₂_mem
        (div_nonneg htMax_pos.le hden.le) (div_nonneg (by linarith) hden.le)
        (by dsimp only [c₁, c₂]; field_simp [hden.ne']; ring)

end MinkowskiCaratheodory

/-! ### 4. Straszewicz's Theorem -/

section Straszewicz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Any point `y ∈ S` maximizing the Euclidean distance `‖z - p‖` to a fixed point `p` is an
exposed point of `S`. -/
theorem mem_exposedPoints_of_isMaxOn_norm_sub {S : Set E} {p y : E}
    (hyS : y ∈ S) (hmax : ∀ z ∈ S, ‖z - p‖ ≤ ‖y - p‖) :
    y ∈ S.exposedPoints ℝ := by
  refine ⟨hyS, innerSL ℝ (y - p), fun z hz => ?_⟩
  change ⟪y - p, z⟫ ≤ ⟪y - p, y⟫ ∧ (⟪y - p, y⟫ ≤ ⟪y - p, z⟫ → z = y)
  have hnorm_le : ‖z - p‖ ^ 2 ≤ ‖y - p‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hmax z hz) 2
  have hcs : ⟪y - p, z - p⟫ ≤ ‖y - p‖ ^ 2 := by
    calc
      ⟪y - p, z - p⟫ ≤ ‖y - p‖ * ‖z - p‖ := real_inner_le_norm (y - p) (z - p)
      _ ≤ ‖y - p‖ * ‖y - p‖ := mul_le_mul_of_nonneg_left (hmax z hz) (norm_nonneg _)
      _ = ‖y - p‖ ^ 2 := (sq ‖y - p‖).symm
  have hdiff : ⟪y - p, z⟫ - ⟪y - p, y⟫ = ⟪y - p, z - p⟫ - ‖y - p‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (y - p), inner_sub_right, inner_sub_right]
    ring
  refine ⟨by linarith, fun hge => ?_⟩
  have hinner_ge : ‖y - p‖ ^ 2 ≤ ⟪y - p, z - p⟫ := by linarith
  have hsq_le : ‖z - y‖ ^ 2 ≤ 0 := by
    have hexp : ‖z - y‖ ^ 2 = ‖z - p‖ ^ 2 - 2 * ⟪y - p, z - p⟫ + ‖y - p‖ ^ 2 := by
      have : z - y = (z - p) - (y - p) := by abel
      rw [this, norm_sub_sq_real, real_inner_comm (z - p) (y - p)]
    linarith
  have hzero : ‖z - y‖ = 0 := by nlinarith [norm_nonneg (z - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- **Straszewicz's Theorem:**
In a finite-dimensional real inner product space, every extreme point of a compact convex set
lies in the closure of its exposed points. -/
theorem extremePoints_subset_closure_exposedPoints [FiniteDimensional ℝ E]
    {K : Set E} (hKc : IsCompact K) (hKconv : Convex ℝ K) :
    K.extremePoints ℝ ⊆ closure (K.exposedPoints ℝ) := by
  intro x hx_ext
  rw [Metric.mem_closure_iff]
  intro ε hε
  let Kout : Set E := K \ Metric.ball x ε
  by_cases hemp : Kout.Nonempty
  · have hKout_comp : IsCompact Kout :=
      hKc.of_isClosed_subset (hKc.isClosed.sdiff Metric.isOpen_ball) Set.sdiff_subset
    let C : Set E := convexHull ℝ Kout
    have hC_comp : IsCompact C := isCompact_convexHull_of_isCompact hKout_comp
    have hC_conv : Convex ℝ C := convex_convexHull ℝ Kout
    have hC_ne : C.Nonempty := hemp.convexHull
    have hx_not_C : x ∉ C := by
      have hconv_sdiff : Convex ℝ (K \ {x}) :=
        (hKconv.mem_extremePoints_iff_convex_sdiff.mp hx_ext).2
      have hsub : Kout ⊆ K \ {x} := fun z ⟨hzK, hzball⟩ =>
        ⟨hzK, fun hzx => hzball (hzx ▸ Metric.mem_ball_self hε)⟩
      exact fun hxC => (convexHull_min hsub hconv_sdiff hxC).2 rfl
    -- Separate `x` from `C` via `metricProj` onto `C`.
    let Cbody : ConvexBody E := ⟨C, hC_conv, hC_comp, hC_ne⟩
    let p₀ : E := metricProj Cbody x
    have hp₀C : p₀ ∈ C := metricProj_mem Cbody x
    let u : E := x - p₀
    have hu_ne : u ≠ 0 := fun h0 => hx_not_C (sub_eq_zero.mp h0 ▸ hp₀C)
    have hu_pos : 0 < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu_ne) 2
    have hsep : ∀ z ∈ C, ⟪z - x, u⟫ ≤ -‖u‖ ^ 2 := by
      intro z hz
      have h1 : ⟪x - p₀, z - p₀⟫ ≤ 0 := inner_sub_metricProj_le_zero Cbody x hz
      have h2 : ⟪z - x, u⟫ = ⟪u, z - p₀⟫ - ‖u‖ ^ 2 := by
        rw [show z - x = (z - p₀) - u by simp [u], inner_sub_left, real_inner_self_eq_norm_sq,
          real_inner_comm]
      linarith
    obtain ⟨R, hR⟩ := hKc.isBounded.subset_closedBall x
    let t : ℝ := (R ^ 2 + 1) / (2 * ‖u‖ ^ 2)
    have ht_pos : 0 < t := by positivity
    let p : E := x - t • u
    have hcont : ContinuousOn (fun z : E => ‖z - p‖) K :=
      (continuous_id.sub continuous_const).norm.continuousOn
    obtain ⟨y, hyK, hy_max⟩ := hKc.exists_isMaxOn ⟨x, hx_ext.1⟩ hcont
    have hy_exp : y ∈ K.exposedPoints ℝ := mem_exposedPoints_of_isMaxOn_norm_sub hyK hy_max
    have hy_not_C : y ∉ C := by
      intro hyC
      have hyx_le : ‖y - x‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hR hyK
      have hsq : ‖y - p‖ ^ 2 < ‖x - p‖ ^ 2 := by
        have h1 : y - p = (y - x) + t • u := by simp [p]; abel
        have h2 : x - p = t • u := by simp [p]
        rw [h1, h2, norm_add_sq_real, inner_smul_right]
        have h3 : ‖y - x‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hyx_le 2
        have h4 : 2 * t * ⟪y - x, u⟫ ≤ -(R ^ 2 + 1) := by
          have h5 := hsep y hyC
          have h6 : 2 * t * ‖u‖ ^ 2 = R ^ 2 + 1 := by
            dsimp only [t]; field_simp [hu_pos.ne']
          nlinarith
        linarith
      have hlt : ‖y - p‖ < ‖x - p‖ := by nlinarith [norm_nonneg (y - p), norm_nonneg (x - p)]
      exact hlt.not_ge (hy_max hx_ext.1)
    have hy_ball : y ∈ Metric.ball x ε := by
      by_contra hnot
      exact hy_not_C (subset_convexHull ℝ Kout ⟨hyK, hnot⟩)
    exact ⟨y, hy_exp, by simpa [Metric.mem_ball, dist_comm] using hy_ball⟩
  · -- `K ⊆ ball x ε`, so any exposed point (e.g. a furthest point from `x`) lies in `ball x ε`.
    have hKsub : K ⊆ Metric.ball x ε := by
      intro z hz
      by_contra hnot
      exact hemp ⟨z, hz, hnot⟩
    have hcont : ContinuousOn (fun z : E => ‖z - x‖) K :=
      (continuous_id.sub continuous_const).norm.continuousOn
    obtain ⟨y, hyK, hy_max⟩ := hKc.exists_isMaxOn ⟨x, hx_ext.1⟩ hcont
    exact ⟨y, mem_exposedPoints_of_isMaxOn_norm_sub hyK hy_max,
      by simpa [Metric.mem_ball, dist_comm] using hKsub hyK⟩

/-- **Straszewicz's Theorem (closed convex hull form):**
Every compact convex set in a finite-dimensional real inner product space is the closed convex
hull of its exposed points. -/
theorem closure_convexHull_exposedPoints [FiniteDimensional ℝ E]
    {K : Set E} (hKc : IsCompact K) (hKconv : Convex ℝ K) :
    closure (convexHull ℝ (K.exposedPoints ℝ)) = K := by
  apply Set.Subset.antisymm
  · exact closure_minimal (convexHull_min exposedPoints_subset hKconv) hKc.isClosed
  · conv_lhs => rw [← closure_convexHull_extremePoints hKc hKconv]
    refine closure_minimal ?_ isClosed_closure
    refine convexHull_min ?_ (convex_convexHull ℝ _).closure
    exact (extremePoints_subset_closure_exposedPoints hKc hKconv).trans
      (closure_mono (subset_convexHull ℝ _))

end Straszewicz

/-! ### 5. Jung's Circumradius Theorem -/

section Jung

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- **Jung's Theorem for `≤ d + 1` points:**
Any nonempty finite set `T` of at most `finrank ℝ E + 1` points of diameter `≤ D` is contained
in a closed ball of radius `√(d / (2 * (d + 1))) * D` centered in `convexHull ℝ T`. -/
theorem jung_circumradius_finset {T : Finset E} (hTne : T.Nonempty)
    (hTcard : T.card ≤ Module.finrank ℝ E + 1) {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ x ∈ T, ∀ y ∈ T, ‖x - y‖ ≤ D) :
    ∃ c ∈ convexHull ℝ (T : Set E),
      ∀ x ∈ T,
        ‖x - c‖ ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) / (2 * (Module.finrank ℝ E + 1))) * D := by
  classical
  set d : ℕ := Module.finrank ℝ E
  set R_bound : ℝ := Real.sqrt ((d : ℝ) / (2 * (d + 1))) * D
  -- Minimize `f(c) = max_{x ∈ T} ‖x - c‖` over the compact set `conv(T)`.
  let f : E → ℝ := fun c => T.sup' hTne fun x => ‖x - c‖
  have hf_cont : Continuous f := by
    change Continuous (fun c => T.sup' hTne fun x => ‖x - c‖)
    clear hTcard hdiam
    induction hTne using Finset.Nonempty.cons_induction with
    | singleton a => simpa using (continuous_const.sub continuous_id).norm
    | cons a s has hs ih =>
      simp only [Finset.sup'_cons hs]
      exact ((continuous_const.sub continuous_id).norm).max ih
  have hconv_comp : IsCompact (convexHull ℝ (T : Set E)) := T.finite_toSet.isCompact_convexHull ℝ
  obtain ⟨c, hc_conv, hc_min⟩ :=
    hconv_comp.exists_isMinOn hTne.to_set.convexHull hf_cont.continuousOn
  set r : ℝ := f c
  have hr_nonneg : 0 ≤ r := by
    obtain ⟨x₀, hx₀⟩ := hTne
    exact (norm_nonneg (x₀ - c)).trans (Finset.le_sup' (f := fun x => ‖x - c‖) hx₀)
  refine ⟨c, hc_conv, fun x hx => (Finset.le_sup' (f := fun y => ‖y - c‖) hx).trans ?_⟩
  change r ≤ R_bound
  by_cases hr0 : r = 0
  · rw [hr0]; positivity
  have hr_pos : 0 < r := lt_of_le_of_ne hr_nonneg (Ne.symm hr0)
  -- Active vertices `T₀ = {x ∈ T | ‖x - c‖ = r}`.
  let T₀ : Finset E := T.filter fun x => ‖x - c‖ = r
  have hT₀_ne : T₀.Nonempty := by
    obtain ⟨x₀, hx₀, hx₀_eq⟩ := Finset.exists_mem_eq_sup' hTne fun x => ‖x - c‖
    exact ⟨x₀, Finset.mem_filter.mpr ⟨hx₀, hx₀_eq.symm⟩⟩
  -- Key step: `c ∈ convexHull ℝ T₀` (otherwise moving toward `metricProj (conv T₀) c` lowers `f`).
  have hc_in_T₀ : c ∈ convexHull ℝ (T₀ : Set E) := by
    by_contra hc_not
    let P₀ : ConvexBody E := bodyConvexHull T₀ hT₀_ne
    let p : E := metricProj P₀ c
    have hp_mem : p ∈ convexHull ℝ (T₀ : Set E) := by
      have h : p ∈ (P₀ : Set E) := metricProj_mem P₀ c
      rwa [coe_bodyConvexHull] at h
    let u : E := p - c
    have hu_ne : u ≠ 0 := fun h0 => hc_not (sub_eq_zero.mp h0 ▸ hp_mem)
    have hu_sq_pos : 0 < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu_ne) 2
    have hinner_ge : ∀ x ∈ T₀, ‖u‖ ^ 2 ≤ ⟪x - c, u⟫ := by
      intro x hx
      have hxP₀ : x ∈ (P₀ : Set E) := by
        rw [coe_bodyConvexHull]; exact subset_convexHull ℝ _ hx
      have h1 : ⟪c - p, x - p⟫ ≤ 0 := inner_sub_metricProj_le_zero P₀ c hxP₀
      have h2 : ⟪x - c, u⟫ = ‖u‖ ^ 2 - ⟪c - p, x - p⟫ := by
        have hcp : c - p = -u := by simp [u]
        have hxp : x - p = (x - c) - u := by simp [u]
        rw [hcp, hxp, inner_neg_left, inner_sub_right u, real_inner_self_eq_norm_sq,
          real_inner_comm u (x - c)]
        ring
      linarith
    -- Non-active vertices stay strictly below `r` on a uniform margin `δ > 0`.
    let T₁ : Finset E := T.filter fun x => ‖x - c‖ ≠ r
    have hδ_ex : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ T₁, ‖x - c‖ + δ < r := by
      by_cases hT₁ : T₁.Nonempty
      · set M₁ : ℝ := T₁.sup' hT₁ fun x => ‖x - c‖
        obtain ⟨x₁, hx₁, hx₁_eq⟩ := Finset.exists_mem_eq_sup' hT₁ fun x => ‖x - c‖
        have hlt : M₁ < r := by
          dsimp only [M₁]; rw [hx₁_eq]
          exact lt_of_le_of_ne (Finset.le_sup' (f := fun x => ‖x - c‖) (Finset.mem_filter.mp hx₁).1)
            (Finset.mem_filter.mp hx₁).2
        refine ⟨(r - M₁) / 2, by linarith, fun x hx => ?_⟩
        have hle : ‖x - c‖ ≤ M₁ := Finset.le_sup' (f := fun y => ‖y - c‖) hx
        linarith
      · rw [Finset.not_nonempty_iff_eq_empty] at hT₁
        exact ⟨1, zero_lt_one, fun x hx => (by simp [hT₁] at hx)⟩
    obtain ⟨δ, hδ_pos, hδ_lt⟩ := hδ_ex
    set t : ℝ := min (1 / 2) (δ / ‖u‖)
    have ht_pos : 0 < t := lt_min (by norm_num) (div_pos hδ_pos (norm_pos_iff.mpr hu_ne))
    have ht_le_half : t ≤ 1 / 2 := min_le_left _ _
    let c' : E := (1 - t) • c + t • p
    have hc'_conv : c' ∈ convexHull ℝ (T : Set E) := by
      have hpT : p ∈ convexHull ℝ (T : Set E) :=
        convexHull_mono (Finset.coe_subset.mpr (Finset.filter_subset _ T)) hp_mem
      exact (convex_convexHull ℝ _) hc_conv hpT (by linarith) ht_pos.le (by ring)
    have hc'_lt : f c' < r := by
      rw [Finset.sup'_lt_iff]
      intro x hx
      have hdiff : x - c' = (x - c) - t • u := by
        dsimp only [c', u]; rw [sub_smul, one_smul, smul_sub]; abel
      by_cases hx₀ : x ∈ T₀
      · have hnorm_eq : ‖x - c‖ = r := (Finset.mem_filter.mp hx₀).2
        have hsq_lt : ‖x - c'‖ ^ 2 < r ^ 2 := by
          rw [hdiff, norm_sub_sq_real, inner_smul_right, hnorm_eq, norm_smul, Real.norm_eq_abs,
            abs_of_pos ht_pos]
          have hge := hinner_ge x hx₀
          have hmul : t * ‖u‖ ^ 2 ≤ t * ⟪x - c, u⟫ := mul_le_mul_of_nonneg_left hge ht_pos.le
          have hsq : (t * ‖u‖) ^ 2 = t ^ 2 * ‖u‖ ^ 2 := mul_pow t ‖u‖ 2
          have hstrict : t ^ 2 * ‖u‖ ^ 2 < 2 * (t * ‖u‖ ^ 2) := by nlinarith
          linarith
        nlinarith [norm_nonneg (x - c')]
      · have hx₁ : x ∈ T₁ :=
          Finset.mem_filter.mpr ⟨hx, fun heq => hx₀ (Finset.mem_filter.mpr ⟨hx, heq⟩)⟩
        have hle : ‖x - c'‖ ≤ ‖x - c‖ + t * ‖u‖ := by
          rw [hdiff]
          calc
            ‖(x - c) - t • u‖ ≤ ‖x - c‖ + ‖t • u‖ := norm_sub_le _ _
            _ = ‖x - c‖ + t * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
        have htu : t * ‖u‖ ≤ δ := by
          calc
            t * ‖u‖ ≤ (δ / ‖u‖) * ‖u‖ :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg u)
            _ = δ := div_mul_cancel₀ δ (norm_ne_zero_iff.mpr hu_ne)
        linarith [hδ_lt x hx₁]
    exact hc'_lt.not_ge (hc_min hc'_conv)
  -- Express `c = ∑ x ∈ T₀, w x • x` and evaluate the weighted pairwise squared-distance sum.
  rw [T₀.convexHull_eq] at hc_in_T₀
  obtain ⟨w, hw0, hw1, hcm⟩ := hc_in_T₀
  have hc_sum : ∑ x ∈ T₀, w x • (x - c) = 0 := by
    have h1 : ∑ x ∈ T₀, w x • x = c := by
      rwa [T₀.centerMass_eq_of_sum_1 id hw1] at hcm
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw1, one_smul, h1, sub_self]
  have hdouble : ∑ x ∈ T₀, ∑ y ∈ T₀, (w x * w y) * ‖x - y‖ ^ 2 = 2 * r ^ 2 := by
    have hexp : ∀ x ∈ T₀, ∀ y ∈ T₀,
        (w x * w y) * ‖x - y‖ ^ 2 =
          (w x * w y) * r ^ 2 + (w x * w y) * r ^ 2 - 2 * ⟪w x • (x - c), w y • (y - c)⟫ := by
      intro x hx y hy
      have hnx : ‖x - c‖ = r := (Finset.mem_filter.mp hx).2
      have hny : ‖y - c‖ = r := (Finset.mem_filter.mp hy).2
      have hxy : x - y = (x - c) - (y - c) := by abel
      rw [hxy, norm_sub_sq_real, hnx, hny, inner_smul_left, inner_smul_right]
      simp only [RCLike.conj_to_real]
      ring
    have hcross : ∑ x ∈ T₀, ∑ y ∈ T₀, ⟪w x • (x - c), w y • (y - c)⟫ = 0 := by
      calc
        ∑ x ∈ T₀, ∑ y ∈ T₀, ⟪w x • (x - c), w y • (y - c)⟫
          = ∑ x ∈ T₀, ⟪w x • (x - c), ∑ y ∈ T₀, w y • (y - c)⟫ :=
              Finset.sum_congr rfl fun x _ => (inner_sum T₀ (fun y => w y • (y - c)) _).symm
        _ = 0 := by simp [hc_sum]
    calc
      ∑ x ∈ T₀, ∑ y ∈ T₀, (w x * w y) * ‖x - y‖ ^ 2
        = ∑ x ∈ T₀, ∑ y ∈ T₀,
            ((w x * w y) * r ^ 2 + (w x * w y) * r ^ 2 - 2 * ⟪w x • (x - c), w y • (y - c)⟫) :=
            Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => hexp x hx y hy
      _ = (∑ x ∈ T₀, ∑ y ∈ T₀, (w x * w y) * r ^ 2) +
          (∑ x ∈ T₀, ∑ y ∈ T₀, (w x * w y) * r ^ 2) -
          2 * (∑ x ∈ T₀, ∑ y ∈ T₀, ⟪w x • (x - c), w y • (y - c)⟫) := by
            simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = 2 * r ^ 2 := by
            have hsum_w : ∑ x ∈ T₀, ∑ y ∈ T₀, (w x * w y) * r ^ 2 = r ^ 2 := by
              simp only [← Finset.sum_mul, ← Finset.mul_sum, hw1, mul_one, one_mul]
            rw [hsum_w, hcross, mul_zero, sub_zero]; ring
  have hdouble_le : ∑ x ∈ T₀, ∑ y ∈ T₀, (w x * w y) * ‖x - y‖ ^ 2 ≤
      D ^ 2 * (1 - ∑ x ∈ T₀, w x ^ 2) := by
    have hdiag : ∀ x ∈ T₀, ∀ y ∈ T₀,
        (w x * w y) * ‖x - y‖ ^ 2 ≤ (if x = y then 0 else (w x * w y) * D ^ 2) := by
      intro x hx y hy
      split_ifs with hxy
      · subst hxy; simp
      · refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hw0 x hx) (hw0 y hy))
        exact pow_le_pow_left₀ (norm_nonneg _)
          (hdiam x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1) 2
    calc
      ∑ x ∈ T₀, ∑ y ∈ T₀, (w x * w y) * ‖x - y‖ ^ 2
        ≤ ∑ x ∈ T₀, ∑ y ∈ T₀, (if x = y then 0 else (w x * w y) * D ^ 2) :=
            Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hdiag x hx y hy
      _ = ∑ x ∈ T₀, (∑ y ∈ T₀, (w x * w y) * D ^ 2 - (w x * w x) * D ^ 2) := by
            refine Finset.sum_congr rfl fun x hx => ?_
            have hsplit : ∑ y ∈ T₀, (w x * w y) * D ^ 2 =
                ∑ y ∈ T₀, (if x = y then (w x * w y) * D ^ 2 else 0) +
                ∑ y ∈ T₀, (if x = y then 0 else (w x * w y) * D ^ 2) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun y _ => by split_ifs <;> ring
            have hsingle : ∑ y ∈ T₀, (if x = y then (w x * w y) * D ^ 2 else 0) =
                (w x * w x) * D ^ 2 := by
              simp [hx]
            linarith
      _ = D ^ 2 * (1 - ∑ x ∈ T₀, w x ^ 2) := by
            rw [Finset.sum_sub_distrib]
            have h1 : ∑ x ∈ T₀, ∑ y ∈ T₀, (w x * w y) * D ^ 2 = D ^ 2 := by
              simp only [← Finset.sum_mul, ← Finset.mul_sum, hw1, mul_one, one_mul]
            have h2 : ∑ x ∈ T₀, (w x * w x) * D ^ 2 = (∑ x ∈ T₀, w x ^ 2) * D ^ 2 := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun x _ => by ring
            rw [h1, h2]; ring
  -- Cauchy–Schwarz: `1 = (∑ w x)² ≤ T₀.card * ∑ w x² ≤ (d + 1) * ∑ w x²`.
  have hcs : (1 : ℝ) / ((d : ℝ) + 1) ≤ ∑ x ∈ T₀, w x ^ 2 := by
    have hcard_T₀ : (T₀.card : ℝ) ≤ (d : ℝ) + 1 := by
      exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ T)).trans hTcard
    have hsq_le : (∑ x ∈ T₀, w x) ^ 2 ≤ (T₀.card : ℝ) * ∑ x ∈ T₀, w x ^ 2 := by
      have h0 : 0 ≤ ∑ x ∈ T₀, ∑ y ∈ T₀, (w x - w y) ^ 2 :=
        Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => sq_nonneg _
      have hexp : ∑ x ∈ T₀, ∑ y ∈ T₀, (w x - w y) ^ 2 =
          2 * ((T₀.card : ℝ) * ∑ x ∈ T₀, w x ^ 2 - (∑ x ∈ T₀, w x) ^ 2) := by
        have h1 : ∑ x ∈ T₀, ∑ y ∈ T₀, (w x - w y) ^ 2 =
            ∑ x ∈ T₀, ∑ y ∈ T₀, (w x ^ 2 - 2 * (w x * w y) + w y ^ 2) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
        rw [h1]
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
          ← Finset.mul_sum, ← Finset.sum_mul]
        ring
      linarith
    rw [hw1, one_pow] at hsq_le
    have hle2 : 1 ≤ ((d : ℝ) + 1) * ∑ x ∈ T₀, w x ^ 2 :=
      hsq_le.trans (mul_le_mul_of_nonneg_right hcard_T₀ (Finset.sum_nonneg fun x _ => sq_nonneg _))
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < (d : ℝ) + 1)).mpr (by linarith)
  have hr_sq_le : r ^ 2 ≤ ((d : ℝ) / (2 * ((d : ℝ) + 1))) * D ^ 2 := by
    have h1 : 1 - ∑ x ∈ T₀, w x ^ 2 ≤ (d : ℝ) / ((d : ℝ) + 1) := by
      have : (1 : ℝ) - 1 / ((d : ℝ) + 1) = (d : ℝ) / ((d : ℝ) + 1) := by
        field_simp [show ((d : ℝ) + 1) ≠ 0 by positivity]; ring
      linarith
    have h2 : 2 * r ^ 2 ≤ D ^ 2 * ((d : ℝ) / ((d : ℝ) + 1)) :=
      (hdouble ▸ hdouble_le).trans (mul_le_mul_of_nonneg_left h1 (sq_nonneg D))
    have h3 : (d : ℝ) / (2 * ((d : ℝ) + 1)) * D ^ 2 = (D ^ 2 * ((d : ℝ) / ((d : ℝ) + 1))) / 2 := by
      field_simp [show ((d : ℝ) + 1) ≠ 0 by positivity]
    linarith
  have hR_sq : R_bound ^ 2 = ((d : ℝ) / (2 * ((d : ℝ) + 1))) * D ^ 2 := by
    dsimp only [R_bound]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hR_nonneg : 0 ≤ R_bound := by positivity
  nlinarith

/-- **Jung's Circumradius Theorem (arbitrary bounded set):**
Any bounded set `S` in a finite-dimensional real inner product space `E` is contained in
a closed ball of radius `√(d / (2 * (d + 1))) * Metric.diam S`, where `d = finrank ℝ E`. -/
theorem jung_circumradius {S : Set E} (hSb : Bornology.IsBounded S) :
    ∃ c : E, S ⊆ Metric.closedBall c
      (Real.sqrt ((Module.finrank ℝ E : ℝ) / (2 * (Module.finrank ℝ E + 1))) * Metric.diam S) := by
  classical
  set R : ℝ :=
    Real.sqrt ((Module.finrank ℝ E : ℝ) / (2 * (Module.finrank ℝ E + 1))) * Metric.diam S
  have hF_inter : (⋂ x : S, Metric.closedBall (x : E) R).Nonempty := by
    refine Convex.helly_theorem_compact' (𝕜 := ℝ)
      (fun x : S => convex_closedBall (x : E) R)
      (fun x : S => isCompact_closedBall (x : E) R) ?_
    intro I hIcard
    rcases I.eq_empty_or_nonempty with rfl | hIne
    · simp
    let T : Finset E := I.image Subtype.val
    have hTne : T.Nonempty := hIne.image _
    have hTcard : T.card ≤ Module.finrank ℝ E + 1 := Finset.card_image_le.trans hIcard
    have hdiam : ∀ x ∈ T, ∀ y ∈ T, ‖x - y‖ ≤ Metric.diam S := by
      intro x hx y hy
      rcases Finset.mem_image.mp hx with ⟨⟨x', hx'⟩, _, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨⟨y', hy'⟩, _, rfl⟩
      rw [← dist_eq_norm]
      exact Metric.dist_le_diam_of_mem hSb hx' hy'
    obtain ⟨c, _, hc⟩ := jung_circumradius_finset hTne hTcard Metric.diam_nonneg hdiam
    refine ⟨c, ?_⟩
    simp only [Set.mem_iInter, Metric.mem_closedBall, dist_eq_norm]
    intro x hxI
    rw [norm_sub_rev]
    exact hc x.1 (Finset.mem_image_of_mem Subtype.val hxI)
  obtain ⟨c, hc⟩ := hF_inter
  refine ⟨c, fun x hx => ?_⟩
  have hmem := Set.mem_iInter.mp hc ⟨x, hx⟩
  simpa [Metric.mem_closedBall, dist_comm] using hmem

/-- **Jung's Circumradius Theorem for `ConvexBody E`:**
Every convex body `K` is contained in a closed ball of radius
`√(d / (2 * (d + 1))) * Metric.diam (K : Set E)`. -/
theorem jung_circumradius_convexBody (K : ConvexBody E) :
    ∃ c : E, (K : Set E) ⊆ Metric.closedBall c
      (Real.sqrt ((Module.finrank ℝ E : ℝ) / (2 * (Module.finrank ℝ E + 1))) *
        Metric.diam (K : Set E)) :=
  jung_circumradius K.isCompact.isBounded

end Jung

end

end ConvexGeom
