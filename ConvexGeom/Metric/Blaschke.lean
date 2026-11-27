/-
Copyright (c) 2026 Yegor Gorodzha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yegor Gorodzha
-/
module

public import ConvexGeom.Metric.SupportFunction

import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Blaschke Selection Theorem and Completeness of `ConvexBody`

Using **Hörmander's isometric embedding** (`isometry_supportFnOnBall`),
**Minkowski's representation theorem** (`exists_convexBody_supportFn_eq`),
and Mathlib's **Arzelà–Ascoli theorem** (`BoundedContinuousFunction.arzela_ascoli₂`),
we prove:

- `isClosed_range_supportFnOnBall`: the image of `ConvexBody E` inside
  `Metric.closedBall (0 : E) 1 →ᵇ ℝ` is closed.
- `instCompleteSpaceConvexBody`: `ConvexBody E` is a **complete metric space** in any
  finite-dimensional real inner product space `E`.
- `isCompact_subset_closedBall`: `{K : ConvexBody E | (K : Set E) ⊆ Metric.closedBall 0 R}`
  is compact in the Hausdorff metric.
- `blaschke_selection` (`isCompact_subset_of_isCompact`): **Blaschke Selection Theorem** —
  for any compact set `C ⊆ E`, `{K : ConvexBody E | (K : Set E) ⊆ C}` is compact, so every
  uniformly bounded sequence of convex bodies has a Hausdorff-convergent subsequence.
-/

open scoped RealInnerProductSpace BoundedContinuousFunction

namespace ConvexGeom

public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Extend a function `f` on the closed unit ball `B(0, 1)` positively homogeneously to all of `E`:
`extendHomog f u = ‖u‖ * f(u / ‖u‖)` for `u ≠ 0` and `0` at `u = 0`. -/
noncomputable def extendHomog (f : Metric.closedBall (0 : E) 1 →ᵇ ℝ) (u : E) : ℝ := by
  classical
  exact if hu : u = 0 then 0
  else ‖u‖ * f ⟨‖u‖⁻¹ • u, by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg u)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)]⟩

omit [FiniteDimensional ℝ E] in
lemma extendHomog_zero (f : Metric.closedBall (0 : E) 1 →ᵇ ℝ) :
    extendHomog f 0 = 0 := by
  classical
  simp [extendHomog]

omit [FiniteDimensional ℝ E] in
lemma extendHomog_of_ne_zero (f : Metric.closedBall (0 : E) 1 →ᵇ ℝ) {u : E} (hu : u ≠ 0) :
    extendHomog f u = ‖u‖ * f ⟨‖u‖⁻¹ • u, by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg u)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)]⟩ := by
  classical
  simp [extendHomog, hu]

lemma extendHomog_supportFnOnBall (K : ConvexBody E) (u : E) :
    extendHomog (supportFnOnBall K) u = supportFn K u := by
  by_cases hu : u = 0
  · subst hu; simp [extendHomog_zero]
  · have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    rw [extendHomog_of_ne_zero _ hu, supportFnOnBall_apply,
      supportFn_smul K (inv_nonneg.mpr hpos.le), ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]

/-- Evaluation at a point `u` is 1-Lipschitz (hence continuous) on `α →ᵇ ℝ`. -/
private lemma continuous_eval_bcf {α : Type*} [TopologicalSpace α] (u : α) :
    Continuous (fun f : α →ᵇ ℝ => f u) :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun f g => by
    simpa using BoundedContinuousFunction.dist_coe_le_dist (f := f) (g := g) u).continuous

/-- The image of `supportFnOnBall : ConvexBody E → (closedBall 0 1 →ᵇ ℝ)` is closed. -/
theorem isClosed_range_supportFnOnBall :
    IsClosed (Set.range (supportFnOnBall (E := E))) := by
  rw [← isSeqClosed_iff_isClosed]
  intro fn f hfn htend
  choose K hK using hfn
  have hpt : ∀ u : Metric.closedBall (0 : E) 1,
      Filter.Tendsto (fun n => supportFn (K n) u.1) Filter.atTop (nhds (f u)) := by
    intro u
    have hev : Filter.Tendsto (fun n => fn n u) Filter.atTop (nhds (f u)) :=
      (continuous_eval_bcf u).continuousAt.tendsto.comp htend
    simpa [← hK] using hev
  have hpt_ext : ∀ u : E,
      Filter.Tendsto (fun n => supportFn (K n) u) Filter.atTop (nhds (extendHomog f u)) := by
    intro u
    by_cases hu : u = 0
    · subst hu; simp [extendHomog_zero]
    · have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
      let u1 : Metric.closedBall (0 : E) 1 := ⟨‖u‖⁻¹ • u, by
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr hpos.le), inv_mul_cancel₀ hpos.ne']⟩
      have heq : (fun n => supportFn (K n) u) = fun n => ‖u‖ * supportFn (K n) u1.1 := by
        ext n
        rw [← supportFn_smul (K n) hpos.le]
        congr 1
        simp [u1, smul_smul, mul_inv_cancel₀ hpos.ne']
      rw [heq, extendHomog_of_ne_zero f hu]
      exact (hpt u1).const_mul ‖u‖
  have h_hom : ∀ c : ℝ, 0 ≤ c → ∀ u, extendHomog f (c • u) = c * extendHomog f u := by
    intro c hc u
    have h1 := hpt_ext (c • u)
    have h2 : Filter.Tendsto (fun n => supportFn (K n) (c • u)) Filter.atTop
        (nhds (c * extendHomog f u)) := by
      have := (hpt_ext u).const_mul c
      simpa [supportFn_smul (K _) hc] using this
    exact tendsto_nhds_unique h1 h2
  have h_add : ∀ u v, extendHomog f (u + v) ≤ extendHomog f u + extendHomog f v := by
    intro u v
    exact le_of_tendsto_of_tendsto (hpt_ext (u + v)) ((hpt_ext u).add (hpt_ext v))
      (Filter.Eventually.of_forall fun n => supportFn_add_le (K n) u v)
  obtain ⟨K₀, hK₀, _⟩ := exists_convexBody_supportFn_eq (extendHomog f) h_hom h_add
  refine ⟨K₀, ?_⟩
  ext u
  rw [supportFnOnBall_apply, hK₀]
  exact tendsto_nhds_unique (hpt_ext u.1) (hpt u)

/-- **Completeness of `ConvexBody E` (Schneider, *Convex Bodies*, Thm. 1.8.2):**
In a finite-dimensional real inner product space, `ConvexBody E` with the Hausdorff metric
is a complete metric space.

*Maintainer note:* This is a global instance on Mathlib's `ConvexBody`; check for overlap on
Mathlib upgrades (candidate for upstreaming). -/
instance instCompleteSpaceConvexBody : CompleteSpace (ConvexBody E) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have h_iso := isometry_supportFnOnBall (E := E)
  have hcauchy : CauchySeq (fun n => supportFnOnBall (u n)) :=
    h_iso.uniformContinuous.comp_cauchySeq hu
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hmem : f ∈ Set.range (supportFnOnBall (E := E)) :=
    isClosed_range_supportFnOnBall.mem_of_tendsto hf
      (Filter.Eventually.of_forall fun n => ⟨u n, rfl⟩)
  obtain ⟨K₀, rfl⟩ := hmem
  refine ⟨K₀, ?_⟩
  rw [Metric.tendsto_atTop] at hf ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hf ε hε
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_dist_supportFnOnBall]
  exact hN n hn

/-- **Blaschke Selection Theorem (closed-ball version):**
For any `R : ℝ`, the set of convex bodies contained in `Metric.closedBall 0 R` is compact
in the Hausdorff metric. -/
theorem isCompact_subset_closedBall (R : ℝ) :
    IsCompact {K : ConvexBody E | (K : Set E) ⊆ Metric.closedBall 0 R} := by
  let S : Set (ConvexBody E) := {K : ConvexBody E | (K : Set E) ⊆ Metric.closedBall 0 R}
  let A : Set (Metric.closedBall (0 : E) 1 →ᵇ ℝ) := supportFnOnBall '' S
  change IsCompact S
  rw [(isometry_supportFnOnBall (E := E)).isUniformInducing.isInducing.isCompact_iff]
  change IsCompact A
  have hA_eq : A = Set.range (supportFnOnBall (E := E)) ∩
      {f | ∀ u : Metric.closedBall (0 : E) 1, f u ≤ R} := by
    ext f
    constructor
    · rintro ⟨K, hKR, rfl⟩
      refine ⟨⟨K, rfl⟩, fun ⟨u, hu⟩ => ?_⟩
      rw [supportFnOnBall_apply]
      have hu1 : ‖u‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hu
      have hR0 : 0 ≤ R := by
        obtain ⟨x, hx⟩ := K.nonempty
        exact (norm_nonneg x).trans (by simpa [Metric.mem_closedBall, dist_eq_norm] using hKR hx)
      exact ((le_abs_self _).trans (abs_supportFn_le_of_subset_closedBall hKR u)).trans
        ((mul_le_mul_of_nonneg_left hu1 hR0).trans (by rw [mul_one]))
    · rintro ⟨⟨K, rfl⟩, hfR⟩
      refine ⟨K, ?_, rfl⟩
      intro x hx
      rw [Metric.mem_closedBall, dist_zero_right]
      by_cases hx0 : x = 0
      · subst hx0
        have := hfR ⟨0, Metric.mem_closedBall_self zero_le_one⟩
        simpa [supportFnOnBall_apply] using this
      · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
        let u : Metric.closedBall (0 : E) 1 := ⟨‖x‖⁻¹ • x, by
          rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr hpos.le), inv_mul_cancel₀ hpos.ne']⟩
        have h1 : ‖x‖ = ⟪x, u.1⟫ := by
          simp only [u, inner_smul_right, real_inner_self_eq_norm_sq]
          field_simp [hpos.ne']
        rw [h1]
        have hfu : supportFn K u.1 ≤ R := by simpa [supportFnOnBall_apply] using hfR u
        exact (inner_le_supportFn hx u.1).trans hfu
  have hA_closed : IsClosed A := by
    rw [hA_eq]
    refine isClosed_range_supportFnOnBall.inter ?_
    have heq : {f : Metric.closedBall (0 : E) 1 →ᵇ ℝ | ∀ u, f u ≤ R} =
        ⋂ u : Metric.closedBall (0 : E) 1, {f | f u ≤ R} := by ext f; simp
    rw [heq]
    exact isClosed_iInter fun u => isClosed_le (continuous_eval_bcf u) continuous_const
  rcases lt_or_ge R 0 with hRneg | hR0
  · have hA_empty : A = ∅ := by
      ext f
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨K, hKR, _⟩
      obtain ⟨x, hx⟩ := K.nonempty
      have : ‖x‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hKR hx
      linarith [norm_nonneg x]
    rw [hA_empty]
    exact isCompact_empty
  · have : CompactSpace (Metric.closedBall (0 : E) 1) :=
      isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E) 1)
    refine BoundedContinuousFunction.arzela_ascoli₂ (Set.Icc (-R) R) isCompact_Icc A hA_closed ?_ ?_
    · rintro _ ⟨u, hu⟩ ⟨K, hKR, rfl⟩
      rw [supportFnOnBall_apply]
      have hu1 : ‖u‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hu
      have habs : |supportFn K u| ≤ R :=
        (abs_supportFn_le_of_subset_closedBall hKR u).trans
          ((mul_le_mul_of_nonneg_left hu1 hR0).trans (by rw [mul_one]))
      exact abs_le.mp habs
    · refine (LipschitzWith.uniformEquicontinuous (fun f : A => (f.1 : Metric.closedBall (0 : E) 1 → ℝ))
        ⟨R, hR0⟩ ?_).equicontinuous
      rintro ⟨_, K, hKR, rfl⟩
      refine LipschitzWith.of_dist_le_mul fun u v => ?_
      change |supportFnOnBall K u - supportFnOnBall K v| ≤ R * dist u v
      rw [supportFnOnBall_apply, supportFnOnBall_apply, Subtype.dist_eq, dist_eq_norm]
      exact abs_supportFn_sub_le_of_subset_closedBall hKR u.1 v.1

/-- **Blaschke Selection Theorem:**
For any compact subset `C ⊆ E`, the family `{K : ConvexBody E | (K : Set E) ⊆ C}` is compact
in the Hausdorff metric. -/
theorem isCompact_subset_of_isCompact {C : Set E} (hC : IsCompact C) :
    IsCompact {K : ConvexBody E | (K : Set E) ⊆ C} := by
  obtain ⟨R, hCR⟩ := hC.isBounded.subset_closedBall (0 : E)
  refine (isCompact_subset_closedBall (E := E) R).of_isClosed_subset ?_ (fun K hK => hK.trans hCR)
  rw [← isSeqClosed_iff_isClosed]
  intro Kn K hKn htend x hxK
  have hdist : ∀ n, ∃ y ∈ Kn n, dist x y ≤ dist K (Kn n) := fun n => by
    obtain ⟨y, hy, hinf⟩ := (Kn n).isCompact.exists_infDist_eq_dist (Kn n).nonempty x
    refine ⟨y, hy, ?_⟩
    rw [← hinf]
    exact (Metric.infDist_le_hausdorffDist_of_mem hxK ConvexBody.hausdorffEDist_ne_top).trans
      (by rw [ConvexBody.hausdorffDist_coe])
  choose yn hyn hdist_yn using hdist
  have hyn_tend : Filter.Tendsto yn Filter.atTop (nhds x) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htend ε hε
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_comm]
    exact (hdist_yn n).trans_lt (by simpa [dist_comm] using hN n hn)
  exact hC.isClosed.mem_of_tendsto hyn_tend (Filter.Eventually.of_forall fun n => hKn n (hyn n))

/-- **Sequential Blaschke Selection Theorem:**
Every sequence of convex bodies contained in a compact set `C` admits a Hausdorff-convergent
subsequence whose limit is also contained in `C`. -/
theorem blaschke_selection {C : Set E} (hC : IsCompact C) (K : ℕ → ConvexBody E)
    (hK : ∀ n, (K n : Set E) ⊆ C) :
    ∃ K₀ : ConvexBody E, (K₀ : Set E) ⊆ C ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Filter.Tendsto (K ∘ φ) Filter.atTop (nhds K₀) := by
  obtain ⟨K₀, hK₀C, φ, hφ, htend⟩ := (isCompact_subset_of_isCompact hC).tendsto_subseq hK
  exact ⟨K₀, hK₀C, φ, hφ, htend⟩

end

end ConvexGeom
