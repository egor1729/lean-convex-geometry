module

public import ConvexGeom.Metric.Polarity
public import ConvexGeom.Polytope.GeneralPosition
public import Mathlib.Analysis.Convex.Extreme

import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Polytope Faces, Weyl–Minkowski Duality, and Radial Facet-Cone Tiling

For a finite point set `S : Finset E` in a finite-dimensional real inner product space `E`,
this file develops the `V → H` facet structure of `P = convexHull ℝ (S : Set E)` via geometric
polarity (`ConvexGeom.Metric.Polarity`) and Krein–Milman:

1. **Finitely Many Facet Normals (`tightVertices`, `finite_extremePoints_polarBody`,
   `facetNormals`):**
   Every extreme point `u` of `polarBody S` has `span (tightVertices S u) = ⊤`, hence is uniquely
   determined by its tight subset `tightVertices S u ⊆ S`. Thus `(polarBody S).extremePoints ℝ`
   is finite.
2. **Weyl–Minkowski `V → H` Representation (`polarBody_eq_convexHull_facetNormals`,
   `weyl_minkowski_halfspaces`, `facetNormals_irredundant`):**
   When `0 ∈ interior P`, `P = {x | ∀ u ∈ facetNormals S, ⟪x, u⟫ ≤ 1}`, and no half-space
   inequality `⟪x, u⟫ ≤ 1` (`u ∈ facetNormals S`) is redundant.
3. **Facet Characterization & Simpliciality (`polytopeFacet`,
   `polytopeFacet_eq_convexHull_tightVertices`, `affineSpan_polytopeFacet`,
   `card_tightVertices_eq_finrank_of_inGeneralPosition`):**
   Each facet `polytopeFacet S u = convexHull ℝ (tightVertices S u)` spans the full supporting
   hyperplane `{x | ⟪x, u⟫ = 1}`. If the vertices of `S` are in affine general position, every
   facet has exactly `finrank ℝ E` affinely independent vertices (a `(d - 1)`-simplex).
4. **Radial Facet-Cone Tiling (`facetCone`, `iUnion_facetCone_eq`,
   `pairwise_aedisjoint_facetCone`, `addHaar_convexHull_eq_sum_facetCone`):**
   When `0 ∈ interior P` (`Nontrivial E`), the origin-apex cones `facetCone S u` cover `P` with
   pairwise Haar-null overlaps, yielding `μ P = ∑ u ∈ facetNormals S, μ (facetCone S u)`.
-/

open MeasureTheory Set Finset
open scoped RealInnerProductSpace ENNReal

namespace ConvexGeom

public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### 1. Tight Vertices and Finiteness of Extreme Polar Points -/

/-- The subset of generators `s ∈ S` attaining `⟪s, u⟫ = 1`. -/
@[expose]
noncomputable def tightVertices (S : Finset E) (u : E) : Finset E := by
  classical exact S.filter fun s => ⟪s, u⟫ = 1

omit [FiniteDimensional ℝ E] in
lemma mem_tightVertices {S : Finset E} {u s : E} :
    s ∈ tightVertices S u ↔ s ∈ S ∧ ⟪s, u⟫ = 1 := by
  classical simp [tightVertices]

omit [FiniteDimensional ℝ E] in
lemma tightVertices_subset (S : Finset E) (u : E) : tightVertices S u ⊆ S := by
  classical exact Finset.filter_subset _ S

/-- Every extreme point `u` of `polarBody S` has tight vertices spanning the entire space `E`. -/
theorem span_tightVertices_eq_top_of_mem_extremePoints_polarBody
    {S : Finset E} {u : E} (hu : u ∈ (polarBody (S : Set E)).extremePoints ℝ) :
    Submodule.span ℝ (tightVertices S u : Set E) = ⊤ := by
  classical
  by_contra hne_top
  have horth_ne : (Submodule.span ℝ (tightVertices S u : Set E))ᗮ ≠ ⊥ := by
    intro hbot
    have hadd := Submodule.finrank_add_finrank_orthogonal
      (Submodule.span ℝ (tightVertices S u : Set E))
    rw [hbot, finrank_bot, add_zero] at hadd
    exact hne_top (Submodule.eq_top_of_finrank_eq hadd)
  obtain ⟨v, hv_orth, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot horth_ne
  have hv_tight : ∀ s ∈ tightVertices S u, ⟪s, v⟫ = 0 := fun s hs =>
    (Submodule.mem_orthogonal _ v).mp hv_orth s (Submodule.subset_span hs)
  let S_strict : Finset E := S.filter fun s => ⟪s, u⟫ < 1
  have hmargin : ∃ m : ℝ, 0 < m ∧ ∀ s ∈ S_strict, m ≤ 1 - ⟪s, u⟫ := by
    by_cases hne : S_strict.Nonempty
    · refine ⟨S_strict.inf' hne fun s => 1 - ⟪s, u⟫, ?_, fun s hs => Finset.inf'_le _ hs⟩
      rw [Finset.lt_inf'_iff]
      intro s hs
      have hlt : ⟪s, u⟫ < 1 := (Finset.mem_filter.mp hs).2
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      exact ⟨1, zero_lt_one, fun s hs => (by simp [hne] at hs)⟩
  obtain ⟨m, hm_pos, hm_le⟩ := hmargin
  have hnorm_bound : ∃ M : ℝ, 0 < M ∧ ∀ s ∈ S, ‖s‖ ≤ M := by
    by_cases hS_ne : S.Nonempty
    · refine ⟨(S.sup' hS_ne fun s => ‖s‖) + 1, ?_, fun s hs => ?_⟩
      · have ⟨s₀, hs₀⟩ := hS_ne
        have : 0 ≤ S.sup' hS_ne fun s => ‖s‖ :=
          (norm_nonneg s₀).trans (Finset.le_sup' (f := fun s => ‖s‖) hs₀)
        linarith
      · exact (Finset.le_sup' (f := fun s => ‖s‖) hs).trans (by linarith)
    · rw [Finset.not_nonempty_iff_eq_empty] at hS_ne
      exact ⟨1, zero_lt_one, fun s hs => (by simp [hS_ne] at hs)⟩
  obtain ⟨M, hM_pos, hM_le⟩ := hnorm_bound
  set ε : ℝ := m / (M * ‖v‖)
  have hε_pos : 0 < ε := div_pos hm_pos (mul_pos hM_pos (norm_pos_iff.mpr hv_ne))
  have hpm_mem : ∀ σ : ℝ, |σ| = 1 → u + (σ * ε) • v ∈ polarBody (S : Set E) := by
    intro σ hσ s hs
    have hsu_le : ⟪s, u⟫ ≤ 1 := hu.1 s hs
    rw [inner_add_right, inner_smul_right]
    by_cases htight : ⟪s, u⟫ = 1
    · have hsv : ⟪s, v⟫ = 0 := hv_tight s (mem_tightVertices.mpr ⟨hs, htight⟩)
      rw [htight, hsv, mul_zero, add_zero]
    · have hs_strict : s ∈ S_strict :=
        Finset.mem_filter.mpr ⟨hs, lt_of_le_of_ne hsu_le htight⟩
      have h1 : σ * ε * ⟪s, v⟫ ≤ ε * (‖s‖ * ‖v‖) := by
        calc
          σ * ε * ⟪s, v⟫ ≤ |σ * ε * ⟪s, v⟫| := le_abs_self _
          _ = |σ| * |ε| * |⟪s, v⟫| := by rw [abs_mul, abs_mul]
          _ = ε * |⟪s, v⟫| := by rw [hσ, one_mul, abs_of_pos hε_pos]
          _ ≤ ε * (‖s‖ * ‖v‖) := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm s v) hε_pos.le
      have h2 : ε * (‖s‖ * ‖v‖) ≤ m := by
        calc
          ε * (‖s‖ * ‖v‖) ≤ ε * (M * ‖v‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hM_le s hs) (norm_nonneg v))
              hε_pos.le
          _ = m := div_mul_cancel₀ m (mul_pos hM_pos (norm_pos_iff.mpr hv_ne)).ne'
      linarith [hm_le s hs_strict]
  have hup : u + (1 * ε) • v ∈ polarBody (S : Set E) := hpm_mem 1 (by simp)
  have hum : u + (-1 * ε) • v ∈ polarBody (S : Set E) := hpm_mem (-1) (by simp)
  have hu_mid : u ∈ openSegment ℝ (u + (1 * ε) • v) (u + (-1 * ε) • v) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    module
  have heq : u + (1 * ε) • v = u := hu.2 hup hum hu_mid
  have hzero : (1 * ε) • v = 0 := by simpa using heq
  rcases smul_eq_zero.mp hzero with hε0 | hv0
  · linarith
  · exact hv_ne hv0

/-- A finite set `S` has only finitely many extreme polar points. -/
theorem finite_extremePoints_polarBody (S : Finset E) :
    ((polarBody (S : Set E)).extremePoints ℝ).Finite := by
  classical
  have hinj : Set.InjOn (tightVertices S) ((polarBody (S : Set E)).extremePoints ℝ) := by
    intro u₁ hu₁ u₂ hu₂ hEq
    have horth : u₁ - u₂ ∈ (Submodule.span ℝ (tightVertices S u₁ : Set E))ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro x hx
      refine Submodule.span_induction ?_ (by simp)
        (fun a b _ _ ha hb => by rw [inner_add_left, ha, hb, add_zero])
        (fun c a _ ha => by rw [inner_smul_left, ha, mul_zero]) hx
      intro s hs
      have hs₁ : ⟪s, u₁⟫ = 1 := (mem_tightVertices.mp hs).2
      have hs₂ : ⟪s, u₂⟫ = 1 := (mem_tightVertices.mp (hEq ▸ hs)).2
      rw [inner_sub_right, hs₁, hs₂, sub_self]
    rw [span_tightVertices_eq_top_of_mem_extremePoints_polarBody hu₁,
      Submodule.top_orthogonal_eq_bot, Submodule.mem_bot] at horth
    exact sub_eq_zero.mp horth
  have hsub : tightVertices S '' ((polarBody (S : Set E)).extremePoints ℝ) ⊆
      (S.powerset : Set (Finset E)) := by
    rintro _ ⟨u, _, rfl⟩
    exact Finset.mem_powerset.mpr (tightVertices_subset S u)
  exact Set.Finite.of_finite_image (S.powerset.finite_toSet.subset hsub) hinj

/-- The finite set of irredundant facet normals of `convexHull ℝ S`: the extreme points of
`polarBody S`. -/
@[expose]
noncomputable def facetNormals (S : Finset E) : Finset E :=
  (finite_extremePoints_polarBody S).toFinset

@[simp]
lemma mem_facetNormals {S : Finset E} {u : E} :
    u ∈ facetNormals S ↔ u ∈ (polarBody (S : Set E)).extremePoints ℝ :=
  Set.Finite.mem_toFinset _

lemma facetNormals_subset_polarBody (S : Finset E) :
    (facetNormals S : Set E) ⊆ polarBody (S : Set E) := fun _ hu =>
  (mem_facetNormals.mp hu).1

/-! ### 2. Weyl–Minkowski `V → H` Representation and Irredundancy -/

/-- When `0 ∈ interior (convexHull ℝ S)`, the polar body is the convex hull of `facetNormals S`. -/
theorem polarBody_eq_convexHull_facetNormals {S : Finset E}
    (h0 : (0 : E) ∈ interior (convexHull ℝ (S : Set E))) :
    polarBody (S : Set E) = convexHull ℝ (facetNormals S : Set E) := by
  have hP_comp : IsCompact (polarBody (S : Set E)) := by
    rw [← polarBody_convexHull]
    exact isCompact_polarBody_of_zero_mem_interior h0
  have hcoe : (facetNormals S : Set E) = (polarBody (S : Set E)).extremePoints ℝ :=
    Set.Finite.coe_toFinset _
  have hch_closed : IsClosed (convexHull ℝ (facetNormals S : Set E)) :=
    ((facetNormals S).finite_toSet.isCompact_convexHull ℝ).isClosed
  rw [← hch_closed.closure_eq, hcoe]
  exact (closure_convexHull_extremePoints hP_comp (convex_polarBody _)).symm

/-- **Weyl–Minkowski `V → H` Representation Theorem:**
If `S : Finset E` has `0 ∈ interior (convexHull ℝ S)`, then `convexHull ℝ S` is the finite
intersection of closed half-spaces `{x | ⟪x, u⟫ ≤ 1}` over `u ∈ facetNormals S`. -/
theorem weyl_minkowski_halfspaces {S : Finset E}
    (h0 : (0 : E) ∈ interior (convexHull ℝ (S : Set E))) :
    convexHull ℝ (S : Set E) = {x : E | ∀ u ∈ facetNormals S, ⟪x, u⟫ ≤ 1} := by
  have hconv_closed : IsClosed (convexHull ℝ (S : Set E)) :=
    (S.finite_toSet.isCompact_convexHull ℝ).isClosed
  have h1 : convexHull ℝ (S : Set E) = polarBody (polarBody (S : Set E)) := by
    rw [← polarBody_convexHull (S : Set E)]
    exact (polarBody_polarBody (convex_convexHull ℝ _) hconv_closed (interior_subset h0)).symm
  rw [h1, polarBody_eq_convexHull_facetNormals h0, polarBody_convexHull]
  ext x
  simp [polarBody, real_inner_comm]

/-- In any nontrivial space, `0 ∉ facetNormals S`. -/
lemma zero_notMem_facetNormals [Nontrivial E] {S : Finset E} :
    (0 : E) ∉ facetNormals S := by
  intro h0_mem
  have h0_ext := mem_facetNormals.mp h0_mem
  have h0_int : (0 : E) ∈ interior (polarBody (S : Set E)) :=
    zero_mem_interior_polarBody_of_isBounded S.finite_toSet.isBounded
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior 0 h0_int
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  let w : E := ((ε / 2) / ‖v‖) • v
  have hw_ne : w ≠ 0 := by
    intro hw0
    rcases smul_eq_zero.mp hw0 with h0 | hv0
    · exact (div_pos (half_pos hε) (norm_pos_iff.mpr hv)).ne' h0
    · exact hv hv0
  have hw_norm : ‖w‖ < ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hv)]
    linarith
  have hw_mem : w ∈ polarBody (S : Set E) :=
    interior_subset (hball (by simpa [Metric.mem_ball] using hw_norm))
  have hnw_mem : -w ∈ polarBody (S : Set E) :=
    interior_subset (hball (by simpa [Metric.mem_ball] using hw_norm))
  have hmid : (0 : E) ∈ openSegment ℝ w (-w) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    module
  exact hw_ne (h0_ext.2 hw_mem hnw_mem hmid)

/-- **Irredundancy of `facetNormals`:**
In any nontrivial space, removing any `u ∈ facetNormals S` strictly enlarges the half-space
intersection: there exists `x` satisfying `⟪x, v⟫ ≤ 1` for all `v ∈ facetNormals S` with `v ≠ u`,
and `1 < ⟪x, u⟫`. -/
theorem facetNormals_irredundant [Nontrivial E] {S : Finset E}
    {u : E} (hu : u ∈ facetNormals S) :
    ∃ x : E, (∀ v ∈ facetNormals S, v ≠ u → ⟪x, v⟫ ≤ 1) ∧ 1 < ⟪x, u⟫ := by
  classical
  let U' : Finset E := (facetNormals S).erase u
  let C : Set E := convexHull ℝ (insert (0 : E) (U' : Set E))
  have hC_closed : IsClosed C :=
    ((U'.finite_toSet.insert (0 : E)).isCompact_convexHull ℝ).isClosed
  have hu_not_C : u ∉ C := by
    intro huC
    have hu_ext := mem_facetNormals.mp hu
    have hconv_sdiff : Convex ℝ (polarBody (S : Set E) \ {u}) :=
      ((convex_polarBody _).mem_extremePoints_iff_convex_sdiff.mp hu_ext).2
    have hsub_sdiff : insert (0 : E) (U' : Set E) ⊆ polarBody (S : Set E) \ {u} := by
      intro v hv
      rcases Set.mem_insert_iff.mp hv with rfl | hv'
      · exact ⟨zero_mem_polarBody _, fun h0u => zero_notMem_facetNormals (h0u ▸ hu)⟩
      · exact ⟨facetNormals_subset_polarBody S (Finset.erase_subset u _ hv'),
          (Finset.mem_erase.mp hv').1⟩
    exact (convexHull_min hsub_sdiff hconv_sdiff huC).2 rfl
  have hbip : polarBody (polarBody C) = C :=
    polarBody_polarBody (convex_convexHull ℝ _) hC_closed (subset_convexHull ℝ _ (Set.mem_insert 0 _))
  rw [← hbip] at hu_not_C
  simp only [polarBody, Set.mem_ofPred_eq, not_forall, not_le] at hu_not_C
  obtain ⟨x, hx_pol, hxu⟩ := hu_not_C
  refine ⟨x, fun v hv hvu => ?_, hxu⟩
  have hvU' : v ∈ U' := Finset.mem_erase.mpr ⟨hvu, hv⟩
  have hvC : v ∈ C := subset_convexHull ℝ _ (Set.mem_insert_of_mem 0 hvU')
  simpa [real_inner_comm] using hx_pol v hvC

/-! ### 3. Facets and Simpliciality under General Position -/

/-- The facet of `convexHull ℝ S` exposed by `u : E`:
`polytopeFacet S u = {x ∈ convexHull ℝ S | ⟪x, u⟫ = 1}`. -/
@[expose]
def polytopeFacet (S : Finset E) (u : E) : Set E :=
  {x ∈ convexHull ℝ (S : Set E) | ⟪x, u⟫ = 1}

omit [FiniteDimensional ℝ E] in
/-- For any `u ∈ polarBody S`, `polytopeFacet S u` is the convex hull of its tight vertices. -/
theorem polytopeFacet_eq_convexHull_tightVertices {S : Finset E} {u : E}
    (hu : u ∈ polarBody (S : Set E)) :
    polytopeFacet S u = convexHull ℝ (tightVertices S u : Set E) := by
  classical
  apply Set.Subset.antisymm
  · intro x ⟨hx_ch, hxu⟩
    rw [S.convexHull_eq] at hx_ch
    obtain ⟨w, hw0, hw1, rfl⟩ := hx_ch
    rw [S.centerMass_eq_of_sum_1 id hw1] at hxu ⊢
    simp only [id_eq] at hxu ⊢
    have hdiff_zero : ∑ s ∈ S, w s * (1 - ⟪s, u⟫) = 0 := by
      have h1 : ∑ s ∈ S, w s * ⟪s, u⟫ = 1 := by
        simpa [sum_inner, inner_smul_left] using hxu
      calc
        ∑ s ∈ S, w s * (1 - ⟪s, u⟫) = ∑ s ∈ S, w s - ∑ s ∈ S, w s * ⟪s, u⟫ := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun s _ => by ring
        _ = 0 := by rw [hw1, h1, sub_self]
    have hterm_nonneg : ∀ s ∈ S, 0 ≤ w s * (1 - ⟪s, u⟫) := fun s hs =>
      mul_nonneg (hw0 s hs) (sub_nonneg.mpr (hu s hs))
    have hzero_off : ∀ s ∈ S, s ∉ tightVertices S u → w s = 0 := by
      intro s hs hnot
      have hterm0 : w s * (1 - ⟪s, u⟫) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hdiff_zero s hs
      rcases mul_eq_zero.mp hterm0 with hw | h1
      · exact hw
      · exact (hnot (mem_tightVertices.mpr ⟨hs, by linarith⟩)).elim
    have hsum_tight : ∑ s ∈ tightVertices S u, w s = 1 := by
      rw [← hw1]
      exact Finset.sum_subset (tightVertices_subset S u) fun s hs hnot => hzero_off s hs hnot
    have hcomb_tight : ∑ s ∈ tightVertices S u, w s • s = ∑ s ∈ S, w s • s := by
      exact Finset.sum_subset (tightVertices_subset S u) fun s hs hnot => by
        rw [hzero_off s hs hnot, zero_smul]
    rw [← hcomb_tight]
    have hcm : (tightVertices S u).centerMass w id = ∑ s ∈ tightVertices S u, w s • s := by
      simpa using (tightVertices S u).centerMass_eq_of_sum_1 id hsum_tight
    rw [← hcm]
    exact (tightVertices S u).centerMass_mem_convexHull
      (fun s hs => hw0 s (tightVertices_subset S u hs)) (by rw [hsum_tight]; exact zero_lt_one)
      (fun _ hs => hs)
  · refine convexHull_min ?_ ?_
    · intro s hs
      exact ⟨subset_convexHull ℝ _ (tightVertices_subset S u hs), (mem_tightVertices.mp hs).2⟩
    · change Convex ℝ (convexHull ℝ (S : Set E) ∩ {x : E | ⟪x, u⟫ = 1})
      refine (convex_convexHull ℝ _).inter ?_
      intro x hx y hy a b _ _ hab
      change ⟪a • x + b • y, u⟫ = 1
      change ⟪x, u⟫ = 1 at hx
      change ⟪y, u⟫ = 1 at hy
      rw [inner_add_left, inner_smul_left, inner_smul_left]
      simp only [RCLike.conj_to_real, hx, hy, mul_one]
      exact hab

/-- Every facet `polytopeFacet S u` (`u ∈ facetNormals S`) spans the full `(d - 1)`-dimensional
supporting hyperplane `{x | ⟪x, u⟫ = 1}`. -/
theorem affineSpan_polytopeFacet [Nontrivial E] {S : Finset E} {u : E}
    (hu : u ∈ facetNormals S) :
    (affineSpan ℝ (polytopeFacet S u) : Set E) = {x : E | ⟪x, u⟫ = 1} := by
  have hu_pol : u ∈ polarBody (S : Set E) := facetNormals_subset_polarBody S hu
  have hF_eq : polytopeFacet S u = convexHull ℝ (tightVertices S u : Set E) :=
    polytopeFacet_eq_convexHull_tightVertices hu_pol
  have htight_ne : (tightVertices S u).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have htop := span_tightVertices_eq_top_of_mem_extremePoints_polarBody (mem_facetNormals.mp hu)
    rw [hemp, Finset.coe_empty, Submodule.span_empty] at htop
    exact bot_ne_top htop
  obtain ⟨s₀, hs₀⟩ := htight_ne
  have hs₀_in : ⟪s₀, u⟫ = 1 := (mem_tightVertices.mp hs₀).2
  have hs₀_F : s₀ ∈ polytopeFacet S u :=
    ⟨subset_convexHull ℝ _ (tightVertices_subset S u hs₀), hs₀_in⟩
  have hvspan_eq : vectorSpan ℝ (polytopeFacet S u) = (ℝ ∙ u)ᗮ := by
    apply le_antisymm
    · rw [vectorSpan_def, Submodule.span_le]
      rintro _ ⟨x, hx, y, hy, rfl⟩
      change x -ᵥ y ∈ (ℝ ∙ u)ᗮ
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left, vsub_eq_sub, inner_sub_left,
        hx.2, hy.2, sub_self]
    · intro w hw
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at hw
      have hspan_top :=
        span_tightVertices_eq_top_of_mem_extremePoints_polarBody (mem_facetNormals.mp hu)
      have hw_mem : w ∈ Submodule.span ℝ (tightVertices S u : Set E) := hspan_top ▸ Submodule.mem_top
      rw [Finsupp.mem_span_iff_linearCombination] at hw_mem
      obtain ⟨c, hc⟩ := hw_mem
      have hsum_zero : ∑ s ∈ c.support, c s = 0 := by
        have h1 : ⟪Finsupp.linearCombination ℝ (fun x : (tightVertices S u : Set E) => (x : E)) c, u⟫ = 0 := by
          rw [hc, hw]
        rw [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner] at h1
        have h2 : ∑ s ∈ c.support, ⟪c s • (s : E), u⟫ = ∑ s ∈ c.support, c s := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [inner_smul_left, RCLike.conj_to_real, (mem_tightVertices.mp s.2).2, mul_one]
        rwa [h2] at h1
      have hw_eq : w = ∑ s ∈ c.support, c s • ((s : E) -ᵥ s₀) := by
        rw [← hc, Finsupp.linearCombination_apply, Finsupp.sum]
        simp only [vsub_eq_sub, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
          hsum_zero, zero_smul, sub_zero]
      rw [hw_eq]
      refine Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ ?_
      exact vsub_mem_vectorSpan ℝ
        (hF_eq ▸ subset_convexHull ℝ _ s.2) hs₀_F
  ext x
  constructor
  · intro hx
    have hsub : x -ᵥ s₀ ∈ (affineSpan ℝ (polytopeFacet S u)).direction :=
      AffineSubspace.vsub_mem_direction hx (subset_affineSpan ℝ _ hs₀_F)
    rw [direction_affineSpan, hvspan_eq, Submodule.mem_orthogonal_singleton_iff_inner_left,
      vsub_eq_sub, inner_sub_left, hs₀_in] at hsub
    change ⟪x, u⟫ = 1
    linarith
  · intro hxu
    change ⟪x, u⟫ = 1 at hxu
    have hdir : x -ᵥ s₀ ∈ (affineSpan ℝ (polytopeFacet S u)).direction := by
      rw [direction_affineSpan, hvspan_eq, Submodule.mem_orthogonal_singleton_iff_inner_left,
        vsub_eq_sub, inner_sub_left, hxu, hs₀_in, sub_self]
    have := AffineSubspace.vadd_mem_of_mem_direction hdir (subset_affineSpan ℝ _ hs₀_F)
    simpa using this

/-- **Simplicial Facet Theorem under General Position:**
If the elements of `S : Finset E` are in affine general position (`InGeneralPosition ((↑) : S → E)`),
then for every `u ∈ facetNormals S` (`Nontrivial E`), the facet `polytopeFacet S u` has **exactly**
`finrank ℝ E` affinely independent vertices — i.e., every facet is a `(d - 1)`-simplex. -/
theorem card_tightVertices_eq_finrank_of_inGeneralPosition [Nontrivial E]
    {S : Finset E} (hgp : InGeneralPosition ((↑) : S → E))
    {u : E} (hu : u ∈ facetNormals S) :
    (tightVertices S u).card = Module.finrank ℝ E ∧
      AffineIndependent ℝ ((↑) : tightVertices S u → E) := by
  classical
  set d : ℕ := Module.finrank ℝ E
  set T : Finset E := tightVertices S u
  have hge : d ≤ T.card := by
    have htop := span_tightVertices_eq_top_of_mem_extremePoints_polarBody (mem_facetNormals.mp hu)
    have hle : Module.finrank ℝ (Submodule.span ℝ (T : Set E)) ≤ T.card :=
      finrank_span_finset_le_card (R := ℝ) T
    dsimp only [T] at hle
    rw [htop, finrank_top] at hle
    exact hle
  have hle : T.card ≤ d := by
    by_contra hgt
    push Not at hgt
    obtain ⟨T', hT'sub, hT'card⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hgt)
    let t : Finset S := T'.attach.map
      ⟨fun x => ⟨x.1, tightVertices_subset S u (hT'sub x.2)⟩,
        fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)⟩
    have ht_card : t.card = d + 1 := by
      rw [Finset.card_map, Finset.card_attach, hT'card]
    have ht_ind : AffineIndepOn ℝ ((↑) : S → E) (t : Set S) := hgp t (le_of_eq ht_card)
    have himg : ((↑) : S → E) '' (t : Set S) = (T' : Set E) := by
      ext x
      simp only [Set.mem_image, Finset.mem_coe, t, Finset.mem_map, Finset.mem_attach,
        true_and, Subtype.exists]
      exact ⟨fun ⟨_, _, ⟨y, hy, heq⟩, hval⟩ => by
          have : y = x := by rw [← hval]; exact congrArg Subtype.val heq
          rwa [← this],
        fun hx => ⟨x, tightVertices_subset S u (hT'sub hx), ⟨x, hx, rfl⟩, rfl⟩⟩
    have hspan_dim : Module.finrank ℝ (vectorSpan ℝ (T' : Set E)) = d := by
      rw [← himg]
      have hfin : (t : Set S).Finite := t.finite_toSet
      have hne : (t : Set S).Nonempty := by
        rw [Finset.coe_nonempty, ← Finset.card_pos]; omega
      have h1 := ht_ind.finrank_vectorSpan_image hfin hne
      have hnc : (t : Set S).ncard = d + 1 := by simp [Set.ncard_coe_finset, ht_card]
      omega
    have hT'_sub_F : (T' : Set E) ⊆ polytopeFacet S u := fun x hx =>
      ⟨subset_convexHull ℝ _ (tightVertices_subset S u (hT'sub hx)),
        (mem_tightVertices.mp (hT'sub hx)).2⟩
    have hspan_le_H : vectorSpan ℝ (T' : Set E) ≤ (ℝ ∙ u)ᗮ := by
      rw [vectorSpan_def, Submodule.span_le]
      rintro _ ⟨x, hx, y, hy, rfl⟩
      change x -ᵥ y ∈ (ℝ ∙ u)ᗮ
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left, vsub_eq_sub, inner_sub_left,
        (hT'_sub_F hx).2, (hT'_sub_F hy).2, sub_self]
    have hdim_H : Module.finrank ℝ (ℝ ∙ u)ᗮ < d := by
      have hu_ne : u ≠ 0 := fun h0 => zero_notMem_facetNormals (h0 ▸ hu)
      have hadd := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ u)
      have h1 : Module.finrank ℝ (ℝ ∙ u) = 1 := finrank_span_singleton hu_ne
      omega
    have hle_H := Submodule.finrank_mono hspan_le_H
    omega
  have hcard_eq : T.card = d := le_antisymm hle hge
  refine ⟨hcard_eq, ?_⟩
  let t : Finset S := T.attach.map
    ⟨fun x => ⟨x.1, tightVertices_subset S u x.2⟩,
      fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)⟩
  have ht_card : t.card ≤ d + 1 := by
    rw [Finset.card_map, Finset.card_attach, hcard_eq]; omega
  have ht_ind : AffineIndepOn ℝ ((↑) : S → E) (t : Set S) := hgp t ht_card
  let e : T ↪ (t : Set S) :=
    ⟨fun x => ⟨⟨x.1, tightVertices_subset S u x.2⟩, by
      simp only [Finset.mem_coe, t, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists]
      exact ⟨x.1, x.2, rfl⟩⟩,
    fun a b hab => Subtype.ext (congrArg (fun z : (t : Set S) => (z.1 : E)) hab)⟩
  exact ht_ind.affineIndependent.comp_embedding e

/-! ### 4. Radial Facet-Cone Tiling -/

/-- The radial cone (pyramid) from the origin over the facet `polytopeFacet S u`. -/
@[expose]
def facetCone (S : Finset E) (u : E) : Set E :=
  convexHull ℝ (insert (0 : E) (polytopeFacet S u))

omit [FiniteDimensional ℝ E] in
lemma facetCone_subset_convexHull {S : Finset E}
    (h0 : (0 : E) ∈ convexHull ℝ (S : Set E)) (u : E) :
    facetCone S u ⊆ convexHull ℝ (S : Set E) := by
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hxF
  · exact h0
  · exact hxF.1

omit [FiniteDimensional ℝ E] in
/-- Every element of `facetCone S u` has the form `t • y` with `t ∈ [0, 1]` and `y ∈ polytopeFacet S u`
(whenever `polytopeFacet S u` is nonempty). -/
lemma mem_facetCone_iff {S : Finset E} {u : E} (hu : u ∈ polarBody (S : Set E))
    (hFne : (polytopeFacet S u).Nonempty) {x : E} :
    x ∈ facetCone S u ↔ ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ polytopeFacet S u, x = t • y := by
  have hFconv : Convex ℝ (polytopeFacet S u) := by
    rw [polytopeFacet_eq_convexHull_tightVertices hu]
    exact convex_convexHull ℝ _
  constructor
  · intro hx
    have hset_conv : Convex ℝ {z : E | ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ polytopeFacet S u, z = t • y} := by
      rintro z₁ ⟨t₁, ⟨ht₁0, ht₁1⟩, y₁, hy₁, rfl⟩ z₂ ⟨t₂, ⟨ht₂0, ht₂1⟩, y₂, hy₂, rfl⟩
        a b ha hb hab
      let t : ℝ := a * t₁ + b * t₂
      have ht0 : 0 ≤ t := by positivity
      have ht1 : t ≤ 1 := by nlinarith
      by_cases ht_eq : t = 0
      · obtain ⟨y₀, hy₀⟩ := hFne
        refine ⟨0, ⟨le_rfl, zero_le_one⟩, y₀, hy₀, ?_⟩
        have h1 : a * t₁ = 0 := by nlinarith
        have h2 : b * t₂ = 0 := by nlinarith
        simp [smul_smul, h1, h2]
      · have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht_eq)
        let y : E := (a * t₁ / t) • y₁ + (b * t₂ / t) • y₂
        have hy_mem : y ∈ polytopeFacet S u :=
          hFconv hy₁ hy₂ (div_nonneg (mul_nonneg ha ht₁0) ht_pos.le)
            (div_nonneg (mul_nonneg hb ht₂0) ht_pos.le)
            (by rw [← add_div]; exact div_self ht_pos.ne')
        refine ⟨t, ⟨ht0, ht1⟩, y, hy_mem, ?_⟩
        dsimp only [y]
        rw [smul_add, smul_smul, smul_smul, smul_smul, smul_smul,
          mul_div_cancel₀ _ ht_pos.ne', mul_div_cancel₀ _ ht_pos.ne']
    have hsub : insert (0 : E) (polytopeFacet S u) ⊆
        {z : E | ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ polytopeFacet S u, z = t • y} := by
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hzF
      · obtain ⟨y₀, hy₀⟩ := hFne
        exact ⟨0, ⟨le_rfl, zero_le_one⟩, y₀, hy₀, by simp⟩
      · exact ⟨1, ⟨zero_le_one, le_rfl⟩, z, hzF, by simp⟩
    exact convexHull_min hsub hset_conv hx
  · rintro ⟨t, ⟨ht0, ht1⟩, y, hyF, rfl⟩
    have hcomb : (1 - t) • (0 : E) + t • y = t • y := by simp
    rw [← hcomb]
    exact (convex_convexHull ℝ _)
      (subset_convexHull ℝ _ (Set.mem_insert 0 _))
      (subset_convexHull ℝ _ (Set.mem_insert_of_mem 0 hyF))
      (sub_nonneg.mpr ht1) ht0 (by ring)

/-- **Radial Facet-Cone Covering:**
When `0 ∈ interior (convexHull ℝ S)` and `E` is nontrivial, the cones `facetCone S u` over
`u ∈ facetNormals S` cover `convexHull ℝ S`. -/
theorem iUnion_facetCone_eq [Nontrivial E] {S : Finset E}
    (h0 : (0 : E) ∈ interior (convexHull ℝ (S : Set E))) :
    (⋃ u ∈ facetNormals S, facetCone S u) = convexHull ℝ (S : Set E) := by
  have hU_ne : (facetNormals S).Nonempty := by
    have hP_comp : IsCompact (polarBody (S : Set E)) := by
      rw [← polarBody_convexHull]
      exact isCompact_polarBody_of_zero_mem_interior h0
    obtain ⟨u, hu⟩ := hP_comp.extremePoints_nonempty (polarBody_nonempty _)
    exact ⟨u, mem_facetNormals.mpr hu⟩
  apply Set.Subset.antisymm
  · refine Set.iUnion₂_subset fun u _ => facetCone_subset_convexHull (interior_subset h0) u
  · intro x hx
    by_cases hx0 : x = 0
    · obtain ⟨u, hu⟩ := hU_ne
      exact Set.mem_biUnion hu (hx0 ▸ subset_convexHull ℝ _ (Set.mem_insert 0 _))
    · obtain ⟨u, hu, hu_max⟩ := Finset.exists_mem_eq_sup' hU_ne fun v => ⟪x, v⟫
      set t : ℝ := ⟪x, u⟫
      have ht_le_one : t ≤ 1 := by
        rw [weyl_minkowski_halfspaces h0] at hx
        exact hx u hu
      have ht_pos : 0 < t := by
        by_contra hle
        push Not at hle
        obtain ⟨R, hR⟩ := (S.finite_toSet.isCompact_convexHull ℝ).isBounded.subset_closedBall 0
        let c : ℝ := (max R 0 + 1) / ‖x‖
        have hc_pos : 0 < c := div_pos (by positivity) (norm_pos_iff.mpr hx0)
        have hcx_mem : c • x ∈ convexHull ℝ (S : Set E) := by
          rw [weyl_minkowski_halfspaces h0]
          intro v hv
          have hxv : ⟪x, v⟫ ≤ t := hu_max ▸ Finset.le_sup' (f := fun w => ⟪x, w⟫) hv
          rw [inner_smul_left, RCLike.conj_to_real]
          have : c * ⟪x, v⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc_pos.le (hxv.trans hle)
          linarith
        have hcx_norm : ‖c • x‖ ≤ R := by simpa [Metric.mem_closedBall] using hR hcx_mem
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc_pos] at hcx_norm
        dsimp only [c] at hcx_norm
        rw [div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx0)] at hcx_norm
        linarith [le_max_left R 0]
      let y : E := t⁻¹ • x
      have hy_F : y ∈ polytopeFacet S u := by
        refine ⟨?_, ?_⟩
        · rw [weyl_minkowski_halfspaces h0]
          intro v hv
          have hxv : ⟪x, v⟫ ≤ t := hu_max ▸ Finset.le_sup' (f := fun w => ⟪x, w⟫) hv
          rw [inner_smul_left, RCLike.conj_to_real]
          calc
            t⁻¹ * ⟪x, v⟫ ≤ t⁻¹ * t := mul_le_mul_of_nonneg_left hxv (inv_nonneg.mpr ht_pos.le)
            _ = 1 := inv_mul_cancel₀ ht_pos.ne'
        · rw [inner_smul_left, RCLike.conj_to_real]
          exact inv_mul_cancel₀ ht_pos.ne'
      have hx_cone : x ∈ facetCone S u := by
        rw [mem_facetCone_iff (facetNormals_subset_polarBody S hu) ⟨y, hy_F⟩]
        exact ⟨t, ⟨ht_pos.le, ht_le_one⟩, y, hy_F, by simp [y, smul_smul, mul_inv_cancel₀ ht_pos.ne']⟩
      exact Set.mem_biUnion hu hx_cone

/-- **Pairwise `AEDisjoint` Facet Cones:**
Distinct facet cones `facetCone S u₁`, `facetCone S u₂` (`u₁ ≠ u₂ ∈ facetNormals S`) overlap
only inside the hyperplane `(u₁ - u₂)⊥`, which has Haar measure `0`. -/
theorem pairwise_aedisjoint_facetCone [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {S : Finset E} :
    (facetNormals S : Set E).Pairwise (Function.onFun (AEDisjoint μ) (facetCone S)) := by
  intro u₁ hu₁ u₂ hu₂ hne
  change μ (facetCone S u₁ ∩ facetCone S u₂) = 0
  have hsub : facetCone S u₁ ∩ facetCone S u₂ ⊆ ((ℝ ∙ (u₁ - u₂))ᗮ : Set E) := by
    intro x ⟨hx₁, hx₂⟩
    by_cases hx0 : x = 0
    · rw [hx0]; exact Submodule.zero_mem _
    · have hFne₁ : (polytopeFacet S u₁).Nonempty := by
        by_contra hemp
        rw [Set.not_nonempty_iff_eq_empty] at hemp
        have : facetCone S u₁ = {0} := by simp [facetCone, hemp]
        rw [this] at hx₁
        exact hx0 hx₁
      have hFne₂ : (polytopeFacet S u₂).Nonempty := by
        by_contra hemp
        rw [Set.not_nonempty_iff_eq_empty] at hemp
        have : facetCone S u₂ = {0} := by simp [facetCone, hemp]
        rw [this] at hx₂
        exact hx0 hx₂
      have hu₁_pol : u₁ ∈ polarBody (S : Set E) := facetNormals_subset_polarBody S hu₁
      have hu₂_pol : u₂ ∈ polarBody (S : Set E) := facetNormals_subset_polarBody S hu₂
      rw [mem_facetCone_iff hu₁_pol hFne₁] at hx₁
      rw [mem_facetCone_iff hu₂_pol hFne₂] at hx₂
      obtain ⟨t₁, ⟨ht₁0, _⟩, y₁, hy₁, hxy₁⟩ := hx₁
      obtain ⟨t₂, ⟨ht₂0, _⟩, y₂, hy₂, hxy₂⟩ := hx₂
      have hy₁_u₂ : ⟪y₁, u₂⟫ ≤ 1 := (polarBody_convexHull (S : Set E) ▸ hu₂_pol) y₁ hy₁.1
      have hy₂_u₁ : ⟪y₂, u₁⟫ ≤ 1 := (polarBody_convexHull (S : Set E) ▸ hu₁_pol) y₂ hy₂.1
      have hle1 : ⟪x, u₂⟫ ≤ ⟪x, u₁⟫ := by
        rw [hxy₁, inner_smul_left, inner_smul_left]
        simp only [RCLike.conj_to_real, hy₁.2, mul_one]
        exact (mul_le_mul_of_nonneg_left hy₁_u₂ ht₁0).trans_eq (mul_one t₁)
      have hle2 : ⟪x, u₁⟫ ≤ ⟪x, u₂⟫ := by
        rw [hxy₂, inner_smul_left, inner_smul_left]
        simp only [RCLike.conj_to_real, hy₂.2, mul_one]
        exact (mul_le_mul_of_nonneg_left hy₂_u₁ ht₂0).trans_eq (mul_one t₂)
      change x ∈ (ℝ ∙ (u₁ - u₂))ᗮ
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right]
      linarith
  have hne_top : (ℝ ∙ (u₁ - u₂))ᗮ ≠ ⊤ := by
    intro htop
    have hmem : u₁ - u₂ ∈ (ℝ ∙ (u₁ - u₂))ᗮ := htop ▸ Submodule.mem_top
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_self_eq_norm_sq] at hmem
    exact hne (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hmem)))
  exact measure_mono_null hsub (Measure.addHaar_submodule μ _ hne_top)

/-- **Radial Facet-Cone Volume Sum Formula:**
When `0 ∈ interior (convexHull ℝ S)` and `E` is nontrivial, the additive Haar measure of
`convexHull ℝ S` equals the sum of the measures of its origin-apex facet cones `facetCone S u`. -/
theorem addHaar_convexHull_eq_sum_facetCone [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {S : Finset E}
    (h0 : (0 : E) ∈ interior (convexHull ℝ (S : Set E))) :
    μ (convexHull ℝ (S : Set E)) = ∑ u ∈ facetNormals S, μ (facetCone S u) := by
  classical
  rw [← iUnion_facetCone_eq h0]
  have hmeas : ∀ u : facetNormals S, NullMeasurableSet (facetCone S u.1) μ := by
    intro u
    have hF_eq : polytopeFacet S u.1 = convexHull ℝ (tightVertices S u.1 : Set E) :=
      polytopeFacet_eq_convexHull_tightVertices (facetNormals_subset_polarBody S u.2)
    have hcone_eq : facetCone S u.1 = convexHull ℝ (insert (0 : E) (tightVertices S u.1 : Set E)) := by
      unfold facetCone
      rw [hF_eq]
      apply Set.Subset.antisymm
      · refine convexHull_min ?_ (convex_convexHull ℝ _)
        intro x hx
        rcases Set.mem_insert_iff.mp hx with rfl | hxch
        · exact subset_convexHull ℝ _ (Set.mem_insert 0 _)
        · exact convexHull_mono (Set.subset_insert 0 _) hxch
      · refine convexHull_min ?_ (convex_convexHull ℝ _)
        intro x hx
        rcases Set.mem_insert_iff.mp hx with rfl | hxt
        · exact subset_convexHull ℝ _ (Set.mem_insert 0 _)
        · exact subset_convexHull ℝ _ (Set.mem_insert_of_mem 0 (subset_convexHull ℝ _ hxt))
    have hcomp : IsCompact (facetCone S u.1) := by
      rw [hcone_eq]
      exact ((tightVertices S u.1).finite_toSet.insert (0 : E)).isCompact_convexHull ℝ
    exact hcomp.isClosed.measurableSet.nullMeasurableSet
  have hpw : Pairwise (Function.onFun (AEDisjoint μ) (fun u : facetNormals S => facetCone S u.1)) := by
    intro u₁ u₂ hne
    exact pairwise_aedisjoint_facetCone μ u₁.2 u₂.2 (fun h => hne (Subtype.ext h))
  have hunion : (⋃ u ∈ facetNormals S, facetCone S u) =
      ⋃ u : facetNormals S, facetCone S u.1 := by
    ext x; simp
  rw [hunion, measure_iUnion₀ hpw hmeas, tsum_fintype, Finset.univ_eq_attach,
    Finset.sum_attach (facetNormals S) (fun u => μ (facetCone S u))]

end

end ConvexGeom
