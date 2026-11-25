module

public import ConvexGeom.Polytope
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Affine General Position in ℝᵈ and Simplicial Polytope Approximation

This module formalizes **affine general position** for finite point configurations in any
finite-dimensional real normed space `E`, establishes its density under arbitrarily small
perturbations, and combines this with `ConvexGeom.Polytope` to approximate any convex body
by polytopes whose vertices are in general position (simplicial polytopes).

## Main Results
- `InGeneralPosition v`: every finite subfamily of size `≤ finrank ℝ E + 1` is affinely
  independent (`AffineIndepOn ℝ v s`).
- `InGeneralPosition.injective`: in any nontrivial space (`finrank ℝ E ≥ 1`), general-position
  families have pairwise distinct points.
- `InGeneralPosition.comp_injective`, `InGeneralPosition.affineEquiv`: stability under
  injective reindexing and invertible affine maps.
- `addHaar_affineSpan_image_eq_zero`, `addHaar_affineSpan_finset_eq_zero`: the affine span
  of at most `finrank ℝ E` points has additive Haar measure `0`.
- `exists_generalPosition_snoc`: extending a general-position `m`-tuple by one point inside
  any open ball `ball p ε`.
- `exists_generalPosition_dist_lt` & `exists_generalPosition_dist_lt_of_fintype`:
  **Density of Affine General Position** — every finite configuration can be perturbed by
  `< ε` into general position.
- `exists_generalPosition_polytope_dist_lt`: **General-Position Polytope Approximation** —
  every `ConvexBody E` can be approximated within `< ε` in Hausdorff distance by the convex
  hull of a finite family of points in general position.
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace ConvexGeom

public section

/-! ### 1. Definition and Basic Invariance -/

section GeneralPositionBasic

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A family `v : ι → E` is in **affine general position** in `E` if every finite subfamily of
cardinality at most `finrank ℝ E + 1` is affinely independent over `ℝ`. -/
def InGeneralPosition {ι : Type*} (v : ι → E) : Prop :=
  ∀ s : Finset ι, s.card ≤ Module.finrank ℝ E + 1 →
    AffineIndepOn ℝ v (s : Set ι)

/-- Equivalent `AffineIndependent` form on subtypes of cardinality `≤ finrank ℝ E + 1`. -/
lemma InGeneralPosition.affineIndependent {ι : Type*} {v : ι → E} (hv : InGeneralPosition v)
    {s : Finset ι} (hs : s.card ≤ Module.finrank ℝ E + 1) :
    AffineIndependent ℝ (fun i : (s : Set ι) => v i) :=
  hv s hs

/-- Pulling back a general-position family along an injective map preserves general position. -/
lemma InGeneralPosition.comp_injective {ι κ : Type*} {v : ι → E} (hv : InGeneralPosition v)
    {f : κ → ι} (hf : Function.Injective f) :
    InGeneralPosition (v ∘ f) := by
  classical
  intro s hs
  have hcard : (s.image f).card ≤ Module.finrank ℝ E + 1 :=
    (Finset.card_image_le).trans hs
  have hind : AffineIndependent ℝ (fun i : ((s.image f : Finset ι) : Set ι) => v i) :=
    hv (s.image f) hcard
  let emb : (s : Set κ) ↪ ((s.image f : Finset ι) : Set ι) :=
    ⟨fun x => ⟨f x.1, Finset.mem_coe.mpr (Finset.mem_image_of_mem f (Finset.mem_coe.mp x.2))⟩,
      fun a b hab => Subtype.ext (hf (congrArg Subtype.val hab))⟩
  exact hind.comp_embedding emb

/-- Any invertible affine transformation preserves general position. -/
lemma InGeneralPosition.affineEquiv {F : Type*} [AddCommGroup F] [Module ℝ F]
    {ι : Type*} {v : ι → E} (hv : InGeneralPosition v) (e : E ≃ᵃ[ℝ] F) :
    InGeneralPosition (e ∘ v) := by
  intro s hs
  have hdim : Module.finrank ℝ E = Module.finrank ℝ F := e.linear.finrank_eq
  rw [← hdim] at hs
  exact (e.affineIndepOn_iff (s := (s : Set ι)) (p := v)).mpr (hv s hs)

/-- In any nontrivial finite-dimensional space (`finrank ℝ E ≥ 1`), points in general position
are pairwise distinct. -/
theorem InGeneralPosition.injective [FiniteDimensional ℝ E] [Nontrivial E]
    {ι : Type*} {v : ι → E} (hv : InGeneralPosition v) :
    Function.Injective v := by
  classical
  intro i j hij
  by_contra hne
  have hcard : ({i, j} : Finset ι).card ≤ Module.finrank ℝ E + 1 := by
    rw [Finset.card_pair hne]
    exact Nat.succ_le_succ Module.finrank_pos
  have hind := hv {i, j} hcard
  have hcoe : (({i, j} : Finset ι) : Set ι) = {i, j} := by simp
  rw [hcoe, affineIndepOn_pair_iff ℝ hne] at hind
  exact hind hij

end GeneralPositionBasic

/-! ### 2. Measure Zero of Low-Dimensional Affine Spans -/

section AffineSpanMeasure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The affine span of at most `finrank ℝ E` points in `E` has additive Haar measure `0`. -/
theorem addHaar_affineSpan_image_eq_zero [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {ι : Type*} (v : ι → E) (s : Finset ι) (hs : s.card ≤ Module.finrank ℝ E) :
    μ (affineSpan ℝ (v '' (s : Set ι)) : Set E) = 0 := by
  have henc : ((s : Set ι).encard) ≤ (Module.finrank ℝ E : ENat) := by
    rw [Set.encard_coe_eq_coe_finsetCard]
    exact Nat.cast_le.mpr hs
  have hne : affineSpan ℝ (v '' (s : Set ι)) ≠ ⊤ :=
    affineSpan_image_ne_top_of_encard_le_finrank ℝ henc v
  exact Measure.addHaar_affineSubspace μ _ hne

/-- The affine span of a finite set of at most `finrank ℝ E` points has measure `0`. -/
theorem addHaar_affineSpan_finset_eq_zero [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (S : Finset E) (hS : S.card ≤ Module.finrank ℝ E) :
    μ (affineSpan ℝ (S : Set E) : Set E) = 0 := by
  simpa using addHaar_affineSpan_image_eq_zero μ id S hS

end AffineSpanMeasure

/-! ### 3. Density of Affine General Position in ℝᵈ -/

section Density

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **One-point general-position extension:**
given a general-position `m`-tuple `w : Fin m → E`, any center `p : E`, and any `ε > 0`,
there exists `q ∈ ball p ε` such that `Fin.snoc w q` is in general position. -/
theorem exists_generalPosition_snoc {m : ℕ} (w : Fin m → E) (hw : InGeneralPosition w)
    (p : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ q ∈ ball p ε, InGeneralPosition (Fin.snoc (α := fun _ => E) w q) := by
  classical
  set d := Module.finrank ℝ E
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  let μ : Measure E := (Module.finBasis ℝ E).addHaar
  let badSets : Finset (Finset (Fin m)) := Finset.univ.powerset.filter (fun t => t.card ≤ d)
  let bad : Set E := ⋃ t ∈ (badSets : Set (Finset (Fin m))),
    (affineSpan ℝ (w '' (t : Set (Fin m))) : Set E)
  have hbad_zero : μ bad = 0 := by
    rw [measure_biUnion_null_iff (Finset.countable_toSet badSets)]
    intro t ht
    have ht_card : t.card ≤ d := (Finset.mem_filter.mp ht).2
    exact addHaar_affineSpan_image_eq_zero μ w t ht_card
  have hball_pos : 0 < μ (ball p ε) :=
    isOpen_ball.measure_pos μ ⟨p, mem_ball_self hε⟩
  have hnot_sub : ¬ (ball p ε ⊆ bad) := fun hsub =>
    hball_pos.ne' (le_antisymm ((measure_mono hsub).trans_eq hbad_zero) zero_le)
  obtain ⟨q, hq_ball, hq_not_bad⟩ := Set.not_subset.mp hnot_sub
  have hq_avoid : ∀ t : Finset (Fin m), t.card ≤ d →
      q ∉ affineSpan ℝ (w '' (t : Set (Fin m))) := by
    intro t ht hmem
    apply hq_not_bad
    exact Set.mem_biUnion (x := t)
      (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ t), ht⟩) hmem
  let w' : Fin (m + 1) → E := Fin.snoc (α := fun _ => E) w q
  refine ⟨q, hq_ball, ?_⟩
  -- Helper: any subset `s' ⊆ Fin (m + 1)` not containing `Fin.last m` pulls back along
  -- `Fin.castSucc` to a subset `t ⊆ Fin m` of the same cardinality.
  have hpull : ∀ s' : Finset (Fin (m + 1)), Fin.last m ∉ s' →
      let t := s'.preimage Fin.castSucc (Fin.castSucc_injective m).injOn
      t.card = s'.card ∧
      (Fin.castSucc : Fin m → Fin (m + 1)) '' (t : Set (Fin m)) = (s' : Set (Fin (m + 1))) := by
    intro s' hlast
    set t := s'.preimage Fin.castSucc (Fin.castSucc_injective m).injOn
    have himg : t.image Fin.castSucc = s' := by
      ext i
      simp only [Finset.mem_image, t, Finset.mem_preimage]
      constructor
      · rintro ⟨j, hj, rfl⟩; exact hj
      · intro hi
        revert hi
        refine Fin.lastCases ?_ (fun j hj => ⟨j, hj, rfl⟩) i
        exact fun h => (hlast h).elim
    have hcard : t.card = s'.card := by
      rw [← himg, Finset.card_image_of_injective _ (Fin.castSucc_injective m)]
    have hset : (Fin.castSucc : Fin m → Fin (m + 1)) '' (t : Set (Fin m)) =
        (s' : Set (Fin (m + 1))) := by
      rw [← Finset.coe_image, himg]
    exact ⟨hcard, hset⟩
  -- Helper: `AffineIndepOn ℝ w' s'` whenever `Fin.last m ∉ s'` and `s'.card ≤ d + 1`.
  have hind_no_last : ∀ s' : Finset (Fin (m + 1)), Fin.last m ∉ s' → s'.card ≤ d + 1 →
      AffineIndepOn ℝ w' (s' : Set (Fin (m + 1))) := by
    intro s' hlast hcard
    set t := s'.preimage Fin.castSucc (Fin.castSucc_injective m).injOn
    obtain ⟨ht_card, ht_img⟩ := hpull s' hlast
    have hwt : AffineIndepOn ℝ w (t : Set (Fin m)) := hw t (ht_card.trans_le hcard)
    have hcomp : AffineIndepOn ℝ (w' ∘ Fin.castSucc) (t : Set (Fin m)) := by
      have hfun : (w' ∘ Fin.castSucc : Fin m → E) = w := by
        ext j; exact Fin.snoc_castSucc (α := fun _ => E) q w j
      rwa [hfun]
    rw [← ht_img]
    exact hcomp.image_of_comp
  intro s hs
  by_cases hlast : Fin.last m ∈ s
  · set s' := s.erase (Fin.last m)
    have hlast' : Fin.last m ∉ s' := Finset.notMem_erase (Fin.last m) s
    have hs'_card : s'.card ≤ d := by
      have h1 : s'.card + 1 = s.card := Finset.card_erase_add_one hlast
      omega
    have hind' : AffineIndepOn ℝ w' (s' : Set (Fin (m + 1))) :=
      hind_no_last s' hlast' (Nat.le_succ_of_le hs'_card)
    set t := s'.preimage Fin.castSucc (Fin.castSucc_injective m).injOn
    obtain ⟨ht_card, ht_img⟩ := hpull s' hlast'
    have himg_eq : w' '' (s' : Set (Fin (m + 1))) = w '' (t : Set (Fin m)) := by
      rw [← ht_img, ← Set.image_comp]
      congr 1; ext j; exact Fin.snoc_castSucc (α := fun _ => E) q w j
    have hnot_span : w' (Fin.last m) ∉ affineSpan ℝ (w' '' (s' : Set (Fin (m + 1)))) := by
      have hlast_eq : w' (Fin.last m) = q := Fin.snoc_last (α := fun _ => E) q w
      rw [hlast_eq, himg_eq]
      exact hq_avoid t (ht_card.trans_le hs'_card)
    have hins : (s : Set (Fin (m + 1))) = insert (Fin.last m) (s' : Set (Fin (m + 1))) := by
      ext i
      simp only [Finset.mem_coe, Set.mem_insert_iff, s', Finset.mem_erase]
      by_cases hi : i = Fin.last m
      · subst hi; simp [hlast]
      · simp [hi]
    rw [hins]
    exact hind'.insert hnot_span
  · exact hind_no_last s hlast hs

/-- **Density of Affine General Position in `ℝᵈ` (indexed by `Fin m`):**
for any finite point configuration `v : Fin m → E` and any `ε > 0`, there exists a
general-position configuration `w : Fin m → E` with `dist (w i) (v i) < ε` for every `i`. -/
theorem exists_generalPosition_dist_lt {m : ℕ} (v : Fin m → E) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : Fin m → E, InGeneralPosition w ∧ ∀ i, dist (w i) (v i) < ε := by
  induction m with
  | zero =>
    refine ⟨Fin.elim0, ?_, fun i => Fin.elim0 i⟩
    intro s _
    exact affineIndependent_of_subsingleton ℝ _
  | succ m ih =>
    obtain ⟨w, hw_gp, hw_dist⟩ := ih (Fin.init v)
    obtain ⟨q, hq_ball, hq_gp⟩ := exists_generalPosition_snoc w hw_gp (v (Fin.last m)) hε
    refine ⟨Fin.snoc (α := fun _ => E) w q, hq_gp, fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [Fin.snoc_last] using Metric.mem_ball.mp hq_ball
    · simpa [Fin.snoc_castSucc, Fin.init] using hw_dist j

/-- **Density of Affine General Position (arbitrary `Fintype` index set):**
for any finite-indexed family `v : ι → E` and `ε > 0`, there exists `w : ι → E` in general
position with `dist (w i) (v i) < ε` for every `i : ι`. -/
theorem exists_generalPosition_dist_lt_of_fintype {ι : Type*} [Fintype ι]
    (v : ι → E) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : ι → E, InGeneralPosition w ∧ ∀ i, dist (w i) (v i) < ε := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  obtain ⟨w', hw'_gp, hw'_dist⟩ := exists_generalPosition_dist_lt (v ∘ e.symm) hε
  refine ⟨w' ∘ e, hw'_gp.comp_injective e.injective, fun i => ?_⟩
  simpa using hw'_dist (e i)

end Density

/-! ### 4. General-Position (Simplicial) Polytope Approximation -/

section SimplicialApproximation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **General-Position Polytope Approximation:**
every convex body `K : ConvexBody E` can be approximated within `< ε` in the Hausdorff metric
by the convex hull of a nonempty finite set `S = range w` whose points `w : Fin m → E` are in
affine general position. -/
theorem exists_generalPosition_polytope_dist_lt (K : ConvexBody E) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (w : Fin m → E) (S : Finset E) (hS : S.Nonempty),
      InGeneralPosition w ∧ (S : Set E) = Set.range w ∧
      dist (bodyConvexHull S hS) K < ε := by
  classical
  obtain ⟨T, hT_ne, _, _, hTK⟩ := exists_polytope_dist_lt K (half_pos hε)
  set m := T.card
  have hm : 0 < m := Finset.card_pos.mpr hT_ne
  have _ : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  let e : T ≃ Fin m := T.equivFin
  let v : Fin m → E := fun i => (e.symm i).1
  have hrange_v : Set.range v = (T : Set E) := by
    ext x
    simp only [Set.mem_range, v, Finset.mem_coe]
    constructor
    · rintro ⟨i, rfl⟩; exact (e.symm i).2
    · intro hx; exact ⟨e ⟨x, hx⟩, by simp⟩
  obtain ⟨w, hw_gp, hw_dist⟩ := exists_generalPosition_dist_lt v (half_pos hε)
  let S : Finset E := Finset.univ.image w
  have hS_ne : S.Nonempty := ⟨w ⟨0, hm⟩, Finset.mem_image_of_mem w (Finset.mem_univ _)⟩
  have hrange_w : (S : Set E) = Set.range w := by
    ext x; simp [S]
  let Q := bodyConvexHull S hS_ne
  have hQT : dist Q (bodyConvexHull T hT_ne) ≤ ε / 2 := by
    rw [← ConvexBody.hausdorffDist_coe, coe_bodyConvexHull, coe_bodyConvexHull,
      hrange_w, ← hrange_v]
    exact hausdorffDist_convexHull_range_le w v (half_pos hε).le fun i => (hw_dist i).le
  refine ⟨m, w, S, hS_ne, hw_gp, hrange_w, ?_⟩
  calc
    dist Q K ≤ dist Q (bodyConvexHull T hT_ne) + dist (bodyConvexHull T hT_ne) K :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hQT hTK
    _ = ε := add_halves ε

end SimplicialApproximation

end

end ConvexGeom
