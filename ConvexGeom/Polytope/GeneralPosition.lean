/-
Copyright (c) 2026 Yegor Gorodzha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yegor Gorodzha
-/
module

public import ConvexGeom.Polytope.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Affine and Spherical General Position and Polytope Approximation

This module formalizes affine and spherical general position for finite point configurations in a
finite-dimensional real normed or inner product space `E`, establishes their density under
arbitrarily small perturbations, and approximates convex bodies by general-position polytopes.

## Main definitions

* `ConvexGeom.InGeneralPosition`: every finite subfamily of size `≤ finrank ℝ E + 1` is affinely
  independent (`AffineIndepOn ℝ v s`).
* `ConvexGeom.InSphericalGeneralPosition`: spherical general position on `Metric.sphere 0 r`.

## Main statements

* `ConvexGeom.InGeneralPosition.injective`, `ConvexGeom.InGeneralPosition.comp_injective`,
  `ConvexGeom.InGeneralPosition.affineEquiv`: injectivity and invariance properties.
* `ConvexGeom.nonempty_interior_convexHull_of_inGeneralPosition`: convex hull of at least
  `finrank ℝ E + 1` points in general position has nonempty interior.
* `ConvexGeom.addHaar_affineSpan_image_eq_zero`, `ConvexGeom.addHaar_affineSpan_finset_eq_zero`:
  the affine span of at most `finrank ℝ E` points has additive Haar measure `0`.
* `ConvexGeom.exists_generalPosition_dist_lt`,
  `ConvexGeom.exists_sphericalGeneralPosition_dist_lt`: density of affine and spherical general
  position under arbitrarily small perturbations.
* `ConvexGeom.exists_generalPosition_polytope_dist_lt`,
  `ConvexGeom.exists_inscribed_generalPosition_polytope_dist_lt`: general-position and inscribed
  full-dimensional polytope approximation.
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace ConvexGeom

public section

/-! ### 1. Definition and Basic Invariance -/

section GeneralPositionBasic

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A family `v : ι → E` in a real vector space `E` is in **affine general position** if every
finite subfamily of cardinality at most `finrank ℝ E + 1` is affinely independent over `ℝ`.

This definition is intended for finite-dimensional spaces (where `Module.finrank ℝ E` equals the
vector-space dimension); in dimension `0`, `finrank ℝ E + 1 = 1` and every family satisfies
`InGeneralPosition` (since singletons are affinely independent). -/
@[expose]
def InGeneralPosition {ι : Type*} (v : ι → E) : Prop :=
  ∀ s : Finset ι, s.card ≤ Module.finrank ℝ E + 1 →
    AffineIndepOn ℝ v (s : Set ι)

/-- Equivalent `AffineIndependent` form on subtypes of cardinality `≤ finrank ℝ E + 1`. -/
lemma InGeneralPosition.affineIndependent {ι : Type*} {v : ι → E}
    (hv : InGeneralPosition v) {s : Finset ι} (hs : s.card ≤ Module.finrank ℝ E + 1) :
    AffineIndependent ℝ (fun i : (s : Set ι) => v i) :=
  hv s hs

/-- Pulling back a general-position family along an injective map preserves general position. -/
lemma InGeneralPosition.comp_injective {ι κ : Type*} {v : ι → E}
    (hv : InGeneralPosition v) {f : κ → ι} (hf : Function.Injective f) :
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

/-- Helper: every open ball `ball p ε` contains a point avoiding the affine spans of all
subfamilies of `w` of cardinality at most `finrank ℝ E`. -/
private lemma exists_avoiding_affineSpans {m : ℕ} (w : Fin m → E) (p : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ q ∈ ball p ε, ∀ t : Finset (Fin m), t.card ≤ Module.finrank ℝ E →
      q ∉ affineSpan ℝ (w '' (t : Set (Fin m))) := by
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
    exact addHaar_affineSpan_image_eq_zero μ w t (Finset.mem_filter.mp ht).2
  have hball_pos : 0 < μ (ball p ε) :=
    isOpen_ball.measure_pos μ ⟨p, mem_ball_self hε⟩
  have hnot_sub : ¬ (ball p ε ⊆ bad) := fun hsub =>
    hball_pos.ne' (le_antisymm ((measure_mono hsub).trans_eq hbad_zero) zero_le)
  obtain ⟨q, hq_ball, hq_not_bad⟩ := Set.not_subset.mp hnot_sub
  refine ⟨q, hq_ball, fun t ht hmem => hq_not_bad ?_⟩
  exact Set.mem_biUnion (x := t)
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ t), ht⟩) hmem

omit [FiniteDimensional ℝ E] in
/-- Helper: appending a point `q` outside every affine span of at most `finrank ℝ E` points of `w`
preserves affine general position. -/
private lemma inGeneralPosition_snoc_of_notMem_affineSpan {m : ℕ} {w : Fin m → E}
    (hw : InGeneralPosition w) {q : E}
    (hq : ∀ t : Finset (Fin m), t.card ≤ Module.finrank ℝ E →
      q ∉ affineSpan ℝ (w '' (t : Set (Fin m)))) :
    InGeneralPosition (Fin.snoc (α := fun _ => E) w q) := by
  classical
  set d := Module.finrank ℝ E
  let w' : Fin (m + 1) → E := Fin.snoc (α := fun _ => E) w q
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
    refine ⟨?_, ?_⟩
    · rw [← himg, Finset.card_image_of_injective _ (Fin.castSucc_injective m)]
    · rw [← Finset.coe_image, himg]
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
      exact hq t (ht_card.trans_le hs'_card)
    have hins : (s : Set (Fin (m + 1))) = insert (Fin.last m) (s' : Set (Fin (m + 1))) := by
      ext i
      simp only [Finset.mem_coe, Set.mem_insert_iff, s', Finset.mem_erase]
      by_cases hi : i = Fin.last m
      · subst hi; simp [hlast]
      · simp [hi]
    rw [hins]
    exact hind'.insert hnot_span
  · exact hind_no_last s hlast hs

/-- **One-point general-position extension:**
given a general-position `m`-tuple `w : Fin m → E`, any center `p : E`, and any `ε > 0`,
there exists `q ∈ ball p ε` such that `Fin.snoc w q` is in general position. -/
theorem exists_generalPosition_snoc {m : ℕ} (w : Fin m → E) (hw : InGeneralPosition w)
    (p : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ q ∈ ball p ε, InGeneralPosition (Fin.snoc (α := fun _ => E) w q) := by
  obtain ⟨q, hq_ball, hq_avoid⟩ := exists_avoiding_affineSpans w p hε
  exact ⟨q, hq_ball, inGeneralPosition_snoc_of_notMem_affineSpan hw hq_avoid⟩

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
theorem exists_generalPosition_dist_lt_of_fintype {ι : Type*} [Finite ι]
    (v : ι → E) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : ι → E, InGeneralPosition w ∧ ∀ i, dist (w i) (v i) < ε := by
  have : Fintype ι := Fintype.ofFinite ι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  obtain ⟨w', hw'_gp, hw'_dist⟩ := exists_generalPosition_dist_lt (v ∘ e.symm) hε
  refine ⟨w' ∘ e, hw'_gp.comp_injective e.injective, fun i => ?_⟩
  simpa using hw'_dist (e i)

/-- The convex hull of at least `finrank ℝ E + 1` points in general position has nonempty
interior (is full-dimensional). -/
theorem nonempty_interior_convexHull_of_inGeneralPosition {m : ℕ} {w : Fin m → E}
    (hw : InGeneralPosition w) (hm : Module.finrank ℝ E + 1 ≤ m) :
    (interior (convexHull ℝ (Set.range w))).Nonempty := by
  set d := Module.finrank ℝ E
  let f : Fin (d + 1) → Fin m := Fin.castLE hm
  have hw_sub : InGeneralPosition (w ∘ f) := hw.comp_injective (Fin.castLE_injective hm)
  have hind_on : AffineIndepOn ℝ (w ∘ f) (Finset.univ : Finset (Fin (d + 1))) :=
    hw_sub Finset.univ (by simp [d])
  have hind : AffineIndependent ℝ (w ∘ f) := by
    let emb : Fin (d + 1) ↪ ((Finset.univ : Finset (Fin (d + 1))) : Set (Fin (d + 1))) :=
      ⟨fun i => ⟨i, Finset.mem_univ i⟩, fun _ _ h => congrArg Subtype.val h⟩
    exact hind_on.comp_embedding emb
  have hfinrank : Module.finrank ℝ (vectorSpan ℝ (Set.range (w ∘ f))) = d :=
    hind.finrank_vectorSpan (Fintype.card_fin (d + 1))
  have hdir_top : (affineSpan ℝ (Set.range (w ∘ f))).direction = ⊤ := by
    rw [direction_affineSpan]
    exact Submodule.eq_top_of_finrank_eq hfinrank
  have hne_sub : (Set.range (w ∘ f)).Nonempty := Set.range_nonempty _
  have hspan_sub : affineSpan ℝ (Set.range (w ∘ f)) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hx₀ : w (f ⟨0, Nat.succ_pos d⟩) ∈ affineSpan ℝ (Set.range (w ∘ f)) :=
      subset_affineSpan ℝ _ ⟨⟨0, Nat.succ_pos d⟩, rfl⟩
    have hdir : y -ᵥ w (f ⟨0, Nat.succ_pos d⟩) ∈ (affineSpan ℝ (Set.range (w ∘ f))).direction := by
      rw [hdir_top]; trivial
    simpa [vsub_vadd] using AffineSubspace.vadd_mem_of_mem_direction hdir hx₀
  have hsub_hull : Set.range (w ∘ f) ⊆ convexHull ℝ (Set.range w) := by
    rintro _ ⟨j, rfl⟩
    exact subset_convexHull ℝ (Set.range w) ⟨f j, rfl⟩
  have hspan_hull : affineSpan ℝ (convexHull ℝ (Set.range w)) = ⊤ :=
    eq_top_iff.mpr (hspan_sub ▸ affineSpan_mono ℝ hsub_hull)
  have hne_hull : (convexHull ℝ (Set.range w)).Nonempty := hne_sub.mono hsub_hull
  obtain ⟨y, hy⟩ := hne_hull.intrinsicInterior (convex_convexHull ℝ _)
  rw [mem_intrinsicInterior] at hy
  obtain ⟨⟨y', hy'mem⟩, hy'int, rfl⟩ := hy
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hy'int
  obtain ⟨r, hr, hball⟩ := hy'int
  refine ⟨y', mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨r, hr, fun z hz => ?_⟩)⟩
  have hz_mem : z ∈ affineSpan ℝ (convexHull ℝ (Set.range w)) := hspan_hull ▸ trivial
  exact hball (show (⟨z, hz_mem⟩ : affineSpan ℝ (convexHull ℝ (Set.range w))) ∈
    Metric.ball ⟨y', hy'mem⟩ r from hz)

end Density

/-! ### 4. General-Position Polytope Approximation -/

section PolytopeApproximation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Ambient General-Position Polytope Approximation:**
every convex body `K : ConvexBody E` (including lower-dimensional bodies) can be approximated
within `< ε` in the Hausdorff metric by the convex hull of a nonempty finite set `S = range w`
whose points `w : Fin m → E` are in affine general position.

Note: this theorem does not guarantee `P ⊆ K` or full-dimensionality (which are impossible when
`interior K = ∅`). For full-dimensional bodies, see `exists_inscribed_generalPosition_polytope_dist_lt`. -/
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

/-- **Inscribed Full-Dimensional General-Position Polytope Approximation:**
for every full-dimensional convex body `K : ConvexBody E` (`(interior K).Nonempty`) and every
`ε > 0`, there exists a finite general-position family `w : Fin m → E` with `S = range w` whose
convex hull `P = bodyConvexHull S hS` is:
1. inscribed in `K` (`P ⊆ K`),
2. full-dimensional (`(interior P).Nonempty`), and
3. within Hausdorff distance `< ε` of `K` (`dist P K < ε`). -/
theorem exists_inscribed_generalPosition_polytope_dist_lt (K : ConvexBody E)
    (hKint : (interior (K : Set E)).Nonempty) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (w : Fin m → E) (S : Finset E) (hS : S.Nonempty),
      InGeneralPosition w ∧ (S : Set E) = Set.range w ∧
      (bodyConvexHull S hS : Set E) ⊆ K ∧
      (interior (bodyConvexHull S hS : Set E)).Nonempty ∧
      dist (bodyConvexHull S hS) K < ε := by
  classical
  set d := Module.finrank ℝ E
  obtain ⟨x₀, hx₀_int⟩ := hKint
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx₀_int)
  obtain ⟨R₀, hKR₀⟩ := K.isBounded.subset_closedBall x₀
  set R := max R₀ 1
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hKR : (K : Set E) ⊆ closedBall x₀ R :=
    hKR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  -- Step 1: Inscribed polytope `T₀ ⊆ K` within `ε / 3`.
  obtain ⟨T₀, hT₀_ne, hT₀K, hP₀K, hP₀_dist⟩ := exists_polytope_dist_lt K (by linarith : 0 < ε / 3)
  let T : Finset E := insert x₀ T₀
  have hT_ne : T.Nonempty := ⟨x₀, Finset.mem_insert_self _ _⟩
  have hTK : (T : Set E) ⊆ K := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy₀
    · exact interior_subset hx₀_int
    · exact hT₀K hy₀
  have hPK : (bodyConvexHull T hT_ne : Set E) ⊆ K := by
    rw [coe_bodyConvexHull]
    exact convexHull_min hTK K.convex
  have hP_dist : dist (bodyConvexHull T hT_ne) K < ε / 3 := by
    have hle : dist (bodyConvexHull T hT_ne) K ≤ dist (bodyConvexHull T₀ hT₀_ne) K := by
      rw [← ConvexBody.hausdorffDist_coe]
      refine Metric.hausdorffDist_le_of_mem_dist dist_nonneg ?_ ?_
      · intro x hx
        exact ⟨x, hPK hx, by simp [dist_nonneg]⟩
      · intro y hyK
        obtain ⟨x, hxP₀, hinf⟩ := (bodyConvexHull T₀ hT₀_ne).isCompact.exists_infDist_eq_dist
          (bodyConvexHull T₀ hT₀_ne).nonempty y
        have hxP : x ∈ (bodyConvexHull T hT_ne : Set E) := by
          rw [coe_bodyConvexHull] at hxP₀ ⊢
          exact convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert x₀ T₀)) hxP₀
        refine ⟨x, hxP, ?_⟩
        rw [← hinf]
        have hcomm : Metric.hausdorffDist (K : Set E) (bodyConvexHull T₀ hT₀_ne : Set E) =
            dist (bodyConvexHull T₀ hT₀_ne) K := by
          rw [Metric.hausdorffDist_comm, ConvexBody.hausdorffDist_coe]
        exact (Metric.infDist_le_hausdorffDist_of_mem hyK ConvexBody.hausdorffEDist_ne_top).trans
          hcomm.le
    exact hle.trans_lt hP₀_dist
  -- Step 2: Shrink toward `x₀` by `α ∈ (0, 1/2]` so every vertex has clearance `α * r` inside `K`.
  set α := min (1 / 2 : ℝ) (ε / (4 * R))
  have hα_pos : 0 < α := lt_min (by norm_num) (div_pos hε (by positivity))
  have hα_le_half : α ≤ 1 / 2 := min_le_left _ _
  have hαR_lt : α * R < ε / 3 := by
    have h1 : α * R ≤ (ε / (4 * R)) * R := mul_le_mul_of_nonneg_right (min_le_right _ _) hR_pos.le
    have h2 : (ε / (4 * R)) * R = ε / 4 := by field_simp [hR_pos.ne']
    linarith
  let shrink : E → E := fun y => (1 - α) • y + α • x₀
  have hshrink_ball : ∀ y ∈ (K : Set E), ball (shrink y) (α * r) ⊆ K := by
    intro y hy z hz
    have hz_norm : ‖z - shrink y‖ < α * r := by rwa [Metric.mem_ball, dist_eq_norm] at hz
    let u : E := x₀ + α⁻¹ • (z - shrink y)
    have hu_ball : u ∈ ball x₀ r := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [u, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hα_pos)]
      have := mul_lt_mul_of_pos_left hz_norm (inv_pos.mpr hα_pos)
      rwa [← mul_assoc, inv_mul_cancel₀ hα_pos.ne', one_mul] at this
    have huK : u ∈ K := hball hu_ball
    have hz_eq : z = (1 - α) • y + α • u := by
      dsimp only [u, shrink]
      rw [smul_add, smul_smul, mul_inv_cancel₀ hα_pos.ne', one_smul]
      abel
    rw [hz_eq]
    exact K.convex hy huK (by linarith) hα_pos.le (by ring)
  have hshrink_dist : ∀ y ∈ (K : Set E), dist (shrink y) y ≤ α * R := by
    intro y hy
    have hdiff : shrink y - y = α • (x₀ - y) := by
      dsimp only [shrink]; rw [sub_smul, one_smul, smul_sub]; abel
    rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos hα_pos, ← dist_eq_norm,
      dist_comm]
    exact mul_le_mul_of_nonneg_left (Metric.mem_closedBall.mp (hKR hy)) hα_pos.le
  -- Step 3: Index `T` padded with `d + 1` copies of `x₀` so total count `m ≥ d + 1`.
  set m := T.card + (d + 1)
  have hm_ge : d + 1 ≤ m := Nat.le_add_left (d + 1) T.card
  have hm_pos : 0 < m := Nat.lt_of_lt_of_le (Nat.succ_pos d) hm_ge
  have _ : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm_pos
  let e : T ≃ Fin T.card := T.equivFin
  let u : Fin m → E := fun i =>
    if hi : i.1 < T.card then (e.symm ⟨i.1, hi⟩).1 else x₀
  have hu_mem : ∀ i, u i ∈ T := fun i => by
    dsimp only [u]; split_ifs with hi
    · exact (e.symm ⟨i.1, hi⟩).2
    · exact Finset.mem_insert_self x₀ T₀
  have hrange_u : Set.range u = (T : Set E) := by
    ext y
    simp only [Set.mem_range, Finset.mem_coe]
    constructor
    · rintro ⟨i, rfl⟩; exact hu_mem i
    · intro hy
      let j : Fin T.card := e ⟨y, hy⟩
      refine ⟨⟨j.1, Nat.lt_of_lt_of_le j.2 (Nat.le_add_right _ _)⟩, ?_⟩
      simp [u, j]
  let v : Fin m → E := fun i => shrink (u i)
  -- Step 4: Perturb `v` by `δ = min (α * r) (ε / 3)` into general position `w`.
  set δ := min (α * r) (ε / 3)
  have hδ_pos : 0 < δ := lt_min (mul_pos hα_pos hr) (by linarith)
  obtain ⟨w, hw_gp, hw_dist⟩ := exists_generalPosition_dist_lt v hδ_pos
  let S : Finset E := Finset.univ.image w
  have hS_ne : S.Nonempty := ⟨w ⟨0, hm_pos⟩, Finset.mem_image_of_mem w (Finset.mem_univ _)⟩
  have hrange_w : (S : Set E) = Set.range w := by ext x; simp [S]
  let Q := bodyConvexHull S hS_ne
  have hQK : (Q : Set E) ⊆ K := by
    rw [coe_bodyConvexHull, hrange_w]
    refine convexHull_min ?_ K.convex
    rintro _ ⟨i, rfl⟩
    have hwi_ball : w i ∈ ball (shrink (u i)) (α * r) :=
      Metric.mem_ball.mpr ((hw_dist i).trans_le (min_le_left _ _))
    exact hshrink_ball (u i) (hTK (hu_mem i)) hwi_ball
  have hQint : (interior (Q : Set E)).Nonempty := by
    rw [coe_bodyConvexHull, hrange_w]
    exact nonempty_interior_convexHull_of_inGeneralPosition hw_gp hm_ge
  have hQP : dist Q (bodyConvexHull T hT_ne) ≤ 2 * ε / 3 := by
    rw [← ConvexBody.hausdorffDist_coe, coe_bodyConvexHull, coe_bodyConvexHull,
      hrange_w, ← hrange_u]
    refine hausdorffDist_convexHull_range_le w u (by linarith) fun i => ?_
    calc
      dist (w i) (u i) ≤ dist (w i) (v i) + dist (v i) (u i) := dist_triangle _ _ _
      _ ≤ ε / 3 + α * R :=
          add_le_add ((hw_dist i).le.trans (min_le_right _ _))
            (hshrink_dist (u i) (hTK (hu_mem i)))
      _ ≤ 2 * ε / 3 := by linarith
  refine ⟨m, w, S, hS_ne, hw_gp, hrange_w, hQK, hQint, ?_⟩
  calc
    dist Q K ≤ dist Q (bodyConvexHull T hT_ne) + dist (bodyConvexHull T hT_ne) K :=
      dist_triangle _ _ _
    _ < 2 * ε / 3 + ε / 3 := add_lt_add_of_le_of_lt hQP hP_dist
    _ = ε := by ring

end PolytopeApproximation

/-! ### 5. Density of General Position on a Sphere `S(0, r)` -/

section SphericalGeneralPosition

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A family `v : ι → E` is in **spherical general position** on `sphere 0 r` if every point lies
on `sphere 0 r`, `v` is in affine general position (`InGeneralPosition v`), and every finite
subfamily of size at most `finrank ℝ E` is linearly independent over `ℝ` (equivalently, no
`≤ finrank ℝ E` points lie in a linear hyperplane through the origin). -/
@[expose]
def InSphericalGeneralPosition {ι : Type*} (r : ℝ) (v : ι → E) : Prop :=
  (∀ i, v i ∈ Metric.sphere (0 : E) r) ∧
  InGeneralPosition v ∧
  ∀ s : Finset ι, s.card ≤ Module.finrank ℝ E → LinearIndepOn ℝ v (s : Set ι)

/-- In dimension `≥ 2`, a proper affine subspace cannot contain any nonempty open patch
`ball q η ∩ sphere 0 r` (`r > 0`). -/
theorem not_ball_inter_sphere_subset_affineSubspace
    (hd : 2 ≤ Module.finrank ℝ E) {r : ℝ} (hr : 0 < r)
    {q : E} (hq : q ∈ Metric.sphere (0 : E) r) {η : ℝ} (hη : 0 < η)
    {A : AffineSubspace ℝ E} (hA : A ≠ ⊤) :
    ¬ (Metric.ball q η ∩ Metric.sphere (0 : E) r ⊆ (A : Set E)) := by
  intro hsub
  have hqA : q ∈ A := hsub ⟨Metric.mem_ball_self hη, hq⟩
  have hq_norm : ‖q‖ = r := by simpa [Metric.mem_sphere] using hq
  -- Helper: any unit vector `v ⊥ q` yields `q ∈ A.direction` and `v ∈ A.direction`.
  have horth : ∀ v : E, ⟪q, v⟫ = 0 → ‖v‖ = 1 → v ∈ A.direction ∧ q ∈ A.direction := by
    intro v hqv hv_norm
    set s : ℝ := η / 3
    have hs_pos : 0 < s := by positivity
    set R : ℝ := Real.sqrt (r ^ 2 + s ^ 2)
    have hR_pos : 0 < R := Real.sqrt_pos.mpr (by positivity)
    have hR_gt : r < R := by
      have hsq : r ^ 2 < r ^ 2 + s ^ 2 := by nlinarith
      calc
        r = Real.sqrt (r ^ 2) := (Real.sqrt_sq hr.le).symm
        _ < Real.sqrt (r ^ 2 + s ^ 2) := Real.sqrt_lt_sqrt (sq_nonneg r) hsq
    have hR_le : R ≤ r + s := by
      have hsq : r ^ 2 + s ^ 2 ≤ (r + s) ^ 2 := by nlinarith
      exact (Real.sqrt_le_iff).mpr ⟨by linarith, hsq⟩
    set c : ℝ := r / R
    have hc_pos : 0 < c := div_pos hr hR_pos
    have hc_lt_one : c < 1 := (div_lt_one hR_pos).mpr hR_gt
    have h1mc_le : 1 - c ≤ s / r := by
      have h1 : 1 - c = (R - r) / R := by
        dsimp only [c]; field_simp [hR_pos.ne']
      rw [h1]
      calc
        (R - r) / R ≤ s / R := div_le_div_of_nonneg_right (by linarith) hR_pos.le
        _ ≤ s / r := div_le_div_of_nonneg_left hs_pos.le hr hR_gt.le
    have hpm_mem : ∀ σ : ℝ, |σ| = 1 → c • (q + (σ * s) • v) ∈ A := by
      intro σ hσ
      have hσ_sq : σ ^ 2 = 1 := by
        have := sq_abs σ; rw [hσ] at this; linarith
      have hnorm_sum : ‖q + (σ * s) • v‖ = R := by
        have hsq : ‖q + (σ * s) • v‖ ^ 2 = r ^ 2 + s ^ 2 := by
          rw [norm_add_sq_real, inner_smul_right, hqv, mul_zero, mul_zero, add_zero,
            hq_norm, norm_smul, hv_norm, mul_one, Real.norm_eq_abs, sq_abs]
          calc
            r ^ 2 + (σ * s) ^ 2 = r ^ 2 + σ ^ 2 * s ^ 2 := by ring
            _ = r ^ 2 + s ^ 2 := by rw [hσ_sq, one_mul]
        rw [← Real.sqrt_sq (norm_nonneg _), hsq]
      have hsph : c • (q + (σ * s) • v) ∈ Metric.sphere (0 : E) r := by
        rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hc_pos,
          hnorm_sum]
        dsimp only [c]
        exact div_mul_cancel₀ r hR_pos.ne'
      have hball : c • (q + (σ * s) • v) ∈ Metric.ball q η := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hdiff : c • (q + (σ * s) • v) - q = (c - 1) • q + (c * (σ * s)) • v := by
          rw [smul_add, smul_smul, sub_smul, one_smul]; abel
        rw [hdiff]
        have h1 : ‖(c - 1) • q + (c * (σ * s)) • v‖ ≤
            ‖(c - 1) • q‖ + ‖(c * (σ * s)) • v‖ := norm_add_le _ _
        have h2 : ‖(c - 1) • q‖ = (1 - c) * r := by
          rw [norm_smul, hq_norm, Real.norm_eq_abs, abs_of_neg (by linarith)]; ring
        have h3 : ‖(c * (σ * s)) • v‖ = c * s := by
          rw [norm_smul, hv_norm, mul_one, Real.norm_eq_abs, abs_mul, abs_mul,
            abs_of_pos hc_pos, hσ, abs_of_pos hs_pos, one_mul]
        have h4 : (1 - c) * r ≤ s := by
          calc
            (1 - c) * r ≤ (s / r) * r := mul_le_mul_of_nonneg_right h1mc_le hr.le
            _ = s := div_mul_cancel₀ s hr.ne'
        have h5 : c * s < s := by nlinarith
        dsimp only [s] at h1 h3 h4 h5 ⊢
        linarith
      exact hsub ⟨hball, hsph⟩
    have hqp : c • (q + (1 * s) • v) ∈ A := hpm_mem 1 (by simp)
    have hqm : c • (q + (-1 * s) • v) ∈ A := hpm_mem (-1) (by simp)
    have hv_dir : v ∈ A.direction := by
      have hsub_mem : c • (q + (1 * s) • v) -ᵥ c • (q + (-1 * s) • v) ∈ A.direction :=
        AffineSubspace.vsub_mem_direction hqp hqm
      have hval : c • (q + (1 * s) • v) -ᵥ c • (q + (-1 * s) • v) = (2 * c * s) • v := by
        rw [vsub_eq_sub]; module
      rw [hval] at hsub_mem
      have hne : (2 * c * s : ℝ) ≠ 0 := by positivity
      have := A.direction.smul_mem (2 * c * s)⁻¹ hsub_mem
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
    have hq_dir : q ∈ A.direction := by
      have h1 : c • (q + (1 * s) • v) -ᵥ q ∈ A.direction :=
        AffineSubspace.vsub_mem_direction hqp hqA
      have h2 : c • (q + (-1 * s) • v) -ᵥ q ∈ A.direction :=
        AffineSubspace.vsub_mem_direction hqm hqA
      have hsum : (c • (q + (1 * s) • v) -ᵥ q) + (c • (q + (-1 * s) • v) -ᵥ q) ∈ A.direction :=
        A.direction.add_mem h1 h2
      have hval : (c • (q + (1 * s) • v) -ᵥ q) + (c • (q + (-1 * s) • v) -ᵥ q) =
          (2 * (c - 1)) • q := by
        rw [vsub_eq_sub, vsub_eq_sub]; module
      rw [hval] at hsum
      have hne : (2 * (c - 1) : ℝ) ≠ 0 := by linarith
      have := A.direction.smul_mem (2 * (c - 1))⁻¹ hsum
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
    exact ⟨hv_dir, hq_dir⟩
  -- Pick one unit vector orthogonal to `q` (exists since `2 ≤ finrank ℝ E`) to get `q ∈ A.direction`.
  have hq_dir : q ∈ A.direction := by
    have hspan_le : Module.finrank ℝ (Submodule.span ℝ ({q} : Set E)) ≤ 1 :=
      finrank_span_le_card ({q} : Set E)
    have horth_dim : 1 ≤ Module.finrank ℝ (Submodule.span ℝ ({q} : Set E))ᗮ := by
      have hadd := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ ({q} : Set E))
      omega
    have hne_bot : (Submodule.span ℝ ({q} : Set E))ᗮ ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at horth_dim
      omega
    obtain ⟨u, hu_mem, hu_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
    have hqu : ⟪q, u⟫ = 0 :=
      (Submodule.mem_orthogonal _ u).mp hu_mem q (Submodule.subset_span (Set.mem_singleton q))
    let v : E := ‖u‖⁻¹ • u
    have hqv : ⟪q, v⟫ = 0 := by simp [v, inner_smul_right, hqu]
    have hv_norm : ‖v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hu_ne)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu_ne)]
    exact (horth v hqv hv_norm).2
  -- Now every `w : E` decomposes into `span {q}` + orthogonal part, hence lies in `A.direction`.
  have hdir_top : A.direction = ⊤ := by
    rw [eq_top_iff]
    intro w _
    let α : ℝ := ⟪w, q⟫ / r ^ 2
    let w_perp : E := w - α • q
    have hw_eq : w = α • q + w_perp := by simp [w_perp]
    have hqw : ⟪q, w_perp⟫ = 0 := by
      rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hq_norm, real_inner_comm]
      dsimp only [α]
      rw [div_mul_cancel₀ _ (by positivity)]
      exact sub_self _
    have hw_perp_dir : w_perp ∈ A.direction := by
      by_cases hw0 : w_perp = 0
      · rw [hw0]; exact A.direction.zero_mem
      · let v : E := ‖w_perp‖⁻¹ • w_perp
        have hqv : ⟪q, v⟫ = 0 := by simp [v, inner_smul_right, hqw]
        have hv_norm : ‖v‖ = 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hw0)),
            inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0)]
        have hv_dir := (horth v hqv hv_norm).1
        have := A.direction.smul_mem ‖w_perp‖ hv_dir
        rwa [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw0), one_smul] at this
    rw [hw_eq]
    exact A.direction.add_mem (A.direction.smul_mem α hq_dir) hw_perp_dir
  refine hA (eq_top_iff.mpr fun w _ => ?_)
  have hmem : (w -ᵥ q) +ᵥ q ∈ A :=
    AffineSubspace.vadd_mem_of_mem_direction (hdir_top ▸ Submodule.mem_top) hqA
  simpa using hmem

/-- In dimension `≥ 2`, every nonempty open patch `ball p ε ∩ sphere 0 r` (`r > 0`) contains a
point avoiding any finite collection of proper affine subspaces. -/
theorem exists_mem_ball_sphere_notMem_biUnion_affineSubspace
    (hd : 2 ≤ Module.finrank ℝ E) {r : ℝ} (hr : 0 < r)
    {p : E} (hp : p ∈ Metric.sphere (0 : E) r) {ε : ℝ} (hε : 0 < ε)
    (F : Finset (AffineSubspace ℝ E)) (hF : ∀ A ∈ F, A ≠ ⊤) :
    ∃ q ∈ Metric.ball p ε ∩ Metric.sphere (0 : E) r, ∀ A ∈ F, q ∉ (A : Set E) := by
  classical
  induction F using Finset.induction with
  | empty => exact ⟨p, ⟨Metric.mem_ball_self hε, hp⟩, fun _ h => (Finset.notMem_empty _ h).elim⟩
  | @insert A F hAF ih =>
    obtain ⟨q₀, ⟨hq₀_ball, hq₀_sph⟩, hq₀_avoid⟩ :=
      ih fun B hB => hF B (Finset.mem_insert_of_mem hB)
    have hU_open : IsOpen (Metric.ball p ε \ ⋃ B ∈ F, (B : Set E)) := by
      refine Metric.isOpen_ball.sdiff ?_
      exact F.finite_toSet.isClosed_biUnion fun B _ => AffineSubspace.isClosed_of_finiteDimensional B
    have hq₀_U : q₀ ∈ Metric.ball p ε \ ⋃ B ∈ F, (B : Set E) := by
      refine ⟨hq₀_ball, ?_⟩
      simp only [Set.mem_iUnion, exists_prop, not_exists, not_and]
      exact hq₀_avoid
    obtain ⟨η, hη_pos, hη_sub⟩ := Metric.isOpen_iff.mp hU_open q₀ hq₀_U
    have hnot : ¬ (Metric.ball q₀ η ∩ Metric.sphere (0 : E) r ⊆ (A : Set E)) :=
      not_ball_inter_sphere_subset_affineSubspace hd hr hq₀_sph hη_pos
        (hF A (Finset.mem_insert_self A F))
    obtain ⟨q, ⟨hq_ballη, hq_sph⟩, hq_notA⟩ := Set.not_subset.mp hnot
    have hq_U := hη_sub hq_ballη
    refine ⟨q, ⟨hq_U.1, hq_sph⟩, fun B hB => ?_⟩
    rcases Finset.mem_insert.mp hB with rfl | hBF
    · exact hq_notA
    · intro hqB
      exact hq_U.2 (Set.mem_biUnion hBF hqB)

omit [FiniteDimensional ℝ E] in
/-- Helper: appending `q` outside every linear span of `≤ d - 1` points of `w` preserves
linear independence of all subfamilies of cardinality `≤ d`. -/
private lemma linearIndepOn_snoc_of_notMem_span {m : ℕ} {w : Fin m → E}
    (hw : ∀ s : Finset (Fin m), s.card ≤ Module.finrank ℝ E → LinearIndepOn ℝ w (s : Set (Fin m)))
    {q : E}
    (hq : ∀ t : Finset (Fin m), t.card + 1 ≤ Module.finrank ℝ E →
      q ∉ Submodule.span ℝ (w '' (t : Set (Fin m)))) :
    ∀ s : Finset (Fin (m + 1)), s.card ≤ Module.finrank ℝ E →
      LinearIndepOn ℝ (Fin.snoc (α := fun _ => E) w q) (s : Set (Fin (m + 1))) := by
  classical
  set d := Module.finrank ℝ E
  let w' : Fin (m + 1) → E := Fin.snoc (α := fun _ => E) w q
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
    refine ⟨?_, ?_⟩
    · rw [← himg, Finset.card_image_of_injective _ (Fin.castSucc_injective m)]
    · rw [← Finset.coe_image, himg]
  have hind_no_last : ∀ s' : Finset (Fin (m + 1)), Fin.last m ∉ s' → s'.card ≤ d →
      LinearIndepOn ℝ w' (s' : Set (Fin (m + 1))) := by
    intro s' hlast hcard
    set t := s'.preimage Fin.castSucc (Fin.castSucc_injective m).injOn
    obtain ⟨ht_card, ht_img⟩ := hpull s' hlast
    have hwt : LinearIndepOn ℝ w (t : Set (Fin m)) := hw t (ht_card.trans_le hcard)
    have hcomp : LinearIndepOn ℝ (w' ∘ Fin.castSucc) (t : Set (Fin m)) := by
      have hfun : (w' ∘ Fin.castSucc : Fin m → E) = w := by
        ext j; exact Fin.snoc_castSucc (α := fun _ => E) q w j
      rwa [hfun]
    rw [← ht_img]
    exact hcomp.image_of_comp
  intro s hs
  by_cases hlast : Fin.last m ∈ s
  · set s' := s.erase (Fin.last m)
    have hlast' : Fin.last m ∉ s' := Finset.notMem_erase (Fin.last m) s
    have hs'_card : s'.card + 1 ≤ d := by
      have h1 : s'.card + 1 = s.card := Finset.card_erase_add_one hlast
      omega
    have hind' : LinearIndepOn ℝ w' (s' : Set (Fin (m + 1))) :=
      hind_no_last s' hlast' (by omega)
    set t := s'.preimage Fin.castSucc (Fin.castSucc_injective m).injOn
    obtain ⟨ht_card, ht_img⟩ := hpull s' hlast'
    have himg_eq : w' '' (s' : Set (Fin (m + 1))) = w '' (t : Set (Fin m)) := by
      rw [← ht_img, ← Set.image_comp]
      congr 1; ext j; exact Fin.snoc_castSucc (α := fun _ => E) q w j
    have hnot_span : w' (Fin.last m) ∉ Submodule.span ℝ (w' '' (s' : Set (Fin (m + 1)))) := by
      have hlast_eq : w' (Fin.last m) = q := Fin.snoc_last (α := fun _ => E) q w
      rw [hlast_eq, himg_eq]
      exact hq t (ht_card.symm ▸ hs'_card)
    have hins : (s : Set (Fin (m + 1))) = insert (Fin.last m) (s' : Set (Fin (m + 1))) := by
      ext i
      simp only [Finset.mem_coe, Set.mem_insert_iff, s', Finset.mem_erase]
      by_cases hi : i = Fin.last m
      · subst hi; simp [hlast]
      · simp [hi]
    rw [hins]
    exact hind'.insert hnot_span
  · exact hind_no_last s hlast hs

/-- One-point spherical general-position extension on `sphere 0 r` (`r > 0`, `2 ≤ finrank ℝ E`). -/
theorem exists_sphericalGeneralPosition_snoc
    (hd : 2 ≤ Module.finrank ℝ E) {r : ℝ} (hr : 0 < r)
    {m : ℕ} (w : Fin m → E) (hw : InSphericalGeneralPosition r w)
    {p : E} (hp : p ∈ Metric.sphere (0 : E) r) {ε : ℝ} (hε : 0 < ε) :
    ∃ q ∈ Metric.ball p ε ∩ Metric.sphere (0 : E) r,
      InSphericalGeneralPosition r (Fin.snoc (α := fun _ => E) w q) := by
  classical
  set d := Module.finrank ℝ E
  let affSets : Finset (Finset (Fin m)) := Finset.univ.powerset.filter (fun t => t.card ≤ d)
  let linSets : Finset (Finset (Fin m)) := Finset.univ.powerset.filter (fun t => t.card + 1 ≤ d)
  let F_aff : Finset (AffineSubspace ℝ E) :=
    affSets.image fun (t : Finset (Fin m)) => affineSpan ℝ (w '' (t : Set (Fin m)))
  let F_lin : Finset (AffineSubspace ℝ E) :=
    linSets.image fun (t : Finset (Fin m)) => (Submodule.span ℝ (w '' (t : Set (Fin m)))).toAffineSubspace
  let F : Finset (AffineSubspace ℝ E) := F_aff ∪ F_lin
  have hF : ∀ A ∈ F, A ≠ ⊤ := by
    intro A hA
    rcases Finset.mem_union.mp hA with hA_aff | hA_lin
    · rcases Finset.mem_image.mp hA_aff with ⟨t, ht, rfl⟩
      have ht_card : t.card ≤ d := (Finset.mem_filter.mp ht).2
      have henc : ((t : Set (Fin m)).encard) ≤ (d : ENat) := by
        rw [Set.encard_coe_eq_coe_finsetCard]; exact Nat.cast_le.mpr ht_card
      exact affineSpan_image_ne_top_of_encard_le_finrank ℝ henc w
    · rcases Finset.mem_image.mp hA_lin with ⟨t, ht, rfl⟩
      have ht_card : t.card + 1 ≤ d := (Finset.mem_filter.mp ht).2
      intro htop
      have hspan_top : Submodule.span ℝ (w '' (t : Set (Fin m))) = ⊤ := by
        have hdir := congrArg AffineSubspace.direction htop
        simpa using hdir
      have hfin_le : Module.finrank ℝ (Submodule.span ℝ (w '' (t : Set (Fin m)))) ≤ t.card := by
        rw [← Finset.coe_image]
        exact (finrank_span_finset_le_card (R := ℝ) (t.image w)).trans Finset.card_image_le
      rw [hspan_top, finrank_top] at hfin_le
      omega
  obtain ⟨q, ⟨hq_ball, hq_sph⟩, hq_avoid⟩ :=
    exists_mem_ball_sphere_notMem_biUnion_affineSubspace hd hr hp hε F hF
  refine ⟨q, ⟨hq_ball, hq_sph⟩, ?_, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [Fin.snoc_last] using hq_sph
    · simpa [Fin.snoc_castSucc] using hw.1 j
  · refine inGeneralPosition_snoc_of_notMem_affineSpan hw.2.1 fun t ht => ?_
    exact hq_avoid _ (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ht⟩)))
  · refine linearIndepOn_snoc_of_notMem_span hw.2.2 fun t ht => ?_
    exact hq_avoid _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ht⟩)))

/-- **Density of Spherical General Position on `S(0, r)` (`Fin m`):**
In dimension `≥ 2` and for `r > 0`, any finite configuration on `sphere 0 r` can be perturbed
within `< ε` on `sphere 0 r` into `InSphericalGeneralPosition r w` (both affinely in general
position and with every `≤ d` points linearly independent). -/
theorem exists_sphericalGeneralPosition_dist_lt
    (hd : 2 ≤ Module.finrank ℝ E) {r : ℝ} (hr : 0 < r)
    {m : ℕ} (v : Fin m → E) (hv : ∀ i, v i ∈ Metric.sphere (0 : E) r) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : Fin m → E, InSphericalGeneralPosition r w ∧ ∀ i, dist (w i) (v i) < ε := by
  induction m with
  | zero =>
    refine ⟨Fin.elim0, ⟨fun i => Fin.elim0 i, ?_, ?_⟩, fun i => Fin.elim0 i⟩
    · intro s _; exact affineIndependent_of_subsingleton ℝ _
    · intro s _
      have hs : (s : Set (Fin 0)) = ∅ := Set.eq_empty_of_isEmpty _
      rw [hs]; exact linearIndepOn_empty ℝ _
  | succ m ih =>
    obtain ⟨w, hw_gp, hw_dist⟩ := ih (Fin.init v) (fun j => hv (Fin.castSucc j))
    obtain ⟨q, ⟨hq_ball, _⟩, hq_gp⟩ :=
      exists_sphericalGeneralPosition_snoc hd hr w hw_gp (hv (Fin.last m)) hε
    refine ⟨Fin.snoc (α := fun _ => E) w q, hq_gp, fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [Fin.snoc_last] using Metric.mem_ball.mp hq_ball
    · simpa [Fin.snoc_castSucc, Fin.init] using hw_dist j

/-- **Density of Spherical General Position on `S(0, r)` (arbitrary `Fintype`):**
generalizes `exists_sphericalGeneralPosition_dist_lt` to any finite index type `ι`. -/
theorem exists_sphericalGeneralPosition_dist_lt_of_fintype
    (hd : 2 ≤ Module.finrank ℝ E) {r : ℝ} (hr : 0 < r)
    {ι : Type*} [Finite ι] (v : ι → E) (hv : ∀ i, v i ∈ Metric.sphere (0 : E) r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w : ι → E, InSphericalGeneralPosition r w ∧ ∀ i, dist (w i) (v i) < ε := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  obtain ⟨w₀, hw₀_gp, hw₀_dist⟩ :=
    exists_sphericalGeneralPosition_dist_lt hd hr (v ∘ e.symm) (fun j => hv (e.symm j)) hε
  refine ⟨w₀ ∘ e, ⟨fun i => hw₀_gp.1 (e i), hw₀_gp.2.1.comp_injective e.injective, ?_⟩, fun i => ?_⟩
  · intro s hs
    have himg_card : (s.image e).card ≤ Module.finrank ℝ E :=
      (Finset.card_image_le).trans hs
    have hli : LinearIndepOn ℝ w₀ ((s.image e : Finset (Fin (Fintype.card ι))) : Set _) :=
      hw₀_gp.2.2 (s.image e) himg_card
    rw [Finset.coe_image] at hli
    exact hli.comp_of_image e.injective.injOn
  · simpa using hw₀_dist (e i)

end SphericalGeneralPosition

end

end ConvexGeom
