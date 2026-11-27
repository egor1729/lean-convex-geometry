/-
Copyright (c) 2026 Yegor Gorodzha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yegor Gorodzha
-/
module

import ConvexGeom.Polytope

/-! Checks for `ConvexGeom.Polytope`. -/

namespace ConvexGeomChecks

open ConvexGeom MeasureTheory Set
open scoped ENNReal

/-- Dimension 1 simplex `[0, 3]` in `ℝ` has Lebesgue volume `3`. -/
example :
    volume (convexHull ℝ (Set.range ![(0 : ℝ), 3])) = ENNReal.ofReal 3 := by
  have hrange : Set.range ![(0 : ℝ), 3] = {(0 : ℝ), 3} := by
    ext x
    simp only [mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      mem_insert_iff, mem_singleton_iff]
    tauto
  rw [hrange, convexHull_pair, segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 3), Real.volume_Icc]
  norm_num

/-- Dimension 2 standard triangle `(0, 0), (1, 0), (0, 1)` in `EuclideanSpace ℝ (Fin 2)`
has volume `1 / 2` , computed via the public `volume_convexHull_simplex_euclideanSpace_matrix` API.
-/
example :
    let v : Fin 3 → EuclideanSpace ℝ (Fin 2) :=
      ![WithLp.toLp 2 ![0, 0], WithLp.toLp 2 ![1, 0], WithLp.toLp 2 ![0, 1]]
    volume (convexHull ℝ (Set.range v)) = ENNReal.ofReal (1 / 2 : ℝ) := by
  intro v
  rw [volume_convexHull_simplex_euclideanSpace_matrix v]
  have hdet : (simplexEdgeMatrix (fun i => (v i).ofLp)).det = 1 := by
    rw [Matrix.det_fin_two]
    simp [simplexEdgeMatrix_apply, v]
  rw [hdet, abs_one, Nat.factorial_two]
  norm_num

/-- Degenerate simplex with a repeated vertex has volume `0`. -/
example :
    let v : Fin 3 → EuclideanSpace ℝ (Fin 2) :=
      ![WithLp.toLp 2 ![0, 0], WithLp.toLp 2 ![1, 0], WithLp.toLp 2 ![0, 0]]
    volume (convexHull ℝ (Set.range v)) = 0 := by
  intro v
  rw [volume_convexHull_simplex_euclideanSpace_matrix v]
  have hdet : (simplexEdgeMatrix (fun i => (v i).ofLp)).det = 0 := by
    rw [Matrix.det_fin_two]
    simp [simplexEdgeMatrix_apply, v]
  rw [hdet, abs_zero, zero_div, ENNReal.ofReal_zero]

/-- General position in dimension 0: a singleton family in `EuclideanSpace ℝ (Fin 0)` is
vacuously in general position. -/
example : InGeneralPosition (fun _ : Fin 1 => (0 : EuclideanSpace ℝ (Fin 0))) := by
  intro s hs
  have hcard : s.card ≤ 1 := by
    simpa [finrank_euclideanSpace_fin] using hs
  have : Subsingleton (s : Set (Fin 1)) :=
    ⟨fun a b => Subtype.ext (Finset.card_le_one.mp hcard a.1 a.2 b.1 b.2)⟩
  exact affineIndependent_of_subsingleton ℝ _

/-- General position in dimension 1: two distinct points `0, 1 ∈ ℝ` are in general position. -/
example : InGeneralPosition ![(0 : ℝ), 1] := by
  intro s hs
  by_cases h2 : s.card ≤ 1
  · have : Subsingleton (s : Set (Fin 2)) :=
      ⟨fun a b => Subtype.ext (Finset.card_le_one.mp h2 a.1 a.2 b.1 b.2)⟩
    exact affineIndependent_of_subsingleton ℝ _
  · have hfull : s = Finset.univ := by
      have hle : s.card ≤ Fintype.card (Fin 2) := Finset.card_le_univ s
      have hfin : Fintype.card (Fin 2) = 2 := Fintype.card_fin 2
      have heq : s.card = 2 := by omega
      exact Finset.eq_univ_of_card s (by simpa [hfin] using heq)
    subst hfull
    unfold AffineIndepOn
    let i0 : ((Finset.univ : Finset (Fin 2)) : Set (Fin 2)) := ⟨(0 : Fin 2), Finset.mem_univ _⟩
    rw [affineIndependent_iff_linearIndependent_vsub ℝ _ i0]
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hi1 : i.1 = ⟨(1 : Fin 2), Finset.mem_univ _⟩ := by
      rcases i with ⟨⟨j, hj⟩, hne⟩
      fin_cases j
      · exact absurd (Subtype.ext rfl) hne
      · rfl
    have hsum : ∑ x : {x : ((Finset.univ : Finset (Fin 2)) : Set (Fin 2)) // x ≠ i0},
        g x • ((![(0 : ℝ), 1] x.1.1) -ᵥ (![(0 : ℝ), 1] i0.1)) = g i := by
      rw [Finset.sum_eq_single i]
      · simp [hi1, i0]
      · intro b _ hbi
        exfalso
        apply hbi
        ext
        rcases b with ⟨⟨j, _⟩, hne⟩
        fin_cases j
        · exact absurd (Subtype.ext rfl) hne
        · simp [hi1]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rwa [hsum] at hg

/-- Three collinear points `(0, 0), (1, 0), (2, 0)` in `ℝ²` are NOT in general position. -/
example :
    ¬ InGeneralPosition
      (![WithLp.toLp 2 ![(0 : ℝ), 0], WithLp.toLp 2 ![1, 0], WithLp.toLp 2 ![2, 0]] :
        Fin 3 → EuclideanSpace ℝ (Fin 2)) := by
  intro hgp
  have hind_on := hgp Finset.univ (by simp)
  let emb : Fin 3 ↪ ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)) :=
    ⟨fun i => ⟨i, Finset.mem_univ i⟩, fun _ _ h => congrArg Subtype.val h⟩
  have hind : AffineIndependent ℝ
      (![WithLp.toLp 2 ![(0 : ℝ), 0], WithLp.toLp 2 ![1, 0], WithLp.toLp 2 ![2, 0]] :
        Fin 3 → EuclideanSpace ℝ (Fin 2)) := hind_on.comp_embedding emb
  rw [affineIndependent_iff] at hind
  let w : Fin 3 → ℝ := ![1, -2, 1]
  have hw_sum : Finset.univ.sum w = 0 := by
    simp [w, Fin.sum_univ_three]
    norm_num
  have hw_vsum :
      ∑ e : Fin 3, w e •
        (![WithLp.toLp 2 ![(0 : ℝ), 0], WithLp.toLp 2 ![1, 0], WithLp.toLp 2 ![2, 0]] :
          Fin 3 → EuclideanSpace ℝ (Fin 2)) e = 0 := by
    ext k
    fin_cases k <;> simp [w, Fin.sum_univ_three]
  have hzero := hind Finset.univ w hw_sum hw_vsum 0 (Finset.mem_univ 0)
  simp [w] at hzero

end ConvexGeomChecks
