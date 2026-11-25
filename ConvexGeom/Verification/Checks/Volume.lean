module

import ConvexGeom.Volume

/-! Checks for `ConvexGeom.Volume`. -/

namespace ConvexGeomChecks

open ConvexGeom MeasureTheory Metric Set
open scoped ENNReal Pointwise

/-- Contract regression test for `steinerSymm` on a disconnected set:
`{-1, 1} × {0}` maps to the filled interval `[-1, 1] × {0}` (interval-hull symmetrization). -/
example :
    steinerSymm ({(-1 : ℝ), 1} ×ˢ {(0 : ℝ)}) = Icc (-1 : ℝ) 1 ×ˢ {(0 : ℝ)} := by
  let K : Set (ℝ × ℝ) := {(-1 : ℝ), 1} ×ˢ {(0 : ℝ)}
  have hfib0 : steinerFiber K 0 = {(-1 : ℝ), 1} := by
    ext t; simp [steinerFiber, K]
  have hup0 : steinerUpper K 0 = 1 := by
    rw [steinerUpper, hfib0]
    exact le_antisymm (csSup_le (by simp) fun t ht => by rcases ht with rfl | rfl <;> norm_num)
      (le_csSup ⟨1, fun t ht => by rcases ht with rfl | rfl <;> norm_num⟩ (by simp))
  have hlo0 : steinerLower K 0 = -1 := by
    rw [steinerLower, hfib0]
    exact le_antisymm (csInf_le ⟨-1, fun t ht => by rcases ht with rfl | rfl <;> norm_num⟩ (by simp))
      (le_csInf (by simp) fun t ht => by rcases ht with rfl | rfl <;> norm_num)
  ext ⟨t, y⟩
  simp only [steinerSymm, mem_ofPred_eq, mem_prod, mem_Icc, mem_singleton_iff]
  constructor
  · rintro ⟨⟨s, hs⟩, ht⟩
    have hy : y = 0 := hs.2
    subst hy
    rw [hup0, hlo0] at ht
    exact ⟨abs_le.mp (by linarith), rfl⟩
  · rintro ⟨⟨h1, h2⟩, rfl⟩
    refine ⟨⟨1, by simp [steinerFiber]⟩, ?_⟩
    rw [hup0, hlo0]
    have habs : |t| ≤ 1 := abs_le.mpr ⟨h1, h2⟩
    linarith

/-- Contract regression test: Mathlib equips `ℝ × ℝ` with the product max-norm (`‖(1, 1)‖ = 1`),
whereas `steinerSymm_dist_le_diam` uses explicit Euclidean squared distance `(t₁ - t₂)² + ‖y₁ - y₂‖²`. -/
example : ‖((1 : ℝ), (1 : ℝ))‖ = 1 := by
  simp [Prod.norm_def]

/-- 1D Brunn–Minkowski equality on `[0, 2]` and `[0, 3]`. -/
example :
    volume (Icc (0 : ℝ) 2) + volume (Icc (0 : ℝ) 3) = volume (Icc (0 : ℝ) 2 + Icc (0 : ℝ) 3) := by
  have hsum : Icc (0 : ℝ) 2 + Icc (0 : ℝ) 3 = Icc (0 : ℝ) 5 := by
    ext z
    simp only [Set.mem_add, mem_Icc]
    constructor
    · rintro ⟨x, ⟨hx0, hx2⟩, y, ⟨hy0, hy3⟩, rfl⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨hz0, hz5⟩
      refine ⟨min z 2, ⟨le_min hz0 (by norm_num), min_le_right _ _⟩,
        z - min z 2, ⟨sub_nonneg.mpr (min_le_left _ _), ?_⟩, add_sub_cancel _ _⟩
      rcases le_total z 2 with h | h
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right h]; linarith
  rw [hsum, Real.volume_Icc, Real.volume_Icc, Real.volume_Icc,
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- General-dimension half-ball origin criterion in `ℝ`:
`[0, 1] ⊆ [-1, 1]` does not contain `0` in its interior, so `volume [0, 1] ≤ volume [-1, 1] / 2`. -/
example :
    volume (Icc (0 : ℝ) 1) ≤ volume (closedBall (0 : ℝ) 1) / 2 :=
  addHaar_le_half_closedBall_of_zero_not_mem_interior volume (convex_Icc 0 1)
    (fun x hx => by rw [mem_closedBall_zero_iff, Real.norm_eq_abs, abs_le]; constructor <;> linarith [hx.1, hx.2])
    (by rw [interior_Icc]; simp)

/-- In dimension 1, the outer Minkowski surface area of `closedBall c r` (`r > 0`) is `2`
(corresponding to the two boundary endpoints of the interval `[c - r, c + r]`). -/
example (c : ℝ) {r : ℝ} (hr : 0 < r) :
    minkowskiSurfaceArea (closedBall c r) = 2 := by
  rw [minkowskiSurfaceArea_closedBall c hr, Module.finrank_self]
  simp [Real.volume_closedBall]

/-- Covariogram at `0` equals volume and is even. -/
example (K : Set ℝ) (x : ℝ) :
    covariogram volume K 0 = volume K ∧ covariogram volume K (-x) = covariogram volume K x :=
  ⟨covariogram_zero volume K, covariogram_neg volume K x⟩

end ConvexGeomChecks
