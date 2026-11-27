/-
Copyright (c) 2026 Yegor Gorodzha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yegor Gorodzha
-/
module

import ConvexGeom.Metric

/-! Checks for `ConvexGeom.Metric`. -/

namespace ConvexGeomChecks

open ConvexGeom Metric Set
open scoped RealInnerProductSpace

/-- Off-set convention test: `normalCone S y` contains `0` even when `y ∉ S`,
whereas `strictNormalCone S y = ∅` whenever `y ∉ S`. -/
example : (0 : ℝ) ∈ normalCone (closedBall (0 : ℝ) 1) 2 := by
  intro x _
  simp

example : strictNormalCone (closedBall (0 : ℝ) 1) 2 = ∅ :=
  strictNormalCone_of_notMem (by norm_num [mem_closedBall])

/-- Halfspace characterization on `bodyClosedBall 0 1`: `x ∈ [-1, 1]` iff `∀ u, x * u ≤ |u|`. -/
example (x : ℝ) :
    x ∈ (bodyClosedBall (0 : ℝ) zero_le_one : Set ℝ) ↔ ∀ u : ℝ, ⟪x, u⟫ ≤ |u| := by
  rw [SetLike.mem_coe, mem_iff_forall_inner_le_supportFn]
  simp [supportFn_bodyClosedBall, Real.norm_eq_abs]

/-- `bodyOfSupportFn` round-trip for `h(u) = |u|` recovers the unit ball's support function. -/
example (u : ℝ) :
    supportFn (bodyOfSupportFn (fun v : ℝ => ‖v‖)
      (fun c hc x => by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc])
      (fun x y => norm_add_le x y)) u = ‖u‖ :=
  congrFun (supportFn_bodyOfSupportFn _ _ _) u

/-- `mapLinear` composition identity on `ConvexBody ℝ`. -/
example (K : ConvexBody ℝ) :
    mapLinear (ContinuousLinearMap.id ℝ ℝ) K = K :=
  mapLinear_id K

/-- Polar of a closed ball of radius `r = 2` in `ℝ` is the closed ball of radius `1 / 2`. -/
example : polarBody (closedBall (0 : ℝ) 2) = closedBall (0 : ℝ) (2 : ℝ)⁻¹ :=
  polarBody_closedBall (by norm_num)

/-- Bipolar theorem on a non-symmetric closed convex interval `[-1, 2]` containing `0`. -/
example : polarBody (polarBody (Icc (-1 : ℝ) 2)) = Icc (-1 : ℝ) 2 :=
  polarBody_polarBody (convex_Icc (-1) 2) isClosed_Icc (by norm_num)

end ConvexGeomChecks
