module

import ConvexGeom

/-!
# Downstream Import Smoke Test

Imports *only* the public `ConvexGeom` umbrella module (no direct Mathlib imports) and exercises
representative definitions and theorems from all four layers (`Metric`, `Polytope`, `Volume`,
`Asymptotic`) to ensure downstream consumers have a clean, self-contained import surface.
-/

namespace ConvexGeomTest

open ConvexGeom

example (r : ℝ) (hr : 0 ≤ r) :
    supportFn (bodyClosedBall (0 : ℝ) hr) 1 = r := by
  simp [supportFn_bodyClosedBall]

example (K : ConvexBody ℝ) :
    meanWidth (centralSymm K) = meanWidth K :=
  meanWidth_centralSymm K

example (K : ConvexBody ℝ) (h0 : (0 : ℝ) ∈ interior (K : Set ℝ)) :
    (MeasureTheory.volume.real (Metric.closedBall (0 : ℝ) 1) /
        MeasureTheory.volume.real (polarBody (K : Set ℝ))) ^
      (1 / (Module.finrank ℝ ℝ : ℝ)) ≤ meanWidth K :=
  dual_urysohn_inequality K h0

example : banachMazurEDist (Metric.closedBall (0 : ℝ) 1) (Metric.closedBall (0 : ℝ) 1) = 1 :=
  banachMazurEDist_self _

example : affineBanachMazurDist (Metric.closedBall (0 : ℝ) 1) (Metric.closedBall (0 : ℝ) 1) = 1 :=
  affineBanachMazurDist_self _

example (K : ConvexBody ℝ) (hKint : (interior (K : Set ℝ)).Nonempty) :
    ∃ (m : ℕ) (w : Fin m → ℝ) (S : Finset ℝ) (hS : S.Nonempty),
      InGeneralPosition w ∧ (S : Set ℝ) = Set.range w ∧
      (bodyConvexHull S hS : Set ℝ) ⊆ K ∧
      (interior (bodyConvexHull S hS : Set ℝ)).Nonempty ∧
      dist (bodyConvexHull S hS) K < 1 :=
  exists_inscribed_generalPosition_polytope_dist_lt K hKint zero_lt_one

end ConvexGeomTest
