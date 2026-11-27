/-
Copyright (c) 2026 Yegor Gorodzha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yegor Gorodzha
-/
module

import ConvexGeom

/-! Import check for the public `ConvexGeom` API without direct Mathlib imports. -/

namespace ConvexGeomChecks

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

example (K : ConvexBody ℝ) : steinerPoint K ∈ (K : Set ℝ) :=
  steinerPoint_mem K

example (u : ℝ) (hu : ‖u‖ = 1) :
    sphericalCap u 1 = Metric.closedBall u 0 ∩ Metric.sphere (0 : ℝ) 1 := by
  simpa using sphericalCap_eq_closedBall_inter_sphere hu le_rfl

example (A : Set ℝ) : translativeCoveringNumber A A ≤ 1 :=
  translativeCoveringNumber_self_le_one A

example (K : ConvexBody ℝ) :
    symmDiffVol MeasureTheory.volume (K : Set ℝ) (K : Set ℝ) = 0 :=
  symmDiffVol_self _ _

example (K : ConvexBody ℝ) :
    convexHull ℝ ((K : Set ℝ).extremePoints ℝ) = (K : Set ℝ) :=
  convexHull_extremePoints_eq K.isCompact K.convex

example (K : ConvexBody ℝ) (hsym : IsOriginSymmetric (K : Set ℝ))
    (h0 : (0 : ℝ) ∈ interior (K : Set ℝ)) :
    banachMazurDist (K : Set ℝ) (Metric.closedBall (0 : ℝ) 1) ≤
      Real.sqrt (Module.finrank ℝ ℝ : ℝ) :=
  banachMazurDist_closedBall_le_sqrt_finrank K hsym h0

example (K : ConvexBody ℝ) (hsym : IsOriginSymmetric (K : Set ℝ))
    (h0 : (0 : ℝ) ∈ interior (K : Set ℝ)) :
    ∃ T : ℝ ≃ₗ[ℝ] ℝ,
      Metric.closedBall (0 : ℝ) 1 ⊆ T '' (K : Set ℝ) ∧
      MeasureTheory.volume (T '' (K : Set ℝ)) ≤ (2 : ENNReal) ^ Module.finrank ℝ ℝ :=
  ball_volume_ratio_symmetric K hsym h0

example (K : ConvexBody ℝ) :
    gaussianWidth K = (∫ x : ℝ, ‖x‖ ∂stdGaussian ℝ) * meanWidth K :=
  gaussianWidth_eq_integral_norm_mul_meanWidth K

example (K : ConvexBody ℝ) (hne : (interior (K : Set ℝ)).Nonempty) :
    santaloMahlerVolume MeasureTheory.volume (K : Set ℝ) ≤
      MeasureTheory.volume (Metric.closedBall (0 : ℝ) 1) ^ 2 :=
  blaschke_santalo K hne

example (K : ConvexBody ℝ) :
    (MeasureTheory.volume.real (K : Set ℝ) /
        MeasureTheory.volume.real (Metric.closedBall (0 : ℝ) 1)) ^
      (1 / (Module.finrank ℝ ℝ : ℝ)) ≤ meanWidth K :=
  urysohn_inequality K

end ConvexGeomChecks
