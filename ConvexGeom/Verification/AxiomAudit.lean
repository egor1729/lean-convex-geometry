module

import ConvexGeom

/-!
# Axiom Audit

Verifies that every headline theorem in `ConvexGeom` depends solely on Lean's three standard
classical axioms (`propext`, `Classical.choice`, `Quot.sound`) — with zero `sorryAx`,
zero custom axioms, and zero `Lean.ofReduceBool`.
-/

-- 1. Support Functions, Hörmander Isometry, and Minkowski Representation
#print axioms ConvexGeom.supportFn_minkowski_add
#print axioms ConvexGeom.supportFn_le_iff_subset
#print axioms ConvexGeom.supportFn_injective
#print axioms ConvexGeom.diam_eq_sSup_width
#print axioms ConvexGeom.isometry_supportFnOnBall
#print axioms ConvexGeom.dist_add_right
#print axioms ConvexGeom.dist_add_le
#print axioms ConvexGeom.dist_smul
#print axioms ConvexGeom.exists_convexBody_supportFn_eq

-- 2. Blaschke Selection Theorem & Completeness
#print axioms ConvexGeom.isClosed_range_supportFnOnBall
#print axioms ConvexGeom.instCompleteSpaceConvexBody
#print axioms ConvexGeom.isCompact_subset_closedBall
#print axioms ConvexGeom.isCompact_subset_of_isCompact
#print axioms ConvexGeom.blaschke_selection

-- 3. Polarity, Bipolar Theorem, and Gauge–Support Duality
#print axioms ConvexGeom.polarBody_closedBall
#print axioms ConvexGeom.polarBody_image_continuousLinearMap
#print axioms ConvexGeom.polarBody_polarBody
#print axioms ConvexGeom.gauge_polarBody_eq_supportFn
#print axioms ConvexGeom.supportFn_bodyPolar_eq_gauge

-- 4. Polytopes & Inscribed Polytope Approximation
#print axioms ConvexGeom.supportFn_bodyConvexHull
#print axioms ConvexGeom.hausdorffDist_convexHull_range_le
#print axioms ConvexGeom.exists_polytope_dist_lt

-- 5. Simplex Volume
#print axioms ConvexGeom.volume_orderSimplex
#print axioms ConvexGeom.volume_solidSimplex
#print axioms ConvexGeom.volume_convexHull_simplex
#print axioms ConvexGeom.volume_convexHull_simplex_euclideanSpace

-- 6. Half-Ball Bounds & Continuity of Volume
#print axioms ConvexGeom.addHaar_halfBall
#print axioms ConvexGeom.addHaar_le_half_ball
#print axioms ConvexGeom.upperSemicontinuous_addHaar_convexBody
#print axioms ConvexGeom.lowerSemicontinuous_addHaar_convexBody
#print axioms ConvexGeom.continuous_addHaar_convexBody
#print axioms ConvexGeom.continuous_addHaarReal_convexBody
#print axioms ConvexGeom.continuous_addHaar_convexHull_range

-- 7. Volumetric Covering & Packing Bounds
#print axioms ConvexGeom.measure_le_externalCoveringNumber_mul_closedBall
#print axioms ConvexGeom.measure_le_coveringNumber_mul_closedBall
#print axioms ConvexGeom.packingNumber_mul_ball_le_measure_add_ball
#print axioms ConvexGeom.coveringNumber_mul_ball_le_measure_add_ball
#print axioms ConvexGeom.inv_pow_le_externalCoveringNumber_closedBall
#print axioms ConvexGeom.packingNumber_closedBall_le
#print axioms ConvexGeom.coveringNumber_closedBall_le
#print axioms ConvexGeom.coveringNumber_closedBall_le_three_div

-- 8. Prékopa–Leindler, Brunn–Minkowski, Isodiametric Inequality, and Log-Concave Marginals
#print axioms ConvexGeom.brunn_minkowski_one_dim
#print axioms ConvexGeom.prekopa_leindler_one_dim
#print axioms ConvexGeom.prekopa_leindler_pi
#print axioms ConvexGeom.prekopa_leindler
#print axioms ConvexGeom.brunn_minkowski_mul
#print axioms ConvexGeom.brunn_minkowski_mul_compact
#print axioms ConvexGeom.brunn_minkowski_compact
#print axioms ConvexGeom.brunn_minkowski_convexBody
#print axioms ConvexGeom.isodiametric_inequality
#print axioms ConvexGeom.logConcave_marginal_prod

-- 9. Minkowski, Central, and Steiner Symmetrization
#print axioms ConvexGeom.supportFn_minkowskiSymm
#print axioms ConvexGeom.reflectBody_minkowskiSymm
#print axioms ConvexGeom.volume_le_volume_minkowskiSymm
#print axioms ConvexGeom.diam_minkowskiSymm_le
#print axioms ConvexGeom.supportFn_centralSymm
#print axioms ConvexGeom.volume_le_volume_centralSymm
#print axioms ConvexGeom.convex_steinerSymm
#print axioms ConvexGeom.isCompact_steinerSymm
#print axioms ConvexGeom.volume_steinerSymm
#print axioms ConvexGeom.steinerSymm_dist_le_diam
