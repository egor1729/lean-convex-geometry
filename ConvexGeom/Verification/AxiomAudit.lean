module

import ConvexGeom

/-!
# Axiom Audit

Prints the axioms of headline theorems in `ConvexGeom`. For the full module- and declaration-level
audit, run `lake exe convexgeom-audit`.
-/

-- 1. Support Functions, Linear Transport, Hörmander Isometry, and Minkowski Representation
#print axioms ConvexGeom.supportFn_minkowski_add
#print axioms ConvexGeom.supportFn_le_iff_subset
#print axioms ConvexGeom.supportFn_injective
#print axioms ConvexGeom.mem_iff_forall_inner_le_supportFn
#print axioms ConvexGeom.mem_iff_forall_norm_le_one_inner_le_supportFn
#print axioms ConvexGeom.supportFn_mapLinearIsometry
#print axioms ConvexGeom.dist_mapLinear_le
#print axioms ConvexGeom.diam_eq_sSup_width
#print axioms ConvexGeom.diam_eq_sSup_width_sphere
#print axioms ConvexGeom.dist_le_iff_supportFn_sub_le_sphere
#print axioms ConvexGeom.isometry_supportFnOnBall
#print axioms ConvexGeom.dist_add_right
#print axioms ConvexGeom.dist_add_le
#print axioms ConvexGeom.dist_smul
#print axioms ConvexGeom.supportFn_bodyOfSupportFn
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
#print axioms ConvexGeom.volume_convexHull_simplex_matrix
#print axioms ConvexGeom.volume_convexHull_simplex_euclideanSpace
#print axioms ConvexGeom.volume_convexHull_simplex_euclideanSpace_matrix

-- 6. Volume-Root Scaling, Half-Ball Bounds, Continuity, and Compact Maximizers
#print axioms ConvexGeom.addHaar_smul_rpow_inv_finrank
#print axioms ConvexGeom.addHaar_real_smul_rpow_inv_finrank
#print axioms ConvexGeom.addHaar_halfBall
#print axioms ConvexGeom.addHaar_le_half_ball
#print axioms ConvexGeom.addHaar_le_half_closedBall_of_zero_not_mem_interior
#print axioms ConvexGeom.upperSemicontinuous_addHaar_convexBody
#print axioms ConvexGeom.lowerSemicontinuous_addHaar_convexBody
#print axioms ConvexGeom.continuous_addHaar_convexBody
#print axioms ConvexGeom.continuous_addHaarReal_convexBody
#print axioms ConvexGeom.continuous_addHaar_convexHull_range
#print axioms ConvexGeom.continuous_addHaarReal_convexHull_range
#print axioms ConvexGeom.exists_max_addHaar_convexHull_of_isCompact
#print axioms ConvexGeom.exists_max_addHaar_convexHull_sphere
#print axioms ConvexGeom.exists_max_addHaar_convexHull_closedBall

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
#print axioms ConvexGeom.volume_bodySteinerSymm
#print axioms ConvexGeom.steinerSymm_dist_le_diam

-- 10. Metric Projection, Outer Normal Cones, and Supporting Hyperplanes
#print axioms ConvexGeom.metricProj_eq_iff
#print axioms ConvexGeom.sq_norm_metricProj_sub_le
#print axioms ConvexGeom.lipschitzWith_metricProj
#print axioms ConvexGeom.metricProj_mem_frontier_of_not_mem
#print axioms ConvexGeom.mem_normalCone_iff_supportFn
#print axioms ConvexGeom.strictNormalCone_of_notMem
#print axioms ConvexGeom.exists_supporting_normal_of_mem_frontier
#print axioms ConvexGeom.exists_unit_supportFn_eq_of_mem_frontier

-- 11. Brunn Concavity, Log-Concave Convolutions, Covariogram, and Rogers–Shephard
#print axioms ConvexGeom.logConcave_sections
#print axioms ConvexGeom.brunn_concavity_sections
#print axioms ConvexGeom.concaveOn_volume_slice_rpow
#print axioms ConvexGeom.logConcave_convolution
#print axioms ConvexGeom.covariogram_neg
#print axioms ConvexGeom.covariogram_lintegral
#print axioms ConvexGeom.covariogram_rpow_concave
#print axioms ConvexGeom.two_pow_mul_volume_le_volume_diff
#print axioms ConvexGeom.rogers_shephard

-- 12. Minkowski's First Inequality and Euclidean Isoperimetric Inequality
#print axioms ConvexGeom.volume_add_smul_ge
#print axioms ConvexGeom.minkowski_first_diff_ge
#print axioms ConvexGeom.minkowski_first_inequality
#print axioms ConvexGeom.minkowskiSurfaceArea_closedBall
#print axioms ConvexGeom.isoperimetric_inequality
#print axioms ConvexGeom.isoperimetric_inequality_ball

-- 13. Spherical Integration, Polar Volume Formula, Mean Width, and Dual Urysohn
#print axioms ConvexGeom.sphereProb_smul
#print axioms ConvexGeom.sphereProb_eq_of_isAddHaarMeasure
#print axioms ConvexGeom.measurePreserving_sphereMap_sphereProb
#print axioms ConvexGeom.measurePreserving_sphereNeg_sphereProb
#print axioms ConvexGeom.addHaar_eq_lintegral_gauge_inv_pow
#print axioms ConvexGeom.addHaar_real_eq_integral_gauge_inv_pow
#print axioms ConvexGeom.addHaar_real_polarBody_eq_integral_supportFn_inv_pow
#print axioms ConvexGeom.meanWidth_add
#print axioms ConvexGeom.meanWidth_smul
#print axioms ConvexGeom.integral_width_eq_two_mul_meanWidth
#print axioms ConvexGeom.meanWidth_translate
#print axioms ConvexGeom.meanWidth_bodyClosedBall
#print axioms ConvexGeom.lipschitzWith_meanWidth
#print axioms ConvexGeom.meanWidth_linearIsometry
#print axioms ConvexGeom.meanWidth_mapLinearIsometry
#print axioms ConvexGeom.meanWidth_minkowskiSymm
#print axioms ConvexGeom.meanWidth_centralSymm
#print axioms ConvexGeom.dual_urysohn_inequality
#print axioms ConvexGeom.urysohn_of_santalo
#print axioms ConvexGeom.urysohn_of_santalo_at

-- 14. Origin-Symmetric Bodies, Ellipsoids, Mahler Volume, and Banach–Mazur Distance
#print axioms ConvexGeom.isOriginSymmetric_convexBody_iff_supportFn
#print axioms ConvexGeom.gauge_smul_abs_of_isOriginSymmetric
#print axioms ConvexGeom.mem_polarBody_iff_abs_inner_le_one
#print axioms ConvexGeom.det_adjoint_eq_det
#print axioms ConvexGeom.polarBody_linearEquiv_image
#print axioms ConvexGeom.polarBody_ellipsoid
#print axioms ConvexGeom.addHaar_ellipsoid
#print axioms ConvexGeom.mahlerVolume_linearEquiv
#print axioms ConvexGeom.mahlerVolume_smul
#print axioms ConvexGeom.mahlerVolume_ellipsoid
#print axioms ConvexGeom.mahlerVolumeAt_affineEquiv
#print axioms ConvexGeom.santaloMahlerVolume_translate
#print axioms ConvexGeom.santaloMahlerVolume_affineEquiv
#print axioms ConvexGeom.one_le_banachMazurDist
#print axioms ConvexGeom.banachMazurDist_self
#print axioms ConvexGeom.banachMazurDist_symm
#print axioms ConvexGeom.banachMazurDist_mul_triangle
#print axioms ConvexGeom.banachMazurDist_linearEquiv_left
#print axioms ConvexGeom.banachMazurDist_linearEquiv_right
#print axioms ConvexGeom.banachMazurDist_polar
#print axioms ConvexGeom.mahlerVolume_le_banachMazurDist_pow_mul
#print axioms ConvexGeom.mahlerVolume_le_banachMazurDist_ball_pow_mul
#print axioms ConvexGeom.banachMazurEDist_eq_top_of_empty
#print axioms ConvexGeom.banachMazurEDist_mul_triangle
#print axioms ConvexGeom.affineBanachMazurDist_self
#print axioms ConvexGeom.affineBanachMazurDist_symm
#print axioms ConvexGeom.affineBanachMazurDist_affineEquiv_left
#print axioms ConvexGeom.affineBanachMazurDist_affineEquiv_right
#print axioms ConvexGeom.affineBanachMazurDist_mul_triangle
#print axioms ConvexGeom.affineBanachMazurEDist_mul_triangle

-- 15. Affine General Position and Inscribed Polytope Approximation
#print axioms ConvexGeom.InGeneralPosition.injective
#print axioms ConvexGeom.InGeneralPosition.affineEquiv
#print axioms ConvexGeom.addHaar_affineSpan_image_eq_zero
#print axioms ConvexGeom.addHaar_affineSpan_finset_eq_zero
#print axioms ConvexGeom.exists_generalPosition_snoc
#print axioms ConvexGeom.exists_generalPosition_dist_lt
#print axioms ConvexGeom.exists_generalPosition_dist_lt_of_fintype
#print axioms ConvexGeom.nonempty_interior_convexHull_of_inGeneralPosition
#print axioms ConvexGeom.exists_generalPosition_polytope_dist_lt
#print axioms ConvexGeom.exists_inscribed_generalPosition_polytope_dist_lt

-- 16. Vertex Push-Out, Spherical General Position, and Volume Supremum Reductions
#print axioms ConvexGeom.exists_pushOut_vertex_sphere
#print axioms ConvexGeom.exists_pushOut_range_sphere
#print axioms ConvexGeom.exists_sphericalGeneralPosition_snoc
#print axioms ConvexGeom.exists_sphericalGeneralPosition_dist_lt
#print axioms ConvexGeom.exists_sphericalGeneralPosition_dist_lt_of_fintype
#print axioms ConvexGeom.zero_mem_interior_of_addHaar_gt_half_closedBall
#print axioms ConvexGeom.strict_addHaar_convexHull_insert_of_notMem
#print axioms ConvexGeom.iSup_addHaar_convexHull_closedBall_eq_sphere
#print axioms ConvexGeom.mem_sphere_of_max_addHaar_convexHull_closedBall
#print axioms ConvexGeom.iSup_addHaar_convexHull_sphere_eq_generalPosition

-- 17. Combinatorial & Extremal Convexity (Radon, Helly, Minkowski–Carathéodory, Straszewicz, Jung)
#print axioms ConvexGeom.radon_partition_card_ge
#print axioms ConvexGeom.radon_partition_fin
#print axioms ConvexGeom.helly_convexBody
#print axioms ConvexGeom.helly_convexBody_finset
#print axioms ConvexGeom.isCompact_convexHull_of_isCompact
#print axioms ConvexGeom.convexHull_extremePoints_eq
#print axioms ConvexGeom.extremePoints_subset_closure_exposedPoints
#print axioms ConvexGeom.closure_convexHull_exposedPoints
#print axioms ConvexGeom.jung_circumradius_finset
#print axioms ConvexGeom.jung_circumradius
#print axioms ConvexGeom.jung_circumradius_convexBody

-- 18. Polytope Faces, Weyl–Minkowski Duality, Simplicial Facets, and Radial Facet-Cone Tiling
#print axioms ConvexGeom.finite_extremePoints_polarBody
#print axioms ConvexGeom.polarBody_eq_convexHull_facetNormals
#print axioms ConvexGeom.weyl_minkowski_halfspaces
#print axioms ConvexGeom.facetNormals_irredundant
#print axioms ConvexGeom.polytopeFacet_eq_convexHull_tightVertices
#print axioms ConvexGeom.affineSpan_polytopeFacet
#print axioms ConvexGeom.card_tightVertices_eq_finrank_of_inGeneralPosition
#print axioms ConvexGeom.iUnion_facetCone_eq
#print axioms ConvexGeom.pairwise_aedisjoint_facetCone
#print axioms ConvexGeom.addHaar_convexHull_eq_sum_facetCone

-- 19. Spherical Trigonometry, Dihedral Angles, and Spherical Caps
#print axioms ConvexGeom.spherical_law_of_cosines
#print axioms ConvexGeom.spherical_triangle_inequality
#print axioms ConvexGeom.gramDet3_eq_sq_sin_mul
#print axioms ConvexGeom.spherical_law_of_sines
#print axioms ConvexGeom.dihedralAngle_comm
#print axioms ConvexGeom.sphericalCap_eq_closedBall_inter_sphere
#print axioms ConvexGeom.sphericalCap_cos_eq_angle_le
#print axioms ConvexGeom.image_sphericalCap_linearIsometry

-- 20. Translative Covering, Central Intersection Lemma, and Symmetric-Difference Metric
#print axioms ConvexGeom.translativeCoveringNumber_mul_le
#print axioms ConvexGeom.measure_le_translativeCoveringNumber_mul
#print axioms ConvexGeom.translativeCoveringNumber_sub_mul_le
#print axioms ConvexGeom.translativeCoveringNumber_symm_smul_le
#print axioms ConvexGeom.reflectedCovariogram_lintegral
#print axioms ConvexGeom.exists_reflectedCovariogram_ge
#print axioms ConvexGeom.translativeCoveringNumber_mul_volume_le_four_pow
#print axioms ConvexGeom.translativeCoveringNumber_convex_smul_le
#print axioms ConvexGeom.symmDiffVol_triangle
#print axioms ConvexGeom.abs_measureReal_sub_le_symmDiffVolReal
#print axioms ConvexGeom.symmDiffVol_vadd
#print axioms ConvexGeom.symmDiffVol_smul
#print axioms ConvexGeom.tendsto_symmDiffVol_self
#print axioms ConvexGeom.continuous_symmDiffVolReal_convexBody
#print axioms ConvexGeom.continuous_symmDiffVol_convexBody

-- 21. Spherical Isotropic Identity and the Steiner Point
#print axioms ConvexGeom.integral_sphereProb_id
#print axioms ConvexGeom.integral_inner_sq_sphereProb
#print axioms ConvexGeom.integral_inner_mul_inner_sphereProb
#print axioms ConvexGeom.finrank_smul_integral_inner_smul_sphereProb
#print axioms ConvexGeom.steinerPoint_bodySingleton
#print axioms ConvexGeom.steinerPoint_add
#print axioms ConvexGeom.steinerPoint_smul
#print axioms ConvexGeom.steinerPoint_mapLinearIsometry
#print axioms ConvexGeom.steinerPoint_bodyClosedBall
#print axioms ConvexGeom.steinerPoint_mem
#print axioms ConvexGeom.dist_steinerPoint_le
#print axioms ConvexGeom.lipschitzWith_steinerPoint
