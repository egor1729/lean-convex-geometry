module

public import ConvexGeom.Polarity
public import ConvexGeom.Symmetrization
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Spherical Probability Measure, Polar Volume Formula, Mean Width, and Dual Urysohn

Built directly on Mathlib's generalized polar coordinate measure `Measure.toSphere`
(`Mathlib.MeasureTheory.Constructions.HaarToSphere`), this file establishes the spherical
integration layer underlying high-dimensional convex geometry (Ball, Lectures 1–2; Klartag;
Artstein-Avidan–Giannopoulos–Milman, Ch. 1; Schneider, §1.7):

1. **Uniform Spherical Probability Measure (`sphereProb`):**
   `sphereProb μ := (μ.toSphere univ)⁻¹ • μ.toSphere` is a probability measure on `sphere 0 1`,
   invariant under antipodal negation (`measurePreserving_sphereNeg_sphereProb`) and under every
   linear isometry preserving `μ` (in particular, all `U : E ≃ₗᵢ[ℝ] E` for `volume`).
2. **Polar-Coordinate Volume Formula:**
   For any `ConvexBody E` with `0 ∈ interior K` and any add-Haar measure `μ`:
   - `addHaar_real_eq_integral_gauge_inv_pow`:
     $$\mu.\mathrm{real}(K) = \mu.\mathrm{real}(\overline{B}(0, 1)) \int_{S^{d-1}} (\mathrm{gauge}\,K\,u)^{-d}\,d\sigma(u).$$
   - `addHaar_real_polarBody_eq_integral_supportFn_inv_pow`:
     $$\mu.\mathrm{real}(K^\circ) = \mu.\mathrm{real}(\overline{B}(0, 1)) \int_{S^{d-1}} h_K(u)^{-d}\,d\sigma(u).$$
3. **Mean Width (`meanWidth`):**
   `meanWidth K := ∫ u, supportFn K u ∂(sphereProb volume)` with full algebraic & metric calculus:
   Minkowski additivity, positive homogeneity, translation invariance, rotation invariance,
   monotonicity, `meanWidth (bodyClosedBall c r) = r`, 1-Lipschitz continuity in the Hausdorff
   metric (`lipschitzWith_meanWidth`), and invariance under Minkowski and central symmetrization.
4. **Dual Urysohn Inequality (`dual_urysohn_inequality`) & Santaló–Urysohn Bridge (`urysohn_of_santalo`):**
   For any `K : ConvexBody E` with `0 ∈ interior K`:
   $$\left(\frac{\mathrm{vol}(\overline{B}(0, 1))}{\mathrm{vol}(K^\circ)}\right)^{1/d} \le w(K),$$
   and hence any body satisfying the Blaschke–Santaló inequality satisfies Urysohn's inequality.
-/

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ENNReal NNReal Pointwise

namespace ConvexGeom

public section

/-! ### 1. Normalized Uniform Spherical Probability Measure -/

section SphereMap

variable {E : Type*} [NormedAddCommGroup E] [Module ℝ E]

/-- Action of a linear isometry `U : E ≃ₗᵢ[ℝ] E` on the unit sphere `sphere (0 : E) 1`. -/
def sphereMap (U : E ≃ₗᵢ[ℝ] E) : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1 where
  toFun u := ⟨U u.1, by
    rw [mem_sphere_zero_iff_norm, U.norm_map]
    exact mem_sphere_zero_iff_norm.mp u.2⟩
  invFun u := ⟨U.symm u.1, by
    rw [mem_sphere_zero_iff_norm, U.symm.norm_map]
    exact mem_sphere_zero_iff_norm.mp u.2⟩
  left_inv u := Subtype.ext (U.symm_apply_apply u.1)
  right_inv u := Subtype.ext (U.apply_symm_apply u.1)
  continuous_toFun := (U.continuous.comp continuous_subtype_val).subtype_mk fun u => by
    dsimp only [Function.comp_apply]
    rw [mem_sphere_zero_iff_norm, U.norm_map]
    exact mem_sphere_zero_iff_norm.mp u.2
  continuous_invFun := (U.symm.continuous.comp continuous_subtype_val).subtype_mk fun u => by
    dsimp only [Function.comp_apply]
    rw [mem_sphere_zero_iff_norm, U.symm.norm_map]
    exact mem_sphere_zero_iff_norm.mp u.2

@[simp]
lemma sphereMap_coe (U : E ≃ₗᵢ[ℝ] E) (u : sphere (0 : E) 1) :
    ((sphereMap U u : sphere (0 : E) 1) : E) = U u.1 := by
  rfl

end SphereMap

section SphereProb

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The normalized uniform probability measure on `Metric.sphere (0 : E) 1` induced by an
additive Haar measure `μ` on `E`. -/
noncomputable def sphereProb (μ : Measure E) : Measure (sphere (0 : E) 1) :=
  (μ.toSphere Set.univ)⁻¹ • μ.toSphere

instance instIsProbabilityMeasure_sphereProb [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    IsProbabilityMeasure (sphereProb μ) where
  measure_univ := by
    have hne0 : μ.toSphere Set.univ ≠ 0 := by
      rw [Measure.toSphere_apply_univ]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr Module.finrank_pos.ne')
        (isOpen_ball.measure_pos μ ⟨0, mem_ball_self zero_lt_one⟩).ne'
    rw [sphereProb, smul_apply, smul_eq_mul,
      ENNReal.inv_mul_cancel hne0 (measure_ne_top μ.toSphere Set.univ)]

lemma addHaar_closedBall_eq_addHaar_ball [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (c : E) {r : ℝ} (_hr : 0 ≤ r) :
    μ (closedBall c r) = μ (ball c r) := by
  have hunion : closedBall c r = ball c r ∪ sphere c r :=
    (ball_union_sphere (x := c) (ε := r)).symm
  have hdisj : Disjoint (ball c r) (sphere c r) := by
    rw [Set.disjoint_left]
    intro x h1 h2
    rw [mem_ball] at h1; rw [mem_sphere] at h2
    linarith
  rw [hunion, measure_union hdisj isClosed_sphere.measurableSet,
    Measure.addHaar_sphere μ c r, add_zero]

/-- Any linear isometry preserving `μ` preserves `μ.toSphere`. -/
theorem measurePreserving_sphereMap_toSphere [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (U : E ≃ₗᵢ[ℝ] E)
    (hU : MeasurePreserving U μ μ) :
    MeasurePreserving (sphereMap U) μ.toSphere μ.toSphere := by
  refine ⟨(sphereMap U).continuous.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (sphereMap U).continuous.measurable hs,
    μ.toSphere_apply' ((sphereMap U).continuous.measurable hs), μ.toSphere_apply' hs]
  congr 1
  have hpre : Ioo (0 : ℝ) 1 • ((↑) '' (sphereMap U ⁻¹' s)) =
      U ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
    ext x
    simp only [Set.mem_smul, mem_image, mem_preimage, Subtype.exists]
    constructor
    · rintro ⟨t, ht, _, ⟨u, hu, hUs, rfl⟩, rfl⟩
      exact ⟨t, ht, U u, ⟨U u, by simpa [mem_sphere_zero_iff_norm] using hu, hUs, rfl⟩,
        by rw [map_smul]⟩
    · rintro ⟨t, ht, _, ⟨v, hv, hvs, rfl⟩, hUx⟩
      refine ⟨t, ht, U.symm v, ⟨U.symm v, by simpa [mem_sphere_zero_iff_norm] using hv, ?_, rfl⟩, ?_⟩
      · show sphereMap U ⟨U.symm v, _⟩ ∈ s
        have heq : sphereMap U ⟨U.symm v, by simpa [mem_sphere_zero_iff_norm] using hv⟩ =
            ⟨v, hv⟩ := by ext; simp
        rwa [heq]
      · apply U.injective
        rw [map_smul, LinearIsometryEquiv.apply_symm_apply, hUx]
  have hmeas : MeasurableSet (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
    have h1 : Ioo (0 : ℝ) 1 • (Subtype.val '' s) =
        Subtype.val '' ((homeomorphUnitSphereProd E) ⁻¹' (s ×ˢ Iio ⟨1, mem_Ioi.mpr one_pos⟩)) := by
      ext x
      simp only [Set.mem_smul, mem_image, mem_preimage, mem_prod, mem_Iio, Subtype.exists]
      constructor
      · rintro ⟨t, ⟨ht0, ht1⟩, _, ⟨u, hu, hus, rfl⟩, rfl⟩
        have hnorm : ‖t • u‖ = t := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, mem_sphere_zero_iff_norm.mp hu, mul_one]
        have hne : t • u ≠ 0 := by
          rw [ne_eq, ← norm_eq_zero, hnorm]; exact ht0.ne'
        refine ⟨t • u, hne, ⟨?_, ?_⟩, rfl⟩
        · have hfst : (homeomorphUnitSphereProd E ⟨t • u, hne⟩).1 = ⟨u, hu⟩ := by
            ext
            simp only [homeomorphUnitSphereProd_apply_fst_coe, hnorm, smul_smul,
              inv_mul_cancel₀ ht0.ne', one_smul]
          rwa [hfst]
        · change ((homeomorphUnitSphereProd E ⟨t • u, hne⟩).2 : ℝ) < 1
          rw [homeomorphUnitSphereProd_apply_snd_coe, hnorm]; exact ht1
      · rintro ⟨y, hy, ⟨hys, hlt⟩, rfl⟩
        have hy_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy
        have hlt' : ‖y‖ < 1 := by
          have : ((homeomorphUnitSphereProd E ⟨y, hy⟩).2 : ℝ) < 1 := hlt
          rwa [homeomorphUnitSphereProd_apply_snd_coe] at this
        refine ⟨‖y‖, ⟨hy_pos, hlt'⟩, (homeomorphUnitSphereProd E ⟨y, hy⟩).1.1,
          ⟨_, (homeomorphUnitSphereProd E ⟨y, hy⟩).1.2, hys, rfl⟩, ?_⟩
        rw [homeomorphUnitSphereProd_apply_fst_coe, smul_smul, mul_inv_cancel₀ hy_pos.ne', one_smul]
    have hcomp : MeasurableEmbedding (Subtype.val ∘ (homeomorphUnitSphereProd E).symm) :=
      (MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : E)).compl).comp
        (homeomorphUnitSphereProd E).symm.measurableEmbedding
    have h2 : Ioo (0 : ℝ) 1 • (Subtype.val '' s) =
        (Subtype.val ∘ (homeomorphUnitSphereProd E).symm) ''
          (s ×ˢ Iio ⟨1, mem_Ioi.mpr one_pos⟩) := by
      rw [h1, Set.image_comp, Homeomorph.image_symm]
    rw [h2]
    exact hcomp.measurableSet_image.mpr (hs.prod measurableSet_Iio)
  rw [hpre, hU.measure_preimage hmeas.nullMeasurableSet]

/-- Any linear isometry preserving `μ` preserves the uniform spherical probability measure. -/
theorem measurePreserving_sphereMap_sphereProb [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (U : E ≃ₗᵢ[ℝ] E)
    (hU : MeasurePreserving U μ μ) :
    MeasurePreserving (sphereMap U) (sphereProb μ) (sphereProb μ) := by
  have hmp := measurePreserving_sphereMap_toSphere μ U hU
  refine ⟨hmp.measurable, ?_⟩
  rw [sphereProb, Measure.map_smul, hmp.map_eq]
  exact hmp.measurable.aemeasurable

/-- Antipodal negation `u ↦ -u` preserves `sphereProb μ` for every add-Haar measure `μ`. -/
theorem measurePreserving_sphereNeg_sphereProb [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    MeasurePreserving (sphereMap (LinearIsometryEquiv.neg ℝ (E := E)))
      (sphereProb μ) (sphereProb μ) := by
  refine measurePreserving_sphereMap_sphereProb μ (LinearIsometryEquiv.neg ℝ) ?_
  refine ⟨(LinearIsometryEquiv.neg ℝ).continuous.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (LinearIsometryEquiv.neg ℝ).continuous.measurable hs]
  have hpre : (LinearIsometryEquiv.neg ℝ (E := E)) ⁻¹' s = (-1 : ℝ) • s := by
    ext x; simp
  rw [hpre, Measure.addHaar_smul]
  simp

end SphereProb

/-! ### 2. Polar-Coordinate Volume Formula for Convex Bodies -/

section PolarVolume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Helper: `gauge K` is continuous on `E` whenever `0 ∈ interior K`. -/
lemma continuous_gauge_of_zero_mem_interior (K : ConvexBody E)
    (h0 : (0 : E) ∈ interior (K : Set E)) :
    Continuous (gauge (K : Set E)) := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at h0
  obtain ⟨r, hr, hball⟩ := h0
  have hbound : ∀ x : E, gauge (K : Set E) x ≤ (2 / r) * ‖x‖ := fun x => by
    by_cases hx : x = 0
    · simp [hx]
    · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hmem : (r / (2 * ‖x‖)) • x ∈ K := by
        apply hball
        rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
          abs_of_pos (div_pos hr (mul_pos two_pos hxn)),
          div_mul_eq_mul_div, mul_div_mul_right _ _ hxn.ne']
        linarith
      have h1 : gauge (K : Set E) ((r / (2 * ‖x‖)) • x) ≤ 1 := gauge_le_one_of_mem hmem
      have hpos : 0 < r / (2 * ‖x‖) := div_pos hr (mul_pos two_pos hxn)
      rw [gauge_smul_of_nonneg hpos.le] at h1
      exact ((le_div_iff₀' hpos).mpr h1).trans_eq (by field_simp [hr.ne', hxn.ne'])
  refine (LipschitzWith.of_dist_le_mul (K := ⟨2 / r, by positivity⟩) fun x y => ?_).continuous
  change |gauge (K : Set E) x - gauge (K : Set E) y| ≤ (2 / r) * dist x y
  rw [dist_eq_norm, abs_sub_le_iff]
  have habs : Absorbent ℝ (K : Set E) :=
    absorbent_nhds_zero (Metric.mem_nhds_iff.mpr ⟨r, hr, hball⟩)
  constructor
  · have htri : gauge (K : Set E) x ≤ gauge (K : Set E) y + gauge (K : Set E) (x - y) := by
      simpa [add_sub_cancel] using gauge_add_le K.convex habs y (x - y)
    linarith [hbound (x - y)]
  · have htri : gauge (K : Set E) y ≤ gauge (K : Set E) x + gauge (K : Set E) (y - x) := by
      simpa [add_sub_cancel] using gauge_add_le K.convex habs x (y - x)
    have hb := hbound (y - x)
    rw [norm_sub_rev] at hb
    linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Helper: `0 < gauge K u` on `sphere 0 1` when `0 ∈ interior K`. -/
lemma gauge_pos_of_mem_sphere (K : ConvexBody E) (h0 : (0 : E) ∈ interior (K : Set E))
    {u : E} (hu : u ∈ sphere (0 : E) 1) :
    0 < gauge (K : Set E) u := by
  obtain ⟨R, hKR⟩ := K.isBounded.subset_closedBall (0 : E)
  set M := max R 1
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  have hnot : u ∉ (2 * M)⁻¹ • (K : Set E) := by
    rintro ⟨x, hx, hxu⟩
    have hxM : ‖x‖ ≤ M := (mem_closedBall_zero_iff.mp (hKR hx)).trans (le_max_left R 1)
    have hnorm := congrArg norm hxu
    rw [mem_sphere_zero_iff_norm.mp hu, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (mul_pos two_pos hM_pos))] at hnorm
    have hle : (2 * M)⁻¹ * ‖x‖ ≤ 1 / 2 := by
      calc
        (2 * M)⁻¹ * ‖x‖ ≤ (2 * M)⁻¹ * M :=
          mul_le_mul_of_nonneg_left hxM (inv_nonneg.mpr (mul_pos two_pos hM_pos).le)
        _ = 1 / 2 := by field_simp [hM_pos.ne']
    linarith
  have habs : Absorbent ℝ (K : Set E) := absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp h0)
  have hle : (2 * M)⁻¹ ≤ gauge (K : Set E) u :=
    le_gauge_of_notMem (K.convex.starConvex (interior_subset h0)) (habs u) hnot
  exact lt_of_lt_of_le (inv_pos.mpr (mul_pos two_pos hM_pos)) hle

/-- **Polar-Coordinate Volume Formula (`ℝ≥0∞` form):**
for any `ConvexBody E` with `0 ∈ interior K` and any additive Haar measure `μ` in dimension
`d = finrank ℝ E ≥ 1`:
`μ K = μ (closedBall 0 1) * ∫⁻ u, ENNReal.ofReal ((gauge K u)⁻¹ ^ d) ∂(sphereProb μ)`. -/
theorem addHaar_eq_lintegral_gauge_inv_pow [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : ConvexBody E) (h0 : (0 : E) ∈ interior (K : Set E)) :
    μ (K : Set E) = μ (closedBall (0 : E) 1) *
      ∫⁻ u : sphere (0 : E) 1,
        ENNReal.ofReal ((gauge (K : Set E) u.1)⁻¹ ^ Module.finrank ℝ E) ∂(sphereProb μ) := by
  set d := Module.finrank ℝ E
  have hd_pos : 0 < d := Module.finrank_pos
  have hnhds : (K : Set E) ∈ nhds (0 : E) := mem_interior_iff_mem_nhds.mp h0
  -- Transfer `μ K` to `sphere 0 1 × Ioi 0` via `measurePreserving_homeomorphUnitSphereProd`.
  have hK0 : μ (K : Set E) = μ ((K : Set E) \ {0}) := by
    rw [measure_sdiff_null (measure_singleton (0 : E))]
  let A : Set (sphere (0 : E) 1 × Ioi (0 : ℝ)) :=
    {p | (p.2 : ℝ) • (p.1 : E) ∈ (K : Set E)}
  have hAm : MeasurableSet A := by
    have hcont : Continuous (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => (p.2 : ℝ) • (p.1 : E)) :=
      (continuous_subtype_val.comp continuous_snd).smul (continuous_subtype_val.comp continuous_fst)
    exact (K.isClosed.preimage hcont).measurableSet
  have hpre : (homeomorphUnitSphereProd E) ⁻¹' A =
      (Subtype.val : ({0}ᶜ : Set E) → E) ⁻¹' (K : Set E) := by
    ext ⟨x, hx⟩
    simp only [mem_preimage, A, mem_ofPred_eq, homeomorphUnitSphereProd_apply_fst_coe,
      homeomorphUnitSphereProd_apply_snd_coe]
    have hne : x ≠ 0 := hx
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hne), one_smul]
  have hpolar : μ (K : Set E) =
      (μ.toSphere.prod (Measure.volumeIoiPow (d - 1))) A := by
    have hmp := μ.measurePreserving_homeomorphUnitSphereProd
    rw [← hmp.measure_preimage hAm.nullMeasurableSet, hpre,
      Measure.comap_apply _ Subtype.val_injective
        (fun s hs => (MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : E)).compl).measurableSet_image.mpr hs)
        _ ((K.isClosed.preimage continuous_subtype_val).measurableSet),
      show Subtype.val '' ((Subtype.val : ({0}ᶜ : Set E) → E) ⁻¹' (K : Set E)) =
        (K : Set E) \ {0} by ext x; simp [Set.sdiff_eq, and_comm],
      ← hK0]
  rw [hpolar, Measure.prod_apply hAm]
  -- Evaluate the radial fiber measure for every `u ∈ sphere 0 1`.
  have hfiber : ∀ u : sphere (0 : E) 1,
      Measure.volumeIoiPow (d - 1) (Prod.mk u ⁻¹' A) =
        ENNReal.ofReal ((gauge (K : Set E) u.1)⁻¹ ^ d / (d : ℝ)) := by
    intro u
    have hgu_pos : 0 < gauge (K : Set E) u.1 := gauge_pos_of_mem_sphere K h0 u.2
    let r₀ : Ioi (0 : ℝ) := ⟨(gauge (K : Set E) u.1)⁻¹, inv_pos.mpr hgu_pos⟩
    have hlo : Iio r₀ ⊆ Prod.mk u ⁻¹' A := by
      intro r hr
      have hrlt : (r : ℝ) < 1 / gauge (K : Set E) u.1 := by
        rw [one_div]; exact hr
      have hglt : gauge (K : Set E) ((r : ℝ) • u.1) < 1 := by
        rw [gauge_smul_of_nonneg r.2.out.le]
        simpa [smul_eq_mul] using (lt_div_iff₀ hgu_pos).mp hrlt
      show (r : ℝ) • u.1 ∈ (K : Set E)
      exact interior_subset ((gauge_lt_one_iff_mem_interior K.convex hnhds).mp hglt)
    have hhi : Prod.mk u ⁻¹' A ⊆ Iic r₀ := by
      intro r hr
      have hgle : gauge (K : Set E) ((r : ℝ) • u.1) ≤ 1 := gauge_le_one_of_mem hr
      rw [gauge_smul_of_nonneg r.2.out.le, smul_eq_mul] at hgle
      change (r : ℝ) ≤ (gauge (K : Set E) u.1)⁻¹
      rw [← one_div, le_div_iff₀ hgu_pos]
      exact hgle
    have hsingle : Measure.volumeIoiPow (d - 1) {r₀} = 0 := by
      have hzero : (Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) volume) {r₀} = 0 := by
        rw [Measure.comap_apply _ Subtype.val_injective
          (fun s hs => (MeasurableEmbedding.subtype_coe measurableSet_Ioi).measurableSet_image.mpr hs)
          _ (measurableSet_singleton r₀), image_singleton, measure_singleton]
      rw [Measure.volumeIoiPow, withDensity_apply _ (measurableSet_singleton r₀),
        Measure.restrict_eq_zero.mpr hzero, lintegral_zero_measure]
    have hIic : Measure.volumeIoiPow (d - 1) (Iic r₀) = Measure.volumeIoiPow (d - 1) (Iio r₀) := by
      rw [← Iio_union_right]
      exact le_antisymm
        ((measure_union_le _ _).trans (by rw [hsingle, add_zero]))
        (measure_mono subset_union_left)
    have heq : Measure.volumeIoiPow (d - 1) (Prod.mk u ⁻¹' A) =
        Measure.volumeIoiPow (d - 1) (Iio r₀) :=
      le_antisymm ((measure_mono hhi).trans_eq hIic) (measure_mono hlo)
    rw [heq, Measure.volumeIoiPow_apply_Iio, Nat.sub_add_cancel hd_pos]
    have hd_cast : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel hd_pos
    rw [hd_cast]
  simp_rw [hfiber]
  -- Pull out `1 / d` and convert `μ.toSphere` to `sphereProb μ`.
  have hdiv : ∀ u : sphere (0 : E) 1,
      ENNReal.ofReal ((gauge (K : Set E) u.1)⁻¹ ^ d / (d : ℝ)) =
        ENNReal.ofReal ((d : ℝ)⁻¹) * ENNReal.ofReal ((gauge (K : Set E) u.1)⁻¹ ^ d) := fun u => by
    rw [div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg d))]
  simp_rw [hdiv]
  have hmeas_g : Measurable (fun u : sphere (0 : E) 1 =>
      ENNReal.ofReal ((gauge (K : Set E) u.1)⁻¹ ^ d)) := by
    have hcont : Continuous (fun u : sphere (0 : E) 1 => (gauge (K : Set E) u.1)⁻¹ ^ d) :=
      (((continuous_gauge_of_zero_mem_interior K h0).comp continuous_subtype_val).inv₀
        fun u => (gauge_pos_of_mem_sphere K h0 u.2).ne').pow d
    exact ENNReal.measurable_ofReal.comp hcont.measurable
  rw [lintegral_const_mul _ hmeas_g]
  -- Rewrite `∫⁻ ∂(sphereProb μ) = (μ.toSphere univ)⁻¹ * ∫⁻ ∂(μ.toSphere)`.
  rw [sphereProb, lintegral_smul_measure, smul_eq_mul, Measure.toSphere_apply_univ,
    ← addHaar_closedBall_eq_addHaar_ball μ 0 zero_le_one]
  have hB0 : μ (closedBall (0 : E) 1) ≠ 0 := by
    rw [addHaar_closedBall_eq_addHaar_ball μ 0 zero_le_one]
    exact (isOpen_ball.measure_pos μ ⟨0, mem_ball_self zero_lt_one⟩).ne'
  have hBfin : μ (closedBall (0 : E) 1) ≠ ⊤ := (isCompact_closedBall (0 : E) 1).measure_lt_top.ne
  have hd0 : (d : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
  have hdfin : (d : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top d
  rw [ENNReal.mul_inv (Or.inl hd0) (Or.inl hdfin),
    ← mul_assoc (μ (closedBall (0 : E) 1)), mul_left_comm (μ (closedBall (0 : E) 1)) (d : ℝ≥0∞)⁻¹,
    ENNReal.mul_inv_cancel hB0 hBfin, mul_one,
    ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr hd_pos), ENNReal.ofReal_natCast]

/-- **Polar-Coordinate Volume Formula (real-valued Bochner integral form):**
`μ.real K = μ.real (closedBall 0 1) * ∫ u, (gauge K u)⁻¹ ^ d ∂(sphereProb μ)`. -/
theorem addHaar_real_eq_integral_gauge_inv_pow [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : ConvexBody E) (h0 : (0 : E) ∈ interior (K : Set E)) :
    μ.real (K : Set E) = μ.real (closedBall (0 : E) 1) *
      ∫ u : sphere (0 : E) 1,
        (gauge (K : Set E) u.1)⁻¹ ^ Module.finrank ℝ E ∂(sphereProb μ) := by
  have hcont : Continuous (fun u : sphere (0 : E) 1 =>
      (gauge (K : Set E) u.1)⁻¹ ^ Module.finrank ℝ E) :=
    (((continuous_gauge_of_zero_mem_interior K h0).comp continuous_subtype_val).inv₀
      fun u => (gauge_pos_of_mem_sphere K h0 u.2).ne').pow _
  have hint : Integrable (fun u : sphere (0 : E) 1 =>
      (gauge (K : Set E) u.1)⁻¹ ^ Module.finrank ℝ E) (sphereProb μ) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hnn : 0 ≤ᵐ[sphereProb μ] fun u : sphere (0 : E) 1 =>
      (gauge (K : Set E) u.1)⁻¹ ^ Module.finrank ℝ E :=
    Filter.Eventually.of_forall fun u =>
      pow_nonneg (inv_nonneg.mpr (gauge_pos_of_mem_sphere K h0 u.2).le) _
  have hlin := addHaar_eq_lintegral_gauge_inv_pow μ K h0
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn] at hlin
  have htoReal := congrArg ENNReal.toReal hlin
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (integral_nonneg fun u => pow_nonneg (inv_nonneg.mpr (gauge_pos_of_mem_sphere K h0 u.2).le) _)]
    at htoReal
  exact htoReal

/-- **Polar Volume Formula for Polar Bodies:**
for any `K : ConvexBody E` with `0 ∈ interior K` and any add-Haar measure `μ`:
`μ.real (polarBody K) = μ.real (closedBall 0 1) * ∫ u, (supportFn K u)⁻¹ ^ d ∂(sphereProb μ)`. -/
theorem addHaar_real_polarBody_eq_integral_supportFn_inv_pow [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : ConvexBody E) (h0 : (0 : E) ∈ interior (K : Set E)) :
    μ.real (polarBody (K : Set E)) = μ.real (closedBall (0 : E) 1) *
      ∫ u : sphere (0 : E) 1,
        (supportFn K u.1)⁻¹ ^ Module.finrank ℝ E ∂(sphereProb μ) := by
  have h0pol : (0 : E) ∈ interior ((bodyPolar (K : Set E) h0 : ConvexBody E) : Set E) := by
    rw [coe_bodyPolar]
    exact zero_mem_interior_polarBody_of_isBounded K.isBounded
  have h := addHaar_real_eq_integral_gauge_inv_pow μ (bodyPolar (K : Set E) h0) h0pol
  rw [coe_bodyPolar] at h
  simp_rw [gauge_polarBody_eq_supportFn K (interior_subset h0)] at h
  exact h

end PolarVolume

/-! ### 3. Mean Width and Its Calculus -/

section MeanWidth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Mean width** (half mean breadth) of a convex body `K : ConvexBody E`:
`meanWidth K = ∫ u ∈ S^{d-1}, supportFn K u dσ(u)`, normalized so `meanWidth B(c, r) = r`. -/
noncomputable def meanWidth (K : ConvexBody E) : ℝ :=
  ∫ u : sphere (0 : E) 1, supportFn K u.1 ∂(sphereProb (volume : Measure E))

lemma integrable_supportFn_sphereProb [Nontrivial E] (K : ConvexBody E) :
    Integrable (fun u : sphere (0 : E) 1 => supportFn K u.1) (sphereProb (volume : Measure E)) :=
  ((continuous_supportFn K).comp continuous_subtype_val).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Minkowski additivity of mean width: `meanWidth (K + L) = meanWidth K + meanWidth L`. -/
theorem meanWidth_add [Nontrivial E] (K L : ConvexBody E) :
    meanWidth (K + L) = meanWidth K + meanWidth L := by
  simp only [meanWidth, supportFn_minkowski_add]
  exact integral_add (integrable_supportFn_sphereProb K) (integrable_supportFn_sphereProb L)

/-- Positive homogeneity of mean width: `meanWidth (c • K) = c * meanWidth K` for `c ≥ 0`. -/
theorem meanWidth_smul [Nontrivial E] (K : ConvexBody E) {c : ℝ} (hc : 0 ≤ c) :
    meanWidth (c • K) = c * meanWidth K := by
  simp only [meanWidth, supportFn_body_smul K hc]
  exact integral_const_mul c _

/-- Negation invariance: `meanWidth ((-1) • K) = meanWidth K`. -/
theorem meanWidth_neg_one_smul [Nontrivial E] (K : ConvexBody E) :
    meanWidth ((-1 : ℝ) • K) = meanWidth K := by
  simp only [meanWidth, supportFn_neg_one_smul]
  have hmp := measurePreserving_sphereNeg_sphereProb (E := E) (volume : Measure E)
  simpa [sphereMap_coe] using
    hmp.integral_comp (sphereMap (LinearIsometryEquiv.neg ℝ (E := E))).measurableEmbedding
      (fun u : sphere (0 : E) 1 => supportFn K u.1)

/-- Singletons have zero mean width (by antipodal symmetry of the sphere). -/
theorem meanWidth_bodySingleton [Nontrivial E] (a : E) :
    meanWidth (bodySingleton a) = 0 := by
  have h1 : meanWidth (bodySingleton a) = meanWidth ((-1 : ℝ) • bodySingleton a) :=
    (meanWidth_neg_one_smul (bodySingleton a)).symm
  have h2 : meanWidth ((-1 : ℝ) • bodySingleton a) = -meanWidth (bodySingleton a) := by
    simp only [meanWidth, supportFn_neg_one_smul, supportFn_bodySingleton, inner_neg_right]
    exact integral_neg _
  linarith

/-- Translation invariance of mean width: `meanWidth (K + {a}) = meanWidth K`. -/
theorem meanWidth_translate [Nontrivial E] (K : ConvexBody E) (a : E) :
    meanWidth (K + bodySingleton a) = meanWidth K := by
  rw [meanWidth_add, meanWidth_bodySingleton, add_zero]

/-- Monotonicity of mean width: `K ⊆ L → meanWidth K ≤ meanWidth L`. -/
theorem meanWidth_mono [Nontrivial E] {K L : ConvexBody E} (hKL : (K : Set E) ⊆ L) :
    meanWidth K ≤ meanWidth L :=
  integral_mono (integrable_supportFn_sphereProb K) (integrable_supportFn_sphereProb L)
    fun u => supportFn_mono hKL u.1

/-- Mean width is always nonnegative. -/
theorem meanWidth_nonneg [Nontrivial E] (K : ConvexBody E) :
    0 ≤ meanWidth K := by
  have hsum : meanWidth K + meanWidth K = meanWidth (K + (-1 : ℝ) • K) := by
    rw [meanWidth_add, meanWidth_neg_one_smul]
  have hnn : 0 ≤ meanWidth (K + (-1 : ℝ) • K) := by
    rw [meanWidth]
    refine integral_nonneg fun u => ?_
    rw [← width_eq_supportFn_diff]
    exact width_nonneg K u.1
  linarith

/-- The closed ball of radius `r ≥ 0` has mean width exactly `r`. -/
theorem meanWidth_bodyClosedBall [Nontrivial E] (c : E) {r : ℝ} (hr : 0 ≤ r) :
    meanWidth (bodyClosedBall c hr) = r := by
  have hsplit : bodyClosedBall c hr = bodySingleton c + bodyClosedBall 0 hr := by
    apply supportFn_injective
    ext u
    rw [supportFn_minkowski_add, supportFn_bodySingleton, supportFn_bodyClosedBall,
      supportFn_bodyClosedBall, inner_zero_left, zero_add]
  rw [hsplit, add_comm, meanWidth_translate]
  simp only [meanWidth, supportFn_bodyClosedBall, inner_zero_left, zero_add]
  have hconst : ∀ u : sphere (0 : E) 1, r * ‖u.1‖ = r := fun u => by
    rw [mem_sphere_zero_iff_norm.mp u.2, mul_one]
  simp_rw [hconst]
  simp [integral_const]

/-- **Mean width is 1-Lipschitz in the Hausdorff metric:**
`|meanWidth K - meanWidth L| ≤ dist K L`. -/
theorem dist_meanWidth_le [Nontrivial E] (K L : ConvexBody E) :
    dist (meanWidth K) (meanWidth L) ≤ dist K L := by
  rw [Real.dist_eq, meanWidth, meanWidth,
    ← integral_sub (integrable_supportFn_sphereProb K) (integrable_supportFn_sphereProb L)]
  have hle : ∀ u : sphere (0 : E) 1, |supportFn K u.1 - supportFn L u.1| ≤ dist K L := fun u => by
    have hmem : u.1 ∈ closedBall (0 : E) 1 := by
      rw [mem_closedBall_zero_iff, mem_sphere_zero_iff_norm.mp u.2]
    have h1 := BoundedContinuousFunction.dist_coe_le_dist
      (f := supportFnOnBall K) (g := supportFnOnBall L) (⟨u.1, hmem⟩ : closedBall (0 : E) 1)
    rw [← dist_eq_dist_supportFnOnBall] at h1
    simpa [supportFnOnBall_apply, Real.dist_eq] using h1
  calc
    |∫ u : sphere (0 : E) 1, (supportFn K u.1 - supportFn L u.1) ∂(sphereProb volume)|
      ≤ ∫ u : sphere (0 : E) 1, |supportFn K u.1 - supportFn L u.1| ∂(sphereProb volume) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _u : sphere (0 : E) 1, dist K L ∂(sphereProb volume) :=
        integral_mono (((integrable_supportFn_sphereProb K).sub
          (integrable_supportFn_sphereProb L)).abs) (integrable_const _) hle
    _ = dist K L := by simp [integral_const]

theorem lipschitzWith_meanWidth [Nontrivial E] :
    LipschitzWith 1 (meanWidth (E := E)) :=
  LipschitzWith.of_dist_le_mul fun K L => by simpa using dist_meanWidth_le K L

/-- Rotation / reflection invariance of mean width: any linear isometry `U : E ≃ₗᵢ[ℝ] E`
preserves `meanWidth`. -/
theorem meanWidth_linearIsometry [Nontrivial E] (U : E ≃ₗᵢ[ℝ] E) (K L : ConvexBody E)
    (hL : ∀ v : E, supportFn L v = supportFn K (U.symm v)) :
    meanWidth L = meanWidth K := by
  simp only [meanWidth, hL]
  have hmp := measurePreserving_sphereMap_sphereProb (volume : Measure E) U.symm
    U.symm.measurePreserving
  simpa [sphereMap_coe] using
    hmp.integral_comp (sphereMap U.symm).measurableEmbedding
      (fun u : sphere (0 : E) 1 => supportFn K u.1)

/-- Mean width is invariant under Minkowski symmetrization. -/
theorem meanWidth_minkowskiSymm [Nontrivial E] {u : E} (hu : ‖u‖ = 1) (K : ConvexBody E) :
    meanWidth (minkowskiSymm hu K) = meanWidth K := by
  have hrefl : meanWidth (reflectBody hu K) = meanWidth K :=
    meanWidth_linearIsometry (reflectHyperplane hu) K (reflectBody hu K) fun v => by
      rw [supportFn_reflectBody, reflectHyperplane_symm]
  have h1 : ∀ v : sphere (0 : E) 1,
      supportFn (minkowskiSymm hu K) v.1 =
        (1 / 2 : ℝ) * (supportFn K v.1 + supportFn (reflectBody hu K) v.1) := fun v => by
    rw [supportFn_minkowskiSymm, supportFn_reflectBody]; ring
  rw [meanWidth]
  simp_rw [h1]
  rw [integral_const_mul, integral_add (integrable_supportFn_sphereProb K)
    (integrable_supportFn_sphereProb (reflectBody hu K))]
  change (1 / 2 : ℝ) * (meanWidth K + meanWidth (reflectBody hu K)) = meanWidth K
  rw [hrefl]; ring

/-- Mean width is invariant under central symmetrization. -/
theorem meanWidth_centralSymm [Nontrivial E] (K : ConvexBody E) :
    meanWidth (centralSymm K) = meanWidth K := by
  have h1 : ∀ v : sphere (0 : E) 1,
      supportFn (centralSymm K) v.1 =
        (1 / 2 : ℝ) * (supportFn K v.1 + supportFn ((-1 : ℝ) • K) v.1) := fun v => by
    rw [supportFn_centralSymm, width_eq_supportFn_diff, supportFn_minkowski_add]; ring
  rw [meanWidth]
  simp_rw [h1]
  rw [integral_const_mul, integral_add (integrable_supportFn_sphereProb K)
    (integrable_supportFn_sphereProb ((-1 : ℝ) • K))]
  change (1 / 2 : ℝ) * (meanWidth K + meanWidth ((-1 : ℝ) • K)) = meanWidth K
  rw [meanWidth_neg_one_smul]; ring

/-! ### 4. Dual Urysohn Inequality and the Santaló–Urysohn Bridge -/

/-- Helper: `x ↦ (x ^ d)⁻¹` is convex on `[r, ∞)` for any `r > 0` and `d : ℕ`. -/
private lemma convexOn_inv_pow {r : ℝ} (hr : 0 < r) (d : ℕ) :
    ConvexOn ℝ (Ici r) (fun x : ℝ => (x ^ d)⁻¹) := by
  refine ⟨convex_Ici r, fun x hx y hy a b ha hb hab => ?_⟩
  have hx_pos : 0 < x := lt_of_lt_of_le hr hx
  have hy_pos : 0 < y := lt_of_lt_of_le hr hy
  have hxy_pos : 0 < a * x + b * y := by
    rcases ha.eq_or_lt with rfl | ha_pos
    · have hb1 : b = 1 := by linarith
      subst hb1; simpa using hy_pos
    · exact add_pos_of_pos_of_nonneg (mul_pos ha_pos hx_pos) (mul_nonneg hb hy_pos.le)
  have hinv : (a * x + b * y)⁻¹ ≤ a * x⁻¹ + b * y⁻¹ := by
    have hnum : x * y ≤ (a * x + b * y) * (a * y + b * x) := by
      have hid : (a * x + b * y) * (a * y + b * x) - x * y =
          ((a + b) ^ 2 - 1) * (x * y) + a * b * (x - y) ^ 2 := by ring
      rw [hab] at hid
      have hsq : 0 ≤ a * b * (x - y) ^ 2 := by positivity
      linarith
    have hprod : 0 < (a * x + b * y) * (x * y) := mul_pos hxy_pos (mul_pos hx_pos hy_pos)
    have hdiv := div_le_div_of_nonneg_right hnum hprod.le
    have hlhs : x * y / ((a * x + b * y) * (x * y)) = (a * x + b * y)⁻¹ := by
      field_simp [hxy_pos.ne', hx_pos.ne', hy_pos.ne']
    have hrhs : (a * x + b * y) * (a * y + b * x) / ((a * x + b * y) * (x * y)) =
        a * x⁻¹ + b * y⁻¹ := by
      field_simp [hxy_pos.ne', hx_pos.ne', hy_pos.ne']
    linarith
  have hpow_conv := (convexOn_pow d).2 (inv_nonneg.mpr hx_pos.le) (inv_nonneg.mpr hy_pos.le) ha hb hab
  simpa [smul_eq_mul, inv_pow] using
    (pow_le_pow_left₀ (inv_nonneg.mpr hxy_pos.le) hinv d).trans hpow_conv

/-- **Dual Urysohn Inequality:**
for any `ConvexBody E` with `0 ∈ interior K` in dimension `d = finrank ℝ E ≥ 1`:
$$(w(K))^{-d} \le \frac{\mathrm{vol}(K^\circ)}{\mathrm{vol}(\overline{B}(0, 1))},$$
or equivalently `(vol(B₁) / vol(K°)) ^ (1 / d) ≤ meanWidth K`. -/
theorem dual_urysohn_inequality [Nontrivial E]
    (K : ConvexBody E) (h0 : (0 : E) ∈ interior (K : Set E)) :
    ((volume.real (closedBall (0 : E) 1)) / (volume.real (polarBody (K : Set E)))) ^
        (1 / (Module.finrank ℝ E : ℝ)) ≤
      meanWidth K := by
  set d := Module.finrank ℝ E
  have hd_pos : 1 ≤ d := Module.finrank_pos
  have hd_rpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd_pos
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at h0
  obtain ⟨r, hr, hball⟩ := h0
  have h0' : (0 : E) ∈ interior (K : Set E) :=
    mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨r, hr, hball⟩)
  have hcb_sub : closedBall (0 : E) (r / 2) ⊆ (K : Set E) := fun x hx =>
    hball (by rw [mem_ball_zero_iff]; linarith [mem_closedBall_zero_iff.mp hx])
  have hr2_pos : 0 < r / 2 := half_pos hr
  have hsup_ge : ∀ u : sphere (0 : E) 1, r / 2 ≤ supportFn K u.1 := fun u => by
    have hmem : (r / 2) • u.1 ∈ K := hcb_sub (by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr2_pos,
        mem_sphere_zero_iff_norm.mp u.2, mul_one])
    calc
      r / 2 = ⟪(r / 2) • u.1, u.1⟫ := by
        rw [inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq,
          mem_sphere_zero_iff_norm.mp u.2, one_pow, mul_one]
      _ ≤ supportFn K u.1 := inner_le_supportFn hmem u.1
  have hconv : ConvexOn ℝ (Ici (r / 2)) (fun x : ℝ => (x ^ d)⁻¹) := convexOn_inv_pow hr2_pos d
  have hcont_g : ContinuousOn (fun x : ℝ => (x ^ d)⁻¹) (Ici (r / 2)) :=
    (continuousOn_pow d).inv₀ fun x hx => pow_ne_zero d (lt_of_lt_of_le hr2_pos hx).ne'
  have hint_comp : Integrable (fun u : sphere (0 : E) 1 => (supportFn K u.1 ^ d)⁻¹)
      (sphereProb (volume : Measure E)) := by
    have hcont : Continuous (fun u : sphere (0 : E) 1 => (supportFn K u.1 ^ d)⁻¹) :=
      (((continuous_supportFn K).comp continuous_subtype_val).pow d).inv₀ fun u =>
        pow_ne_zero d (lt_of_lt_of_le hr2_pos (hsup_ge u)).ne'
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hjensen : (meanWidth K ^ d)⁻¹ ≤
      ∫ u : sphere (0 : E) 1, (supportFn K u.1 ^ d)⁻¹ ∂(sphereProb (volume : Measure E)) := by
    simpa [meanWidth, Function.comp_def] using
      hconv.map_integral_le hcont_g isClosed_Ici (Filter.Eventually.of_forall hsup_ge)
        (integrable_supportFn_sphereProb K) hint_comp
  have hpol := addHaar_real_polarBody_eq_integral_supportFn_inv_pow (volume : Measure E) K h0'
  simp_rw [inv_pow] at hpol
  have hvB_pos : 0 < volume.real (closedBall (0 : E) 1) := by
    rw [Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨by rw [addHaar_closedBall_eq_addHaar_ball volume 0 zero_le_one]
              exact isOpen_ball.measure_pos volume ⟨0, mem_ball_self zero_lt_one⟩,
           (isCompact_closedBall (0 : E) 1).measure_lt_top⟩
  have hmw_pos : 0 < meanWidth K := by
    calc
      0 < r / 2 := hr2_pos
      _ = ∫ _u : sphere (0 : E) 1, r / 2 ∂(sphereProb (volume : Measure E)) := by
          simp [integral_const]
      _ ≤ meanWidth K := integral_mono (integrable_const _) (integrable_supportFn_sphereProb K) hsup_ge
  have hpol_ratio : (meanWidth K ^ d)⁻¹ ≤
      volume.real (polarBody (K : Set E)) / volume.real (closedBall (0 : E) 1) := by
    rw [hpol, mul_div_cancel_left₀ _ hvB_pos.ne']
    exact hjensen
  have hvpol_pos : 0 < volume.real (polarBody (K : Set E)) := by
    have hpos_inv : 0 < (meanWidth K ^ d)⁻¹ := inv_pos.mpr (pow_pos hmw_pos d)
    have hdiv_pos : 0 < volume.real (polarBody (K : Set E)) / volume.real (closedBall (0 : E) 1) :=
      lt_of_lt_of_le hpos_inv hpol_ratio
    exact (div_pos_iff_of_pos_right hvB_pos).mp hdiv_pos
  have hle_pow : volume.real (closedBall (0 : E) 1) / volume.real (polarBody (K : Set E)) ≤
      meanWidth K ^ d := by
    have := inv_anti₀ (inv_pos.mpr (pow_pos hmw_pos d)) hpol_ratio
    simpa [inv_div] using this
  calc
    (volume.real (closedBall (0 : E) 1) / volume.real (polarBody (K : Set E))) ^ (1 / (d : ℝ))
      ≤ (meanWidth K ^ d) ^ (1 / (d : ℝ)) :=
        Real.rpow_le_rpow (div_nonneg hvB_pos.le hvpol_pos.le) hle_pow (one_div_nonneg.mpr hd_rpos.le)
    _ = meanWidth K := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hmw_pos.le,
          mul_one_div_cancel hd_rpos.ne', Real.rpow_one]

/-- **Santaló–Urysohn Bridge:**
if `K` satisfies the Blaschke–Santaló inequality `vol(K) * vol(K°) ≤ vol(B₁)²`, then `K`
satisfies **Urysohn's Inequality**: `(vol(K) / vol(B₁)) ^ (1 / d) ≤ meanWidth K`. -/
theorem urysohn_of_santalo [Nontrivial E]
    (K : ConvexBody E) (h0 : (0 : E) ∈ interior (K : Set E))
    (hsantalo : volume.real (K : Set E) * volume.real (polarBody (K : Set E)) ≤
      volume.real (closedBall (0 : E) 1) ^ 2) :
    (volume.real (K : Set E) / volume.real (closedBall (0 : E) 1)) ^
        (1 / (Module.finrank ℝ E : ℝ)) ≤
      meanWidth K := by
  set d := Module.finrank ℝ E
  have hd_rpos : (0 : ℝ) < d := Nat.cast_pos.mpr Module.finrank_pos
  have hvB_pos : 0 < volume.real (closedBall (0 : E) 1) := by
    rw [Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨by rw [addHaar_closedBall_eq_addHaar_ball volume 0 zero_le_one]
              exact isOpen_ball.measure_pos volume ⟨0, mem_ball_self zero_lt_one⟩,
           (isCompact_closedBall (0 : E) 1).measure_lt_top⟩
  have h0pol : (0 : E) ∈ interior (polarBody (K : Set E)) :=
    zero_mem_interior_polarBody_of_isBounded K.isBounded
  have hvpol_pos : 0 < volume.real (polarBody (K : Set E)) := by
    rw [Measure.real, ENNReal.toReal_pos_iff]
    refine ⟨?_, (isCompact_polarBody_of_zero_mem_interior h0).measure_lt_top⟩
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at h0pol
    obtain ⟨r, hr, hball⟩ := h0pol
    exact (isOpen_ball.measure_pos volume ⟨0, mem_ball_self hr⟩).trans_le (measure_mono hball)
  have hratio : volume.real (K : Set E) / volume.real (closedBall (0 : E) 1) ≤
      volume.real (closedBall (0 : E) 1) / volume.real (polarBody (K : Set E)) := by
    rw [div_le_div_iff₀ hvB_pos hvpol_pos]
    simpa [sq] using hsantalo
  exact (Real.rpow_le_rpow (div_nonneg measureReal_nonneg hvB_pos.le) hratio
    (one_div_nonneg.mpr hd_rpos.le)).trans (dual_urysohn_inequality K h0)

end MeanWidth

end

end ConvexGeom
