module

public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Support Functions, Hörmander's Embedding, and Minkowski's Representation

This file develops the theory of the support function `supportFn K u = sSup {⟪x, u⟫ | x ∈ K}`
of a `ConvexBody E` in a real inner product space `E` (following Schneider, *Convex Bodies*,
§1.7–1.8).

**Convention:** Mathlib's `ConvexBody E` is the type of nonempty compact convex subsets of `E`,
so it deliberately includes degenerate bodies with empty interior (singletons, line segments,
radius-zero balls). Results requiring nonempty interior or `0 ∈ interior K` state that hypothesis
explicitly.

1. **Constructors & Transport:** `bodySingleton`, `bodyClosedBall`, and continuous linear image
   transport `mapLinear` (`coe_mapLinear`, `mapLinear_id`, `mapLinear_comp`, `dist_mapLinear_le`,
   `supportFn_mapLinearIsometry`).
2. **Core calculus:** attainment (`exists_mem_supportFn_eq`), sublinearity (`supportFn_smul`,
   `supportFn_add_le`, `supportFn_convexOn`), Minkowski additivity (`supportFn_minkowski_add`),
   body scaling (`supportFn_body_smul`), negation (`supportFn_neg_one_smul`), and formulas for
   singletons and closed balls (`supportFn_bodySingleton`, `supportFn_bodyClosedBall`).
3. **Separation, Halfspace Characterization & Width:**
   - `supportFn_le_iff_subset`, `supportFn_injective`, `mem_iff_forall_inner_le_supportFn`.
   - `width K u := supportFn K u + supportFn K (-u)`, `diam_eq_sSup_width`, and
     `diam_eq_sSup_width_sphere` (in nontrivial spaces).
4. **Hörmander's Isometric Embedding:**
   - `supportFnOnBall : ConvexBody E → (Metric.closedBall (0 : E) 1 →ᵇ ℝ)` is an **isometry**:
     `dist_eq_dist_supportFnOnBall`, `dist_le_iff_supportFn_sub_le`,
     `dist_le_iff_supportFn_sub_le_sphere`, `dist_add_right`, `dist_add_le`, `dist_smul`.
5. **Minkowski's Representation Theorem (Schneider, Thm. 1.7.1):**
   - `bodyOfSupportFn`: constructive halfspace-intersection `ConvexBody E` from a sublinear `h`,
     with `coe_bodyOfSupportFn`, `supportFn_bodyOfSupportFn`, and `exists_convexBody_supportFn_eq`.
-/

open scoped RealInnerProductSpace Pointwise BoundedContinuousFunction

namespace ConvexGeom

public section

/-! ### 1. Basic Constructors and Continuous Linear Transport -/

section Transport

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Image of a convex body `K : ConvexBody E` under a continuous linear map `f : E →L[ℝ] F`. -/
def mapLinear (f : E →L[ℝ] F) (K : ConvexBody E) : ConvexBody F where
  carrier := f '' (K : Set E)
  convex' := K.convex.linear_image f.toLinearMap
  isCompact' := K.isCompact.image f.continuous
  nonempty' := K.nonempty.image f

@[simp]
lemma coe_mapLinear (f : E →L[ℝ] F) (K : ConvexBody E) :
    (mapLinear f K : Set F) = f '' (K : Set E) := by
  simp [mapLinear, ConvexBody.coe_mk]

@[simp]
lemma mapLinear_id (K : ConvexBody E) :
    mapLinear (ContinuousLinearMap.id ℝ E) K = K := by
  apply ConvexBody.ext
  simp

lemma mapLinear_comp (g : F →L[ℝ] G) (f : E →L[ℝ] F) (K : ConvexBody E) :
    mapLinear (g.comp f) K = mapLinear g (mapLinear f K) := by
  apply ConvexBody.ext
  rw [coe_mapLinear, coe_mapLinear, coe_mapLinear, ContinuousLinearMap.coe_comp, Set.image_comp]

/-- Hausdorff stability of continuous linear transport:
`dist (mapLinear f K) (mapLinear f L) ≤ ‖f‖ * dist K L`. -/
theorem dist_mapLinear_le (f : E →L[ℝ] F) (K L : ConvexBody E) :
    dist (mapLinear f K) (mapLinear f L) ≤ ‖f‖ * dist K L := by
  rw [← ConvexBody.hausdorffDist_coe, coe_mapLinear, coe_mapLinear]
  refine Metric.hausdorffDist_le_of_mem_dist (mul_nonneg (norm_nonneg f) dist_nonneg) ?_ ?_
  · rintro _ ⟨x, hxK, rfl⟩
    obtain ⟨y, hyL, hinf⟩ := L.isCompact.exists_infDist_eq_dist L.nonempty x
    refine ⟨f y, ⟨y, hyL, rfl⟩, ?_⟩
    have hxy : dist x y ≤ dist K L := by
      rw [← hinf]
      exact (Metric.infDist_le_hausdorffDist_of_mem hxK ConvexBody.hausdorffEDist_ne_top).trans
        (by rw [ConvexBody.hausdorffDist_coe])
    calc
      dist (f x) (f y) = ‖f (x - y)‖ := by rw [dist_eq_norm, ← map_sub]
      _ ≤ ‖f‖ * ‖x - y‖ := f.le_opNorm (x - y)
      _ = ‖f‖ * dist x y := by rw [dist_eq_norm]
      _ ≤ ‖f‖ * dist K L := mul_le_mul_of_nonneg_left hxy (norm_nonneg f)
  · rintro _ ⟨y, hyL, rfl⟩
    obtain ⟨x, hxK, hinf⟩ := K.isCompact.exists_infDist_eq_dist K.nonempty y
    refine ⟨f x, ⟨x, hxK, rfl⟩, ?_⟩
    have hyx : dist y x ≤ dist K L := by
      rw [← hinf]
      have hcomm : Metric.hausdorffDist (L : Set E) K = dist K L := by
        rw [Metric.hausdorffDist_comm, ConvexBody.hausdorffDist_coe]
      exact (Metric.infDist_le_hausdorffDist_of_mem hyL ConvexBody.hausdorffEDist_ne_top).trans
        hcomm.le
    calc
      dist (f y) (f x) = ‖f (y - x)‖ := by rw [dist_eq_norm, ← map_sub]
      _ ≤ ‖f‖ * ‖y - x‖ := f.le_opNorm (y - x)
      _ = ‖f‖ * dist y x := by rw [dist_eq_norm]
      _ ≤ ‖f‖ * dist K L := mul_le_mul_of_nonneg_left hyx (norm_nonneg f)

end Transport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A singleton `{a}` viewed as a `ConvexBody E`. -/
def bodySingleton (a : E) : ConvexBody E where
  carrier := {a}
  convex' := convex_singleton a
  isCompact' := isCompact_singleton
  nonempty' := Set.singleton_nonempty a

@[simp]
lemma coe_bodySingleton (a : E) : (bodySingleton a : Set E) = {a} := by
  simp [bodySingleton, ConvexBody.coe_mk]

/-- A closed ball `Metric.closedBall c r` (for `0 ≤ r`) viewed as a `ConvexBody E`
in a proper (e.g. finite-dimensional) inner product space. -/
def bodyClosedBall [ProperSpace E] (c : E) {r : ℝ} (hr : 0 ≤ r) : ConvexBody E where
  carrier := Metric.closedBall c r
  convex' := convex_closedBall c r
  isCompact' := isCompact_closedBall c r
  nonempty' := Metric.nonempty_closedBall.mpr hr

@[simp]
lemma coe_bodyClosedBall [ProperSpace E] (c : E) {r : ℝ} (hr : 0 ≤ r) :
    (bodyClosedBall c hr : Set E) = Metric.closedBall c r := by
  simp [bodyClosedBall, ConvexBody.coe_mk]

/-! ### 2. Support Function Definition and Calculus -/

/-- The support function of a convex body `K` in direction `u`:
`h_K(u) = sup { ⟪x, u⟫ | x ∈ K }`. -/
noncomputable def supportFn (K : ConvexBody E) (u : E) : ℝ :=
  sSup ((fun x : E => ⟪x, u⟫) '' (K : Set E))

lemma supportFn_image_nonempty (K : ConvexBody E) (u : E) :
    ((fun x : E => ⟪x, u⟫) '' (K : Set E)).Nonempty :=
  K.nonempty.image _

lemma supportFn_image_isCompact (K : ConvexBody E) (u : E) :
    IsCompact ((fun x : E => ⟪x, u⟫) '' (K : Set E)) :=
  K.isCompact.image (continuous_id.inner continuous_const)

lemma supportFn_bddAbove (K : ConvexBody E) (u : E) :
    BddAbove ((fun x : E => ⟪x, u⟫) '' (K : Set E)) :=
  (supportFn_image_isCompact K u).bddAbove

/-- Every point `x ∈ K` satisfies `⟪x, u⟫ ≤ supportFn K u`. -/
theorem inner_le_supportFn {K : ConvexBody E} {x : E} (hx : x ∈ K) (u : E) :
    ⟪x, u⟫ ≤ supportFn K u :=
  le_csSup (supportFn_bddAbove K u) ⟨x, hx, rfl⟩

/-- `supportFn K u ≤ c` if and only if every `x ∈ K` satisfies `⟪x, u⟫ ≤ c`. -/
theorem supportFn_le_iff {K : ConvexBody E} {u : E} {c : ℝ} :
    supportFn K u ≤ c ↔ ∀ x ∈ K, ⟪x, u⟫ ≤ c := by
  constructor
  · intro h x hx
    exact (inner_le_supportFn hx u).trans h
  · intro h
    refine csSup_le (supportFn_image_nonempty K u) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx

/-- Attainment: since `K` is compact and nonempty, the supremum is attained at some `x ∈ K`. -/
theorem exists_mem_supportFn_eq (K : ConvexBody E) (u : E) :
    ∃ x ∈ K, ⟪x, u⟫ = supportFn K u :=
  (supportFn_image_isCompact K u).sSup_mem (supportFn_image_nonempty K u)

@[simp]
theorem supportFn_zero (K : ConvexBody E) : supportFn K 0 = 0 := by
  apply le_antisymm
  · rw [supportFn_le_iff]
    intro x _
    simp
  · obtain ⟨x, hx⟩ := K.nonempty
    simpa using inner_le_supportFn hx (0 : E)

/-- Monotonicity: if `K ⊆ L`, then `h_K(u) ≤ h_L(u)`. -/
theorem supportFn_mono {K L : ConvexBody E} (hKL : (K : Set E) ⊆ L) (u : E) :
    supportFn K u ≤ supportFn L u := by
  rw [supportFn_le_iff]
  intro x hx
  exact inner_le_supportFn (hKL hx) u

/-- Positive homogeneity in the direction: `h_K(c • u) = c * h_K(u)` for `c ≥ 0`. -/
theorem supportFn_smul (K : ConvexBody E) {c : ℝ} (hc : 0 ≤ c) (u : E) :
    supportFn K (c • u) = c * supportFn K u := by
  apply le_antisymm
  · rw [supportFn_le_iff]
    intro x hx
    rw [inner_smul_right]
    exact mul_le_mul_of_nonneg_left (inner_le_supportFn hx u) hc
  · obtain ⟨x, hx, hxu⟩ := exists_mem_supportFn_eq K u
    calc
      c * supportFn K u = c * ⟪x, u⟫ := by rw [hxu]
      _ = ⟪x, c • u⟫ := by rw [inner_smul_right]
      _ ≤ supportFn K (c • u) := inner_le_supportFn hx (c • u)

/-- Subadditivity in the direction: `h_K(u + v) ≤ h_K(u) + h_K(v)`. -/
theorem supportFn_add_le (K : ConvexBody E) (u v : E) :
    supportFn K (u + v) ≤ supportFn K u + supportFn K v := by
  rw [supportFn_le_iff]
  intro x hx
  rw [inner_add_right]
  exact add_le_add (inner_le_supportFn hx u) (inner_le_supportFn hx v)

/-- Sublinearity on nonnegative combinations:
`h_K(a • u + b • v) ≤ a * h_K(u) + b * h_K(v)` for `a, b ≥ 0`. -/
theorem supportFn_convex_comb (K : ConvexBody E) (u v : E)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    supportFn K (a • u + b • v) ≤ a * supportFn K u + b * supportFn K v := by
  calc
    supportFn K (a • u + b • v)
      ≤ supportFn K (a • u) + supportFn K (b • v) := supportFn_add_le K (a • u) (b • v)
    _ = a * supportFn K u + b * supportFn K v := by
      rw [supportFn_smul K ha u, supportFn_smul K hb v]

/-- The support function of a convex body is convex on the entire space `E`. -/
theorem supportFn_convexOn (K : ConvexBody E) :
    ConvexOn ℝ Set.univ (supportFn K) := by
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb _
  simpa [smul_eq_mul] using supportFn_convex_comb K u v ha hb

/-- Minkowski additivity: `h_{K + L}(u) = h_K(u) + h_L(u)`. -/
theorem supportFn_minkowski_add (K L : ConvexBody E) (u : E) :
    supportFn (K + L) u = supportFn K u + supportFn L u := by
  apply le_antisymm
  · rw [supportFn_le_iff]
    intro x hx
    rw [← SetLike.mem_coe, ConvexBody.coe_add] at hx
    rcases Set.mem_add.mp hx with ⟨y, hy, z, hz, rfl⟩
    rw [inner_add_left]
    exact add_le_add (inner_le_supportFn hy u) (inner_le_supportFn hz u)
  · obtain ⟨y, hy, hyu⟩ := exists_mem_supportFn_eq K u
    obtain ⟨z, hz, hzu⟩ := exists_mem_supportFn_eq L u
    have hyz : y + z ∈ K + L := by
      rw [← SetLike.mem_coe, ConvexBody.coe_add]
      exact Set.add_mem_add hy hz
    calc
      supportFn K u + supportFn L u = ⟪y, u⟫ + ⟪z, u⟫ := by rw [hyu, hzu]
      _ = ⟪y + z, u⟫ := by rw [inner_add_left]
      _ ≤ supportFn (K + L) u := inner_le_supportFn hyz u

/-- Scaling of the convex body by a nonnegative scalar: `h_{c • K}(u) = c * h_K(u)`. -/
theorem supportFn_body_smul (K : ConvexBody E) {c : ℝ} (hc : 0 ≤ c) (u : E) :
    supportFn (c • K) u = c * supportFn K u := by
  apply le_antisymm
  · rw [supportFn_le_iff]
    intro x hx
    rw [← SetLike.mem_coe, ConvexBody.coe_smul] at hx
    rcases Set.mem_smul_set.mp hx with ⟨y, hy, rfl⟩
    rw [inner_smul_left]
    simpa using mul_le_mul_of_nonneg_left (inner_le_supportFn hy u) hc
  · obtain ⟨y, hy, hyu⟩ := exists_mem_supportFn_eq K u
    have hcy : c • y ∈ c • K := by
      rw [← SetLike.mem_coe, ConvexBody.coe_smul]
      exact Set.smul_mem_smul_set hy
    calc
      c * supportFn K u = c * ⟪y, u⟫ := by rw [hyu]
      _ = ⟪c • y, u⟫ := by simp [inner_smul_left]
      _ ≤ supportFn (c • K) u := inner_le_supportFn hcy u

/-- Negation of a convex body: `h_{(-1) • K}(u) = h_K(-u)`. -/
theorem supportFn_neg_one_smul (K : ConvexBody E) (u : E) :
    supportFn ((-1 : ℝ) • K) u = supportFn K (-u) := by
  apply le_antisymm
  · rw [supportFn_le_iff]
    intro x hx
    rw [← SetLike.mem_coe, ConvexBody.coe_smul] at hx
    rcases Set.mem_smul_set.mp hx with ⟨y, hy, rfl⟩
    simpa [inner_neg_left, inner_neg_right] using inner_le_supportFn hy (-u)
  · obtain ⟨y, hy, hyu⟩ := exists_mem_supportFn_eq K (-u)
    have hny : (-1 : ℝ) • y ∈ (-1 : ℝ) • K := by
      rw [← SetLike.mem_coe, ConvexBody.coe_smul]
      exact Set.smul_mem_smul_set hy
    calc
      supportFn K (-u) = ⟪y, -u⟫ := hyu.symm
      _ = ⟪(-1 : ℝ) • y, u⟫ := by simp [inner_neg_left, inner_neg_right]
      _ ≤ supportFn ((-1 : ℝ) • K) u := inner_le_supportFn hny u

/-- Scaling of a convex body by any real scalar `c : ℝ`:
`h_{c • K}(u) = h_K(c • u)`. -/
theorem supportFn_body_smul_eq (K : ConvexBody E) (c : ℝ) (u : E) :
    supportFn (c • K) u = supportFn K (c • u) := by
  rcases le_total 0 c with hc | hc
  · rw [supportFn_body_smul K hc, supportFn_smul K hc]
  · have hnc : 0 ≤ -c := neg_nonneg.mpr hc
    have h1 : c • K = (-c) • ((-1 : ℝ) • K) := by
      rw [smul_smul]; simp
    rw [h1, supportFn_body_smul _ hnc, supportFn_neg_one_smul, ← supportFn_smul K hnc]
    congr 1
    rw [smul_neg, neg_smul, neg_neg]

@[simp]
theorem supportFn_bodySingleton (a u : E) :
    supportFn (bodySingleton a) u = ⟪a, u⟫ := by
  apply le_antisymm
  · rw [supportFn_le_iff]
    intro x hx
    have : x = a := hx
    rw [this]
  · exact inner_le_supportFn (Set.mem_singleton a) u

/-- Support function of a closed ball: `h_{B(c, r)}(u) = ⟪c, u⟫ + r * ‖u‖`. -/
@[simp]
theorem supportFn_bodyClosedBall [ProperSpace E] (c : E) {r : ℝ} (hr : 0 ≤ r) (u : E) :
    supportFn (bodyClosedBall c hr) u = ⟪c, u⟫ + r * ‖u‖ := by
  apply le_antisymm
  · rw [supportFn_le_iff]
    intro x hx
    rw [← SetLike.mem_coe, coe_bodyClosedBall, Metric.mem_closedBall, dist_eq_norm] at hx
    have hcs : ⟪x - c, u⟫ ≤ r * ‖u‖ :=
      (real_inner_le_norm (x - c) u).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg u))
    have hsplit : ⟪x, u⟫ = ⟪c, u⟫ + ⟪x - c, u⟫ := by
      rw [inner_sub_left]; ring
    linarith
  · by_cases hu : u = 0
    · subst hu; simp
    · have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
      let x : E := c + (r / ‖u‖) • u
      have hx : x ∈ bodyClosedBall c hr := by
        rw [← SetLike.mem_coe, coe_bodyClosedBall, Metric.mem_closedBall, dist_eq_norm]
        simp only [x, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg hr hpos.le)]
        rw [div_mul_cancel₀ r hpos.ne']
      calc
        ⟪c, u⟫ + r * ‖u‖
          = ⟪c, u⟫ + (r / ‖u‖) * ‖u‖ ^ 2 := by
            field_simp [hpos.ne']
        _ = ⟪c, u⟫ + (r / ‖u‖) * ⟪u, u⟫ := by
            rw [real_inner_self_eq_norm_sq]
        _ = ⟪x, u⟫ := by
            simp [x, inner_add_left, inner_smul_left]
        _ ≤ supportFn (bodyClosedBall c hr) u := inner_le_supportFn hx u

/-- Support function of an isometric linear image `mapLinear U K`:
`h_{U(K)}(v) = h_K(U⁻¹ v)`. -/
theorem supportFn_mapLinearIsometry {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (U : E ≃ₗᵢ[ℝ] F) (K : ConvexBody E) (v : F) :
    supportFn (mapLinear U.toLinearIsometry.toContinuousLinearMap K) v = supportFn K (U.symm v) := by
  apply le_antisymm
  · rw [supportFn_le_iff]
    intro y hy
    rw [← SetLike.mem_coe, coe_mapLinear] at hy
    rcases hy with ⟨x, hx, rfl⟩
    have hinner : ⟪U.toLinearIsometry.toContinuousLinearMap x, v⟫ = ⟪x, U.symm v⟫ := by
      simpa using U.inner_map_map x (U.symm v)
    rw [hinner]
    exact inner_le_supportFn hx (U.symm v)
  · obtain ⟨x, hx, hxv⟩ := exists_mem_supportFn_eq K (U.symm v)
    have hmem : U.toLinearIsometry.toContinuousLinearMap x ∈
        mapLinear U.toLinearIsometry.toContinuousLinearMap K := by
      rw [← SetLike.mem_coe, coe_mapLinear]
      exact ⟨x, hx, rfl⟩
    have hinner : ⟪U.toLinearIsometry.toContinuousLinearMap x, v⟫ = ⟪x, U.symm v⟫ := by
      simpa using U.inner_map_map x (U.symm v)
    rw [← hxv, ← hinner]
    exact inner_le_supportFn hmem v

/-! ### 3. Separation, Injectivity, Lipschitz Continuity, and Width -/

/-- **Separation Theorem for Convex Bodies (in Hilbert spaces):**
`K ⊆ L` if and only if `supportFn K u ≤ supportFn L u` for all `u : E`. -/
theorem supportFn_le_iff_subset [CompleteSpace E] {K L : ConvexBody E} :
    (∀ u : E, supportFn K u ≤ supportFn L u) ↔ (K : Set E) ⊆ L := by
  constructor
  · intro h x hxK
    by_contra hxL
    obtain ⟨f, s, hLs, hfx⟩ :=
      geometric_hahn_banach_closed_point L.convex L.isClosed hxL
    let u : E := (InnerProductSpace.toDual ℝ E).symm f
    have hLu : supportFn L u ≤ s := by
      rw [supportFn_le_iff]
      intro y hy
      have : ⟪y, u⟫ = f y := by
        rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
      rw [this]
      exact (hLs y hy).le
    have hKu : s < ⟪x, u⟫ := by
      have : ⟪x, u⟫ = f x := by
        rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
      rwa [this]
    have hle : ⟪x, u⟫ ≤ supportFn L u := (inner_le_supportFn hxK u).trans (h u)
    linarith
  · intro h u
    exact supportFn_mono h u

/-- A convex body in a Hilbert space is uniquely determined by its support function. -/
theorem supportFn_injective [CompleteSpace E] :
    Function.Injective (supportFn (E := E)) := by
  intro K L h
  apply ConvexBody.ext
  apply Set.Subset.antisymm
  · exact supportFn_le_iff_subset.mp (fun u => (congrFun h u).le)
  · exact supportFn_le_iff_subset.mp (fun u => (congrFun h u).ge)

/-- **Halfspace Characterization of a Convex Body:**
in a Hilbert space, `x ∈ K ↔ ∀ u : E, ⟪x, u⟫ ≤ supportFn K u`. -/
theorem mem_iff_forall_inner_le_supportFn [CompleteSpace E] (K : ConvexBody E) (x : E) :
    x ∈ K ↔ ∀ u : E, ⟪x, u⟫ ≤ supportFn K u := by
  constructor
  · exact fun hx u => inner_le_supportFn hx u
  · intro h
    have hsub : (bodySingleton x : Set E) ⊆ K :=
      supportFn_le_iff_subset.mp fun u => by simpa [supportFn_bodySingleton] using h u
    exact hsub (by simp)

/-- Unit-ball halfspace characterization: `x ∈ K ↔ ∀ u, ‖u‖ ≤ 1 → ⟪x, u⟫ ≤ supportFn K u`. -/
theorem mem_iff_forall_norm_le_one_inner_le_supportFn [CompleteSpace E]
    (K : ConvexBody E) (x : E) :
    x ∈ K ↔ ∀ u : E, ‖u‖ ≤ 1 → ⟪x, u⟫ ≤ supportFn K u := by
  rw [mem_iff_forall_inner_le_supportFn]
  constructor
  · exact fun h u _ => h u
  · intro h u
    by_cases hu : u = 0
    · subst hu; simp
    · have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
      have hunit : ‖‖u‖⁻¹ • u‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hpos.le),
          inv_mul_cancel₀ hpos.ne']
      have h1 := h (‖u‖⁻¹ • u) hunit
      rw [inner_smul_right, supportFn_smul K (inv_nonneg.mpr hpos.le)] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
      rwa [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, one_mul] at h2

/-- If `K ⊆ closedBall 0 R`, then `|h_K(u)| ≤ R * ‖u‖`. -/
theorem abs_supportFn_le_of_subset_closedBall {K : ConvexBody E} {R : ℝ}
    (hKR : (K : Set E) ⊆ Metric.closedBall 0 R) (u : E) :
    |supportFn K u| ≤ R * ‖u‖ := by
  obtain ⟨x, hx, hxu⟩ := exists_mem_supportFn_eq K u
  have hxR : ‖x‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hKR hx
  rw [← hxu]
  exact (abs_real_inner_le_norm x u).trans (mul_le_mul_of_nonneg_right hxR (norm_nonneg u))

/-- If `K ⊆ closedBall 0 R`, then `supportFn K` is `R`-Lipschitz:
`|h_K(u) - h_K(v)| ≤ R * ‖u - v‖`. -/
theorem abs_supportFn_sub_le_of_subset_closedBall {K : ConvexBody E} {R : ℝ}
    (hKR : (K : Set E) ⊆ Metric.closedBall 0 R) (u v : E) :
    |supportFn K u - supportFn K v| ≤ R * ‖u - v‖ := by
  have h1 : supportFn K u - supportFn K v ≤ R * ‖u - v‖ := by
    have hadd := supportFn_add_le K v (u - v)
    rw [add_sub_cancel] at hadd
    have hbound := (le_abs_self _).trans (abs_supportFn_le_of_subset_closedBall hKR (u - v))
    linarith
  have h2 : supportFn K v - supportFn K u ≤ R * ‖u - v‖ := by
    have hadd := supportFn_add_le K u (v - u)
    rw [add_sub_cancel] at hadd
    have hbound := (le_abs_self _).trans (abs_supportFn_le_of_subset_closedBall hKR (v - u))
    rw [norm_sub_rev] at hbound
    linarith
  exact abs_sub_le_iff.mpr ⟨h1, h2⟩

/-- Every support function `supportFn K` is continuous on `E`. -/
theorem continuous_supportFn (K : ConvexBody E) : Continuous (supportFn K) := by
  obtain ⟨R, hKR⟩ := K.isBounded.subset_closedBall (0 : E)
  have hR0 : 0 ≤ R := by
    obtain ⟨x, hx⟩ := K.nonempty
    exact (norm_nonneg x).trans (by simpa [Metric.mem_closedBall, dist_eq_norm] using hKR hx)
  refine (LipschitzWith.of_dist_le_mul (K := ⟨R, hR0⟩) fun u v => ?_).continuous
  change |supportFn K u - supportFn K v| ≤ R * dist u v
  rw [dist_eq_norm]
  exact abs_supportFn_sub_le_of_subset_closedBall hKR u v

/-- Directional width of a convex body `K` in direction `u`:
`width K u = h_K(u) + h_K(-u) = h_{K - K}(u)`. -/
noncomputable def width (K : ConvexBody E) (u : E) : ℝ :=
  supportFn K u + supportFn K (-u)

theorem width_nonneg (K : ConvexBody E) (u : E) : 0 ≤ width K u := by
  have h := supportFn_add_le K u (-u)
  rw [add_neg_cancel, supportFn_zero] at h
  exact h

theorem width_eq_supportFn_diff (K : ConvexBody E) (u : E) :
    width K u = supportFn (K + (-1 : ℝ) • K) u := by
  rw [supportFn_minkowski_add, supportFn_neg_one_smul, width]

/-- For every `x, y ∈ K` and unit vector `u`, `⟪x - y, u⟫ ≤ width K u`. -/
theorem inner_sub_le_width {K : ConvexBody E} {x y : E} (hx : x ∈ K) (hy : y ∈ K) (u : E) :
    ⟪x - y, u⟫ ≤ width K u := by
  rw [inner_sub_left, width]
  have h1 := inner_le_supportFn hx u
  have h2 := inner_le_supportFn hy (-u)
  rw [inner_neg_right] at h2
  linarith

/-- The diameter of a convex body `K` equals the supremum of its directional widths on the
closed unit ball (see `diam_eq_sSup_width_sphere` for the unit sphere in nontrivial spaces). -/
theorem diam_eq_sSup_width (K : ConvexBody E) :
    Metric.diam (K : Set E) =
      sSup ((fun u : Metric.closedBall (0 : E) 1 => width K u) '' Set.univ) := by
  let u0 : Metric.closedBall (0 : E) 1 := ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  have hne_u : ((fun u : Metric.closedBall (0 : E) 1 => width K u) '' Set.univ).Nonempty :=
    ⟨width K u0, ⟨u0, Set.mem_univ _, rfl⟩⟩
  have hbdd : BddAbove ((fun u : Metric.closedBall (0 : E) 1 => width K u) '' Set.univ) := by
    refine ⟨Metric.diam (K : Set E), ?_⟩
    rintro _ ⟨⟨u, hu⟩, _, rfl⟩
    obtain ⟨x, hx, hxu⟩ := exists_mem_supportFn_eq K u
    obtain ⟨y, hy, hyu⟩ := exists_mem_supportFn_eq K (-u)
    have hu1 : ‖u‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hu
    have hxy : ‖x - y‖ ≤ Metric.diam (K : Set E) := by
      simpa [dist_eq_norm] using Metric.dist_le_diam_of_mem K.isBounded hx hy
    calc
      width K u = ⟪x, u⟫ + ⟪y, -u⟫ := by rw [width, hxu, hyu]
      _ = ⟪x - y, u⟫ := by rw [inner_sub_left, inner_neg_right]; ring
      _ ≤ ‖x - y‖ * ‖u‖ := real_inner_le_norm _ _
      _ ≤ ‖x - y‖ * 1 := mul_le_mul_of_nonneg_left hu1 (norm_nonneg _)
      _ = ‖x - y‖ := mul_one _
      _ ≤ Metric.diam (K : Set E) := hxy
  apply le_antisymm
  · refine Metric.diam_le_of_forall_dist_le (le_csSup_of_le hbdd ⟨⟨0, Metric.mem_closedBall_self zero_le_one⟩, Set.mem_univ _, rfl⟩ (width_nonneg K 0)) ?_
    intro x hx y hy
    by_cases hxy : x = y
    · subst hxy
      simpa using le_csSup_of_le hbdd
        ⟨⟨0, Metric.mem_closedBall_self zero_le_one⟩, Set.mem_univ _, rfl⟩ (width_nonneg K 0)
    · have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      let u : E := (‖x - y‖⁻¹) • (x - y)
      have hu : u ∈ Metric.closedBall (0 : E) 1 := by
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr hpos.le), inv_mul_cancel₀ hpos.ne']
      have hnorm : dist x y = ⟪x - y, u⟫ := by
        rw [dist_eq_norm, inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp [hpos.ne']
      rw [hnorm]
      exact (inner_sub_le_width hx hy u).trans
        (le_csSup hbdd ⟨⟨u, hu⟩, Set.mem_univ _, rfl⟩)
  · refine csSup_le hne_u ?_
    rintro _ ⟨⟨u, hu⟩, _, rfl⟩
    obtain ⟨x, hx, hxu⟩ := exists_mem_supportFn_eq K u
    obtain ⟨y, hy, hyu⟩ := exists_mem_supportFn_eq K (-u)
    have hu1 : ‖u‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hu
    have hxy : ‖x - y‖ ≤ Metric.diam (K : Set E) := by
      simpa [dist_eq_norm] using Metric.dist_le_diam_of_mem K.isBounded hx hy
    calc
      width K u = ⟪x, u⟫ + ⟪y, -u⟫ := by rw [width, hxu, hyu]
      _ = ⟪x - y, u⟫ := by rw [inner_sub_left, inner_neg_right]; ring
      _ ≤ ‖x - y‖ * ‖u‖ := real_inner_le_norm _ _
      _ ≤ ‖x - y‖ * 1 := mul_le_mul_of_nonneg_left hu1 (norm_nonneg _)
      _ = ‖x - y‖ := mul_one _
      _ ≤ Metric.diam (K : Set E) := hxy

/-- In a nontrivial inner product space, the diameter of `K` equals the supremum of its
directional widths over the unit sphere `Metric.sphere 0 1`. -/
theorem diam_eq_sSup_width_sphere [Nontrivial E] (K : ConvexBody E) :
    Metric.diam (K : Set E) =
      sSup ((fun u : Metric.sphere (0 : E) 1 => width K u.1) '' Set.univ) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u₀ : Metric.sphere (0 : E) 1 := ⟨‖v‖⁻¹ • v, by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hv_pos.le), inv_mul_cancel₀ hv_pos.ne']⟩
  have hne : ((fun u : Metric.sphere (0 : E) 1 => width K u.1) '' Set.univ).Nonempty :=
    ⟨width K u₀.1, ⟨u₀, Set.mem_univ _, rfl⟩⟩
  have hbdd : BddAbove ((fun u : Metric.sphere (0 : E) 1 => width K u.1) '' Set.univ) := by
    refine ⟨Metric.diam (K : Set E), ?_⟩
    rintro _ ⟨⟨u, hu⟩, _, rfl⟩
    obtain ⟨x, hx, hxu⟩ := exists_mem_supportFn_eq K u
    obtain ⟨y, hy, hyu⟩ := exists_mem_supportFn_eq K (-u)
    have hu1 : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp hu
    have hxy : ‖x - y‖ ≤ Metric.diam (K : Set E) := by
      simpa [dist_eq_norm] using Metric.dist_le_diam_of_mem K.isBounded hx hy
    calc
      width K u = ⟪x - y, u⟫ := by rw [width, ← hxu, ← hyu, inner_sub_left, inner_neg_right]; ring
      _ ≤ ‖x - y‖ * ‖u‖ := real_inner_le_norm _ _
      _ = ‖x - y‖ := by rw [hu1, mul_one]
      _ ≤ Metric.diam (K : Set E) := hxy
  apply le_antisymm
  · refine Metric.diam_le_of_forall_dist_le
      (le_csSup_of_le hbdd ⟨u₀, Set.mem_univ _, rfl⟩ (width_nonneg K u₀.1)) ?_
    intro x hx y hy
    by_cases hxy : x = y
    · subst hxy
      simpa using le_csSup_of_le hbdd ⟨u₀, Set.mem_univ _, rfl⟩ (width_nonneg K u₀.1)
    · have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      let u : Metric.sphere (0 : E) 1 := ⟨‖x - y‖⁻¹ • (x - y), by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr hpos.le), inv_mul_cancel₀ hpos.ne']⟩
      have hnorm : dist x y = ⟪x - y, u.1⟫ := by
        rw [dist_eq_norm, inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp [hpos.ne']
      rw [hnorm]
      exact (inner_sub_le_width hx hy u.1).trans (le_csSup hbdd ⟨u, Set.mem_univ _, rfl⟩)
  · refine csSup_le hne ?_
    rintro _ ⟨⟨u, hu⟩, _, rfl⟩
    obtain ⟨x, hx, hxu⟩ := exists_mem_supportFn_eq K u
    obtain ⟨y, hy, hyu⟩ := exists_mem_supportFn_eq K (-u)
    have hu1 : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp hu
    have hxy : ‖x - y‖ ≤ Metric.diam (K : Set E) := by
      simpa [dist_eq_norm] using Metric.dist_le_diam_of_mem K.isBounded hx hy
    calc
      width K u = ⟪x - y, u⟫ := by rw [width, ← hxu, ← hyu, inner_sub_left, inner_neg_right]; ring
      _ ≤ ‖x - y‖ * ‖u‖ := real_inner_le_norm _ _
      _ = ‖x - y‖ := by rw [hu1, mul_one]
      _ ≤ Metric.diam (K : Set E) := hxy

/-! ### 4. Hörmander's Isometric Embedding & Hausdorff Metric Algebra -/

/-- The support function restricted to the closed unit ball as a bounded continuous function. -/
noncomputable def supportFnOnBall [ProperSpace E] (K : ConvexBody E) :
    Metric.closedBall (0 : E) 1 →ᵇ ℝ :=
  haveI : CompactSpace (Metric.closedBall (0 : E) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E) 1)
  BoundedContinuousFunction.mkOfCompact
    ⟨fun u => supportFn K u.1, (continuous_supportFn K).comp continuous_subtype_val⟩

@[simp]
lemma supportFnOnBall_apply [ProperSpace E] (K : ConvexBody E) (u : Metric.closedBall (0 : E) 1) :
    supportFnOnBall K u = supportFn K u.1 := by
  simp [supportFnOnBall]

/-- Auxiliary characterization: `dist K L ≤ r` iff `|h_K(u) - h_L(u)| ≤ r` for all `‖u‖ ≤ 1`. -/
theorem dist_le_iff_supportFn_sub_le [FiniteDimensional ℝ E] {K L : ConvexBody E}
    {r : ℝ} (hr : 0 ≤ r) :
    dist K L ≤ r ↔ ∀ u : E, ‖u‖ ≤ 1 → |supportFn K u - supportFn L u| ≤ r := by
  constructor
  · intro hdist u hu1
    have h1 : supportFn K u - supportFn L u ≤ r := by
      obtain ⟨x, hxK, hxu⟩ := exists_mem_supportFn_eq K u
      obtain ⟨y, hyL, hinf⟩ := L.isCompact.exists_infDist_eq_dist L.nonempty x
      have hxy : dist x y ≤ r := by
        rw [← hinf]
        exact (Metric.infDist_le_hausdorffDist_of_mem hxK ConvexBody.hausdorffEDist_ne_top).trans
          (by rwa [ConvexBody.hausdorffDist_coe])
      have hyu : ⟪y, u⟫ ≤ supportFn L u := inner_le_supportFn hyL u
      have hcs : ⟪x - y, u⟫ ≤ r := by
        calc
          ⟪x - y, u⟫ ≤ ‖x - y‖ * ‖u‖ := real_inner_le_norm _ _
          _ = dist x y * ‖u‖ := by rw [dist_eq_norm]
          _ ≤ r * 1 := mul_le_mul hxy hu1 (norm_nonneg u) hr
          _ = r := mul_one r
      have hsplit : ⟪x, u⟫ - ⟪y, u⟫ = ⟪x - y, u⟫ := (inner_sub_left x y u).symm
      linarith
    have h2 : supportFn L u - supportFn K u ≤ r := by
      obtain ⟨y, hyL, hyu⟩ := exists_mem_supportFn_eq L u
      obtain ⟨x, hxK, hinf⟩ := K.isCompact.exists_infDist_eq_dist K.nonempty y
      have hyx : dist y x ≤ r := by
        rw [← hinf]
        have hcomm : Metric.hausdorffDist (L : Set E) K ≤ r := by
          rw [Metric.hausdorffDist_comm, ConvexBody.hausdorffDist_coe]; exact hdist
        exact (Metric.infDist_le_hausdorffDist_of_mem hyL ConvexBody.hausdorffEDist_ne_top).trans
          hcomm
      have hxu : ⟪x, u⟫ ≤ supportFn K u := inner_le_supportFn hxK u
      have hcs : ⟪y - x, u⟫ ≤ r := by
        calc
          ⟪y - x, u⟫ ≤ ‖y - x‖ * ‖u‖ := real_inner_le_norm _ _
          _ = dist y x * ‖u‖ := by rw [dist_eq_norm]
          _ ≤ r * 1 := mul_le_mul hyx hu1 (norm_nonneg u) hr
          _ = r := mul_one r
      have hsplit : ⟪y, u⟫ - ⟪x, u⟫ = ⟪y - x, u⟫ := (inner_sub_left y x u).symm
      linarith
    exact abs_sub_le_iff.mpr ⟨h1, h2⟩
  · intro hsup
    -- Show `K ⊆ L + closedBall 0 r` and `L ⊆ K + closedBall 0 r` via support function separation!
    have hscale : ∀ u : E, |supportFn K u - supportFn L u| ≤ r * ‖u‖ := by
      intro u
      by_cases hu : u = 0
      · subst hu; simp
      · have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
        have hunit : ‖‖u‖⁻¹ • u‖ ≤ 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hpos.le),
            inv_mul_cancel₀ hpos.ne']
        have h0 := hsup (‖u‖⁻¹ • u) hunit
        rw [supportFn_smul K (inv_nonneg.mpr hpos.le),
          supportFn_smul L (inv_nonneg.mpr hpos.le), ← mul_sub, abs_mul,
          abs_of_nonneg (inv_nonneg.mpr hpos.le)] at h0
        have := mul_le_mul_of_nonneg_left h0 hpos.le
        rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, mul_comm] at this
    have hKL : (K : Set E) ⊆ (L + bodyClosedBall (0 : E) hr : ConvexBody E) := by
      refine supportFn_le_iff_subset.mp fun u => ?_
      rw [supportFn_minkowski_add, supportFn_bodyClosedBall, inner_zero_left, zero_add]
      have := (le_abs_self _).trans (hscale u)
      linarith
    have hLK : (L : Set E) ⊆ (K + bodyClosedBall (0 : E) hr : ConvexBody E) := by
      refine supportFn_le_iff_subset.mp fun u => ?_
      rw [supportFn_minkowski_add, supportFn_bodyClosedBall, inner_zero_left, zero_add]
      have := (neg_le_abs _).trans (hscale u)
      linarith
    rw [← ConvexBody.hausdorffDist_coe]
    refine Metric.hausdorffDist_le_of_mem_dist hr ?_ ?_
    · intro x hx
      have hx' : x ∈ (L : Set E) + Metric.closedBall (0 : E) r := by
        simpa [ConvexBody.coe_add] using hKL hx
      rcases Set.mem_add.mp hx' with ⟨y, hyL, z, hz, rfl⟩
      refine ⟨y, hyL, ?_⟩
      simpa [dist_eq_norm] using hz
    · intro y hy
      have hy' : y ∈ (K : Set E) + Metric.closedBall (0 : E) r := by
        simpa [ConvexBody.coe_add] using hLK hy
      rcases Set.mem_add.mp hy' with ⟨x, hxK, z, hz, rfl⟩
      refine ⟨x, hxK, ?_⟩
      simpa [dist_eq_norm] using hz

/-- Unit-sphere form of Hausdorff distance characterization:
`dist K L ≤ r` iff `|h_K(u) - h_L(u)| ≤ r` for all unit vectors `‖u‖ = 1`. -/
theorem dist_le_iff_supportFn_sub_le_sphere [FiniteDimensional ℝ E] {K L : ConvexBody E}
    {r : ℝ} (hr : 0 ≤ r) :
    dist K L ≤ r ↔ ∀ u : E, ‖u‖ = 1 → |supportFn K u - supportFn L u| ≤ r := by
  rw [dist_le_iff_supportFn_sub_le hr]
  constructor
  · exact fun h u hu => h u hu.le
  · intro h u hu1
    by_cases hu0 : u = 0
    · subst hu0; simpa using hr
    · have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
      have hunit : ‖‖u‖⁻¹ • u‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hpos.le),
          inv_mul_cancel₀ hpos.ne']
      have h1 := h (‖u‖⁻¹ • u) hunit
      rw [supportFn_smul K (inv_nonneg.mpr hpos.le),
        supportFn_smul L (inv_nonneg.mpr hpos.le), ← mul_sub, abs_mul,
        abs_of_nonneg (inv_nonneg.mpr hpos.le)] at h1
      calc
        |supportFn K u - supportFn L u|
          = ‖u‖ * (‖u‖⁻¹ * |supportFn K u - supportFn L u|) := by
              rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
        _ ≤ 1 * r := mul_le_mul hu1 h1 (by positivity) zero_le_one
        _ = r := one_mul r

/-- **Hörmander's Isometric Embedding Theorem:**
The map `K ↦ supportFnOnBall K` is an isometry from `ConvexBody E` (with the Hausdorff metric)
into `Metric.closedBall (0 : E) 1 →ᵇ ℝ` (with the supremum norm). -/
theorem isometry_supportFnOnBall [FiniteDimensional ℝ E] :
    Isometry (supportFnOnBall (E := E)) := by
  refine Isometry.of_dist_eq fun K L => ?_
  apply le_antisymm
  · rw [BoundedContinuousFunction.dist_le dist_nonneg]
    intro ⟨u, hu⟩
    have hu1 : ‖u‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hu
    simpa [Real.dist_eq] using (dist_le_iff_supportFn_sub_le dist_nonneg).mp le_rfl u hu1
  · rw [dist_le_iff_supportFn_sub_le dist_nonneg]
    intro u hu1
    have hu : u ∈ Metric.closedBall (0 : E) 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hu1
    simpa [Real.dist_eq] using
      BoundedContinuousFunction.dist_coe_le_dist (f := supportFnOnBall K) (g := supportFnOnBall L)
        ⟨u, hu⟩

/-- **Hörmander's Distance Formula:**
`dist K L = dist (supportFnOnBall K) (supportFnOnBall L)`. -/
theorem dist_eq_dist_supportFnOnBall [FiniteDimensional ℝ E] (K L : ConvexBody E) :
    dist K L = dist (supportFnOnBall K) (supportFnOnBall L) :=
  (isometry_supportFnOnBall.dist_eq K L).symm

/-- Cancellation / translation invariance of the Hausdorff metric under Minkowski addition:
`dist (K + M) (L + M) = dist K L`. -/
theorem dist_add_right [FiniteDimensional ℝ E] (K L M : ConvexBody E) :
    dist (K + M) (L + M) = dist K L := by
  apply le_antisymm
  · rw [dist_le_iff_supportFn_sub_le dist_nonneg]
    intro u hu1
    rw [supportFn_minkowski_add, supportFn_minkowski_add]
    have hsub : supportFn K u + supportFn M u - (supportFn L u + supportFn M u) =
        supportFn K u - supportFn L u := by ring
    rw [hsub]
    exact (dist_le_iff_supportFn_sub_le dist_nonneg).mp le_rfl u hu1
  · rw [dist_le_iff_supportFn_sub_le dist_nonneg]
    intro u hu1
    have h := (dist_le_iff_supportFn_sub_le dist_nonneg (K := K + M) (L := L + M)).mp le_rfl u hu1
    rw [supportFn_minkowski_add, supportFn_minkowski_add] at h
    have hsub : supportFn K u + supportFn M u - (supportFn L u + supportFn M u) =
        supportFn K u - supportFn L u := by ring
    rwa [hsub] at h

/-- Nonexpansiveness of Minkowski addition in the Hausdorff metric:
`dist (K₁ + K₂) (L₁ + L₂) ≤ dist K₁ L₁ + dist K₂ L₂`. -/
theorem dist_add_le [FiniteDimensional ℝ E] (K₁ K₂ L₁ L₂ : ConvexBody E) :
    dist (K₁ + K₂) (L₁ + L₂) ≤ dist K₁ L₁ + dist K₂ L₂ := by
  calc
    dist (K₁ + K₂) (L₁ + L₂)
      ≤ dist (K₁ + K₂) (L₁ + K₂) + dist (L₁ + K₂) (L₁ + L₂) := dist_triangle _ _ _
    _ = dist K₁ L₁ + dist K₂ L₂ := by
        rw [dist_add_right, add_comm L₁ K₂, add_comm L₁ L₂, dist_add_right]

/-- Scaling law of the Hausdorff metric on `ConvexBody E`:
`dist (c • K) (c • L) = |c| * dist K L`. -/
theorem dist_smul [FiniteDimensional ℝ E] (c : ℝ) (K L : ConvexBody E) :
    dist (c • K) (c • L) = |c| * dist K L := by
  by_cases hc : c = 0
  · subst hc
    have h0 : ∀ M : ConvexBody E, (0 : ℝ) • M = 0 := fun M => by
      apply ConvexBody.ext
      rw [ConvexBody.coe_smul, ConvexBody.coe_zero, Set.zero_smul_set M.nonempty]
    simp [h0]
  · have hpos : 0 < |c| := abs_pos.mpr hc
    apply le_antisymm
    · rw [dist_le_iff_supportFn_sub_le (mul_nonneg hpos.le dist_nonneg)]
      intro u hu1
      rw [supportFn_body_smul_eq, supportFn_body_smul_eq]
      have hscale : ∀ v : E, |supportFn K v - supportFn L v| ≤ dist K L * ‖v‖ := fun v => by
        by_cases hv : v = 0
        · subst hv; simp
        · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
          have hunit : ‖‖v‖⁻¹ • v‖ ≤ 1 := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hvpos.le),
              inv_mul_cancel₀ hvpos.ne']
          have h0 := (dist_le_iff_supportFn_sub_le dist_nonneg (K := K) (L := L)).mp le_rfl _ hunit
          rw [supportFn_smul K (inv_nonneg.mpr hvpos.le),
            supportFn_smul L (inv_nonneg.mpr hvpos.le), ← mul_sub, abs_mul,
            abs_of_nonneg (inv_nonneg.mpr hvpos.le)] at h0
          have := mul_le_mul_of_nonneg_left h0 hvpos.le
          rwa [← mul_assoc, mul_inv_cancel₀ hvpos.ne', one_mul, mul_comm] at this
      calc
        |supportFn K (c • u) - supportFn L (c • u)|
          ≤ dist K L * ‖c • u‖ := hscale (c • u)
        _ = dist K L * (|c| * ‖u‖) := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ dist K L * (|c| * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu1 hpos.le) dist_nonneg
        _ = |c| * dist K L := by ring
    · have hle : dist K L ≤ |c|⁻¹ * dist (c • K) (c • L) := by
        rw [dist_le_iff_supportFn_sub_le (mul_nonneg (inv_nonneg.mpr hpos.le) dist_nonneg)]
        intro u hu1
        have hcu : ‖(c⁻¹ • u)‖ ≤ |c|⁻¹ := by
          rw [norm_smul, Real.norm_eq_abs, abs_inv]
          exact (mul_le_mul_of_nonneg_left hu1 (inv_nonneg.mpr hpos.le)).trans (by simp)
        have h1 : ‖(|c| • (c⁻¹ • u))‖ ≤ 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_abs]
          exact (mul_le_mul_of_nonneg_left hcu hpos.le).trans (by rw [mul_inv_cancel₀ hpos.ne'])
        have h0 := (dist_le_iff_supportFn_sub_le dist_nonneg
          (K := c • K) (L := c • L)).mp le_rfl (|c| • (c⁻¹ • u)) h1
        rw [supportFn_body_smul_eq, supportFn_body_smul_eq] at h0
        have hsimp : c • (|c| • (c⁻¹ • u)) = |c| • u := by
          rw [smul_smul, smul_smul, mul_comm c |c|, mul_assoc, mul_inv_cancel₀ hc, mul_one]
        rw [hsimp, supportFn_smul K hpos.le, supportFn_smul L hpos.le, ← mul_sub, abs_mul,
          abs_of_nonneg hpos.le] at h0
        have := mul_le_mul_of_nonneg_left h0 (inv_nonneg.mpr hpos.le)
        rwa [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul] at this
      have := mul_le_mul_of_nonneg_left hle hpos.le
      rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at this

/-! ### 5. Minkowski's Representation Theorem -/

/-- Every positively homogeneous subadditive function on a finite-dimensional real inner product
space is bounded above by `C * ‖u‖` for some constant `C ≥ 0`. -/
lemma sublinear_bounded_of_finiteDimensional [FiniteDimensional ℝ E] (h : E → ℝ)
    (h_hom : ∀ c : ℝ, 0 ≤ c → ∀ u, h (c • u) = c * h u)
    (h_add : ∀ u v, h (u + v) ≤ h u + h v) :
    ∃ C ≥ 0, ∀ u : E, h u ≤ C * ‖u‖ := by
  let b := stdOrthonormalBasis ℝ E
  let M : Fin (Module.finrank ℝ E) → ℝ := fun i => max (h (b i)) (h (-(b i)))
  have hM_nonneg : ∀ i, 0 ≤ M i := fun i => by
    have h0 : h 0 = 0 := by simpa using h_hom 0 le_rfl 0
    have hsum : 0 ≤ h (b i) + h (-(b i)) := by
      have := h_add (b i) (-(b i))
      rwa [add_neg_cancel, h0] at this
    by_contra hlt
    push Not at hlt
    have h1 : h (b i) < 0 := lt_of_le_of_lt (le_max_left _ _) hlt
    have h2 : h (-(b i)) < 0 := lt_of_le_of_lt (le_max_right _ _) hlt
    linarith
  refine ⟨∑ i, M i, Finset.sum_nonneg fun i _ => hM_nonneg i, fun u => ?_⟩
  have hrepr : u = ∑ i, ⟪b i, u⟫ • b i := (b.sum_repr' u).symm
  have hsum_le : ∀ (s : Finset (Fin (Module.finrank ℝ E))) (f : Fin (Module.finrank ℝ E) → E),
      h (∑ i ∈ s, f i) ≤ ∑ i ∈ s, h (f i) := by
    intro s f
    classical
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      have h0 : h 0 = 0 := by simpa using h_hom 0 le_rfl 0
      linarith
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (h_add _ _).trans (add_le_add le_rfl ih)
  calc
    h u = h (∑ i, ⟪b i, u⟫ • b i) := by rw [← hrepr]
    _ ≤ ∑ i, h (⟪b i, u⟫ • b i) := hsum_le _ _
    _ ≤ ∑ i, M i * ‖u‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hcs : |⟪b i, u⟫| ≤ ‖u‖ := by
          have := abs_real_inner_le_norm (b i) u
          rwa [b.orthonormal.1 i, one_mul] at this
        rcases le_total 0 ⟪b i, u⟫ with hc | hc
        · rw [h_hom _ hc]
          calc
            ⟪b i, u⟫ * h (b i) ≤ ⟪b i, u⟫ * M i :=
              mul_le_mul_of_nonneg_left (le_max_left _ _) hc
            _ = M i * |⟪b i, u⟫| := by rw [abs_of_nonneg hc, mul_comm]
            _ ≤ M i * ‖u‖ := mul_le_mul_of_nonneg_left hcs (hM_nonneg i)
        · have hnc : 0 ≤ -⟪b i, u⟫ := neg_nonneg.mpr hc
          have heq : ⟪b i, u⟫ • b i = (-⟪b i, u⟫) • (-(b i)) := by
            rw [smul_neg, neg_smul, neg_neg]
          rw [heq, h_hom _ hnc]
          calc
            (-⟪b i, u⟫) * h (-(b i)) ≤ (-⟪b i, u⟫) * M i :=
              mul_le_mul_of_nonneg_left (le_max_right _ _) hnc
            _ = M i * |⟪b i, u⟫| := by rw [abs_of_nonpos hc, mul_comm]
            _ ≤ M i * ‖u‖ := mul_le_mul_of_nonneg_left hcs (hM_nonneg i)
    _ = (∑ i, M i) * ‖u‖ := (Finset.sum_mul _ _ _).symm

/-- Helper: every direction `u₀ : E` admits a supporting point `x` in the halfspace intersection
`{x | ∀ u, ⟪x, u⟫ ≤ h u}` attaining `⟪x, u₀⟫ = h u₀` (Hahn–Banach extension). -/
private lemma exists_supporting_point_of_sublinear [FiniteDimensional ℝ E] (h : E → ℝ)
    (h_hom : ∀ c : ℝ, 0 ≤ c → ∀ u, h (c • u) = c * h u)
    (h_add : ∀ u v, h (u + v) ≤ h u + h v) (u₀ : E) :
    ∃ x : E, (∀ u, ⟪x, u⟫ ≤ h u) ∧ ⟪x, u₀⟫ = h u₀ := by
  have h0 : h 0 = 0 := by simpa using h_hom 0 le_rfl 0
  by_cases hu0 : u₀ = 0
  · let f0 : E →ₗ.[ℝ] ℝ := { domain := ⊥, toFun := 0 }
    obtain ⟨g, _, hgle⟩ := exists_extension_of_le_sublinear f0 h
      (fun c hc => h_hom c hc.le) h_add (fun x => by
        have hx0 : (x : E) = 0 := x.2
        simp [f0, hx0, h0])
    let gC : StrongDual ℝ E := ⟨g, g.continuous_of_finiteDimensional⟩
    let x : E := (InnerProductSpace.toDual ℝ E).symm gC
    refine ⟨x, fun u => ?_, by subst hu0; simp [h0]⟩
    have hx : ⟪x, u⟫ = g u := InnerProductSpace.toDual_symm_apply
    rw [hx]; exact hgle u
  · let p : Submodule ℝ E := Submodule.span ℝ {u₀}
    let f : E →ₗ.[ℝ] ℝ :=
      { domain := p
        toFun :=
          { toFun := fun v => (⟪v.1, u₀⟫ / ‖u₀‖ ^ 2) * h u₀
            map_add' := fun v w => by
              simp only [Submodule.coe_add, inner_add_left, add_div, add_mul]
            map_smul' := fun c v => by
              simp only [SetLike.val_smul, inner_smul_left, RCLike.conj_to_real,
                RingHom.id_apply, smul_eq_mul]
              ring } }
    have hf_le : ∀ v : f.domain, f v ≤ h v.1 := by
      rintro ⟨v, hv⟩
      rcases Submodule.mem_span_singleton.mp hv with ⟨t, rfl⟩
      have hnorm : ‖u₀‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hu0)
      have hcoeff : ⟪t • u₀, u₀⟫ / ‖u₀‖ ^ 2 = t := by
        rw [inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq]
        field_simp [hnorm]
      change (⟪t • u₀, u₀⟫ / ‖u₀‖ ^ 2) * h u₀ ≤ h (t • u₀)
      rw [hcoeff]
      rcases le_total 0 t with ht | ht
      · rw [h_hom t ht]
      · have hnt : 0 ≤ -t := neg_nonneg.mpr ht
        have hsum : 0 ≤ h u₀ + h (-u₀) := by
          have := h_add u₀ (-u₀)
          rwa [add_neg_cancel, h0] at this
        have hneg : h (t • u₀) = (-t) * h (-u₀) := by
          have : t • u₀ = (-t) • (-u₀) := by rw [smul_neg, neg_smul, neg_neg]
          rw [this, h_hom (-t) hnt]
        rw [hneg]; nlinarith
    obtain ⟨g, hgeq, hgle⟩ := exists_extension_of_le_sublinear f h
      (fun c hc => h_hom c hc.le) h_add hf_le
    let gC : StrongDual ℝ E := ⟨g, g.continuous_of_finiteDimensional⟩
    let x : E := (InnerProductSpace.toDual ℝ E).symm gC
    refine ⟨x, fun u => ?_, ?_⟩
    · have hx : ⟪x, u⟫ = g u := InnerProductSpace.toDual_symm_apply
      rw [hx]; exact hgle u
    · have hx : ⟪x, u₀⟫ = g u₀ := InnerProductSpace.toDual_symm_apply
      have hu_mem : u₀ ∈ f.domain := Submodule.subset_span (Set.mem_singleton u₀)
      rw [hx, hgeq ⟨u₀, hu_mem⟩]
      have hnorm : ‖u₀‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hu0)
      change (⟪u₀, u₀⟫ / ‖u₀‖ ^ 2) * h u₀ = h u₀
      rw [real_inner_self_eq_norm_sq, div_self hnorm, one_mul]

/-- Constructive Minkowski body associated to a positively 1-homogeneous subadditive function `h`:
the halfspace intersection `{x | ∀ u, ⟪x, u⟫ ≤ h u}` packaged as a `ConvexBody E`. -/
noncomputable def bodyOfSupportFn [FiniteDimensional ℝ E] (h : E → ℝ)
    (h_hom : ∀ c : ℝ, 0 ≤ c → ∀ u, h (c • u) = c * h u)
    (h_add : ∀ u v, h (u + v) ≤ h u + h v) : ConvexBody E where
  carrier := {x | ∀ u, ⟪x, u⟫ ≤ h u}
  convex' := by
    intro x hx y hy a b ha hb hab u
    rw [inner_add_left, inner_smul_left, inner_smul_left]
    simp only [RCLike.conj_to_real]
    calc
      a * ⟪x, u⟫ + b * ⟪y, u⟫
        ≤ a * h u + b * h u := add_le_add (mul_le_mul_of_nonneg_left (hx u) ha)
            (mul_le_mul_of_nonneg_left (hy u) hb)
      _ = (a + b) * h u := by ring
      _ = h u := by rw [hab, one_mul]
  isCompact' := by
    have hclosed : IsClosed {x : E | ∀ u, ⟪x, u⟫ ≤ h u} := by
      have heq : {x : E | ∀ u, ⟪x, u⟫ ≤ h u} = ⋂ u : E, {x : E | ⟪x, u⟫ ≤ h u} := by
        ext x; simp
      rw [heq]
      exact isClosed_iInter fun u => isClosed_le (continuous_id.inner continuous_const) continuous_const
    obtain ⟨C, hC0, hC⟩ := sublinear_bounded_of_finiteDimensional h h_hom h_add
    have hsub : {x : E | ∀ u, ⟪x, u⟫ ≤ h u} ⊆ Metric.closedBall 0 C := by
      intro x hx
      rw [Metric.mem_closedBall, dist_zero_right]
      by_cases hx0 : x = 0
      · simpa [hx0] using hC0
      · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
        have hxx : ‖x‖ ^ 2 ≤ C * ‖x‖ := by
          rw [← real_inner_self_eq_norm_sq]
          exact (hx x).trans (hC x)
        nlinarith
    exact (isCompact_closedBall (0 : E) C).of_isClosed_subset hclosed hsub
  nonempty' := by
    obtain ⟨x, hx, _⟩ := exists_supporting_point_of_sublinear h h_hom h_add 0
    exact ⟨x, hx⟩

@[simp]
lemma coe_bodyOfSupportFn [FiniteDimensional ℝ E] (h : E → ℝ)
    (h_hom : ∀ c : ℝ, 0 ≤ c → ∀ u, h (c • u) = c * h u)
    (h_add : ∀ u v, h (u + v) ≤ h u + h v) :
    (bodyOfSupportFn h h_hom h_add : Set E) = {x | ∀ u, ⟪x, u⟫ ≤ h u} := by
  rfl

@[simp]
theorem supportFn_bodyOfSupportFn [FiniteDimensional ℝ E] (h : E → ℝ)
    (h_hom : ∀ c : ℝ, 0 ≤ c → ∀ u, h (c • u) = c * h u)
    (h_add : ∀ u v, h (u + v) ≤ h u + h v) :
    supportFn (bodyOfSupportFn h h_hom h_add) = h := by
  ext u
  apply le_antisymm
  · rw [supportFn_le_iff]
    intro x hx
    rw [← SetLike.mem_coe, coe_bodyOfSupportFn] at hx
    exact hx u
  · obtain ⟨x, hx, hxu⟩ := exists_supporting_point_of_sublinear h h_hom h_add u
    rw [← hxu]
    have hxmem : x ∈ bodyOfSupportFn h h_hom h_add := by
      rw [← SetLike.mem_coe, coe_bodyOfSupportFn]; exact hx
    exact inner_le_supportFn hxmem u

/-- **Minkowski's Representation Theorem (Schneider, *Convex Bodies*, Thm. 1.7.1):**
On a finite-dimensional real inner product space `E`, every positively 1-homogeneous subadditive
function `h : E → ℝ` is the support function of a unique convex body `K : ConvexBody E`,
explicitly realized by `bodyOfSupportFn h h_hom h_add`. -/
theorem exists_convexBody_supportFn_eq [FiniteDimensional ℝ E] (h : E → ℝ)
    (h_hom : ∀ c : ℝ, 0 ≤ c → ∀ u, h (c • u) = c * h u)
    (h_add : ∀ u v, h (u + v) ≤ h u + h v) :
    ∃! K : ConvexBody E, supportFn K = h :=
  ⟨bodyOfSupportFn h h_hom h_add, supportFn_bodyOfSupportFn h h_hom h_add,
    fun _ hL => supportFn_injective (hL.trans (supportFn_bodyOfSupportFn h h_hom h_add).symm)⟩

end

end ConvexGeom
