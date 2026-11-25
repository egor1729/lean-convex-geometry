module

public import ConvexGeom.Metric.SupportFunction

import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# Metric Projection, Outer Normal Cones, and Supporting Hyperplanes

This file develops the Hilbert-space nearest-point projection onto a `ConvexBody E` and its
geometric consequences (Schneider, *Convex Bodies*, §1.2–1.3):

1. **Metric projection (`metricProj`):**
   Wrapping Mathlib's Hilbert projection theorem (`exists_norm_eq_iInf_of_complete_convex`),
   we define `metricProj K : E → E` and prove:
   - `metricProj_eq_iff`: variational characterization
     `metricProj K x = y ↔ y ∈ K ∧ ∀ z ∈ K, ⟪x - y, z - y⟫ ≤ 0`.
   - `metricProj_of_mem`, `metricProj_idem`: idempotence on `K`.
   - `sq_norm_metricProj_sub_le`: **firm non-expansiveness**
     `‖P x - P y‖² ≤ ⟪x - y, P x - P y⟫`.
   - `lipschitzWith_metricProj`: `metricProj K` is **1-Lipschitz** (non-expansive).
   - `metricProj_mem_frontier_of_not_mem`: points outside `K` project to `frontier K`.
2. **Outer normal cone (`normalCone`):**
   `normalCone S y = {u | ∀ z ∈ S, ⟪z - y, u⟫ ≤ 0}` is a closed convex cone satisfying
   `u ∈ normalCone K y ↔ supportFn K u = ⟪y, u⟫` for `y ∈ K`, and
   `x - metricProj K x ∈ normalCone K (metricProj K x)`.
3. **Supporting Hyperplane Theorem (`exists_supporting_normal_of_mem_frontier`):**
   In any finite-dimensional (in fact proper) real inner product space, every boundary point
   `y ∈ frontier K` admits a unit outer normal `u` (`‖u‖ = 1`) with `supportFn K u = ⟪y, u⟫`.
-/

open Set Filter
open scoped RealInnerProductSpace Topology

namespace ConvexGeom

public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### 1. Metric Projection onto a Convex Body -/

/-- The unique nearest point in `K : ConvexBody E` to `x : E`. -/
noncomputable def metricProj (K : ConvexBody E) (x : E) : E :=
  (exists_norm_eq_iInf_of_complete_convex K.nonempty K.isCompact.isComplete K.convex x).choose

theorem metricProj_mem (K : ConvexBody E) (x : E) : metricProj K x ∈ K :=
  (exists_norm_eq_iInf_of_complete_convex K.nonempty K.isCompact.isComplete K.convex x).choose_spec.1

theorem norm_sub_metricProj_eq_iInf (K : ConvexBody E) (x : E) :
    ‖x - metricProj K x‖ = ⨅ w : (K : Set E), ‖x - w‖ :=
  (exists_norm_eq_iInf_of_complete_convex K.nonempty K.isCompact.isComplete K.convex x).choose_spec.2

theorem norm_sub_metricProj_le (K : ConvexBody E) (x : E) {z : E} (hz : z ∈ K) :
    ‖x - metricProj K x‖ ≤ ‖x - z‖ := by
  rw [norm_sub_metricProj_eq_iInf]
  exact ciInf_le (f := fun w : (K : Set E) => ‖x - w‖)
    ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩ ⟨z, hz⟩

/-- Obtuse-angle / Kolmogorov variational inequality for the metric projection. -/
theorem inner_sub_metricProj_le_zero (K : ConvexBody E) (x : E) {z : E} (hz : z ∈ K) :
    ⟪x - metricProj K x, z - metricProj K x⟫ ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero K.convex (metricProj_mem K x)).mp
    (norm_sub_metricProj_eq_iInf K x) z hz

/-- Variational characterization (and uniqueness) of the metric projection:
`metricProj K x = y ↔ y ∈ K ∧ ∀ z ∈ K, ⟪x - y, z - y⟫ ≤ 0`. -/
theorem metricProj_eq_iff (K : ConvexBody E) {x y : E} :
    metricProj K x = y ↔ y ∈ K ∧ ∀ z ∈ K, ⟪x - y, z - y⟫ ≤ 0 := by
  constructor
  · rintro rfl
    exact ⟨metricProj_mem K x, fun z hz => inner_sub_metricProj_le_zero K x hz⟩
  · rintro ⟨hy, hvar⟩
    set p := metricProj K x
    have h1 : ⟪x - p, y - p⟫ ≤ 0 := inner_sub_metricProj_le_zero K x hy
    have h2 : ⟪x - y, p - y⟫ ≤ 0 := hvar p (metricProj_mem K x)
    have hsq : ‖p - y‖ ^ 2 ≤ 0 := by
      have hid : ‖p - y‖ ^ 2 = ⟪x - p, y - p⟫ + ⟪x - y, p - y⟫ := by
        rw [← real_inner_self_eq_norm_sq, show y - p = -(p - y) by abel, inner_neg_right,
          neg_add_eq_sub, ← inner_sub_left, show (x - y) - (x - p) = p - y by abel]
      linarith
    have hnorm : ‖p - y‖ = 0 := by nlinarith [norm_nonneg (p - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

@[simp]
theorem metricProj_of_mem {K : ConvexBody E} {x : E} (hx : x ∈ K) :
    metricProj K x = x := by
  rw [metricProj_eq_iff]
  exact ⟨hx, fun z _ => by simp⟩

@[simp]
theorem metricProj_idem (K : ConvexBody E) (x : E) :
    metricProj K (metricProj K x) = metricProj K x :=
  metricProj_of_mem (metricProj_mem K x)

/-- **Firm non-expansiveness** of the metric projection onto a convex body:
`‖P x - P y‖² ≤ ⟪x - y, P x - P y⟫`. -/
theorem sq_norm_metricProj_sub_le (K : ConvexBody E) (x y : E) :
    ‖metricProj K x - metricProj K y‖ ^ 2 ≤ ⟪x - y, metricProj K x - metricProj K y⟫ := by
  set px := metricProj K x
  set py := metricProj K y
  have h1 : ⟪x - px, py - px⟫ ≤ 0 := inner_sub_metricProj_le_zero K x (metricProj_mem K y)
  have h2 : ⟪y - py, px - py⟫ ≤ 0 := inner_sub_metricProj_le_zero K y (metricProj_mem K x)
  rw [show py - px = -(px - py) by abel, inner_neg_right] at h1
  have hsum : ⟪(y - py) - (x - px), px - py⟫ ≤ 0 := by
    rw [inner_sub_left]
    linarith
  have hid : (y - py) - (x - px) = (px - py) - (x - y) := by abel
  rw [hid, inner_sub_left, real_inner_self_eq_norm_sq] at hsum
  linarith

/-- The metric projection onto a convex body is 1-Lipschitz (non-expansive). -/
theorem dist_metricProj_le (K : ConvexBody E) (x y : E) :
    dist (metricProj K x) (metricProj K y) ≤ dist x y := by
  rw [dist_eq_norm, dist_eq_norm]
  have hsq := sq_norm_metricProj_sub_le K x y
  have hcs : ⟪x - y, metricProj K x - metricProj K y⟫ ≤
      ‖x - y‖ * ‖metricProj K x - metricProj K y‖ :=
    real_inner_le_norm _ _
  have hle : ‖metricProj K x - metricProj K y‖ ^ 2 ≤
      ‖x - y‖ * ‖metricProj K x - metricProj K y‖ := hsq.trans hcs
  by_cases h0 : ‖metricProj K x - metricProj K y‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖metricProj K x - metricProj K y‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

theorem lipschitzWith_metricProj (K : ConvexBody E) :
    LipschitzWith 1 (metricProj K) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simpa using dist_metricProj_le K x y

theorem continuous_metricProj (K : ConvexBody E) :
    Continuous (metricProj K) :=
  (lipschitzWith_metricProj K).continuous

/-- Any point outside `K` projects onto the boundary `frontier K`. -/
theorem metricProj_mem_frontier_of_not_mem {K : ConvexBody E} {x : E} (hx : x ∉ K) :
    metricProj K x ∈ frontier (K : Set E) := by
  set p := metricProj K x
  have hp : p ∈ K := metricProj_mem K x
  refine ⟨subset_closure hp, fun hint => ?_⟩
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hint
  obtain ⟨ε, hε, hball⟩ := hint
  have hne : x - p ≠ 0 := fun h0 => hx (sub_eq_zero.mp h0 ▸ hp)
  have hnorm_pos : 0 < ‖x - p‖ := norm_pos_iff.mpr hne
  let t : ℝ := ε / (2 * ‖x - p‖)
  have ht_pos : 0 < t := div_pos hε (mul_pos two_pos hnorm_pos)
  let z : E := p + t • (x - p)
  have hz_ball : z ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, dist_eq_norm, show z - p = t • (x - p) by simp [z],
      norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
    dsimp only [t]
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hnorm_pos.ne']
    linarith
  have hzK : z ∈ K := hball hz_ball
  have hle : ⟪x - p, z - p⟫ ≤ 0 := inner_sub_metricProj_le_zero K x hzK
  have hpos : 0 < ⟪x - p, z - p⟫ := by
    rw [show z - p = t • (x - p) by simp [z], inner_smul_right, real_inner_self_eq_norm_sq]
    exact mul_pos ht_pos (pow_pos hnorm_pos 2)
  linarith

/-! ### 2. Outer Normal Cone -/

/-- The **ambient outer normal cone** of a set `S ⊆ E` at a point `y : E`:
`normalCone S y = {u | ∀ z ∈ S, ⟪z - y, u⟫ ≤ 0}`.

**Convention:** This definition is total in `y` and does not guard on `y ∈ S` (in particular,
`0 ∈ normalCone S y` even if `y ∉ S`). All geometric normal-cone theorems in this file take
`hy : y ∈ S` explicitly; for the Rockafellar convention returning `∅` outside `S`, see
`strictNormalCone`. -/
@[expose]
def normalCone (S : Set E) (y : E) : Set E :=
  {u : E | ∀ z ∈ S, ⟪z - y, u⟫ ≤ 0}

/-- The **strict (Rockafellar) outer normal cone** of `S ⊆ E` at `y : E`: agrees with
`normalCone S y` for `y ∈ S` and is `∅` for `y ∉ S`. -/
noncomputable def strictNormalCone (S : Set E) (y : E) : Set E := by
  classical exact if y ∈ S then normalCone S y else ∅

@[simp]
lemma strictNormalCone_of_mem {S : Set E} {y : E} (hy : y ∈ S) :
    strictNormalCone S y = normalCone S y := by
  classical simp [strictNormalCone, hy]

@[simp]
lemma strictNormalCone_of_notMem {S : Set E} {y : E} (hy : y ∉ S) :
    strictNormalCone S y = ∅ := by
  classical simp [strictNormalCone, hy]

lemma mem_normalCone {S : Set E} {y u : E} :
    u ∈ normalCone S y ↔ ∀ z ∈ S, ⟪z - y, u⟫ ≤ 0 := Iff.rfl

lemma zero_mem_normalCone (S : Set E) (y : E) : (0 : E) ∈ normalCone S y := by
  intro z _; simp

lemma smul_mem_normalCone {S : Set E} {y u : E} (hu : u ∈ normalCone S y)
    {c : ℝ} (hc : 0 ≤ c) : c • u ∈ normalCone S y := by
  intro z hz
  rw [inner_smul_right]
  exact mul_nonpos_of_nonneg_of_nonpos hc (hu z hz)

lemma convex_normalCone (S : Set E) (y : E) : Convex ℝ (normalCone S y) := by
  intro u hu v hv a b ha hb _ z hz
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha (hu z hz))
    (mul_nonpos_of_nonneg_of_nonpos hb (hv z hz))

lemma isClosed_normalCone (S : Set E) (y : E) : IsClosed (normalCone S y) := by
  have heq : normalCone S y = ⋂ z ∈ S, {u : E | ⟪z - y, u⟫ ≤ 0} := by
    ext u; simp [normalCone]
  rw [heq]
  exact isClosed_biInter fun z _ =>
    isClosed_le (continuous_const.inner continuous_id) continuous_const

/-- For `y ∈ K`, `u` is an outer normal at `y` if and only if the support function in direction `u`
is attained at `y`: `u ∈ normalCone K y ↔ supportFn K u = ⟪y, u⟫`. -/
theorem mem_normalCone_iff_supportFn {K : ConvexBody E} {y : E} (hy : y ∈ K) {u : E} :
    u ∈ normalCone (K : Set E) y ↔ supportFn K u = ⟪y, u⟫ := by
  constructor
  · intro hu
    apply le_antisymm
    · rw [supportFn_le_iff]
      intro z hz
      have h := hu z hz
      rw [inner_sub_left] at h
      linarith
    · exact inner_le_supportFn hy u
  · intro hsup z hz
    rw [inner_sub_left, ← hsup]
    linarith [inner_le_supportFn hz u]

theorem sub_metricProj_mem_normalCone (K : ConvexBody E) (x : E) :
    x - metricProj K x ∈ normalCone (K : Set E) (metricProj K x) := fun z hz => by
  rw [real_inner_comm]
  exact inner_sub_metricProj_le_zero K x hz

theorem supportFn_sub_metricProj (K : ConvexBody E) (x : E) :
    supportFn K (x - metricProj K x) = ⟪metricProj K x, x - metricProj K x⟫ :=
  (mem_normalCone_iff_supportFn (metricProj_mem K x)).mp (sub_metricProj_mem_normalCone K x)

/-! ### 3. Supporting Hyperplane Theorem at Every Boundary Point -/

/-- **Supporting Hyperplane Theorem:**
In a proper (e.g., finite-dimensional) real inner product space `E`, every boundary point
`y ∈ frontier K` of a convex body `K` admits a unit outer normal `u` (`‖u‖ = 1`) with
`u ∈ normalCone K y` (equivalently `supportFn K u = ⟪y, u⟫`). -/
theorem exists_supporting_normal_of_mem_frontier [ProperSpace E]
    (K : ConvexBody E) {y : E} (hy : y ∈ frontier (K : Set E)) :
    ∃ u : E, ‖u‖ = 1 ∧ u ∈ normalCone (K : Set E) y := by
  have hyK : y ∈ K := by
    have : y ∈ closure (K : Set E) := hy.1
    rwa [K.isClosed.closure_eq] at this
  have hnotint : y ∉ interior (K : Set E) := hy.2
  have hex : ∀ n : ℕ, ∃ x : E, x ∈ Metric.ball y (1 / ((n : ℝ) + 1)) ∧ x ∉ K := by
    intro n
    by_contra hall
    push Not at hall
    exact hnotint (mem_interior_iff_mem_nhds.mpr
      (Metric.mem_nhds_iff.mpr ⟨1 / ((n : ℝ) + 1), by positivity, hall⟩))
  choose x hx_ball hx_not using hex
  have hx_tend : Tendsto x atTop (𝓝 y) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨N, fun n hn => ?_⟩
    have hle : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
    exact (Metric.mem_ball.mp (hx_ball n)).trans_le (hle.trans hN.le)
  let p : ℕ → E := fun n => metricProj K (x n)
  have hp_tend : Tendsto p atTop (𝓝 y) := by
    have h := ((continuous_metricProj K).continuousAt (x := y)).tendsto.comp hx_tend
    rw [metricProj_of_mem hyK] at h
    exact h
  have hdiff_ne : ∀ n, x n - p n ≠ 0 := fun n h0 =>
    hx_not n (sub_eq_zero.mp h0 ▸ metricProj_mem K (x n))
  let u : ℕ → E := fun n => ‖x n - p n‖⁻¹ • (x n - p n)
  have hu_sphere : ∀ n, u n ∈ Metric.sphere (0 : E) 1 := fun n => by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hdiff_ne n))]
  have hu_normal : ∀ n, u n ∈ normalCone (K : Set E) (p n) := fun n =>
    smul_mem_normalCone (sub_metricProj_mem_normalCone K (x n)) (inv_nonneg.mpr (norm_nonneg _))
  obtain ⟨u₀, hu₀_mem, φ, hφ, hu_tend⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq hu_sphere
  refine ⟨u₀, by simpa [Metric.mem_sphere, dist_zero_right] using hu₀_mem, fun z hz => ?_⟩
  have hsub_tend : Tendsto (fun n => ⟪z - p (φ n), u (φ n)⟫) atTop (𝓝 ⟪z - y, u₀⟫) :=
    (tendsto_const_nhds.sub (hp_tend.comp hφ.tendsto_atTop)).inner hu_tend
  exact le_of_tendsto hsub_tend (Eventually.of_forall fun n => hu_normal (φ n) z hz)

/-- Corollary: every boundary point `y ∈ frontier K` is supported by a hyperplane `⟪·, u⟫ = h_K(u)`
with `‖u‖ = 1`. -/
theorem exists_unit_supportFn_eq_of_mem_frontier [ProperSpace E]
    (K : ConvexBody E) {y : E} (hy : y ∈ frontier (K : Set E)) :
    ∃ u : E, ‖u‖ = 1 ∧ supportFn K u = ⟪y, u⟫ := by
  have hyK : y ∈ K := by
    have : y ∈ closure (K : Set E) := hy.1
    rwa [K.isClosed.closure_eq] at this
  obtain ⟨u, hu, hnorm⟩ := exists_supporting_normal_of_mem_frontier K hy
  exact ⟨u, hu, (mem_normalCone_iff_supportFn hyK).mp hnorm⟩

end

end ConvexGeom
