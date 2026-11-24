module

public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Support Functions of Convex Bodies

This file defines the support function `supportFn K u = sSup {⟪x, u⟫ | x ∈ K}` of a
`ConvexBody E` in a real inner product space `E`, and proves its foundational properties:

- `supportFn_bddAbove`: the set `{⟪x, u⟫ | x ∈ K}` is bounded above (by compactness of `K`).
- `inner_le_supportFn`: `⟪x, u⟫ ≤ supportFn K u` for all `x ∈ K`.
- `supportFn_le_iff`: `supportFn K u ≤ c ↔ ∀ x ∈ K, ⟪x, u⟫ ≤ c`.
- `exists_mem_supportFn_eq`: attainment — there exists `x ∈ K` with `⟪x, u⟫ = supportFn K u`.
- `supportFn_zero`: `supportFn K 0 = 0`.
- `supportFn_mono`: monotonicity in `K`.
- `supportFn_smul`: positive homogeneity `supportFn K (c • u) = c * supportFn K u` for `0 ≤ c`.
- `supportFn_add_le`: subadditivity `supportFn K (u + v) ≤ supportFn K u + supportFn K v`.
-/

open scoped RealInnerProductSpace Pointwise

namespace ConvexGeom

public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

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
    ∃ x ∈ K, ⟪x, u⟫ = supportFn K u := by
  have hmem : supportFn K u ∈ (fun x : E => ⟪x, u⟫) '' (K : Set E) :=
    (supportFn_image_isCompact K u).sSup_mem (supportFn_image_nonempty K u)
  exact hmem

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

/-- Positive homogeneity: `h_K(c • u) = c * h_K(u)` for `c ≥ 0`. -/
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

/-- Subadditivity: `h_K(u + v) ≤ h_K(u) + h_K(v)`. -/
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

/-- Scaling of the convex body: `h_{c • K}(u) = c * h_K(u)` for `0 ≤ c`. -/
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

end

end ConvexGeom
