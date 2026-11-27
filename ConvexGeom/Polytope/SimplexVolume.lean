/-
Copyright (c) 2026 Yegor Gorodzha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yegor Gorodzha
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Volume of a $d$-Simplex via Permutation Tiling

This file proves the $d$-dimensional Lebesgue volume of a simplex in `Fin d → ℝ`:
$$
  \mathrm{vol}(\mathrm{conv}\{v_0, v_1, \dots, v_d\})
  = \frac{|\det(v_1 - v_0, \dots, v_d - v_0)|}{d!}.
$$

## Proof Overview (Permutation Tiling)
1. **Standard solid simplex & order simplex:**
   - `solidSimplex d`: `{y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1}`.
   - `orderSimplex d`: `{x | x ∈ [0, 1]^d ∧ Monotone x}`.
   - `permSimplex d σ`: `{x | x ∈ [0, 1]^d ∧ Monotone (x ∘ σ)}`.
2. **Hyperplanes have measure zero (`volume_coord_eq_zero`):**
   For `i ≠ j`, `{x | x i = x j}` is a proper submodule of `Fin d → ℝ`, hence has volume `0`
   by `Measure.addHaar_submodule`.
3. **Tiling of the unit cube (`iUnion_permSimplex_eq_unitCube` & `pairwise_aedisjoint_permSimplex`):**
   Every point in `[0, 1]^d` lies in `permSimplex d (Tuple.sort x)`. Two distinct permutations
   `σ ≠ τ` can only overlap on `{x | ∃ i ≠ j, x i = x j}`, which has measure `0`.
4. **Volume of `orderSimplex d` (`volume_orderSimplex`):**
   Each `permSimplex d σ` is a coordinate-permutation image of `orderSimplex d` (with `|det| = 1`),
   so all `d!` pieces have equal volume summing to `volume [0, 1]^d = 1`.
5. **Partial-sum linear map (`volume_solidSimplex`):**
   The lower-triangular map `(T y)_k = ∑ j ≤ k, y j` has `det = 1` and maps `solidSimplex d`
   onto `orderSimplex d`, giving `volume (solidSimplex d) = 1 / d!`.
6. **General $d$-simplex (`volume_convexHull_simplex`):**
   `convexHull ℝ (Set.range v)` is the translate by `v 0` of the linear image of `solidSimplex d`
   under the edge-matrix `j ↦ v j.succ - v 0`, so `Measure.addHaar_image_linearMap` finishes it.
-/

open MeasureTheory Set

namespace ConvexGeom

public section

/-! ### 1. Definitions -/

/-- The solid standard $d$-simplex in `Fin d → ℝ`:
`{y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1}`. -/
@[expose]
def solidSimplex (d : ℕ) : Set (Fin d → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1}

/-- The standard order simplex in `[0, 1]^d`:
`{x | 0 ≤ x ≤ 1 ∧ Monotone x}`, i.e. `0 ≤ x 0 ≤ x 1 ≤ … ≤ x (d-1) ≤ 1`. -/
@[expose]
def orderSimplex (d : ℕ) : Set (Fin d → ℝ) :=
  {x | x ∈ Icc (0 : Fin d → ℝ) 1 ∧ Monotone x}

/-- The order simplex permuted by `σ : Equiv.Perm (Fin d)`:
`0 ≤ x (σ 0) ≤ x (σ 1) ≤ … ≤ x (σ (d-1)) ≤ 1`. -/
@[expose]
def permSimplex (d : ℕ) (σ : Equiv.Perm (Fin d)) : Set (Fin d → ℝ) :=
  {x | x ∈ Icc (0 : Fin d → ℝ) 1 ∧ Monotone (x ∘ σ)}

/-! ### 2. Measure-Zero Hyperplanes -/

/-- For `i ≠ j`, the coordinate hyperplane `{x | x i = x j}` has Lebesgue measure `0`. -/
lemma volume_coord_eq_zero {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    volume ({x : Fin d → ℝ | x i = x j}) = 0 := by
  -- Express `{x | x i = x j}` as a linear subspace (submodule) of `Fin d → ℝ`.
  let H : Submodule ℝ (Fin d → ℝ) :=
    { carrier := {x | x i = x j}
      add_mem' := fun {a b} ha hb => by
        change a i = a j at ha; change b i = b j at hb
        change a i + b i = a j + b j
        rw [ha, hb]
      zero_mem' := rfl
      smul_mem' := fun c {a} ha => by
        change a i = a j at ha
        change c * a i = c * a j
        rw [ha] }
  -- `H` is a proper subspace because the indicator vector `Pi.single i 1` is not in `H`.
  have hH_ne : H ≠ ⊤ := by
    intro htop
    have hmem : Pi.single i (1 : ℝ) ∈ H := by rw [htop]; trivial
    simp [H, Pi.single_eq_same, Pi.single_eq_of_ne hij.symm] at hmem
  exact Measure.addHaar_submodule volume H hH_ne

/-! ### 3. Permutation Tiling of `[0, 1]^d` -/

/-- Every `permSimplex d σ` is closed, hence measurable. -/
lemma measurableSet_permSimplex (d : ℕ) (σ : Equiv.Perm (Fin d)) :
    MeasurableSet (permSimplex d σ) := by
  have hclosed : IsClosed (permSimplex d σ) := by
    have h1 : IsClosed (Icc (0 : Fin d → ℝ) 1) := isClosed_Icc
    have h2 : IsClosed {x : Fin d → ℝ | Monotone (x ∘ σ)} := by
      have heq : {x : Fin d → ℝ | Monotone (x ∘ σ)} =
          ⋂ (a : Fin d) (b : Fin d) (_ : a ≤ b), {x : Fin d → ℝ | x (σ a) ≤ x (σ b)} := by
        ext x
        simp [Monotone]
      rw [heq]
      refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ => ?_
      exact isClosed_le (continuous_apply (σ a)) (continuous_apply (σ b))
    exact h1.inter h2
  exact hclosed.measurableSet

/-- The `d!` permuted order simplices cover the unit cube `[0, 1]^d`. -/
lemma iUnion_permSimplex_eq_unitCube (d : ℕ) :
    (⋃ σ : Equiv.Perm (Fin d), permSimplex d σ) = Icc (0 : Fin d → ℝ) 1 := by
  ext x
  simp only [mem_iUnion, permSimplex, mem_ofPred_eq]
  constructor
  · rintro ⟨_, hx, _⟩
    exact hx
  · intro hx
    exact ⟨Tuple.sort x, hx, Tuple.monotone_sort x⟩

/-- If `x` lies in both `permSimplex d σ` and `permSimplex d τ` with `σ ≠ τ`,
then `x` has two equal coordinates `x i = x j` with `i ≠ j`. -/
lemma exists_coord_eq_of_mem_inter {d : ℕ} {σ τ : Equiv.Perm (Fin d)} (hne : σ ≠ τ)
    {x : Fin d → ℝ} (hσ : Monotone (x ∘ σ)) (hτ : Monotone (x ∘ τ)) :
    ∃ i j : Fin d, i ≠ j ∧ x i = x j := by
  by_contra h
  push Not at h
  -- If all coordinates of `x` are distinct, then `x` is injective.
  have hinj : Function.Injective x := by
    intro i j hij
    by_contra hne_ij
    exact h i j hne_ij hij
  -- A monotone injection `Fin d → ℝ` is strictly monotone, so `x ∘ σ` and `x ∘ τ`
  -- are both strictly monotone.
  have hσ_strict : StrictMono (x ∘ σ) := hσ.strictMono_of_injective (hinj.comp σ.injective)
  have hτ_strict : StrictMono (x ∘ τ) := hτ.strictMono_of_injective (hinj.comp τ.injective)
  -- `τ⁻¹ ∘ σ` is strictly monotone on `Fin d` (since `x ∘ τ ∘ (τ⁻¹ ∘ σ) = x ∘ σ`),
  -- and any strictly monotone permutation of `Fin d` is the identity!
  have hcomp_strict : StrictMono (τ.symm ∘ σ) := by
    intro a b hab
    have hlt : x (τ ((τ.symm ∘ σ) a)) < x (τ ((τ.symm ∘ σ) b)) := by
      simpa using hσ_strict hab
    exact hτ_strict.lt_iff_lt.mp hlt
  have h_id : (τ.symm * σ : Equiv.Perm (Fin d)) = 1 := by
    ext k
    have hle : ∀ m : Fin d, m ≤ (τ.symm ∘ σ) m := fun m => hcomp_strict.id_le m
    have hge : ∀ m : Fin d, (τ.symm ∘ σ) m ≤ m := by
      intro m
      by_contra hlt
      push Not at hlt
      have hsum_eq : ∑ i : Fin d, (i : ℕ) = ∑ i : Fin d, ((τ.symm ∘ σ) i : ℕ) :=
        (Equiv.sum_comp (τ.symm * σ) (fun i : Fin d => (i : ℕ))).symm
      have hsum_lt : ∑ i : Fin d, (i : ℕ) < ∑ i : Fin d, ((τ.symm ∘ σ) i : ℕ) :=
        Finset.sum_lt_sum (fun i _ => hle i) ⟨m, Finset.mem_univ m, hlt⟩
      exact hsum_lt.ne hsum_eq
    exact le_antisymm (hge k) (hle k)
  exact hne (inv_mul_eq_one.mp h_id).symm

/-- Distinct permuted simplices are almost-everywhere disjoint (`AEDisjoint`). -/
lemma pairwise_aedisjoint_permSimplex (d : ℕ) :
    Pairwise (Function.onFun (AEDisjoint volume) (permSimplex d)) := by
  intro σ τ hne
  change volume (permSimplex d σ ∩ permSimplex d τ) = 0
  -- The intersection is contained in the finite union of hyperplanes `{x | x i = x j}` (`i ≠ j`).
  have hsub : permSimplex d σ ∩ permSimplex d τ ⊆
      ⋃ (i : Fin d) (j : Fin d) (_ : i ≠ j), {x : Fin d → ℝ | x i = x j} := by
    intro x ⟨hσ, hτ⟩
    obtain ⟨i, j, hij, heq⟩ := exists_coord_eq_of_mem_inter hne hσ.2 hτ.2
    exact mem_iUnion₂.mpr ⟨i, j, mem_iUnion.mpr ⟨hij, heq⟩⟩
  refine measure_mono_null hsub ?_
  refine measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun hij => ?_
  exact volume_coord_eq_zero hij

/-! ### 4. Symmetry & Volume of `orderSimplex d` -/

/-- The coordinate-permutation linear map `(P_σ x)_i = x (σ i)`. -/
def permLinMap (d : ℕ) (σ : Equiv.Perm (Fin d)) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun x i := x (σ i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The coordinate-permutation map has determinant `±1`, hence `|det| = 1`. -/
lemma abs_det_permLinMap (d : ℕ) (σ : Equiv.Perm (Fin d)) :
    |(permLinMap d σ).det| = 1 := by
  have hmat : LinearMap.toMatrix' (permLinMap d σ) =
      (1 : Matrix (Fin d) (Fin d) ℝ).submatrix σ id := by
    ext i j
    simp [LinearMap.toMatrix'_apply, permLinMap, Pi.single_apply, Matrix.one_apply, eq_comm]
  rw [← LinearMap.det_toMatrix', hmat, Matrix.det_permute, Matrix.det_one, mul_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/-- Every permuted order simplex has the same volume as `orderSimplex d`. -/
lemma volume_permSimplex_eq (d : ℕ) (σ : Equiv.Perm (Fin d)) :
    volume (permSimplex d σ) = volume (orderSimplex d) := by
  have himg : permSimplex d σ = permLinMap d σ.symm '' orderSimplex d := by
    ext x
    constructor
    · intro ⟨hxIcc, hxMono⟩
      refine ⟨x ∘ σ, ⟨?_, hxMono⟩, ?_⟩
      · constructor
        · intro i; exact hxIcc.1 (σ i)
        · intro i; exact hxIcc.2 (σ i)
      · ext i; simp [permLinMap]
    · rintro ⟨y, ⟨hyIcc, hyMono⟩, rfl⟩
      refine ⟨⟨fun i => hyIcc.1 (σ.symm i), fun i => hyIcc.2 (σ.symm i)⟩, ?_⟩
      intro a b hab
      simpa [permLinMap] using hyMono hab
  rw [himg, Measure.addHaar_image_linearMap, abs_det_permLinMap]
  simp

/-- The $d$-dimensional volume of `orderSimplex d` is `1 / d!`. -/
theorem volume_orderSimplex (d : ℕ) :
    volume (orderSimplex d) = ENNReal.ofReal (1 / (d.factorial : ℝ)) := by
  -- Volume of the unit cube `[0, 1]^d` is `1`.
  have hcube : volume (Icc (0 : Fin d → ℝ) 1) = 1 := by
    rw [Real.volume_Icc_pi]
    simp
  -- Tiling `[0, 1]^d` by the `d!` a.e.-disjoint permuted simplices gives `1 = d! * vol(orderSimplex d)`.
  have hsum : (1 : ENNReal) = (d.factorial : ENNReal) * volume (orderSimplex d) := by
    calc
      (1 : ENNReal) = volume (Icc (0 : Fin d → ℝ) 1) := hcube.symm
      _ = volume (⋃ σ : Equiv.Perm (Fin d), permSimplex d σ) := by
            rw [iUnion_permSimplex_eq_unitCube]
      _ = ∑' σ : Equiv.Perm (Fin d), volume (permSimplex d σ) :=
            measure_iUnion₀ (pairwise_aedisjoint_permSimplex d)
              (fun σ => (measurableSet_permSimplex d σ).nullMeasurableSet)
      _ = ∑ _σ : Equiv.Perm (Fin d), volume (orderSimplex d) := by
            rw [tsum_fintype]
            refine Finset.sum_congr rfl fun σ _ => volume_permSimplex_eq d σ
      _ = (d.factorial : ENNReal) * volume (orderSimplex d) := by
            simp [Fintype.card_perm]
  -- Solve `1 = d! * vol` in `ENNReal`.
  have hfact_ne : (d.factorial : ENNReal) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero d
  have hfact_top : (d.factorial : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hvol : volume (orderSimplex d) = (d.factorial : ENNReal)⁻¹ := by
    have := congrArg ((d.factorial : ENNReal)⁻¹ * ·) hsum
    simpa [← mul_assoc, ENNReal.inv_mul_cancel hfact_ne hfact_top] using this.symm
  rw [hvol, one_div, ENNReal.ofReal_inv_of_pos (by positivity)]
  simp

/-! ### 5. Partial-Sum Map & Volume of `solidSimplex d` -/

/-- The partial-sum linear map `(T y)_k = ∑ j ≤ k, y j`. -/
def partialSumMap (d : ℕ) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun y k := ∑ j : Fin d, if j ≤ k then y j else 0
  map_add' y z := by
    ext k
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  map_smul' c y := by
    ext k
    simp [Finset.mul_sum, apply_ite]

/-- `partialSumMap d` has a lower-triangular matrix with `1`s on the diagonal, so `det = 1`. -/
lemma det_partialSumMap (d : ℕ) : (partialSumMap d).det = 1 := by
  rw [← LinearMap.det_toMatrix']
  have hentry : ∀ i j : Fin d,
      LinearMap.toMatrix' (partialSumMap d) i j = if j ≤ i then 1 else 0 := by
    intro i j
    simp only [LinearMap.toMatrix'_apply, partialSumMap, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.single_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro x _ hxj; simp [hxj]
    · intro h; exact absurd (Finset.mem_univ j) h
  have htri : (LinearMap.toMatrix' (partialSumMap d)).IsLowerTriangular := by
    intro i j hij
    have hlt : i < j := OrderDual.toDual_lt_toDual.mp hij
    simp [hentry i j, not_le_of_gt hlt]
  rw [Matrix.det_of_isLowerTriangular _ htri]
  refine Finset.prod_eq_one fun i _ => ?_
  simp [hentry i i]

/-- `partialSumMap d` maps `solidSimplex d` onto `orderSimplex d`. -/
lemma image_solidSimplex_eq_orderSimplex (d : ℕ) :
    partialSumMap d '' solidSimplex d = orderSimplex d := by
  ext x
  constructor
  · rintro ⟨y, ⟨hy_nonneg, hy_sum⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro k
      change 0 ≤ ∑ j : Fin d, if j ≤ k then y j else 0
      exact Finset.sum_nonneg fun j _ => by split_ifs <;> [exact hy_nonneg j; exact le_rfl]
    · intro k
      change (∑ j : Fin d, if j ≤ k then y j else 0) ≤ 1
      calc
        ∑ j : Fin d, (if j ≤ k then y j else 0)
          ≤ ∑ j : Fin d, y j := Finset.sum_le_sum fun j _ => by
              split_ifs <;> [exact le_rfl; exact hy_nonneg j]
        _ ≤ 1 := hy_sum
    · intro a b hab
      change (∑ j : Fin d, if j ≤ a then y j else 0) ≤ ∑ j : Fin d, if j ≤ b then y j else 0
      refine Finset.sum_le_sum fun j _ => ?_
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd (h1.trans hab) h2
      · exact hy_nonneg j
      · exact le_rfl
  · rintro ⟨⟨hx0, hx1⟩, hxMono⟩
    -- Inverse: finite differences `y 0 = x 0` and `y (k+1) = x (k+1) - x k`.
    let y : Fin d → ℝ := fun k =>
      if h : k.val = 0 then x k else x k - x ⟨k.val - 1, by omega⟩
    have hsum_y : ∀ k : Fin d, (∑ j : Fin d, if j ≤ k then y j else 0) = x k := by
      intro k
      -- Induct on `k.val`.
      obtain ⟨m, hm⟩ := k
      induction m with
      | zero =>
        have honly : ∀ j : Fin d, (if j ≤ ⟨0, hm⟩ then y j else 0) =
            if j = ⟨0, hm⟩ then x ⟨0, hm⟩ else 0 := by
          intro j
          by_cases hj : j = ⟨0, hm⟩
          · subst hj; simp [y]
          · have hnot : ¬ j ≤ ⟨0, hm⟩ := by
              intro hle
              exact hj (Fin.ext (Nat.eq_zero_of_le_zero hle))
            simp [hj, hnot]
        simp [honly]
      | succ m ih =>
        have hm' : m < d := Nat.lt_of_succ_lt hm
        have hsplit : ∀ j : Fin d, (if j ≤ ⟨m + 1, hm⟩ then y j else 0) =
            (if j ≤ ⟨m, hm'⟩ then y j else 0) + (if j = ⟨m + 1, hm⟩ then y ⟨m + 1, hm⟩ else 0) := by
          intro j
          by_cases hjeq : j = ⟨m + 1, hm⟩
          · subst hjeq
            have hnot : ¬ (⟨m + 1, hm⟩ : Fin d) ≤ ⟨m, hm'⟩ := by
              change ¬ m + 1 ≤ m; omega
            simp [hnot]
          · have hiff : j ≤ ⟨m + 1, hm⟩ ↔ j ≤ ⟨m, hm'⟩ := by
              change j.val ≤ m + 1 ↔ j.val ≤ m
              have : j.val ≠ m + 1 := fun h => hjeq (Fin.ext h)
              omega
            simp [hjeq, hiff]
        calc
          (∑ j : Fin d, if j ≤ ⟨m + 1, hm⟩ then y j else 0)
            = (∑ j : Fin d, if j ≤ ⟨m, hm'⟩ then y j else 0) +
                (∑ j : Fin d, if j = ⟨m + 1, hm⟩ then y ⟨m + 1, hm⟩ else 0) := by
              simp_rw [hsplit, Finset.sum_add_distrib]
          _ = x ⟨m, hm'⟩ + y ⟨m + 1, hm⟩ := by rw [ih hm']; simp
          _ = x ⟨m + 1, hm⟩ := by simp [y]
    refine ⟨y, ⟨?_, ?_⟩, ?_⟩
    · intro k
      dsimp [y]
      split_ifs with h
      · exact hx0 k
      · exact sub_nonneg.mpr (hxMono (by change k.val - 1 ≤ k.val; omega))
    · cases d with
      | zero => simp
      | succ d' =>
        have hlast : (∑ j : Fin (d' + 1), y j) =
            ∑ j : Fin (d' + 1), if j ≤ Fin.last d' then y j else 0 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          simp [Fin.le_last]
        rw [hlast, hsum_y (Fin.last d')]
        exact hx1 (Fin.last d')
    · ext k
      exact hsum_y k

/-- The $d$-dimensional Lebesgue volume of the solid standard $d$-simplex is `1 / d!`. -/
theorem volume_solidSimplex (d : ℕ) :
    volume (solidSimplex d) = ENNReal.ofReal (1 / (d.factorial : ℝ)) := by
  have h := volume_orderSimplex d
  rw [← image_solidSimplex_eq_orderSimplex, Measure.addHaar_image_linearMap, det_partialSumMap] at h
  simpa using h

/-! ### 6. Volume of an Arbitrary $d$-Simplex -/

/-- The edge linear map of a $(d+1)$-tuple of vertices `v : Fin (d + 1) → (Fin d → ℝ)`:
sends `y : Fin d → ℝ` to `∑ j, y j • (v j.succ - v 0)`. -/
def simplexEdgeMap {d : ℕ} (v : Fin (d + 1) → (Fin d → ℝ)) :
    (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun y := ∑ j : Fin d, y j • (v j.succ - v 0)
  map_add' y z := by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' c y := by
    simp [mul_smul, Finset.smul_sum]

@[simp]
lemma simplexEdgeMap_apply {d : ℕ} (v : Fin (d + 1) → (Fin d → ℝ)) (y : Fin d → ℝ) :
    simplexEdgeMap v y = ∑ j : Fin d, y j • (v j.succ - v 0) := by
  rfl

/-- The `d × d` edge matrix whose `j`-th column is `v j.succ - v 0`. -/
@[expose]
def simplexEdgeMatrix {d : ℕ} (v : Fin (d + 1) → (Fin d → ℝ)) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => v j.succ i - v 0 i

@[simp]
lemma simplexEdgeMatrix_apply {d : ℕ} (v : Fin (d + 1) → (Fin d → ℝ)) (i j : Fin d) :
    simplexEdgeMatrix v i j = v j.succ i - v 0 i := by
  rfl

/-- `simplexEdgeMap v` has the same determinant as the explicit edge matrix `simplexEdgeMatrix v`. -/
theorem det_simplexEdgeMap_eq_det_matrix {d : ℕ} (v : Fin (d + 1) → (Fin d → ℝ)) :
    (simplexEdgeMap v).det = (simplexEdgeMatrix v).det := by
  rw [← LinearMap.det_toMatrix']
  congr 1
  ext i j
  rw [LinearMap.toMatrix'_apply, simplexEdgeMap_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, simplexEdgeMatrix_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [Pi.single_eq_of_ne hkj]
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- `convexHull ℝ (Set.range v)` is the translate by `v 0` of `simplexEdgeMap v '' solidSimplex d`. -/
lemma convexHull_range_eq_image_solidSimplex {d : ℕ} (v : Fin (d + 1) → (Fin d → ℝ)) :
    convexHull ℝ (Set.range v) = (fun x => v 0 + x) '' (simplexEdgeMap v '' solidSimplex d) := by
  rw [convexHull_range_eq_exists_affineCombination]
  ext p
  constructor
  · rintro ⟨s, w, hw0, hw1, rfl⟩
    -- Extend `w` by `0` outside `s`, then take `y j = w' j.succ`.
    let w' : Fin (d + 1) → ℝ := fun i => if i ∈ s then w i else 0
    have hw'_nonneg : ∀ i, 0 ≤ w' i := fun i => by
      dsimp [w']; split_ifs with hi
      · exact hw0 i hi
      · exact le_rfl
    have hw'_sum : ∑ i : Fin (d + 1), w' i = 1 := by
      simpa [w', Finset.sum_ite_mem, Finset.univ_inter] using hw1
    let y : Fin d → ℝ := fun j => w' j.succ
    have hy_mem : y ∈ solidSimplex d := by
      refine ⟨fun j => hw'_nonneg j.succ, ?_⟩
      have h0 : 0 ≤ w' 0 := hw'_nonneg 0
      have hsplit : w' 0 + ∑ j : Fin d, y j = 1 := by
        simpa [y, Fin.sum_univ_succ] using hw'_sum
      linarith
    refine ⟨simplexEdgeMap v y, ⟨y, hy_mem, rfl⟩, ?_⟩
    rw [Finset.affineCombination_eq_linear_combination s v w hw1]
    have hsum_v : ∑ i ∈ s, w i • v i = ∑ i : Fin (d + 1), w' i • v i := by
      rw [← Finset.sum_subset (Finset.subset_univ s)]
      · refine Finset.sum_congr rfl fun i hi => by simp [w', hi]
      · intro i _ hi; simp [w', hi]
    rw [hsum_v, Fin.sum_univ_succ]
    have hw0_eq : w' 0 = 1 - ∑ j : Fin d, y j := by
      have hsplit : w' 0 + ∑ j : Fin d, y j = 1 := by
        simpa [y, Fin.sum_univ_succ] using hw'_sum
      linarith
    simp only [simplexEdgeMap, LinearMap.coe_mk, AddHom.coe_mk, smul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_smul, hw0_eq, sub_smul, one_smul]
    abel
  · rintro ⟨_, ⟨y, ⟨hy0, hysum⟩, rfl⟩, rfl⟩
    let w : Fin (d + 1) → ℝ := Fin.cons (1 - ∑ j : Fin d, y j) y
    have hw0 : ∀ i ∈ (Finset.univ : Finset (Fin (d + 1))), 0 ≤ w i := by
      intro i _
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [w]; linarith
      · simpa [w] using hy0 j
    have hw1 : ∑ i ∈ (Finset.univ : Finset (Fin (d + 1))), w i = 1 := by
      simp [w, Fin.sum_univ_succ]
    refine ⟨Finset.univ, w, hw0, hw1, ?_⟩
    rw [Finset.affineCombination_eq_linear_combination Finset.univ v w hw1, Fin.sum_univ_succ]
    simp only [w, Fin.cons_zero, Fin.cons_succ, simplexEdgeMap, LinearMap.coe_mk, AddHom.coe_mk,
      smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, sub_smul, one_smul]
    abel

/-- **Volume of a $d$-simplex in `Fin d → ℝ`:**
`volume (convexHull ℝ (Set.range v)) = ENNReal.ofReal (|(simplexEdgeMap v).det| / d!)`. -/
theorem volume_convexHull_simplex {d : ℕ} (v : Fin (d + 1) → (Fin d → ℝ)) :
    volume (convexHull ℝ (Set.range v)) =
      ENNReal.ofReal (|(simplexEdgeMap v).det| / (d.factorial : ℝ)) := by
  rw [convexHull_range_eq_image_solidSimplex]
  have htrans : (fun x => v 0 + x) '' (simplexEdgeMap v '' solidSimplex d) =
      (fun x => -v 0 + x) ⁻¹' (simplexEdgeMap v '' solidSimplex d) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; simpa using hy
    · intro hx; exact ⟨-v 0 + x, hx, by simp⟩
  rw [htrans, measure_preimage_add, Measure.addHaar_image_linearMap, volume_solidSimplex,
    ← ENNReal.ofReal_mul (abs_nonneg _), mul_one_div]

/-- **Matrix-determinant form of $d$-simplex volume in `Fin d → ℝ`:**
`volume (convexHull ℝ (Set.range v)) = ENNReal.ofReal (|(simplexEdgeMatrix v).det| / d!)`. -/
theorem volume_convexHull_simplex_matrix {d : ℕ} (v : Fin (d + 1) → (Fin d → ℝ)) :
    volume (convexHull ℝ (Set.range v)) =
      ENNReal.ofReal (|(simplexEdgeMatrix v).det| / (d.factorial : ℝ)) := by
  rw [volume_convexHull_simplex, det_simplexEdgeMap_eq_det_matrix]

/-- **Volume of a $d$-simplex in `EuclideanSpace ℝ (Fin d)`:**
transfers `volume_convexHull_simplex` via the measure-preserving equivalence `WithLp.ofLp`. -/
theorem volume_convexHull_simplex_euclideanSpace {d : ℕ}
    (v : Fin (d + 1) → EuclideanSpace ℝ (Fin d)) :
    volume (convexHull ℝ (Set.range v)) =
      ENNReal.ofReal (|(simplexEdgeMap (fun i => (v i).ofLp)).det| / (d.factorial : ℝ)) := by
  let e := EuclideanSpace.equiv (Fin d) ℝ
  have hpre : convexHull ℝ (Set.range v) =
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm ⁻¹'
        convexHull ℝ (Set.range (fun i => (v i).ofLp)) := by
    have hmap : e.toAffineMap '' convexHull ℝ (Set.range v) =
        convexHull ℝ (Set.range (fun i => (v i).ofLp)) := by
      rw [AffineMap.image_convexHull, ← Set.range_comp]
      rfl
    ext x
    simp only [Set.mem_preimage, MeasurableEquiv.coe_toLp_symm]
    rw [← hmap]
    constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = x := e.injective hyx
      rwa [← this]
  have hmeas : NullMeasurableSet (convexHull ℝ (Set.range (fun i => (v i).ofLp))) volume :=
    ((Set.finite_range _).isCompact_convexHull ℝ).isClosed.measurableSet.nullMeasurableSet
  rw [hpre, (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).measure_preimage hmeas]
  exact volume_convexHull_simplex (fun i => (v i).ofLp)

/-- **Matrix-determinant form of $d$-simplex volume in `EuclideanSpace ℝ (Fin d)`.** -/
theorem volume_convexHull_simplex_euclideanSpace_matrix {d : ℕ}
    (v : Fin (d + 1) → EuclideanSpace ℝ (Fin d)) :
    volume (convexHull ℝ (Set.range v)) =
      ENNReal.ofReal (|(simplexEdgeMatrix (fun i => (v i).ofLp)).det| / (d.factorial : ℝ)) := by
  rw [volume_convexHull_simplex_euclideanSpace, det_simplexEdgeMap_eq_det_matrix]

end

end ConvexGeom
