/-
Copyright (c) 2026 Yegor Gorodzha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yegor Gorodzha
-/
module

public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Prékopa–Leindler, Brunn–Minkowski, and Bieberbach's Isodiametric Inequality

This file proves the **Prékopa–Leindler inequality** in arbitrary finite dimension via the
layer-cake representation and Tonelli induction, and derives its foundational convex-geometric
corollaries.

## Main statements

* `ConvexGeom.brunn_minkowski_one_dim_compact`, `ConvexGeom.brunn_minkowski_one_dim`:
  1D Brunn–Minkowski `volume A + volume B ≤ volume (A + B)` for nonempty measurable `A, B ⊆ ℝ`.
* `ConvexGeom.prekopa_leindler_one_dim`, `ConvexGeom.prekopa_leindler_pi`,
  `ConvexGeom.prekopa_leindler`: Prékopa–Leindler inequality for measurable `ℝ≥0∞`-valued
  functions without integrability hypotheses.
* `ConvexGeom.brunn_minkowski_mul`, `ConvexGeom.brunn_minkowski_mul_compact`:
  multiplicative Brunn–Minkowski `volume A ^ (1 - t) * volume B ^ t ≤ volume ((1 - t) • A + t • B)`.
* `ConvexGeom.brunn_minkowski_compact`, `ConvexGeom.brunn_minkowski_convexBody`:
  additive Brunn–Minkowski `volume A ^ (1 / d) + volume B ^ (1 / d) ≤ volume (A + B) ^ (1 / d)`.
* `ConvexGeom.isodiametric_inequality`: Bieberbach's isodiametric inequality
  `volume K ≤ volume (closedBall 0 (diam K / 2))`.
* `ConvexGeom.logConcave_marginal_prod`: Prékopa's theorem on log-concavity of marginals.

## References

* [K. Ball, *An Elementary Introduction to Modern Convex Geometry*][ball1997], Lectures 1 and 5
* [R. J. Gardner, *The Brunn–Minkowski inequality*][gardner2002], §7
-/

open MeasureTheory Set
open scoped ENNReal NNReal Pointwise

namespace ConvexGeom

public section

/-! ### 1. One-Dimensional Brunn–Minkowski -/

/-- **1D Brunn–Minkowski for compact nonempty sets:**
`volume A + volume B ≤ volume (A + B)` for compact nonempty `A, B ⊆ ℝ`. -/
theorem brunn_minkowski_one_dim_compact {A B : Set ℝ}
    (hAc : IsCompact A) (hAne : A.Nonempty) (hBc : IsCompact B) (hBne : B.Nonempty) :
    volume A + volume B ≤ volume (A + B) := by
  let a := sSup A
  let b := sInf B
  have ha : a ∈ A := hAc.sSup_mem hAne
  have hb : b ∈ B := hBc.sInf_mem hBne
  let A' : Set ℝ := (· + b) '' A
  let B' : Set ℝ := (a + ·) '' B
  have hA'_sub : A' ⊆ A + B := by
    rintro _ ⟨x, hx, rfl⟩
    exact Set.add_mem_add hx hb
  have hB'_sub : B' ⊆ A + B := by
    rintro _ ⟨y, hy, rfl⟩
    exact Set.add_mem_add ha hy
  have hinter : A' ∩ B' ⊆ {a + b} := by
    rintro z ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    have hxa : x ≤ a := le_csSup hAc.bddAbove hx
    have hby : b ≤ y := csInf_le hBc.bddBelow hy
    have hx_eq : x = a := by linarith
    simp [hx_eq]
  have hinter_zero : volume (A' ∩ B') = 0 :=
    measure_mono_null hinter (measure_singleton (a + b))
  have hB'_meas : MeasurableSet B' :=
    (hBc.image (continuous_const.add continuous_id)).isClosed.measurableSet
  have hA'_vol : volume A' = volume A := by
    have heq : A' = (fun x => -b + x) ⁻¹' A := by
      ext z; simp only [A', mem_image, mem_preimage]
      exact ⟨fun ⟨x, hx, hxz⟩ => by rw [show -b + z = x by linarith]; exact hx,
        fun hz => ⟨-b + z, hz, by ring⟩⟩
    rw [heq, measure_preimage_add]
  have hB'_vol : volume B' = volume B := by
    have heq : B' = (fun x => -a + x) ⁻¹' B := by
      ext z; simp only [B', mem_image, mem_preimage]
      exact ⟨fun ⟨y, hy, hyz⟩ => by rwa [← hyz, neg_add_cancel_left],
        fun hz => ⟨-a + z, hz, by ring⟩⟩
    rw [heq, measure_preimage_add]
  have hunion : volume (A' ∪ B') = volume A' + volume B' := by
    have h := measure_union_add_inter A' hB'_meas (μ := volume)
    rw [hinter_zero, add_zero] at h
    exact h
  calc
    volume A + volume B = volume A' + volume B' := by rw [hA'_vol, hB'_vol]
    _ = volume (A' ∪ B') := hunion.symm
    _ ≤ volume (A + B) := measure_mono (union_subset hA'_sub hB'_sub)

/-- Helper: every nonempty measurable set `A ⊆ ℝ` is inner-approximated by nonempty compact subsets. -/
private lemma exists_isCompact_nonempty_lt {A : Set ℝ} (hAm : MeasurableSet A) (hAne : A.Nonempty)
    {c : ℝ≥0∞} (hc : c < volume A) :
    ∃ K, K ⊆ A ∧ IsCompact K ∧ K.Nonempty ∧ c < volume K := by
  let An : ℕ → Set ℝ := fun n => A ∩ Icc (-(n : ℝ)) n
  have hAn_mono : Monotone An := fun m n hmn x ⟨hxA, h1, h2⟩ =>
    ⟨hxA, by have : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn; linarith,
          by have : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn; linarith⟩
  have hUnion : (⋃ n : ℕ, An n) = A := by
    ext x
    simp only [An, mem_iUnion, mem_inter_iff, mem_Icc]
    constructor
    · rintro ⟨_, hxA, _⟩; exact hxA
    · intro hxA
      obtain ⟨n, hn⟩ := exists_nat_gt |x|
      have h1 : -(n : ℝ) ≤ x := by linarith [neg_abs_le x]
      have h2 : x ≤ n := by linarith [le_abs_self x]
      exact ⟨n, hxA, h1, h2⟩
  have hsup : ⨆ n : ℕ, volume (An n) = volume A := by
    rw [← hUnion, hAn_mono.directed_le.measure_iUnion]
  rw [← hsup, lt_iSup_iff] at hc
  obtain ⟨n, hn⟩ := hc
  have hAn_meas : MeasurableSet (An n) := hAm.inter measurableSet_Icc
  have hAn_fin : volume (An n) ≠ ∞ :=
    ne_of_lt ((measure_mono inter_subset_right).trans_lt isCompact_Icc.measure_lt_top)
  have hdiff_pos : volume (An n) - c ≠ 0 := (tsub_pos_of_lt hn).ne'
  obtain ⟨K, hKsub, hKc, hKlt⟩ := hAn_meas.exists_isCompact_lt_add hAn_fin hdiff_pos
  have hc_lt_K : c < volume K := by
    by_contra hle
    push Not at hle
    have : volume K + (volume (An n) - c) ≤ c + (volume (An n) - c) := add_le_add hle le_rfl
    rw [add_tsub_cancel_of_le hn.le] at this
    exact not_lt_of_ge this hKlt
  obtain ⟨a, ha⟩ := hAne
  refine ⟨K ∪ {a}, union_subset (hKsub.trans inter_subset_left) (singleton_subset_iff.mpr ha),
    hKc.union isCompact_singleton, ⟨a, Or.inr rfl⟩,
    hc_lt_K.trans_le (measure_mono subset_union_left)⟩

/-- **1D Brunn–Minkowski for arbitrary nonempty measurable sets `A, B ⊆ ℝ`:**
`volume A + volume B ≤ volume (A + B)` (holds for both finite and infinite measure!). -/
theorem brunn_minkowski_one_dim {A B : Set ℝ}
    (hAm : MeasurableSet A) (hAne : A.Nonempty) (hBm : MeasurableSet B) (hBne : B.Nonempty) :
    volume A + volume B ≤ volume (A + B) := by
  by_cases hA0 : volume A = 0
  · obtain ⟨a, ha⟩ := hAne
    rw [hA0, zero_add]
    have hsub : (a + ·) '' B ⊆ A + B := by
      rintro _ ⟨y, hy, rfl⟩; exact Set.add_mem_add ha hy
    have hvol : volume ((a + ·) '' B) = volume B := by
      have heq : (a + ·) '' B = (fun z => -a + z) ⁻¹' B := by
        ext z; simp only [mem_image, mem_preimage]
        exact ⟨fun ⟨y, hy, hyz⟩ => by rwa [← hyz, neg_add_cancel_left],
          fun hz => ⟨-a + z, hz, by ring⟩⟩
      rw [heq, measure_preimage_add]
    exact hvol ▸ measure_mono hsub
  · by_cases hB0 : volume B = 0
    · obtain ⟨b, hb⟩ := hBne
      rw [hB0, add_zero]
      have hsub : (· + b) '' A ⊆ A + B := by
        rintro _ ⟨x, hx, rfl⟩; exact Set.add_mem_add hx hb
      have hvol : volume ((· + b) '' A) = volume A := by
        have heq : (· + b) '' A = (fun z => -b + z) ⁻¹' A := by
          ext z; simp only [mem_image, mem_preimage]
          exact ⟨fun ⟨x, hx, hxz⟩ => by rw [show -b + z = x by linarith]; exact hx,
            fun hz => ⟨-b + z, hz, by ring⟩⟩
        rw [heq, measure_preimage_add]
      exact hvol ▸ measure_mono hsub
    · refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
      have hpair : ∃ c d : ℝ≥0∞, c < volume A ∧ d < volume B ∧ r ≤ c + d := by
        by_cases hAtop : volume A = ⊤
        · exact ⟨r, 0, hAtop ▸ lt_top_iff_ne_top.mpr (ne_top_of_lt hr),
            pos_iff_ne_zero.mpr hB0, by simp⟩
        · by_cases hBtop : volume B = ⊤
          · exact ⟨0, r, pos_iff_ne_zero.mpr hA0,
              hBtop ▸ lt_top_iff_ne_top.mpr (ne_top_of_lt hr), by simp⟩
          · have hsum_fin : volume A + volume B ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hAtop, hBtop⟩
            have hr_fin : r ≠ ⊤ := ne_top_of_lt hr
            let δ := (volume A + volume B - r).toReal
            have hδ_pos : 0 < δ := ENNReal.toReal_pos (tsub_pos_of_lt hr).ne'
              (ENNReal.sub_ne_top hsum_fin)
            let c := ENNReal.ofReal (max 0 ((volume A).toReal - δ / 3))
            let d := ENNReal.ofReal (max 0 ((volume B).toReal - δ / 3))
            have hApos : 0 < (volume A).toReal := ENNReal.toReal_pos hA0 hAtop
            have hBpos : 0 < (volume B).toReal := ENNReal.toReal_pos hB0 hBtop
            have hc_lt : c < volume A := by
              rw [← ENNReal.ofReal_toReal hAtop]
              exact (ENNReal.ofReal_lt_ofReal_iff hApos).mpr (max_lt hApos (by linarith))
            have hd_lt : d < volume B := by
              rw [← ENNReal.ofReal_toReal hBtop]
              exact (ENNReal.ofReal_lt_ofReal_iff hBpos).mpr (max_lt hBpos (by linarith))
            have hr_le : r ≤ c + d := by
              rw [← ENNReal.ofReal_toReal hr_fin,
                ← ENNReal.ofReal_add (le_max_left _ _) (le_max_left _ _)]
              apply ENNReal.ofReal_le_ofReal
              have hδ_eq : δ = (volume A).toReal + (volume B).toReal - r.toReal := by
                dsimp only [δ]
                rw [ENNReal.toReal_sub_of_le hr.le hsum_fin, ENNReal.toReal_add hAtop hBtop]
              have h1 : (volume A).toReal - δ / 3 ≤ max 0 ((volume A).toReal - δ / 3) :=
                le_max_right _ _
              have h2 : (volume B).toReal - δ / 3 ≤ max 0 ((volume B).toReal - δ / 3) :=
                le_max_right _ _
              linarith
            exact ⟨c, d, hc_lt, hd_lt, hr_le⟩
      obtain ⟨c, d, hc, hd, hrcd⟩ := hpair
      obtain ⟨K, hKA, hKc, hKne, hcK⟩ := exists_isCompact_nonempty_lt hAm hAne hc
      obtain ⟨L, hLB, hLc, hLne, hdL⟩ := exists_isCompact_nonempty_lt hBm hBne hd
      calc
        r ≤ c + d := hrcd
        _ ≤ volume K + volume L := add_le_add hcK.le hdL.le
        _ ≤ volume (K + L) := brunn_minkowski_one_dim_compact hKc hKne hLc hLne
        _ ≤ volume (A + B) := measure_mono (Set.add_subset_add hKA hLB)

/-! ### 2. One-Dimensional Prékopa–Leindler Inequality -/

/-- Helper: normalizing `f` by its finite nonzero supremum `A = ⨆ x, f x` makes every strict
superlevel `{x | s < (A⁻¹ * f x).toReal}` nonempty for `s < 1`. -/
private lemma nonempty_superlevel_of_lt_one {f : ℝ → ℝ≥0∞} {A : ℝ≥0∞}
    (hA : A = ⨆ x, f x) (hA_ne0 : A ≠ 0) (hA_top : A ≠ ⊤) {s : ℝ} (hs1 : s < 1) :
    {x : ℝ | s < (A⁻¹ * f x).toReal}.Nonempty := by
  have hlt : ENNReal.ofReal s * A < ⨆ x, f x := by
    rw [← hA]
    simpa using ENNReal.mul_lt_mul_left hA_ne0 hA_top (ENNReal.ofReal_lt_one.mpr hs1)
  rw [lt_iSup_iff] at hlt
  obtain ⟨x, hx⟩ := hlt
  refine ⟨x, ?_⟩
  have hmul : ENNReal.ofReal s < A⁻¹ * f x := by
    calc
      ENNReal.ofReal s = A⁻¹ * (ENNReal.ofReal s * A) := by
        rw [mul_comm (ENNReal.ofReal s) A, ← mul_assoc, ENNReal.inv_mul_cancel hA_ne0 hA_top,
          one_mul]
      _ < A⁻¹ * f x := ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.mpr hA_top)
          (ENNReal.inv_ne_top.mpr hA_ne0) hx
  have hof : ENNReal.ofReal (A⁻¹ * f x).toReal = A⁻¹ * f x :=
    ENNReal.ofReal_toReal (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hA_ne0)
      (ne_top_of_le_ne_top hA_top (hA ▸ le_iSup f x)))
  rw [← hof] at hmul
  exact (ENNReal.ofReal_lt_ofReal_iff (by
    by_contra hle; push Not at hle
    rw [ENNReal.ofReal_of_nonpos hle] at hmul; exact not_lt_zero hmul)).mp hmul

/-- Helper: nonzero scalar multiplication preserves measurability of subsets of `ℝ`. -/
private lemma measurableSet_smul_real {A : Set ℝ} (hAm : MeasurableSet A) {c : ℝ} (hc : c ≠ 0) :
    MeasurableSet (c • A) := by
  have heq : c • A = (fun x => c⁻¹ * x) ⁻¹' A := by
    ext x; simp only [Set.mem_smul_set, smul_eq_mul, mem_preimage]
    exact ⟨fun ⟨a, ha, hax⟩ => by rw [← hax, inv_mul_cancel_left₀ hc]; exact ha,
      fun hx => ⟨c⁻¹ * x, hx, mul_inv_cancel_left₀ hc x⟩⟩
  rw [heq]
  exact (measurable_const_mul c⁻¹) hAm

/-- Helper: layer-cake integral on `(0, 1)` for a measurable `[0, 1]`-valued real function. -/
private lemma lintegral_Ioo_meas_lt_eq {f : ℝ → ℝ} (hf_m : Measurable f)
    (hf_nn : ∀ x, 0 ≤ f x) (hf_le1 : ∀ x, f x ≤ 1) :
    ∫⁻ s in Ioo (0 : ℝ) 1, volume {x : ℝ | s < f x} = ∫⁻ x, ENNReal.ofReal (f x) := by
  have hlc := lintegral_eq_lintegral_meas_lt (μ := volume) (f := f)
    (Filter.Eventually.of_forall hf_nn) hf_m.aemeasurable
  rw [hlc]
  have hsplit : (Ioi (0 : ℝ)) = Ioo 0 1 ∪ Ici 1 := by
    ext s; simp only [mem_Ioi, mem_union, mem_Ioo, mem_Ici]; constructor <;> intro h
    · rcases lt_or_ge s 1 with h1 | h1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr h1
    · rcases h with ⟨h0, _⟩ | h1
      · exact h0
      · linarith
  have hdisj : Disjoint (Ioo (0 : ℝ) 1) (Ici 1) := by
    rw [Set.disjoint_left]; intro s ⟨_, h1⟩ h2; rw [mem_Ici] at h2; linarith
  rw [hsplit, lintegral_union measurableSet_Ici hdisj]
  have hzero : ∫⁻ s in Ici (1 : ℝ), volume {x : ℝ | s < f x} = 0 := by
    refine setLIntegral_eq_zero measurableSet_Ici fun s hs => ?_
    have hemp : {x : ℝ | s < f x} = ∅ := by
      ext x; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      exact (hf_le1 x).trans hs
    simp [hemp]
  rw [hzero, add_zero]

/-- Bounded 1D Prékopa–Leindler via layer-cake + 1D Brunn–Minkowski + weighted AM-GM. -/
private lemma prekopa_leindler_one_dim_bounded {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {f g h : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    {M : ℝ≥0∞} (hM : M ≠ ⊤) (hfM : ∀ x, f x ≤ M) (hgM : ∀ y, g y ≤ M)
    (hcond : ∀ x y : ℝ, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) * x + t * y)) :
    (∫⁻ x, f x) ^ (1 - t) * (∫⁻ y, g y) ^ t ≤ ∫⁻ z, h z := by
  have h1t : 0 < 1 - t := sub_pos.mpr ht1
  by_cases hf0 : ∫⁻ x, f x = 0
  · rw [hf0, ENNReal.zero_rpow_of_pos h1t, zero_mul]; exact zero_le
  by_cases hg0 : ∫⁻ y, g y = 0
  · rw [hg0, ENNReal.zero_rpow_of_pos ht0, mul_zero]; exact zero_le
  let A : ℝ≥0∞ := ⨆ x, f x
  let B : ℝ≥0∞ := ⨆ y, g y
  have hA_ne0 : A ≠ 0 := by
    intro h0
    have hall : ∀ x, f x = 0 := fun x => le_antisymm ((le_iSup f x).trans_eq h0) zero_le
    exact hf0 (by simp [hall])
  have hB_ne0 : B ≠ 0 := by
    intro h0
    have hall : ∀ y, g y = 0 := fun y => le_antisymm ((le_iSup g y).trans_eq h0) zero_le
    exact hg0 (by simp [hall])
  have hA_top : A ≠ ⊤ := ne_top_of_le_ne_top hM (iSup_le hfM)
  have hB_top : B ≠ ⊤ := ne_top_of_le_ne_top hM (iSup_le hgM)
  let C : ℝ≥0∞ := A ^ (1 - t) * B ^ t
  have hC_ne0 : C ≠ 0 :=
    mul_ne_zero (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hA_ne0) hA_top).ne'
      (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hB_ne0) hB_top).ne'
  have hC_top : C ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg h1t.le hA_top)
      (ENNReal.rpow_ne_top_of_nonneg ht0.le hB_top)
  -- Normalize into `[0, 1]`-valued real measurable functions (`min 1` in `ℝ≥0∞` before `toReal`!).
  let f' : ℝ → ℝ := fun x => (A⁻¹ * f x).toReal
  let g' : ℝ → ℝ := fun y => (B⁻¹ * g y).toReal
  let h' : ℝ → ℝ := fun z => (min (1 : ℝ≥0∞) (C⁻¹ * h z)).toReal
  have hf'_m : Measurable f' := (hf.const_mul A⁻¹).ennreal_toReal
  have hg'_m : Measurable g' := (hg.const_mul B⁻¹).ennreal_toReal
  have hh'_m : Measurable h' := (measurable_const.min (hh.const_mul C⁻¹)).ennreal_toReal
  have hf'_le1 : ∀ x, f' x ≤ 1 := fun x => by
    have hle : A⁻¹ * f x ≤ 1 := by
      calc
        A⁻¹ * f x ≤ A⁻¹ * A := by gcongr; exact le_iSup f x
        _ = 1 := ENNReal.inv_mul_cancel hA_ne0 hA_top
    simpa [f'] using ENNReal.toReal_mono ENNReal.one_ne_top hle
  have hg'_le1 : ∀ y, g' y ≤ 1 := fun y => by
    have hle : B⁻¹ * g y ≤ 1 := by
      calc
        B⁻¹ * g y ≤ B⁻¹ * B := by gcongr; exact le_iSup g y
        _ = 1 := ENNReal.inv_mul_cancel hB_ne0 hB_top
    simpa [g'] using ENNReal.toReal_mono ENNReal.one_ne_top hle
  have hf'_ofReal : ∀ x, ENNReal.ofReal (f' x) = A⁻¹ * f x := fun x =>
    ENNReal.ofReal_toReal (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hA_ne0)
      (ne_top_of_le_ne_top hA_top (le_iSup f x)))
  have hg'_ofReal : ∀ y, ENNReal.ofReal (g' y) = B⁻¹ * g y := fun y =>
    ENNReal.ofReal_toReal (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hB_ne0)
      (ne_top_of_le_ne_top hB_top (le_iSup g y)))
  have hh'_ofReal : ∀ z, ENNReal.ofReal (h' z) = min (1 : ℝ≥0∞) (C⁻¹ * h z) := fun z =>
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _))
  -- For every `s ∈ (0, 1)`, `(1-t) • {s < f'} + t • {s < g'} ⊆ {s < h'}`.
  have hlevel : ∀ s ∈ Ioo (0 : ℝ) 1,
      ENNReal.ofReal (1 - t) * volume {x : ℝ | s < f' x} +
        ENNReal.ofReal t * volume {y : ℝ | s < g' y} ≤
        volume {z : ℝ | s < h' z} := by
    rintro s ⟨hs0, hs1⟩
    let As := {x : ℝ | s < f' x}
    let Bs := {y : ℝ | s < g' y}
    let Cs := {z : ℝ | s < h' z}
    have hAs_m : MeasurableSet As := measurableSet_lt measurable_const hf'_m
    have hBs_m : MeasurableSet Bs := measurableSet_lt measurable_const hg'_m
    have hAs_ne : As.Nonempty := nonempty_superlevel_of_lt_one rfl hA_ne0 hA_top hs1
    have hBs_ne : Bs.Nonempty := nonempty_superlevel_of_lt_one rfl hB_ne0 hB_top hs1
    have hsub : (1 - t) • As + t • Bs ⊆ Cs := by
      intro z hz
      rcases Set.mem_add.mp hz with ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      change s < h' ((1 - t) * x + t * y)
      have hsx : ENNReal.ofReal s < A⁻¹ * f x := by
        rw [← hf'_ofReal x]; exact (ENNReal.ofReal_lt_ofReal_iff (hs0.trans hx)).mpr hx
      have hsy : ENNReal.ofReal s < B⁻¹ * g y := by
        rw [← hg'_ofReal y]; exact (ENNReal.ofReal_lt_ofReal_iff (hs0.trans hy)).mpr hy
      have hC_inv : C⁻¹ = (A⁻¹) ^ (1 - t) * (B⁻¹) ^ t := by
        dsimp only [C]
        rw [ENNReal.mul_inv (Or.inl (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hA_ne0) hA_top).ne')
          (Or.inl (ENNReal.rpow_ne_top_of_nonneg h1t.le hA_top)),
          ENNReal.inv_rpow, ENNReal.inv_rpow]
      have hge : ENNReal.ofReal s < C⁻¹ * h ((1 - t) * x + t * y) := by
        calc
          ENNReal.ofReal s = ENNReal.ofReal s ^ (1 - t) * ENNReal.ofReal s ^ t := by
            rw [← ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.mpr hs0).ne' ENNReal.ofReal_ne_top,
              sub_add_cancel, ENNReal.rpow_one]
          _ < (A⁻¹ * f x) ^ (1 - t) * (B⁻¹ * g y) ^ t := by
            have h1 := ENNReal.rpow_lt_rpow hsx h1t
            have h2 := ENNReal.rpow_lt_rpow hsy ht0
            exact ENNReal.mul_lt_mul h1 h2
          _ = (A⁻¹ ^ (1 - t) * B⁻¹ ^ t) * (f x ^ (1 - t) * g y ^ t) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ h1t.le, ENNReal.mul_rpow_of_nonneg _ _ ht0.le]
            ring
          _ = C⁻¹ * (f x ^ (1 - t) * g y ^ t) := by rw [← hC_inv]
          _ ≤ C⁻¹ * h ((1 - t) * x + t * y) := by gcongr; exact hcond x y
      have hmin : ENNReal.ofReal s < ENNReal.ofReal (h' ((1 - t) * x + t * y)) := by
        rw [hh'_ofReal]
        exact lt_min (ENNReal.ofReal_lt_one.mpr hs1) hge
      exact (ENNReal.ofReal_lt_ofReal_iff (by
        by_contra hle; push Not at hle
        rw [ENNReal.ofReal_of_nonpos hle] at hmin; exact not_lt_zero hmin)).mp hmin
    calc
      ENNReal.ofReal (1 - t) * volume As + ENNReal.ofReal t * volume Bs
        = volume ((1 - t) • As) + volume (t • Bs) := by
            rw [Measure.addHaar_smul, Measure.addHaar_smul]
            simp [abs_of_nonneg h1t.le, abs_of_nonneg ht0.le]
      _ ≤ volume ((1 - t) • As + t • Bs) :=
            brunn_minkowski_one_dim (measurableSet_smul_real hAs_m h1t.ne') hAs_ne.smul_set
              (measurableSet_smul_real hBs_m ht0.ne') hBs_ne.smul_set
      _ ≤ volume Cs := measure_mono hsub
  -- Integrate `hlevel` over `s ∈ Ioo 0 1` using layer-cake!
  have hIoo_f : ∫⁻ s in Ioo (0 : ℝ) 1, volume {x : ℝ | s < f' x} = ∫⁻ x, A⁻¹ * f x := by
    rw [lintegral_Ioo_meas_lt_eq hf'_m (fun _ => ENNReal.toReal_nonneg) hf'_le1]
    simp_rw [hf'_ofReal]
  have hIoo_g : ∫⁻ s in Ioo (0 : ℝ) 1, volume {y : ℝ | s < g' y} = ∫⁻ y, B⁻¹ * g y := by
    rw [lintegral_Ioo_meas_lt_eq hg'_m (fun _ => ENNReal.toReal_nonneg) hg'_le1]
    simp_rw [hg'_ofReal]
  have hIoo_h : ∫⁻ s in Ioo (0 : ℝ) 1, volume {z : ℝ | s < h' z} ≤ ∫⁻ z, C⁻¹ * h z := by
    have hlc := lintegral_eq_lintegral_meas_lt (μ := volume) (f := h')
      (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hh'_m.aemeasurable
    calc
      ∫⁻ s in Ioo (0 : ℝ) 1, volume {z : ℝ | s < h' z}
        ≤ ∫⁻ s in Ioi (0 : ℝ), volume {z : ℝ | s < h' z} :=
          lintegral_mono_set Ioo_subset_Ioi_self
      _ = ∫⁻ z, ENNReal.ofReal (h' z) := hlc.symm
      _ ≤ ∫⁻ z, C⁻¹ * h z := lintegral_mono fun z => (hh'_ofReal z).trans_le (min_le_right _ _)
  have hm_f : Measurable (fun s : ℝ => volume {x : ℝ | s < f' x}) :=
    Antitone.measurable (fun _ _ h => measure_mono fun _ hx => lt_of_le_of_lt h hx)
  have hm_g : Measurable (fun s : ℝ => volume {y : ℝ | s < g' y}) :=
    Antitone.measurable (fun _ _ h => measure_mono fun _ hy => lt_of_le_of_lt h hy)
  have hlin :
      ENNReal.ofReal (1 - t) * (∫⁻ x, A⁻¹ * f x) + ENNReal.ofReal t * (∫⁻ y, B⁻¹ * g y) ≤
        ∫⁻ z, C⁻¹ * h z := by
    calc
      ENNReal.ofReal (1 - t) * (∫⁻ x, A⁻¹ * f x) + ENNReal.ofReal t * (∫⁻ y, B⁻¹ * g y)
        = (∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (1 - t) * volume {x : ℝ | s < f' x}) +
            (∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal t * volume {y : ℝ | s < g' y}) := by
            rw [← hIoo_f, ← hIoo_g, lintegral_const_mul _ hm_f, lintegral_const_mul _ hm_g]
      _ = ∫⁻ s in Ioo (0 : ℝ) 1, (ENNReal.ofReal (1 - t) * volume {x : ℝ | s < f' x} +
            ENNReal.ofReal t * volume {y : ℝ | s < g' y}) := by
            rw [lintegral_add_left (hm_f.const_mul _)]
      _ ≤ ∫⁻ s in Ioo (0 : ℝ) 1, volume {z : ℝ | s < h' z} :=
            setLIntegral_mono' measurableSet_Ioo hlevel
      _ ≤ ∫⁻ z, C⁻¹ * h z := hIoo_h
  -- Apply weighted AM-GM in `ℝ≥0∞` and undo the `A, B, C` rescaling!
  let w₁ : ℝ≥0 := ⟨1 - t, h1t.le⟩
  let w₂ : ℝ≥0 := ⟨t, ht0.le⟩
  have hw : w₁ + w₂ = 1 := NNReal.eq (by change (1 - t) + t = 1; ring)
  have hamgm : (∫⁻ x, A⁻¹ * f x) ^ (1 - t) * (∫⁻ y, B⁻¹ * g y) ^ t ≤ ∫⁻ z, C⁻¹ * h z := by
    have hgm := ENNReal.geom_mean_le_arith_mean2_weighted w₁ w₂
      (∫⁻ x, A⁻¹ * f x) (∫⁻ y, B⁻¹ * g y) hw
    have h1 : (w₁ : ℝ) = 1 - t := rfl
    have h2 : (w₂ : ℝ) = t := rfl
    have h1' : (w₁ : ℝ≥0∞) = ENNReal.ofReal (1 - t) :=
      (ENNReal.ofReal_eq_coe_nnreal h1t.le).symm
    have h2' : (w₂ : ℝ≥0∞) = ENNReal.ofReal t :=
      (ENNReal.ofReal_eq_coe_nnreal ht0.le).symm
    rw [h1, h2, h1', h2'] at hgm
    exact hgm.trans hlin
  rw [lintegral_const_mul _ hf, lintegral_const_mul _ hg, lintegral_const_mul _ hh] at hamgm
  have hC_inv : C⁻¹ = (A⁻¹) ^ (1 - t) * (B⁻¹) ^ t := by
    dsimp only [C]
    rw [ENNReal.mul_inv (Or.inl (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hA_ne0) hA_top).ne')
      (Or.inl (ENNReal.rpow_ne_top_of_nonneg h1t.le hA_top)),
      ENNReal.inv_rpow, ENNReal.inv_rpow]
  have hinv_le : C⁻¹ * ((∫⁻ x, f x) ^ (1 - t) * (∫⁻ y, g y) ^ t) ≤ C⁻¹ * ∫⁻ z, h z := by
    calc
      C⁻¹ * ((∫⁻ x, f x) ^ (1 - t) * (∫⁻ y, g y) ^ t)
        = (A⁻¹ * ∫⁻ x, f x) ^ (1 - t) * (B⁻¹ * ∫⁻ y, g y) ^ t := by
          rw [hC_inv, ENNReal.mul_rpow_of_nonneg _ _ h1t.le, ENNReal.mul_rpow_of_nonneg _ _ ht0.le]
          ring
      _ ≤ C⁻¹ * ∫⁻ z, h z := hamgm
  calc
    (∫⁻ x, f x) ^ (1 - t) * (∫⁻ y, g y) ^ t
      = C * (C⁻¹ * ((∫⁻ x, f x) ^ (1 - t) * (∫⁻ y, g y) ^ t)) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hC_ne0 hC_top, one_mul]
    _ ≤ C * (C⁻¹ * ∫⁻ z, h z) := by gcongr
    _ = ∫⁻ z, h z := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hC_ne0 hC_top, one_mul]

/-- **One-Dimensional Prékopa–Leindler Inequality** (arbitrary measurable `f, g, h : ℝ → ℝ≥0∞`,
zero boundedness or integrability assumptions!). -/
theorem prekopa_leindler_one_dim {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {f g h : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hcond : ∀ x y : ℝ, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) * x + t * y)) :
    (∫⁻ x, f x) ^ (1 - t) * (∫⁻ y, g y) ^ t ≤ ∫⁻ z, h z := by
  have h1t : 0 < 1 - t := sub_pos.mpr ht1
  -- Truncate `f` and `g` at level `n : ℕ` and pass to the limit via monotone convergence.
  let fn : ℕ → ℝ → ℝ≥0∞ := fun n x => min (f x) n
  let gn : ℕ → ℝ → ℝ≥0∞ := fun n y => min (g y) n
  have hstep : ∀ n : ℕ, (∫⁻ x, fn n x) ^ (1 - t) * (∫⁻ y, gn n y) ^ t ≤ ∫⁻ z, h z := fun n =>
    prekopa_leindler_one_dim_bounded ht0 ht1
      (hf.min measurable_const) (hg.min measurable_const) hh (ENNReal.natCast_ne_top n)
      (fun _ => min_le_right _ _) (fun _ => min_le_right _ _) (fun x y => by
        calc
          (min (f x) n) ^ (1 - t) * (min (g y) n) ^ t
            ≤ f x ^ (1 - t) * g y ^ t := by
              gcongr <;> exact min_le_left _ _
          _ ≤ h ((1 - t) * x + t * y) := hcond x y)
  have hfn_sup : (⨆ n : ℕ, ∫⁻ x, fn n x) = ∫⁻ x, f x := by
    rw [← lintegral_iSup (fun n => hf.min measurable_const)
      (fun m n hmn x => min_le_min le_rfl (Nat.cast_le.mpr hmn))]
    refine lintegral_congr fun x => ?_
    apply le_antisymm (iSup_le fun n => min_le_left _ _)
    rcases eq_or_ne (f x) ⊤ with htop | hfin
    · rw [htop, top_le_iff, eq_top_iff]
      refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
      obtain ⟨n, hn⟩ := exists_nat_gt r.toReal
      refine le_iSup_of_le n ?_
      simp only [min_eq_right le_top]
      rw [← ENNReal.ofReal_toReal (ne_top_of_lt hr)]
      exact (ENNReal.ofReal_le_ofReal hn.le).trans (by simp)
    · obtain ⟨n, hn⟩ := exists_nat_gt (f x).toReal
      refine le_iSup_of_le n (le_min le_rfl ?_)
      rw [← ENNReal.ofReal_toReal hfin]
      exact (ENNReal.ofReal_le_ofReal hn.le).trans (by simp)
  have hgn_sup : (⨆ n : ℕ, ∫⁻ y, gn n y) = ∫⁻ y, g y := by
    rw [← lintegral_iSup (fun n => hg.min measurable_const)
      (fun m n hmn y => min_le_min le_rfl (Nat.cast_le.mpr hmn))]
    refine lintegral_congr fun y => ?_
    apply le_antisymm (iSup_le fun n => min_le_left _ _)
    rcases eq_or_ne (g y) ⊤ with htop | hfin
    · rw [htop, top_le_iff, eq_top_iff]
      refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
      obtain ⟨n, hn⟩ := exists_nat_gt r.toReal
      refine le_iSup_of_le n ?_
      simp only [min_eq_right le_top]
      rw [← ENNReal.ofReal_toReal (ne_top_of_lt hr)]
      exact (ENNReal.ofReal_le_ofReal hn.le).trans (by simp)
    · obtain ⟨n, hn⟩ := exists_nat_gt (g y).toReal
      refine le_iSup_of_le n (le_min le_rfl ?_)
      rw [← ENNReal.ofReal_toReal hfin]
      exact (ENNReal.ofReal_le_ofReal hn.le).trans (by simp)
  have htf : Filter.Tendsto (fun n => ∫⁻ x, fn n x) Filter.atTop (nhds (∫⁻ x, f x)) := by
    rw [← hfn_sup]
    exact tendsto_atTop_iSup fun m n hmn => lintegral_mono fun x =>
      min_le_min le_rfl (Nat.cast_le.mpr hmn)
  have htg : Filter.Tendsto (fun n => ∫⁻ y, gn n y) Filter.atTop (nhds (∫⁻ y, g y)) := by
    rw [← hgn_sup]
    exact tendsto_atTop_iSup fun m n hmn => lintegral_mono fun y =>
      min_le_min le_rfl (Nat.cast_le.mpr hmn)
  have htprod : Filter.Tendsto (fun n => (∫⁻ x, fn n x) ^ (1 - t) * (∫⁻ y, gn n y) ^ t)
      Filter.atTop (nhds ((∫⁻ x, f x) ^ (1 - t) * (∫⁻ y, g y) ^ t)) := by
    have h1 := (ENNReal.continuous_rpow_const (y := 1 - t)).continuousAt.tendsto.comp htf
    have h2 := (ENNReal.continuous_rpow_const (y := t)).continuousAt.tendsto.comp htg
    -- Note `ENNReal.Tendsto.mul` fails only for `0 * ∞`, which can't happen if one factor is `0`!
    by_cases hf0 : ∫⁻ x, f x = 0
    · rw [hf0, ENNReal.zero_rpow_of_pos h1t, zero_mul]
      have hfn0 : ∀ n, ∫⁻ x, fn n x = 0 := fun n =>
        le_antisymm ((lintegral_mono fun x => min_le_left _ _).trans_eq hf0) zero_le
      simp [hfn0, ENNReal.zero_rpow_of_pos h1t]
    by_cases hg0 : ∫⁻ y, g y = 0
    · rw [hg0, ENNReal.zero_rpow_of_pos ht0, mul_zero]
      have hgn0 : ∀ n, ∫⁻ y, gn n y = 0 := fun n =>
        le_antisymm ((lintegral_mono fun y => min_le_left _ _).trans_eq hg0) zero_le
      simp [hgn0, ENNReal.zero_rpow_of_pos ht0]
    have hf_pow_ne0 : (∫⁻ x, f x) ^ (1 - t) ≠ 0 := by
      intro h0
      rcases ENNReal.rpow_eq_zero_iff.mp h0 with ⟨h, _⟩ | ⟨_, h⟩
      · exact hf0 h
      · linarith
    have hg_pow_ne0 : (∫⁻ y, g y) ^ t ≠ 0 := by
      intro h0
      rcases ENNReal.rpow_eq_zero_iff.mp h0 with ⟨h, _⟩ | ⟨_, h⟩
      · exact hg0 h
      · linarith
    exact ENNReal.Tendsto.mul h1 (Or.inl hf_pow_ne0) h2 (Or.inl hg_pow_ne0)
  exact le_of_tendsto htprod (Filter.Eventually.of_forall hstep)

/-! ### 3. $d$-Dimensional Prékopa–Leindler (on `Fin d → ℝ` and any inner product space `E`) -/

/-- **$d$-Dimensional Prékopa–Leindler Inequality on `Fin d → ℝ`** by Tonelli induction. -/
theorem prekopa_leindler_pi : ∀ (d : ℕ) {t : ℝ} (_ht0 : 0 < t) (_ht1 : t < 1)
    {f g h : (Fin d → ℝ) → ℝ≥0∞} (_hf : Measurable f) (_hg : Measurable g) (_hh : Measurable h)
    (_hcond : ∀ x y : Fin d → ℝ, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y)),
    (∫⁻ x, f x) ^ (1 - t) * (∫⁻ y, g y) ^ t ≤ ∫⁻ z, h z
  | 0, t, _, _, f, g, h, _, _, _, hcond => by
    rw [Measure.volume_pi_eq_dirac 0, lintegral_dirac, lintegral_dirac, lintegral_dirac]
    simpa using hcond 0 0
  | d + 1, t, ht0, ht1, f, g, h, hf, hg, hh, hcond => by
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm
    have he : MeasurePreserving e volume volume :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm
    have hfe : ∫⁻ x, f x = ∫⁻ a : ℝ, ∫⁻ x : Fin d → ℝ, f (e (a, x)) := by
      rw [← he.lintegral_comp_emb e.measurableEmbedding, Measure.volume_eq_prod]
      exact lintegral_prod (f ∘ e) (hf.comp e.measurable).aemeasurable
    have hge : ∫⁻ y, g y = ∫⁻ b : ℝ, ∫⁻ y : Fin d → ℝ, g (e (b, y)) := by
      rw [← he.lintegral_comp_emb e.measurableEmbedding, Measure.volume_eq_prod]
      exact lintegral_prod (g ∘ e) (hg.comp e.measurable).aemeasurable
    have hhe : ∫⁻ z, h z = ∫⁻ c : ℝ, ∫⁻ z : Fin d → ℝ, h (e (c, z)) := by
      rw [← he.lintegral_comp_emb e.measurableEmbedding, Measure.volume_eq_prod]
      exact lintegral_prod (h ∘ e) (hh.comp e.measurable).aemeasurable
    rw [hfe, hge, hhe]
    have hF_m : Measurable (fun a : ℝ => ∫⁻ x : Fin d → ℝ, f (e (a, x))) :=
      (hf.comp e.measurable).lintegral_prod_right'
    have hG_m : Measurable (fun b : ℝ => ∫⁻ y : Fin d → ℝ, g (e (b, y))) :=
      (hg.comp e.measurable).lintegral_prod_right'
    have hH_m : Measurable (fun c : ℝ => ∫⁻ z : Fin d → ℝ, h (e (c, z))) :=
      (hh.comp e.measurable).lintegral_prod_right'
    refine prekopa_leindler_one_dim ht0 ht1 hF_m hG_m hH_m fun a b => ?_
    refine prekopa_leindler_pi d ht0 ht1
      (hf.comp (e.measurable.comp (measurable_const.prodMk measurable_id)))
      (hg.comp (e.measurable.comp (measurable_const.prodMk measurable_id)))
      (hh.comp (e.measurable.comp (measurable_const.prodMk measurable_id)))
      fun x y => ?_
    have hlin : e ((1 - t) * a + t * b, (1 - t) • x + t • y) =
        (1 - t) • e (a, x) + t • e (b, y) := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    rw [hlin]
    exact hcond (e (a, x)) (e (b, y))

/-- **Prékopa–Leindler Inequality on any finite-dimensional real inner product space `E`:**
for measurable `f, g, h : E → ℝ≥0∞` and `0 < t < 1`, if
`f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y)` for all `x, y : E`, then
`(∫⁻ x, f x) ^ (1 - t) * (∫⁻ y, g y) ^ t ≤ ∫⁻ z, h z`. -/
theorem prekopa_leindler {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {f g h : E → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hcond : ∀ x y : E, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y)) :
    (∫⁻ x, f x) ^ (1 - t) * (∫⁻ y, g y) ^ t ≤ ∫⁻ z, h z := by
  set d := Module.finrank ℝ E
  let b := stdOrthonormalBasis ℝ E
  let φ : (Fin d → ℝ) ≃ᵐ E :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).trans b.repr.symm.toMeasurableEquiv
  have hφ : MeasurePreserving φ volume volume :=
    (PiLp.volume_preserving_toLp (Fin d)).trans b.repr.symm.measurePreserving
  have hφ_lin : ∀ (a b' : ℝ) (x y : Fin d → ℝ),
      φ (a • x + b' • y) = a • φ x + b' • φ y := fun a b' x y => by
    change b.repr.symm (WithLp.toLp 2 (a • x + b' • y)) =
      a • b.repr.symm (WithLp.toLp 2 x) + b' • b.repr.symm (WithLp.toLp 2 y)
    rw [WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_smul, map_add, map_smul, map_smul]
  rw [← hφ.lintegral_comp_emb φ.measurableEmbedding,
    ← hφ.lintegral_comp_emb φ.measurableEmbedding,
    ← hφ.lintegral_comp_emb φ.measurableEmbedding]
  refine prekopa_leindler_pi d ht0 ht1 (hf.comp φ.measurable) (hg.comp φ.measurable)
    (hh.comp φ.measurable) fun x y => ?_
  rw [hφ_lin]
  exact hcond (φ x) (φ y)

/-! ### 4. Brunn–Minkowski Inequality (Multiplicative and Additive Forms) -/

/-- **Multiplicative Brunn–Minkowski Inequality (for measurable sets):**
for measurable `A, B ⊆ E`, `t ∈ (0, 1)`, if `(1 - t) • A + t • B` is measurable, then
`volume A ^ (1 - t) * volume B ^ t ≤ volume ((1 - t) • A + t • B)`. -/
theorem brunn_minkowski_mul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {A B : Set E} (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hABm : MeasurableSet ((1 - t) • A + t • B)) :
    volume A ^ (1 - t) * volume B ^ t ≤ volume ((1 - t) • A + t • B) := by
  have h1t : 0 < 1 - t := sub_pos.mpr ht1
  let f : E → ℝ≥0∞ := A.indicator 1
  let g : E → ℝ≥0∞ := B.indicator 1
  let h : E → ℝ≥0∞ := ((1 - t) • A + t • B).indicator 1
  have hf : Measurable f := measurable_const.indicator hAm
  have hg : Measurable g := measurable_const.indicator hBm
  have hh : Measurable h := measurable_const.indicator hABm
  have hpl := prekopa_leindler ht0 ht1 hf hg hh fun x y => by
    by_cases hx : x ∈ A
    · by_cases hy : y ∈ B
      · have hxy : (1 - t) • x + t • y ∈ (1 - t) • A + t • B :=
          Set.add_mem_add (Set.smul_mem_smul_set hx) (Set.smul_mem_smul_set hy)
        simp [f, g, h, hx, hy, hxy]
      · simp [g, hy, ENNReal.zero_rpow_of_pos ht0]
    · simp [f, hx, ENNReal.zero_rpow_of_pos h1t]
  simpa [f, g, h, lintegral_indicator_one hAm, lintegral_indicator_one hBm,
    lintegral_indicator_one hABm] using hpl

/-- **Multiplicative Brunn–Minkowski Inequality (for compact sets):**
for any compact `A, B ⊆ E` and `t ∈ (0, 1)`,
`volume A ^ (1 - t) * volume B ^ t ≤ volume ((1 - t) • A + t • B)`. -/
theorem brunn_minkowski_mul_compact {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {A B : Set E} (hAc : IsCompact A) (hBc : IsCompact B)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    volume A ^ (1 - t) * volume B ^ t ≤ volume ((1 - t) • A + t • B) := by
  have hABc : IsCompact ((1 - t) • A + t • B) :=
    (hAc.smul (1 - t)).add (hBc.smul t)
  exact brunn_minkowski_mul hAc.isClosed.measurableSet hBc.isClosed.measurableSet ht0 ht1
    hABc.isClosed.measurableSet

/-- **Additive Brunn–Minkowski Inequality (`1/d`-power form, for compact nonempty sets):**
in dimension `d = finrank ℝ E ≥ 1`, for compact nonempty `A, B ⊆ E`:
`volume A ^ (1 / d : ℝ) + volume B ^ (1 / d : ℝ) ≤ volume (A + B) ^ (1 / d : ℝ)`. -/
theorem brunn_minkowski_compact {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {A B : Set E} (hAc : IsCompact A) (hAne : A.Nonempty)
    (hBc : IsCompact B) (hBne : B.Nonempty) :
    volume A ^ (1 / (Module.finrank ℝ E : ℝ)) + volume B ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
      volume (A + B) ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  set d := Module.finrank ℝ E
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr Module.finrank_pos
  have hinv_pos : (0 : ℝ) < 1 / (d : ℝ) := one_div_pos.mpr hd_pos
  by_cases hA0 : volume A = 0
  · obtain ⟨a, ha⟩ := hAne
    rw [hA0, ENNReal.zero_rpow_of_pos hinv_pos, zero_add]
    have hsub : (a + ·) '' B ⊆ A + B := by
      rintro _ ⟨y, hy, rfl⟩; exact Set.add_mem_add ha hy
    have hvol : volume ((a + ·) '' B) = volume B := by
      have heq : (a + ·) '' B = (fun z => -a + z) ⁻¹' B := by
        ext z; simp only [mem_image, mem_preimage]
        exact ⟨fun ⟨y, hy, hyz⟩ => by rwa [← hyz, neg_add_cancel_left],
          fun hz => ⟨-a + z, hz, by abel⟩⟩
      rw [heq, measure_preimage_add]
    exact ENNReal.rpow_le_rpow (hvol ▸ measure_mono hsub) hinv_pos.le
  by_cases hB0 : volume B = 0
  · obtain ⟨b, hb⟩ := hBne
    rw [hB0, ENNReal.zero_rpow_of_pos hinv_pos, add_zero]
    have hsub : (· + b) '' A ⊆ A + B := by
      rintro _ ⟨x, hx, rfl⟩; exact Set.add_mem_add hx hb
    have hvol : volume ((· + b) '' A) = volume A := by
      have heq : (· + b) '' A = (fun z => -b + z) ⁻¹' A := by
        ext z; simp only [mem_image, mem_preimage]
        exact ⟨fun ⟨x, hx, hxz⟩ => by rw [← hxz]; simpa [add_comm] using hx,
          fun hz => ⟨-b + z, hz, by abel⟩⟩
      rw [heq, measure_preimage_add]
    exact ENNReal.rpow_le_rpow (hvol ▸ measure_mono hsub) hinv_pos.le
  -- Both `A` and `B` have strictly positive finite volume. Rescale each to volume `1`!
  have hAfin : volume A ≠ ⊤ := hAc.measure_lt_top.ne
  have hBfin : volume B ≠ ⊤ := hBc.measure_lt_top.ne
  let a : ℝ := (volume A).toReal ^ (1 / (d : ℝ))
  let b : ℝ := (volume B).toReal ^ (1 / (d : ℝ))
  have ha_pos : 0 < a := Real.rpow_pos_of_pos (ENNReal.toReal_pos hA0 hAfin) _
  have hb_pos : 0 < b := Real.rpow_pos_of_pos (ENNReal.toReal_pos hB0 hBfin) _
  let t : ℝ := b / (a + b)
  have ht0 : 0 < t := div_pos hb_pos (add_pos ha_pos hb_pos)
  have ht1 : t < 1 := (div_lt_one (add_pos ha_pos hb_pos)).mpr (by linarith)
  have h1t_eq : 1 - t = a / (a + b) := by
    dsimp only [t]; field_simp [(add_pos ha_pos hb_pos).ne']; ring
  let A' : Set E := a⁻¹ • A
  let B' : Set E := b⁻¹ • B
  have hA'_vol : volume A' = 1 := by
    rw [Measure.addHaar_smul, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr ha_pos.le) _),
      ← ENNReal.ofReal_toReal hAfin, ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr ha_pos.le) _)]
    have ha_pow : a ^ d = (volume A).toReal := by
      dsimp only [a]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (ENNReal.toReal_nonneg),
        one_div_mul_cancel hd_pos.ne', Real.rpow_one]
    rw [inv_pow, ha_pow, inv_mul_cancel₀ (ENNReal.toReal_pos hA0 hAfin).ne', ENNReal.ofReal_one]
  have hB'_vol : volume B' = 1 := by
    rw [Measure.addHaar_smul, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hb_pos.le) _),
      ← ENNReal.ofReal_toReal hBfin, ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hb_pos.le) _)]
    have hb_pow : b ^ d = (volume B).toReal := by
      dsimp only [b]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (ENNReal.toReal_nonneg),
        one_div_mul_cancel hd_pos.ne', Real.rpow_one]
    rw [inv_pow, hb_pow, inv_mul_cancel₀ (ENNReal.toReal_pos hB0 hBfin).ne', ENNReal.ofReal_one]
  have hcomb : (1 - t) • A' + t • B' = (a + b)⁻¹ • (A + B) := by
    have h1 : (1 - t) • A' = (a + b)⁻¹ • A := by
      dsimp only [A']
      rw [smul_smul, h1t_eq, div_mul_eq_mul_div, mul_inv_cancel₀ ha_pos.ne', one_div]
    have h2 : t • B' = (a + b)⁻¹ • B := by
      dsimp only [B', t]
      rw [smul_smul, div_mul_eq_mul_div, mul_inv_cancel₀ hb_pos.ne', one_div]
    rw [h1, h2, ← smul_add]
  have hbm := brunn_minkowski_mul_compact (hAc.smul a⁻¹) (hBc.smul b⁻¹) ht0 ht1
  rw [hA'_vol, hB'_vol, ENNReal.one_rpow, ENNReal.one_rpow, mul_one, hcomb,
    Measure.addHaar_smul, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (add_pos ha_pos hb_pos).le) _)]
    at hbm
  -- Now `1 ≤ ((a + b)⁻¹)^d * volume (A + B)`, so `(a + b)^d ≤ volume (A + B)`!
  have hab_pow : ENNReal.ofReal ((a + b) ^ d) ≤ volume (A + B) := by
    have hmul : ENNReal.ofReal ((a + b) ^ d) * 1 ≤
        ENNReal.ofReal ((a + b) ^ d) *
          (ENNReal.ofReal (((a + b)⁻¹) ^ d) * volume (A + B)) := by gcongr
    rw [mul_one, ← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg (add_pos ha_pos hb_pos).le _),
      ← mul_pow, mul_inv_cancel₀ (add_pos ha_pos hb_pos).ne', one_pow, ENNReal.ofReal_one,
      one_mul] at hmul
    exact hmul
  have hrpow := ENNReal.rpow_le_rpow hab_pow hinv_pos.le
  rw [ENNReal.ofReal_rpow_of_pos (pow_pos (add_pos ha_pos hb_pos) d),
    ← Real.rpow_natCast, ← Real.rpow_mul (add_pos ha_pos hb_pos).le,
    mul_one_div_cancel hd_pos.ne', Real.rpow_one,
    ENNReal.ofReal_add ha_pos.le hb_pos.le] at hrpow
  have ha_eq : ENNReal.ofReal a = volume A ^ (1 / (d : ℝ)) := by
    dsimp only [a]
    rw [← ENNReal.ofReal_rpow_of_pos (ENNReal.toReal_pos hA0 hAfin), ENNReal.ofReal_toReal hAfin]
  have hb_eq : ENNReal.ofReal b = volume B ^ (1 / (d : ℝ)) := by
    dsimp only [b]
    rw [← ENNReal.ofReal_rpow_of_pos (ENNReal.toReal_pos hB0 hBfin), ENNReal.ofReal_toReal hBfin]
  rwa [ha_eq, hb_eq] at hrpow

/-- **Brunn–Minkowski Inequality for `ConvexBody E`:**
`volume K ^ (1 / d) + volume L ^ (1 / d) ≤ volume (K + L) ^ (1 / d)`. -/
theorem brunn_minkowski_convexBody {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (K L : ConvexBody E) :
    volume (K : Set E) ^ (1 / (Module.finrank ℝ E : ℝ)) +
        volume (L : Set E) ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
      volume ((K + L : ConvexBody E) : Set E) ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  rw [ConvexBody.coe_add]
  exact brunn_minkowski_compact K.isCompact K.nonempty L.isCompact L.nonempty

/-! ### 5. Bieberbach's Isodiametric Inequality -/

/-- **Bieberbach's Isodiametric Inequality (1915):**
Among all compact sets of a given diameter in a finite-dimensional real inner product space `E`,
the Euclidean ball has the largest volume:
`volume K ≤ volume (Metric.closedBall (0 : E) (Metric.diam K / 2))`. -/
theorem isodiametric_inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K : Set E} (hKc : IsCompact K) :
    volume K ≤ volume (Metric.closedBall (0 : E) (Metric.diam K / 2)) := by
  have hneg_vol : volume ((-1 : ℝ) • K) = volume K := by
    rw [Measure.addHaar_smul]; simp
  have hhalf : (1 - (1 / 2 : ℝ)) = 1 / 2 := by norm_num
  have hbm := brunn_minkowski_mul_compact hKc (hKc.smul (-1 : ℝ)) (t := (1 / 2 : ℝ))
    (by norm_num) (by norm_num)
  rw [hhalf, hneg_vol,
    ← ENNReal.rpow_add_of_nonneg (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num),
    show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, ENNReal.rpow_one] at hbm
  -- Every point `(1/2)x + (1/2)(-y) = (x - y) / 2` has norm `≤ diam K / 2`.
  have hsub : (1 / 2 : ℝ) • K + (1 / 2 : ℝ) • ((-1 : ℝ) • K) ⊆
      Metric.closedBall (0 : E) (Metric.diam K / 2) := by
    intro z hz
    rcases Set.mem_add.mp hz with ⟨_, ⟨x, hx, rfl⟩, _, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have heq : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (-1 : ℝ) • y = (1 / 2 : ℝ) • (x - y) := by
      rw [smul_sub, neg_smul, one_smul, smul_neg, sub_eq_add_neg]
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← dist_eq_norm, one_div, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (Metric.dist_le_diam_of_mem hKc.isBounded hx hy) (by norm_num)
  exact hbm.trans (measure_mono hsub)

/-! ### 6. Log-Concavity of Marginals -/

/-- **Log-Concavity of Marginals (Prékopa's Theorem):**
If `f : E × F → ℝ≥0∞` is measurable and log-concave (for `t ∈ (0, 1)`), then its marginal
`x ↦ ∫⁻ y, f (x, y)` is also log-concave. -/
theorem logConcave_marginal_prod
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [MeasurableSpace F] [BorelSpace F]
    {f : E × F → ℝ≥0∞} (hf : Measurable f)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hlog : ∀ (x₁ x₂ : E) (y₁ y₂ : F),
      f (x₁, y₁) ^ (1 - t) * f (x₂, y₂) ^ t ≤ f ((1 - t) • x₁ + t • x₂, (1 - t) • y₁ + t • y₂))
    (x₁ x₂ : E) :
    (∫⁻ y : F, f (x₁, y)) ^ (1 - t) * (∫⁻ y : F, f (x₂, y)) ^ t ≤
      ∫⁻ y : F, f ((1 - t) • x₁ + t • x₂, y) :=
  prekopa_leindler ht0 ht1
    (hf.comp (measurable_const.prodMk measurable_id))
    (hf.comp (measurable_const.prodMk measurable_id))
    (hf.comp (measurable_const.prodMk measurable_id))
    (fun y₁ y₂ => hlog x₁ x₂ y₁ y₂)

end

end ConvexGeom
