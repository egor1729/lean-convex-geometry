/-
Copyright (c) 2026 Yegor Gorodzha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yegor Gorodzha
-/
module

public import ConvexGeom.Volume.BrunnMinkowski

import ConvexGeom.Volume.Continuity
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Minkowski's First Inequality and the Euclidean Isoperimetric Inequality

This file derives **Minkowski's First Inequality** and the **Euclidean Isoperimetric Inequality**
in lower outer Minkowski content form (`liminf_{t → 0⁺}`) in arbitrary dimension
`d = finrank ℝ E ≥ 1` directly from additive Brunn–Minkowski (Ball, *An Elementary Introduction
to Modern Convex Geometry*, Lecture 5; Klartag, Lecture 1; Schneider, *Convex Bodies*, §7.1):

1. **Finite-`t` Minkowski First Inequality (`volume_add_smul_ge`, `minkowski_first_diff_ge`):**
   For any compact nonempty `K, L ⊆ E` and `t > 0`,
   $$\frac{\mathrm{vol}(K + t L) - \mathrm{vol}(K)}{t} \ge d\,\mathrm{vol}(K)^{(d-1)/d}\,\mathrm{vol}(L)^{1/d}.$$
2. **Minkowski's First Inequality (`minkowski_first_inequality`):**
   $$\liminf_{t \to 0^+} \frac{\mathrm{vol}(K + t L) - \mathrm{vol}(K)}{t} \ge d\,\mathrm{vol}(K)^{(d-1)/d}\,\mathrm{vol}(L)^{1/d}.$$
3. **Exact Outer Minkowski Content of Euclidean Balls (`minkowskiSurfaceArea_closedBall`):**
   For `r > 0`, the limit exists and equals
   $$S(\overline{B}(c, r)) = d\,r^{d-1}\,\mathrm{vol}(\overline{B}(0, 1)).$$
4. **Euclidean Isoperimetric Inequality (`isoperimetric_inequality`, `isoperimetric_inequality_ball`):**
   Among all compact nonempty sets `K ⊆ E` of a given volume, the Euclidean ball minimizes
   lower outer Minkowski content:
   $$S(K) \ge d\,\mathrm{vol}(K)^{(d-1)/d}\,\mathrm{vol}(\overline{B}(0, 1))^{1/d} = S(\overline{B}(c, r_K)).$$

**Convention:** `minkowskiSurfaceArea` is the *lower outer Minkowski content* (`liminf` as `t → 0⁺`
of `(volume (K + t • closedBall 0 1) - volume K) / t`). For convex bodies (and in particular balls),
the limit exists and agrees with classical surface area (`(d - 1)`-dimensional Hausdorff measure of
the boundary); on general compact sets `liminf` is the standard lower Minkowski content.
-/

open MeasureTheory Set Filter
open scoped ENNReal Pointwise Topology

namespace ConvexGeom

public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ### 1. Elementary Power Lower Bound and Finite-`t` First Variation -/

/-- Elementary binomial lower bound in `ℝ≥0∞`:
for `1 ≤ d`, `a ^ d + d * a ^ (d - 1) * b ≤ (a + b) ^ d`. -/
lemma add_pow_ge_linear (a b : ℝ≥0∞) : ∀ {d : ℕ}, 1 ≤ d →
    a ^ d + (d : ℝ≥0∞) * a ^ (d - 1) * b ≤ (a + b) ^ d
  | 0, hd => absurd hd (by omega)
  | 1, _ => by simp
  | d + 2, _ => by
    have ih := add_pow_ge_linear a b (d := d + 1) (by omega)
    simp only [Nat.add_sub_cancel] at ih
    have hmul : (a ^ (d + 1) + ((d + 1 : ℕ) : ℝ≥0∞) * a ^ d * b) * (a + b) ≤
        (a + b) ^ (d + 1) * (a + b) := by gcongr
    have hexp : (a ^ (d + 1) + ((d + 1 : ℕ) : ℝ≥0∞) * a ^ d * b) * (a + b) =
        a ^ (d + 2) + ((d + 2 : ℕ) : ℝ≥0∞) * a ^ (d + 1) * b +
          ((d + 1 : ℕ) : ℝ≥0∞) * a ^ d * b ^ 2 := by
      push_cast
      ring
    rw [pow_succ (a + b)]
    calc
      a ^ (d + 2) + ((d + 2 : ℕ) : ℝ≥0∞) * a ^ (d + 1) * b
        ≤ a ^ (d + 2) + ((d + 2 : ℕ) : ℝ≥0∞) * a ^ (d + 1) * b +
            ((d + 1 : ℕ) : ℝ≥0∞) * a ^ d * b ^ 2 := le_self_add
      _ = (a ^ (d + 1) + ((d + 1 : ℕ) : ℝ≥0∞) * a ^ d * b) * (a + b) := hexp.symm
      _ ≤ (a + b) ^ (d + 1) * (a + b) := hmul

/-- **Finite-`t` Minkowski First Inequality (additive form):**
for any compact nonempty `K, L ⊆ E` (`d = finrank ℝ E ≥ 1`) and `t > 0`:
`volume K + d * t * volume K ^ ((d - 1) / d) * volume L ^ (1 / d) ≤ volume (K + t • L)`. -/
theorem volume_add_smul_ge [Nontrivial E]
    {K L : Set E} (hKc : IsCompact K) (hKne : K.Nonempty)
    (hLc : IsCompact L) (hLne : L.Nonempty)
    {t : ℝ} (ht : 0 < t) :
    volume K + (Module.finrank ℝ E : ℝ≥0∞) * ENNReal.ofReal t *
        volume K ^ (((Module.finrank ℝ E - 1 : ℕ) : ℝ) / (Module.finrank ℝ E : ℝ)) *
        volume L ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
      volume (K + t • L) := by
  set d := Module.finrank ℝ E
  have hd_pos : 1 ≤ d := Module.finrank_pos
  have hd_rpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd_pos
  have hbm := brunn_minkowski_compact hKc hKne (hLc.smul t) hLne.smul_set
  rw [addHaar_smul_rpow_inv_finrank volume ht.le L] at hbm
  have hpow : (volume K ^ (1 / (d : ℝ)) + ENNReal.ofReal t * volume L ^ (1 / (d : ℝ))) ^ d ≤
      (volume (K + t • L) ^ (1 / (d : ℝ))) ^ d := pow_le_pow_left' hbm d
  have hcancel : ∀ x : ℝ≥0∞, (x ^ (1 / (d : ℝ))) ^ d = x := fun x => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, one_div_mul_cancel hd_rpos.ne', ENNReal.rpow_one]
  have hpow_pred : (volume K ^ (1 / (d : ℝ))) ^ (d - 1) =
      volume K ^ (((d - 1 : ℕ) : ℝ) / (d : ℝ)) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, one_div_mul_eq_div]
  rw [hcancel] at hpow
  have hlin := add_pow_ge_linear (volume K ^ (1 / (d : ℝ)))
    (ENNReal.ofReal t * volume L ^ (1 / (d : ℝ))) hd_pos
  rw [hcancel, hpow_pred] at hlin
  calc
    volume K + (d : ℝ≥0∞) * ENNReal.ofReal t *
        volume K ^ (((d - 1 : ℕ) : ℝ) / (d : ℝ)) * volume L ^ (1 / (d : ℝ))
      = volume K + (d : ℝ≥0∞) * volume K ^ (((d - 1 : ℕ) : ℝ) / (d : ℝ)) *
          (ENNReal.ofReal t * volume L ^ (1 / (d : ℝ))) := by ring
    _ ≤ (volume K ^ (1 / (d : ℝ)) + ENNReal.ofReal t * volume L ^ (1 / (d : ℝ))) ^ d := hlin
    _ ≤ volume (K + t • L) := hpow

/-- **Finite-`t` Minkowski First Inequality (difference-quotient form):**
for any compact nonempty `K, L ⊆ E` (`d = finrank ℝ E ≥ 1`) and `t > 0`:
`d * volume K ^ ((d - 1) / d) * volume L ^ (1 / d) ≤ (volume (K + t • L) - volume K) / t`. -/
theorem minkowski_first_diff_ge [Nontrivial E]
    {K L : Set E} (hKc : IsCompact K) (hKne : K.Nonempty)
    (hLc : IsCompact L) (hLne : L.Nonempty)
    {t : ℝ} (ht : 0 < t) :
    (Module.finrank ℝ E : ℝ≥0∞) *
        volume K ^ (((Module.finrank ℝ E - 1 : ℕ) : ℝ) / (Module.finrank ℝ E : ℝ)) *
        volume L ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
      (volume (K + t • L) - volume K) / ENNReal.ofReal t := by
  have hge := volume_add_smul_ge hKc hKne hLc hLne ht
  have hsub : (Module.finrank ℝ E : ℝ≥0∞) * ENNReal.ofReal t *
      volume K ^ (((Module.finrank ℝ E - 1 : ℕ) : ℝ) / (Module.finrank ℝ E : ℝ)) *
      volume L ^ (1 / (Module.finrank ℝ E : ℝ)) ≤ volume (K + t • L) - volume K :=
    ENNReal.le_sub_of_add_le_left hKc.measure_lt_top.ne hge
  rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr ht).ne')
    (Or.inl ENNReal.ofReal_ne_top)]
  calc
    (Module.finrank ℝ E : ℝ≥0∞) *
        volume K ^ (((Module.finrank ℝ E - 1 : ℕ) : ℝ) / (Module.finrank ℝ E : ℝ)) *
        volume L ^ (1 / (Module.finrank ℝ E : ℝ)) * ENNReal.ofReal t
      = (Module.finrank ℝ E : ℝ≥0∞) * ENNReal.ofReal t *
        volume K ^ (((Module.finrank ℝ E - 1 : ℕ) : ℝ) / (Module.finrank ℝ E : ℝ)) *
        volume L ^ (1 / (Module.finrank ℝ E : ℝ)) := by ring
    _ ≤ volume (K + t • L) - volume K := hsub

/-! ### 2. Lower Outer Minkowski Content, First Inequality, and Euclidean Isoperimetry -/

/-- Directional lower outer Minkowski first variation of `K` with respect to `L`:
`liminf_{t → 0⁺} (volume (K + t • L) - volume K) / t`. -/
@[expose]
noncomputable def minkowskiFirstDiff (K L : Set E) : ℝ≥0∞ :=
  Filter.liminf (fun t : ℝ => (volume (K + t • L) - volume K) / ENNReal.ofReal t)
    (𝓝[>] (0 : ℝ))

/-- Lower outer Minkowski content (outer Minkowski surface area) of `K ⊆ E`:
`minkowskiSurfaceArea K = liminf_{t → 0⁺} (volume (K + t • B₁) - volume K) / t`. -/
@[expose]
noncomputable def minkowskiSurfaceArea (K : Set E) : ℝ≥0∞ :=
  minkowskiFirstDiff K (Metric.closedBall (0 : E) 1)

/-- **Minkowski's First Inequality:**
for any compact nonempty `K, L ⊆ E` in dimension `d = finrank ℝ E ≥ 1`:
`d * volume K ^ ((d - 1) / d) * volume L ^ (1 / d) ≤ minkowskiFirstDiff K L`. -/
theorem minkowski_first_inequality [Nontrivial E]
    {K L : Set E} (hKc : IsCompact K) (hKne : K.Nonempty)
    (hLc : IsCompact L) (hLne : L.Nonempty) :
    (Module.finrank ℝ E : ℝ≥0∞) *
        volume K ^ (((Module.finrank ℝ E - 1 : ℕ) : ℝ) / (Module.finrank ℝ E : ℝ)) *
        volume L ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
      minkowskiFirstDiff K L := by
  rw [minkowskiFirstDiff]
  have hconst : Filter.liminf
      (fun _ : ℝ => (Module.finrank ℝ E : ℝ≥0∞) *
        volume K ^ (((Module.finrank ℝ E - 1 : ℕ) : ℝ) / (Module.finrank ℝ E : ℝ)) *
        volume L ^ (1 / (Module.finrank ℝ E : ℝ))) (𝓝[>] (0 : ℝ)) =
      (Module.finrank ℝ E : ℝ≥0∞) *
        volume K ^ (((Module.finrank ℝ E - 1 : ℕ) : ℝ) / (Module.finrank ℝ E : ℝ)) *
        volume L ^ (1 / (Module.finrank ℝ E : ℝ)) :=
    Filter.liminf_const _
  rw [← hconst]
  exact Filter.liminf_le_liminf (eventually_nhdsWithin_of_forall fun t ht =>
    minkowski_first_diff_ge hKc hKne hLc hLne ht)

/-- **Euclidean Isoperimetric Inequality (lower outer Minkowski content form):**
for every compact nonempty `K ⊆ E` in dimension `d = finrank ℝ E ≥ 1`:
$$S(K) \ge d\,\mathrm{vol}(K)^{(d-1)/d}\,\mathrm{vol}(\overline{B}(0, 1))^{1/d}.$$ -/
theorem isoperimetric_inequality [Nontrivial E]
    {K : Set E} (hKc : IsCompact K) (hKne : K.Nonempty) :
    (Module.finrank ℝ E : ℝ≥0∞) *
        volume K ^ (((Module.finrank ℝ E - 1 : ℕ) : ℝ) / (Module.finrank ℝ E : ℝ)) *
        volume (Metric.closedBall (0 : E) 1) ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
      minkowskiSurfaceArea K :=
  minkowski_first_inequality hKc hKne (isCompact_closedBall (0 : E) 1)
    ⟨0, Metric.mem_closedBall_self zero_le_one⟩

/-! ### 3. Exact Surface Area of Euclidean Balls and Ball Comparison -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Minkowski sum of a closed ball with a scaled unit closed ball:
`closedBall c r + t • closedBall 0 1 = closedBall c (r + t)` for `r ≥ 0, t ≥ 0`. -/
lemma closedBall_add_smul_unitClosedBall (c : E) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) :
    Metric.closedBall c r + t • Metric.closedBall (0 : E) 1 = Metric.closedBall c (r + t) := by
  ext z
  simp only [Set.mem_add, Set.mem_smul_set, Metric.mem_closedBall, dist_eq_norm, sub_zero]
  constructor
  · rintro ⟨x, hx, _, ⟨u, hu, rfl⟩, rfl⟩
    calc
      ‖x + t • u - c‖ = ‖(x - c) + t • u‖ := by congr 1; abel
      _ ≤ ‖x - c‖ + ‖t • u‖ := norm_add_le _ _
      _ = ‖x - c‖ + t * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
      _ ≤ r + t * 1 := add_le_add hx (mul_le_mul_of_nonneg_left hu ht)
      _ = r + t := by ring
  · intro hz
    by_cases hrt : r + t = 0
    · have hr0 : r = 0 := by linarith
      have ht0 : t = 0 := by linarith
      subst hr0; subst ht0
      have hzc : z = c := sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa using hz))
      subst hzc
      exact ⟨z, by simp, 0, ⟨0, by simp, by simp⟩, by simp⟩
    · have hrt_pos : 0 < r + t := lt_of_le_of_ne (add_nonneg hr ht) (Ne.symm hrt)
      let x : E := c + (r / (r + t)) • (z - c)
      let u : E := (1 / (r + t)) • (z - c)
      refine ⟨x, ?_, t • u, ⟨u, ?_, rfl⟩, ?_⟩
      · rw [show x - c = (r / (r + t)) • (z - c) by simp [x], norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg hr hrt_pos.le)]
        calc
          r / (r + t) * ‖z - c‖ ≤ r / (r + t) * (r + t) :=
            mul_le_mul_of_nonneg_left hz (div_nonneg hr hrt_pos.le)
          _ = r := div_mul_cancel₀ r hrt_pos.ne'
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (one_div_nonneg.mpr hrt_pos.le),
          one_div_mul_eq_div]
        exact (div_le_one hrt_pos).mpr hz
      · dsimp only [x, u]
        rw [smul_smul, add_assoc, ← add_smul,
          show r / (r + t) + t * (1 / (r + t)) = 1 by field_simp [hrt_pos.ne'],
          one_smul, add_sub_cancel]

/-- **Exact Minkowski surface area of a closed Euclidean ball:**
for `r > 0`, `minkowskiSurfaceArea (closedBall c r) = d * r ^ (d - 1) * volume (closedBall 0 1)`. -/
theorem minkowskiSurfaceArea_closedBall (c : E) {r : ℝ} (hr : 0 < r) :
    minkowskiSurfaceArea (Metric.closedBall c r) =
      (Module.finrank ℝ E : ℝ≥0∞) * ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) *
        volume (Metric.closedBall (0 : E) 1) := by
  set d := Module.finrank ℝ E
  set vB := volume (Metric.closedBall (0 : E) 1)
  have hball_vol : ∀ s : ℝ, 0 ≤ s →
      volume (Metric.closedBall c s) = ENNReal.ofReal (s ^ d) * vB := fun s hs => by
    have heq : Metric.closedBall c s = (fun x => -c + x) ⁻¹' (s • Metric.closedBall (0 : E) 1) := by
      ext x; simp only [mem_preimage, Set.mem_smul_set, Metric.mem_closedBall, dist_eq_norm, sub_zero]
      constructor
      · intro hx
        rcases hs.eq_or_lt with rfl | hs_pos
        · have hxc : x = c := sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa using hx))
          exact ⟨0, by simp, by simp [hxc]⟩
        · refine ⟨s⁻¹ • (-c + x), ?_, by rw [smul_smul, mul_inv_cancel₀ hs_pos.ne', one_smul]⟩
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hs_pos.le),
            show -c + x = x - c by abel, inv_mul_le_iff₀ hs_pos, mul_one]
          exact hx
      · rintro ⟨u, hu, hux⟩
        have hxc : x - c = s • u := by
          have : -c + x = s • u := hux.symm
          rwa [show -c + x = x - c by abel] at this
        rw [hxc, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
        exact (mul_le_mul_of_nonneg_left hu hs).trans_eq (mul_one s)
    rw [heq, measure_preimage_add, Measure.addHaar_smul, abs_of_nonneg (pow_nonneg hs _)]
  have hquot : ∀ t : ℝ, 0 < t →
      (volume (Metric.closedBall c r + t • Metric.closedBall (0 : E) 1) -
          volume (Metric.closedBall c r)) / ENNReal.ofReal t =
        ENNReal.ofReal (((r + t) ^ d - r ^ d) / t) * vB := fun t ht => by
    rw [closedBall_add_smul_unitClosedBall c hr.le ht.le,
      hball_vol (r + t) (add_pos hr ht).le, hball_vol r hr.le,
      ← ENNReal.sub_mul (fun _ _ => (isCompact_closedBall (0 : E) 1).measure_lt_top.ne),
      ← ENNReal.ofReal_sub _ (pow_nonneg hr.le _),
      ENNReal.div_eq_inv_mul, ← mul_assoc,
      ← ENNReal.ofReal_inv_of_pos ht,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le),
      inv_mul_eq_div]
  have hderiv : Tendsto (fun t : ℝ => ((r + t) ^ d - r ^ d) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 ((d : ℝ) * r ^ (d - 1))) := by
    have hd := (hasDerivAt_iff_tendsto_slope_zero.mp (hasDerivAt_pow d r)).mono_left
      (nhdsWithin_mono (0 : ℝ) (show Ioi (0 : ℝ) ⊆ ({0} : Set ℝ)ᶜ from fun _ hx => ne_of_gt hx))
    simpa [smul_eq_mul, inv_mul_eq_div] using hd
  have hvB_fin : vB ≠ ⊤ := (isCompact_closedBall (0 : E) 1).measure_lt_top.ne
  have htend : Tendsto
      (fun t : ℝ => ENNReal.ofReal (((r + t) ^ d - r ^ d) / t) * vB)
      (𝓝[>] (0 : ℝ))
      (𝓝 (ENNReal.ofReal ((d : ℝ) * r ^ (d - 1)) * vB)) :=
    ENNReal.Tendsto.mul_const (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hderiv)
      (Or.inr hvB_fin)
  have htend_eq : Tendsto
      (fun t : ℝ => (volume (Metric.closedBall c r + t • Metric.closedBall (0 : E) 1) -
          volume (Metric.closedBall c r)) / ENNReal.ofReal t)
      (𝓝[>] (0 : ℝ))
      (𝓝 (ENNReal.ofReal ((d : ℝ) * r ^ (d - 1)) * vB)) :=
    htend.congr' (eventually_nhdsWithin_of_forall fun t ht => (hquot t ht).symm)
  rw [minkowskiSurfaceArea, minkowskiFirstDiff, htend_eq.liminf_eq,
    ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_natCast]

/-- **Euclidean Isoperimetric Inequality (ball-comparison form):**
if `K ⊆ E` is compact nonempty and `closedBall c r` (`r > 0`) has the same volume as `K`, then
`minkowskiSurfaceArea (closedBall c r) ≤ minkowskiSurfaceArea K`. -/
theorem isoperimetric_inequality_ball [Nontrivial E]
    {K : Set E} (hKc : IsCompact K) (hKne : K.Nonempty)
    (c : E) {r : ℝ} (hr : 0 < r)
    (hvol : volume (Metric.closedBall c r) = volume K) :
    minkowskiSurfaceArea (Metric.closedBall c r) ≤ minkowskiSurfaceArea K := by
  set d := Module.finrank ℝ E
  have hd_pos : 1 ≤ d := Module.finrank_pos
  have hd_rpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd_pos
  set vB := volume (Metric.closedBall (0 : E) 1)
  have hKvol : volume K = ENNReal.ofReal (r ^ d) * vB := by
    rw [← hvol]
    have heq : Metric.closedBall c r = (fun x => -c + x) ⁻¹' (r • Metric.closedBall (0 : E) 1) := by
      ext x; simp only [mem_preimage, Set.mem_smul_set, Metric.mem_closedBall, dist_eq_norm, sub_zero]
      constructor
      · intro hx
        refine ⟨r⁻¹ • (-c + x), ?_, by rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]⟩
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hr.le),
          show -c + x = x - c by abel, inv_mul_le_iff₀ hr, mul_one]
        exact hx
      · rintro ⟨u, hu, hux⟩
        have hxc : x - c = r • u := by
          have : -c + x = r • u := hux.symm
          rwa [show -c + x = x - c by abel] at this
        rw [hxc, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.le]
        exact (mul_le_mul_of_nonneg_left hu hr.le).trans_eq (mul_one r)
    rw [heq, measure_preimage_add, Measure.addHaar_smul, abs_of_nonneg (pow_nonneg hr.le _)]
  have hisop := isoperimetric_inequality hKc hKne
  have hr_pow : (r ^ d) ^ (((d - 1 : ℕ) : ℝ) / (d : ℝ)) = r ^ (d - 1) := by
    rw [← Real.rpow_natCast r d, ← Real.rpow_mul hr.le, mul_div_cancel₀ _ hd_rpos.ne',
      Real.rpow_natCast]
  have hexp : ((d - 1 : ℕ) : ℝ) / (d : ℝ) + 1 / (d : ℝ) = 1 := by
    rw [← add_div, show ((d - 1 : ℕ) : ℝ) + 1 = d by exact_mod_cast Nat.sub_add_cancel hd_pos,
      div_self hd_rpos.ne']
  have hvB_eq : vB ^ (((d - 1 : ℕ) : ℝ) / (d : ℝ)) * vB ^ (1 / (d : ℝ)) = vB := by
    rw [← ENNReal.rpow_add_of_nonneg (((d - 1 : ℕ) : ℝ) / (d : ℝ)) (1 / (d : ℝ))
      (div_nonneg (Nat.cast_nonneg _) hd_rpos.le) (one_div_nonneg.mpr hd_rpos.le),
      hexp, ENNReal.rpow_one]
  calc
    minkowskiSurfaceArea (Metric.closedBall c r)
      = (d : ℝ≥0∞) * ENNReal.ofReal (r ^ (d - 1)) * vB := minkowskiSurfaceArea_closedBall c hr
    _ = (d : ℝ≥0∞) * (ENNReal.ofReal (r ^ (d - 1)) * vB ^ (((d - 1 : ℕ) : ℝ) / (d : ℝ))) *
          vB ^ (1 / (d : ℝ)) := by
        rw [mul_assoc (d : ℝ≥0∞), mul_assoc (d : ℝ≥0∞), mul_assoc (ENNReal.ofReal (r ^ (d - 1))),
          hvB_eq]
    _ = (d : ℝ≥0∞) * volume K ^ (((d - 1 : ℕ) : ℝ) / (d : ℝ)) * vB ^ (1 / (d : ℝ)) := by
        rw [hKvol, ENNReal.mul_rpow_of_nonneg _ _ (div_nonneg (Nat.cast_nonneg _) hd_rpos.le),
          ENNReal.ofReal_rpow_of_pos (pow_pos hr d), hr_pow]
    _ ≤ minkowskiSurfaceArea K := hisop

end

end ConvexGeom
