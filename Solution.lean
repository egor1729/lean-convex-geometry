/-
Copyright (c) 2026 Yegor Gorodzha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yegor Gorodzha
-/
module

public import ConvexGeom

public section

/-!
# Comparator Proofs (`Solution`)

Connects the 30 Mathlib-only statements in `Challenge.lean` to their completed proofs in
`ConvexGeom`. Run `./scripts/verify-comparator.sh` (or `lake comparator --paranoid`) to verify that
every declaration matches `Challenge.lean` identically, uses only `{propext, Quot.sound,
Classical.choice}`, and is accepted by Lean's kernel and the bundled independent checkers.
-/

namespace ConvexGeomChallenge

open MeasureTheory
open scoped ENNReal NNReal Pointwise RealInnerProductSpace

/-! ### Auxiliary Definitions (Identical to `Challenge.lean`) -/

@[expose]
noncomputable def minkowskiSurfaceArea {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (K : Set E) : ℝ≥0∞ :=
  Filter.liminf
    (fun t : ℝ => (volume (K + t • Metric.closedBall (0 : E) 1) - volume K) / ENNReal.ofReal t)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))

@[expose]
noncomputable def sphereProb {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    Measure (Metric.sphere (0 : E) 1) :=
  ((volume : Measure E).toSphere Set.univ)⁻¹ • (volume : Measure E).toSphere

@[expose]
noncomputable def meanWidth {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (K : ConvexBody E) : ℝ :=
  ∫ u : Metric.sphere (0 : E) 1,
    sSup ((fun x : E => ⟪x, u.1⟫) '' (K : Set E)) ∂(sphereProb (E := E))

@[expose]
noncomputable def stdGaussian (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Measure E :=
  volume.withDensity fun x : E =>
    ENNReal.ofReal ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (-(‖x‖ ^ 2) / 2))

/-! ### 1. Metric & Duality -/

theorem blaschke_selection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {C : Set E} (hC : IsCompact C) (K : ℕ → ConvexBody E)
    (hK : ∀ n, (K n : Set E) ⊆ C) :
    ∃ K₀ : ConvexBody E, (K₀ : Set E) ⊆ C ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Filter.Tendsto (K ∘ φ) Filter.atTop (nhds K₀) :=
  ConvexGeom.blaschke_selection hC K hK

theorem bipolar_theorem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {K : Set E} (hconv : Convex ℝ K) (hclosed : IsClosed K) (h0 : (0 : E) ∈ K) :
    {z : E | ∀ y ∈ {w : E | ∀ x ∈ K, ⟪x, w⟫ ≤ 1}, ⟪y, z⟫ ≤ 1} = K :=
  ConvexGeom.polarBody_polarBody hconv hclosed h0

theorem supporting_hyperplane {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : ConvexBody E) {y : E} (hy : y ∈ frontier (K : Set E)) :
    ∃ u : E, ‖u‖ = 1 ∧ ∀ x ∈ (K : Set E), ⟪x, u⟫ ≤ ⟪y, u⟫ := by
  obtain ⟨u, hu, hnorm⟩ := ConvexGeom.exists_supporting_normal_of_mem_frontier K hy
  refine ⟨u, hu, fun x hx => ?_⟩
  have hle : ⟪x - y, u⟫ ≤ 0 := hnorm x hx
  rw [inner_sub_left] at hle
  linarith

/-! ### 2. Polytopes & Combinatorial Convexity -/

theorem simplex_volume {d : ℕ} (v : Fin (d + 1) → (Fin d → ℝ)) :
    volume (convexHull ℝ (Set.range v)) =
      ENNReal.ofReal (|(Matrix.of fun i j : Fin d => v j.succ i - v 0 i).det| / (d.factorial : ℝ)) :=
  ConvexGeom.volume_convexHull_simplex_matrix v

theorem helly_theorem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (F : Finset (ConvexBody E))
    (hcard : Module.finrank ℝ E + 1 ≤ F.card)
    (hinter : ∀ G ⊆ F, G.card = Module.finrank ℝ E + 1 → (⋂ K ∈ G, (K : Set E)).Nonempty) :
    (⋂ K ∈ F, (K : Set E)).Nonempty :=
  ConvexGeom.helly_convexBody_finset F hcard hinter

theorem krein_milman_finDim {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hKc : IsCompact K) (hKconv : Convex ℝ K) :
    convexHull ℝ (K.extremePoints ℝ) = K :=
  ConvexGeom.convexHull_extremePoints_eq hKc hKconv

theorem jung_theorem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : ConvexBody E) :
    ∃ c : E, (K : Set E) ⊆ Metric.closedBall c
      (Real.sqrt ((Module.finrank ℝ E : ℝ) / (2 * (Module.finrank ℝ E + 1))) *
        Metric.diam (K : Set E)) :=
  ConvexGeom.jung_circumradius_convexBody K

theorem weyl_minkowski_halfspaces {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Finset E} (h0 : (0 : E) ∈ interior (convexHull ℝ (S : Set E))) :
    ∃ U : Finset E, convexHull ℝ (S : Set E) = {x : E | ∀ u ∈ U, ⟪x, u⟫ ≤ 1} :=
  ⟨ConvexGeom.facetNormals S, ConvexGeom.weyl_minkowski_halfspaces h0⟩

/-! ### 3. Volume & Isoperimetry -/

theorem prekopa_leindler {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {f g h : E → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hcond : ∀ x y : E, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y)) :
    (∫⁻ x, f x) ^ (1 - t) * (∫⁻ y, g y) ^ t ≤ ∫⁻ z, h z :=
  ConvexGeom.prekopa_leindler ht0 ht1 hf hg hh hcond

theorem brunn_minkowski {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {A B : Set E} (hAc : IsCompact A) (hAne : A.Nonempty)
    (hBc : IsCompact B) (hBne : B.Nonempty) :
    volume A ^ (1 / (Module.finrank ℝ E : ℝ)) + volume B ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
      volume (A + B) ^ (1 / (Module.finrank ℝ E : ℝ)) :=
  ConvexGeom.brunn_minkowski_compact hAc hAne hBc hBne

theorem isodiametric_inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K : Set E} (hKc : IsCompact K) :
    volume K ≤ volume (Metric.closedBall (0 : E) (Metric.diam K / 2)) :=
  ConvexGeom.isodiametric_inequality hKc

theorem rogers_shephard {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K : Set E} (hKconv : Convex ℝ K) (hKc : IsCompact K) :
    volume (K - K) ≤ ((Nat.choose (2 * Module.finrank ℝ E) (Module.finrank ℝ E) : ℕ) : ℝ≥0∞) *
      volume K :=
  ConvexGeom.rogers_shephard hKconv hKc

theorem isoperimetric_inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {K : Set E} (hKc : IsCompact K) (hKne : K.Nonempty) :
    (Module.finrank ℝ E : ℝ≥0∞) *
        volume K ^ (((Module.finrank ℝ E - 1 : ℕ) : ℝ) / (Module.finrank ℝ E : ℝ)) *
        volume (Metric.closedBall (0 : E) 1) ^ (1 / (Module.finrank ℝ E : ℝ)) ≤
      minkowskiSurfaceArea K :=
  ConvexGeom.isoperimetric_inequality hKc hKne

/-! ### 4. Asymptotic Convex Geometry (Ball's Lectures) -/

theorem john_theorem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (K : ConvexBody E) (hint : (interior (K : Set E)).Nonempty) :
    ∃ A : E ≃ᵃ[ℝ] E,
      Metric.closedBall (0 : E) 1 ⊆ A '' (K : Set E) ∧
      A '' (K : Set E) ⊆ (Module.finrank ℝ E : ℝ) • Metric.closedBall (0 : E) 1 := by
  obtain ⟨A, _, h1, h2⟩ := ConvexGeom.john_theorem K hint
  exact ⟨A, h1, h2⟩

theorem john_theorem_symmetric {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (K : ConvexBody E) (hsym : ∀ x ∈ (K : Set E), -x ∈ (K : Set E))
    (h0 : (0 : E) ∈ interior (K : Set E)) :
    ∃ T : E ≃ₗ[ℝ] E,
      Metric.closedBall (0 : E) 1 ⊆ T '' (K : Set E) ∧
      T '' (K : Set E) ⊆ Real.sqrt (Module.finrank ℝ E : ℝ) • Metric.closedBall (0 : E) 1 := by
  obtain ⟨T, _, h1, h2⟩ := ConvexGeom.john_theorem_symmetric K hsym h0
  exact ⟨T, h1, h2⟩

theorem loomis_whitney {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} (b : OrthonormalBasis (Fin (n + 2)) ℝ E) {K : Set E} (hKc : IsCompact K) :
    volume K ^ (n + 1) ≤
      ∏ i : Fin (n + 2),
        volume ((fun x : E => Fin.removeNth i (WithLp.ofLp (b.repr x))) '' K) :=
  ConvexGeom.loomis_whitney b hKc

private lemma mk_john_decomp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] {u : ι → E} {c : ι → ℝ}
    (hu : ∀ i, ‖u i‖ = 1) (hc : ∀ i, 0 < c i)
    (hid : ∀ x : E, ∑ i, (c i * ⟪u i, x⟫) • u i = x) :
    ConvexGeom.IsJohnDecomposition u c := by
  refine ⟨hu, hc, ?_⟩
  ext x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, ConvexGeom.rankOne_apply, smul_smul,
    LinearMap.id_coe, id_eq]
  simpa [real_inner_comm] using hid x

theorem brascamp_lieb_rankOne {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} [Fintype ι] {u : ι → E} {c : ι → ℝ}
    (hu : ∀ i, ‖u i‖ = 1) (hc : ∀ i, 0 < c i)
    (hid : ∀ x : E, ∑ i, (c i * ⟪u i, x⟫) • u i = x)
    {f : ι → ℝ → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : E, ∏ i, f i ⟪x, u i⟫ ^ c i ≤ ∏ i, (∫⁻ t : ℝ, f i t) ^ c i :=
  ConvexGeom.brascamp_lieb_rankOne (mk_john_decomp hu hc hid) hf

theorem reverse_brascamp_lieb_rankOne {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} [Fintype ι] {u : ι → E} {c : ι → ℝ}
    (hu : ∀ i, ‖u i‖ = 1) (hc : ∀ i, 0 < c i)
    (hid : ∀ x : E, ∑ i, (c i * ⟪u i, x⟫) • u i = x)
    {I : ι → Set ℝ} (hIopen : ∀ i, IsOpen (I i)) (hIconn : ∀ i, IsPreconnected (I i))
    (hIne : ∀ i, (I i).Nonempty)
    {f : ι → ℝ → ℝ} (hf_cont : ∀ i, ContinuousOn (f i) (I i))
    (hf_pos : ∀ i, ∀ t ∈ I i, 0 < f i t) (hf_int : ∀ i, IntegrableOn (f i) (I i) volume)
    {H : E → ℝ≥0∞}
    (hdom : ∀ y : ι → ℝ, (∀ i, y i ∈ I i) →
      ∏ i, ENNReal.ofReal (f i (y i)) ^ c i ≤ H (∑ i, (c i * y i) • u i)) :
    ∏ i, ENNReal.ofReal (∫ t in I i, f i t) ^ c i ≤ ∫⁻ z : E, H z :=
  ConvexGeom.reverse_brascamp_lieb_rankOne (mk_john_decomp hu hc hid)
    hIopen hIconn hIne hf_cont hf_pos hf_int hdom

theorem ball_volume_ratio_symmetric {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (K : ConvexBody E) (hsym : ∀ x ∈ (K : Set E), -x ∈ (K : Set E))
    (h0 : (0 : E) ∈ interior (K : Set E)) :
    ∃ T : E ≃ₗ[ℝ] E,
      Metric.closedBall (0 : E) 1 ⊆ T '' (K : Set E) ∧
      volume (T '' (K : Set E)) ≤ (2 : ℝ≥0∞) ^ Module.finrank ℝ E :=
  ConvexGeom.ball_volume_ratio_symmetric K hsym h0

theorem ball_volume_ratio {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (K : ConvexBody E) (hint : (interior (K : Set E)).Nonempty) :
    ∃ e : E ≃ᵃ[ℝ] E,
      Metric.closedBall (0 : E) 1 ⊆ e '' (K : Set E) ∧
      volume (e '' (K : Set E)) ≤
        ENNReal.ofReal ((Module.finrank ℝ E : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2) *
          ((Module.finrank ℝ E : ℝ) + 1) ^ (((Module.finrank ℝ E : ℝ) + 1) / 2) /
          (Nat.factorial (Module.finrank ℝ E) : ℝ)) :=
  ConvexGeom.ball_volume_ratio K hint

theorem ball_reverse_isoperimetric_symmetric {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [BorelSpace E]
    (K : ConvexBody E) (hsym : ∀ x ∈ (K : Set E), -x ∈ (K : Set E))
    (h0 : (0 : E) ∈ interior (K : Set E)) :
    ∃ T : E ≃ₗ[ℝ] E,
      minkowskiSurfaceArea (T '' (K : Set E)) ≤
        (2 * (Module.finrank ℝ E : ℝ≥0∞)) *
          volume (T '' (K : Set E)) ^ (((Module.finrank ℝ E - 1 : ℕ) : ℝ) / (Module.finrank ℝ E : ℝ)) :=
  ConvexGeom.ball_reverse_isoperimetric_symmetric K hsym h0

theorem ball_reverse_isoperimetric {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (K : ConvexBody E) (hint : (interior (K : Set E)).Nonempty) :
    ∃ e : E ≃ᵃ[ℝ] E,
      minkowskiSurfaceArea (e '' (K : Set E)) ≤
        (Module.finrank ℝ E : ℝ≥0∞) *
          ENNReal.ofReal ((Module.finrank ℝ E : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2) *
            ((Module.finrank ℝ E : ℝ) + 1) ^ (((Module.finrank ℝ E : ℝ) + 1) / 2) /
            (Nat.factorial (Module.finrank ℝ E) : ℝ)) ^ (1 / (Module.finrank ℝ E : ℝ)) *
          volume (e '' (K : Set E)) ^ (((Module.finrank ℝ E - 1 : ℕ) : ℝ) / (Module.finrank ℝ E : ℝ)) :=
  ConvexGeom.ball_reverse_isoperimetric K hint

theorem gaussian_lipschitz_concentration {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {L : ℝ≥0} (hL : 0 < L) {f : E → ℝ} (hf : LipschitzWith L f) {t : ℝ} (ht : 0 ≤ t) :
    stdGaussian E {x : E | t ≤ |f x - ∫ y : E, f y ∂stdGaussian E|} ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (4 * (L : ℝ) ^ 2))) :=
  ConvexGeom.gaussian_lipschitz_concentration_mean hL hf ht

theorem spherical_lipschitz_concentration {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [BorelSpace E]
    {L : ℝ≥0} (hL : 0 < L) {f : Metric.sphere (0 : E) 1 → ℝ} (hf : LipschitzWith L f) {m : ℝ}
    (hm_le : ENNReal.ofReal (1 / 2 : ℝ) ≤ sphereProb (E := E) {u | f u ≤ m})
    (hm_ge : ENNReal.ofReal (1 / 2 : ℝ) ≤ sphereProb (E := E) {u | m ≤ f u})
    {t : ℝ} (ht : 0 ≤ t) :
    sphereProb (E := E) {u | t < |f u - m|} ≤
      ENNReal.ofReal (576 * Real.exp (-(Module.finrank ℝ E : ℝ) * t ^ 2 / (8 * (L : ℝ) ^ 2))) :=
  ConvexGeom.spherical_lipschitz_concentration_median hL hf hm_le hm_ge ht

theorem johnson_lindenstrauss {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {N k : ℕ} (x : Fin N → E) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hk : (16 : ℝ) * Real.log (N : ℝ) / ε ^ 2 ≤ (k : ℝ)) :
    ∃ L : E →ₗ[ℝ] EuclideanSpace ℝ (Fin k),
      ∀ i j : Fin N,
        (1 - ε) * ‖x i - x j‖ ^ 2 ≤ ‖L (x i) - L (x j)‖ ^ 2 ∧
        ‖L (x i) - L (x j)‖ ^ 2 ≤ (1 + ε) * ‖x i - x j‖ ^ 2 :=
  ConvexGeom.johnson_lindenstrauss x hε0 hε1 hk

theorem dvoretzky_theorem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : ConvexBody E) (hsym : ∀ x ∈ (K : Set E), -x ∈ (K : Set E))
    (h0 : (0 : E) ∈ interior (K : Set E)) (hd2 : 2 ≤ Module.finrank ℝ E)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {k : ℕ}
    (hk_bd : (8192 : ℝ) * (k : ℝ) * Real.log (48 / ε) ≤
      ε ^ 2 * Real.log (Module.finrank ℝ E : ℝ)) :
    ∃ (F : Submodule ℝ E) (T : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] F),
      Module.finrank ℝ F = k ∧
      (∀ w : EuclideanSpace ℝ (Fin k),
        ‖w‖ ≤ gauge (K : Set E) (T w : E) ∧ gauge (K : Set E) (T w : E) ≤ (1 + ε) * ‖w‖) ∧
      ((1 + ε)⁻¹ • ((F.subtype.comp T.toLinearMap) '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) ⊆
          (K : Set E) ∩ (F : Set E) ∧
        (K : Set E) ∩ (F : Set E) ⊆
          (F.subtype.comp T.toLinearMap) '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) :=
  ConvexGeom.dvoretzky_theorem K hsym h0 hd2 hε0 hε1 hk_bd

theorem blaschke_santalo {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (K : ConvexBody E) (hne : (interior (K : Set E)).Nonempty) :
    ∃ z ∈ interior (K : Set E),
      volume (K : Set E) * volume {y : E | ∀ x ∈ (K : Set E), ⟪x - z, y⟫ ≤ 1} ≤
        volume (Metric.closedBall (0 : E) 1) ^ 2 := by
  obtain ⟨z, hz, hmin⟩ := ConvexGeom.exists_santaloPoint K hne
  refine ⟨z, hz, ?_⟩
  have hle : ConvexGeom.mahlerVolumeAt (volume : Measure E) (K : Set E) z ≤
      volume (Metric.closedBall (0 : E) 1) ^ 2 :=
    hmin.trans_le (ConvexGeom.blaschke_santalo K hne)
  have hvol_eq : volume ((fun x : E => x - z) '' (K : Set E)) = volume (K : Set E) := by
    have hpre : (fun x : E => x - z) '' (K : Set E) = (fun x : E => z + x) ⁻¹' (K : Set E) := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      exact ⟨fun ⟨x, hx, hxy⟩ => by rw [← hxy]; simpa [add_sub_cancel] using hx,
        fun hy => ⟨z + y, hy, by abel⟩⟩
    rw [hpre, MeasureTheory.measure_preimage_add]
  have hpol_eq : ConvexGeom.polarBody ((fun x : E => x - z) '' (K : Set E)) =
      {y : E | ∀ x ∈ (K : Set E), ⟪x - z, y⟫ ≤ 1} := by
    ext y
    simp [ConvexGeom.polarBody]
  unfold ConvexGeom.mahlerVolumeAt ConvexGeom.mahlerVolume at hle
  rwa [hvol_eq, hpol_eq] at hle

theorem blaschke_santalo_symmetric {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (K : ConvexBody E) (hsym : ∀ x ∈ (K : Set E), -x ∈ (K : Set E))
    (h0 : (0 : E) ∈ interior (K : Set E)) :
    volume (K : Set E) * volume {y : E | ∀ x ∈ (K : Set E), ⟪x, y⟫ ≤ 1} ≤
      volume (Metric.closedBall (0 : E) 1) ^ 2 :=
  ConvexGeom.blaschke_santalo_symmetric K hsym h0

theorem dual_urysohn_inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (K : ConvexBody E) (h0 : (0 : E) ∈ interior (K : Set E)) :
    (volume.real (Metric.closedBall (0 : E) 1) /
        volume.real {y : E | ∀ x ∈ (K : Set E), ⟪x, y⟫ ≤ 1}) ^
        (1 / (Module.finrank ℝ E : ℝ)) ≤
      meanWidth K :=
  ConvexGeom.dual_urysohn_inequality K h0

theorem urysohn_inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (K : ConvexBody E) :
    (volume.real (K : Set E) / volume.real (Metric.closedBall (0 : E) 1)) ^
        (1 / (Module.finrank ℝ E : ℝ)) ≤
      meanWidth K :=
  ConvexGeom.urysohn_inequality K

end ConvexGeomChallenge

end
