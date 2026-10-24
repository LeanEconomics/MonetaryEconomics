/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.QuadraticRoots
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field

/-!
# The cubic lag polynomial of the inflation-inertia model

Woodford (2003), *Interest and Prices*, Chapter 8, §3.2, pp. 593–598, eqs. (3.17), (3.20);
Appendix G, §G.3 (Lemmas G.1 and G.2, pp. 719–720) and §G.6 (proof of Proposition 8.7,
pp. 724–727).

The cubic `A(z) = βγ − (1 + γ + βγ)z + (1 + γ + β⁻¹(1 + κσ))z² − β⁻¹z³` of (3.17) is studied
through its reciprocal `P(λ) = λ³A(1/λ)`, whose roots are the `λⱼ` of the factorization (3.20).

## Main results

* `lemma_G1` (Lemma G.1, any field of characteristic 0); the shape facts of App. G.6:
  `Apoly_pos_of_nonpos`, `Aderiv_neg_of_nonpos`, `Apoly_beta`, `Aderiv_beta`, `Apoly_one`,
  `tendsto_Apoly_atTop`.
* The canonical roots: `lam1` (the unique real root of `P` in `(−∞, 1]`, `lam1_unique`),
  `lam2 = (S − √(S² − 4P₂₃))/2`, `lam3 = (S + √(S² − 4P₂₃))/2` (complex square root `csqrt`),
  with `S = sumS`, `P₂₃ = prodP`; the factorization `ApolyC_factor` (3.20)/(G.16); Vieta
  `vieta_G19`, `vieta_G20`, `vieta_G18_pair`, `gamma_mul_lam3`; `vieta_of_factor` and
  `factorization_unique` (any factorization is the canonical one up to `λ₂ ↔ λ₃`).
* **Proposition 8.7**: `prop_8_7`; the real case `one_lt_lam2r`, `lam2r_le_lam3r`; the complex
  case `lam3_eq_conj`, `lam2_complex` (`Re λ₂ = S/2 > 1`); `one_lt_norm_lam2`,
  `one_lt_norm_lam3`.
* Survey E20: `no_two_roots_gt_one_of_shape` shows the shape facts the book lists (with
  `A′(β) > 0`) already exclude two roots `z > 1`, so the printed argument is complete once this
  step is written out (`Apoly_unique_root_gt_one`); the Vieta closure
  `vieta_excludes_three_roots_gt_one` (`z₁z₂z₃ = β²γ < 1`) is also proved.
* The discriminant: `delta_eq_bracket`, `deltaG_eq_quartic` (the printed quartic is correct),
  `deltaG_factor` (`Δ = −β⁴(βγ)⁴q(λ₁)²(S² − 4P₂₃)`), Cardano's cases `three_distinct_real_iff`,
  `repeated_root_iff`, `complex_pair_iff`, `ApolyC_eq_zero_iff_depressed`,
  `lam_real_iff_zeta_real`; `deltaQuartic_zero`, `deltaQuartic_one` and their signs,
  `tendsto_deltaQuartic`, `deltaQuartic_exists_root`, `deltaQuartic_exists_root_gt_one`;
  `three_real_roots_small_gamma`, `complex_pair_near_one`.
* The threshold at the Table 6.1 calibration: `calib_gamma_bar` (`γ̄ ∈ (.3533, .3534)`, unique,
  `Δ < 0` below, `Δ > 0` above).
* Continuity in `γ`: `tendsto_root_of_sign`, `continuousOn_lam1`, `continuousOn_sumS`,
  `continuousOn_prodP`, `continuousOn_lam2`, `continuousOn_lam3`.
* **Lemma G.2** (survey E22: the boundedness of `λ₁, λ₂` the book assumes is proved):
  `tendsto_lam1_zero` (`λ₁ → μ₁`), `tendsto_lam2r_zero` (`λ₂ → μ₂`), `tendsto_lam3r_atTop`,
  `tendsto_gamma_mul_lam3r` (`γλ₃ → β⁻¹`), packaged as `lemma_G2`; `μ₁, μ₂` are the roots of
  (3.10) (`mu_sum`, `mu_prod`, `mu_bounds`).
-/

namespace Woodford.OptimalPolicyRules.CubicRoots

open Filter Topology

/-! ### The polynomial `A(z)` and Lemma G.1 -/

/-- Woodford (2003), eq. (3.17), p. 593, and App. G.6, p. 726: the coefficient `A₀ = βγ`. -/
def coefA0 (β γ : ℝ) : ℝ := β * γ

/-- Woodford (2003), App. G.6, p. 726: the coefficient `A₁ = −(1 + γ + βγ)`. -/
def coefA1 (β γ : ℝ) : ℝ := -(1 + γ + β * γ)

/-- Woodford (2003), App. G.6, p. 726: the coefficient `A₂ = 1 + γ + β⁻¹(1 + κσ)`. -/
noncomputable def coefA2 (β γ κ σ : ℝ) : ℝ := 1 + γ + β⁻¹ * (1 + κ * σ)

/-- Woodford (2003), App. G.6, p. 726: the coefficient `A₃ = −β⁻¹`. -/
noncomputable def coefA3 (β : ℝ) : ℝ := -β⁻¹

/-- Woodford (2003), eq. (3.17), p. 593 = (G.17), p. 724: the cubic
`A(z) = βγ − (1 + γ + βγ) z + (1 + γ + β⁻¹(1 + κσ)) z² − β⁻¹ z³`. -/
noncomputable def Apoly (β γ κ σ z : ℝ) : ℝ :=
  coefA0 β γ + coefA1 β γ * z + coefA2 β γ κ σ * z ^ 2 + coefA3 β * z ^ 3

/-- Woodford (2003), eq. (3.17), p. 593: the same cubic evaluated at a complex argument. -/
noncomputable def ApolyC (β γ κ σ : ℝ) (z : ℂ) : ℂ :=
  (coefA0 β γ : ℂ) + (coefA1 β γ : ℂ) * z + (coefA2 β γ κ σ : ℂ) * z ^ 2 + (coefA3 β : ℂ) * z ^ 3

/-- Woodford (2003), eq. (3.17), p. 593: `A` at a real argument is the real cubic. -/
theorem ApolyC_ofReal (β γ κ σ z : ℝ) : ApolyC β γ κ σ (z : ℂ) = (Apoly β γ κ σ z : ℂ) := by
  simp only [ApolyC, Apoly]
  push_cast
  ring

/-- Woodford (2003), App. G.6, p. 724: the derivative `A′(z) = A₁ + 2A₂ z + 3A₃ z²`. -/
noncomputable def Aderiv (β γ κ σ z : ℝ) : ℝ :=
  coefA1 β γ + 2 * coefA2 β γ κ σ * z + 3 * coefA3 β * z ^ 2

/-- Woodford (2003), App. G.6, p. 724: `A′` is the derivative of `A`. -/
theorem hasDerivAt_Apoly (β γ κ σ z : ℝ) :
    HasDerivAt (Apoly β γ κ σ) (Aderiv β γ κ σ z) z := by
  have h1 : HasDerivAt (fun z => coefA1 β γ * z) (coefA1 β γ * 1) z :=
    (hasDerivAt_id z).const_mul _
  have h2 : HasDerivAt (fun z => coefA2 β γ κ σ * z ^ 2)
      (coefA2 β γ κ σ * ((2 : ℕ) * z ^ (2 - 1))) z := (hasDerivAt_pow 2 z).const_mul _
  have h3 : HasDerivAt (fun z => coefA3 β * z ^ 3) (coefA3 β * ((3 : ℕ) * z ^ (3 - 1))) z :=
    (hasDerivAt_pow 3 z).const_mul _
  have h := HasDerivAt.add (HasDerivAt.add (HasDerivAt.const_add (coefA0 β γ) h1) h2) h3
  refine HasDerivAt.congr_deriv h ?_
  simp only [Aderiv]
  push_cast
  ring

/-- Woodford (2003), Lemma G.1, p. 719: the constant term
`B₀ = (27A₀A₃² + 2A₂³ − 9A₃A₂A₁)/(27A₃³)` of the depressed cubic. -/
def depB0 {K : Type*} [Field K] (A0 A1 A2 A3 : K) : K :=
  (27 * A0 * A3 ^ 2 + 2 * A2 ^ 3 - 9 * A3 * A2 * A1) / (27 * A3 ^ 3)

/-- Woodford (2003), Lemma G.1, p. 719: the linear coefficient `B₁ = (3A₃A₁ − A₂²)/(3A₃²)` of
the depressed cubic. -/
def depB1 {K : Type*} [Field K] (A1 A2 A3 : K) : K := (3 * A3 * A1 - A2 ^ 2) / (3 * A3 ^ 2)

/-- Woodford (2003), **Lemma G.1**, pp. 719–720: with `ζ = z + A₂/(3A₃)`,
`A₃z³ + A₂z² + A₁z + A₀ = A₃(B₀ + B₁ζ + ζ³)` (any field of characteristic zero, `A₃ ≠ 0`). -/
theorem lemma_G1 {K : Type*} [Field K] [CharZero K] (A0 A1 A2 A3 z : K) (h3 : A3 ≠ 0) :
    A3 * z ^ 3 + A2 * z ^ 2 + A1 * z + A0 =
      A3 * (depB0 A0 A1 A2 A3 + depB1 A1 A2 A3 * (z + A2 / (3 * A3)) +
        (z + A2 / (3 * A3)) ^ 3) := by
  unfold depB0 depB1
  field_simp
  ring

/-! ### Standing assumptions and the shape facts of App. G.6 -/

namespace Assumptions

variable (β γ κ σ : ℝ)

/-- Woodford (2003), Proposition 8.7, p. 594: the standing assumptions `σ, κ > 0`, `0 < β < 1`
and `0 < γ ≤ 1`. -/
structure Standing where
  sigma_pos : 0 < σ
  kappa_pos : 0 < κ
  beta_pos : 0 < β
  beta_lt_one : β < 1
  gamma_pos : 0 < γ
  gamma_le_one : γ ≤ 1

end Assumptions

open Assumptions

variable {β γ κ σ : ℝ}

/-- Woodford (2003), App. G.6, p. 724: `κσ > 0` under the standing assumptions. -/
theorem Assumptions.Standing.kappa_sigma_pos (h : Standing β γ κ σ) : 0 < κ * σ :=
  mul_pos h.kappa_pos h.sigma_pos

/-- Woodford (2003), App. G.6, p. 724: `A₂ > 0`. -/
theorem coefA2_pos (h : Standing β γ κ σ) : 0 < coefA2 β γ κ σ := by
  have := h.kappa_sigma_pos
  have := h.beta_pos
  have := h.gamma_pos
  unfold coefA2
  positivity

/-- Woodford (2003), App. G.6, p. 724: `A(z) > 0` for all `z ≤ 0`. -/
theorem Apoly_pos_of_nonpos (h : Standing β γ κ σ) {z : ℝ} (hz : z ≤ 0) :
    0 < Apoly β γ κ σ z := by
  have hβ := h.beta_pos
  have hγ := h.gamma_pos
  have hA2 := coefA2_pos h
  have h0 : 0 < coefA0 β γ := mul_pos hβ hγ
  have h1 : 0 ≤ coefA1 β γ * z :=
    mul_nonneg_of_nonpos_of_nonpos (by unfold coefA1; nlinarith) hz
  have h2 : 0 ≤ coefA2 β γ κ σ * z ^ 2 := by positivity
  have h3 : 0 ≤ coefA3 β * z ^ 3 := by
    have hz3 : z ^ 3 ≤ 0 := by
      have : 0 ≤ (-z) ^ 3 := pow_nonneg (by linarith) 3
      nlinarith [this]
    exact mul_nonneg_of_nonpos_of_nonpos (by unfold coefA3; simp [hβ.le]) hz3
  unfold Apoly
  linarith

/-- Woodford (2003), App. G.6, p. 724: `A′(z) < 0` for all `z ≤ 0`. -/
theorem Aderiv_neg_of_nonpos (h : Standing β γ κ σ) {z : ℝ} (hz : z ≤ 0) :
    Aderiv β γ κ σ z < 0 := by
  have hβ := h.beta_pos
  have hγ := h.gamma_pos
  have hA2 := coefA2_pos h
  have h1 : coefA1 β γ < 0 := by unfold coefA1; nlinarith
  have h2 : 2 * coefA2 β γ κ σ * z ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hz
  have h3 : 3 * coefA3 β * z ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by unfold coefA3; simp [hβ.le]) (sq_nonneg z)
  unfold Aderiv
  linarith

/-- Woodford (2003), App. G.6, p. 724: `A(β) = βκσ`. -/
theorem Apoly_beta (hβ : β ≠ 0) : Apoly β γ κ σ β = β * κ * σ := by
  unfold Apoly coefA0 coefA1 coefA2 coefA3
  field_simp
  ring

/-- Woodford (2003), App. G.6, p. 724: `A′(β) = (1 − β)(1 − γ) + 2κσ`. -/
theorem Aderiv_beta (hβ : β ≠ 0) : Aderiv β γ κ σ β = (1 - β) * (1 - γ) + 2 * κ * σ := by
  unfold Aderiv coefA1 coefA2 coefA3
  field_simp
  ring

/-- Woodford (2003), App. G.6, p. 724: `A(1) = β⁻¹κσ`. -/
theorem Apoly_one : Apoly β γ κ σ 1 = β⁻¹ * (κ * σ) := by
  unfold Apoly coefA0 coefA1 coefA2 coefA3
  ring

/-- Woodford (2003), App. G.6, p. 724: `A(β) > 0`. -/
theorem Apoly_beta_pos (h : Standing β γ κ σ) : 0 < Apoly β γ κ σ β := by
  rw [Apoly_beta h.beta_pos.ne']
  have := h.kappa_sigma_pos
  have := h.beta_pos
  rw [mul_assoc]
  positivity

/-- Woodford (2003), App. G.6, p. 724: `A′(β) > 0`. -/
theorem Aderiv_beta_pos (h : Standing β γ κ σ) : 0 < Aderiv β γ κ σ β := by
  rw [Aderiv_beta h.beta_pos.ne']
  have := h.kappa_sigma_pos
  have : 0 ≤ (1 - β) * (1 - γ) :=
    mul_nonneg (by linarith [h.beta_lt_one]) (by linarith [h.gamma_le_one])
  nlinarith

/-- Woodford (2003), App. G.6, p. 724: `A(1) > 0`. -/
theorem Apoly_one_pos (h : Standing β γ κ σ) : 0 < Apoly β γ κ σ 1 := by
  rw [Apoly_one]
  have := h.kappa_sigma_pos
  have := h.beta_pos
  positivity

/-- Woodford (2003), App. G.6, p. 724: `A(+∞) = −∞`. -/
theorem tendsto_Apoly_atTop (hβ : 0 < β) : Tendsto (Apoly β γ κ σ) atTop atBot := by
  have hg : Tendsto (fun z : ℝ => coefA3 β + coefA2 β γ κ σ * z⁻¹ + coefA1 β γ * (z⁻¹) ^ 2 +
      coefA0 β γ * (z⁻¹) ^ 3) atTop (𝓝 (coefA3 β + coefA2 β γ κ σ * 0 + coefA1 β γ * 0 ^ 2 +
        coefA0 β γ * 0 ^ 3)) := by
    have hi := tendsto_inv_atTop_zero (𝕜 := ℝ)
    exact (((tendsto_const_nhds.add (hi.const_mul _)).add ((hi.pow 2).const_mul _)).add
      ((hi.pow 3).const_mul _))
  simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at hg
  have hA3 : coefA3 β < 0 := by unfold coefA3; simp [hβ]
  have h3 := (tendsto_pow_atTop (α := ℝ) (n := 3) (by norm_num)).atTop_mul_neg hA3 hg
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
  unfold Apoly
  field_simp
  ring

/-! ### The reciprocal polynomial and the root `λ₁ ∈ (0, 1)` -/

/-- Woodford (2003), App. G.6, p. 725: the reciprocal cubic `P(λ) = λ³ A(1/λ)`,
`P(λ) = βγλ³ − (1 + γ + βγ)λ² + A₂λ − β⁻¹`, whose roots are the `λⱼ = zⱼ⁻¹` of (G.16). -/
noncomputable def Precip (β γ κ σ l : ℝ) : ℝ :=
  β * γ * l ^ 3 - (1 + γ + β * γ) * l ^ 2 + coefA2 β γ κ σ * l - β⁻¹

/-- Woodford (2003), App. G.6, p. 725: `A(λ⁻¹) = P(λ)/λ³`, so `z = λ⁻¹` is a root of `A` iff
`λ` is a root of `P` (`λⱼ ≡ zⱼ⁻¹`). -/
theorem Apoly_inv {l : ℝ} (hl : l ≠ 0) : Apoly β γ κ σ l⁻¹ = Precip β γ κ σ l / l ^ 3 := by
  unfold Apoly Precip coefA0 coefA1 coefA3
  field_simp
  ring

/-- Woodford (2003), App. G.6, p. 725: for `z ≠ 0`, `A(z) = 0 ↔ P(z⁻¹) = 0`. -/
theorem Apoly_eq_zero_iff {z : ℝ} (hz : z ≠ 0) :
    Apoly β γ κ σ z = 0 ↔ Precip β γ κ σ z⁻¹ = 0 := by
  have h := Apoly_inv (β := β) (γ := γ) (κ := κ) (σ := σ) (inv_ne_zero hz)
  rw [inv_inv] at h
  rw [h, div_eq_zero_iff]
  simp [hz]

/-- Woodford (2003), App. G.6, p. 724: `P(0) = −β⁻¹`. -/
theorem Precip_zero : Precip β γ κ σ 0 = -β⁻¹ := by
  unfold Precip
  ring

/-- Woodford (2003), App. G.6, p. 724: `P(1) = A(1) = β⁻¹κσ`. -/
theorem Precip_one : Precip β γ κ σ 1 = β⁻¹ * (κ * σ) := by
  unfold Precip coefA2
  ring

/-- Woodford (2003), App. G.6, pp. 724–725: `P` has a root in `(0, 1)` (by the
intermediate value theorem; equivalently `A` has a root `z₁ > 1`). -/
theorem exists_root_Ioo (h : Standing β γ κ σ) :
    ∃ l, 0 < l ∧ l < 1 ∧ Precip β γ κ σ l = 0 := by
  have hc : ContinuousOn (Precip β γ κ σ) (Set.Icc 0 1) := by
    unfold Precip
    fun_prop
  have hβ := h.beta_pos
  have h0 : Precip β γ κ σ 0 < 0 := by
    rw [Precip_zero]
    simp [hβ]
  have h1 : 0 < Precip β γ κ σ 1 := by
    rw [Precip_one]
    have := h.kappa_sigma_pos
    positivity
  obtain ⟨l, ⟨hl0, hl1⟩, hl⟩ := intermediate_value_Ioo zero_le_one hc ⟨h0, h1⟩
  exact ⟨l, hl0, hl1, hl⟩

/-- Woodford (2003), Prop. 8.7, p. 594, and (G.16): the real root `0 < λ₁ < 1` (a root of `P`
in `(0, 1)`, chosen by `Classical.epsilon`; it is unique by `lam1_unique`). -/
noncomputable def lam1 (β γ κ σ : ℝ) : ℝ :=
  Classical.epsilon (fun l => 0 < l ∧ l < 1 ∧ Precip β γ κ σ l = 0)

/-- Woodford (2003), Prop. 8.7, p. 594: `0 < λ₁ < 1` and `P(λ₁) = 0`. -/
theorem lam1_spec (h : Standing β γ κ σ) :
    0 < lam1 β γ κ σ ∧ lam1 β γ κ σ < 1 ∧ Precip β γ κ σ (lam1 β γ κ σ) = 0 :=
  Classical.epsilon_spec (exists_root_Ioo h)

/-- Woodford (2003), (G.20), p. 725: `S = λ₂ + λ₃ = (1 + γ + βγ)/(βγ) − λ₁`. -/
noncomputable def sumS (β γ κ σ : ℝ) : ℝ := (1 + γ + β * γ) / (β * γ) - lam1 β γ κ σ

/-- Woodford (2003), (G.18), p. 725: `P₂₃ = λ₂λ₃ = A₂/(βγ) − Sλ₁` (the `L²` coefficient). -/
noncomputable def prodP (β γ κ σ : ℝ) : ℝ :=
  coefA2 β γ κ σ / (β * γ) - sumS β γ κ σ * lam1 β γ κ σ

/-- Woodford (2003), App. G.6, p. 726: the discriminant `S² − 4P₂₃` of the quadratic
`λ² − Sλ + P₂₃` whose roots are `λ₂, λ₃`. -/
noncomputable def discQ (β γ κ σ : ℝ) : ℝ := sumS β γ κ σ ^ 2 - 4 * prodP β γ κ σ

/-- Woodford (2003), (G.18), p. 725: the identity
`P(λ) = βγ(λ − λ₁)(λ² − Sλ + P₂₃) + (βγλ₁P₂₃ − β⁻¹)` (pure algebra, `βγ ≠ 0`). -/
theorem Precip_eq_factor_add (hβ : β ≠ 0) (hγ : γ ≠ 0) (l : ℝ) :
    Precip β γ κ σ l = β * γ * (l - lam1 β γ κ σ) *
        (l ^ 2 - sumS β γ κ σ * l + prodP β γ κ σ) +
      (β * γ * lam1 β γ κ σ * prodP β γ κ σ - β⁻¹) := by
  unfold Precip prodP sumS
  field_simp
  ring

/-- Woodford (2003), (G.19), p. 725 (form used below): `βγ λ₁ P₂₃ = β⁻¹`. -/
theorem vieta_const (h : Standing β γ κ σ) :
    β * γ * lam1 β γ κ σ * prodP β γ κ σ = β⁻¹ := by
  have h1 := Precip_eq_factor_add (κ := κ) (σ := σ) h.beta_pos.ne' h.gamma_pos.ne'
    (lam1 β γ κ σ)
  rw [(lam1_spec h).2.2, sub_self, mul_zero, zero_mul, zero_add] at h1
  linarith

/-- Woodford (2003), (G.16)/(G.18), p. 725: `P(λ) = βγ(λ − λ₁)(λ² − Sλ + P₂₃)`. -/
theorem Precip_factor (h : Standing β γ κ σ) (l : ℝ) :
    Precip β γ κ σ l = β * γ * (l - lam1 β γ κ σ) *
      (l ^ 2 - sumS β γ κ σ * l + prodP β γ κ σ) := by
  rw [Precip_eq_factor_add h.beta_pos.ne' h.gamma_pos.ne', vieta_const h, sub_self, add_zero]

/-- Woodford (2003), (G.20), p. 725: `βγ(λ₁ + S) = 1 + γ + βγ`. -/
theorem vieta_sum (h : Standing β γ κ σ) :
    β * γ * (lam1 β γ κ σ + sumS β γ κ σ) = 1 + γ + β * γ := by
  have hβ := h.beta_pos.ne'
  have hγ := h.gamma_pos.ne'
  unfold sumS
  field_simp
  ring

/-- Woodford (2003), (G.18), p. 725: `βγ(P₂₃ + Sλ₁) = A₂`. -/
theorem vieta_pair (h : Standing β γ κ σ) :
    β * γ * (prodP β γ κ σ + sumS β γ κ σ * lam1 β γ κ σ) = coefA2 β γ κ σ := by
  have hβ := h.beta_pos.ne'
  have hγ := h.gamma_pos.ne'
  unfold prodP
  field_simp
  ring

/-- Woodford (2003), App. G.6, p. 725: `λ₂ + λ₃ > 2/β` (the book shows `> 1 + β⁻¹ > 2`). -/
theorem two_div_lt_sumS (h : Standing β γ κ σ) : 2 / β < sumS β γ κ σ := by
  have hβ := h.beta_pos
  have hγ := h.gamma_pos
  have e : (1 + γ + β * γ) / (β * γ) = (1 / γ + 1) / β + 1 := by
    field_simp
  have h1 : 1 ≤ 1 / γ := by rw [le_div_iff₀ hγ]; linarith [h.gamma_le_one]
  have h2 : 2 / β ≤ (1 / γ + 1) / β := by gcongr; linarith
  have h3 := (lam1_spec h).2.1
  unfold sumS
  rw [e]
  linarith

/-- Woodford (2003), App. G.6, p. 725: `λ₂ + λ₃ > 1 + β⁻¹`, the book's bound. -/
theorem one_add_inv_lt_sumS (h : Standing β γ κ σ) : 1 + β⁻¹ < sumS β γ κ σ := by
  have hβ := h.beta_pos
  have hγ := h.gamma_pos
  have e : (1 + γ + β * γ) / (β * γ) = (1 / γ) / β + β⁻¹ + 1 := by
    field_simp
  have h1 : 1 ≤ 1 / γ := by rw [le_div_iff₀ hγ]; linarith [h.gamma_le_one]
  have h2 : 1 / β ≤ (1 / γ) / β := by gcongr
  have h3 := (lam1_spec h).2.1
  have h4 : 1 < 1 / β := by rw [lt_div_iff₀ hβ]; linarith [h.beta_lt_one]
  unfold sumS
  rw [e]
  linarith

/-- Woodford (2003), App. G.6, p. 725: `λ₂ + λ₃ > 2`. -/
theorem two_lt_sumS (h : Standing β γ κ σ) : 2 < sumS β γ κ σ := by
  have h1 := two_div_lt_sumS h
  have h2 : 2 < 2 / β := by rw [lt_div_iff₀ h.beta_pos]; linarith [h.beta_lt_one]
  linarith

/-- Woodford (2003), App. G.6, p. 725: the quadratic factor is positive at `1`:
`1 − S + P₂₃ > 0` (because `P(1) = βγ(1 − λ₁)(1 − S + P₂₃) > 0`). -/
theorem quad_one_pos (h : Standing β γ κ σ) : 0 < 1 - sumS β γ κ σ + prodP β γ κ σ := by
  have hP1 : 0 < Precip β γ κ σ 1 := by
    rw [Precip_one]
    have := h.kappa_sigma_pos
    have := h.beta_pos
    positivity
  rw [Precip_factor h] at hP1
  have hpos : 0 < β * γ * (1 - lam1 β γ κ σ) :=
    mul_pos (mul_pos h.beta_pos h.gamma_pos) (by linarith [(lam1_spec h).2.1])
  have := pos_of_mul_pos_right hP1 hpos.le
  linarith

/-- Woodford (2003), App. G.6, p. 725: the quadratic factor `λ² − Sλ + P₂₃` is positive for
every real `λ ≤ 1`. -/
theorem quad_pos_of_le_one (h : Standing β γ κ σ) {l : ℝ} (hl : l ≤ 1) :
    0 < l ^ 2 - sumS β γ κ σ * l + prodP β γ κ σ := by
  have h1 := quad_one_pos h
  have h2 := two_lt_sumS h
  have h3 : 0 ≤ (l - 1) * (l + 1 - sumS β γ κ σ) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  nlinarith

/-- Woodford (2003), Prop. 8.7, p. 594: `λ₁` is the ONLY real root of `P` in `(−∞, 1]` (so
the real root `0 < λ₁ < 1` of the factorization is uniquely determined). -/
theorem lam1_unique (h : Standing β γ κ σ) {l : ℝ} (hl : l ≤ 1) (hP : Precip β γ κ σ l = 0) :
    l = lam1 β γ κ σ := by
  rw [Precip_factor h] at hP
  have hq := (quad_pos_of_le_one h hl).ne'
  have hβγ : β * γ ≠ 0 := (mul_pos h.beta_pos h.gamma_pos).ne'
  rcases mul_eq_zero.mp hP with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 hβγ
    · linarith
  · exact absurd h1 hq

/-- Woodford (2003), App. G.6: `P(λ) < 0` for `λ < λ₁`. -/
theorem Precip_neg_of_lt (h : Standing β γ κ σ) {l : ℝ} (hl : l < lam1 β γ κ σ) :
    Precip β γ κ σ l < 0 := by
  rw [Precip_factor h]
  have hq := quad_pos_of_le_one h (hl.le.trans (lam1_spec h).2.1.le)
  have hβγ : 0 < β * γ := mul_pos h.beta_pos h.gamma_pos
  have : β * γ * (l - lam1 β γ κ σ) < 0 := mul_neg_of_pos_of_neg hβγ (by linarith)
  exact mul_neg_of_neg_of_pos this hq

/-- Woodford (2003), App. G.6: `P(λ) > 0` for `λ₁ < λ ≤ 1`. -/
theorem Precip_pos_of_gt (h : Standing β γ κ σ) {l : ℝ} (hl : lam1 β γ κ σ < l) (hl1 : l ≤ 1) :
    0 < Precip β γ κ σ l := by
  rw [Precip_factor h]
  have hq := quad_pos_of_le_one h hl1
  have hβγ : 0 < β * γ := mul_pos h.beta_pos h.gamma_pos
  exact mul_pos (mul_pos hβγ (by linarith)) hq

/-! ### The roots `λ₂, λ₃` -/

/-- A continuous complex square root of a real number: `√D` for `D ≥ 0` and `i√(−D)` for
`D < 0` (Woodford (2003), App. G.6, p. 726: Cardano's formulas). -/
noncomputable def csqrt (D : ℝ) : ℂ := (Real.sqrt D : ℂ) + Complex.I * (Real.sqrt (-D) : ℂ)

/-- `csqrt D ^ 2 = D` (Woodford (2003), App. G.6, p. 726). -/
theorem csqrt_sq (D : ℝ) : csqrt D ^ 2 = D := by
  unfold csqrt
  rcases le_total 0 D with hD | hD
  · rw [Real.sqrt_eq_zero'.mpr (by linarith : -D ≤ 0)]
    simp only [Complex.ofReal_zero, mul_zero, add_zero]
    rw [← Complex.ofReal_pow, Real.sq_sqrt hD]
  · rw [Real.sqrt_eq_zero'.mpr hD]
    simp only [Complex.ofReal_zero, zero_add]
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]
    push_cast
    ring

/-- The real part of `csqrt D` is `√D` (Woodford (2003), App. G.6, p. 726). -/
theorem csqrt_re (D : ℝ) : (csqrt D).re = Real.sqrt D := by
  simp [csqrt]

/-- The imaginary part of `csqrt D` is `√(−D)` (Woodford (2003), App. G.6, p. 726). -/
theorem csqrt_im (D : ℝ) : (csqrt D).im = Real.sqrt (-D) := by
  simp [csqrt]

/-- `csqrt D = 0 ↔ D = 0` (Woodford (2003), App. G.6, p. 726: repeated root iff `Δ = 0`). -/
theorem csqrt_eq_zero_iff (D : ℝ) : csqrt D = 0 ↔ D = 0 := by
  constructor
  · intro h0
    have h1 := congrArg Complex.re h0
    have h2 := congrArg Complex.im h0
    rw [csqrt_re, Complex.zero_re, Real.sqrt_eq_zero'] at h1
    rw [csqrt_im, Complex.zero_im, Real.sqrt_eq_zero'] at h2
    linarith
  · intro h0
    simp [csqrt, h0]

/-- Woodford (2003), Prop. 8.7, p. 594: the root `λ₂ = (S − √(S² − 4P₂₃))/2` (complex if the
discriminant is negative). -/
noncomputable def lam2 (β γ κ σ : ℝ) : ℂ := ((sumS β γ κ σ : ℂ) - csqrt (discQ β γ κ σ)) / 2

/-- Woodford (2003), Prop. 8.7, p. 594: the root `λ₃ = (S + √(S² − 4P₂₃))/2`. -/
noncomputable def lam3 (β γ κ σ : ℝ) : ℂ := ((sumS β γ κ σ : ℂ) + csqrt (discQ β γ κ σ)) / 2

/-- Woodford (2003), Prop. 8.7, p. 594: the real form of `λ₂` (equal to `λ₂` when the roots
are real). -/
noncomputable def lam2r (β γ κ σ : ℝ) : ℝ := (sumS β γ κ σ - Real.sqrt (discQ β γ κ σ)) / 2

/-- Woodford (2003), Prop. 8.7, p. 594: the real form of `λ₃`. -/
noncomputable def lam3r (β γ κ σ : ℝ) : ℝ := (sumS β γ κ σ + Real.sqrt (discQ β γ κ σ)) / 2

/-- Woodford (2003), (G.20), p. 725: `λ₂ + λ₃ = S`. -/
theorem lam2_add_lam3 : lam2 β γ κ σ + lam3 β γ κ σ = sumS β γ κ σ := by
  unfold lam2 lam3
  ring

/-- Woodford (2003), (G.18)–(G.19), p. 725: `λ₂λ₃ = P₂₃`. -/
theorem lam2_mul_lam3 : lam2 β γ κ σ * lam3 β γ κ σ = prodP β γ κ σ := by
  have h := csqrt_sq (discQ β γ κ σ)
  unfold lam2 lam3
  have e : ((sumS β γ κ σ : ℂ) - csqrt (discQ β γ κ σ)) / 2 *
      (((sumS β γ κ σ : ℂ) + csqrt (discQ β γ κ σ)) / 2) =
      ((sumS β γ κ σ : ℂ) ^ 2 - csqrt (discQ β γ κ σ) ^ 2) / 4 := by ring
  rw [e, h]
  unfold discQ
  push_cast
  ring

/-- `λ₂ = λ₃ ↔ S² − 4P₂₃ = 0` (Woodford (2003), App. G.6, p. 726). -/
theorem lam2_eq_lam3_iff : lam2 β γ κ σ = lam3 β γ κ σ ↔ discQ β γ κ σ = 0 := by
  rw [← csqrt_eq_zero_iff]
  unfold lam2 lam3
  constructor
  · intro h0
    linear_combination -h0
  · intro h0
    rw [h0]
    ring

/-- Real case (Woodford (2003), Prop. 8.7, p. 594): if `S² − 4P₂₃ ≥ 0` then `λ₂ = λ₂ʳ`. -/
theorem lam2_eq_ofReal {D : ℝ} (hD : discQ β γ κ σ = D) (hD0 : 0 ≤ D) :
    lam2 β γ κ σ = (lam2r β γ κ σ : ℂ) := by
  unfold lam2 lam2r csqrt
  rw [hD, Real.sqrt_eq_zero'.mpr (by linarith : -D ≤ 0)]
  push_cast
  ring

/-- Real case (Woodford (2003), Prop. 8.7, p. 594): if `S² − 4P₂₃ ≥ 0` then `λ₃ = λ₃ʳ`. -/
theorem lam3_eq_ofReal {D : ℝ} (hD : discQ β γ κ σ = D) (hD0 : 0 ≤ D) :
    lam3 β γ κ σ = (lam3r β γ κ σ : ℂ) := by
  unfold lam3 lam3r csqrt
  rw [hD, Real.sqrt_eq_zero'.mpr (by linarith : -D ≤ 0)]
  push_cast
  ring

/-- Woodford (2003), Prop. 8.7, p. 594: in the real case `1 < λ₂`. -/
theorem one_lt_lam2r (h : Standing β γ κ σ) : 1 < lam2r β γ κ σ := by
  have h1 := quad_one_pos h
  have h2 := two_lt_sumS h
  have h3 : Real.sqrt (discQ β γ κ σ) < sumS β γ κ σ - 2 := by
    rw [Real.sqrt_lt' (by linarith)]
    unfold discQ
    nlinarith
  unfold lam2r
  linarith

/-- Woodford (2003), Prop. 8.7, p. 594: in the real case `λ₂ ≤ λ₃`. -/
theorem lam2r_le_lam3r : lam2r β γ κ σ ≤ lam3r β γ κ σ := by
  unfold lam2r lam3r
  linarith [Real.sqrt_nonneg (discQ β γ κ σ)]

/-- Woodford (2003), Prop. 8.7, p. 594: in the real case `1 < λ₃`. -/
theorem one_lt_lam3r (h : Standing β γ κ σ) : 1 < lam3r β γ κ σ :=
  (one_lt_lam2r h).trans_le lam2r_le_lam3r

/-- Woodford (2003), Prop. 8.7, p. 594: in the complex case `λ₃ = conj λ₂`. -/
theorem lam3_eq_conj (hD : discQ β γ κ σ < 0) :
    lam3 β γ κ σ = (starRingEnd ℂ) (lam2 β γ κ σ) := by
  unfold lam2 lam3 csqrt
  rw [Real.sqrt_eq_zero'.mpr hD.le]
  simp only [map_div₀, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I,
    map_ofNat, Complex.ofReal_zero, zero_add]
  ring

/-- Woodford (2003), Prop. 8.7 / App. G.6, p. 725: `Re λ₂ = Re λ₃ = S/2`. -/
theorem re_lam2 : (lam2 β γ κ σ).re = sumS β γ κ σ / 2 ∨
    (lam2 β γ κ σ).re = lam2r β γ κ σ := by
  rcases le_or_gt 0 (discQ β γ κ σ) with hD | hD
  · right
    rw [lam2_eq_ofReal rfl hD, Complex.ofReal_re]
  · left
    simp [lam2, csqrt, Real.sqrt_eq_zero'.mpr hD.le]

/-- Woodford (2003), Prop. 8.7, p. 594 (complex case): `Im λ₂ ≠ 0` and `Re λ₂ = S/2 > 1`. -/
theorem lam2_complex (h : Standing β γ κ σ) (hD : discQ β γ κ σ < 0) :
    (lam2 β γ κ σ).im ≠ 0 ∧ (lam2 β γ κ σ).re = sumS β γ κ σ / 2 ∧
      1 < (lam2 β γ κ σ).re := by
  have hre : (lam2 β γ κ σ).re = sumS β γ κ σ / 2 := by
    simp [lam2, csqrt, Real.sqrt_eq_zero'.mpr hD.le]
  have him : (lam2 β γ κ σ).im = -(Real.sqrt (-discQ β γ κ σ)) / 2 := by
    simp [lam2, csqrt, Real.sqrt_eq_zero'.mpr hD.le]
  refine ⟨?_, hre, ?_⟩
  · rw [him]
    have : 0 < Real.sqrt (-discQ β γ κ σ) := Real.sqrt_pos.mpr (by linarith)
    intro h0
    linarith
  · rw [hre]
    linarith [two_lt_sumS h]

/-- Woodford (2003), Prop. 8.7, p. 594: `|λ₂| > 1`. -/
theorem one_lt_norm_lam2 (h : Standing β γ κ σ) : 1 < ‖lam2 β γ κ σ‖ := by
  rcases le_or_gt 0 (discQ β γ κ σ) with hD | hD
  · rw [lam2_eq_ofReal rfl hD, Complex.norm_real, Real.norm_eq_abs]
    have := one_lt_lam2r h
    rw [abs_of_pos (by linarith)]
    exact this
  · exact (lam2_complex h hD).2.2.trans_le ((le_abs_self _).trans (Complex.abs_re_le_norm _))

/-- Woodford (2003), Prop. 8.7, p. 594: `|λ₃| > 1`. -/
theorem one_lt_norm_lam3 (h : Standing β γ κ σ) : 1 < ‖lam3 β γ κ σ‖ := by
  rcases le_or_gt 0 (discQ β γ κ σ) with hD | hD
  · rw [lam3_eq_ofReal rfl hD, Complex.norm_real, Real.norm_eq_abs]
    have := one_lt_lam3r h
    rw [abs_of_pos (by linarith)]
    exact this
  · rw [lam3_eq_conj hD, Complex.norm_conj]
    exact one_lt_norm_lam2 h

/-- Woodford (2003), (G.16)/(3.20), pp. 594, 724: the factorization
`A(z) = βγ(1 − λ₁z)(1 − λ₂z)(1 − λ₃z)` for every complex `z`. -/
theorem ApolyC_factor (h : Standing β γ κ σ) (z : ℂ) :
    ApolyC β γ κ σ z = (β * γ : ℝ) * (1 - (lam1 β γ κ σ : ℂ) * z) *
      (1 - lam2 β γ κ σ * z) * (1 - lam3 β γ κ σ * z) := by
  have e : (β * γ : ℝ) * (1 - (lam1 β γ κ σ : ℂ) * z) * (1 - lam2 β γ κ σ * z) *
      (1 - lam3 β γ κ σ * z) = (β * γ : ℝ) * (1 - (lam1 β γ κ σ : ℂ) * z) *
      (1 - (lam2 β γ κ σ + lam3 β γ κ σ) * z + lam2 β γ κ σ * lam3 β γ κ σ * z ^ 2) := by
    ring
  rw [e, lam2_add_lam3, lam2_mul_lam3]
  have h1 : coefA1 β γ = -(β * γ * (lam1 β γ κ σ + sumS β γ κ σ)) := by
    rw [vieta_sum h]; rfl
  have h2 : coefA2 β γ κ σ = β * γ * (prodP β γ κ σ + sumS β γ κ σ * lam1 β γ κ σ) :=
    (vieta_pair h).symm
  have h3 : coefA3 β = -(β * γ * lam1 β γ κ σ * prodP β γ κ σ) := by
    rw [vieta_const h]; rfl
  unfold ApolyC
  rw [h1, h2, h3]
  unfold coefA0
  push_cast
  ring

/-- Woodford (2003), (G.19), p. 725: `(βλ₁λ₂λ₃)⁻¹ = βγ`. -/
theorem vieta_G19 (h : Standing β γ κ σ) :
    ((β : ℂ) * lam1 β γ κ σ * lam2 β γ κ σ * lam3 β γ κ σ)⁻¹ = β * γ := by
  have hc := vieta_const h
  have hβ := h.beta_pos.ne'
  have hγ := h.gamma_pos.ne'
  rw [mul_assoc _ (lam2 β γ κ σ), lam2_mul_lam3]
  have hr : β * lam1 β γ κ σ * prodP β γ κ σ = (β * γ)⁻¹ := by
    rw [mul_inv, ← hc]
    field_simp
  have : (β : ℂ) * lam1 β γ κ σ * prodP β γ κ σ = ((β * γ) : ℂ)⁻¹ := by
    exact_mod_cast hr
  rw [this, inv_inv]

/-- Woodford (2003), (G.20), p. 725: `βγ(λ₁ + λ₂ + λ₃) = 1 + γ + βγ`. -/
theorem vieta_G20 (h : Standing β γ κ σ) :
    (β * γ : ℂ) * (lam1 β γ κ σ + lam2 β γ κ σ + lam3 β γ κ σ) = 1 + γ + β * γ := by
  rw [add_assoc, lam2_add_lam3]
  have := vieta_sum h
  exact_mod_cast this

/-- Woodford (2003), (G.18), p. 725: `βγ(λ₁λ₂ + λ₁λ₃ + λ₂λ₃) = A₂ = 1 + γ + β⁻¹(1 + κσ)`. -/
theorem vieta_G18_pair (h : Standing β γ κ σ) :
    (β * γ : ℂ) * (lam1 β γ κ σ * lam2 β γ κ σ + lam1 β γ κ σ * lam3 β γ κ σ +
      lam2 β γ κ σ * lam3 β γ κ σ) = (coefA2 β γ κ σ : ℂ) := by
  have e : (lam1 β γ κ σ : ℂ) * lam2 β γ κ σ + lam1 β γ κ σ * lam3 β γ κ σ +
      lam2 β γ κ σ * lam3 β γ κ σ =
      lam1 β γ κ σ * (lam2 β γ κ σ + lam3 β γ κ σ) + lam2 β γ κ σ * lam3 β γ κ σ := by ring
  rw [e, lam2_add_lam3, lam2_mul_lam3, ← vieta_pair h]
  push_cast
  ring

/-- Woodford (2003), (G.20) as used in the proof of Lemma G.2, p. 720:
`γλ₃ = β⁻¹ + γ(1 + β⁻¹ − λ₁ − λ₂)`. -/
theorem gamma_mul_lam3 (h : Standing β γ κ σ) :
    (γ : ℂ) * lam3 β γ κ σ = (β : ℂ)⁻¹ + γ * (1 + (β : ℂ)⁻¹ - lam1 β γ κ σ - lam2 β γ κ σ) := by
  have h20 := vieta_G20 h
  have hβ : (β : ℂ) ≠ 0 := by exact_mod_cast h.beta_pos.ne'
  field_simp
  linear_combination h20

/-! ### Proposition 8.7 -/

/-- Woodford (2003), **Proposition 8.7**, p. 594 (proof App. G.6, pp. 724–727): under
`σ, κ > 0`, `0 < β < 1`, `0 < γ ≤ 1`, the cubic (3.17) factorizes as (3.20)
`A(z) = βγ(1 − λ₁z)(1 − λ₂z)(1 − λ₃z)` with one real root `0 < λ₁ < 1` and two roots outside
the unit circle, which are either real with `1 < λ₂ ≤ λ₃` or a complex-conjugate pair with
real part `> 1`. -/
theorem prop_8_7 (h : Standing β γ κ σ) :
    ∃ (l1 : ℝ) (l2 l3 : ℂ),
      (∀ z : ℂ, ApolyC β γ κ σ z = (β * γ : ℝ) * (1 - (l1 : ℂ) * z) * (1 - l2 * z) *
        (1 - l3 * z)) ∧ 0 < l1 ∧ l1 < 1 ∧
      ((∃ r2 r3 : ℝ, l2 = r2 ∧ l3 = r3 ∧ 1 < r2 ∧ r2 ≤ r3) ∨
        (l3 = (starRingEnd ℂ) l2 ∧ l2.im ≠ 0 ∧ 1 < l2.re)) ∧
      1 < ‖l2‖ ∧ 1 < ‖l3‖ := by
  refine ⟨lam1 β γ κ σ, lam2 β γ κ σ, lam3 β γ κ σ, ApolyC_factor h, (lam1_spec h).1,
    (lam1_spec h).2.1, ?_, one_lt_norm_lam2 h, one_lt_norm_lam3 h⟩
  rcases le_or_gt 0 (discQ β γ κ σ) with hD | hD
  · exact Or.inl ⟨lam2r β γ κ σ, lam3r β γ κ σ, lam2_eq_ofReal rfl hD, lam3_eq_ofReal rfl hD,
      one_lt_lam2r h, lam2r_le_lam3r⟩
  · exact Or.inr ⟨lam3_eq_conj hD, (lam2_complex h hD).1, (lam2_complex h hD).2.2⟩

/-- Woodford (2003), (G.16)–(G.20), p. 725: Vieta's formulas from ANY factorization
`A(z) = βγ(1 − l₁z)(1 − l₂z)(1 − l₃z)` (coefficient comparison): `βγ(l₁ + l₂ + l₃) = 1 + γ + βγ`,
`βγ(l₁l₂ + l₁l₃ + l₂l₃) = A₂`, `βγ l₁l₂l₃ = β⁻¹`. -/
theorem vieta_of_factor {l1 l2 l3 : ℂ}
    (hf : ∀ z : ℂ, ApolyC β γ κ σ z = (β * γ : ℝ) * (1 - l1 * z) * (1 - l2 * z) * (1 - l3 * z)) :
    (β * γ : ℂ) * (l1 + l2 + l3) = 1 + γ + β * γ ∧
      (β * γ : ℂ) * (l1 * l2 + l1 * l3 + l2 * l3) = (coefA2 β γ κ σ : ℂ) ∧
      (β * γ : ℂ) * (l1 * l2 * l3) = (β : ℂ)⁻¹ := by
  have h0 := hf 0
  have h1 := hf 1
  have hm := hf (-1)
  have h2 := hf 2
  simp only [ApolyC, coefA0, coefA1, coefA3] at h0 h1 hm h2
  push_cast at h0 h1 hm h2
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-(1 : ℂ) / 6) * h2 + h1 - (1 / 3 : ℂ) * hm - (1 / 2 : ℂ) * h0
  · linear_combination (-(1 : ℂ) / 2) * h1 - (1 / 2 : ℂ) * hm + h0
  · linear_combination (1 / 6 : ℂ) * h2 - (1 / 2 : ℂ) * h1 - (1 / 6 : ℂ) * hm + (1 / 2 : ℂ) * h0

/-- Woodford (2003), Prop. 8.7, p. 594: the factorization (3.20) is UNIQUE up to the order of
`λ₂, λ₃`: if `A(z) = βγ(1 − l₁z)(1 − l₂z)(1 − l₃z)` with `l₁ ≤ 1` real, then `l₁ = λ₁` and
`{l₂, l₃} = {λ₂, λ₃}`. -/
theorem factorization_unique (h : Standing β γ κ σ) {l1 : ℝ} {l2 l3 : ℂ} (hl1 : l1 ≤ 1)
    (hf : ∀ z : ℂ, ApolyC β γ κ σ z = (β * γ : ℝ) * (1 - (l1 : ℂ) * z) * (1 - l2 * z) *
      (1 - l3 * z)) :
    l1 = lam1 β γ κ σ ∧ ((l2 = lam2 β γ κ σ ∧ l3 = lam3 β γ κ σ) ∨
      (l2 = lam3 β γ κ σ ∧ l3 = lam2 β γ κ σ)) := by
  obtain ⟨v1, v2, v3⟩ := vieta_of_factor hf
  have hβ : (β : ℂ) ≠ 0 := by exact_mod_cast h.beta_pos.ne'
  have hγ : (γ : ℂ) ≠ 0 := by exact_mod_cast h.gamma_pos.ne'
  -- `l₁` is a root of the reciprocal polynomial
  have hP : ((Precip β γ κ σ l1 : ℝ) : ℂ) = 0 := by
    have e : ((Precip β γ κ σ l1 : ℝ) : ℂ) = (β * γ : ℂ) * (l1 - l1) * (l1 - l2) * (l1 - l3) := by
      unfold Precip
      push_cast
      linear_combination (l1 : ℂ) ^ 2 * v1 - (l1 : ℂ) * v2 + v3
    rw [e]
    ring
  have hl1' : l1 = lam1 β γ κ σ := lam1_unique h hl1 (by exact_mod_cast hP)
  refine ⟨hl1', ?_⟩
  subst hl1'
  have hs : l2 + l3 = sumS β γ κ σ := by
    have e2 := vieta_G20 h
    have : (β * γ : ℂ) * (l2 + l3 - (lam2 β γ κ σ + lam3 β γ κ σ)) = 0 := by
      linear_combination v1 - e2
    rw [lam2_add_lam3] at this
    have hβγ : (β * γ : ℂ) ≠ 0 := mul_ne_zero hβ hγ
    have := (mul_eq_zero.mp this).resolve_left hβγ
    linear_combination this
  have hp : l2 * l3 = prodP β γ κ σ := by
    have e3 := vieta_G18_pair h
    have : (β * γ : ℂ) * (lam1 β γ κ σ * ((l2 + l3) - (lam2 β γ κ σ + lam3 β γ κ σ)) +
        (l2 * l3 - lam2 β γ κ σ * lam3 β γ κ σ)) = 0 := by
      linear_combination v2 - e3
    rw [hs, lam2_add_lam3, lam2_mul_lam3, sub_self, mul_zero, zero_add] at this
    have hβγ : (β * γ : ℂ) ≠ 0 := mul_ne_zero hβ hγ
    have := (mul_eq_zero.mp this).resolve_left hβγ
    linear_combination this
  have hq : (l2 - lam2 β γ κ σ) * (l2 - lam3 β γ κ σ) = 0 := by
    have e1 := lam2_add_lam3 (β := β) (γ := γ) (κ := κ) (σ := σ)
    have e2 := lam2_mul_lam3 (β := β) (γ := γ) (κ := κ) (σ := σ)
    linear_combination (-l2) * e1 + e2 + l2 * hs - hp
  rcases mul_eq_zero.mp hq with hq | hq
  · left
    refine ⟨by linear_combination hq, ?_⟩
    have e1 := lam2_add_lam3 (β := β) (γ := γ) (κ := κ) (σ := σ)
    linear_combination hs - e1 - hq
  · right
    refine ⟨by linear_combination hq, ?_⟩
    have e1 := lam2_add_lam3 (β := β) (γ := γ) (κ := κ) (σ := σ)
    linear_combination hs - e1 - hq

/-! ### Survey item E20: does the book's shape argument exclude three roots `z > 1`? -/

/-- Woodford (2003), App. G.6, p. 724 (survey E20): the shape facts the book lists DO exclude
two distinct real roots `z > 1` — for ANY real cubic `p(z) = a₀ + a₁z + a₂z² + a₃z³` with
`a₃ < 0`, `p(1) > 0` and `p′(β) > 0` for some `β < 1` (if `x ≠ y > 1` were roots, the third root
`w` is real and `> 1` because `p(1) > 0`, and then `p′(β) = a₃ Σ (β − ·)(β − ·) < 0`). So the
gap claimed in E20 closes with the book's own fact `A′(β) > 0`. -/
theorem no_two_roots_gt_one_of_shape {a0 a1 a2 a3 b : ℝ} (ha3 : a3 < 0) (hb : b < 1)
    (hp1 : 0 < a0 + a1 + a2 + a3) (hpb : 0 < a1 + 2 * a2 * b + 3 * a3 * b ^ 2)
    {x y : ℝ} (hx : 1 < x) (hy : 1 < y) (hxy : x ≠ y)
    (hpx : a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3 = 0)
    (hpy : a0 + a1 * y + a2 * y ^ 2 + a3 * y ^ 3 = 0) : False := by
  set w := -a2 / a3 - x - y with hw
  have ha3' : a3 ≠ 0 := ha3.ne
  have hsum : a2 = -a3 * (x + y + w) := by rw [hw]; field_simp; ring
  -- the linear remainder `c₁ z + c₀` vanishes at `x` and `y`
  have hx' : (a1 - a3 * (x * y + x * w + y * w)) * x + (a0 + a3 * x * y * w) = 0 := by
    rw [hsum] at hpx
    linear_combination hpx
  have hy' : (a1 - a3 * (x * y + x * w + y * w)) * y + (a0 + a3 * x * y * w) = 0 := by
    rw [hsum] at hpy
    linear_combination hpy
  have hc1 : a1 - a3 * (x * y + x * w + y * w) = 0 := by
    have : (a1 - a3 * (x * y + x * w + y * w)) * (x - y) = 0 := by linear_combination hx' - hy'
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hxy)
  have hc0 : a0 + a3 * x * y * w = 0 := by
    rw [hc1, zero_mul, zero_add] at hx'
    exact hx'
  have ha1 : a1 = a3 * (x * y + x * w + y * w) := by linarith
  have ha0 : a0 = -(a3 * x * y * w) := by linarith
  -- `p(1) = a₃(1 − x)(1 − y)(1 − w) > 0` forces `w > 1`
  have hp1' : a0 + a1 + a2 + a3 = a3 * (1 - x) * (1 - y) * (1 - w) := by
    rw [ha0, ha1, hsum]; ring
  have hxy1 : 0 < (1 - x) * (1 - y) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
  have hw1 : 1 < w := by
    by_contra hcon
    push Not at hcon
    have : a3 * (1 - x) * (1 - y) * (1 - w) ≤ 0 := by
      have : a3 * ((1 - x) * (1 - y)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha3.le hxy1.le
      rw [mul_assoc a3]
      exact mul_nonpos_of_nonpos_of_nonneg this (by linarith)
    linarith
  -- then `p′(b) < 0`
  have hpb' : a1 + 2 * a2 * b + 3 * a3 * b ^ 2 =
      a3 * ((b - y) * (b - w) + (b - x) * (b - w) + (b - x) * (b - y)) := by
    rw [ha1, hsum]; ring
  have hpos : 0 < (b - y) * (b - w) + (b - x) * (b - w) + (b - x) * (b - y) := by
    have e1 : 0 < (b - y) * (b - w) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
    have e2 : 0 < (b - x) * (b - w) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
    have e3 : 0 < (b - x) * (b - y) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
    linarith
  have : a3 * ((b - y) * (b - w) + (b - x) * (b - w) + (b - x) * (b - y)) < 0 :=
    mul_neg_of_neg_of_pos ha3 hpos
  linarith

/-- Woodford (2003), App. G.6, p. 724 (E20 resolved): `A(z)` has exactly one real root `z > 1`,
namely `z₁ = λ₁⁻¹`, deduced from the book's shape facts `A(1) > 0`, `A′(β) > 0` (via
`no_two_roots_gt_one_of_shape`). -/
theorem Apoly_unique_root_gt_one (h : Standing β γ κ σ) :
    1 < (lam1 β γ κ σ)⁻¹ ∧ Apoly β γ κ σ (lam1 β γ κ σ)⁻¹ = 0 ∧
      ∀ z, 1 < z → Apoly β γ κ σ z = 0 → z = (lam1 β γ κ σ)⁻¹ := by
  obtain ⟨h0, h1, hP⟩ := lam1_spec h
  have hroot : Apoly β γ κ σ (lam1 β γ κ σ)⁻¹ = 0 := by
    rw [Apoly_inv h0.ne', hP, zero_div]
  refine ⟨one_lt_inv_iff₀.mpr ⟨h0, h1⟩, hroot, fun z hz hAz => ?_⟩
  by_contra hne
  have hA3 : coefA3 β < 0 := by unfold coefA3; simp [h.beta_pos]
  have hp1 := Apoly_one_pos h
  have hpb := Aderiv_beta_pos h
  unfold Apoly at hp1 hAz hroot
  unfold Aderiv at hpb
  exact no_two_roots_gt_one_of_shape hA3 h.beta_lt_one (by simpa using hp1) hpb hz
    (one_lt_inv_iff₀.mpr ⟨h0, h1⟩) hne hAz hroot

/-- Woodford (2003), App. G.6 (survey E20, the Vieta closure): `A` cannot have three real roots
`z > 1`, because `z₁z₂z₃ = −A₀/A₃ = β²γ < 1`. -/
theorem vieta_excludes_three_roots_gt_one (h : Standing β γ κ σ) {z1 z2 z3 : ℝ}
    (h1 : 1 < z1) (h2 : 1 < z2) (h3 : 1 < z3)
    (hf : ∀ z, Apoly β γ κ σ z = coefA3 β * (z - z1) * (z - z2) * (z - z3)) : False := by
  have h0 := hf 0
  have hβ := h.beta_pos
  have hprod : z1 * z2 * z3 = β ^ 2 * γ := by
    unfold Apoly coefA0 coefA1 coefA3 at h0
    field_simp at h0
    linear_combination -h0
  have hlt : β ^ 2 * γ < 1 := by
    have : β ^ 2 < 1 := by nlinarith [h.beta_lt_one]
    nlinarith [h.gamma_le_one, h.gamma_pos]
  have : 1 < z1 * z2 * z3 := by
    have : 1 < z1 * z2 := one_lt_mul_of_lt_of_le h1 h2.le
    exact one_lt_mul_of_lt_of_le this h3.le
  linarith

/-! ### The Cardano discriminant `Δ(γ)` -/

/-- Woodford (2003), App. G.6, p. 726: the bracket
`27A₀²A₃² + 4A₀A₂³ − 18A₀A₃A₂A₁ − A₂²A₁² + 4A₃A₁³` (minus the classical discriminant). -/
def discBracket {K : Type*} [Field K] (A0 A1 A2 A3 : K) : K :=
  27 * A0 ^ 2 * A3 ^ 2 + 4 * A0 * A2 ^ 3 - 18 * A0 * A3 * A2 * A1 - A2 ^ 2 * A1 ^ 2 +
    4 * A3 * A1 ^ 3

/-- Woodford (2003), App. G.6, p. 726: `Δ ≡ 27B₀² + 4B₁³ = A₃⁻⁴(27A₀²A₃² + 4A₀A₂³ −
18A₀A₃A₂A₁ − A₂²A₁² + 4A₃A₁³)`. -/
theorem delta_eq_bracket {K : Type*} [Field K] [CharZero K] (A0 A1 A2 A3 : K) (h3 : A3 ≠ 0) :
    27 * depB0 A0 A1 A2 A3 ^ 2 + 4 * depB1 A1 A2 A3 ^ 3 =
      (A3 ^ 4)⁻¹ * discBracket A0 A1 A2 A3 := by
  unfold depB0 depB1 discBracket
  field_simp
  ring

/-- The bracket of a factored cubic `a(1 − lz)(1 − sz + pz²)`:
it equals `−a⁴(l² − sl + p)²(s² − 4p)` (Woodford (2003), App. G.6, p. 726; the classical
discriminant is `a⁴ ∏ (λᵢ − λⱼ)²`). -/
theorem bracket_factored {K : Type*} [Field K] (a l s p : K) :
    discBracket a (-(a * (l + s))) (a * (p + s * l)) (-(a * l * p)) =
      -(a ^ 4 * (l ^ 2 - s * l + p) ^ 2 * (s ^ 2 - 4 * p)) := by
  unfold discBracket
  ring

/-- Woodford (2003), App. G.6, p. 726: `Δ(γ) = 27B₀² + 4B₁³` for the cubic (G.17). -/
noncomputable def deltaG (β γ κ σ : ℝ) : ℝ :=
  27 * depB0 (coefA0 β γ) (coefA1 β γ) (coefA2 β γ κ σ) (coefA3 β) ^ 2 +
    4 * depB1 (coefA1 β γ) (coefA2 β γ κ σ) (coefA3 β) ^ 3

/-- Woodford (2003), App. G.6, pp. 726–727: the printed quartic in `γ`. -/
noncomputable def deltaQuartic (β γ κ σ : ℝ) : ℝ :=
  -β ^ 4 * (1 - β) ^ 2 * γ ^ 4
    - 2 * β ^ 3 * ((1 + β ^ 2 - 4 * β) * (κ * σ) - (1 + β) * (1 - β) ^ 2) * γ ^ 3
    - β ^ 2 * ((κ * σ) ^ 2 * (1 - 10 * β + β ^ 2) + 2 * (κ * σ) * (1 + β) * (1 + β + β ^ 2)
        + (1 + 4 * β + β ^ 2) * (1 - β) ^ 2) * γ ^ 2
    + β ^ 2 * (4 * (κ * σ) ^ 3 + 10 * (1 + β) * (κ * σ) ^ 2 + 4 * (2 + 2 * β ^ 2 - β) * (κ * σ)
        + 2 * (1 + β) * (1 - β) ^ 2) * γ
    - β ^ 2 * (2 * β * (κ * σ) + (κ * σ) ^ 2 + 2 * (κ * σ) + (1 - β) ^ 2)

/-- Woodford (2003), App. G.6, pp. 726–727: `Δ(γ)` equals the printed quartic (verified). -/
theorem deltaG_eq_quartic (hβ : β ≠ 0) : deltaG β γ κ σ = deltaQuartic β γ κ σ := by
  unfold deltaG
  rw [delta_eq_bracket _ _ _ _ (by unfold coefA3; simp [hβ])]
  unfold discBracket deltaQuartic coefA0 coefA1 coefA2 coefA3
  field_simp
  ring

/-- Woodford (2003), App. G.6, p. 726: `Δ(γ) = −β⁴(βγ)⁴ q(λ₁)² (S² − 4P₂₃)` with
`q(λ₁) = λ₁² − Sλ₁ + P₂₃ > 0`, so the sign of `Δ` is minus the sign of the discriminant of
the quadratic whose roots are `λ₂, λ₃`. -/
theorem deltaG_factor (h : Standing β γ κ σ) :
    deltaG β γ κ σ = -(β ^ 4 * (β * γ) ^ 4 *
      (lam1 β γ κ σ ^ 2 - sumS β γ κ σ * lam1 β γ κ σ + prodP β γ κ σ) ^ 2 *
        discQ β γ κ σ) := by
  have hβ := h.beta_pos.ne'
  have h0 : coefA0 β γ = β * γ := rfl
  have h1 : coefA1 β γ = -(β * γ * (lam1 β γ κ σ + sumS β γ κ σ)) := by
    rw [vieta_sum h]; rfl
  have h2 : coefA2 β γ κ σ = β * γ * (prodP β γ κ σ + sumS β γ κ σ * lam1 β γ κ σ) :=
    (vieta_pair h).symm
  have h3 : coefA3 β = -(β * γ * lam1 β γ κ σ * prodP β γ κ σ) := by
    rw [vieta_const h]; rfl
  unfold deltaG
  rw [delta_eq_bracket _ _ _ _ (by unfold coefA3; simp [hβ]), h0, h1, h2, h3, bracket_factored,
    vieta_const h]
  unfold discQ
  field_simp

/-- Woodford (2003), App. G.6, p. 726: the positive factor `β⁴(βγ)⁴ q(λ₁)²` of `−Δ/(S²−4P₂₃)`. -/
theorem deltaG_factor_pos (h : Standing β γ κ σ) :
    0 < β ^ 4 * (β * γ) ^ 4 *
      (lam1 β γ κ σ ^ 2 - sumS β γ κ σ * lam1 β γ κ σ + prodP β γ κ σ) ^ 2 := by
  have hq := quad_pos_of_le_one h (lam1_spec h).2.1.le
  have hβ := h.beta_pos
  have hγ := h.gamma_pos
  positivity

/-- Woodford (2003), App. G.6, p. 726, Cardano case (1): `Δ < 0 ↔ S² − 4P₂₃ > 0`. -/
theorem deltaG_neg_iff (h : Standing β γ κ σ) : deltaG β γ κ σ < 0 ↔ 0 < discQ β γ κ σ := by
  rw [deltaG_factor h, neg_lt_zero]
  exact mul_pos_iff_of_pos_left (deltaG_factor_pos h)

/-- Woodford (2003), App. G.6, p. 726, Cardano case (2): `Δ = 0 ↔ S² − 4P₂₃ = 0`. -/
theorem deltaG_eq_zero_iff (h : Standing β γ κ σ) :
    deltaG β γ κ σ = 0 ↔ discQ β γ κ σ = 0 := by
  rw [deltaG_factor h, neg_eq_zero, mul_eq_zero]
  simp [(deltaG_factor_pos h).ne']

/-- Woodford (2003), App. G.6, p. 726, Cardano case (3): `Δ > 0 ↔ S² − 4P₂₃ < 0`. -/
theorem deltaG_pos_iff (h : Standing β γ κ σ) : 0 < deltaG β γ κ σ ↔ discQ β γ κ σ < 0 := by
  rw [deltaG_factor h, neg_pos]
  have hK := deltaG_factor_pos h
  constructor
  · intro hd
    by_contra hc
    push Not at hc
    have := mul_nonneg hK.le hc
    linarith
  · intro hD
    exact mul_neg_of_pos_of_neg hK hD

/-- `Im λ₂ = −√(−(S² − 4P₂₃))/2` (Woodford (2003), App. G.6, p. 726). -/
theorem im_lam2 : (lam2 β γ κ σ).im = -Real.sqrt (-discQ β γ κ σ) / 2 := by
  simp [lam2, csqrt]

/-- `Im λ₃ = √(−(S² − 4P₂₃))/2` (Woodford (2003), App. G.6, p. 726). -/
theorem im_lam3 : (lam3 β γ κ σ).im = Real.sqrt (-discQ β γ κ σ) / 2 := by
  simp [lam3, csqrt]

/-- Woodford (2003), App. G.6, p. 726, case (1): `Δ < 0` iff `λ₂, λ₃` are real and distinct. -/
theorem three_distinct_real_iff (h : Standing β γ κ σ) :
    deltaG β γ κ σ < 0 ↔ ((lam2 β γ κ σ).im = 0 ∧ (lam3 β γ κ σ).im = 0 ∧
      lam2 β γ κ σ ≠ lam3 β γ κ σ) := by
  rw [deltaG_neg_iff h, im_lam2, im_lam3, Ne, lam2_eq_lam3_iff]
  constructor
  · intro hD
    rw [Real.sqrt_eq_zero'.mpr (by linarith)]
    exact ⟨by simp, by simp, hD.ne'⟩
  · rintro ⟨h1, -, h3⟩
    have : Real.sqrt (-discQ β γ κ σ) = 0 := by linarith
    rw [Real.sqrt_eq_zero'] at this
    exact lt_of_le_of_ne (by linarith) (Ne.symm h3)

/-- Woodford (2003), App. G.6, p. 726, case (2): `Δ = 0` iff `λ₂ = λ₃` (a repeated real root). -/
theorem repeated_root_iff (h : Standing β γ κ σ) :
    deltaG β γ κ σ = 0 ↔ lam2 β γ κ σ = lam3 β γ κ σ := by
  rw [deltaG_eq_zero_iff h, lam2_eq_lam3_iff]

/-- Woodford (2003), App. G.6, p. 726, case (3): `Δ > 0` iff `λ₂, λ₃` are non-real (then a
conjugate pair, `lam3_eq_conj`). -/
theorem complex_pair_iff (h : Standing β γ κ σ) :
    0 < deltaG β γ κ σ ↔ (lam2 β γ κ σ).im ≠ 0 := by
  rw [deltaG_pos_iff h, im_lam2]
  constructor
  · intro hD
    have : 0 < Real.sqrt (-discQ β γ κ σ) := Real.sqrt_pos.mpr (by linarith)
    intro h0
    linarith
  · intro h0
    by_contra hcon
    push Not at hcon
    apply h0
    rw [Real.sqrt_eq_zero'.mpr (by linarith)]
    simp

/-- Woodford (2003), App. G.6, p. 726 (via Lemma G.1): `z` is a root of `A` iff
`ζ = z + A₂/(3A₃)` is a root of the depressed cubic `B₀ + B₁ζ + ζ³`. -/
theorem ApolyC_eq_zero_iff_depressed (hβ : β ≠ 0) (z : ℂ) :
    ApolyC β γ κ σ z = 0 ↔
      depB0 (coefA0 β γ : ℂ) (coefA1 β γ) (coefA2 β γ κ σ) (coefA3 β) +
        depB1 (coefA1 β γ : ℂ) (coefA2 β γ κ σ) (coefA3 β) *
          (z + (coefA2 β γ κ σ : ℂ) / (3 * coefA3 β)) +
        (z + (coefA2 β γ κ σ : ℂ) / (3 * coefA3 β)) ^ 3 = 0 := by
  have h3 : (coefA3 β : ℂ) ≠ 0 := by
    unfold coefA3
    push_cast
    simp [hβ]
  have e := lemma_G1 (coefA0 β γ : ℂ) (coefA1 β γ) (coefA2 β γ κ σ) (coefA3 β) z h3
  have e2 : ApolyC β γ κ σ z = (coefA3 β : ℂ) * z ^ 3 + (coefA2 β γ κ σ : ℂ) * z ^ 2 +
      (coefA1 β γ : ℂ) * z + (coefA0 β γ : ℂ) := by
    unfold ApolyC
    ring
  rw [e2, e, mul_eq_zero]
  simp [h3]

/-- Woodford (2003), App. G.6, p. 726: "each `λⱼ` is real iff the corresponding `ζⱼ` is real",
where `zⱼ = λⱼ⁻¹` and `ζⱼ = zⱼ + A₂/(3A₃)` (the shift is real). -/
theorem lam_real_iff_zeta_real (l : ℂ) (hl : l ≠ 0) :
    l.im = 0 ↔ (l⁻¹ + (coefA2 β γ κ σ : ℂ) / (3 * coefA3 β)).im = 0 := by
  have hs : ((coefA2 β γ κ σ : ℂ) / (3 * coefA3 β)).im = 0 := by
    have : (coefA2 β γ κ σ : ℂ) / (3 * coefA3 β) = ((coefA2 β γ κ σ / (3 * coefA3 β) : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.ofReal_im]
  rw [Complex.add_im, hs, add_zero, Complex.inv_im, neg_div, neg_eq_zero,
    div_eq_zero_iff]
  have : Complex.normSq l ≠ 0 := by
    rw [Ne, Complex.normSq_eq_zero]
    exact hl
  simp [this]

/-- Woodford (2003), App. G.6, p. 727: `Δ(0) = −β²(2βκσ + κ²σ² + 2κσ + (1 − β)²)`. -/
theorem deltaQuartic_zero :
    deltaQuartic β 0 κ σ =
      -(β ^ 2 * (2 * β * (κ * σ) + (κ * σ) ^ 2 + 2 * (κ * σ) + (1 - β) ^ 2)) := by
  unfold deltaQuartic
  ring

/-- Woodford (2003), App. G.6, p. 727: `Δ(1) = β²κσ(4κ²σ² + (8 + 20β − β²)κσ + 4(1 − β)³)`. -/
theorem deltaQuartic_one :
    deltaQuartic β 1 κ σ =
      β ^ 2 * (κ * σ) * (4 * (κ * σ) ^ 2 + (8 + 20 * β - β ^ 2) * (κ * σ) + 4 * (1 - β) ^ 3) := by
  unfold deltaQuartic
  ring

/-- Woodford (2003), App. G.6, p. 727: `Δ(0) < 0`. -/
theorem deltaQuartic_zero_neg (hβ : 0 < β) (hκσ : 0 < κ * σ) : deltaQuartic β 0 κ σ < 0 := by
  rw [deltaQuartic_zero, neg_lt_zero]
  positivity

/-- Woodford (2003), App. G.6, p. 727: `Δ(1) > 0`. -/
theorem deltaQuartic_one_pos (hβ : 0 < β) (hβ1 : β < 1) (hκσ : 0 < κ * σ) :
    0 < deltaQuartic β 1 κ σ := by
  rw [deltaQuartic_one]
  have h1 : 0 < 8 + 20 * β - β ^ 2 := by nlinarith
  have h2 : 0 < 1 - β := by linarith
  positivity

/-- Woodford (2003), App. G.6, p. 727: `Δ(γ)` is continuous in `γ`. -/
theorem continuous_deltaQuartic : Continuous (fun γ => deltaQuartic β γ κ σ) := by
  unfold deltaQuartic
  fun_prop

/-- Woodford (2003), App. G.6, p. 727: `Δ(γ) → −∞` as `γ → +∞` and as `γ → −∞` (the leading
coefficient is `−β⁴(1 − β)² < 0`). -/
theorem tendsto_deltaQuartic (hβ : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun γ => deltaQuartic β γ κ σ) atTop atBot ∧
      Tendsto (fun γ => deltaQuartic β γ κ σ) atBot atBot := by
  set c4 := -β ^ 4 * (1 - β) ^ 2 with hc4
  set c3 := -(2 * β ^ 3 * ((1 + β ^ 2 - 4 * β) * (κ * σ) - (1 + β) * (1 - β) ^ 2)) with hc3
  set c2 := -(β ^ 2 * ((κ * σ) ^ 2 * (1 - 10 * β + β ^ 2) + 2 * (κ * σ) * (1 + β) *
    (1 + β + β ^ 2) + (1 + 4 * β + β ^ 2) * (1 - β) ^ 2)) with hc2
  set c1 := β ^ 2 * (4 * (κ * σ) ^ 3 + 10 * (1 + β) * (κ * σ) ^ 2 +
    4 * (2 + 2 * β ^ 2 - β) * (κ * σ) + 2 * (1 + β) * (1 - β) ^ 2) with hc1
  set c0 := -(β ^ 2 * (2 * β * (κ * σ) + (κ * σ) ^ 2 + 2 * (κ * σ) + (1 - β) ^ 2)) with hc0
  have hneg : c4 < 0 := by
    have : 0 < β ^ 4 * (1 - β) ^ 2 := by have : 0 < 1 - β := by linarith
                                         positivity
    rw [hc4]
    linarith [neg_mul (β ^ 4) ((1 - β) ^ 2)]
  have key : ∀ γ : ℝ, γ ≠ 0 → deltaQuartic β γ κ σ =
      γ ^ 4 * (c4 + c3 * γ⁻¹ + c2 * γ⁻¹ ^ 2 + c1 * γ⁻¹ ^ 3 + c0 * γ⁻¹ ^ 4) := by
    intro γ hγ
    rw [hc4, hc3, hc2, hc1, hc0]
    unfold deltaQuartic
    field_simp
    ring
  have hlim : ∀ l : Filter ℝ, Tendsto (fun γ : ℝ => γ⁻¹) l (𝓝 0) →
      Tendsto (fun γ : ℝ => c4 + c3 * γ⁻¹ + c2 * γ⁻¹ ^ 2 + c1 * γ⁻¹ ^ 3 + c0 * γ⁻¹ ^ 4) l
        (𝓝 c4) := by
    intro l hi
    have := (((tendsto_const_nhds (x := c4)).add (hi.const_mul c3)).add
      ((hi.pow 2).const_mul c2)).add ((hi.pow 3).const_mul c1) |>.add ((hi.pow 4).const_mul c0)
    simpa using this
  constructor
  · have h4 := (tendsto_pow_atTop (α := ℝ) (n := 4) (by norm_num)).atTop_mul_neg hneg
      (hlim atTop tendsto_inv_atTop_zero)
    refine h4.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with γ hγ
    rw [key γ hγ.ne']
  · have hp : Tendsto (fun γ : ℝ => γ ^ 4) atBot atTop := by
      have := (tendsto_pow_atTop (α := ℝ) (n := 4) (by norm_num)).comp tendsto_neg_atBot_atTop
      refine this.congr ?_
      intro γ
      simp only [Function.comp_apply]
      ring
    have h4 := hp.atTop_mul_neg hneg (hlim atBot tendsto_inv_atBot_zero)
    refine h4.congr' ?_
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with γ hγ
    rw [key γ hγ.ne]

/-- Woodford (2003), App. G.6, p. 727: `Δ` has a root strictly between `0` and `1`. -/
theorem deltaQuartic_exists_root (hβ : 0 < β) (hβ1 : β < 1) (hκσ : 0 < κ * σ) :
    ∃ γ, 0 < γ ∧ γ < 1 ∧ deltaQuartic β γ κ σ = 0 := by
  obtain ⟨γ, ⟨h0, h1⟩, hγ⟩ := intermediate_value_Ioo zero_le_one
    (continuous_deltaQuartic (β := β) (κ := κ) (σ := σ)).continuousOn
    ⟨deltaQuartic_zero_neg hβ hκσ, deltaQuartic_one_pos hβ hβ1 hκσ⟩
  exact ⟨γ, h0, h1, hγ⟩

/-- Woodford (2003), App. G.6, p. 727: `Δ` also has a root `> 1` (since `Δ(1) > 0` and
`Δ(+∞) = −∞`), so `Δ` has at most three distinct roots in `(0, 1)`. -/
theorem deltaQuartic_exists_root_gt_one (hβ : 0 < β) (hβ1 : β < 1) (hκσ : 0 < κ * σ) :
    ∃ γ, 1 < γ ∧ deltaQuartic β γ κ σ = 0 := by
  obtain ⟨M, hM⟩ := (tendsto_deltaQuartic (κ := κ) (σ := σ) hβ hβ1).1.eventually
    (eventually_lt_atBot 0) |>.exists_forall_of_atTop
  obtain ⟨γ, ⟨h0, h1⟩, hγ⟩ := intermediate_value_Ioo' (le_max_left 1 (M + 1))
    (continuous_deltaQuartic (β := β) (κ := κ) (σ := σ)).continuousOn
    ⟨hM _ (by linarith [le_max_right 1 (M + 1)]), deltaQuartic_one_pos hβ hβ1 hκσ⟩
  exact ⟨γ, h0, hγ⟩

/-- Woodford (2003), Prop. 8.7, p. 594 and App. G.6, p. 727: **three real roots exist for all
small enough `γ > 0`** — indeed three distinct real roots `0 < λ₁ < 1 < λ₂ < λ₃`. -/
theorem three_real_roots_small_gamma (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ ε > 0, ∀ γ, 0 < γ → γ < ε →
      deltaG β γ κ σ < 0 ∧ lam2 β γ κ σ = (lam2r β γ κ σ : ℂ) ∧
        lam3 β γ κ σ = (lam3r β γ κ σ : ℂ) ∧ 1 < lam2r β γ κ σ ∧
          lam2r β γ κ σ < lam3r β γ κ σ := by
  have hκσ : 0 < κ * σ := mul_pos hκ hσ
  have hc := (continuous_deltaQuartic (β := β) (κ := κ) (σ := σ)).tendsto 0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    (hc.eventually (gt_mem_nhds (deltaQuartic_zero_neg hβ hκσ)))
  refine ⟨min ε 1, lt_min hε one_pos, fun γ hγ0 hγε => ?_⟩
  have hS : Standing β γ κ σ := ⟨hσ, hκ, hβ, hβ1, hγ0, (hγε.trans_le (min_le_right _ _)).le⟩
  have hd : deltaG β γ κ σ < 0 := by
    rw [deltaG_eq_quartic hβ.ne']
    apply hball
    rw [Real.dist_eq, sub_zero, abs_of_pos hγ0]
    exact hγε.trans_le (min_le_left _ _)
  have hD := (deltaG_neg_iff hS).mp hd
  refine ⟨hd, lam2_eq_ofReal rfl hD.le, lam3_eq_ofReal rfl hD.le, one_lt_lam2r hS, ?_⟩
  unfold lam2r lam3r
  have := Real.sqrt_pos.mpr hD
  linarith

/-- Woodford (2003), Prop. 8.7, p. 594 and App. G.6, p. 727: **a complex pair exists for all
`γ` close enough to `1`**. -/
theorem complex_pair_near_one (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ δ > 0, ∀ γ, 1 - δ < γ → γ ≤ 1 →
      0 < deltaG β γ κ σ ∧ (lam2 β γ κ σ).im ≠ 0 ∧
        lam3 β γ κ σ = (starRingEnd ℂ) (lam2 β γ κ σ) ∧ 1 < (lam2 β γ κ σ).re := by
  have hκσ : 0 < κ * σ := mul_pos hκ hσ
  have hc := (continuous_deltaQuartic (β := β) (κ := κ) (σ := σ)).tendsto 1
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
    (hc.eventually (lt_mem_nhds (deltaQuartic_one_pos hβ hβ1 hκσ)))
  refine ⟨min δ 1, lt_min hδ one_pos, fun γ hγ1 hγ2 => ?_⟩
  have hγ0 : 0 < γ := by linarith [min_le_right δ 1]
  have hS : Standing β γ κ σ := ⟨hσ, hκ, hβ, hβ1, hγ0, hγ2⟩
  have hd : 0 < deltaG β γ κ σ := by
    rw [deltaG_eq_quartic hβ.ne']
    apply hball
    rw [Real.dist_eq, abs_of_nonpos (by linarith)]
    linarith [min_le_left δ 1]
  have hD := (deltaG_pos_iff hS).mp hd
  exact ⟨hd, (lam2_complex hS hD).1, lam3_eq_conj hD, (lam2_complex hS hD).2.2⟩

/-! ### The threshold `γ̄ ≈ .35` at the Table 6.1 calibration -/

/-- Woodford (2003), p. 599 with Table 6.1, p. 431 (`β = .99`, `κ = .024`, `σ = 1/.16`, so
`κσ = .15`): `Δ(γ)` as an explicit quartic with rational coefficients. -/
theorem deltaQuartic_calib (γ : ℝ) :
    deltaQuartic (99 / 100) γ (3 / 125) (25 / 4) =
      -96059601 / 1000000000000 * γ ^ 4 + 9011166813 / 15625000000 * γ ^ 3
        - 390948648849 / 250000000000 * γ ^ 2 + 2748896271 / 1250000000 * γ
        - 15181749 / 25000000 := by
  unfold deltaQuartic
  ring

/-- Woodford (2003), p. 599: at the Table 6.1 calibration `Δ` is strictly increasing on
`[0, 1]`. -/
theorem deltaQuartic_calib_strictMonoOn :
    StrictMonoOn (fun γ => deltaQuartic (99 / 100) γ (3 / 125) (25 / 4)) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  simp only [deltaQuartic_calib]
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  set u := x + y with hu
  have h1 : 3 / 4 * u ^ 2 ≤ x ^ 2 + x * y + y ^ 2 := by nlinarith [sq_nonneg (x - y)]
  have hx3 : x ^ 3 ≤ 1 := pow_le_one₀ hx0 hx1
  have hy3 : y ^ 3 ≤ 1 := pow_le_one₀ hy0 hy1
  have hxy2 : x ^ 2 * y ≤ 1 := by
    have : x ^ 2 ≤ 1 := pow_le_one₀ hx0 hx1
    nlinarith [mul_le_mul this hy1 hy0 zero_le_one]
  have hxy3 : x * y ^ 2 ≤ 1 := by
    have : y ^ 2 ≤ 1 := pow_le_one₀ hy0 hy1
    nlinarith [mul_le_mul hx1 this (sq_nonneg y) zero_le_one]
  have h2 : x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3 ≤ 4 := by linarith
  have hq : 0 < 2748896271 / 1250000000 + 4 * (-96059601 / 1000000000000) +
      (-390948648849 / 250000000000) * u + 3 / 4 * (9011166813 / 15625000000) * u ^ 2 := by
    nlinarith [sq_nonneg (u - 390948648849 / 250000000000 /
      (2 * (3 / 4 * (9011166813 / 15625000000))))]
  have hB : 0 < 2748896271 / 1250000000 + (-390948648849 / 250000000000) * (x + y)
      + 9011166813 / 15625000000 * (x ^ 2 + x * y + y ^ 2)
      + (-96059601 / 1000000000000) * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3) := by
    nlinarith
  have hd : 0 < y - x := by linarith
  have key : (-96059601 / 1000000000000 * y ^ 4 + 9011166813 / 15625000000 * y ^ 3
        - 390948648849 / 250000000000 * y ^ 2 + 2748896271 / 1250000000 * y
        - 15181749 / 25000000) -
      (-96059601 / 1000000000000 * x ^ 4 + 9011166813 / 15625000000 * x ^ 3
        - 390948648849 / 250000000000 * x ^ 2 + 2748896271 / 1250000000 * x
        - 15181749 / 25000000) =
      (y - x) * (2748896271 / 1250000000 + (-390948648849 / 250000000000) * (x + y)
      + 9011166813 / 15625000000 * (x ^ 2 + x * y + y ^ 2)
      + (-96059601 / 1000000000000) * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3)) := by ring
  have := mul_pos hd hB
  linarith

/-- Woodford (2003), p. 599 ("for all values `γ < γ̄ = .35` there are three real roots, and for
`γ > γ̄` only rule III is defined"), Table 6.1 calibration: there is a unique threshold
`γ̄ ∈ (.3533, .3534)` with `Δ(γ̄) = 0`, `Δ < 0` on `(0, γ̄)` and `Δ > 0` on `(γ̄, 1]`. -/
theorem calib_gamma_bar :
    ∃ γb : ℝ, 3533 / 10000 < γb ∧ γb < 3534 / 10000 ∧
      deltaG (99 / 100) γb (3 / 125) (25 / 4) = 0 ∧
      (∀ γ, 0 < γ → γ < γb → deltaG (99 / 100) γ (3 / 125) (25 / 4) < 0) ∧
      (∀ γ, γb < γ → γ ≤ 1 → 0 < deltaG (99 / 100) γ (3 / 125) (25 / 4)) ∧
      (∀ γ, 0 < γ → γ ≤ 1 → deltaG (99 / 100) γ (3 / 125) (25 / 4) = 0 → γ = γb) := by
  have hβ : (99 / 100 : ℝ) ≠ 0 := by norm_num
  have hlo : deltaQuartic (99 / 100) (3533 / 10000) (3 / 125) (25 / 4) < 0 := by
    rw [deltaQuartic_calib]; norm_num
  have hhi : 0 < deltaQuartic (99 / 100) (3534 / 10000) (3 / 125) (25 / 4) := by
    rw [deltaQuartic_calib]; norm_num
  obtain ⟨γb, ⟨h0, h1⟩, hγb⟩ :=
    intermediate_value_Ioo (by norm_num : (3533 / 10000 : ℝ) ≤ 3534 / 10000)
    (continuous_deltaQuartic (β := 99 / 100) (κ := 3 / 125) (σ := 25 / 4)).continuousOn ⟨hlo, hhi⟩
  simp only at hγb
  have hmono := deltaQuartic_calib_strictMonoOn
  have hmem : γb ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  refine ⟨γb, h0, h1, ?_, ?_, ?_, ?_⟩
  · rw [deltaG_eq_quartic hβ]; exact hγb
  · intro γ hγ0 hγ
    rw [deltaG_eq_quartic hβ]
    have := hmono ⟨hγ0.le, by linarith⟩ hmem hγ
    simp only at this
    rw [hγb] at this
    exact this
  · intro γ hγ hγ1
    rw [deltaG_eq_quartic hβ]
    have := hmono hmem ⟨by linarith, hγ1⟩ hγ
    simp only at this
    rw [hγb] at this
    exact this
  · intro γ hγ0 hγ1 hz
    rw [deltaG_eq_quartic hβ] at hz
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := hmono ⟨hγ0.le, hγ1⟩ hmem hlt
      simp only at this
      rw [hγb, hz] at this
      exact lt_irrefl _ this
    · have := hmono hmem ⟨hγ0.le, hγ1⟩ hgt
      simp only at this
      rw [hγb, hz] at this
      exact lt_irrefl _ this

/-! ### Continuity of the roots in `γ` -/

/-- A root-continuity lemma (used for Lemma G.2 and the continuity claims of Woodford (2003),
pp. 596–597): if `g a ·` has a unique sign change at `r a` on `[0, 1]`, `g a l → g₀ l` for each
`l`, and `g₀` changes sign exactly at `r₀ ∈ (0, 1)`, then `r a → r₀`. -/
theorem tendsto_root_of_sign {α : Type*} {F : Filter α} {g : α → ℝ → ℝ} {g0 : ℝ → ℝ}
    {r : α → ℝ} {r0 : ℝ} (hr0 : 0 < r0) (hr1 : r0 < 1)
    (hg : ∀ l, Tendsto (fun a => g a l) F (𝓝 (g0 l)))
    (hneg : ∀ l, 0 ≤ l → l < r0 → g0 l < 0) (hpos : ∀ l, r0 < l → l ≤ 1 → 0 < g0 l)
    (hr : ∀ᶠ a in F, (∀ l, r a ≤ l → l ≤ 1 → 0 ≤ g a l) ∧
      (∀ l, 0 ≤ l → l ≤ r a → g a l ≤ 0)) :
    Tendsto r F (𝓝 r0) := by
  rw [tendsto_order]
  constructor
  · intro a' ha'
    have hl0 : 0 ≤ max a' 0 := le_max_right _ _
    have hlr : max a' 0 < r0 := max_lt ha' hr0
    have hev := (hg (max a' 0)).eventually (gt_mem_nhds (hneg _ hl0 hlr))
    filter_upwards [hev, hr] with a h1 h2
    by_contra hc
    push Not at hc
    have := h2.1 (max a' 0) (hc.trans (le_max_left _ _)) (hlr.le.trans hr1.le)
    linarith
  · intro b' hb'
    have hl1 : min b' 1 ≤ 1 := min_le_right _ _
    have hrl : r0 < min b' 1 := lt_min hb' hr1
    have hev := (hg (min b' 1)).eventually (lt_mem_nhds (hpos _ hrl hl1))
    filter_upwards [hev, hr] with a h1 h2
    by_contra hc
    push Not at hc
    have := h2.2 (min b' 1) (hr0.le.trans hrl.le) ((min_le_left _ _).trans hc)
    linarith

/-- Woodford (2003), App. G.6: the sign pattern of `P` on `[0, 1]` around `λ₁`. -/
theorem Precip_sign (h : Standing β γ κ σ) :
    (∀ l, lam1 β γ κ σ ≤ l → l ≤ 1 → 0 ≤ Precip β γ κ σ l) ∧
      (∀ l, 0 ≤ l → l ≤ lam1 β γ κ σ → Precip β γ κ σ l ≤ 0) := by
  constructor
  · intro l hl hl1
    rcases hl.lt_or_eq with hl | hl
    · exact (Precip_pos_of_gt h hl hl1).le
    · rw [← hl, (lam1_spec h).2.2]
  · intro l _ hl
    rcases hl.lt_or_eq with hl | hl
    · exact (Precip_neg_of_lt h hl).le
    · rw [hl, (lam1_spec h).2.2]

/-- `P(λ)` is continuous in `γ` for fixed `λ` (Woodford (2003), App. G.6). -/
theorem continuous_Precip_gamma (l : ℝ) : Continuous (fun γ => Precip β γ κ σ l) := by
  unfold Precip coefA2
  fun_prop

/-- Woodford (2003), pp. 596–597: the root `λ₁` is a continuous function of `γ ∈ (0, 1]`. -/
theorem continuousOn_lam1 (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) :
    ContinuousOn (fun γ => lam1 β γ κ σ) (Set.Ioc 0 1) := by
  intro γ0 hγ0
  have hS0 : Standing β γ0 κ σ := ⟨hσ, hκ, hβ, hβ1, hγ0.1, hγ0.2⟩
  refine tendsto_root_of_sign (g := fun γ l => Precip β γ κ σ l) (lam1_spec hS0).1
    (lam1_spec hS0).2.1 (fun l => ((continuous_Precip_gamma l).tendsto γ0).mono_left
      nhdsWithin_le_nhds) (fun l _ hl => Precip_neg_of_lt hS0 hl)
    (fun l hl hl1 => Precip_pos_of_gt hS0 hl hl1) ?_
  filter_upwards [self_mem_nhdsWithin] with γ hγ
  exact Precip_sign ⟨hσ, hκ, hβ, hβ1, hγ.1, hγ.2⟩

/-- Woodford (2003), pp. 596–597: `S = λ₂ + λ₃` is continuous in `γ ∈ (0, 1]`. -/
theorem continuousOn_sumS (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) :
    ContinuousOn (fun γ => sumS β γ κ σ) (Set.Ioc 0 1) := by
  unfold sumS
  refine ContinuousOn.sub (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
    (continuousOn_lam1 hσ hκ hβ hβ1)
  intro γ hγ
  exact (mul_pos hβ hγ.1).ne'

/-- Woodford (2003), pp. 596–597: `P₂₃ = λ₂λ₃` is continuous in `γ ∈ (0, 1]`. -/
theorem continuousOn_prodP (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) :
    ContinuousOn (fun γ => prodP β γ κ σ) (Set.Ioc 0 1) := by
  unfold prodP coefA2
  refine ContinuousOn.sub (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
    ((continuousOn_sumS hσ hκ hβ hβ1).mul (continuousOn_lam1 hσ hκ hβ hβ1))
  intro γ hγ
  exact (mul_pos hβ hγ.1).ne'

/-- The complex square root `csqrt` is continuous (Woodford (2003), p. 596: at the bifurcation
both branches meet at `0`). -/
theorem continuous_csqrt : Continuous csqrt := by
  unfold csqrt
  fun_prop

/-- Woodford (2003), pp. 596–597: `λ₂` is a continuous (complex-valued) function of
`γ ∈ (0, 1]`, through the bifurcation point `γ̄`. -/
theorem continuousOn_lam2 (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) :
    ContinuousOn (fun γ => lam2 β γ κ σ) (Set.Ioc 0 1) := by
  have hS := continuousOn_sumS hσ hκ hβ hβ1
  have hP := continuousOn_prodP hσ hκ hβ hβ1
  have hD : ContinuousOn (fun γ => discQ β γ κ σ) (Set.Ioc 0 1) := by
    unfold discQ
    exact (hS.pow 2).sub (continuousOn_const.mul hP)
  unfold lam2
  exact ((Complex.continuous_ofReal.comp_continuousOn hS).sub
    (continuous_csqrt.comp_continuousOn hD)).div_const 2

/-- Woodford (2003), pp. 596–597: `λ₃` is a continuous (complex-valued) function of
`γ ∈ (0, 1]`. -/
theorem continuousOn_lam3 (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) :
    ContinuousOn (fun γ => lam3 β γ κ σ) (Set.Ioc 0 1) := by
  have hS := continuousOn_sumS hσ hκ hβ hβ1
  have hP := continuousOn_prodP hσ hκ hβ hβ1
  have hD : ContinuousOn (fun γ => discQ β γ κ σ) (Set.Ioc 0 1) := by
    unfold discQ
    exact (hS.pow 2).sub (continuousOn_const.mul hP)
  unfold lam3
  exact ((Complex.continuous_ofReal.comp_continuousOn hS).add
    (continuous_csqrt.comp_continuousOn hD)).div_const 2

/-! ### Lemma G.2: the limit `γ → 0` -/

/-- Woodford (2003), (3.10), p. 590, and Lemma G.2: the smaller root `μ₁` of
`βμ² − (1 + β + κσ)μ + 1`, i.e. `QuadraticRoots.lam1` at `c = κσ`. -/
noncomputable def mu1 (β κ σ : ℝ) : ℝ := QuadraticRoots.lam1 β (κ * σ)

/-- Woodford (2003), (3.10), p. 590, and Lemma G.2: the larger root `μ₂` of
`βμ² − (1 + β + κσ)μ + 1`, i.e. `QuadraticRoots.lam2` at `c = κσ`. -/
noncomputable def mu2 (β κ σ : ℝ) : ℝ := QuadraticRoots.lam2 β (κ * σ)

/-- Woodford (2003), (3.10), p. 590: `μ₁ + μ₂ = (1 + β + κσ)/β = ρ₁ + ρ₂` with
`ρ₁ = 1 + κσ/β`, `ρ₂ = β⁻¹` of (3.8). -/
theorem mu_sum (hβ : 0 < β) :
    mu1 β κ σ + mu2 β κ σ = 1 + κ * σ / β + β⁻¹ := by
  unfold mu1 mu2
  rw [QuadraticRoots.lam1_add_lam2 hβ]
  field_simp
  ring

/-- Woodford (2003), (3.10), p. 590: `μ₁μ₂ = β⁻¹ = ρ₂`. -/
theorem mu_prod (hβ : 0 < β) (hκσ : 0 < κ * σ) : mu1 β κ σ * mu2 β κ σ = β⁻¹ :=
  QuadraticRoots.lam1_mul_lam2 hβ hκσ

/-- Woodford (2003), (3.10), p. 590: `0 < μ₁ < 1 < μ₂` (`β < 1` is not needed). -/
theorem mu_bounds (hβ : 0 < β) (hκσ : 0 < κ * σ) :
    0 < mu1 β κ σ ∧ mu1 β κ σ < 1 ∧ 1 < mu2 β κ σ :=
  ⟨QuadraticRoots.lam1_pos hβ hκσ, (QuadraticRoots.lam1_lt_one_lt_lam2 hβ hκσ).1,
    (QuadraticRoots.lam1_lt_one_lt_lam2 hβ hκσ).2⟩

/-- Woodford (2003), Lemma G.2, p. 720: at `γ = 0` the reciprocal polynomial reduces to
`P₀(λ) = −(λ − μ₁)(λ − μ₂)`. -/
theorem Precip_gamma_zero (hβ : 0 < β) (hκσ : 0 < κ * σ) (l : ℝ) :
    Precip β 0 κ σ l = -((l - mu1 β κ σ) * (l - mu2 β κ σ)) := by
  have e1 := mu_sum (κ := κ) (σ := σ) hβ
  have e2 := mu_prod hβ hκσ
  have : (l - mu1 β κ σ) * (l - mu2 β κ σ) =
      l ^ 2 - (mu1 β κ σ + mu2 β κ σ) * l + mu1 β κ σ * mu2 β κ σ := by ring
  rw [this, e1, e2]
  unfold Precip coefA2
  field_simp
  ring

/-- Woodford (2003), **Lemma G.2** (fn 44), p. 720: `λ₁ → μ₁` as `γ → 0⁺`. -/
theorem tendsto_lam1_zero (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun γ => lam1 β γ κ σ) (𝓝[>] 0) (𝓝 (mu1 β κ σ)) := by
  have hκσ : 0 < κ * σ := mul_pos hκ hσ
  obtain ⟨hm0, hm1, hm2⟩ := mu_bounds hβ hκσ
  refine tendsto_root_of_sign (g := fun γ l => Precip β γ κ σ l) (g0 := Precip β 0 κ σ) hm0 hm1
    (fun l => ((continuous_Precip_gamma l).tendsto 0).mono_left nhdsWithin_le_nhds) ?_ ?_ ?_
  · intro l _ hl
    rw [Precip_gamma_zero hβ hκσ, neg_lt_zero]
    exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  · intro l hl hl1
    rw [Precip_gamma_zero hβ hκσ, neg_pos]
    exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with γ hγ
    exact Precip_sign ⟨hσ, hκ, hβ, hβ1, hγ.1, hγ.2.le⟩

/-- Woodford (2003), Lemma G.2: eventually (as `γ → 0⁺`) the standing assumptions hold. -/
theorem eventually_standing (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ γ in 𝓝[>] (0 : ℝ), Standing β γ κ σ := by
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with γ hγ
  exact ⟨hσ, hκ, hβ, hβ1, hγ.1, hγ.2.le⟩

/-- Woodford (2003), Lemma G.2, p. 720: `γ(λ₂ + λ₃) → β⁻¹` as `γ → 0⁺`. -/
theorem tendsto_gamma_mul_sumS (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun γ => γ * sumS β γ κ σ) (𝓝[>] 0) (𝓝 β⁻¹) := by
  have hl := tendsto_lam1_zero hσ hκ hβ hβ1
  have hid : Tendsto (fun γ : ℝ => γ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have h : Tendsto (fun γ => (1 + γ + β * γ) / β - γ * lam1 β γ κ σ) (𝓝[>] 0)
      (𝓝 ((1 + 0 + β * 0) / β - 0 * mu1 β κ σ)) :=
    ((((tendsto_const_nhds.add hid).add (hid.const_mul β)).div_const β)).sub (hid.mul hl)
  simp only [add_zero, mul_zero, zero_mul, sub_zero, one_div] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with γ hγ
  have hγ' : (γ : ℝ) ≠ 0 := (Set.mem_Ioi.mp hγ).ne'
  unfold sumS
  field_simp

/-- Woodford (2003), Lemma G.2, p. 720: `γλ₂λ₃ = (β²λ₁)⁻¹ → (β²μ₁)⁻¹` as `γ → 0⁺`. -/
theorem tendsto_gamma_mul_prodP (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun γ => γ * prodP β γ κ σ) (𝓝[>] 0) (𝓝 (β ^ 2 * mu1 β κ σ)⁻¹) := by
  have hκσ : 0 < κ * σ := mul_pos hκ hσ
  have hm := (mu_bounds hβ hκσ).1
  have hl := tendsto_lam1_zero hσ hκ hβ hβ1
  have h := (tendsto_const_nhds (x := β ^ 2)).mul hl |>.inv₀ (by positivity)
  refine h.congr' ?_
  filter_upwards [eventually_standing hσ hκ hβ hβ1] with γ hS
  have hc := vieta_const hS
  have h0 := (lam1_spec hS).1
  have hγ := hS.gamma_pos.ne'
  field_simp
  field_simp at hc
  linear_combination -hc

/-- Woodford (2003), Lemma G.2: `γ²(S² − 4P₂₃) → β⁻²`, so the roots are real and distinct for
small `γ > 0`. -/
theorem eventually_discQ_pos (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ γ in 𝓝[>] (0 : ℝ), 0 < discQ β γ κ σ := by
  have hS := tendsto_gamma_mul_sumS hσ hκ hβ hβ1
  have hP := tendsto_gamma_mul_prodP hσ hκ hβ hβ1
  have hid : Tendsto (fun γ : ℝ => γ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have h := (hS.pow 2).sub ((hid.mul hP).const_mul 4)
  simp only [zero_mul, mul_zero, sub_zero] at h
  have hpos : 0 < β⁻¹ ^ 2 := by positivity
  filter_upwards [h.eventually (lt_mem_nhds hpos), self_mem_nhdsWithin] with γ hγ hγ0
  have hγ0' : 0 < γ := hγ0
  have e : (γ * sumS β γ κ σ) ^ 2 - 4 * (γ * (γ * prodP β γ κ σ)) = γ ^ 2 * discQ β γ κ σ := by
    unfold discQ
    ring
  rw [e] at hγ
  by_contra hc
  push Not at hc
  have : γ ^ 2 * discQ β γ κ σ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg γ) hc
  linarith

/-- Woodford (2003), **Lemma G.2** (fn 44), p. 720: `λ₂ → μ₂` as `γ → 0⁺` (the two smaller roots
approach the roots of the quadratic in (3.10)). -/
theorem tendsto_lam2r_zero (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun γ => lam2r β γ κ σ) (𝓝[>] 0) (𝓝 (mu2 β κ σ)) := by
  have hκσ : 0 < κ * σ := mul_pos hκ hσ
  have hm := (mu_bounds hβ hκσ).1
  have hS := tendsto_gamma_mul_sumS hσ hκ hβ hβ1
  have hP := tendsto_gamma_mul_prodP hσ hκ hβ hβ1
  have hid : Tendsto (fun γ : ℝ => γ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hD := ((hS.pow 2).sub ((hid.mul hP).const_mul 4)).sqrt
  simp only [zero_mul, mul_zero, sub_zero] at hD
  rw [Real.sqrt_sq (by positivity)] at hD
  have h := (hP.const_mul 2).div (hS.add hD) (by positivity)
  have hlim : 2 * (β ^ 2 * mu1 β κ σ)⁻¹ / (β⁻¹ + β⁻¹) = mu2 β κ σ := by
    have e := mu_prod (κ := κ) (σ := σ) hβ hκσ
    have hm' : mu1 β κ σ ≠ 0 := hm.ne'
    field_simp
    field_simp at e
    linear_combination -2 * e
  rw [hlim] at h
  refine h.congr' ?_
  filter_upwards [eventually_standing hσ hκ hβ hβ1, eventually_discQ_pos hσ hκ hβ hβ1] with
    γ hSt hDp
  have hγ := hSt.gamma_pos
  have hsq : Real.sqrt ((γ * sumS β γ κ σ) ^ 2 - 4 * (γ * (γ * prodP β γ κ σ))) =
      γ * Real.sqrt (discQ β γ κ σ) := by
    have e : (γ * sumS β γ κ σ) ^ 2 - 4 * (γ * (γ * prodP β γ κ σ)) =
        γ ^ 2 * discQ β γ κ σ := by unfold discQ; ring
    rw [e, Real.sqrt_mul (sq_nonneg γ), Real.sqrt_sq hγ.le]
  simp only [Pi.div_apply]
  rw [hsq]
  have hs2 := two_lt_sumS hSt
  have hsd := Real.sq_sqrt hDp.le
  have hsn := Real.sqrt_nonneg (discQ β γ κ σ)
  have hden : 0 < sumS β γ κ σ + Real.sqrt (discQ β γ κ σ) := by linarith
  have key : (sumS β γ κ σ + Real.sqrt (discQ β γ κ σ)) *
      (sumS β γ κ σ - Real.sqrt (discQ β γ κ σ)) = 4 * prodP β γ κ σ := by
    have e : (sumS β γ κ σ + Real.sqrt (discQ β γ κ σ)) *
        (sumS β γ κ σ - Real.sqrt (discQ β γ κ σ)) =
        sumS β γ κ σ ^ 2 - Real.sqrt (discQ β γ κ σ) ^ 2 := by ring
    rw [e, hsd]
    unfold discQ
    ring
  unfold lam2r
  rw [div_eq_div_iff (by positivity) (by norm_num)]
  linear_combination (-γ) * key

/-- Woodford (2003), **Lemma G.2**, p. 720: `γλ₃ → β⁻¹` as `γ → 0⁺`. -/
theorem tendsto_gamma_mul_lam3r (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun γ => γ * lam3r β γ κ σ) (𝓝[>] 0) (𝓝 β⁻¹) := by
  have hS := tendsto_gamma_mul_sumS hσ hκ hβ hβ1
  have h2 := tendsto_lam2r_zero hσ hκ hβ hβ1
  have hid : Tendsto (fun γ : ℝ => γ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have h := hS.sub (hid.mul h2)
  simp only [zero_mul, sub_zero] at h
  refine h.congr' (Eventually.of_forall fun γ => ?_)
  unfold lam3r lam2r
  ring

/-- Woodford (2003), **Lemma G.2**, p. 720: `λ₃ → +∞` as `γ → 0⁺`. -/
theorem tendsto_lam3r_atTop (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun γ => lam3r β γ κ σ) (𝓝[>] 0) atTop := by
  have h := tendsto_inv_nhdsGT_zero.atTop_mul_pos (inv_pos.mpr hβ)
    (tendsto_gamma_mul_lam3r hσ hκ hβ hβ1)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with γ hγ
  have hγ' : (γ : ℝ) ≠ 0 := (Set.mem_Ioi.mp hγ).ne'
  field_simp

/-- Woodford (2003), **Lemma G.2**, p. 720 (survey E22 closed: the boundedness of `λ₁, λ₂` the
book assumes is proved, via `tendsto_lam1_zero`, `tendsto_lam2r_zero`): as `γ → 0⁺` the roots are
eventually real and distinct, `λ₁ → μ₁`, `λ₂ → μ₂`, `λ₃ → +∞` and `γλ₃ → β⁻¹`. -/
theorem lemma_G2 (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) :
    (∀ᶠ γ in 𝓝[>] (0 : ℝ), lam2 β γ κ σ = (lam2r β γ κ σ : ℂ) ∧
      lam3 β γ κ σ = (lam3r β γ κ σ : ℂ) ∧ lam2r β γ κ σ < lam3r β γ κ σ) ∧
    Tendsto (fun γ => lam1 β γ κ σ) (𝓝[>] 0) (𝓝 (mu1 β κ σ)) ∧
    Tendsto (fun γ => lam2r β γ κ σ) (𝓝[>] 0) (𝓝 (mu2 β κ σ)) ∧
    Tendsto (fun γ => lam3r β γ κ σ) (𝓝[>] 0) atTop ∧
    Tendsto (fun γ => γ * lam3r β γ κ σ) (𝓝[>] 0) (𝓝 β⁻¹) := by
  refine ⟨?_, tendsto_lam1_zero hσ hκ hβ hβ1, tendsto_lam2r_zero hσ hκ hβ hβ1,
    tendsto_lam3r_atTop hσ hκ hβ hβ1, tendsto_gamma_mul_lam3r hσ hκ hβ hβ1⟩
  filter_upwards [eventually_discQ_pos hσ hκ hβ hβ1] with γ hD
  refine ⟨lam2_eq_ofReal rfl hD.le, lam3_eq_ofReal rfl hD.le, ?_⟩
  unfold lam2r lam3r
  have := Real.sqrt_pos.mpr hD
  linarith

end Woodford.OptimalPolicyRules.CubicRoots
