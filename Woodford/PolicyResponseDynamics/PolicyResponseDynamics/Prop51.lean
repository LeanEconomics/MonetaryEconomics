/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PolicyResponseDynamics.ForwardSystems
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Proposition 5.1: optimal pricesetting with endogenous capital

Woodford (2003), *Interest and Prices*, Chapter 5, §3.2, pp. 357–360, and Appendix D.2,
pp. 688–690.

With firm-specific capital, a firm that resets its price must foresee how its relative capital
stock `k̃_t(i)` will evolve while its price stays fixed. The firm-level capital Euler equation
(Ch. 5 (3.7)) and the demand curve give the second-order relation (D.3)
`E_t Q(L) k̃_{t+2}(i) = M E_t p̂_{t+1}(i)`, whose unique bounded solution is (D.4); substituting it
into the Calvo first-order condition (3.13) and averaging over the resetting firms gives (3.14).

The model equations of the investment block — the firm-level (3.7), (3.11)–(3.13) — are taken
as given (their log-linearisation is another module's subject), with the coefficients
`ρ_y, ρ_k, ν, ω, θ, ε_ψ, α, β` (and `δ`) as parameters.

## Main results

* L1 `D3_of_firm_capital_euler`: (D.3) from the firm-level and aggregate (3.7) and the demand
  curve. The first display on p. 689 has `Y_t` where `Y_{t+1}` belongs (survey error 6):
  `printed_display_iff` (the printed display holds iff `E_t Y_{t+1} = E_t Y_t`) and
  `printed_display_fails`.
* L2 `mu1_pos`, `mu1_lt_one`, `inv_beta_lt_mu2`, `Qpoly_factor`, `Ppoly_factor`,
  `eq_mu2_of_root`: the roots of (D.2)/(D.3), `0 < μ₁ < 1 < β⁻¹ < μ₂`, and the factorisation
  `Q(L) = β(1 − μ₁L)(1 − μ₂L)`. L3 `M_eq_Qpoly_one`:
  `M = −θ(ρ_y/ρ_k)Q(1) = βθ(ρ_y/ρ_k)μ₂(1−μ₁)(1−μ₂⁻¹)`.
* L4 `D4_of_D3` (uniqueness) and `D4_solution` (existence): (D.3) has a unique bounded solution
  for each initial capital stock, `k̃_{t+1} = μ₁k̃_t − z_t` with
  `z_t = β⁻¹M ∑_{j≥1} μ₂^{-j} E_t p̂_{t+j}`.
* L5 `D5_iterate`, `D5`: the iterated law of motion and (D.5), a genuine Cauchy-product
  interchange of a double series.
* L6 `D6_coeff`, `D6`, `D6_eq`: the double series (D.6); the coefficient of `E_t p̂_{t+n}` is
  `∑_{j<n} (αβ)ʲ μ₂^{j−n}`, which equals `(μ₂^{-n} − (αβ)ⁿ)/(1 − αβμ₂)` when `αβμ₂ ≠ 1`
  (`cD6_closed`) and `n μ₂^{-n}` when `αβμ₂ = 1` (`cD6_eq_case`); the printed (D.6) divides by
  zero in that case.
* L7 (modelling hypothesis, stated explicitly): the cross-section of date-`t` resetters is a
  probability space `(ι, wt)`; the average relative capital stock of the resetters is zero and
  the average of `E_t p̂_{t+n}(i)` is `p̂*_t − ∑_{j=1}^n E_t π_{t+j}`.
* `prop51`: Proposition 5.1, identity (3.14) in full (genuine infinite sums), for
  `αβμ₂ ≠ 1`; `prop51_eq_case`: the corrected relation when `αβμ₂ = 1`.
* Positivity: the printed claim "`a > 0, b > 0`" is FALSE in general. `b_pos_iff`,
  `b_neg_of`: `sign b = sign(1 − αβμ₂)`; `book_calibration_a_neg`: at the book's calibration
  (Table 5.1, `δ = .012`) with `ε_ψ = 0.1`, `a < 0` and `b < 0`. Corrected statement
  `a_pos_b_pos`: `αβμ₂ < 1 ⇒ a > 0 ∧ b > 0`, and `alpha_beta_mu2_lt_one_iff`: this holds iff
  `c < (1 − α)(1 − αβ)/α`, i.e. iff `ε_ψ > (1 − β(1−δ))ρ_k α/((1 − α)(1 − αβ))`.
* `a_sub_b_eq`, `a_sub_b_pos`: `a − b > 0` always, when `ρ_y ≥ ω` (true for the book's
  primitive definitions of `ρ_y` and `ω`, `primitives_admissible`); without `ρ_y ≥ ω` it fails
  (`a_sub_b_neg_example`).
-/

namespace Woodford.PolicyResponseDynamics.Prop51

open Filter Topology MeasureTheory

/-! ### Parameters -/

/-- Woodford (2003), Ch. 5, pp. 356–359: the coefficients of the investment model. `α` is the
Calvo probability of not resetting, `β` the discount factor, `δ` the depreciation rate, `θ` the
elasticity of demand, `ω` the elasticity of real marginal cost, `ν` the elasticity of the
marginal disutility of labour, and `ρy`, `ρk` the elasticities of the marginal valuation of
capital (3.7). The adjustment-cost parameter `ε_ψ` is a separate argument. -/
structure Params where
  α : ℝ
  β : ℝ
  δ : ℝ
  θ : ℝ
  ω : ℝ
  ν : ℝ
  ρy : ℝ
  ρk : ℝ

variable (P : Params)

/-- Woodford (2003), Ch. 5, pp. 355–359: the parameter restrictions the book states or uses:
`0 < α < 1`, `0 < β < 1`, `0 < δ < 1`, `θ > 0`, `0 < ν < ω`, `ρ_k > 0` and `ρ_y = ρ_k + ν`
(p. 356, "`ρ_y > ρ_k ≡ ρ_y − ν > 0`"). -/
structure Admissible where
  hα0 : 0 < P.α
  hα1 : P.α < 1
  hβ0 : 0 < P.β
  hβ1 : P.β < 1
  hδ0 : 0 < P.δ
  hδ1 : P.δ < 1
  hθ : 0 < P.θ
  hν : 0 < P.ν
  hων : P.ν < P.ω
  hρk : 0 < P.ρk
  hρy : P.ρy = P.ρk + P.ν

/-- Woodford (2003), (3.7) p. 356: the coefficient `1 − β(1 − δ)`. -/
def cprime : ℝ := 1 - P.β * (1 - P.δ)

/-- Woodford (2003), (D.2)–(D.3) pp. 688–689: `c = (1 − β(1 − δ))ρ_k ε_ψ⁻¹`. -/
noncomputable def cD (ε : ℝ) : ℝ := cprime P * P.ρk / ε

/-- Woodford (2003), Prop. 5.1, p. 359: `M = (1 − β(1 − δ))ρ_y θ ε_ψ⁻¹`. -/
noncomputable def MD (ε : ℝ) : ℝ := cprime P * P.ρy * P.θ / ε

variable {P}

/-- Woodford (2003), p. 356: `1 − β(1 − δ) > 0`. -/
theorem cprime_pos (hP : Admissible P) : 0 < cprime P := by
  have h1 := hP.hβ0; have h2 := hP.hβ1; have h3 := hP.hδ0; have h4 := hP.hδ1
  unfold cprime; nlinarith

/-- Woodford (2003), (D.2) p. 688: `c > 0` for `ε_ψ > 0`. -/
theorem cD_pos (hP : Admissible P) {ε : ℝ} (hε : 0 < ε) : 0 < cD P ε := by
  have := cprime_pos hP; have := hP.hρk
  unfold cD; positivity

/-- Woodford (2003), Prop. 5.1, p. 359: `M > 0` for `ε_ψ > 0`. -/
theorem MD_pos (hP : Admissible P) {ε : ℝ} (hε : 0 < ε) : 0 < MD P ε := by
  have := cprime_pos hP; have := hP.hρk; have := hP.hν; have := hP.hθ
  have : 0 < P.ρy := by rw [hP.hρy]; linarith
  unfold MD; positivity

/-! ### L2: the roots of (D.2) and the factorisation of `Q(L)` -/

/-- Woodford (2003), (D.3) p. 689: `Q(z) = β − (1 + β + c)z + z²`. -/
def Qpoly (β c z : ℝ) : ℝ := β - (1 + β + c) * z + z ^ 2

/-- Woodford (2003), (3.15)/(D.2) pp. 359, 688: `P(μ) = βμ² − (1 + β + c)μ + 1`. -/
def Ppoly (β c μ : ℝ) : ℝ := β * μ ^ 2 - (1 + β + c) * μ + 1

/-- Woodford (2003), (D.2) p. 688: the discriminant of `P`. -/
def discr (β c : ℝ) : ℝ := (1 + β + c) ^ 2 - 4 * β

/-- Woodford (2003), (D.2) p. 688: the smaller root `μ₁` of `P`. -/
noncomputable def mu1 (β c : ℝ) : ℝ := (1 + β + c - √(discr β c)) / (2 * β)

/-- Woodford (2003), (3.15)/(D.2) pp. 359, 688: the larger root `μ₂` of `P`. -/
noncomputable def mu2 (β c : ℝ) : ℝ := (1 + β + c + √(discr β c)) / (2 * β)

/-- Woodford (2003), App. D.2, p. 689: the discriminant exceeds `4βc` plus `(1 − β + c)²`. -/
theorem discr_eq (β c : ℝ) : discr β c = (1 - β + c) ^ 2 + 4 * β * c := by
  unfold discr; ring

/-- Woodford (2003), App. D.2, p. 689: `√disc` squared. -/
theorem sqrt_discr_sq {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    √(discr β c) ^ 2 = discr β c :=
  Real.sq_sqrt (by rw [discr_eq]; positivity)

/-- Woodford (2003), App. D.2, p. 689 (L2): Vieta, `β(μ₁ + μ₂) = 1 + β + c`. -/
theorem vieta_sum {β c : ℝ} (hβ : 0 < β) : β * (mu1 β c + mu2 β c) = 1 + β + c := by
  unfold mu1 mu2; field_simp; ring

/-- Woodford (2003), App. D.2, p. 689 (L2): Vieta, `β μ₁ μ₂ = 1`. -/
theorem vieta_prod {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : β * (mu1 β c * mu2 β c) = 1 := by
  have hs := sqrt_discr_sq hβ hc
  unfold mu1 mu2; field_simp
  unfold discr at hs ⊢
  linear_combination (-1 : ℝ) * hs

/-- Woodford (2003), App. D.2, p. 689 (L2): `P(μ) = β(μ − μ₁)(μ − μ₂)`. -/
theorem Ppoly_factor {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (μ : ℝ) :
    Ppoly β c μ = β * (μ - mu1 β c) * (μ - mu2 β c) := by
  have h1 := vieta_sum (c := c) hβ
  have h2 := vieta_prod hβ hc
  unfold Ppoly
  linear_combination μ * h1 - h2

/-- Woodford (2003), App. D.2, p. 689 (L2): `Q(z) = β(1 − μ₁z)(1 − μ₂z)`. -/
theorem Qpoly_factor {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (z : ℝ) :
    Qpoly β c z = β * (1 - mu1 β c * z) * (1 - mu2 β c * z) := by
  have h1 := vieta_sum (c := c) hβ
  have h2 := vieta_prod hβ hc
  unfold Qpoly
  linear_combination z * h1 - z ^ 2 * h2

/-- Woodford (2003), App. D.2, p. 689 (L2): `μ₁` and `μ₂` are roots of `P`. -/
theorem Ppoly_mu1 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : Ppoly β c (mu1 β c) = 0 := by
  rw [Ppoly_factor hβ hc]; ring

/-- Woodford (2003), (3.15) p. 359 (L2): `μ₂` is a root of `P`. -/
theorem Ppoly_mu2 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : Ppoly β c (mu2 β c) = 0 := by
  rw [Ppoly_factor hβ hc]; ring

/-- Woodford (2003), App. D.2, p. 689 (L2): the signs used in the book's root-location
argument, `Q(0) = β > 0`, `Q(β) = −cβ < 0`, `Q(1) = −c < 0`. -/
theorem Qpoly_signs {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    Qpoly β c 0 = β ∧ Qpoly β c β = -(c * β) ∧ Qpoly β c 1 = -c ∧ Qpoly β c β < 0 ∧
      Qpoly β c 1 < 0 := by
  refine ⟨by unfold Qpoly; ring, by unfold Qpoly; ring, by unfold Qpoly; ring, ?_, ?_⟩ <;>
  · unfold Qpoly; nlinarith

/-- Woodford (2003), App. D.2, p. 689 (L2): `μ₁ > 0`. -/
theorem mu1_pos {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : 0 < mu1 β c := by
  have hs := sqrt_discr_sq hβ hc
  have hs0 := Real.sqrt_nonneg (discr β c)
  unfold mu1
  apply div_pos _ (by positivity)
  unfold discr at hs hs0 ⊢
  nlinarith

/-- Woodford (2003), App. D.2, p. 689 (L2): `μ₁ < 1`. -/
theorem mu1_lt_one {β c : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hc : 0 < c) : mu1 β c < 1 := by
  have hs := sqrt_discr_sq hβ hc
  have hs0 := Real.sqrt_nonneg (discr β c)
  have hlt : 1 - β + c < √(discr β c) := by
    rw [Real.lt_sqrt (by linarith), discr_eq]; nlinarith
  unfold mu1
  rw [div_lt_one (by positivity)]
  linarith

/-- Woodford (2003), App. D.2, p. 689 (L2): `β⁻¹ < μ₂`. -/
theorem inv_beta_lt_mu2 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : β⁻¹ < mu2 β c := by
  have hs0 := Real.sqrt_nonneg (discr β c)
  have hlt : 1 - β - c < √(discr β c) := by
    rcases lt_or_ge (1 - β - c) 0 with h | h
    · linarith
    · rw [Real.lt_sqrt h, discr]; nlinarith
  unfold mu2
  rw [lt_div_iff₀ (by positivity)]
  have : β⁻¹ * (2 * β) = 2 := by field_simp
  rw [this]
  linarith

/-- Woodford (2003), App. D.2, p. 689 (L2): `1 < μ₂`. -/
theorem one_lt_mu2 {β c : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hc : 0 < c) : 1 < mu2 β c :=
  lt_trans (one_lt_inv₀ hβ |>.mpr hβ1) (inv_beta_lt_mu2 hβ hc)

/-- Woodford (2003), App. D.2, p. 689 (L2): the full root location `0 < μ₁ < 1 < β⁻¹ < μ₂`. -/
theorem root_location {β c : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hc : 0 < c) :
    0 < mu1 β c ∧ mu1 β c < 1 ∧ 1 < β⁻¹ ∧ β⁻¹ < mu2 β c :=
  ⟨mu1_pos hβ hc, mu1_lt_one hβ hβ1 hc, (one_lt_inv₀ hβ).mpr hβ1, inv_beta_lt_mu2 hβ hc⟩

/-- Woodford (2003), (3.15) p. 359: `μ₂` is THE root of `P` greater than `β⁻¹`. -/
theorem eq_mu2_of_root {β c μ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hc : 0 < c)
    (hP : Ppoly β c μ = 0) (hμ : β⁻¹ < μ) : μ = mu2 β c := by
  rw [Ppoly_factor hβ hc] at hP
  have h1 : μ - mu1 β c ≠ 0 := by
    have := mu1_lt_one hβ hβ1 hc
    have := (one_lt_inv₀ hβ).mpr hβ1
    intro h; linarith
  have : μ - mu2 β c = 0 := by
    rcases mul_eq_zero.mp hP with h | h
    · rcases mul_eq_zero.mp h with h | h
      · linarith
      · exact absurd h h1
    · exact h
  linarith

/-- Woodford (2003), App. D.2, p. 689 (L2, the book's form): the roots of `Q` are
`μ₂⁻¹ ∈ (0, β)` and `μ₁⁻¹ > 1`. -/
theorem Qpoly_roots {β c : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hc : 0 < c) :
    Qpoly β c (mu2 β c)⁻¹ = 0 ∧ 0 < (mu2 β c)⁻¹ ∧ (mu2 β c)⁻¹ < β ∧
      Qpoly β c (mu1 β c)⁻¹ = 0 ∧ 1 < (mu1 β c)⁻¹ := by
  have h1 := mu1_pos hβ hc
  have h2 := mu1_lt_one hβ hβ1 hc
  have h3 := inv_beta_lt_mu2 hβ hc
  have h4 : 0 < mu2 β c := lt_trans (inv_pos.mpr hβ) h3
  refine ⟨?_, inv_pos.mpr h4, ?_, ?_, (one_lt_inv₀ h1).mpr h2⟩
  · rw [Qpoly_factor hβ hc, mul_inv_cancel₀ h4.ne']; ring
  · rw [inv_lt_comm₀ h4 hβ]; exact h3
  · rw [Qpoly_factor hβ hc, mul_inv_cancel₀ h1.ne']; ring

/-- Woodford (2003), App. D.2, p. 689 (L3): `M = −θ(ρ_y/ρ_k)Q(1) = βθ(ρ_y/ρ_k)μ₂(1−μ₁)(1−μ₂⁻¹)`
(true, but not used by the book's argument). -/
theorem M_eq_Qpoly_one (hP : Admissible P) {ε : ℝ} (hε : 0 < ε) :
    MD P ε = -(P.θ * (P.ρy / P.ρk) * Qpoly P.β (cD P ε) 1) ∧
      MD P ε = P.β * P.θ * (P.ρy / P.ρk) * mu2 P.β (cD P ε) * (1 - mu1 P.β (cD P ε)) *
        (1 - (mu2 P.β (cD P ε))⁻¹) := by
  have hc := cD_pos hP hε
  have hβ := hP.hβ0
  have hρk := hP.hρk.ne'
  have h2 : mu2 P.β (cD P ε) ≠ 0 :=
    (lt_trans (inv_pos.mpr hβ) (inv_beta_lt_mu2 hβ hc)).ne'
  have hQ := Qpoly_factor hβ hc 1
  have e1 : MD P ε = -(P.θ * (P.ρy / P.ρk) * Qpoly P.β (cD P ε) 1) := by
    unfold MD Qpoly cD; field_simp; ring
  refine ⟨e1, ?_⟩
  rw [e1, hQ]
  field_simp
  ring

/-! ### Real-sequence lemmas: double series (L5, L6) and partial-sum series (L7) -/

/-- Woodford (2003), App. D.2, (D.5)–(D.6), p. 690: a summable double series over `ℕ × ℕ`
equals its iterated sum and its sum along antidiagonals `j + i = n`. -/
theorem tsum_tsum_eq_tsum_antidiagonal (f : ℕ × ℕ → ℝ) (hf : Summable f) :
    ∑' j, ∑' i, f (j, i) = ∑' n, ∑ kl ∈ Finset.antidiagonal n, f kl := by
  rw [← hf.tsum_prod]
  conv_rhs => congr; ext; rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq f]
  exact (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr hf).tsum_sigma'
    (fun n ↦ (hasSum_fintype _).summable)

/-- Woodford (2003), App. D.2, (D.6), p. 690: the double series `xʲ mⁱ y_{j+i}` is absolutely
summable for `|x|, |m| < 1` and bounded `y`. -/
theorem summable_geom_pair {x m B : ℝ} (hx : |x| < 1) (hm : |m| < 1) {y : ℕ → ℝ}
    (hy : ∀ n, |y n| ≤ B) :
    Summable (fun p : ℕ × ℕ => x ^ p.1 * (m ^ p.2 * y (p.1 + p.2))) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hy 0)
  have h1 : Summable (fun j : ℕ => |x| ^ j) := summable_geometric_of_lt_one (abs_nonneg x) hx
  have h2 : Summable (fun i : ℕ => |m| ^ i * B) :=
    (summable_geometric_of_lt_one (abs_nonneg m) hm).mul_right B
  refine Summable.of_norm_bounded
    (h1.mul_of_nonneg h2 (fun j => by positivity) (fun i => by positivity)) (fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hy _) (by positivity))
    (by positivity)

/-- Woodford (2003), App. D.2, (D.6), p. 690 (L6, the interchange): for `|x|, |m| < 1` and
bounded `y`, `∑_j xʲ ∑_i mⁱ y_{j+i} = ∑_n (∑_{k ≤ n} xᵏ m^{n−k}) y_n`. -/
theorem tsum_geom_tsum_geom {x m B : ℝ} (hx : |x| < 1) (hm : |m| < 1) {y : ℕ → ℝ}
    (hy : ∀ n, |y n| ≤ B) :
    ∑' j, x ^ j * ∑' i, m ^ i * y (j + i) =
      ∑' n, (∑ k ∈ Finset.range (n + 1), x ^ k * m ^ (n - k)) * y n := by
  have hs := summable_geom_pair hx hm hy
  have h1 : ∑' j, x ^ j * ∑' i, m ^ i * y (j + i) =
      ∑' j, ∑' i, (fun p : ℕ × ℕ => x ^ p.1 * (m ^ p.2 * y (p.1 + p.2))) (j, i) := by
    refine tsum_congr fun j => ?_
    rw [← tsum_mul_left]
  rw [h1, tsum_tsum_eq_tsum_antidiagonal _ hs]
  refine tsum_congr fun n => ?_
  have h2 := Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k l => x ^ k * (m ^ l * y (k + l))) n
  rw [h2, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have : k + (n - k) = n := by have := Finset.mem_range.mp hk; omega
  rw [this]; ring

/-- Woodford (2003), (D.6), p. 690: the coefficient `C_N = ∑_{k<N} xᵏ m^{N−k}` of `E_t p̂_{t+N}`
in `∑_j (αβ)ʲ E_t z_{t+j}` (with `x = αβ`, `m = μ₂⁻¹`, up to the factor `β⁻¹M`). -/
def cD6 (x m : ℝ) (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, x ^ k * m ^ (N - k)

/-- Woodford (2003), (D.6), p. 690: `C_0 = 0`. -/
theorem cD6_zero (x m : ℝ) : cD6 x m 0 = 0 := by simp [cD6]

/-- Woodford (2003), (D.6), p. 690: `C_{N+1} = m C_N + xᴺ m`. -/
theorem cD6_succ (x m : ℝ) (N : ℕ) : cD6 x m (N + 1) = m * cD6 x m N + x ^ N * m := by
  unfold cD6
  rw [Finset.sum_range_succ, Finset.mul_sum, show N + 1 - N = 1 by omega, pow_one]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have : N + 1 - k = N - k + 1 := by have := Finset.mem_range.mp hk; omega
  rw [this, pow_succ]; ring

/-- Woodford (2003), (D.6), p. 690: `C_{N+1} = m ∑_{k ≤ N} xᵏ m^{N−k}`. -/
theorem cD6_succ_eq (x m : ℝ) (N : ℕ) :
    cD6 x m (N + 1) = (∑ k ∈ Finset.range (N + 1), x ^ k * m ^ (N - k)) * m := by
  unfold cD6
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have : N + 1 - k = N - k + 1 := by have := Finset.mem_range.mp hk; omega
  rw [this, pow_succ]; ring

/-- Woodford (2003), (D.6), p. 690: `(m − x) C_N = m(mᴺ − xᴺ)`. -/
theorem cD6_mul (x m : ℝ) (N : ℕ) : (m - x) * cD6 x m N = m * (m ^ N - x ^ N) := by
  induction N with
  | zero => simp [cD6_zero]
  | succ N ih => rw [cD6_succ, pow_succ, pow_succ]; linear_combination m * ih

/-- Woodford (2003), (D.6), p. 690 (L6, case `αβμ₂ ≠ 1`): with `m = μ₂⁻¹`,
`(1 − xμ₂) C_N = μ₂^{-N} − xᴺ`, i.e. `C_N = (μ₂^{-N} − (αβ)ᴺ)/(1 − αβμ₂)`. -/
theorem cD6_closed {x μ₂ : ℝ} (hμ : μ₂ ≠ 0) (N : ℕ) :
    (1 - x * μ₂) * cD6 x μ₂⁻¹ N = μ₂⁻¹ ^ N - x ^ N := by
  have h := cD6_mul x μ₂⁻¹ N
  have e : 1 - x * μ₂ = μ₂ * (μ₂⁻¹ - x) := by field_simp
  rw [e, mul_assoc, h, ← mul_assoc, mul_inv_cancel₀ hμ, one_mul]

/-- Woodford (2003), (D.6), p. 690 (L6, case `αβμ₂ = 1`, where the printed (D.6) is `0/0`):
`C_N = N μ₂^{-N}`. -/
theorem cD6_eq_case (x : ℝ) (N : ℕ) : cD6 x x N = N * x ^ N := by
  induction N with
  | zero => simp [cD6_zero]
  | succ N ih => rw [cD6_succ, ih]; push_cast; ring

/-- Woodford (2003), (D.6), p. 690: `|C_N| ≤ N ρᴺ` when `|x|, |m| ≤ ρ`. -/
theorem abs_cD6_le {x m ρ : ℝ} (hx : |x| ≤ ρ) (hm : |m| ≤ ρ) (N : ℕ) :
    |cD6 x m N| ≤ N * ρ ^ N := by
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans hx
  unfold cD6
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ k ∈ Finset.range N, |x ^ k * m ^ (N - k)| ≤ ρ ^ N := by
    intro k hk
    have hk' : k ≤ N := (Finset.mem_range.mp hk).le
    rw [abs_mul, abs_pow, abs_pow]
    calc |x| ^ k * |m| ^ (N - k) ≤ ρ ^ k * ρ ^ (N - k) := by gcongr
      _ = ρ ^ N := by rw [← pow_add, Nat.add_sub_cancel' hk']
  refine (Finset.sum_le_sum hb).trans ?_
  simp

/-- Woodford (2003), (D.6), p. 690 (L6 in full, any `|x|, |m| < 1`):
`∑_j xʲ ∑_{i ≥ 0} m^{i+1} P_{j+i+1} = ∑_{n ≥ 1} C_n P_n`. -/
theorem D6_real {x m B : ℝ} (hx : |x| < 1) (hm : |m| < 1) {P : ℕ → ℝ}
    (hP : ∀ n, |P n| ≤ B) :
    ∑' j, x ^ j * ∑' i, m ^ (i + 1) * P (j + i + 1) = ∑' n, cD6 x m (n + 1) * P (n + 1) := by
  have hy : ∀ n, |m * P (n + 1)| ≤ |m| * B := fun n => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hP _) (abs_nonneg m)
  have h := tsum_geom_tsum_geom hx hm hy
  have e1 : ∀ j, ∑' i, m ^ (i + 1) * P (j + i + 1) = ∑' i, m ^ i * (m * P (j + i + 1)) :=
    fun j => tsum_congr fun i => by ring
  simp_rw [e1]
  rw [h]
  refine tsum_congr fun n => ?_
  rw [cD6_succ_eq]; ring

/-- Woodford (2003), App. D.2, p. 690 (L5, the integrated law of motion): if
`K_{n+1} = μ₁ K_n − Z_n` then `K_n = μ₁ⁿ K_0 − ∑_{j<n} μ₁^{n−1−j} Z_j`. -/
theorem D5_iterate {μ₁ : ℝ} {K Z : ℕ → ℝ} (hK : ∀ n, K (n + 1) = μ₁ * K n - Z n) (n : ℕ) :
    K n = μ₁ ^ n * K 0 - ∑ j ∈ Finset.range n, μ₁ ^ (n - 1 - j) * Z j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hK, ih, Finset.sum_range_succ, mul_sub, Finset.mul_sum, pow_succ]
    have : ∀ j ∈ Finset.range n, μ₁ * (μ₁ ^ (n - 1 - j) * Z j) = μ₁ ^ (n + 1 - 1 - j) * Z j := by
      intro j hj
      have : n + 1 - 1 - j = n - 1 - j + 1 := by have := Finset.mem_range.mp hj; omega
      rw [this, pow_succ]; ring
    rw [Finset.sum_congr rfl this, Nat.add_sub_cancel, Nat.sub_self, pow_zero]
    ring

/-- Woodford (2003), (D.5), p. 690 (L5 in full, a Cauchy product of two series): for
`|x| < 1`, `|xμ₁| < 1`, bounded `Z` and `K_{n+1} = μ₁K_n − Z_n`,
`∑ xⁿ K_n = K_0/(1 − xμ₁) − x/(1 − xμ₁) ∑ xⁿ Z_n`. -/
theorem D5_real {x μ₁ B : ℝ} (hx : |x| < 1) (hxμ : |x * μ₁| < 1) {K Z : ℕ → ℝ}
    (hK : ∀ n, K (n + 1) = μ₁ * K n - Z n) (hZ : ∀ n, |Z n| ≤ B) :
    ∑' n, x ^ n * K n = K 0 / (1 - x * μ₁) - x / (1 - x * μ₁) * ∑' n, x ^ n * Z n := by
  have hne : 1 - x * μ₁ ≠ 0 := by
    intro h; have : x * μ₁ = 1 := by linarith
    rw [this, abs_one] at hxμ; exact lt_irrefl _ hxμ
  set f : ℕ → ℝ := fun k => x ^ k * Z k with hf_def
  set g : ℕ → ℝ := fun i => (x * μ₁) ^ i with hg_def
  have hf : Summable fun k => ‖f k‖ := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      ((summable_geometric_of_lt_one (abs_nonneg x) hx).mul_right B)
    rw [Real.norm_eq_abs, hf_def, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hZ k) (by positivity)
  have hg : Summable fun i => ‖g i‖ := by
    simpa [hg_def, norm_pow, Real.norm_eq_abs] using
      summable_geometric_of_lt_one (abs_nonneg _) hxμ
  set W : ℕ → ℝ := fun n => ∑ k ∈ Finset.range (n + 1), f k * g (n - k) with hW_def
  have hWs : Summable W := (summable_norm_sum_mul_range_of_summable_norm hf hg).of_norm
  have hcauchy : (∑' n, f n) * (∑' n, g n) = ∑' n, W n :=
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hg
  have hgsum : ∑' n, g n = (1 - x * μ₁)⁻¹ := tsum_geometric_of_abs_lt_one hxμ
  set V : ℕ → ℝ := fun n => x ^ n * ∑ j ∈ Finset.range n, μ₁ ^ (n - 1 - j) * Z j with hV_def
  have hVsucc : ∀ n, V (n + 1) = x * W n := by
    intro n
    simp only [hV_def, hW_def, hf_def, hg_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have e : n + 1 - 1 - k = n - k := by omega
    rw [e, mul_pow]
    have e2 : x ^ (n + 1) = x * x ^ k * x ^ (n - k) := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hk', pow_succ]; ring
    rw [e2]; ring
  have hVs : Summable V := by
    rw [← summable_nat_add_iff 1]
    exact (hWs.mul_left x).congr fun n => (hVsucc n).symm
  have hVsum : ∑' n, V n = x * ∑' n, W n := by
    rw [hVs.tsum_eq_zero_add, ← tsum_mul_left]
    simp only [hV_def, pow_zero, Finset.range_zero, Finset.sum_empty, mul_zero, zero_add]
    exact tsum_congr fun n => hVsucc n
  have hGs : Summable fun n => (x * μ₁) ^ n * K 0 :=
    (summable_geometric_of_abs_lt_one hxμ).mul_right _
  have hKn : ∀ n, x ^ n * K n = (x * μ₁) ^ n * K 0 - V n := by
    intro n
    rw [D5_iterate hK n, hV_def, mul_pow]; ring
  rw [tsum_congr hKn, hGs.tsum_sub hVs, tsum_mul_right, tsum_geometric_of_abs_lt_one hxμ,
    hVsum, ← hcauchy, hgsum]
  field_simp

/-- Woodford (2003), App. D.2, p. 690 (L7): for `|r| < 1` and bounded `y`,
`∑ₙ rⁿ ∑_{j<n} y_j = r/(1 − r) ∑ rʲ y_j` (both series converge). -/
theorem tsum_geom_partialSum {r B : ℝ} (hr : |r| < 1) {y : ℕ → ℝ} (hy : ∀ n, |y n| ≤ B) :
    Summable (fun n => r ^ n * ∑ j ∈ Finset.range n, y j) ∧
      ∑' n, r ^ n * ∑ j ∈ Finset.range n, y j = r / (1 - r) * ∑' j, r ^ j * y j := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hy 0)
  have hne : 1 - r ≠ 0 := by
    intro h; have : r = 1 := by linarith
    rw [this, abs_one] at hr; exact lt_irrefl _ hr
  have hY : ∀ n, |∑ j ∈ Finset.range n, y j| ≤ n * B := by
    intro n
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun j _ => hy j).trans ?_
    simp
  have hS : Summable (fun n => r ^ n * ∑ j ∈ Finset.range n, y j) := by
    have h1 : Summable (fun n : ℕ => B * ((n : ℝ) ^ 1 * |r| ^ n)) :=
      (summable_pow_mul_geometric_of_norm_lt_one 1 (by simpa using hr)).mul_left B
    refine Summable.of_norm_bounded h1 (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, pow_one]
    calc |r| ^ n * |∑ j ∈ Finset.range n, y j| ≤ |r| ^ n * (n * B) :=
          mul_le_mul_of_nonneg_left (hY n) (by positivity)
      _ = B * (n * |r| ^ n) := by ring
  have hgy : Summable (fun j => r ^ j * y j) :=
    Summable.of_norm_bounded ((summable_geometric_of_abs_lt_one hr).abs.mul_right B)
      (fun j => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hy j) (abs_nonneg _))
  refine ⟨hS, ?_⟩
  set T := ∑' n, r ^ n * ∑ j ∈ Finset.range n, y j with hT
  have h1 : T = ∑' n, r ^ (n + 1) * ∑ j ∈ Finset.range (n + 1), y j := by
    rw [hT, hS.tsum_eq_zero_add]; simp
  have h2 : ∀ n, r ^ (n + 1) * ∑ j ∈ Finset.range (n + 1), y j =
      r * (r ^ n * ∑ j ∈ Finset.range n, y j) + r * (r ^ n * y n) := by
    intro n; rw [Finset.sum_range_succ, pow_succ]; ring
  rw [tsum_congr h2, (hS.mul_left r).tsum_add (hgy.mul_left r), tsum_mul_left,
    tsum_mul_left, ← hT] at h1
  field_simp
  linear_combination h1

/-- Woodford (2003), App. D.2, p. 690 (L7, used when `αβμ₂ = 1`): for `|r| < 1` and bounded
`y`, `∑ₙ n rⁿ ∑_{j<n} y_j = r²/(1 − r)² ∑ rʲ y_j + r/(1 − r) ∑ (j + 1) rʲ y_j`. -/
theorem tsum_natgeom_partialSum {r B : ℝ} (hr : |r| < 1) {y : ℕ → ℝ}
    (hy : ∀ n, |y n| ≤ B) :
    Summable (fun n : ℕ => n * r ^ n * ∑ j ∈ Finset.range n, y j) ∧
      ∑' n : ℕ, n * r ^ n * ∑ j ∈ Finset.range n, y j =
        r ^ 2 / (1 - r) ^ 2 * ∑' j, r ^ j * y j +
          r / (1 - r) * ∑' j : ℕ, (j + 1) * r ^ j * y j := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hy 0)
  have hne : 1 - r ≠ 0 := by
    intro h; have : r = 1 := by linarith
    rw [this, abs_one] at hr; exact lt_irrefl _ hr
  have hr' : ‖|r|‖ < 1 := by simpa using hr
  have hY : ∀ n, |∑ j ∈ Finset.range n, y j| ≤ n * B := by
    intro n
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun j _ => hy j).trans ?_
    simp
  obtain ⟨hS, hT⟩ := tsum_geom_partialSum hr hy
  have hU : Summable (fun n : ℕ => n * r ^ n * ∑ j ∈ Finset.range n, y j) := by
    have h1 : Summable (fun n : ℕ => B * ((n : ℝ) ^ 2 * |r| ^ n)) :=
      (summable_pow_mul_geometric_of_norm_lt_one 2 hr').mul_left B
    refine Summable.of_norm_bounded h1 (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
    calc (n : ℝ) * |r| ^ n * |∑ j ∈ Finset.range n, y j| ≤ n * |r| ^ n * (n * B) :=
          mul_le_mul_of_nonneg_left (hY n) (by positivity)
      _ = B * ((n : ℝ) ^ 2 * |r| ^ n) := by ring
  have hV : Summable (fun j : ℕ => (j + 1) * r ^ j * y j) := by
    have h1 : Summable (fun n : ℕ => B * ((n : ℝ) ^ 1 * |r| ^ n) + B * |r| ^ n) :=
      ((summable_pow_mul_geometric_of_norm_lt_one 1 hr').mul_left B).add
        ((summable_geometric_of_lt_one (abs_nonneg r) hr).mul_left B)
    refine Summable.of_norm_bounded h1 (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, pow_one,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)]
    calc ((n : ℝ) + 1) * |r| ^ n * |y n| ≤ (n + 1) * |r| ^ n * B :=
          mul_le_mul_of_nonneg_left (hy n) (by positivity)
      _ = B * (n * |r| ^ n) + B * |r| ^ n := by ring
  refine ⟨hU, ?_⟩
  set U := ∑' n : ℕ, n * r ^ n * ∑ j ∈ Finset.range n, y j with hUdef
  set T := ∑' n, r ^ n * ∑ j ∈ Finset.range n, y j with hTdef
  have h1 : U = ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * r ^ (n + 1) * ∑ j ∈ Finset.range (n + 1), y j := by
    rw [hUdef, hU.tsum_eq_zero_add]; simp
  have h2 : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * r ^ (n + 1) * ∑ j ∈ Finset.range (n + 1), y j =
      (r * (n * r ^ n * ∑ j ∈ Finset.range n, y j) +
        r * (r ^ n * ∑ j ∈ Finset.range n, y j)) + r * ((n + 1) * r ^ n * y n) := by
    intro n; rw [Finset.sum_range_succ, pow_succ]; push_cast; ring
  rw [tsum_congr h2, ((hU.mul_left r).add (hS.mul_left r)).tsum_add (hV.mul_left r),
    (hU.mul_left r).tsum_add (hS.mul_left r), tsum_mul_left, tsum_mul_left, tsum_mul_left,
    ← hUdef, ← hTdef, hT] at h1
  have hU' : U = (r * (r / (1 - r) * ∑' j, r ^ j * y j) +
      r * ∑' j : ℕ, (j + 1) * r ^ j * y j) / (1 - r) := by
    rw [eq_div_iff hne]; linear_combination h1
  rw [hU']
  field_simp

/-- Woodford (2003), App. D.2, p. 690 (L7): with `P̄_n = p − ∑_{j<n} y_j`,
`∑ rⁿ P̄_n = p/(1 − r) − r/(1 − r) ∑ rʲ y_j`. -/
theorem tsum_geom_pbar {r B : ℝ} (hr : |r| < 1) {y : ℕ → ℝ} (hy : ∀ n, |y n| ≤ B) (p : ℝ) :
    Summable (fun n => r ^ n * (p - ∑ j ∈ Finset.range n, y j)) ∧
      ∑' n, r ^ n * (p - ∑ j ∈ Finset.range n, y j) =
        p / (1 - r) - r / (1 - r) * ∑' j, r ^ j * y j := by
  obtain ⟨hS, hT⟩ := tsum_geom_partialSum hr hy
  have hg : Summable (fun n => r ^ n * p) := (summable_geometric_of_abs_lt_one hr).mul_right p
  have e : ∀ n, r ^ n * (p - ∑ j ∈ Finset.range n, y j) =
      r ^ n * p - r ^ n * ∑ j ∈ Finset.range n, y j := fun n => by ring
  refine ⟨(hg.sub hS).congr fun n => (e n).symm, ?_⟩
  rw [tsum_congr e, hg.tsum_sub hS, hT, tsum_mul_right, tsum_geometric_of_abs_lt_one hr]
  ring

/-- Woodford (2003), App. D.2, p. 690 (L7, used when `αβμ₂ = 1`): with `P̄_n = p − ∑_{j<n} y_j`,
`∑ n rⁿ P̄_n = p r/(1 − r)² − r²/(1 − r)² ∑ rʲ y_j − r/(1 − r) ∑ (j+1) rʲ y_j`. -/
theorem tsum_natgeom_pbar {r B : ℝ} (hr : |r| < 1) {y : ℕ → ℝ} (hy : ∀ n, |y n| ≤ B)
    (p : ℝ) :
    Summable (fun n : ℕ => n * r ^ n * (p - ∑ j ∈ Finset.range n, y j)) ∧
      ∑' n : ℕ, n * r ^ n * (p - ∑ j ∈ Finset.range n, y j) =
        p * r / (1 - r) ^ 2 - (r ^ 2 / (1 - r) ^ 2 * ∑' j, r ^ j * y j +
          r / (1 - r) * ∑' j : ℕ, (j + 1) * r ^ j * y j) := by
  obtain ⟨hU, hUv⟩ := tsum_natgeom_partialSum hr hy
  have hr' : ‖r‖ < 1 := by simpa using hr
  have hg : Summable (fun n : ℕ => n * r ^ n * p) := by
    have := (summable_pow_mul_geometric_of_norm_lt_one 1 hr').mul_right p
    simpa using this
  have e : ∀ n : ℕ, n * r ^ n * (p - ∑ j ∈ Finset.range n, y j) =
      n * r ^ n * p - n * r ^ n * ∑ j ∈ Finset.range n, y j := fun n => by ring
  refine ⟨(hg.sub hU).congr fun n => (e n).symm, ?_⟩
  rw [tsum_congr e, hg.tsum_sub hU, hUv, tsum_mul_right, tsum_coe_mul_geometric_of_norm_lt_one hr']
  ring

/-! ### L1: (D.3) from the firm-level capital Euler equation -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

variable (P) in
/-- Woodford (2003), (3.7) p. 356, at the level of a firm (or, with aggregate variables, of the
economy): `λ_t + ε_ψ(k_{t+1} − k_t) = β(1−δ)E_tλ_{t+1}
+ [1−β(1−δ)][ρ_y E_t y_{t+1} − ρ_k k_{t+1} − ω E_t q_{t+1}] + βε_ψ(E_t k_{t+2} − k_{t+1})`.
(The book prints `ω q_t`; the derivation gives `ω E_t q_{t+1}` (survey error 5). The common
disturbance cancels from (D.3), so nothing below depends on this.) -/
def CapitalEuler (ε : ℝ) (lam y k q : ℕ → Ω → ℝ) : Prop :=
  ∀ t, lam t + ε • (k (t + 1) - k t) =
    (P.β * (1 - P.δ)) • 𝔼.E t (lam (t + 1)) +
      cprime P • (P.ρy • 𝔼.E t (y (t + 1)) - P.ρk • k (t + 1) - P.ω • 𝔼.E t (q (t + 1))) +
      (P.β * ε) • (𝔼.E t (k (t + 2)) - k (t + 1))

/-- Woodford (2003), (D.3) p. 689: `β E_t k̃_{t+2} − (1 + β + c) k̃_{t+1} + k̃_t = M E_t p̂_{t+1}`,
i.e. `E_t Q(L) k̃_{t+2} = M E_t p̂_{t+1}`. -/
def D3 (β c M : ℝ) (k p : ℕ → Ω → ℝ) : Prop :=
  ∀ t, β • 𝔼.E t (k (t + 2)) - (1 + β + c) • k (t + 1) + k t = M • 𝔼.E t (p (t + 1))

variable (P) in
/-- Woodford (2003), App. D.2, first display of p. 689, as derived: subtracting the aggregate
(3.7) from the firm's, `ε_ψ(k̃_{t+1} − k̃_t) = [1−β(1−δ)][ρ_y E_t(y_{t+1}(i) − Y_{t+1})
− ρ_k k̃_{t+1}] + βε_ψ(E_t k̃_{t+2} − k̃_{t+1})`. -/
def RelativeEuler (ε : ℝ) (y Y kt : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ε • (kt (t + 1) - kt t) =
    cprime P • (P.ρy • 𝔼.E t (y (t + 1) - Y (t + 1)) - P.ρk • kt (t + 1)) +
      (P.β * ε) • (𝔼.E t (kt (t + 2)) - kt (t + 1))

variable (P) in
/-- Woodford (2003), App. D.2, first display of p. 689, AS PRINTED: with `Y_t` in place of
`Y_{t+1}` (survey error 6). -/
def PrintedRelativeEuler (ε : ℝ) (y Y kt : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ε • (kt (t + 1) - kt t) =
    cprime P • (P.ρy • 𝔼.E t (y (t + 1) - Y t) - P.ρk • kt (t + 1)) +
      (P.β * ε) • (𝔼.E t (kt (t + 2)) - kt (t + 1))

/-- Woodford (2003), App. D.2, p. 689: the firm-level and aggregate (3.7) imply the relative
Euler equation (the first display of p. 689, with the correct date `Y_{t+1}`). -/
theorem relativeEuler_of_capitalEuler {ε : ℝ} {lam y k Y K q : ℕ → Ω → ℝ}
    (hfirm : CapitalEuler P 𝔼 ε lam y k q) (hagg : CapitalEuler P 𝔼 ε lam Y K q) (t : ℕ) :
    RelativeEuler P 𝔼 ε y Y (k - K) t := by
  have h1 := hfirm t
  have h2 := hagg t
  unfold RelativeEuler
  funext ω
  have e1 := congrFun h1 ω
  have e2 := congrFun h2 ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub] at e1 e2 ⊢
  linear_combination e1 - e2

/-- Woodford (2003), (D.3) p. 689 (survey L1): the firm-level and aggregate capital Euler
equations (3.7) and the demand curve `y_t(i) − Y_t = −θ p̂_t(i)` imply (D.3) for the relative
capital stock `k̃ = k(i) − K`, with `c = [1−β(1−δ)]ρ_k/ε_ψ` and `M = [1−β(1−δ)]ρ_y θ/ε_ψ`. -/
theorem D3_of_firm_capital_euler {ε : ℝ} (hε : ε ≠ 0) {lam y k Y K q p : ℕ → Ω → ℝ}
    (hfirm : CapitalEuler P 𝔼 ε lam y k q) (hagg : CapitalEuler P 𝔼 ε lam Y K q)
    (hdem : ∀ t, y t - Y t = (-P.θ) • p t) : D3 𝔼 P.β (cD P ε) (MD P ε) (k - K) p := by
  intro t
  have h := relativeEuler_of_capitalEuler 𝔼 hfirm hagg t
  unfold RelativeEuler at h
  rw [hdem (t + 1)] at h
  funext ω
  have e := congrFun h ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_smul]
    at e ⊢
  unfold cD MD
  field_simp
  linear_combination -e

/-- Woodford (2003), App. D.2, p. 689 (survey error 6): given (3.7) for the firm and the
aggregate, the PRINTED first display (with `Y_t`) holds at `t` iff
`[1−β(1−δ)]ρ_y (E_t Y_{t+1} − E_t Y_t) = 0`, i.e. (for the book's parameters) iff
`E_t Y_{t+1} = E_t Y_t`; so it is not implied by the model. -/
theorem printed_display_iff {ε : ℝ} {lam y k Y K q : ℕ → Ω → ℝ}
    (hfirm : CapitalEuler P 𝔼 ε lam y k q) (hagg : CapitalEuler P 𝔼 ε lam Y K q) (t : ℕ) :
    PrintedRelativeEuler P 𝔼 ε y Y (k - K) t ↔
      (cprime P * P.ρy) • (𝔼.E t (Y (t + 1)) - 𝔼.E t (Y t)) = 0 := by
  have h := relativeEuler_of_capitalEuler 𝔼 hfirm hagg t
  unfold RelativeEuler at h
  unfold PrintedRelativeEuler
  rw [h]
  constructor
  · intro h'
    funext ω
    have e := congrFun h' ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub,
      Pi.zero_apply] at e ⊢
    linear_combination -e
  · intro h'
    funext ω
    have e := congrFun h' ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub,
      Pi.zero_apply] at e ⊢
    linear_combination -e

/-- Woodford (2003), App. D.2, p. 689 (survey error 6, CONFIRMED): an explicit perfect-foresight
economy satisfying the firm-level and aggregate (3.7) and the demand curve in which the PRINTED
first display of p. 689 fails at `t = 0` (output grows, `Y_t = t`; all firms identical). -/
theorem printed_display_fails (hP : Admissible P) {ε : ℝ} :
    ∃ lam y k Y K q p : ℕ → Unit → ℝ,
      CapitalEuler P perfectForesight ε lam y k q ∧ CapitalEuler P perfectForesight ε lam Y K q ∧
      (∀ t, y t - Y t = (-P.θ) • p t) ∧
      ¬ PrintedRelativeEuler P perfectForesight ε y Y (k - K) 0 := by
  have hω : P.ω ≠ 0 := (lt_trans hP.hν hP.hων).ne'
  have hc := cprime_pos hP
  have hρy : 0 < P.ρy := by rw [hP.hρy]; linarith [hP.hρk, hP.hν]
  have hcy : (cprime P * P.ρy : ℝ) ≠ 0 := (mul_pos hc hρy).ne'
  refine ⟨fun _ _ => 0, fun t _ => t, fun _ _ => 0, fun t _ => t, fun _ _ => 0,
    fun t _ => P.ρy * t / P.ω, fun _ _ => 0, ?_, ?_, ?_, ?_⟩
  · intro t; funext u
    simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    field_simp; ring
  · intro t; funext u
    simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    field_simp; ring
  · intro t; funext u; simp
  · rw [printed_display_iff perfectForesight (lam := fun _ _ => 0) (q := fun t _ => P.ρy * t / P.ω)]
    · intro h
      have e := congrFun h ()
      simp only [perfectForesight, LinearMap.id_apply, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul, Pi.zero_apply] at e
      push_cast at e
      apply hcy; linarith
    · intro t; funext u
      simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
      field_simp; ring
    · intro t; funext u
      simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
      field_simp; ring

/-! ### L4: the unique bounded solution (D.4) -/

/-- Woodford (2003), App. D.2, p. 689: `z_t = β⁻¹ M ∑_{j ≥ 1} μ₂^{-j} E_t p̂_{t+j}`. -/
noncomputable def zD4 (β M μ₂ : ℝ) (p : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => β⁻¹ * M * ∑' j, μ₂⁻¹ ^ (j + 1) * 𝔼.E t (p (t + j + 1)) ω

/-- Woodford (2003), App. D.2, p. 689: the forcing term `u_t = (M/(βμ₂)) E_t p̂_{t+1}` of the
unstable-root equation. -/
noncomputable def uD4 (β M μ₂ : ℝ) (p : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (M / (β * μ₂)) • 𝔼.E t (p (t + 1))

/-- Woodford (2003), App. D.2, p. 689: `u` is adapted and bounded. -/
theorem uD4_adapted_bounded {β M μ₂ B : ℝ} {p : ℕ → Ω → ℝ} (hp : ∀ t ω, |p t ω| ≤ B) :
    𝔼.Adapted (uD4 𝔼 β M μ₂ p) ∧ ∀ t ω, |uD4 𝔼 β M μ₂ p t ω| ≤ |M / (β * μ₂)| * B := by
  refine ⟨fun t => ?_, fun t ω => ?_⟩
  · unfold uD4; rw [map_smul, 𝔼.E_E_self]
  · unfold uD4
    rw [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hp (t + 1)) t ω) (abs_nonneg _)

/-- Woodford (2003), App. D.2, p. 689: `z` is the forward series of `u` with ratio `μ₂⁻¹`. -/
theorem zD4_eq_forwardSeries {β M μ₂ : ℝ} (hβ : β ≠ 0) (hμ : μ₂ ≠ 0) (p : ℕ → Ω → ℝ) :
    zD4 𝔼 β M μ₂ p = 𝔼.forwardSeries μ₂⁻¹ (uD4 𝔼 β M μ₂ p) := by
  funext t ω
  unfold zD4 ExpectationSystem.forwardSeries uD4
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [map_smul, 𝔼.tower (Nat.le_add_right t j), Pi.smul_apply, smul_eq_mul, pow_succ]
  field_simp

/-- Woodford (2003), App. D.2, p. 689: `|z_t| ≤ |M/(βμ₂)| B/(1 − μ₂⁻¹)` and `z` is adapted. -/
theorem zD4_bounded_adapted {β M μ₂ B : ℝ} (hβ : β ≠ 0) (hμ : 1 < μ₂) {p : ℕ → Ω → ℝ}
    (hp : ∀ t ω, |p t ω| ≤ B) :
    (∀ t ω, |zD4 𝔼 β M μ₂ p t ω| ≤ |M / (β * μ₂)| * B / (1 - |μ₂⁻¹|)) ∧
      𝔼.Adapted (zD4 𝔼 β M μ₂ p) := by
  have hm : |μ₂⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith)]; exact inv_lt_one_of_one_lt₀ hμ
  obtain ⟨_, hub⟩ := uD4_adapted_bounded 𝔼 (β := β) (M := M) (μ₂ := μ₂) hp
  rw [zD4_eq_forwardSeries 𝔼 hβ (by linarith) p]
  refine ⟨fun t ω => ?_, ForwardSolution.forwardSeries_adapted_abs 𝔼 hm hub⟩
  -- the bound of `forwardSeries_bounded_abs`
  have hg : HasSum (fun k : ℕ => |M / (β * μ₂)| * B * |μ₂⁻¹| ^ k)
      (|M / (β * μ₂)| * B / (1 - |μ₂⁻¹|)) := by
    have := (hasSum_geometric_of_lt_one (abs_nonneg _) hm).mul_left (|M / (β * μ₂)| * B)
    simpa [div_eq_mul_inv] using this
  have := tsum_of_norm_bounded hg
    (f := fun k => μ₂⁻¹ ^ k * 𝔼.E t (uD4 𝔼 β M μ₂ p (t + k)) ω) fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow, mul_comm]
      exact mul_le_mul_of_nonneg_right (𝔼.abs_E_le (hub (t + k)) t ω)
        (pow_nonneg (abs_nonneg _) k)
  simpa [ExpectationSystem.forwardSeries, Real.norm_eq_abs] using this

/-- Woodford (2003), App. D.2, p. 689: (D.3) is the second-order equation
`a₀ E_t k̃_{t+2} − a₁ k̃_{t+1} + a₂ k̃_t = f_t` of `ForwardSystems` with `a₀ = β`,
`a₁ = 1 + β + c`, `a₂ = 1` and `f_t = M E_t p̂_{t+1}`. -/
theorem D3_iff_secondOrder (β c M : ℝ) (k p : ℕ → Ω → ℝ) :
    D3 𝔼 β c M k p ↔ ∀ t, β • 𝔼.E t (k (t + 2)) - (1 + β + c) • k (t + 1) + (1 : ℝ) • k t =
      (fun τ => M • 𝔼.E τ (p (τ + 1))) t := by
  simp only [one_smul]
  rfl

/-- Woodford (2003), App. D.2, p. 689: the forward part of the stable-root solution of (D.3)
(`ForwardSystems.wSol`) is `−z_t`. -/
theorem wSol_eq_neg_zD4 {β M μ₂ : ℝ} (hβ : β ≠ 0) (hμ : μ₂ ≠ 0) (p : ℕ → Ω → ℝ) :
    ForwardSystems.wSol 𝔼 β μ₂ (fun τ => M • 𝔼.E τ (p (τ + 1))) = -zD4 𝔼 β M μ₂ p := by
  rw [zD4_eq_forwardSeries 𝔼 hβ hμ]
  funext t ω
  simp only [ForwardSystems.wSol, ExpectationSystem.forwardSeries, uD4, Pi.neg_apply,
    ← tsum_neg]
  refine tsum_congr fun j => ?_
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- Woodford (2003), (D.4) p. 689 (survey L4, uniqueness): if `β(μ₁ + μ₂) = 1 + β + c`,
`βμ₁μ₂ = 1` and `μ₂ > 1`, every bounded solution `k̃` of (D.3) that is predetermined
(`k̃_{t+1}` known at `t`) satisfies `k̃_{t+1} = μ₁ k̃_t − z_t` for bounded `p̂`
(`ForwardSystems.secondOrder_forward_iff`). -/
theorem D4_of_D3 {β c M μ₁ μ₂ B : ℝ} (hβ : 0 < β) (hsum : β * (μ₁ + μ₂) = 1 + β + c)
    (hprod : β * (μ₁ * μ₂) = 1) (hμ : 1 < μ₂) {k p : ℕ → Ω → ℝ}
    (hp : ∀ t ω, |p t ω| ≤ B) (hk : BoundedProc k)
    (hpre : ∀ t, 𝔼.E t (k (t + 1)) = k (t + 1)) (hD3 : D3 𝔼 β c M k p) (t : ℕ) :
    k (t + 1) = μ₁ • k t - zD4 𝔼 β M μ₂ p t := by
  have hf : ∀ τ ω, |(fun τ => M • 𝔼.E τ (p (τ + 1))) τ ω| ≤ |M| * B := fun τ ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hp (τ + 1)) τ ω) (abs_nonneg _)
  have hfa : 𝔼.Adapted (fun τ => M • 𝔼.E τ (p (τ + 1))) := fun τ => by
    simp only [map_smul, 𝔼.E_E_self]
  have h := (ForwardSystems.secondOrder_forward_iff 𝔼 hβ.ne' hsum.symm
    (by linarith : (1 : ℝ) = β * μ₁ * μ₂) (by rw [abs_of_pos (by linarith)]; exact hμ) hf hfa
    hpre hk).mp ((D3_iff_secondOrder 𝔼 β c M k p).mp hD3) t
  rw [h, wSol_eq_neg_zD4 𝔼 hβ.ne' (by linarith), Pi.neg_apply, sub_eq_add_neg]

/-- Woodford (2003), (D.4) p. 689: the capital path generated by (D.4) from an initial
condition `k̃_0`. -/
noncomputable def kD4 (β M μ₁ μ₂ : ℝ) (p : ℕ → Ω → ℝ) (k0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => k0
  | t + 1 => μ₁ • kD4 β M μ₁ μ₂ p k0 t - zD4 𝔼 β M μ₂ p t

/-- Woodford (2003), (D.4) p. 689 (survey L4, existence): for `0 < μ₁ < 1 < μ₂` with
`β(μ₁ + μ₂) = 1 + β + c`, `βμ₁μ₂ = 1`, any bounded `p̂` and any bounded initial capital `k̃_0`
known at date 0, the path (D.4) is bounded, adapted, predetermined and solves (D.3). With
`D4_of_D3` it is the unique such solution: "(D.3) has a unique bounded solution … given an
initial capital stock" (`ForwardSystems.secondOrder_forward_existsUnique`). -/
theorem D4_solution {β c M μ₁ μ₂ B B0 : ℝ} (hβ : 0 < β) (hsum : β * (μ₁ + μ₂) = 1 + β + c)
    (hprod : β * (μ₁ * μ₂) = 1) (hμ₁ : |μ₁| < 1) (hμ : 1 < μ₂) {p : ℕ → Ω → ℝ}
    (hp : ∀ t ω, |p t ω| ≤ B) {k0 : Ω → ℝ} (hk0 : ∀ ω, |k0 ω| ≤ B0)
    (hk0a : 𝔼.E 0 k0 = k0) :
    BoundedProc (kD4 𝔼 β M μ₁ μ₂ p k0) ∧ 𝔼.Adapted (kD4 𝔼 β M μ₁ μ₂ p k0) ∧
      (∀ t, 𝔼.E t (kD4 𝔼 β M μ₁ μ₂ p k0 (t + 1)) = kD4 𝔼 β M μ₁ μ₂ p k0 (t + 1)) ∧
      D3 𝔼 β c M (kD4 𝔼 β M μ₁ μ₂ p k0) p ∧ kD4 𝔼 β M μ₁ μ₂ p k0 0 = k0 := by
  have hf : ∀ τ ω, |(fun τ => M • 𝔼.E τ (p (τ + 1))) τ ω| ≤ |M| * B := fun τ ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hp (τ + 1)) τ ω) (abs_nonneg _)
  have hfa : 𝔼.Adapted (fun τ => M • 𝔼.E τ (p (τ + 1))) := fun τ => by
    simp only [map_smul, 𝔼.E_E_self]
  have h2 : (1 : ℝ) = β * μ₁ * μ₂ := by linarith
  have hμ2 : 1 < |μ₂| := by rw [abs_of_pos (by linarith)]; exact hμ
  obtain ⟨x, ⟨hx0, hxp, hxb, hx⟩, -⟩ := ForwardSystems.secondOrder_forward_existsUnique 𝔼
    hβ.ne' hsum.symm h2 hμ₁ hμ2 hf hfa hk0a hk0
  have hrec := (ForwardSystems.secondOrder_forward_iff 𝔼 hβ.ne' hsum.symm h2 hμ2 hf hfa hxp
    hxb).mp hx
  have hxk : x = kD4 𝔼 β M μ₁ μ₂ p k0 := by
    funext t
    induction t with
    | zero => exact hx0
    | succ t ih =>
      rw [hrec t, ih, wSol_eq_neg_zD4 𝔼 hβ.ne' (by linarith), Pi.neg_apply, ← sub_eq_add_neg]
      rfl
  subst hxk
  refine ⟨hxb, fun t => ?_, hxp, (D3_iff_secondOrder 𝔼 β c M _ p).mpr hx, rfl⟩
  cases t with
  | zero => exact hk0a
  | succ t => exact ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hxp t)

/-! ### L5, L6: the sums (D.5) and (D.6) under an arbitrary expectation system -/

/-- Woodford (2003), App. D.2, p. 690 (L5, the integrated law of motion): from (D.4),
`E_t k̃_{t+n} = μ₁ⁿ k̃_t − ∑_{j<n} μ₁^{n−1−j} E_t z_{t+j}`. -/
theorem D5_iterate_E {μ₁ : ℝ} {k z : ℕ → Ω → ℝ} (hD4 : ∀ τ, k (τ + 1) = μ₁ • k τ - z τ)
    (t : ℕ) (hkt : 𝔼.E t (k t) = k t) (n : ℕ) (ω : Ω) :
    𝔼.E t (k (t + n)) ω =
      μ₁ ^ n * k t ω - ∑ j ∈ Finset.range n, μ₁ ^ (n - 1 - j) * 𝔼.E t (z (t + j)) ω := by
  have h := D5_iterate (K := fun n => 𝔼.E t (k (t + n)) ω) (Z := fun n => 𝔼.E t (z (t + n)) ω)
    (μ₁ := μ₁) (fun n => by
      simp only [← add_assoc, hD4 (t + n), map_sub, map_smul, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul]) n
  simpa [hkt] using h

/-- Woodford (2003), (D.5) p. 690 (survey L5, in full): from (D.4) with bounded `z`,
`∑_k (αβ)ᵏ E_t k̃_{t+k} = k̃_t/(1 − αβμ₁) − αβ/(1 − αβμ₁) ∑_j (αβ)ʲ E_t z_{t+j}`
(here `x = αβ`; a genuine Cauchy-product interchange, `D5_real`). -/
theorem D5 {x μ₁ Bz : ℝ} (hx : |x| < 1) (hxμ : |x * μ₁| < 1) {k z : ℕ → Ω → ℝ}
    (hD4 : ∀ τ, k (τ + 1) = μ₁ • k τ - z τ) (hz : ∀ τ ω, |z τ ω| ≤ Bz) (t : ℕ)
    (hkt : 𝔼.E t (k t) = k t) (ω : Ω) :
    ∑' n, x ^ n * 𝔼.E t (k (t + n)) ω =
      k t ω / (1 - x * μ₁) - x / (1 - x * μ₁) * ∑' n, x ^ n * 𝔼.E t (z (t + n)) ω := by
  have h := D5_real (K := fun n => 𝔼.E t (k (t + n)) ω) (Z := fun n => 𝔼.E t (z (t + n)) ω)
    hx hxμ (fun n => by
      simp only [← add_assoc, hD4 (t + n), map_sub, map_smul, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul]) (fun n => 𝔼.abs_E_le (hz (t + n)) t ω)
  simpa [hkt] using h

/-- Woodford (2003), App. D.2, p. 690: `E_t z_{t+j} = β⁻¹ M ∑_{i ≥ 0} μ₂^{-(i+1)} E_t p̂_{t+j+i+1}`
(`E_t` passes through the forward sum by the law of iterated expectations). -/
theorem E_zD4 {β M μ₂ B : ℝ} (hμ : 1 < μ₂) {p : ℕ → Ω → ℝ} (hp : ∀ τ ω, |p τ ω| ≤ B)
    (t j : ℕ) (ω : Ω) :
    𝔼.E t (zD4 𝔼 β M μ₂ p (t + j)) ω =
      β⁻¹ * M * ∑' i, μ₂⁻¹ ^ (i + 1) * 𝔼.E t (p (t + j + i + 1)) ω := by
  have hm0 : 0 ≤ μ₂⁻¹ := inv_nonneg.mpr (by linarith)
  have hm1 : μ₂⁻¹ < 1 := inv_lt_one_of_one_lt₀ hμ
  set f : ℕ → Ω → ℝ := fun i => (β⁻¹ * M * μ₂⁻¹ ^ (i + 1)) • 𝔼.E (t + j) (p (t + j + i + 1))
    with hf
  have hz : zD4 𝔼 β M μ₂ p (t + j) = fun ω' => ∑' i, f i ω' := by
    funext ω'
    simp only [zD4, hf, Pi.smul_apply, smul_eq_mul, ← tsum_mul_left]
    exact tsum_congr fun i => by ring
  have hb : ∀ i ω', |f i ω'| ≤ μ₂⁻¹ ^ i * (|β⁻¹ * M| * μ₂⁻¹ * B) := by
    intro i ω'
    simp only [hf, Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow, abs_of_nonneg hm0]
    have := 𝔼.abs_E_le (hp (t + j + i + 1)) (t + j) ω'
    calc |β⁻¹| * |M| * (μ₂⁻¹ ^ (i + 1)) * |𝔼.E (t + j) (p (t + j + i + 1)) ω'|
        ≤ |β⁻¹| * |M| * (μ₂⁻¹ ^ (i + 1)) * B := by gcongr
      _ = _ := by ring
  rw [hz, 𝔼.E_tsum hm0 hm1 hb t ω, ← tsum_mul_left]
  refine tsum_congr fun i => ?_
  simp only [hf, map_smul, 𝔼.tower (Nat.le_add_right t j), Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), (D.6) p. 690 (survey L6, in full): with `x = αβ`,
`∑_j xʲ E_t z_{t+j} = β⁻¹ M ∑_{n ≥ 1} C_n E_t p̂_{t+n}`, `C_n = ∑_{j<n} xʲ μ₂^{j−n}`
(a genuine interchange of a double series, `D6_real`). -/
theorem D6_coeff {x β M μ₂ B : ℝ} (hx : |x| < 1) (hμ : 1 < μ₂) {p : ℕ → Ω → ℝ}
    (hp : ∀ τ ω, |p τ ω| ≤ B) (t : ℕ) (ω : Ω) :
    ∑' j, x ^ j * 𝔼.E t (zD4 𝔼 β M μ₂ p (t + j)) ω =
      β⁻¹ * M * ∑' n, cD6 x μ₂⁻¹ (n + 1) * 𝔼.E t (p (t + (n + 1))) ω := by
  have hm : |μ₂⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith)]; exact inv_lt_one_of_one_lt₀ hμ
  have h := D6_real hx hm (P := fun n => 𝔼.E t (p (t + n)) ω)
    (fun n => 𝔼.abs_E_le (hp (t + n)) t ω)
  simp only [E_zD4 𝔼 hμ hp]
  rw [← h, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  have : ∀ i, t + j + i + 1 = t + (j + i + 1) := fun i => by ring
  simp only [this]
  ring

/-- Woodford (2003), (D.6) p. 690, as printed (case `αβμ₂ ≠ 1`):
`∑_j (αβ)ʲ E_t z_{t+j}
= M/(β(1 − αβμ₂)) [∑_{j≥1} μ₂^{-j} E_t p̂_{t+j} − ∑_{j≥1} (αβ)ʲ E_t p̂_{t+j}]`. -/
theorem D6 {x β M μ₂ B : ℝ} (hx : |x| < 1) (hμ : 1 < μ₂) (hD : x * μ₂ ≠ 1)
    {p : ℕ → Ω → ℝ} (hp : ∀ τ ω, |p τ ω| ≤ B) (t : ℕ) (ω : Ω) :
    ∑' j, x ^ j * 𝔼.E t (zD4 𝔼 β M μ₂ p (t + j)) ω =
      M / (β * (1 - x * μ₂)) * (∑' n, μ₂⁻¹ ^ (n + 1) * 𝔼.E t (p (t + (n + 1))) ω -
        ∑' n, x ^ (n + 1) * 𝔼.E t (p (t + (n + 1))) ω) := by
  have hμ0 : μ₂ ≠ 0 := by linarith
  have hD' : 1 - x * μ₂ ≠ 0 := fun h => hD (by linarith)
  have hm : |μ₂⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith)]; exact inv_lt_one_of_one_lt₀ hμ
  have hS1 : Summable fun n => μ₂⁻¹ ^ (n + 1) * 𝔼.E t (p (t + (n + 1))) ω :=
    Summable.of_norm_bounded ((summable_geometric_of_abs_lt_one hm).abs.mul_right B) fun n => by
      rw [Real.norm_eq_abs, abs_mul, pow_succ, abs_mul]
      have h1 := 𝔼.abs_E_le (hp (t + (n + 1))) t ω
      have h2 : |μ₂⁻¹| ≤ 1 := hm.le
      calc |μ₂⁻¹ ^ n| * |μ₂⁻¹| * |𝔼.E t (p (t + (n + 1))) ω| ≤ |μ₂⁻¹ ^ n| * 1 * B := by
            gcongr
        _ = |μ₂⁻¹ ^ n| * B := by ring
  have hS2 : Summable fun n => x ^ (n + 1) * 𝔼.E t (p (t + (n + 1))) ω :=
    Summable.of_norm_bounded ((summable_geometric_of_abs_lt_one hx).abs.mul_right B) fun n => by
      rw [Real.norm_eq_abs, abs_mul, pow_succ, abs_mul]
      have h1 := 𝔼.abs_E_le (hp (t + (n + 1))) t ω
      have h2 : |x| ≤ 1 := hx.le
      calc |x ^ n| * |x| * |𝔼.E t (p (t + (n + 1))) ω| ≤ |x ^ n| * 1 * B := by gcongr
        _ = |x ^ n| * B := by ring
  rw [D6_coeff 𝔼 hx hμ hp, ← hS1.tsum_sub hS2, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hc := cD6_closed (x := x) hμ0 (n + 1)
  have : cD6 x μ₂⁻¹ (n + 1) = (μ₂⁻¹ ^ (n + 1) - x ^ (n + 1)) / (1 - x * μ₂) := by
    rw [eq_div_iff hD', mul_comm]; exact hc
  rw [this]
  field_simp

/-- Woodford (2003), (D.6) p. 690, case `αβμ₂ = 1` (where the printed formula is `0/0`): the
coefficient of `E_t p̂_{t+n}` is `β⁻¹ M n μ₂^{-n}`. -/
theorem D6_eq_case {x β M μ₂ B : ℝ} (hx : |x| < 1) (hμ : 1 < μ₂) (hD : x * μ₂ = 1)
    {p : ℕ → Ω → ℝ} (hp : ∀ τ ω, |p τ ω| ≤ B) (t : ℕ) (ω : Ω) :
    ∑' j, x ^ j * 𝔼.E t (zD4 𝔼 β M μ₂ p (t + j)) ω =
      β⁻¹ * M * ∑' n : ℕ, ((n : ℝ) + 1) * μ₂⁻¹ ^ (n + 1) * 𝔼.E t (p (t + (n + 1))) ω := by
  have hμ0 : μ₂ ≠ 0 := by linarith
  have hxm : x = μ₂⁻¹ := by field_simp; linarith
  rw [D6_coeff 𝔼 hx hμ hp]
  congr 1
  refine tsum_congr fun n => ?_
  rw [← hxm, cD6_eq_case]
  push_cast; ring

/-! ### The coefficients `a`, `b` of (3.14) and their signs -/

variable (P) in
/-- Woodford (2003), Prop. 5.1 (3.14), p. 359: `a = (1 + ωθ)/(1 − αβ)
+ (ω − ν) α/(1 − αβ) · M/((1 − αβμ₁)(1 − αβμ₂))`, as a function of `M, μ₁, μ₂`. -/
noncomputable def aCoef (M μ₁ μ₂ : ℝ) : ℝ :=
  (1 + P.ω * P.θ) / (1 - P.α * P.β) +
    (P.ω - P.ν) * (P.α / (1 - P.α * P.β)) * (M / ((1 - P.α * P.β * μ₁) * (1 - P.α * P.β * μ₂)))

variable (P) in
/-- Woodford (2003), Prop. 5.1 (3.14), p. 359:
`b = (ω − ν) α/(1 − μ₂⁻¹) · M/((1 − αβμ₁)(1 − αβμ₂))`. -/
noncomputable def bCoef (M μ₁ μ₂ : ℝ) : ℝ :=
  (P.ω - P.ν) * (P.α / (1 - μ₂⁻¹)) * (M / ((1 - P.α * P.β * μ₁) * (1 - P.α * P.β * μ₂)))

variable (P) in
/-- Woodford (2003), Prop. 5.1, p. 359: `a` at adjustment cost `ε_ψ` (with `M`, `μ₁`, `μ₂`
determined by the model). -/
noncomputable def aM (ε : ℝ) : ℝ :=
  aCoef P (MD P ε) (mu1 P.β (cD P ε)) (mu2 P.β (cD P ε))

variable (P) in
/-- Woodford (2003), Prop. 5.1, p. 359: `b` at adjustment cost `ε_ψ`. -/
noncomputable def bM (ε : ℝ) : ℝ :=
  bCoef P (MD P ε) (mu1 P.β (cD P ε)) (mu2 P.β (cD P ε))

/-- Woodford (2003), Prop. 5.1, p. 359: the auxiliary facts `0 < αβ < 1`, `0 < μ₁ < 1`,
`1 < μ₂`, `0 < 1 − αβμ₁`, `0 < 1 − μ₂⁻¹`, `0 < M`. -/
theorem basic_facts (hP : Admissible P) {ε : ℝ} (hε : 0 < ε) :
    0 < P.α * P.β ∧ P.α * P.β < 1 ∧ 0 < mu1 P.β (cD P ε) ∧ mu1 P.β (cD P ε) < 1 ∧
      1 < mu2 P.β (cD P ε) ∧ 0 < 1 - P.α * P.β * mu1 P.β (cD P ε) ∧
      0 < 1 - (mu2 P.β (cD P ε))⁻¹ ∧ 0 < MD P ε := by
  have hα0 := hP.hα0; have hα1 := hP.hα1; have hβ0 := hP.hβ0; have hβ1 := hP.hβ1
  have hc := cD_pos hP hε
  have h1 := mu1_pos hβ0 hc
  have h2 := mu1_lt_one hβ0 hβ1 hc
  have h3 := one_lt_mu2 hβ0 hβ1 hc
  have hx : P.α * P.β < 1 := by nlinarith
  refine ⟨by positivity, hx, h1, h2, h3, ?_, ?_, MD_pos hP hε⟩
  · have : P.α * P.β * mu1 P.β (cD P ε) < 1 := by
      calc P.α * P.β * mu1 P.β (cD P ε) < 1 * 1 := by
            apply mul_lt_mul'' hx h2 (by positivity) h1.le
        _ = 1 := by ring
    linarith
  · have : (mu2 P.β (cD P ε))⁻¹ < 1 := inv_lt_one_of_one_lt₀ h3
    linarith

/-- Woodford (2003), Prop. 5.1, p. 359 (correction, survey error 1): the sign of `b` is the
sign of `1 − αβμ₂`: `b > 0 ↔ αβμ₂ < 1` (for `αβμ₂ ≠ 1`). -/
theorem b_pos_iff (hP : Admissible P) {ε : ℝ} (hε : 0 < ε)
    (hD : P.α * P.β * mu2 P.β (cD P ε) ≠ 1) :
    0 < bM P ε ↔ P.α * P.β * mu2 P.β (cD P ε) < 1 := by
  obtain ⟨-, -, -, -, -, h1, h2, hM⟩ := basic_facts hP hε
  have hων : 0 < P.ω - P.ν := by linarith [hP.hων]
  have hpos : 0 < (P.ω - P.ν) * (P.α / (1 - (mu2 P.β (cD P ε))⁻¹)) * MD P ε /
      (1 - P.α * P.β * mu1 P.β (cD P ε)) := by
    have := hP.hα0; positivity
  have he : bM P ε = (P.ω - P.ν) * (P.α / (1 - (mu2 P.β (cD P ε))⁻¹)) * MD P ε /
      (1 - P.α * P.β * mu1 P.β (cD P ε)) / (1 - P.α * P.β * mu2 P.β (cD P ε)) := by
    unfold bM bCoef; field_simp
  rw [he]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have : 1 - P.α * P.β * mu2 P.β (cD P ε) < 0 := by
      rcases lt_or_eq_of_le hc with h' | h'
      · linarith
      · exact absurd h'.symm hD
    have := div_neg_of_pos_of_neg hpos this
    linarith
  · intro h
    exact div_pos hpos (by linarith)

/-- Woodford (2003), Prop. 5.1, p. 359 (survey error 1): if `αβμ₂ > 1` then `b < 0`, so the
printed "`b > 0`" fails (this happens for small `ε_ψ`, since `μ₂ → ∞` as `ε_ψ → 0`). -/
theorem b_neg_of (hP : Admissible P) {ε : ℝ} (hε : 0 < ε)
    (hD : 1 < P.α * P.β * mu2 P.β (cD P ε)) : bM P ε < 0 := by
  obtain ⟨-, -, -, -, -, h1, h2, hM⟩ := basic_facts hP hε
  have hων : 0 < P.ω - P.ν := by linarith [hP.hων]
  have hpos : 0 < (P.ω - P.ν) * (P.α / (1 - (mu2 P.β (cD P ε))⁻¹)) * MD P ε /
      (1 - P.α * P.β * mu1 P.β (cD P ε)) := by
    have := hP.hα0; positivity
  have he : bM P ε = (P.ω - P.ν) * (P.α / (1 - (mu2 P.β (cD P ε))⁻¹)) * MD P ε /
      (1 - P.α * P.β * mu1 P.β (cD P ε)) / (1 - P.α * P.β * mu2 P.β (cD P ε)) := by
    unfold bM bCoef; field_simp
  rw [he]
  exact div_neg_of_pos_of_neg hpos (by linarith)

/-- Woodford (2003), Prop. 5.1, p. 359, CORRECTED (survey error 1): if `αβμ₂ < 1` then
`a > 0` and `b > 0` (using `ω − ν > 0`). -/
theorem a_pos_b_pos (hP : Admissible P) {ε : ℝ} (hε : 0 < ε)
    (hD : P.α * P.β * mu2 P.β (cD P ε) < 1) : 0 < aM P ε ∧ 0 < bM P ε := by
  obtain ⟨hx0, hx1, -, -, -, h1, h2, hM⟩ := basic_facts hP hε
  have hων : 0 < P.ω - P.ν := by linarith [hP.hων]
  have hD' : 0 < 1 - P.α * P.β * mu2 P.β (cD P ε) := by linarith
  have hωθ : 0 < 1 + P.ω * P.θ := by
    have := hP.hθ; have : 0 < P.ω := by linarith [hP.hν]
    positivity
  have h1x : 0 < 1 - P.α * P.β := by linarith
  have := hP.hα0
  refine ⟨?_, (b_pos_iff hP hε hD.ne).mpr hD⟩
  unfold aM aCoef
  positivity

/-- Woodford (2003), Prop. 5.1, p. 359 (the corrected hypothesis made explicit): `αβμ₂ < 1`
iff `c < (1 − α)(1 − αβ)/α`, where `c = [1 − β(1−δ)]ρ_k/ε_ψ`. -/
theorem alpha_beta_mu2_lt_one_iff (hP : Admissible P) {ε : ℝ} (hε : 0 < ε) :
    P.α * P.β * mu2 P.β (cD P ε) < 1 ↔ cD P ε < (1 - P.α) * (1 - P.α * P.β) / P.α := by
  have hα0 := hP.hα0; have hα1 := hP.hα1; have hβ0 := hP.hβ0; have hβ1 := hP.hβ1
  have hc := cD_pos hP hε
  set c := cD P ε
  have h1 := mu1_lt_one hβ0 hβ1 hc
  have h3 := one_lt_mu2 hβ0 hβ1 hc
  have hx0 : 0 < P.α * P.β := by positivity
  have hfac := Ppoly_factor hβ0 hc (P.α * P.β)⁻¹
  have hinv1 : 1 < (P.α * P.β)⁻¹ := (one_lt_inv₀ hx0).mpr (by nlinarith)
  have hP' : Ppoly P.β c (P.α * P.β)⁻¹ * (P.α * P.β) ^ 2 =
      P.β * (1 - P.α) * (1 - P.α * P.β) - c * (P.α * P.β) := by
    unfold Ppoly; field_simp; ring
  constructor
  · intro h
    have hlt : mu2 P.β c < (P.α * P.β)⁻¹ := by
      rw [lt_inv_comm₀ (by linarith) hx0, inv_eq_one_div, lt_div_iff₀ (by linarith)]
      linarith
    have hpos : 0 < Ppoly P.β c (P.α * P.β)⁻¹ := by
      rw [hfac]
      have := mul_pos (sub_pos.mpr (lt_trans h1 hinv1)) (sub_pos.mpr hlt)
      nlinarith
    have : 0 < P.β * (1 - P.α) * (1 - P.α * P.β) - c * (P.α * P.β) := by
      rw [← hP']; positivity
    rw [lt_div_iff₀ hα0]
    nlinarith
  · intro h
    rw [lt_div_iff₀ hα0] at h
    have hpos : 0 < Ppoly P.β c (P.α * P.β)⁻¹ := by
      have : 0 < Ppoly P.β c (P.α * P.β)⁻¹ * (P.α * P.β) ^ 2 := by rw [hP']; nlinarith
      exact pos_of_mul_pos_left this (by positivity)
    rw [hfac] at hpos
    have ha : 0 < (P.α * P.β)⁻¹ - mu1 P.β c := sub_pos.mpr (lt_trans h1 hinv1)
    have hb : 0 < (P.α * P.β)⁻¹ - mu2 P.β c := by
      by_contra hn; push Not at hn
      have : P.β * ((P.α * P.β)⁻¹ - mu1 P.β c) * ((P.α * P.β)⁻¹ - mu2 P.β c) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hn
      linarith
    have : mu2 P.β c < (P.α * P.β)⁻¹ := by linarith
    calc P.α * P.β * mu2 P.β c < P.α * P.β * (P.α * P.β)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hx0.ne'

/-- Woodford (2003), Prop. 5.1, p. 359 (the corrected hypothesis in terms of the adjustment
cost): `αβμ₂ < 1` iff `ε_ψ > [1 − β(1−δ)]ρ_k α/((1 − α)(1 − αβ))`. -/
theorem alpha_beta_mu2_lt_one_iff_eps (hP : Admissible P) {ε : ℝ} (hε : 0 < ε) :
    P.α * P.β * mu2 P.β (cD P ε) < 1 ↔
      cprime P * P.ρk * P.α / ((1 - P.α) * (1 - P.α * P.β)) < ε := by
  have hα0 := hP.hα0; have hα1 := hP.hα1; have hβ0 := hP.hβ0; have hβ1 := hP.hβ1
  have h1 : 0 < 1 - P.α := by linarith
  have h2 : 0 < 1 - P.α * P.β := by nlinarith
  have hcp := cprime_pos hP
  have hρ := hP.hρk
  rw [alpha_beta_mu2_lt_one_iff hP hε, cD, div_lt_div_iff₀ hε hα0, div_lt_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- Woodford (2003), Prop. 5.1, p. 359 (survey conjecture `a − b > 0`): for `αβμ₂ ≠ 1`,
`a − b = [1 + ωθ − (ω − ν)θ(ρ_y/ρ_k) · αβ(1 − μ₁)/(1 − αβμ₁)]/(1 − αβ)`. -/
theorem a_sub_b_eq (hP : Admissible P) {ε : ℝ} (hε : 0 < ε)
    (hD : P.α * P.β * mu2 P.β (cD P ε) ≠ 1) :
    aM P ε - bM P ε = (1 + P.ω * P.θ - (P.ω - P.ν) * P.θ * (P.ρy / P.ρk) *
      (P.α * P.β * (1 - mu1 P.β (cD P ε)) / (1 - P.α * P.β * mu1 P.β (cD P ε)))) /
        (1 - P.α * P.β) := by
  obtain ⟨hx0, hx1, h10, h11, h2, h3, h4, hM⟩ := basic_facts hP hε
  have hL3 := (M_eq_Qpoly_one hP hε).2
  have hD' : 1 - P.α * P.β * mu2 P.β (cD P ε) ≠ 0 := fun h => hD (by linarith)
  have hμ0 : mu2 P.β (cD P ε) ≠ 0 := by linarith
  have hρk := hP.hρk.ne'
  have hm1 : mu2 P.β (cD P ε) - 1 ≠ 0 := by linarith
  have h4' : 1 - (mu2 P.β (cD P ε))⁻¹ = (mu2 P.β (cD P ε) - 1) / mu2 P.β (cD P ε) := by
    field_simp
  have hx' : 1 - P.α * P.β ≠ 0 := by linarith
  have h3' : 1 - P.α * P.β * mu1 P.β (cD P ε) ≠ 0 := h3.ne'
  unfold aM bM aCoef bCoef
  rw [hL3, h4']
  field_simp
  ring

/-- Woodford (2003), Prop. 5.1, p. 359 (survey conjecture, PROVED under `ρ_y ≥ ω`): `a − b > 0`
for every `ε_ψ > 0` with `αβμ₂ ≠ 1`, provided `ω ≤ ρ_y` — which the book's definitions
`ρ_y = νφ_h + φ_h ω_p/(φ_h − 1) > ω = νφ_h + ω_p` guarantee (`primitives_admissible`). -/
theorem a_sub_b_pos (hP : Admissible P) {ε : ℝ} (hε : 0 < ε)
    (hD : P.α * P.β * mu2 P.β (cD P ε) ≠ 1) (hωρ : P.ω ≤ P.ρy) : 0 < aM P ε - bM P ε := by
  obtain ⟨hx0, hx1, h10, h11, h2, h3, h4, hM⟩ := basic_facts hP hε
  rw [a_sub_b_eq hP hε hD]
  have hq : P.α * P.β * (1 - mu1 P.β (cD P ε)) / (1 - P.α * P.β * mu1 P.β (cD P ε)) < 1 := by
    rw [div_lt_one h3]; nlinarith
  have hq0 : 0 ≤ P.α * P.β * (1 - mu1 P.β (cD P ε)) / (1 - P.α * P.β * mu1 P.β (cD P ε)) := by
    apply div_nonneg _ h3.le; nlinarith
  have hρk := hP.hρk
  have hR : (P.ω - P.ν) * (P.ρy / P.ρk) ≤ P.ω := by
    rw [mul_div_assoc', div_le_iff₀ hρk, hP.hρy]
    nlinarith [hP.hν, hP.hρy]
  have hθ := hP.hθ
  have hω0 : 0 < P.ω := by linarith [hP.hν, hP.hων]
  apply div_pos _ (by linarith)
  set q := P.α * P.β * (1 - mu1 P.β (cD P ε)) / (1 - P.α * P.β * mu1 P.β (cD P ε))
  have : (P.ω - P.ν) * P.θ * (P.ρy / P.ρk) * q ≤ P.ω * P.θ * q := by
    have := mul_le_mul_of_nonneg_right hR (mul_nonneg hθ.le hq0)
    nlinarith
  have : P.ω * P.θ * q < P.ω * P.θ * 1 := mul_lt_mul_of_pos_left hq (by positivity)
  linarith

/-- Woodford (2003), (3.6)–(3.11), pp. 356–358: the book's primitive definitions
`ρ_y = νφ_h + φ_h ω_p/(φ_h − 1)`, `ρ_k = ρ_y − ν`, `ω = νφ_h + ω_p` (with `ν > 0`, `φ_h > 1`,
`ω_p > 0`) give `ρ_k > 0`, `ν < ω` and `ω < ρ_y`. -/
theorem primitives_admissible {ν φh ωp : ℝ} (hν : 0 < ν) (hφ : 1 < φh) (hωp : 0 < ωp) :
    0 < ν * φh + φh / (φh - 1) * ωp - ν ∧ ν < ν * φh + ωp ∧
      ν * φh + ωp < ν * φh + φh / (φh - 1) * ωp := by
  have h1 : 0 < φh - 1 := by linarith
  have h2 : 1 < φh / (φh - 1) := by rw [one_lt_div h1]; linarith
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-! ### (3.13) and the relation for one resetting firm -/

variable (P) in
/-- Woodford (2003), p. 359, first display (restated from Ch. 3, the Calvo first-order
condition): `∑_k (αβ)ᵏ E_t [p̂_{t+k}(i) − ŝ_{t+k}(i)] = 0`. -/
def CalvoFOC (p sf : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, ∑' j, (P.α * P.β) ^ j * 𝔼.E t (p (t + j) - sf (t + j)) ω = 0

variable (P) in
/-- Woodford (2003), (3.12) p. 358: `ŝ_t(i) = ŝ_t − (ω − ν)k̃_t(i) − ωθ p̂_t(i)`. -/
def MC312 (sf s k p : ℕ → Ω → ℝ) : Prop :=
  ∀ τ, sf τ = s τ - (P.ω - P.ν) • k τ - (P.ω * P.θ) • p τ

variable (P) in
/-- Woodford (2003), (3.13) p. 359:
`∑_k (αβ)ᵏ E_t [(1 + ωθ)p̂_{t+k}(i) − ŝ_{t+k} + (ω − ν)k̃_{t+k}(i)] = 0`. -/
def Eq313 (p s k : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, ∑' j, (P.α * P.β) ^ j *
    𝔼.E t ((1 + P.ω * P.θ) • p (t + j) - s (t + j) + (P.ω - P.ν) • k (t + j)) ω = 0

/-- Woodford (2003), (3.13) p. 359: substituting (3.12) into the Calvo condition gives (3.13). -/
theorem eq313_of_calvo {p sf s k : ℕ → Ω → ℝ} {t : ℕ} (hF : CalvoFOC P 𝔼 p sf t)
    (h312 : MC312 P sf s k p) : Eq313 P 𝔼 p s k t := by
  intro ω
  rw [← hF ω]
  refine tsum_congr fun j => ?_
  have hfun : (1 + P.ω * P.θ) • p (t + j) - s (t + j) + (P.ω - P.ν) • k (t + j) =
      p (t + j) - sf (t + j) := by
    rw [h312]
    funext ω'
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun]

variable (P) in
/-- Woodford (2003), App. D.2, p. 690: `G = (ω − ν) α M/(1 − αβμ₁)`, the weight of the capital
terms after substituting (D.5) and (D.6) into (3.13). -/
noncomputable def GCoef (M μ₁ : ℝ) : ℝ := (P.ω - P.ν) * P.α * M / (1 - P.α * P.β * μ₁)

variable (P) in
/-- Woodford (2003), App. D.2, p. 690: the weight of `E_t p̂_{t+n}(i)` in the firm's relation,
`w_n = (1 + ωθ)(αβ)ⁿ − G C_n`. -/
noncomputable def wCoef (M μ₁ μ₂ : ℝ) (n : ℕ) : ℝ :=
  (1 + P.ω * P.θ) * (P.α * P.β) ^ n - GCoef P M μ₁ * cD6 (P.α * P.β) μ₂⁻¹ n

/-- Woodford (2003), App. D.2, p. 690: the weights `w_n` are absolutely summable (for
`|αβ| < 1`, `μ₂ > 1`). -/
theorem summable_abs_wCoef {M μ₁ μ₂ : ℝ} (hx : |P.α * P.β| < 1) (hμ : 1 < μ₂) :
    Summable fun n => |wCoef P M μ₁ μ₂ n| := by
  have hm : |μ₂⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith)]; exact inv_lt_one_of_one_lt₀ hμ
  set ρ := max |P.α * P.β| |μ₂⁻¹|
  have hρ0 : 0 ≤ ρ := le_max_of_le_left (abs_nonneg _)
  have hρ1 : ρ < 1 := max_lt hx hm
  have hρ' : ‖ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hρ0]; exact hρ1
  have h1 : Summable fun n : ℕ => |1 + P.ω * P.θ| * |P.α * P.β| ^ n +
      |GCoef P M μ₁| * ((n : ℝ) ^ 1 * ρ ^ n) :=
    ((summable_geometric_of_lt_one (abs_nonneg _) hx).mul_left _).add
      ((summable_pow_mul_geometric_of_norm_lt_one 1 hρ').mul_left _)
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) h1
  unfold wCoef
  refine (abs_sub _ _).trans (add_le_add (by rw [abs_mul, abs_pow]) ?_)
  rw [abs_mul, pow_one]
  exact mul_le_mul_of_nonneg_left (abs_cD6_le (le_max_left _ _) (le_max_right _ _) n)
    (abs_nonneg _)

/-- Woodford (2003), App. D.2, p. 690: `∑ w_n P_n` converges for bounded `P`. -/
theorem summable_wCoef_mul {M μ₁ μ₂ B : ℝ} (hx : |P.α * P.β| < 1) (hμ : 1 < μ₂)
    {Q : ℕ → ℝ} (hQ : ∀ n, |Q n| ≤ B) : Summable fun n => wCoef P M μ₁ μ₂ n * Q n :=
  Summable.of_norm_bounded ((summable_abs_wCoef hx hμ).mul_right B) fun n => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hQ n) (abs_nonneg _)

/-- Woodford (2003), App. D.2, p. 690 (the relation for one resetting firm): substituting the
unique bounded capital path (D.4), and (D.5)–(D.6), into (3.13) gives
`∑_n w_n E_t p̂_{t+n}(i) = ∑_k (αβ)ᵏ E_t ŝ_{t+k} − (ω − ν)/(1 − αβμ₁) · k̃_t(i)`. -/
theorem firm_relation (hP : Admissible P) {ε : ℝ} (hε : 0 < ε) {p k s : ℕ → Ω → ℝ}
    {B Bs : ℝ} (hp : ∀ τ ω, |p τ ω| ≤ B) (hk : BoundedProc k) (hka : 𝔼.Adapted k)
    (hpre : ∀ τ, 𝔼.E τ (k (τ + 1)) = k (τ + 1)) (hD3 : D3 𝔼 P.β (cD P ε) (MD P ε) k p)
    (hs : ∀ τ ω, |s τ ω| ≤ Bs) (t : ℕ) (h313 : Eq313 P 𝔼 p s k t) (ω : Ω) :
    ∑' n, wCoef P (MD P ε) (mu1 P.β (cD P ε)) (mu2 P.β (cD P ε)) n * 𝔼.E t (p (t + n)) ω =
      ∑' n, (P.α * P.β) ^ n * 𝔼.E t (s (t + n)) ω -
        (P.ω - P.ν) / (1 - P.α * P.β * mu1 P.β (cD P ε)) * k t ω := by
  obtain ⟨hx0, hx1, h10, h11, h2, h3, h4, hM⟩ := basic_facts hP hε
  have hc := cD_pos hP hε
  have hβ := hP.hβ0
  set c := cD P ε with hc_def
  set M := MD P ε with hM_def
  set μ₁ := mu1 P.β c with hμ₁
  set μ₂ := mu2 P.β c with hμ₂
  set x := P.α * P.β with hx_def
  have hxa : |x| < 1 := by rw [abs_of_pos hx0]; exact hx1
  have hxμ : |x * μ₁| < 1 := by
    rw [abs_of_pos (by positivity)]; linarith
  have hm : |μ₂⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith)]; exact inv_lt_one_of_one_lt₀ h2
  have hD4 := D4_of_D3 𝔼 hβ (vieta_sum hβ) (vieta_prod hβ hc) h2 hp hk hpre hD3
  obtain ⟨hzb, -⟩ := zD4_bounded_adapted 𝔼 (M := M) hβ.ne' h2 hp
  have h5 := D5 𝔼 hxa hxμ hD4 hzb t (hka t) ω
  have h6 := D6_coeff 𝔼 (β := P.β) (M := M) hxa h2 hp t ω
  obtain ⟨Bk, hBk⟩ := hk
  -- summability of the pieces
  have hgeo : ∀ {Q : ℕ → ℝ} {C : ℝ}, (∀ n, |Q n| ≤ C) → Summable fun n => x ^ n * Q n :=
    fun {Q C} hQ => Summable.of_norm_bounded
      ((summable_geometric_of_abs_lt_one hxa).abs.mul_right C) fun n => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hQ n) (abs_nonneg _)
  have hPb : ∀ n, |𝔼.E t (p (t + n)) ω| ≤ B := fun n => 𝔼.abs_E_le (hp (t + n)) t ω
  have hSP := hgeo hPb
  have hSS := hgeo (fun n => 𝔼.abs_E_le (hs (t + n)) t ω)
  have hSK := hgeo (fun n => 𝔼.abs_E_le (hBk (t + n)) t ω)
  set ρ := max |x| |μ₂⁻¹|
  have hρ0 : 0 ≤ ρ := le_max_of_le_left (abs_nonneg _)
  have hρ' : ‖ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hρ0]; exact max_lt hxa hm
  have hSC : Summable fun n => cD6 x μ₂⁻¹ n * 𝔼.E t (p (t + n)) ω := by
    refine Summable.of_norm_bounded
      ((summable_pow_mul_geometric_of_norm_lt_one 1 hρ').mul_right B) fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, pow_one]
    exact mul_le_mul (abs_cD6_le (le_max_left _ _) (le_max_right _ _) n) (hPb n)
      (abs_nonneg _) (by positivity)
  -- (3.13) split into its three sums
  have e313 : (1 + P.ω * P.θ) * ∑' n, x ^ n * 𝔼.E t (p (t + n)) ω -
      ∑' n, x ^ n * 𝔼.E t (s (t + n)) ω +
      (P.ω - P.ν) * ∑' n, x ^ n * 𝔼.E t (k (t + n)) ω = 0 := by
    rw [← h313 ω, ← tsum_mul_left, ← tsum_mul_left, ← (hSP.mul_left _).tsum_sub hSS,
      ← ((hSP.mul_left _).sub hSS).tsum_add (hSK.mul_left _)]
    refine tsum_congr fun n => ?_
    simp only [map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  have hC0 : ∑' n, cD6 x μ₂⁻¹ n * 𝔼.E t (p (t + n)) ω =
      ∑' n, cD6 x μ₂⁻¹ (n + 1) * 𝔼.E t (p (t + (n + 1))) ω := by
    rw [hSC.tsum_eq_zero_add, cD6_zero, zero_mul, zero_add]
  have ew : ∑' n, wCoef P M μ₁ μ₂ n * 𝔼.E t (p (t + n)) ω =
      (1 + P.ω * P.θ) * ∑' n, x ^ n * 𝔼.E t (p (t + n)) ω -
        GCoef P M μ₁ * ∑' n, cD6 x μ₂⁻¹ n * 𝔼.E t (p (t + n)) ω := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (hSP.mul_left _).tsum_sub (hSC.mul_left _)]
    refine tsum_congr fun n => ?_
    unfold wCoef; ring
  rw [ew, hC0]
  rw [h5, h6] at e313
  have hxμ' : 1 - x * μ₁ ≠ 0 := h3.ne'
  have hG : GCoef P M μ₁ = (P.ω - P.ν) * P.α * M / (1 - x * μ₁) := rfl
  have hαx : P.α = x * P.β⁻¹ := by rw [hx_def]; field_simp
  rw [hG, hαx]
  generalize ∑' n, x ^ n * 𝔼.E t (p (t + n)) ω = SP at e313 ⊢
  generalize ∑' n, x ^ n * 𝔼.E t (s (t + n)) ω = SS at e313 ⊢
  generalize ∑' n, cD6 x μ₂⁻¹ (n + 1) * 𝔼.E t (p (t + (n + 1))) ω = SC at e313 ⊢
  generalize k t ω = k0 at e313 ⊢
  field_simp at e313 ⊢
  linear_combination e313

/-! ### L7 (Calvo averaging) and Proposition 5.1 -/

/-- Woodford (2003), App. D.2, p. 690 (survey L7, the averaging step): the cross-section of the
firms that reset at date `t` is a probability space `(ι, wt)`. MODELLING HYPOTHESES (the book's
"all firms are equally likely to choose new prices"): the resetters' average relative capital
stock is zero, `∫ k̃_t(i) = 0`, and their average expected relative price is
`∫ E_t p̂_{t+n}(i) = p̂*_t − ∑_{j=1}^n E_t π_{t+j}`. Each firm's capital and price paths satisfy
(D.3) and (3.13). Then `∑_n w_n (p̂*_t − ∑_{j<n} E_t π_{t+j+1}) = ∑_k (αβ)ᵏ E_t ŝ_{t+k}`. -/
theorem prop51_averaged (hP : Admissible P) {ε : ℝ} (hε : 0 < ε) {ι : Type*}
    [MeasurableSpace ι] (wt : Measure ι) [IsProbabilityMeasure wt]
    {p k : ι → ℕ → Ω → ℝ} {s infl : ℕ → Ω → ℝ} {pstar : Ω → ℝ} {B Bs : ℝ}
    (hp : ∀ i τ ω, |p i τ ω| ≤ B) (hk : ∀ i, BoundedProc (k i)) (hka : ∀ i, 𝔼.Adapted (k i))
    (hpre : ∀ i τ, 𝔼.E τ (k i (τ + 1)) = k i (τ + 1))
    (hD3 : ∀ i, D3 𝔼 P.β (cD P ε) (MD P ε) (k i) (p i))
    (hs : ∀ τ ω, |s τ ω| ≤ Bs) (t : ℕ) (h313 : ∀ i, Eq313 P 𝔼 (p i) s (k i) t)
    (hik : ∀ ω, Integrable (fun i => k i t ω) wt)
    (hip : ∀ n ω, Integrable (fun i => 𝔼.E t (p i (t + n)) ω) wt)
    (havk : ∀ ω, ∫ i, k i t ω ∂wt = 0)
    (havp : ∀ n ω, ∫ i, 𝔼.E t (p i (t + n)) ω ∂wt =
      pstar ω - ∑ j ∈ Finset.range n, 𝔼.E t (infl (t + j + 1)) ω) (ω : Ω) :
    ∑' n, wCoef P (MD P ε) (mu1 P.β (cD P ε)) (mu2 P.β (cD P ε)) n *
        (pstar ω - ∑ j ∈ Finset.range n, 𝔼.E t (infl (t + j + 1)) ω) =
      ∑' n, (P.α * P.β) ^ n * 𝔼.E t (s (t + n)) ω := by
  obtain ⟨hx0, hx1, -, -, h2, -, -, -⟩ := basic_facts hP hε
  have hxa : |P.α * P.β| < 1 := by rw [abs_of_pos hx0]; exact hx1
  set w := wCoef P (MD P ε) (mu1 P.β (cD P ε)) (mu2 P.β (cD P ε)) with hw
  set cK := (P.ω - P.ν) / (1 - P.α * P.β * mu1 P.β (cD P ε))
  set SS := ∑' n, (P.α * P.β) ^ n * 𝔼.E t (s (t + n)) ω
  have hfirm : ∀ i, ∑' n, w n * 𝔼.E t (p i (t + n)) ω = SS - cK * k i t ω := fun i =>
    firm_relation 𝔼 hP hε (hp i) (hk i) (hka i) (hpre i) (hD3 i) hs t (h313 i) ω
  have hint : ∫ i, ∑' n, w n * 𝔼.E t (p i (t + n)) ω ∂wt = ∫ i, (SS - cK * k i t ω) ∂wt :=
    integral_congr_ae (Eventually.of_forall hfirm)
  have hR : ∫ i, (SS - cK * k i t ω) ∂wt = SS := by
    rw [integral_sub (integrable_const _) ((hik ω).const_mul cK), integral_const,
      integral_const_mul, havk ω, probReal_univ, one_smul, mul_zero, sub_zero]
  have hFi : ∀ n, Integrable (fun i => w n * 𝔼.E t (p i (t + n)) ω) wt :=
    fun n => (hip n ω).const_mul (w n)
  have hbd : ∀ n, ∫ i, ‖w n * 𝔼.E t (p i (t + n)) ω‖ ∂wt ≤ |w n| * B := by
    intro n
    have h := norm_integral_le_of_norm_le_const (μ := wt)
      (f := fun i => ‖w n * 𝔼.E t (p i (t + n)) ω‖) (C := |w n| * B)
      (Eventually.of_forall fun i => by
        rw [norm_norm, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hp i (t + n)) t ω) (abs_nonneg _))
    rw [probReal_univ, mul_one] at h
    exact (le_abs_self _).trans (by rwa [Real.norm_eq_abs] at h)
  have hFs : Summable fun n => ∫ i, ‖w n * 𝔼.E t (p i (t + n)) ω‖ ∂wt :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun i => norm_nonneg _) hbd
      ((summable_abs_wCoef hxa h2).mul_right B)
  rw [← integral_tsum_of_summable_integral_norm hFi hFs, hR] at hint
  rw [← hint]
  refine tsum_congr fun n => ?_
  rw [integral_const_mul, havp n ω]

variable (P) in
/-- Woodford (2003), (3.14) p. 359, the coefficient of `p̂*_t` when `αβμ₂ = 1`, where the
printed `a`, `b` divide by zero: `a₀ = (1 + ωθ)/(1 − αβ) − G αβ/(1 − αβ)²` (the common limit of
`a − b`). -/
noncomputable def a0Coef (M μ₁ : ℝ) : ℝ :=
  (1 + P.ω * P.θ) / (1 - P.α * P.β) - GCoef P M μ₁ * (P.α * P.β) / (1 - P.α * P.β) ^ 2

/-- **Proposition 5.1** (Woodford (2003), (3.14) p. 359; App. D.2, (D.1) pp. 688–690), in full:
under the model equations (D.3) (from (3.7)) and (3.13) for each resetting firm and the Calvo
averaging hypotheses (L7, `prop51_averaged`), whenever `αβμ₂ ≠ 1`,
`(a − b) p̂*_t = ∑_{k≥0} (αβ)ᵏ E_t ŝ_{t+k} + a ∑_{k≥1} (αβ)ᵏ E_t π_{t+k}
− b ∑_{k≥1} μ₂^{-k} E_t π_{t+k}`, all three series converging. -/
theorem prop51 (hP : Admissible P) {ε : ℝ} (hε : 0 < ε)
    (hD : P.α * P.β * mu2 P.β (cD P ε) ≠ 1) {ι : Type*}
    [MeasurableSpace ι] (wt : Measure ι) [IsProbabilityMeasure wt]
    {p k : ι → ℕ → Ω → ℝ} {s infl : ℕ → Ω → ℝ} {pstar : Ω → ℝ} {B Bs Bπ : ℝ}
    (hp : ∀ i τ ω, |p i τ ω| ≤ B) (hk : ∀ i, BoundedProc (k i)) (hka : ∀ i, 𝔼.Adapted (k i))
    (hpre : ∀ i τ, 𝔼.E τ (k i (τ + 1)) = k i (τ + 1))
    (hD3 : ∀ i, D3 𝔼 P.β (cD P ε) (MD P ε) (k i) (p i))
    (hs : ∀ τ ω, |s τ ω| ≤ Bs) (hπ : ∀ τ ω, |infl τ ω| ≤ Bπ) (t : ℕ)
    (h313 : ∀ i, Eq313 P 𝔼 (p i) s (k i) t)
    (hik : ∀ ω, Integrable (fun i => k i t ω) wt)
    (hip : ∀ n ω, Integrable (fun i => 𝔼.E t (p i (t + n)) ω) wt)
    (havk : ∀ ω, ∫ i, k i t ω ∂wt = 0)
    (havp : ∀ n ω, ∫ i, 𝔼.E t (p i (t + n)) ω ∂wt =
      pstar ω - ∑ j ∈ Finset.range n, 𝔼.E t (infl (t + j + 1)) ω) (ω : Ω) :
    (aM P ε - bM P ε) * pstar ω =
      ∑' k, (P.α * P.β) ^ k * 𝔼.E t (s (t + k)) ω +
        aM P ε * ∑' k, (P.α * P.β) ^ (k + 1) * 𝔼.E t (infl (t + k + 1)) ω -
        bM P ε * ∑' k, (mu2 P.β (cD P ε))⁻¹ ^ (k + 1) * 𝔼.E t (infl (t + k + 1)) ω := by
  obtain ⟨hx0, hx1, h10, h11, h2, h3, h4, hM⟩ := basic_facts hP hε
  have hav := prop51_averaged 𝔼 hP hε wt hp hk hka hpre hD3 hs t h313 hik hip havk havp ω
  set x := P.α * P.β with hx_def
  set μ₁ := mu1 P.β (cD P ε)
  set μ₂ := mu2 P.β (cD P ε)
  set M := MD P ε
  set y : ℕ → ℝ := fun j => 𝔼.E t (infl (t + j + 1)) ω with hy
  have hyb : ∀ j, |y j| ≤ Bπ := fun j => 𝔼.abs_E_le (hπ (t + j + 1)) t ω
  have hxa : |x| < 1 := by rw [abs_of_pos hx0]; exact hx1
  have hμ0 : μ₂ ≠ 0 := by linarith
  have hm : |μ₂⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith)]; exact inv_lt_one_of_one_lt₀ h2
  have hD' : 1 - x * μ₂ ≠ 0 := fun h => hD (by linarith)
  have hx' : 1 - x ≠ 0 := by linarith
  have hm' : 1 - μ₂⁻¹ ≠ 0 := h4.ne'
  have hm1 : μ₂ - 1 ≠ 0 := by linarith
  have hm2 : -1 + μ₂ ≠ 0 := by linarith
  have h3' : 1 - x * μ₁ ≠ 0 := h3.ne'
  -- the weights in closed form
  have hw : ∀ n, wCoef P M μ₁ μ₂ n = (1 - x) * aM P ε * x ^ n - (1 - μ₂⁻¹) * bM P ε * μ₂⁻¹ ^ n := by
    intro n
    have hc := cD6_closed (x := x) hμ0 n
    have : cD6 x μ₂⁻¹ n = (μ₂⁻¹ ^ n - x ^ n) / (1 - x * μ₂) := by
      rw [eq_div_iff hD', mul_comm]; exact hc
    have ha : aM P ε = aCoef P M μ₁ μ₂ := rfl
    have hb : bM P ε = bCoef P M μ₁ μ₂ := rfl
    rw [ha, hb]
    unfold wCoef GCoef aCoef bCoef
    rw [← hx_def, this]
    field_simp
    ring
  obtain ⟨hS1, hV1⟩ := tsum_geom_pbar hxa hyb (pstar ω)
  obtain ⟨hS2, hV2⟩ := tsum_geom_pbar hm hyb (pstar ω)
  have hsplit : ∑' n, wCoef P M μ₁ μ₂ n * (pstar ω - ∑ j ∈ Finset.range n, y j) =
      (1 - x) * aM P ε * ∑' n, x ^ n * (pstar ω - ∑ j ∈ Finset.range n, y j) -
        (1 - μ₂⁻¹) * bM P ε * ∑' n, μ₂⁻¹ ^ n * (pstar ω - ∑ j ∈ Finset.range n, y j) := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (hS1.mul_left _).tsum_sub (hS2.mul_left _)]
    refine tsum_congr fun n => ?_
    rw [hw]; ring
  have e1 : ∑' k, x ^ (k + 1) * y k = x * ∑' k, x ^ k * y k := by
    rw [← tsum_mul_left]; exact tsum_congr fun k => by ring
  have e2 : ∑' k, μ₂⁻¹ ^ (k + 1) * y k = μ₂⁻¹ * ∑' k, μ₂⁻¹ ^ k * y k := by
    rw [← tsum_mul_left]; exact tsum_congr fun k => by ring
  change ∑' n, wCoef P M μ₁ μ₂ n * (pstar ω - ∑ j ∈ Finset.range n, y j) = _ at hav
  change _ = _ + aM P ε * ∑' k, x ^ (k + 1) * y k - bM P ε * ∑' k, μ₂⁻¹ ^ (k + 1) * y k
  rw [hsplit, hV1, hV2] at hav
  rw [e1, e2, ← hav]
  field_simp
  ring

/-- Woodford (2003), (3.14) p. 359, CORRECTED for the case `αβμ₂ = 1` (where the printed `a`, `b`
and (D.6) divide by zero): with `a₀ = (1 + ωθ)/(1 − αβ) − Gαβ/(1 − αβ)²` and
`G = (ω − ν)αM/(1 − αβμ₁)`,
`a₀ p̂*_t = ∑_{k≥0} (αβ)ᵏ E_t ŝ_{t+k} + a₀ ∑_{k≥1} (αβ)ᵏ E_t π_{t+k}
− G/(1 − αβ) ∑_{k≥1} k (αβ)ᵏ E_t π_{t+k}`. -/
theorem prop51_eq_case (hP : Admissible P) {ε : ℝ} (hε : 0 < ε)
    (hD : P.α * P.β * mu2 P.β (cD P ε) = 1) {ι : Type*}
    [MeasurableSpace ι] (wt : Measure ι) [IsProbabilityMeasure wt]
    {p k : ι → ℕ → Ω → ℝ} {s infl : ℕ → Ω → ℝ} {pstar : Ω → ℝ} {B Bs Bπ : ℝ}
    (hp : ∀ i τ ω, |p i τ ω| ≤ B) (hk : ∀ i, BoundedProc (k i)) (hka : ∀ i, 𝔼.Adapted (k i))
    (hpre : ∀ i τ, 𝔼.E τ (k i (τ + 1)) = k i (τ + 1))
    (hD3 : ∀ i, D3 𝔼 P.β (cD P ε) (MD P ε) (k i) (p i))
    (hs : ∀ τ ω, |s τ ω| ≤ Bs) (hπ : ∀ τ ω, |infl τ ω| ≤ Bπ) (t : ℕ)
    (h313 : ∀ i, Eq313 P 𝔼 (p i) s (k i) t)
    (hik : ∀ ω, Integrable (fun i => k i t ω) wt)
    (hip : ∀ n ω, Integrable (fun i => 𝔼.E t (p i (t + n)) ω) wt)
    (havk : ∀ ω, ∫ i, k i t ω ∂wt = 0)
    (havp : ∀ n ω, ∫ i, 𝔼.E t (p i (t + n)) ω ∂wt =
      pstar ω - ∑ j ∈ Finset.range n, 𝔼.E t (infl (t + j + 1)) ω) (ω : Ω) :
    a0Coef P (MD P ε) (mu1 P.β (cD P ε)) * pstar ω =
      ∑' k, (P.α * P.β) ^ k * 𝔼.E t (s (t + k)) ω +
        a0Coef P (MD P ε) (mu1 P.β (cD P ε)) *
          ∑' k, (P.α * P.β) ^ (k + 1) * 𝔼.E t (infl (t + k + 1)) ω -
        GCoef P (MD P ε) (mu1 P.β (cD P ε)) / (1 - P.α * P.β) *
          ∑' k : ℕ, ((k : ℝ) + 1) * (P.α * P.β) ^ (k + 1) * 𝔼.E t (infl (t + k + 1)) ω := by
  obtain ⟨hx0, hx1, h10, h11, h2, h3, h4, hM⟩ := basic_facts hP hε
  have hav := prop51_averaged 𝔼 hP hε wt hp hk hka hpre hD3 hs t h313 hik hip havk havp ω
  set x := P.α * P.β with hx_def
  set μ₁ := mu1 P.β (cD P ε)
  set μ₂ := mu2 P.β (cD P ε)
  set M := MD P ε
  set y : ℕ → ℝ := fun j => 𝔼.E t (infl (t + j + 1)) ω with hy
  have hyb : ∀ j, |y j| ≤ Bπ := fun j => 𝔼.abs_E_le (hπ (t + j + 1)) t ω
  have hxa : |x| < 1 := by rw [abs_of_pos hx0]; exact hx1
  have hμ0 : μ₂ ≠ 0 := by linarith
  have hxm : μ₂⁻¹ = x := by field_simp; linarith
  have hx' : 1 - x ≠ 0 := by linarith
  set G := GCoef P M μ₁
  have hw : ∀ n : ℕ, wCoef P M μ₁ μ₂ n = (1 + P.ω * P.θ) * x ^ n - G * (n * x ^ n) := by
    intro n
    unfold wCoef
    rw [← hx_def, hxm, cD6_eq_case]
  obtain ⟨hS1, hV1⟩ := tsum_geom_pbar hxa hyb (pstar ω)
  obtain ⟨hS2, hV2⟩ := tsum_natgeom_pbar hxa hyb (pstar ω)
  have hsplit : ∑' n, wCoef P M μ₁ μ₂ n * (pstar ω - ∑ j ∈ Finset.range n, y j) =
      (1 + P.ω * P.θ) * ∑' n, x ^ n * (pstar ω - ∑ j ∈ Finset.range n, y j) -
        G * ∑' n : ℕ, n * x ^ n * (pstar ω - ∑ j ∈ Finset.range n, y j) := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (hS1.mul_left _).tsum_sub (hS2.mul_left _)]
    refine tsum_congr fun n => ?_
    rw [hw]; ring
  have e1 : ∑' k, x ^ (k + 1) * y k = x * ∑' k, x ^ k * y k := by
    rw [← tsum_mul_left]; exact tsum_congr fun k => by ring
  have e2 : ∑' k : ℕ, ((k : ℝ) + 1) * x ^ (k + 1) * y k =
      x * ∑' k : ℕ, ((k : ℝ) + 1) * x ^ k * y k := by
    rw [← tsum_mul_left]; exact tsum_congr fun k => by ring
  change ∑' n, wCoef P M μ₁ μ₂ n * (pstar ω - ∑ j ∈ Finset.range n, y j) = _ at hav
  change _ = _ + a0Coef P M μ₁ * ∑' k, x ^ (k + 1) * y k -
    G / (1 - x) * ∑' k : ℕ, ((k : ℝ) + 1) * x ^ (k + 1) * y k
  rw [hsplit, hV1, hV2] at hav
  rw [e1, e2, ← hav]
  unfold a0Coef
  rw [← hx_def]
  field_simp
  ring

/-! ### Counterexamples: the printed positivity claim, and `a − b > 0` without `ρ_y ≥ ω` -/

/-- Woodford (2003), Table 5.1 p. 342 and p. 363: the book's calibration `α = .66`, `β = .99`,
`δ = .012`, `θ = 7.88`, `ν = .11`, `ω_p = .33`, `φ_h = 4/3`, so `ω = νφ_h + ω_p = 143/300`,
`ρ_y = νφ_h + φ_h ω_p/(φ_h − 1) = 22/15`, `ρ_k = ρ_y − ν = 407/300`. -/
noncomputable def bookParams : Params where
  α := 66 / 100
  β := 99 / 100
  δ := 12 / 1000
  θ := 788 / 100
  ω := 143 / 300
  ν := 11 / 100
  ρy := 22 / 15
  ρk := 407 / 300

/-- Woodford (2003), Table 5.1 p. 342: the book's calibration is admissible, and it satisfies
`ω ≤ ρ_y`. -/
theorem bookParams_admissible : Admissible bookParams ∧ bookParams.ω ≤ bookParams.ρy := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> norm_num [bookParams]

/-- Woodford (2003), (3.14) p. 359: a sufficient condition for `a < 0` when `αβμ₂ > 1`:
`(ω − ν)αM > (1 + ωθ)(1 − αβμ₁)(αβμ₂ − 1)`. -/
theorem a_neg_of (hP : Admissible P) {ε : ℝ} (hε : 0 < ε)
    (hD : 1 < P.α * P.β * mu2 P.β (cD P ε))
    (hG : (1 + P.ω * P.θ) * (1 - P.α * P.β * mu1 P.β (cD P ε)) *
      (P.α * P.β * mu2 P.β (cD P ε) - 1) < (P.ω - P.ν) * P.α * MD P ε) : aM P ε < 0 := by
  obtain ⟨hx0, hx1, h10, h11, h2, h3, h4, hM⟩ := basic_facts hP hε
  have hD' : 1 - P.α * P.β * mu2 P.β (cD P ε) ≠ 0 := by linarith
  have hx' : 1 - P.α * P.β ≠ 0 := by linarith
  have h3' : 1 - P.α * P.β * mu1 P.β (cD P ε) ≠ 0 := h3.ne'
  have hN : (1 - P.α * P.β * mu1 P.β (cD P ε)) * (1 - P.α * P.β * mu2 P.β (cD P ε)) < 0 :=
    mul_neg_of_pos_of_neg h3 (by linarith)
  have he : aM P ε = ((1 + P.ω * P.θ) * ((1 - P.α * P.β * mu1 P.β (cD P ε)) *
      (1 - P.α * P.β * mu2 P.β (cD P ε))) + (P.ω - P.ν) * P.α * MD P ε) /
      (((1 - P.α * P.β * mu1 P.β (cD P ε)) * (1 - P.α * P.β * mu2 P.β (cD P ε))) *
        (1 - P.α * P.β)) := by
    unfold aM aCoef
    field_simp
  rw [he]
  apply div_neg_of_pos_of_neg _ (mul_neg_of_neg_of_pos hN (by linarith))
  nlinarith

/-- Woodford (2003), Prop. 5.1, p. 359 (survey error 1, CONFIRMED): at the book's calibration
(Table 5.1, `δ = .012`) with `ε_ψ = 0.1` (one of the values of Fig. 5.6's range of `ε_ψ`):
`1.72 < μ₂ < 1.73`, `αβμ₂ > 1`, and both `a < 0` and `b < 0` (numerically `a ≈ −8.9`,
`b ≈ −18.7`). So the printed claim "`a > 0, b > 0`" is false. -/
theorem book_calibration_a_neg :
    1.72 < mu2 bookParams.β (cD bookParams (1 / 10)) ∧
      mu2 bookParams.β (cD bookParams (1 / 10)) < 1.73 ∧
      1 < bookParams.α * bookParams.β * mu2 bookParams.β (cD bookParams (1 / 10)) ∧
      aM bookParams (1 / 10) < 0 ∧ bM bookParams (1 / 10) < 0 := by
  have hP := bookParams_admissible.1
  have hε : (0 : ℝ) < 1 / 10 := by norm_num
  have hc : cD bookParams (1 / 10) = 222629 / 750000 := by
    norm_num [cD, cprime, bookParams]
  have hd : discr bookParams.β (cD bookParams (1 / 10)) = 714167486641 / 562500000000 := by
    rw [hc]; norm_num [discr, bookParams]
  set S := √(discr bookParams.β (cD bookParams (1 / 10))) with hS
  have hs1 : (1.12 : ℝ) < S := by
    rw [hS, Real.lt_sqrt (by norm_num), hd]; norm_num
  have hs2 : S < 1.13 := by
    rw [hS, Real.sqrt_lt' (by norm_num), hd]; norm_num
  have hmu2 : mu2 bookParams.β (cD bookParams (1 / 10)) =
      (1 + bookParams.β + cD bookParams (1 / 10) + S) / (2 * bookParams.β) := rfl
  have hβv : bookParams.β = 99 / 100 := rfl
  have hlo : 1.72 < mu2 bookParams.β (cD bookParams (1 / 10)) := by
    rw [hmu2, hc, hβv, lt_div_iff₀ (by norm_num)]; linarith
  have hhi : mu2 bookParams.β (cD bookParams (1 / 10)) < 1.73 := by
    rw [hmu2, hc, hβv, div_lt_iff₀ (by norm_num)]; linarith
  have hD : 1 < bookParams.α * bookParams.β * mu2 bookParams.β (cD bookParams (1 / 10)) := by
    norm_num [bookParams] at hlo ⊢; linarith
  refine ⟨hlo, hhi, hD, ?_, b_neg_of hP hε hD⟩
  apply a_neg_of hP hε hD
  have hprod := vieta_prod hP.hβ0 (cD_pos hP hε)
  set μ₁ := mu1 bookParams.β (cD bookParams (1 / 10))
  set μ₂ := mu2 bookParams.β (cD bookParams (1 / 10))
  have hμ₂ : 0 < μ₂ := by linarith
  have hx : bookParams.α * bookParams.β * μ₁ = bookParams.α / μ₂ := by
    rw [eq_div_iff hμ₂.ne']; linear_combination bookParams.α * hprod
  have hM : MD bookParams (1 / 10) = 1185349 / 468750 := by
    norm_num [MD, cprime, bookParams]
  rw [hx, hM]
  have h1 : 1 - bookParams.α / μ₂ < 1 - bookParams.α / 1.73 := by
    have : bookParams.α / 1.73 < bookParams.α / μ₂ :=
      div_lt_div_of_pos_left (by norm_num [bookParams]) hμ₂ hhi
    linarith
  have h1' : 0 < 1 - bookParams.α / μ₂ := by
    rw [sub_pos, div_lt_one hμ₂]; norm_num [bookParams]; linarith
  have h2 : bookParams.α * bookParams.β * μ₂ - 1 < bookParams.α * bookParams.β * 1.73 - 1 := by
    norm_num [bookParams]; linarith
  have h2' : 0 < bookParams.α * bookParams.β * μ₂ - 1 := by linarith
  have hA : (0 : ℝ) < 1 + bookParams.ω * bookParams.θ := by norm_num [bookParams]
  calc (1 + bookParams.ω * bookParams.θ) * (1 - bookParams.α / μ₂) *
        (bookParams.α * bookParams.β * μ₂ - 1)
      < (1 + bookParams.ω * bookParams.θ) * (1 - bookParams.α / 1.73) *
        (bookParams.α * bookParams.β * 1.73 - 1) := by
        apply mul_lt_mul'' (mul_lt_mul_of_pos_left h1 hA) h2 (by positivity) h2'.le
    _ < (bookParams.ω - bookParams.ν) * bookParams.α * (1185349 / 468750) := by
        norm_num [bookParams]

/-- Woodford (2003), Prop. 5.1 (survey conjecture): at the book's calibration `a − b > 0` for
EVERY `ε_ψ > 0` with `αβμ₂ ≠ 1` (because `ω = 143/300 ≤ ρ_y = 22/15`). -/
theorem book_a_sub_b_pos {ε : ℝ} (hε : 0 < ε)
    (hD : bookParams.α * bookParams.β * mu2 bookParams.β (cD bookParams ε) ≠ 1) :
    0 < aM bookParams ε - bM bookParams ε :=
  a_sub_b_pos bookParams_admissible.1 hε hD bookParams_admissible.2

/-- Woodford (2003), Prop. 5.1 (survey conjecture `a − b > 0` "always"): the conjecture FAILS
if only the stated coefficient restrictions (`ρ_y > ρ_k = ρ_y − ν > 0`, `ω > ν`) are imposed.
With `α = 1/3`, `β = 1/2`, `δ = 1/2`, `θ = 10`, `ω = 2`, `ν = 1`, `ρ_y = 1.01`, `ρ_k = .01`
and `ε_ψ = 1/100` (so `c = 3/4`, `μ₁ = 1/2`, `μ₂ = 4`, `αβμ₂ = 2/3`): `a − b < 0`. Here
`ω > ρ_y`, which the book's primitive definitions rule out (`primitives_admissible`). -/
theorem a_sub_b_neg_example :
    ∃ P : Params, Admissible P ∧ P.ρy < P.ω ∧
      P.α * P.β * mu2 P.β (cD P (1 / 100)) ≠ 1 ∧ aM P (1 / 100) - bM P (1 / 100) < 0 := by
  set P : Params := ⟨1 / 3, 1 / 2, 1 / 2, 10, 2, 1, 101 / 100, 1 / 100⟩ with hPdef
  have hP : Admissible P := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [hPdef]
  have hε : (0 : ℝ) < 1 / 100 := by norm_num
  have hc : cD P (1 / 100) = 3 / 4 := by norm_num [cD, cprime, hPdef]
  have hsq : √(discr P.β (cD P (1 / 100))) = 7 / 4 := by
    rw [hc, show discr P.β (3 / 4) = (7 / 4) ^ 2 by norm_num [discr, hPdef]]
    exact Real.sqrt_sq (by norm_num)
  have h1 : mu1 P.β (cD P (1 / 100)) = 1 / 2 := by
    unfold mu1; rw [hsq, hc]; norm_num [hPdef]
  have h2 : mu2 P.β (cD P (1 / 100)) = 4 := by
    unfold mu2; rw [hsq, hc]; norm_num [hPdef]
  have hD : P.α * P.β * mu2 P.β (cD P (1 / 100)) ≠ 1 := by rw [h2]; norm_num [hPdef]
  refine ⟨P, hP, by norm_num [hPdef], hD, ?_⟩
  rw [a_sub_b_eq hP hε hD, h1]
  norm_num [hPdef]

end Woodford.PolicyResponseDynamics.Prop51
