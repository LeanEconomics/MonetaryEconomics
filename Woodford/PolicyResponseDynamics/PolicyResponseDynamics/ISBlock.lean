/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PolicyResponseDynamics.ForwardSolution
import PolicyResponseDynamics.InvestmentModel
import PolicyResponseDynamics.ForwardSystems
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# The IS block of the investment model

Woodford (2003), *Interest and Prices*, Chapter 5, §3.3, pp. 362–368, and §3.3's one-period-delay
variant, p. 370.

The "IS block" (3.7)–(3.10) of the model with endogenous capital is taken from the
linearisation as given, with its coefficients as parameters (`Par`): (3.7) is `CapitalEuler`
(with a generic exogenous term `u_t`), (3.8) `InvestEq`, (3.9) `MUEq`, (3.10) `FisherEq`.
Everything holds for an arbitrary `ExpectationSystem`, with genuine infinite sums.

## Main results

* `capitalEuler_iff_eq320`: eliminating `Ŷ_{t+1}` with (3.8)–(3.9) turns (3.7) into (3.20),
  `a₀ E_t K̂_{t+2} − a₁ K̂_{t+1} + a₂ K̂_t = λ̂_t − b₀ E_t λ̂_{t+1} + z_t`, with explicit
  `a₀ = βε_ψ + c'ρ_y k`, `a₁ = ε_ψ(1+β) + c'ρ_k + c'ρ_y k(1−δ)`, `a₂ = ε_ψ`,
  `b₀ = β(1−δ) − c'ρ_yσ`, `c' = 1 − β(1−δ)`.
* `Par.roots_iff`: "for empirically realistic parameter values" `0 < μ̃₁ < 1 < μ̃₂` is exactly
  `ρ_y k δ < ρ_k` (`p(0) = ε_ψ`, `p(1) = c'(ρ_y kδ − ρ_k)`; survey error 13).
* `secondOrder_iff`, `secondOrder_existsUnique`: the unique bounded solution of (3.20) is
  `K̂_{t+1} = μ̃₁K̂_t + w_t`, `w_t = −(a₀μ̃₂)⁻¹∑_j μ̃₂^{−j}E_t f_{t+j}`.
* `lam_iterate`, `eq321_iff`: (3.21), with the exact convergence condition `E_t λ̂_{t+N} → λ̂_∞`.
* `series_rep`, `capital_rep`, `eq322`: (3.22) with explicit
  `χ̃_j = [1 + (μ̃₂⁻¹ − b₀)(1 − μ̃₂^{−j})/(1 − μ̃₂⁻¹)]/(a₀μ̃₂)` and `e^k_t`; `eq323`: (3.23) with
  `χ_j = σ + kχ̃_j`, `N = k[μ̃₁ − (1 − δ)]`, `e^y_t = k e^k_t + g_t`.
* `longrun_lam`, `longrun_solve`, `longrun_s`, `longrun_pi`: the long-run relations of p. 365;
  `longrun_lam_not_from_38_39`: the first comes from (3.7), not "(3.8) and (3.9)" (error 10).
* `N_pos_iff`: fn. 34, `N > 0 ↔ ε_ψ > ρ_k(1 − δ)/δ`, exact.
* `firstOrder_iff`, `output_firstOrder`, `eq323_const`, `chi_const`: p. 367 — when
  `B(L) = −h(1 − μ̃₂L)` (`Par.B_form_iff`), (3.20) is `K̂_{t+1} = μ̃₁K̂_t − hλ̂_t` and every
  `χ_j = σ + k h` (survey error 3: the book prints `σ + h`); `printed_chi_counterexample`
  (and its calibrated instance) refutes `σ + h`. `coincide_iff`: the coincidence happens
  exactly at `ε_ψ = ε_ψ*` (closed form `epsStar`).
* Calibration (`calib12`: `δ = 0.012` as printed, `k ≈ 9.876`; `calib10`: `k = 10`):
  `crit_values` (fn. 34 critical value `≈ 111.70` resp. `≈ 114.34`, printed 114.5),
  `N_calib12`, `N_calib10` (`N ≈ −1.2338` resp. `−1.2482`, printed −1.246), `epsStar_values`
  (`ε_ψ* ≈ 3.109` resp. `3.181`, printed 3.23), `chi_values` (`σ + kh ∈ (3.73, 3.74)`, "a bit
  less than 4"; `σ + h ∈ (1.27, 1.28)`).
* `eq324`, `eq325`, `eq326_iff`: the one-period-delay versions (3.24)–(3.26), same
  coefficients.
-/

namespace Woodford.PolicyResponseDynamics.ISBlock

open Filter Topology ForwardSystems

/-! ### Parameters and the derived coefficients of (3.20) -/

/-- Woodford (2003), §3.1–3.3, pp. 355–367: the parameters of the IS block — the discount
factor `β`, depreciation `δ`, the adjustment-cost parameter `ε_ψ` (`eps`), the elasticities
`ρ_y`, `ρ_k` of the marginal valuation of capital (3.7), the capital–output ratio `k = K̄/Ȳ`
(3.8) and the expenditure elasticity `σ` (3.9). -/
structure Par where
  β : ℝ
  δ : ℝ
  eps : ℝ
  ρy : ℝ
  ρk : ℝ
  k : ℝ
  σ : ℝ

namespace Par

/-- Woodford (2003), eq. (3.7), p. 356: `c' = 1 − β(1 − δ)`, the weight on the marginal
valuation of capital. -/
def cp (P : Par) : ℝ := 1 - P.β * (1 - P.δ)

/-- Woodford (2003), eq. (3.20), p. 365: the coefficient of `E_t K̂_{t+2}` in (3.20),
`a₀ = β ε_ψ + c' ρ_y k`. -/
def a0 (P : Par) : ℝ := P.β * P.eps + P.cp * P.ρy * P.k

/-- Woodford (2003), eq. (3.20), p. 365: minus the coefficient of `K̂_{t+1}` in (3.20),
`a₁ = ε_ψ (1 + β) + c' ρ_k + c' ρ_y k (1 − δ)`. -/
def a1 (P : Par) : ℝ :=
  P.eps * (1 + P.β) + P.cp * P.ρk + P.cp * P.ρy * P.k * (1 - P.δ)

/-- Woodford (2003), eq. (3.20), p. 365: the coefficient of `K̂_t` in (3.20), `a₂ = ε_ψ`. -/
def a2 (P : Par) : ℝ := P.eps

/-- Woodford (2003), eq. (3.20), p. 365: `B(L) λ̂_{t+1} = (λ̂_t − b₀ λ̂_{t+1})/a₀` with
`b₀ = β(1 − δ) − c' ρ_y σ`. -/
def b0 (P : Par) : ℝ := P.β * (1 - P.δ) - P.cp * P.ρy * P.σ

/-- Woodford (2003), eq. (3.20), p. 365: the characteristic polynomial of `A(L)`,
`p(μ) = a₀ μ² − a₁ μ + a₂`; `A(L) = a₀ (1 − μ̃₁ L)(1 − μ̃₂ L)` iff `μ̃₁, μ̃₂` are its roots. -/
def poly (P : Par) (μ : ℝ) : ℝ := P.a0 * μ ^ 2 - P.a1 * μ + P.a2

/-- Woodford (2003), eq. (3.23), p. 366: `N = k[μ̃₁ − (1 − δ)]`. -/
def N (P : Par) (μ1 : ℝ) : ℝ := P.k * (μ1 - (1 - P.δ))

/-- Woodford (2003), p. 365: `p(0) = ε_ψ`. -/
theorem poly_zero (P : Par) : P.poly 0 = P.eps := by
  simp [poly, a2]

/-- Woodford (2003), p. 365 (survey): `p(1) = c'(ρ_y k δ − ρ_k)`. -/
theorem poly_one (P : Par) : P.poly 1 = P.cp * (P.ρy * P.k * P.δ - P.ρk) := by
  simp only [poly, a0, a1, a2, cp]; ring

/-- Woodford (2003), fn. 34, p. 368: `p(1 − δ) = c'[ε_ψ δ − ρ_k (1 − δ)]`. -/
theorem poly_one_sub_delta (P : Par) :
    P.poly (1 - P.δ) = P.cp * (P.eps * P.δ - P.ρk * (1 - P.δ)) := by
  simp only [poly, a0, a1, a2, cp]; ring

/-- Woodford (2003), p. 367: `p` is affine in `ε_ψ`:
`p(x) = ε_ψ (βx − 1)(x − 1) + c' x (ρ_y k x − ρ_k − ρ_y k (1 − δ))`. -/
theorem poly_eq (P : Par) (x : ℝ) : P.poly x =
    P.eps * ((P.β * x - 1) * (x - 1)) +
      P.cp * x * (P.ρy * P.k * x - P.ρk - P.ρy * P.k * (1 - P.δ)) := by
  simp only [poly, a0, a1, a2, cp]; ring

/-- Woodford (2003), (3.20), p. 365: `1 − b₀ = c'(1 + ρ_y σ)`. -/
theorem one_sub_b0 (P : Par) : 1 - P.b0 = P.cp * (1 + P.ρy * P.σ) := by
  simp only [b0, cp]; ring

end Par

/-! ### Equations (3.7)–(3.10) and the derivation of (3.20) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), eq. (3.7), p. 356, as supplied by the linearisation chain: the aggregate
capital Euler equation
`λ̂_t + ε_ψ(K̂_{t+1} − K̂_t) = β(1−δ) E_t λ̂_{t+1} + c'[ρ_y E_t Ŷ_{t+1} − ρ_k K̂_{t+1}]
  + β ε_ψ (E_t K̂_{t+2} − K̂_{t+1}) + u_t`.
The exogenous term `u_t` stands for the book's `−c' ω q_t` (which, by survey error 5, should be
`−c' ω E_t q_{t+1}`); nothing below depends on its form. -/
def CapitalEuler (P : Par) (lam Y K u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, lam t + P.eps • (K (t + 1) - K t) =
    (P.β * (1 - P.δ)) • 𝔼.E t (lam (t + 1)) +
      P.cp • (P.ρy • 𝔼.E t (Y (t + 1)) - P.ρk • K (t + 1)) +
      (P.β * P.eps) • (𝔼.E t (K (t + 2)) - K (t + 1)) + u t

/-- Woodford (2003), eq. (3.8), p. 357: `Î_t = k[K̂_{t+1} − (1 − δ)K̂_t]`. -/
def InvestEq (P : Par) (I K : ℕ → Ω → ℝ) : Prop :=
  ∀ t, I t = P.k • (K (t + 1) - (1 - P.δ) • K t)

/-- Woodford (2003), eq. (3.9), p. 357: `λ̂_t = −σ⁻¹(Ŷ_t − Î_t − g_t)`. -/
def MUEq (P : Par) (lam Y I g : ℕ → Ω → ℝ) : Prop :=
  ∀ t, lam t = -P.σ⁻¹ • (Y t - I t - g t)

/-- Woodford (2003), eq. (3.10), p. 357: `ı̂_t = E_t π_{t+1} + λ̂_t − E_t λ̂_{t+1}`. -/
def FisherEq (lam i π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = 𝔼.E t (π (t + 1)) + lam t - 𝔼.E t (lam (t + 1))

/-- Woodford (2003), p. 357: the capital stock `K̂_{t+1}` is chosen at date `t`. -/
def Predetermined (K : ℕ → Ω → ℝ) : Prop := ∀ t, 𝔼.E t (K (t + 1)) = K (t + 1)

/-- Woodford (2003), eq. (3.20), p. 365: the disturbance `z_t = −c' ρ_y E_t g_{t+1} − u_t`. -/
def zOf (P : Par) (g u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  -(P.cp * P.ρy) • 𝔼.E t (g (t + 1)) - u t

/-- Woodford (2003), eq. (3.20), p. 365, written out:
`a₀ E_t K̂_{t+2} − a₁ K̂_{t+1} + a₂ K̂_t = λ̂_t − b₀ E_t λ̂_{t+1} + z_t`,
i.e. `E_t[A(L) K̂_{t+2}] = E_t[B(L) λ̂_{t+1}] + z_t/a₀` after dividing by `a₀`. -/
def Eq320 (P : Par) (K lam z : ℕ → Ω → ℝ) : Prop :=
  ∀ t, P.a0 • 𝔼.E t (K (t + 2)) - P.a1 • K (t + 1) + P.a2 • K t =
    lam t - P.b0 • 𝔼.E t (lam (t + 1)) + z t

/-- Woodford (2003), eq. (3.9), p. 357: with `σ ≠ 0`, (3.9) reads `Ŷ_t = Î_t + g_t − σ λ̂_t`. -/
theorem output_eq {P : Par} (hσ : P.σ ≠ 0) {lam Y I g : ℕ → Ω → ℝ} (h39 : MUEq P lam Y I g)
    (t : ℕ) : Y t = I t + g t - P.σ • lam t := by
  funext ω
  have h := congrFun (h39 t) ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
  rw [h]
  field_simp
  ring

/-- Woodford (2003), p. 365: "Using (3.8) and (3.9) to eliminate `Ŷ_{t+1}` from (3.7) yields
(3.20)." Given (3.8), (3.9) and a predetermined capital stock, (3.7) holds at every date if and
only if (3.20) does, with the coefficients `a₀, a₁, a₂, b₀` and disturbance `z_t` above. -/
theorem capitalEuler_iff_eq320 {P : Par} (hσ : P.σ ≠ 0) {lam Y I K g u : ℕ → Ω → ℝ}
    (hK : Predetermined 𝔼 K) (h38 : InvestEq P I K) (h39 : MUEq P lam Y I g) :
    CapitalEuler 𝔼 P lam Y K u ↔ Eq320 𝔼 P K lam (zOf 𝔼 P g u) := by
  have hEY : ∀ t, 𝔼.E t (Y (t + 1)) = P.k • (𝔼.E t (K (t + 2)) - (1 - P.δ) • K (t + 1)) +
      𝔼.E t (g (t + 1)) - P.σ • 𝔼.E t (lam (t + 1)) := by
    intro t
    rw [output_eq hσ h39, h38 (t + 1)]
    simp only [map_add, map_sub, map_smul, hK t]
  constructor
  · intro h t
    have h1 := h t
    rw [hEY t] at h1
    funext ω
    have h2 := congrFun h1 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zOf,
      neg_mul] at h2 ⊢
    simp only [Par.a0, Par.a1, Par.a2, Par.b0]
    linear_combination -h2
  · intro h t
    rw [hEY t]
    funext ω
    have h2 := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zOf,
      neg_mul] at h2 ⊢
    simp only [Par.a0, Par.a1, Par.a2, Par.b0] at h2
    linear_combination -h2

/-! ### Root location of `A(L)` (p. 365) -/

namespace Par

/-- Woodford (2003), p. 365: if `p(μ) = a₀(μ − μ̃₁)(μ − μ̃₂)` then `a₁ = a₀(μ̃₁ + μ̃₂)` and
`a₂ = a₀ μ̃₁ μ̃₂`, i.e. `A(L) = a₀(1 − μ̃₁L)(1 − μ̃₂L)`. -/
theorem coeffs_of_factor {P : Par} {μ1 μ2 : ℝ}
    (h : ∀ μ, P.poly μ = P.a0 * (μ - μ1) * (μ - μ2)) :
    P.a1 = P.a0 * (μ1 + μ2) ∧ P.a2 = P.a0 * μ1 * μ2 := by
  have h0 := h 0
  have h1 := h 1
  simp only [poly] at h0 h1
  constructor
  · linear_combination h0 - h1
  · linear_combination h0

/-- Woodford (2003), p. 365, "for empirically realistic parameter values, the polynomial `A(L)`
can be factored as `(1 − μ̃₁L)(1 − μ̃₂L)` with `0 < μ̃₁ < 1 < μ̃₂`" — made exact (survey error
13): given `ε_ψ > 0`, `c' > 0` and `a₀ > 0`, the factorisation with this root location exists
if and only if `ρ_y k δ < ρ_k`. -/
theorem roots_iff (P : Par) (heps : 0 < P.eps) (hcp : 0 < P.cp) (ha0 : 0 < P.a0) :
    (∃ μ1 μ2 : ℝ, 0 < μ1 ∧ μ1 < 1 ∧ 1 < μ2 ∧ ∀ μ, P.poly μ = P.a0 * (μ - μ1) * (μ - μ2)) ↔
      P.ρy * P.k * P.δ < P.ρk := by
  constructor
  · rintro ⟨μ1, μ2, -, h1, h2, h⟩
    have hp := h 1
    rw [poly_one] at hp
    have hneg : P.a0 * (1 - μ1) * (1 - μ2) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos ha0 (by linarith)) (by linarith)
    by_contra hc
    push Not at hc
    have : 0 ≤ P.cp * (P.ρy * P.k * P.δ - P.ρk) := mul_nonneg hcp.le (by linarith)
    linarith
  · intro hlt
    have hp1 : P.poly 1 < 0 := by
      rw [poly_one]; exact mul_neg_of_pos_of_neg hcp (by linarith)
    set D : ℝ := P.a1 ^ 2 - 4 * P.a0 * P.a2 with hD
    have hDid : D = (2 * P.a0 - P.a1) ^ 2 - 4 * P.a0 * P.poly 1 := by
      simp only [hD, poly]; ring
    have hDpos : 0 < D := by
      rw [hDid]; nlinarith [sq_nonneg (2 * P.a0 - P.a1)]
    set s : ℝ := Real.sqrt D with hs
    have hs2 : s ^ 2 = D := Real.sq_sqrt hDpos.le
    have hspos : 0 < s := Real.sqrt_pos.mpr hDpos
    set μ1 : ℝ := (P.a1 - s) / (2 * P.a0) with hμ1
    set μ2 : ℝ := (P.a1 + s) / (2 * P.a0) with hμ2
    have hfac : ∀ μ, P.poly μ = P.a0 * (μ - μ1) * (μ - μ2) := by
      intro μ
      simp only [poly, hμ1, hμ2]
      field_simp
      linear_combination hs2 + hD
    have hlt12 : μ1 < μ2 := by
      rw [hμ1, hμ2]
      exact div_lt_div_of_pos_right (by linarith) (by linarith)
    have hprod1 : P.a0 * (1 - μ1) * (1 - μ2) < 0 := by rw [← hfac]; exact hp1
    have hprod0 : P.a0 * (0 - μ1) * (0 - μ2) = P.eps := by rw [← hfac, poly_zero]
    have hA : μ1 < 1 ∧ 1 < μ2 := by
      by_contra hc
      rcases not_and_or.mp hc with h | h
      · push Not at h
        have : 0 ≤ P.a0 * (1 - μ1) * (1 - μ2) :=
          mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos ha0.le (by linarith))
            (by linarith)
        linarith
      · push Not at h
        have : 0 ≤ P.a0 * (1 - μ1) * (1 - μ2) :=
          mul_nonneg (mul_nonneg ha0.le (by linarith)) (by linarith)
        linarith
    have hpos1 : 0 < μ1 := by
      have h3 : 0 < P.a0 * μ2 * μ1 := by nlinarith
      have h4 : 0 < P.a0 * μ2 := mul_pos ha0 (by linarith)
      exact pos_of_mul_pos_right h3 h4.le
    exact ⟨μ1, μ2, hpos1, hA.1, hA.2, hfac⟩

/-- Woodford (2003), p. 365: with the factorisation, for `x < μ̃₂` the sign of `p(x)` locates
`x` relative to `μ̃₁`: `p(x) > 0 ↔ x < μ̃₁` (used to bracket the calibrated roots). -/
theorem poly_pos_iff_lt {P : Par} {μ1 μ2 x : ℝ} (ha0 : 0 < P.a0)
    (h : ∀ μ, P.poly μ = P.a0 * (μ - μ1) * (μ - μ2)) (hx : x < μ2) :
    0 < P.poly x ↔ x < μ1 := by
  rw [h]
  constructor
  · intro hp
    by_contra hc
    push Not at hc
    have : P.a0 * (x - μ1) * (x - μ2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha0.le (by linarith)) (by linarith)
    linarith
  · intro hxl
    exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg ha0 (by linarith)) (by linarith)

/-- Woodford (2003), p. 365: with the factorisation, for `μ̃₁ < x < μ̃₂` the polynomial is
negative. -/
theorem poly_neg_of_between {P : Par} {μ1 μ2 x : ℝ} (ha0 : 0 < P.a0)
    (h : ∀ μ, P.poly μ = P.a0 * (μ - μ1) * (μ - μ2)) (h1 : μ1 < x) (h2 : x < μ2) :
    P.poly x < 0 := by
  rw [h]
  exact mul_neg_of_pos_of_neg (mul_pos ha0 (by linarith)) (by linarith)

end Par

/-! ### The second-order forward equation behind (3.20)–(3.22)

The forward part `wSol` and the path `path` are in `ForwardSystems`. -/

/-- Woodford (2003), p. 365, "there is a unique bounded solution for `K̂_{t+1}` as a linear
function of `K̂_t` and the expectations `E_t f_{t+j}`": for `A(L) = a₀(1 − μ₁L)(1 − μ₂L)` with
`|μ₂| > 1`, a bounded predetermined process `x` solves
`a₀ E_t x_{t+2} − a₁ x_{t+1} + a₂ x_t = f_t` (bounded adapted `f`) if and only if
`x_{t+1} = μ₁ x_t + w_t` at every date (`ForwardSystems.secondOrder_forward_iff`). -/
theorem secondOrder_iff {a0 a1 a2 μ1 μ2 : ℝ} (ha0 : a0 ≠ 0) (h1 : a1 = a0 * (μ1 + μ2))
    (h2 : a2 = a0 * μ1 * μ2) (hμ2 : 1 < |μ2|) {x f : ℕ → Ω → ℝ} {M : ℝ}
    (hf : ∀ t ω, |f t ω| ≤ M) (hfa : 𝔼.Adapted f) (hx : Predetermined 𝔼 x)
    (hxb : BoundedProc x) :
    (∀ t, a0 • 𝔼.E t (x (t + 2)) - a1 • x (t + 1) + a2 • x t = f t) ↔
      ∀ t, x (t + 1) = μ1 • x t + wSol 𝔼 a0 μ2 f t :=
  ForwardSystems.secondOrder_forward_iff 𝔼 ha0 h1 h2 hμ2 hf hfa hx hxb

/-- Woodford (2003), p. 365 ("there is a unique bounded solution for `K̂_{t+1}` as a linear
function of `K̂_t`, the expectations `E_t λ̂_{t+j}` and `E_t z_{t+j}`"): for
`A(L) = a₀(1 − μ₁L)(1 − μ₂L)` with `|μ₁| < 1 < |μ₂|`, bounded adapted forcing `f` and a bounded
initial stock `x₀` known at date 0, there is exactly one bounded predetermined solution of
`a₀ E_t x_{t+2} − a₁ x_{t+1} + a₂ x_t = f_t` starting from `x₀`: the path
`x_{t+1} = μ₁ x_t + w_t` (`ForwardSystems.secondOrder_forward_existsUnique`). -/
theorem secondOrder_existsUnique {a0 a1 a2 μ1 μ2 : ℝ} (ha0 : a0 ≠ 0) (h1 : a1 = a0 * (μ1 + μ2))
    (h2 : a2 = a0 * μ1 * μ2) (hμ1 : |μ1| < 1) (hμ2 : 1 < |μ2|) {f : ℕ → Ω → ℝ} {M B0 : ℝ}
    (hf : ∀ t ω, |f t ω| ≤ M) (hfa : 𝔼.Adapted f) {x0 : Ω → ℝ} (hx0 : 𝔼.E 0 x0 = x0)
    (hx0b : ∀ ω, |x0 ω| ≤ B0) :
    ∃! x : ℕ → Ω → ℝ, x 0 = x0 ∧ Predetermined 𝔼 x ∧ BoundedProc x ∧
      ∀ t, a0 • 𝔼.E t (x (t + 2)) - a1 • x (t + 1) + a2 • x t = f t :=
  ForwardSystems.secondOrder_forward_existsUnique 𝔼 ha0 h1 h2 hμ1 hμ2 hf hfa hx0 hx0b

/-! ### Equation (3.21): solving (3.10) forward -/

/-- Woodford (2003), eq. (3.10), p. 357: (3.10) is the bond-pricing relation of p. 325,
`ı̂_t = λ̂_t + E_t[π_{t+1} − λ̂_{t+1}]`. -/
theorem fisherEq_bond {lam i π : ℕ → Ω → ℝ} (hF : FisherEq 𝔼 lam i π) (t : ℕ) :
    i t = lam t + 𝔼.E t (π (t + 1) - lam (t + 1)) := by
  rw [hF t, map_sub]; abel

/-- Woodford (2003), eq. (3.10), p. 357, conditioned on date-`s` information (`s ≤ t`):
`E_s λ̂_t = E_s(ı̂_t − π_{t+1}) + E_s λ̂_{t+1}`. -/
theorem lam_step {lam i π : ℕ → Ω → ℝ} (hF : FisherEq 𝔼 lam i π) {s t : ℕ} (hst : s ≤ t) :
    𝔼.E s (lam t) = 𝔼.E s (i t - π (t + 1)) + 𝔼.E s (lam (t + 1)) := by
  have h : lam t = i t - 𝔼.E t (π (t + 1)) + 𝔼.E t (lam (t + 1)) := by
    rw [hF t]; abel
  conv_lhs => rw [h]
  rw [map_add, map_sub, map_sub, 𝔼.tower hst, 𝔼.tower hst]

/-- Woodford (2003), eq. (3.21), p. 365 (finite form): iterating (3.10),
`E_s λ̂_t = ∑_{j<N} E_s(ı̂_{t+j} − π_{t+j+1}) + E_s λ̂_{t+N}` for `s ≤ t`. -/
theorem lam_iterate {lam i π : ℕ → Ω → ℝ} (hF : FisherEq 𝔼 lam i π) {s t : ℕ} (hst : s ≤ t)
    (N : ℕ) : 𝔼.E s (lam t) =
      ∑ j ∈ Finset.range N, 𝔼.E s (i (t + j) - π (t + j + 1)) + 𝔼.E s (lam (t + N)) := by
  rw [add_comm]
  exact ForwardSystems.unitRoot_iterate 𝔼 (fisherEq_bond 𝔼 hF) hst N

/-- Woodford (2003), eq. (3.21), p. 365: `λ̂_t = λ̂_∞ + ∑_{j ≥ 0} E_t(ı̂_{t+j} − π_{t+j+1})`
(conditioned on date `s ≤ t`), the series converging exactly when the expected marginal utility
`E_s λ̂_{t+N}` converges to the long-run value `λ̂_∞` (`ForwardSystems.unitRoot_forward_iff`).
The sum is a limit of partial sums (it need not converge absolutely). -/
theorem eq321_iff {lam i π : ℕ → Ω → ℝ} (hF : FisherEq 𝔼 lam i π) {s t : ℕ} (hst : s ≤ t)
    (ω : Ω) (lamInf : ℝ) :
    Tendsto (fun N => ∑ j ∈ Finset.range N, 𝔼.E s (i (t + j) - π (t + j + 1)) ω) atTop
        (𝓝 (𝔼.E s (lam t) ω - lamInf)) ↔
      Tendsto (fun N => 𝔼.E s (lam (t + N)) ω) atTop (𝓝 lamInf) :=
  ForwardSystems.unitRoot_forward_iff 𝔼 (fisherEq_bond 𝔼 hF) hst lamInf ω

/-! ### Equation (3.22): the capital-stock solution -/

/-- Woodford (2003), eq. (3.22), p. 366: the coefficients
`χ̃_j = [1 + (μ̃₂⁻¹ − b₀)(1 − μ̃₂^{−j})/(1 − μ̃₂⁻¹)]/(a₀ μ̃₂)` of the real-rate expectations. -/
noncomputable def chiTilde (a0 μ2 b0 : ℝ) (j : ℕ) : ℝ :=
  (1 + (μ2⁻¹ - b0) * (1 - μ2⁻¹ ^ j) / (1 - μ2⁻¹)) / (a0 * μ2)

/-- Woodford (2003), eq. (3.23), p. 366: the coefficients `χ_j = σ + k χ̃_j`. -/
noncomputable def chi (P : Par) (μ2 : ℝ) (j : ℕ) : ℝ := P.σ + P.k * chiTilde P.a0 μ2 P.b0 j

/-- Woodford (2003), pp. 365–366 (the series step behind (3.22)): if `L_j = R_j + L_{j+1}`,
`L` is bounded and `L_j → λ_∞`, then for `|μ| < 1`
`∑_m [1 + (μ − b₀)(1 − μᵐ)/(1 − μ)] R_m = ∑_j μʲ (L_j − b₀ L_{j+1}) − (1 − b₀)λ_∞/(1 − μ)`,
the left side converging as a limit of partial sums. -/
theorem series_rep {μ b0 lamInf B : ℝ} (hμ : |μ| < 1) {L R : ℕ → ℝ} (hL : ∀ j, |L j| ≤ B)
    (hLR : ∀ j, L j = R j + L (j + 1)) (hlim : Tendsto L atTop (𝓝 lamInf)) :
    Summable (fun j => μ ^ j * (L j - b0 * L (j + 1))) ∧
      Tendsto (fun N => ∑ m ∈ Finset.range N, (1 + (μ - b0) * (1 - μ ^ m) / (1 - μ)) * R m)
        atTop (𝓝 (∑' j, μ ^ j * (L j - b0 * L (j + 1)) - (1 - b0) * lamInf / (1 - μ))) := by
  have h1μ : 1 - μ ≠ 0 := by
    intro h
    have : μ = 1 := by linarith
    rw [this, abs_one] at hμ
    exact lt_irrefl _ hμ
  have hgeo : Summable (fun j : ℕ => |μ| ^ j * B) :=
    (summable_geometric_of_lt_one (abs_nonneg μ) hμ).mul_right B
  have hS0 : Summable (fun j => μ ^ j * L j) :=
    Summable.of_norm_bounded hgeo (fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hL j) (pow_nonneg (abs_nonneg _) _))
  have hS1 : Summable (fun j => μ ^ j * L (j + 1)) :=
    Summable.of_norm_bounded hgeo (fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hL (j + 1)) (pow_nonneg (abs_nonneg _) _))
  have hR : ∀ m, R m = L m - L (m + 1) := fun m => by linarith [hLR m]
  have hSR : Summable (fun m => μ ^ m * R m) :=
    (hS0.sub hS1).congr (fun m => by rw [hR m]; ring)
  have hT : Summable (fun j => μ ^ j * (L j - b0 * L (j + 1))) :=
    (hS0.sub (hS1.mul_left b0)).congr (fun j => by ring)
  refine ⟨hT, ?_⟩
  have hpart : ∀ N, ∑ m ∈ Finset.range N, (1 + (μ - b0) * (1 - μ ^ m) / (1 - μ)) * R m =
      (1 - b0) / (1 - μ) * (L 0 - L N) -
        (μ - b0) / (1 - μ) * ∑ m ∈ Finset.range N, μ ^ m * R m := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, hR N]
      field_simp
      ring
  have hval : ∑' j, μ ^ j * (L j - b0 * L (j + 1)) =
      (1 - b0) / (1 - μ) * L 0 - (μ - b0) / (1 - μ) * ∑' m, μ ^ m * R m := by
    have e0 : ∑' j, μ ^ j * L j = L 0 + μ * ∑' j, μ ^ j * L (j + 1) := by
      rw [hS0.tsum_eq_zero_add, ← tsum_mul_left]
      simp only [pow_zero, one_mul]
      congr 1
      exact tsum_congr fun j => by ring
    have e1 : ∑' m, μ ^ m * R m = ∑' j, μ ^ j * L j - ∑' j, μ ^ j * L (j + 1) := by
      rw [← hS0.tsum_sub hS1]
      exact tsum_congr fun m => by rw [hR m]; ring
    have e2 : ∑' j, μ ^ j * (L j - b0 * L (j + 1)) =
        ∑' j, μ ^ j * L j - b0 * ∑' j, μ ^ j * L (j + 1) := by
      rw [← tsum_mul_left, ← hS0.tsum_sub (hS1.mul_left b0)]
      exact tsum_congr fun j => by ring
    rw [e2, e1, e0]
    field_simp
    ring
  have hlimR : Tendsto (fun N => ∑ m ∈ Finset.range N, μ ^ m * R m) atTop
      (𝓝 (∑' m, μ ^ m * R m)) := hSR.hasSum.tendsto_sum_nat
  have hlim2 := ((tendsto_const_nhds (x := L 0)).sub hlim).const_mul ((1 - b0) / (1 - μ))
  have hlim3 := hlim2.sub (hlimR.const_mul ((μ - b0) / (1 - μ)))
  simp_rw [hpart]
  convert hlim3 using 2
  rw [hval]
  field_simp
  ring

/-- Woodford (2003), eq. (3.22), p. 366 (the real-number core): if
`K_{t+1} = μ₁ K_t + ∑_j μ₂^{−j}(−(a₀μ₂)⁻¹)(L_j − b₀L_{j+1} + Z_j)` and the long-run values
satisfy `a₀(1 − μ₁)(1 − μ₂)K_∞ = (1 − b₀)λ_∞` (the steady state of (3.20)), then
`∑_j χ̃_j R_j = (1 − μ₁)K_∞ + μ₁K_t − (a₀μ₂)⁻¹ ∑_j μ₂^{−j} Z_j − K_{t+1}`. -/
theorem capital_rep {a0 μ1 μ2 b0 lamInf Kinf Kt Kt1 B : ℝ} {L R Z : ℕ → ℝ} (ha0 : a0 ≠ 0)
    (hμ2 : 1 < μ2) (hL : ∀ j, |L j| ≤ B) (hLR : ∀ j, L j = R j + L (j + 1))
    (hlim : Tendsto L atTop (𝓝 lamInf)) (hZ : Summable (fun j => μ2⁻¹ ^ j * Z j))
    (hK : Kt1 = μ1 * Kt + ∑' j, μ2⁻¹ ^ j * (-(a0 * μ2)⁻¹ * (L j - b0 * L (j + 1) + Z j)))
    (hKinf : a0 * (1 - μ1) * (1 - μ2) * Kinf = (1 - b0) * lamInf) :
    Tendsto (fun N => ∑ j ∈ Finset.range N, chiTilde a0 μ2 b0 j * R j) atTop
      (𝓝 ((1 - μ1) * Kinf + μ1 * Kt + -(a0 * μ2)⁻¹ * ∑' j, μ2⁻¹ ^ j * Z j - Kt1)) := by
  have hμ0 : μ2 ≠ 0 := by positivity
  have hq : |μ2⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith)]; exact inv_lt_one_of_one_lt₀ hμ2
  obtain ⟨hT, hlimS⟩ := series_rep (b0 := b0) hq hL hLR hlim
  have hsplit : ∑' j, μ2⁻¹ ^ j * (-(a0 * μ2)⁻¹ * (L j - b0 * L (j + 1) + Z j)) =
      -(a0 * μ2)⁻¹ * (∑' j, μ2⁻¹ ^ j * (L j - b0 * L (j + 1)) + ∑' j, μ2⁻¹ ^ j * Z j) := by
    rw [← hT.tsum_add hZ, ← tsum_mul_left]
    exact tsum_congr fun j => by ring
  have hsum : ∀ N, ∑ j ∈ Finset.range N, chiTilde a0 μ2 b0 j * R j =
      (a0 * μ2)⁻¹ * ∑ m ∈ Finset.range N, (1 + (μ2⁻¹ - b0) * (1 - μ2⁻¹ ^ m) / (1 - μ2⁻¹)) *
        R m := by
    intro N
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp only [chiTilde]; ring
  simp_rw [hsum]
  convert hlimS.const_mul (a0 * μ2)⁻¹ using 2
  rw [hK, hsplit]
  have hμ1' : μ2 - 1 ≠ 0 := by linarith
  have e : (1 - b0) * lamInf / (1 - μ2⁻¹) = a0 * (1 - μ1) * (1 - μ2) * Kinf * μ2 / (μ2 - 1) := by
    rw [hKinf]; field_simp
  rw [e]
  field_simp
  ring

/-- Woodford (2003), p. 365: the forcing of (3.20), `f_t = λ̂_t − b₀ E_t λ̂_{t+1} + z_t`. -/
def forcing320 (b0 : ℝ) (lam z : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  lam t - b0 • 𝔼.E t (lam (t + 1)) + z t

/-- Woodford (2003), p. 365: the forcing of (3.20) is adapted when `λ̂` and `z` are. -/
theorem forcing320_adapted {b0 : ℝ} {lam z : ℕ → Ω → ℝ} (hl : 𝔼.Adapted lam)
    (hz : 𝔼.Adapted z) : 𝔼.Adapted (forcing320 𝔼 b0 lam z) := fun t => by
  simp only [forcing320, map_add, map_sub, map_smul, 𝔼.E_E_self, hl t, hz t]

/-- Woodford (2003), p. 365: the forcing of (3.20) is bounded when `λ̂` and `z` are. -/
theorem forcing320_bounded {b0 Bl Bz : ℝ} {lam z : ℕ → Ω → ℝ} (hl : ∀ t ω, |lam t ω| ≤ Bl)
    (hz : ∀ t ω, |z t ω| ≤ Bz) (t : ℕ) (ω : Ω) :
    |forcing320 𝔼 b0 lam z t ω| ≤ Bl + |b0| * Bl + Bz := by
  simp only [forcing320, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have h1 := 𝔼.abs_E_le (hl (t + 1)) t ω
  calc |lam t ω - b0 * 𝔼.E t (lam (t + 1)) ω + z t ω|
      ≤ |lam t ω| + |b0 * 𝔼.E t (lam (t + 1)) ω| + |z t ω| := by
        have := abs_add_le (lam t ω - b0 * 𝔼.E t (lam (t + 1)) ω) (z t ω)
        have := abs_sub (lam t ω) (b0 * 𝔼.E t (lam (t + 1)) ω)
        linarith
    _ ≤ Bl + |b0| * Bl + Bz := by
        rw [abs_mul]
        exact add_le_add (add_le_add (hl t ω) (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)))
          (hz t ω)

/-- Woodford (2003), eq. (3.22), p. 366: `e^k_t = −(a₀μ̃₂)⁻¹ ∑_j μ̃₂^{−j} E_t z_{t+j}`, the
exogenous disturbance of the capital equation (a linear combination of the `E_t z_{t+j}`). -/
noncomputable def ek (a0 μ2 : ℝ) (z : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := wSol 𝔼 a0 μ2 z

/-- Woodford (2003), eq. (3.22), p. 366, in full: under (3.20) with
`A(L) = a₀(1 − μ̃₁L)(1 − μ̃₂L)`, `μ̃₂ > 1`, `a₀ > 0`, bounded predetermined capital, bounded
adapted `λ̂` and `z`, (3.10), and the long-run conditions `E_t λ̂_{t+N} → λ̂_∞`,
`p(1)K̂_∞ = (1 − b₀)λ̂_∞`,
`K̂_{t+1} = (1 − μ̃₁)K̂_∞ + μ̃₁K̂_t − ∑_{j ≥ 0} χ̃_j E_t(ı̂_{t+j} − π_{t+j+1}) + e^k_t`,
the series converging as a limit of partial sums. -/
theorem eq322 {P : Par} {μ1 μ2 : ℝ} (ha0 : 0 < P.a0) (hμ2 : 1 < μ2)
    (hfac : ∀ μ, P.poly μ = P.a0 * (μ - μ1) * (μ - μ2)) {K lam z i π : ℕ → Ω → ℝ}
    {Bl Bz lamInf Kinf : ℝ} (hK : Predetermined 𝔼 K) (hKb : BoundedProc K)
    (hl : ∀ t ω, |lam t ω| ≤ Bl) (hla : 𝔼.Adapted lam) (hz : ∀ t ω, |z t ω| ≤ Bz)
    (hza : 𝔼.Adapted z) (h320 : Eq320 𝔼 P K lam z) (hF : FisherEq 𝔼 lam i π)
    (hlim : ∀ t ω, Tendsto (fun N => 𝔼.E t (lam (t + N)) ω) atTop (𝓝 lamInf))
    (hKinf : P.poly 1 * Kinf = (1 - P.b0) * lamInf) (t : ℕ) (ω : Ω) :
    Tendsto (fun N => ∑ j ∈ Finset.range N,
        chiTilde P.a0 μ2 P.b0 j * 𝔼.E t (i (t + j) - π (t + j + 1)) ω) atTop
      (𝓝 ((1 - μ1) * Kinf + μ1 * K t ω + ek 𝔼 P.a0 μ2 z t ω - K (t + 1) ω)) := by
  obtain ⟨h1, h2⟩ := Par.coeffs_of_factor hfac
  have hμ2' : 1 < |μ2| := by rw [abs_of_pos (by linarith)]; exact hμ2
  have hrec := (secondOrder_iff 𝔼 ha0.ne' h1 h2 hμ2'
    (forcing320_bounded 𝔼 (b0 := P.b0) hl hz) (forcing320_adapted 𝔼 hla hza) hK hKb).mp
    (fun t => by simpa [forcing320, Par.a2] using h320 t)
  set L : ℕ → ℝ := fun j => 𝔼.E t (lam (t + j)) ω with hLdef
  set R : ℕ → ℝ := fun j => 𝔼.E t (i (t + j) - π (t + j + 1)) ω with hRdef
  set Z : ℕ → ℝ := fun j => 𝔼.E t (z (t + j)) ω with hZdef
  have hLR : ∀ j, L j = R j + L (j + 1) := fun j => by
    have := congrFun (lam_step 𝔼 hF (Nat.le_add_right t j)) ω
    simp only [Pi.add_apply] at this
    simp only [hLdef, hRdef, ← add_assoc]
    exact this
  have hLb : ∀ j, |L j| ≤ Bl := fun j => 𝔼.abs_E_le (hl (t + j)) t ω
  have hq : |μ2⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith)]; exact inv_lt_one_of_one_lt₀ hμ2
  have hZs : Summable (fun j => μ2⁻¹ ^ j * Z j) := ForwardSolution.summable_A16 𝔼 hq hz t ω
  have hEf : ∀ j, 𝔼.E t (forcing320 𝔼 P.b0 lam z (t + j)) ω = L j - P.b0 * L (j + 1) + Z j := by
    intro j
    simp only [forcing320, map_add, map_sub, map_smul, 𝔼.tower (Nat.le_add_right t j),
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hLdef, hZdef, ← add_assoc]
  have hKt : K (t + 1) ω = μ1 * K t ω +
      ∑' j, μ2⁻¹ ^ j * (-(P.a0 * μ2)⁻¹ * (L j - P.b0 * L (j + 1) + Z j)) := by
    have := congrFun (hrec t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this, wSol_apply]
    simp only [hEf]
  have hKinf' : P.a0 * (1 - μ1) * (1 - μ2) * Kinf = (1 - P.b0) * lamInf := by
    rw [← hKinf, hfac 1]
  have hek : ek 𝔼 P.a0 μ2 z t ω = -(P.a0 * μ2)⁻¹ * ∑' j, μ2⁻¹ ^ j * Z j := by
    simp only [ek, wSol_apply, hZdef, ← tsum_mul_left]
    exact tsum_congr fun j => by ring
  rw [hek]
  exact capital_rep ha0.ne' hμ2 hLb hLR (hlim t ω) hZs hKt hKinf'

/-! ### Long-run values (p. 365) -/

/-- Woodford (2003), p. 365, first long-run relation `λ̂_∞ = ρ_y Ŷ_∞ − ρ_k K̂_∞`: it is the
steady state of (3.7) (with zero disturbances), given `c' ≠ 0`. The book attributes it to
"(3.8) and (3.9)" (survey error 10). -/
theorem longrun_lam (P : Par) (hcp : P.cp ≠ 0) (lamInf Yinf Kinf : ℝ) :
    lamInf + P.eps * (Kinf - Kinf) = P.β * (1 - P.δ) * lamInf +
        P.cp * (P.ρy * Yinf - P.ρk * Kinf) + P.β * P.eps * (Kinf - Kinf) ↔
      lamInf = P.ρy * Yinf - P.ρk * Kinf := by
  constructor
  · intro h
    have h' : P.cp * lamInf = P.cp * (P.ρy * Yinf - P.ρk * Kinf) := by
      simp only [Par.cp] at h ⊢; linarith
    exact mul_left_cancel₀ hcp h'
  · intro h
    rw [h]; simp only [Par.cp]; ring

/-- Woodford (2003), p. 365 (survey error 10): (3.8) and (3.9) alone do not give the first
long-run relation: `K̂_∞ = Î_∞ = 0`, `Ŷ_∞ = 1`, `λ̂_∞ = −σ⁻¹` satisfy the long-run (3.8) and
(3.9) but not `λ̂_∞ = ρ_y Ŷ_∞ − ρ_k K̂_∞` unless `ρ_y = −σ⁻¹`. -/
theorem longrun_lam_not_from_38_39 (P : Par) (h : P.ρy ≠ -P.σ⁻¹) :
    ∃ lamInf Yinf Iinf Kinf : ℝ, Iinf = P.δ * P.k * Kinf ∧
      lamInf = -P.σ⁻¹ * (Yinf - Iinf) ∧ lamInf ≠ P.ρy * Yinf - P.ρk * Kinf :=
  ⟨-P.σ⁻¹, 1, 0, 0, by ring, by ring, by intro h'; apply h; linarith⟩

/-- Woodford (2003), p. 365: the long-run relations
`λ̂_∞ = ρ_y Ŷ_∞ − ρ_k K̂_∞`, `Î_∞ = δ k K̂_∞`, `λ̂_∞ = −σ⁻¹(Ŷ_∞ − Î_∞)` give
`Ŷ_∞ = δ k K̂_∞ − σ λ̂_∞`, `(ρ_y k δ − ρ_k) K̂_∞ = (1 + ρ_y σ) λ̂_∞` (so `Ŷ_∞, Î_∞, K̂_∞` are
multiples of `λ̂_∞` when `ρ_y k δ ≠ ρ_k`), and the steady state of (3.20),
`p(1) K̂_∞ = (1 − b₀) λ̂_∞`. -/
theorem longrun_solve (P : Par) (hσ : P.σ ≠ 0) {lamInf Yinf Iinf Kinf : ℝ}
    (h1 : lamInf = P.ρy * Yinf - P.ρk * Kinf) (h2 : Iinf = P.δ * P.k * Kinf)
    (h3 : lamInf = -P.σ⁻¹ * (Yinf - Iinf)) :
    Yinf = P.δ * P.k * Kinf - P.σ * lamInf ∧
      (P.ρy * P.k * P.δ - P.ρk) * Kinf = (1 + P.ρy * P.σ) * lamInf ∧
      P.poly 1 * Kinf = (1 - P.b0) * lamInf := by
  have hY : Yinf = P.δ * P.k * Kinf - P.σ * lamInf := by
    rw [h3, h2]; field_simp; ring
  have hK : (P.ρy * P.k * P.δ - P.ρk) * Kinf = (1 + P.ρy * P.σ) * lamInf := by
    have := h1; rw [hY] at this; linarith
  refine ⟨hY, hK, ?_⟩
  rw [Par.poly_one, Par.one_sub_b0, mul_assoc, hK]
  ring

/-- Woodford (2003), p. 365: the long-run real marginal cost: averaging (3.11) (equivalently,
(3.18) with (3.9) and zero disturbances) gives `ŝ_∞ = ω Ŷ_∞ − (ω − ν) K̂_∞ − λ̂_∞`. -/
theorem longrun_s {ω ν σ sInf lamInf Yinf Iinf Kinf : ℝ}
    (h318 : sInf = (ω + σ⁻¹) * Yinf - σ⁻¹ * Iinf - (ω - ν) * Kinf)
    (h39 : lamInf = -σ⁻¹ * (Yinf - Iinf)) :
    sInf = ω * Yinf - (ω - ν) * Kinf - lamInf := by
  rw [h318, h39]; ring

/-- Woodford (2003), p. 365: "(3.17) indicates that `π_∞ = (ξ₀ − ξ₁)/(1 − ψ₁ + ψ₂) ŝ_∞`"
(the steady state of (3.17), `InvestmentModel.Linear.longrun_inflation`). -/
theorem longrun_pi {ξ0 ξ1 ψ1 ψ2 πInf sInf : ℝ} (hden : 1 - ψ1 + ψ2 ≠ 0)
    (h317 : πInf = ξ0 * sInf - ξ1 * sInf + ψ1 * πInf - ψ2 * πInf) :
    πInf = (ξ0 - ξ1) / (1 - ψ1 + ψ2) * sInf :=
  InvestmentModel.Linear.longrun_inflation hden h317

/-! ### Equation (3.23): aggregate demand -/

/-- Woodford (2003), eq. (3.23), p. 366: the long-run output `Ŷ_∞ = δ k K̂_∞ − σ λ̂_∞`. -/
def Yinf (P : Par) (lamInf Kinf : ℝ) : ℝ := P.δ * P.k * Kinf - P.σ * lamInf

/-- Woodford (2003), eq. (3.23), p. 366, in full:
`Ŷ_t = Ŷ_∞ − N K̂_∞ + N K̂_t − ∑_{j ≥ 0} χ_j E_t(ı̂_{t+j} − π_{t+j+1}) + e^y_t` with
`N = k[μ̃₁ − (1 − δ)]`, `χ_j = σ + k χ̃_j` and `e^y_t = k e^k_t + g_t`, under the hypotheses
of (3.22) together with (3.8) and (3.9). -/
theorem eq323 {P : Par} {μ1 μ2 : ℝ} (hσ : P.σ ≠ 0) (ha0 : 0 < P.a0) (hμ2 : 1 < μ2)
    (hfac : ∀ μ, P.poly μ = P.a0 * (μ - μ1) * (μ - μ2))
    {K lam z i π Y I g : ℕ → Ω → ℝ} {Bl Bz lamInf Kinf : ℝ} (hK : Predetermined 𝔼 K)
    (hKb : BoundedProc K) (hl : ∀ t ω, |lam t ω| ≤ Bl) (hla : 𝔼.Adapted lam)
    (hz : ∀ t ω, |z t ω| ≤ Bz) (hza : 𝔼.Adapted z) (h320 : Eq320 𝔼 P K lam z)
    (hF : FisherEq 𝔼 lam i π)
    (hlim : ∀ t ω, Tendsto (fun N => 𝔼.E t (lam (t + N)) ω) atTop (𝓝 lamInf))
    (hKinf : P.poly 1 * Kinf = (1 - P.b0) * lamInf) (h38 : InvestEq P I K)
    (h39 : MUEq P lam Y I g) (t : ℕ) (ω : Ω) :
    Tendsto (fun N => ∑ j ∈ Finset.range N,
        chi P μ2 j * 𝔼.E t (i (t + j) - π (t + j + 1)) ω) atTop
      (𝓝 (Yinf P lamInf Kinf - P.N μ1 * Kinf + P.N μ1 * K t ω +
        (P.k * ek 𝔼 P.a0 μ2 z t ω + g t ω) - Y t ω)) := by
  have hcap := eq322 𝔼 ha0 hμ2 hfac hK hKb hl hla hz hza h320 hF hlim hKinf t ω
  have hlam := (eq321_iff 𝔼 hF le_rfl ω lamInf).mpr (hlim t ω)
  rw [hla t] at hlam
  have hsum : ∀ N, ∑ j ∈ Finset.range N, chi P μ2 j * 𝔼.E t (i (t + j) - π (t + j + 1)) ω =
      P.σ * ∑ j ∈ Finset.range N, 𝔼.E t (i (t + j) - π (t + j + 1)) ω +
        P.k * ∑ j ∈ Finset.range N,
          chiTilde P.a0 μ2 P.b0 j * 𝔼.E t (i (t + j) - π (t + j + 1)) ω := by
    intro N
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp only [chi]; ring
  simp_rw [hsum]
  convert (hlam.const_mul P.σ).add (hcap.const_mul P.k) using 2
  have hY := congrFun (output_eq hσ h39 t) ω
  have hI := congrFun (h38 t) ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hY hI
  rw [hY, hI]
  simp only [Yinf, Par.N]
  ring

/-! ### Footnote 34: the sign of `N` -/

/-- Woodford (2003), fn. 34, p. 368: "`N > 0` (because `μ̃₁ > 1 − δ`) if and only if `ε_ψ`
exceeds the critical value `ρ_k(1 − δ)/δ > 0`". Exact, given the root location of p. 365,
`δ > 0`, `k > 0` and `c' > 0`. -/
theorem N_pos_iff {P : Par} {μ1 μ2 : ℝ} (ha0 : 0 < P.a0) (hcp : 0 < P.cp) (hδ0 : 0 < P.δ)
    (hk : 0 < P.k) (hμ2 : 1 < μ2)
    (hfac : ∀ μ, P.poly μ = P.a0 * (μ - μ1) * (μ - μ2)) :
    0 < P.N μ1 ↔ P.ρk * (1 - P.δ) / P.δ < P.eps := by
  have hx : 1 - P.δ < μ2 := by linarith
  have key := Par.poly_pos_iff_lt ha0 hfac hx
  rw [Par.poly_one_sub_delta] at key
  have e1 : 0 < P.N μ1 ↔ 1 - P.δ < μ1 := by
    simp only [Par.N]
    constructor
    · intro h; by_contra hc; push Not at hc
      have : P.k * (μ1 - (1 - P.δ)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk.le (by linarith)
      linarith
    · intro h; exact mul_pos hk (by linarith)
  have e2 : 0 < P.cp * (P.eps * P.δ - P.ρk * (1 - P.δ)) ↔ P.ρk * (1 - P.δ) / P.δ < P.eps := by
    rw [div_lt_iff₀ hδ0]
    constructor
    · intro h; by_contra hc; push Not at hc
      have : P.cp * (P.eps * P.δ - P.ρk * (1 - P.δ)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hcp.le (by linarith)
      linarith
    · intro h; exact mul_pos hcp (by linarith)
  rw [e1, ← key, e2]

/-- Woodford (2003), fn. 34, p. 368: "`ρ_k(1 − δ)/δ > 0`". -/
theorem crit_pos {P : Par} (hρk : 0 < P.ρk) (hδ0 : 0 < P.δ) (hδ1 : P.δ < 1) :
    0 < P.ρk * (1 - P.δ) / P.δ :=
  div_pos (mul_pos hρk (by linarith)) hδ0

/-! ### p. 367: the case of a constant IS coefficient -/

/-- Woodford (2003), p. 367: if `p(r) = 0` for some `r ≠ 0` then `A(L)` factors through it:
`p(x) = a₀(x − a₂/(a₀ r))(x − r)`. -/
theorem Par.factor_of_root {P : Par} {r : ℝ} (ha0 : P.a0 ≠ 0) (hr : r ≠ 0)
    (hroot : P.poly r = 0) (x : ℝ) :
    P.poly x = P.a0 * (x - P.a2 / (P.a0 * r)) * (x - r) := by
  simp only [Par.poly] at hroot ⊢
  linear_combination (norm := (field_simp; ring)) (x / r) * hroot

/-- Woodford (2003), p. 367: with the root location `μ̃₁ < 1 < μ̃₂`, a root `x > 1` of `p` is
`μ̃₂`. -/
theorem Par.root_eq_mu2 {P : Par} {μ1 μ2 x : ℝ} (ha0 : 0 < P.a0)
    (hfac : ∀ μ, P.poly μ = P.a0 * (μ - μ1) * (μ - μ2)) (hμ1 : μ1 < 1) (hx : 1 < x) :
    P.poly x = 0 ↔ x = μ2 := by
  rw [hfac]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h ha0.ne'
      · exact absurd (sub_eq_zero.mp h) (by linarith)
    · exact sub_eq_zero.mp h
  · intro h; rw [h]; ring

/-- Woodford (2003), p. 367: the normalised `B(L) = (L − b₀)/a₀` is of the form
`−h(1 − μ̃₂ L)` with `h > 0` if and only if `h = b₀/a₀ > 0` and `μ̃₂ = 1/b₀`. -/
theorem Par.B_form_iff {P : Par} {μ2 : ℝ} (ha0 : P.a0 ≠ 0) (hb0 : P.b0 ≠ 0) :
    (∃ h : ℝ, 0 < h ∧ -P.b0 / P.a0 = -h ∧ 1 / P.a0 = h * μ2) ↔
      0 < P.b0 / P.a0 ∧ μ2 = P.b0⁻¹ := by
  constructor
  · rintro ⟨h, hh, e1, e2⟩
    have hh' : h = P.b0 / P.a0 := by rw [neg_div] at e1; linarith
    refine ⟨hh' ▸ hh, ?_⟩
    rw [hh'] at e2
    field_simp at e2 ⊢
    linear_combination -e2
  · rintro ⟨hpos, hμ⟩
    refine ⟨P.b0 / P.a0, hpos, by ring, ?_⟩
    rw [hμ]; field_simp

/-- Woodford (2003), p. 367: when `b₀ = μ̃₂⁻¹` every `χ̃_j` equals `h = b₀/a₀`. -/
theorem chiTilde_const {a0 μ2 b0 : ℝ} (hμ2 : μ2 ≠ 0) (hb : b0 = μ2⁻¹) (j : ℕ) :
    chiTilde a0 μ2 b0 j = b0 / a0 := by
  simp only [chiTilde, hb, sub_self, zero_mul, zero_div, add_zero]
  field_simp

/-- Woodford (2003), p. 367, corrected (survey error 3): when `b₀ = μ̃₂⁻¹` the IS coefficients
are all equal to `χ_j = σ + k h`, `h = b₀/a₀` — not `σ + h` as printed. -/
theorem chi_const {P : Par} {μ2 : ℝ} (hμ2 : μ2 ≠ 0) (hb : P.b0 = μ2⁻¹) (j : ℕ) :
    chi P μ2 j = P.σ + P.k * (P.b0 / P.a0) := by
  rw [chi, chiTilde_const hμ2 hb]

/-- Woodford (2003), p. 367: "In this case (3.20) is equivalent to `(1 − μ̃₁L)K̂_{t+1} = −h λ̂_t`"
— for bounded predetermined capital and bounded adapted `λ̂`, with `z = 0`, `b₀ = μ̃₂⁻¹`,
`|μ̃₂| > 1` and `h = b₀/a₀`. -/
theorem firstOrder_iff {P : Par} {μ1 μ2 : ℝ} (ha0 : P.a0 ≠ 0) (hμ2 : 1 < |μ2|)
    (hfac : ∀ μ, P.poly μ = P.a0 * (μ - μ1) * (μ - μ2)) (hb : P.b0 = μ2⁻¹)
    {K lam : ℕ → Ω → ℝ} {Bl : ℝ} (hK : Predetermined 𝔼 K) (hKb : BoundedProc K)
    (hl : ∀ t ω, |lam t ω| ≤ Bl) (hla : 𝔼.Adapted lam) :
    Eq320 𝔼 P K lam 0 ↔ ∀ t, K (t + 1) = μ1 • K t - (P.b0 / P.a0) • lam t := by
  obtain ⟨h1, h2⟩ := Par.coeffs_of_factor hfac
  have hμ0 : μ2 ≠ 0 := by
    intro h; rw [h, abs_zero] at hμ2; linarith
  have hq : |μ2⁻¹| < 1 := by
    rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hμ2
  have hz0 : ∀ t ω, |(0 : ℕ → Ω → ℝ) t ω| ≤ 0 := fun _ _ => by simp
  have hfb := forcing320_bounded 𝔼 (b0 := P.b0) hl hz0
  have hfa := forcing320_adapted 𝔼 (b0 := P.b0) hla (z := 0) (fun t => by simp)
  have hiff := secondOrder_iff 𝔼 ha0 h1 h2 hμ2 hfb hfa hK hKb
  -- the forward part equals `−h λ̂`
  set f := forcing320 𝔼 P.b0 lam 0 with hf
  have hu : ∀ t ω, |(fun t => -(P.a0 * μ2)⁻¹ • f t) t ω| ≤
      |(P.a0 * μ2)⁻¹| * (Bl + |P.b0| * Bl + 0) := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hfb t ω) (abs_nonneg _)
  have hua : 𝔼.Adapted (fun t => -(P.a0 * μ2)⁻¹ • f t) := fun t => by
    simp only [map_smul, hfa t]
  have hsol : ForwardSolution.Solves 𝔼 μ2⁻¹ (fun t => -(P.a0 * μ2)⁻¹ • f t)
      (fun t => -(P.b0 / P.a0) • lam t) := by
    intro t
    funext ω
    simp only [hf, forcing320, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, add_zero, hb]
    field_simp
    ring
  have hbd : BoundedProc (fun t => -(P.b0 / P.a0) • lam t) :=
    ⟨|P.b0 / P.a0| * Bl, fun t ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left (hl t ω) (abs_nonneg _)⟩
  have hw : wSol 𝔼 P.a0 μ2 f = fun t => -(P.b0 / P.a0) • lam t :=
    (ForwardSolution.eq_forwardSeries_abs 𝔼 hq hu hua hsol hbd).symm
  have e320 : Eq320 𝔼 P K lam 0 ↔
      ∀ t, P.a0 • 𝔼.E t (K (t + 2)) - P.a1 • K (t + 1) + P.a2 • K t = f t := by
    simp only [Eq320, hf, forcing320]
  rw [e320, hiff, hw]
  refine forall_congr' fun t => ?_
  simp only [neg_smul, sub_eq_add_neg]

/-- Woodford (2003), p. 367: under `K̂_{t+1} = μ̃₁ K̂_t − h λ̂_t`, (3.8) and (3.9) give
`Ŷ_t = N K̂_t − (σ + k h) λ̂_t + g_t`. -/
theorem output_firstOrder {P : Par} (hσ : P.σ ≠ 0) {μ1 h : ℝ} {K lam Y I g : ℕ → Ω → ℝ}
    (hrec : ∀ t, K (t + 1) = μ1 • K t - h • lam t) (h38 : InvestEq P I K)
    (h39 : MUEq P lam Y I g) (t : ℕ) :
    Y t = P.N μ1 • K t - (P.σ + P.k * h) • lam t + g t := by
  rw [output_eq hσ h39, h38 t, hrec t]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Par.N]
  ring

/-- Woodford (2003), p. 367, in full and corrected: with `b₀ = μ̃₂⁻¹`, `z = 0`, (3.8)–(3.10) and
(3.21), aggregate demand is (3.23) with the constant coefficient `χ_j = σ + k h`:
`Ŷ_t = −(σ + kh)λ̂_∞ + N K̂_t − ∑_j (σ + kh) E_t(ı̂_{t+j} − π_{t+j+1}) + g_t`. -/
theorem eq323_const {P : Par} {μ1 μ2 : ℝ} (hσ : P.σ ≠ 0) (ha0 : P.a0 ≠ 0) (hμ2 : 1 < |μ2|)
    (hfac : ∀ μ, P.poly μ = P.a0 * (μ - μ1) * (μ - μ2)) (hb : P.b0 = μ2⁻¹)
    {K lam Y I g i π : ℕ → Ω → ℝ} {Bl lamInf : ℝ} (hK : Predetermined 𝔼 K)
    (hKb : BoundedProc K) (hl : ∀ t ω, |lam t ω| ≤ Bl) (hla : 𝔼.Adapted lam)
    (h320 : Eq320 𝔼 P K lam 0) (h38 : InvestEq P I K) (h39 : MUEq P lam Y I g)
    (hF : FisherEq 𝔼 lam i π)
    (hlim : ∀ t ω, Tendsto (fun N => 𝔼.E t (lam (t + N)) ω) atTop (𝓝 lamInf)) (t : ℕ) (ω : Ω) :
    Tendsto (fun N => ∑ j ∈ Finset.range N,
        (P.σ + P.k * (P.b0 / P.a0)) * 𝔼.E t (i (t + j) - π (t + j + 1)) ω) atTop
      (𝓝 (-(P.σ + P.k * (P.b0 / P.a0)) * lamInf + P.N μ1 * K t ω + g t ω - Y t ω)) := by
  have hrec := (firstOrder_iff 𝔼 ha0 hμ2 hfac hb hK hKb hl hla).mp h320
  have hY := congrFun (output_firstOrder hσ hrec h38 h39 t) ω
  have hlam := (eq321_iff 𝔼 hF le_rfl ω lamInf).mpr (hlim t ω)
  rw [hla t] at hlam
  simp_rw [← Finset.mul_sum]
  convert hlam.const_mul (P.σ + P.k * (P.b0 / P.a0)) using 2
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hY
  rw [hY]
  ring

/-- Woodford (2003), p. 367: the critical adjustment cost at which the root of `B(L)` coincides
with `μ̃₂`: `ε_ψ* = −c' x (ρ_y k x − ρ_k − ρ_y k (1 − δ)) / ((βx − 1)(x − 1))`, `x = 1/b₀`
(it does not depend on `ε_ψ`). -/
noncomputable def epsStar (P : Par) : ℝ :=
  -(P.cp * P.b0⁻¹ * (P.ρy * P.k * P.b0⁻¹ - P.ρk - P.ρy * P.k * (1 - P.δ))) /
    ((P.β * P.b0⁻¹ - 1) * (P.b0⁻¹ - 1))

/-- Woodford (2003), p. 367: "the root of `B(L)` coincides with a root of `A(L)` … if and only
if `ε_ψ` happens to take a specific value": `p(1/b₀) = 0 ↔ ε_ψ = ε_ψ*` (because `p` is affine
in `ε_ψ`), whenever `(β/b₀ − 1)(1/b₀ − 1) ≠ 0`. -/
theorem coincide_iff (P : Par) (hden : (P.β * P.b0⁻¹ - 1) * (P.b0⁻¹ - 1) ≠ 0) :
    P.poly P.b0⁻¹ = 0 ↔ P.eps = epsStar P := by
  rw [Par.poly_eq, epsStar, eq_div_iff hden]
  constructor <;> intro h <;> linarith

/-! ### Calibration (Table 5.1, pp. 341–342, 362–363, and the numbers of fn. 34 and p. 367) -/

/-- Woodford (2003), Table 5.1, p. 341, and p. 356: with `ν = 0.11`, `φ_h⁻¹ = 0.75`,
`ω_p = 0.33`, `ρ_y = ν φ_h + φ_h/(φ_h − 1) ω_p = 22/15` and `ρ_k = ρ_y − ν = 407/300`. -/
theorem table51_rho :
    (11 / 100 : ℝ) * (4 / 3) + (4 / 3) / (4 / 3 - 1) * (33 / 100) = 22 / 15 ∧
      (22 / 15 : ℝ) - 11 / 100 = 407 / 300 := by
  norm_num

/-- Woodford (2003), p. 363: with `β = 0.99`, `θ = 7.88` (p. 343), `φ_h = 4/3`, the steady state
`β⁻¹ = ((θ − 1)/θ)((φ_h − 1)/φ_h)/k + (1 − δ)` gives `k = 1064250/107759 ≈ 9.876` at
`δ = 0.012`, and `k = 10` exactly at `δ = 2287/195030 ≈ 0.011726`. -/
theorem steady_k :
    ((99 / 100 : ℝ))⁻¹ = (197 / 25 - 1) / (197 / 25) * ((4 / 3 - 1) / (4 / 3)) /
        (1064250 / 107759) + (1 - 3 / 250) ∧
      ((99 / 100 : ℝ))⁻¹ = (197 / 25 - 1) / (197 / 25) * ((4 / 3 - 1) / (4 / 3)) / 10 +
        (1 - 2287 / 195030) := by
  norm_num

/-- Woodford (2003), pp. 362–363: the calibrated IS block (`β = 0.99`, `ρ_y = 22/15`,
`ρ_k = 407/300`, `σ = 1`) at depreciation `δ`, capital–output ratio `k` and adjustment cost
`ε_ψ`. -/
noncomputable def calib (δ k eps : ℝ) : Par := ⟨99 / 100, δ, eps, 22 / 15, 407 / 300, k, 1⟩

/-- Woodford (2003), p. 363: the calibration as printed, `δ = 0.012` (so `k ≈ 9.876`). -/
noncomputable def calib12 (eps : ℝ) : Par := calib (3 / 250) (1064250 / 107759) eps

/-- Woodford (2003), p. 363: the calibration with `k = 10` exactly ("ten quarters"). -/
noncomputable def calib10 (eps : ℝ) : Par := calib (2287 / 195030) 10 eps

/-- Woodford (2003), fn. 34, p. 368: the critical value `ρ_k(1 − δ)/δ` is `100529/900 ≈ 111.70`
at `δ = 0.012` and `78446401/686100 ≈ 114.34` at `k = 10` — not 114.5 as printed (neither rounds
to it). -/
theorem crit_values (e : ℝ) :
    (calib12 e).ρk * (1 - (calib12 e).δ) / (calib12 e).δ = 100529 / 900 ∧
      (calib10 e).ρk * (1 - (calib10 e).δ) / (calib10 e).δ = 78446401 / 686100 ∧
      (111.69 : ℝ) < 100529 / 900 ∧ (100529 / 900 : ℝ) < 111.70 ∧
      (114.33 : ℝ) < 78446401 / 686100 ∧ (78446401 / 686100 : ℝ) < 114.34 := by
  simp only [calib12, calib10, calib]
  norm_num

/-- Woodford (2003), p. 365: at both calibrations and `ε_ψ = 3`, `ρ_y k δ < ρ_k`, so the roots
of `A(L)` satisfy `0 < μ̃₁ < 1 < μ̃₂`. -/
theorem calib_roots :
    (∃ μ1 μ2 : ℝ, 0 < μ1 ∧ μ1 < 1 ∧ 1 < μ2 ∧
        ∀ μ, (calib10 3).poly μ = (calib10 3).a0 * (μ - μ1) * (μ - μ2)) ∧
      ∃ μ1 μ2 : ℝ, 0 < μ1 ∧ μ1 < 1 ∧ 1 < μ2 ∧
        ∀ μ, (calib12 3).poly μ = (calib12 3).a0 * (μ - μ1) * (μ - μ2) := by
  constructor
  · refine ((calib10 3).roots_iff ?_ ?_ ?_).mpr ?_ <;>
      simp only [calib10, calib, Par.cp, Par.a0] <;> norm_num
  · refine ((calib12 3).roots_iff ?_ ?_ ?_).mpr ?_ <;>
      simp only [calib12, calib, Par.cp, Par.a0] <;> norm_num

/-- Woodford (2003), p. 365: bracketing `μ̃₁` by sign changes of `p`: if `p(x_lo) > 0` and
`p(x_hi) < 0` with `x_lo, x_hi < μ̃₂`, then `x_lo < μ̃₁ < x_hi`. -/
theorem Par.bracket {P : Par} {μ1 μ2 xlo xhi : ℝ} (ha0 : 0 < P.a0)
    (hfac : ∀ μ, P.poly μ = P.a0 * (μ - μ1) * (μ - μ2)) (hlo : xlo < μ2) (hhi : xhi < μ2)
    (plo : 0 < P.poly xlo) (phi : P.poly xhi < 0) : xlo < μ1 ∧ μ1 < xhi := by
  refine ⟨(Par.poly_pos_iff_lt ha0 hfac hlo).mp plo, ?_⟩
  rcases lt_trichotomy μ1 xhi with h | h | h
  · exact h
  · rw [← h, hfac] at phi; simp at phi
  · have := (Par.poly_pos_iff_lt ha0 hfac hhi).mpr h; linarith

/-- Woodford (2003), fn. 34, p. 368: "the baseline value `ε_ψ = 3` implies that `N = −1.246`".
At the `k = 10` calibration `−1.2483 < N < −1.2481` (so `N = −1.248` to three decimals). -/
theorem N_calib10 {μ1 μ2 : ℝ} (h2 : 1 < μ2)
    (hfac : ∀ μ, (calib10 3).poly μ = (calib10 3).a0 * (μ - μ1) * (μ - μ2)) :
    (-1.2483 : ℝ) < (calib10 3).N μ1 ∧ (calib10 3).N μ1 < -1.2481 := by
  have ha0 : 0 < (calib10 3).a0 := by
    simp only [calib10, calib, Par.a0, Par.cp]; norm_num
  have hb := Par.bracket (xlo := 1 - 2287 / 195030 - 12483 / 100000)
    (xhi := 1 - 2287 / 195030 - 12481 / 100000) ha0 hfac (by linarith) (by linarith)
    (by simp only [calib10, calib, Par.poly, Par.a0, Par.a1, Par.a2, Par.cp]; norm_num)
    (by simp only [calib10, calib, Par.poly, Par.a0, Par.a1, Par.a2, Par.cp]; norm_num)
  simp only [calib10, calib, Par.N]
  constructor <;> linarith [hb.1, hb.2]

/-- Woodford (2003), fn. 34, p. 368: at the calibration as printed (`δ = 0.012`),
`−1.2339 < N < −1.2337` at `ε_ψ = 3`. -/
theorem N_calib12 {μ1 μ2 : ℝ} (h2 : 1 < μ2)
    (hfac : ∀ μ, (calib12 3).poly μ = (calib12 3).a0 * (μ - μ1) * (μ - μ2)) :
    (-1.2339 : ℝ) < (calib12 3).N μ1 ∧ (calib12 3).N μ1 < -1.2337 := by
  have ha0 : 0 < (calib12 3).a0 := by
    simp only [calib12, calib, Par.a0, Par.cp]; norm_num
  have hb := Par.bracket (xlo := 1 - 3 / 250 - 12339 / 10000 * (107759 / 1064250))
    (xhi := 1 - 3 / 250 - 12337 / 10000 * (107759 / 1064250)) ha0 hfac (by linarith)
    (by linarith)
    (by simp only [calib12, calib, Par.poly, Par.a0, Par.a1, Par.a2, Par.cp]; norm_num)
    (by simp only [calib12, calib, Par.poly, Par.a0, Par.a1, Par.a2, Par.cp]; norm_num)
  simp only [calib12, calib, Par.N]
  constructor <;> nlinarith [hb.1, hb.2]

/-- Woodford (2003), p. 367: "equal approximately to 3.23" — the critical value is
`ε_ψ* ∈ (3.180, 3.181)` at the `k = 10` calibration and `ε_ψ* ∈ (3.109, 3.110)` at `δ = 0.012`;
neither is 3.23. -/
theorem epsStar_values (e : ℝ) :
    (3.180 : ℝ) < epsStar (calib10 e) ∧ epsStar (calib10 e) < 3.181 ∧
      (3.109 : ℝ) < epsStar (calib12 e) ∧ epsStar (calib12 e) < 3.110 := by
  simp only [epsStar, calib10, calib12, calib, Par.cp, Par.b0]
  norm_num

/-- Woodford (2003), p. 367 (survey error 3): at the coincidence (`k = 10` calibration,
`ε_ψ = ε_ψ*`) the constant IS coefficient `σ + k h` lies in `(3.73, 3.74)` — "a bit less than
4", as Fig. 5.7 and p. 369 say — while the printed `σ + h` lies in `(1.27, 1.28)`. -/
theorem chi_values :
    let P := calib10 (epsStar (calib10 0))
    (3.73 : ℝ) < P.σ + P.k * (P.b0 / P.a0) ∧ P.σ + P.k * (P.b0 / P.a0) < 3.74 ∧
      (1.27 : ℝ) < P.σ + P.b0 / P.a0 ∧ P.σ + P.b0 / P.a0 < 1.28 := by
  simp only [epsStar, calib10, calib, Par.cp, Par.b0, Par.a0]
  norm_num

/-- Woodford (2003), p. 367 (survey error 3), a counterexample to the printed `χ_j = σ + h`: if
`p(1/b₀) = 0` (the coincidence case) and `k ≠ 1`, there is a perfect-foresight path satisfying
(3.20) (with `z = 0`), (3.8) and (3.9), with `λ̂_t = 1` at all dates, along which the correct
relation `Ŷ_t = N K̂_t − (σ + k h)λ̂_t + g_t` holds and the printed `Ŷ_t = N K̂_t − (σ + h)λ̂_t
+ g_t` fails at `t = 0` (`h = b₀/a₀`, `μ̃₁ = a₂ b₀/a₀`). -/
theorem printed_chi_counterexample (P : Par) (ha0 : P.a0 ≠ 0) (hb0 : P.b0 ≠ 0) (hk : P.k ≠ 1)
    (hσ : P.σ ≠ 0) (hroot : P.poly P.b0⁻¹ = 0) :
    ∃ K lam Y I g : ℕ → Unit → ℝ, Eq320 perfectForesight P K lam 0 ∧ InvestEq P I K ∧
      MUEq P lam Y I g ∧ Predetermined perfectForesight K ∧ (∀ t, lam t = fun _ => 1) ∧
      (∀ t, Y t = P.N (P.a2 / (P.a0 * P.b0⁻¹)) • K t - (P.σ + P.k * (P.b0 / P.a0)) • lam t
        + g t) ∧
      Y 0 ≠ P.N (P.a2 / (P.a0 * P.b0⁻¹)) • K 0 - (P.σ + P.b0 / P.a0) • lam 0 + g 0 := by
  set r := P.b0⁻¹ with hr
  set μ1 := P.a2 / (P.a0 * r) with hμ1
  set h := P.b0 / P.a0 with hh
  have hr0 : r ≠ 0 := inv_ne_zero hb0
  have hfac : ∀ x, P.poly x = P.a0 * (x - μ1) * (x - r) := Par.factor_of_root ha0 hr0 hroot
  obtain ⟨h1, h2⟩ := Par.coeffs_of_factor hfac
  set K : ℕ → Unit → ℝ := path (fun _ => 0) μ1 (fun _ _ => -h) with hK
  set lam : ℕ → Unit → ℝ := fun _ _ => 1 with hlam
  set g : ℕ → Unit → ℝ := fun _ _ => 0 with hg
  set I : ℕ → Unit → ℝ := fun t => P.k • (K (t + 1) - (1 - P.δ) • K t) with hI
  set Y : ℕ → Unit → ℝ := fun t => I t + g t - P.σ • lam t with hY
  have hrec : ∀ t, K (t + 1) = μ1 • K t - h • lam t := fun t => by
    rw [hK, path_succ]
    funext u
    simp [hlam, sub_eq_add_neg]
  have h38 : InvestEq P I K := fun t => rfl
  have h39 : MUEq P lam Y I g := fun t => by
    funext u
    simp only [hY, hlam, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
    field_simp
    ring
  refine ⟨K, lam, Y, I, g, ?_, h38, h39, fun t => rfl, fun t => rfl, ?_, ?_⟩
  · intro t
    change P.a0 • K (t + 2) - P.a1 • K (t + 1) + P.a2 • K t =
      lam t - P.b0 • lam (t + 1) + 0
    rw [show t + 2 = t + 1 + 1 from rfl, hrec (t + 1), hrec t]
    funext u
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hlam, Pi.zero_apply,
      h1, h2, hh, hr]
    field_simp
    ring
  · exact fun t => output_firstOrder hσ hrec h38 h39 t
  · intro heq
    have h0 := congrFun heq ()
    have hK1 := congrFun (hrec 0) ()
    simp only [hY, hI, hg, hlam, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Par.N] at h0 hK1
    have hK0 : K 0 () = 0 := rfl
    rw [hK1, hK0] at h0
    have hkh : (P.k - 1) * h = 0 := by linarith
    rcases mul_eq_zero.mp hkh with h' | h'
    · exact hk (by linarith)
    · rw [hh] at h'
      exact hb0 (by simpa [ha0] using h')

/-- Woodford (2003), p. 367: the counterexample at the calibration (`k = 10`, `ε_ψ = ε_ψ*`). -/
theorem printed_chi_counterexample_calib :
    let P := calib10 (epsStar (calib10 0))
    ∃ K lam Y I g : ℕ → Unit → ℝ, Eq320 perfectForesight P K lam 0 ∧ InvestEq P I K ∧
      MUEq P lam Y I g ∧ Predetermined perfectForesight K ∧ (∀ t, lam t = fun _ => 1) ∧
      (∀ t, Y t = P.N (P.a2 / (P.a0 * P.b0⁻¹)) • K t - (P.σ + P.k * (P.b0 / P.a0)) • lam t
        + g t) ∧
      Y 0 ≠ P.N (P.a2 / (P.a0 * P.b0⁻¹)) • K 0 - (P.σ + P.b0 / P.a0) • lam 0 + g 0 := by
  intro P
  have hE : epsStar P = epsStar (calib10 0) := by
    simp only [P, epsStar, calib10, calib, Par.cp, Par.b0]
  refine printed_chi_counterexample P ?_ ?_ ?_ ?_ ?_
  · simp only [P, epsStar, calib10, calib, Par.cp, Par.b0, Par.a0]; norm_num
  · simp only [P, calib10, calib, Par.cp, Par.b0]; norm_num
  · simp only [P, calib10, calib]; norm_num
  · simp only [P, calib10, calib]; norm_num
  · refine (coincide_iff P ?_).mpr ?_
    · simp only [P, calib10, calib, Par.cp, Par.b0]; norm_num
    · rw [hE]; rfl

/-! ### One-period delays: (3.24)–(3.26), p. 370 -/

/-- Woodford (2003), eq. (3.24), p. 370, in full: if consumption and investment are determined a
period in advance — `K̂_{t+1}` is known at `t − 1`, and the investment condition (3.20) holds
conditional on date-`t − 1` information — then, under the other hypotheses of (3.22) (now with
`E_{t−1} λ̂_{t+N} → λ̂_∞`),
`K̂_{t+1} = (1 − μ̃₁)K̂_∞ + μ̃₁K̂_t − ∑_j χ̃_j E_{t−1}(ı̂_{t+j} − π_{t+j+1}) + e^k_{t−1}`
with the same coefficients `χ̃_j`. Dates are written `t = s + 1`; the disturbance is
`−(a₀μ̃₂)⁻¹ ∑_j μ̃₂^{−j} E_{t−1} z_{t+j}`, i.e. `ek` of the process `s ↦ E_s z_{s+1}`. -/
theorem eq324 {P : Par} {μ1 μ2 : ℝ} (ha0 : 0 < P.a0) (hμ2 : 1 < μ2)
    (hfac : ∀ μ, P.poly μ = P.a0 * (μ - μ1) * (μ - μ2)) {K lam z i π : ℕ → Ω → ℝ}
    {Bl Bz lamInf Kinf : ℝ} (hK : ∀ s, 𝔼.E s (K (s + 2)) = K (s + 2)) (hKb : BoundedProc K)
    (hl : ∀ t ω, |lam t ω| ≤ Bl) (hz : ∀ t ω, |z t ω| ≤ Bz)
    (h320 : ∀ s, P.a0 • 𝔼.E s (K (s + 3)) - P.a1 • K (s + 2) + P.a2 • K (s + 1) =
      𝔼.E s (forcing320 𝔼 P.b0 lam z (s + 1)))
    (hF : FisherEq 𝔼 lam i π)
    (hlim : ∀ s ω, Tendsto (fun N => 𝔼.E s (lam (s + 1 + N)) ω) atTop (𝓝 lamInf))
    (hKinf : P.poly 1 * Kinf = (1 - P.b0) * lamInf) (s : ℕ) (ω : Ω) :
    Tendsto (fun N => ∑ j ∈ Finset.range N,
        chiTilde P.a0 μ2 P.b0 j * 𝔼.E s (i (s + 1 + j) - π (s + 1 + j + 1)) ω) atTop
      (𝓝 ((1 - μ1) * Kinf + μ1 * K (s + 1) ω + ek 𝔼 P.a0 μ2 (fun s => 𝔼.E s (z (s + 1))) s ω -
        K (s + 2) ω)) := by
  obtain ⟨h1, h2⟩ := Par.coeffs_of_factor hfac
  have hμ2' : 1 < |μ2| := by rw [abs_of_pos (by linarith)]; exact hμ2
  set x : ℕ → Ω → ℝ := fun s => K (s + 1) with hx
  set f : ℕ → Ω → ℝ := fun s => 𝔼.E s (forcing320 𝔼 P.b0 lam z (s + 1)) with hf
  have hxp : Predetermined 𝔼 x := fun s => hK s
  have hxb : BoundedProc x := by
    obtain ⟨M, hM⟩ := hKb; exact ⟨M, fun t ω => hM (t + 1) ω⟩
  have hfb : ∀ t ω, |f t ω| ≤ Bl + |P.b0| * Bl + Bz := fun t ω =>
    𝔼.abs_E_le (fun ω => forcing320_bounded 𝔼 hl hz (t + 1) ω) t ω
  have hfa : 𝔼.Adapted f := fun t => 𝔼.E_E_self t _
  have hrec := (secondOrder_iff 𝔼 ha0.ne' h1 h2 hμ2' hfb hfa hxp hxb).mp (fun s => by
    simpa [hx, hf, Par.a2] using h320 s)
  set L : ℕ → ℝ := fun j => 𝔼.E s (lam (s + 1 + j)) ω with hLdef
  set R : ℕ → ℝ := fun j => 𝔼.E s (i (s + 1 + j) - π (s + 1 + j + 1)) ω with hRdef
  set Z : ℕ → ℝ := fun j => 𝔼.E s (z (s + 1 + j)) ω with hZdef
  have hLR : ∀ j, L j = R j + L (j + 1) := fun j => by
    have := congrFun (lam_step 𝔼 hF (show s ≤ s + 1 + j by omega)) ω
    simp only [Pi.add_apply] at this
    simp only [hLdef, hRdef, ← add_assoc]
    exact this
  have hLb : ∀ j, |L j| ≤ Bl := fun j => 𝔼.abs_E_le (hl (s + 1 + j)) s ω
  have hq : |μ2⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith)]; exact inv_lt_one_of_one_lt₀ hμ2
  have hZs : Summable (fun j => μ2⁻¹ ^ j * Z j) := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (abs_nonneg _) hq).mul_right Bz) (fun j => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hz _) s ω) (pow_nonneg (abs_nonneg _) _)
  have hEf : ∀ j, 𝔼.E s (f (s + j)) ω = L j - P.b0 * L (j + 1) + Z j := by
    intro j
    simp only [hf, 𝔼.tower (Nat.le_add_right s j), forcing320, map_add, map_sub, map_smul,
      𝔼.tower (show s ≤ s + j + 1 by omega), Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, hLdef, hZdef]
    simp only [add_right_comm s j 1, add_assoc]
  have hKt : K (s + 2) ω = μ1 * K (s + 1) ω +
      ∑' j, μ2⁻¹ ^ j * (-(P.a0 * μ2)⁻¹ * (L j - P.b0 * L (j + 1) + Z j)) := by
    have := congrFun (hrec s) ω
    simp only [hx, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this, wSol_apply]
    simp only [hEf]
  have hKinf' : P.a0 * (1 - μ1) * (1 - μ2) * Kinf = (1 - P.b0) * lamInf := by
    rw [← hKinf, hfac 1]
  have hek : ek 𝔼 P.a0 μ2 (fun s => 𝔼.E s (z (s + 1))) s ω =
      -(P.a0 * μ2)⁻¹ * ∑' j, μ2⁻¹ ^ j * Z j := by
    simp only [ek, wSol_apply, hZdef, ← tsum_mul_left, 𝔼.tower (Nat.le_add_right s _)]
    refine tsum_congr fun j => ?_
    rw [add_right_comm s j 1]
    ring
  rw [hek]
  have hlim' : Tendsto L atTop (𝓝 lamInf) := hlim s ω
  exact capital_rep ha0.ne' hμ2 hLb hLR hlim' hZs hKt hKinf'

/-- Woodford (2003), eq. (3.25), p. 370, in full: with consumption also determined a period in
advance, (3.9) becomes `Ŷ_t = Î_t + g_t − σ E_{t−1} λ̂_t`; together with (3.8) and (3.24),
`Ŷ_t = Ŷ_∞ − N K̂_∞ + N K̂_t − ∑_j χ_j E_{t−1}(ı̂_{t+j} − π_{t+j+1}) + e^y` with the same `χ_j`
and `e^y = k e^k_{t−1} + g_t` (note that `g_t` need not be known at `t − 1`). Dates are written
`t = s + 1`. -/
theorem eq325 {P : Par} {μ1 μ2 : ℝ} (ha0 : 0 < P.a0) (hμ2 : 1 < μ2)
    (hfac : ∀ μ, P.poly μ = P.a0 * (μ - μ1) * (μ - μ2)) {K lam z i π Y I g : ℕ → Ω → ℝ}
    {Bl Bz lamInf Kinf : ℝ} (hK : ∀ s, 𝔼.E s (K (s + 2)) = K (s + 2)) (hKb : BoundedProc K)
    (hl : ∀ t ω, |lam t ω| ≤ Bl) (hz : ∀ t ω, |z t ω| ≤ Bz)
    (h320 : ∀ s, P.a0 • 𝔼.E s (K (s + 3)) - P.a1 • K (s + 2) + P.a2 • K (s + 1) =
      𝔼.E s (forcing320 𝔼 P.b0 lam z (s + 1)))
    (hF : FisherEq 𝔼 lam i π)
    (hlim : ∀ s ω, Tendsto (fun N => 𝔼.E s (lam (s + 1 + N)) ω) atTop (𝓝 lamInf))
    (hKinf : P.poly 1 * Kinf = (1 - P.b0) * lamInf) (h38 : InvestEq P I K)
    (h39 : ∀ s, Y (s + 1) = I (s + 1) + g (s + 1) - P.σ • 𝔼.E s (lam (s + 1))) (s : ℕ)
    (ω : Ω) :
    Tendsto (fun N => ∑ j ∈ Finset.range N,
        chi P μ2 j * 𝔼.E s (i (s + 1 + j) - π (s + 1 + j + 1)) ω) atTop
      (𝓝 (Yinf P lamInf Kinf - P.N μ1 * Kinf + P.N μ1 * K (s + 1) ω +
        (P.k * ek 𝔼 P.a0 μ2 (fun s => 𝔼.E s (z (s + 1))) s ω + g (s + 1) ω) - Y (s + 1) ω)) := by
  have hcap := eq324 𝔼 ha0 hμ2 hfac hK hKb hl hz h320 hF hlim hKinf s ω
  have hlam := (eq321_iff 𝔼 hF (show s ≤ s + 1 by omega) ω lamInf).mpr (hlim s ω)
  have hsum : ∀ N, ∑ j ∈ Finset.range N,
      chi P μ2 j * 𝔼.E s (i (s + 1 + j) - π (s + 1 + j + 1)) ω =
      P.σ * ∑ j ∈ Finset.range N, 𝔼.E s (i (s + 1 + j) - π (s + 1 + j + 1)) ω +
        P.k * ∑ j ∈ Finset.range N,
          chiTilde P.a0 μ2 P.b0 j * 𝔼.E s (i (s + 1 + j) - π (s + 1 + j + 1)) ω := by
    intro N
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp only [chi]; ring
  simp_rw [hsum]
  convert (hlam.const_mul P.σ).add (hcap.const_mul P.k) using 2
  have hY := congrFun (h39 s) ω
  have hI := congrFun (h38 (s + 1)) ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hY hI
  rw [hY, hI]
  simp only [Yinf, Par.N]
  ring

/-- Woodford (2003), eq. (3.26), p. 370: if new prices are set a period in advance, (3.17)
holds conditional on date-`t − 1` information and `π_t` is known at `t − 1`; this is equivalent
to `π_t = ξ₀E_{t−1}ŝ_t − ξ₁E_{t−1}ŝ_{t+1} + ψ₁E_{t−1}π_{t+1} − ψ₂E_{t−1}π_{t+2}` with the
coefficients of (3.17). (The conditioning itself is the modelling assumption, stated, as in
§1.1, rather than re-derived from the delayed Calvo problem.) Dates are written `t = s + 1`. -/
theorem eq326_iff {ξ0 ξ1 ψ1 ψ2 : ℝ} {π sc : ℕ → Ω → ℝ}
    (hπ : ∀ s, 𝔼.E s (π (s + 1)) = π (s + 1)) :
    (∀ s, 𝔼.E s (π (s + 1) - ξ0 • sc (s + 1) + ξ1 • 𝔼.E (s + 1) (sc (s + 2)) -
        ψ1 • 𝔼.E (s + 1) (π (s + 2)) + ψ2 • 𝔼.E (s + 1) (π (s + 3))) = 0) ↔
      ∀ s, π (s + 1) = ξ0 • 𝔼.E s (sc (s + 1)) - ξ1 • 𝔼.E s (sc (s + 2)) +
        ψ1 • 𝔼.E s (π (s + 2)) - ψ2 • 𝔼.E s (π (s + 3)) := by
  refine forall_congr' fun s => ?_
  have hs : s ≤ s + 1 := Nat.le_succ s
  simp only [map_add, map_sub, map_smul, 𝔼.tower hs, hπ s]
  constructor
  · intro h
    rw [← sub_eq_zero]
    rw [← h]
    abel
  · intro h
    rw [h]
    abel

end Woodford.PolicyResponseDynamics.ISBlock
