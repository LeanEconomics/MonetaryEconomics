/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PolicyResponseDynamics.Predetermined

/-!
# Small quantitative models

Woodford (2003), *Interest and Prices*, Chapter 5, §2, pp. 336–352: the Rotemberg–Woodford,
Amato–Laubach and Giannoni–Woodford models. The VAR estimates, the impulse-response and
second-moment figures (Figures 5.2–5.5), Table 5.4 and the Wald tests are empirical and out of
scope; what is formalised are the structural equations and the arithmetic of Tables 5.1–5.3.

## Main results

* (2.1), derived from the Chapter 3 Calvo first-order condition with a fraction `ϕ` of prices
  taking effect after one quarter and `1 − ϕ` after two (`eq21`, `eq21_book`),
  `ψ = (1 − ϕ)/(ϕα)`. The natural rate (2.3) is `Predetermined.NatRate`.
* (2.2): `eq22` (`E_{t−1} μ_t` when `d = 2`), using (1.21) and (1.8).
* (2.4): `eq24` (the forecastable habit IS relation); (2.5): `eq25` as an identity, with the
  composite disturbances it requires, and `eq25_bracket`, `eq25_bracket_not_forecastable`: the
  last term of (2.5) contains the revision of expenditure decided at `t − 1`, so it is not purely
  exogenous (imprecision).
* (2.6)–(2.7): predetermination of quasi-differenced inflation (`eq26_predetermined`), its unique
  bounded forward solution (`eq26_forward_unique`, via `shiftSystem`), the real-wage identity and
  the flexible-wage form of (2.7) (`eq27_iff`).
* Tables 5.1–5.3: `table51_*`, `table52_*`, `table53_*`. Survey error 11 confirmed with exact
  bounds (`table51_zeta_from_theta`, `table51_kappa_from_zeta`, `table51_theta_from_zeta`,
  `table51_zeta_rounds_013`).
* Survey error 8 (rule (1.12) and the long-run coefficients of Figures 5.1/5.8, fn. 35):
  `rule112_iff` ((1.12) is (1.14) with an AR(1) intercept), `rule112_determinate_iff`,
  `rule112_longrun`, `rule28_longrun`, `fig58_rule112_indeterminate`,
  `fig58_rule112_baseline_determinate`, `fn35_rule28_longrun`.
* Proposition 4.4 of Chapter 4 (sufficiency of the corrected statement, restated with its
  Proposition C.1/C.2 and Blanchard–Kahn machinery in the nested namespace `Prop44`):
  `Prop44.prop44_sufficient`; and the alternative reading of Fig. 5.8 — rule (2.8) with
  `φ_π = .6`, `φ_x = .3`, `ρ = .7` at the Table 5.1 values is determinate
  (`Prop44.fig58_rule28_determinate`).
-/

namespace Woodford.PolicyResponseDynamics.SmallModels

open Filter Topology
open Woodford.PolicyResponseDynamics.Predetermined ForwardSystems

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (2.1): two implementation lags -/

omit 𝔼 in
/-- Woodford (2003), p. 336: the Rotemberg–Woodford price index — a fraction `ϕ` of the prices
revised for date `t + 2` are set at `t + 1`, the rest at `t`:
`π_{t+2} = (1 − α)[ϕ E_{t+1} q_{t+2} + (1 − ϕ) E_t q_{t+2}]`. -/
def IndexLaw2 (𝔼 : ExpectationSystem Ω) (α ϕ : ℝ) (q infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl (t + 2) = (1 - α) • (ϕ • 𝔼.E (t + 1) (q (t + 2)) + (1 - ϕ) • 𝔼.E t (q (t + 2)))

omit 𝔼 in
/-- Woodford (2003), p. 337: `ψ ≡ (1 − ϕ)/(ϕα)`. -/
noncomputable def psiRW (α ϕ : ℝ) : ℝ := (1 - ϕ) / (ϕ * α)

/-- Woodford (2003), eq. (2.1), pp. 336–337 (**derived** from the recursive Calvo first-order
condition `CalvoRec` of Chapter 3 and the two-lag index law): with `ξ = (1 − α)(1 − αβ)/α`,
`π_{t+2} = (1/(1+ψ))[ξ E_{t+1} c_{t+2} + β E_{t+1} π_{t+3}]
  + (ψ/(1+ψ))[ξ E_t c_{t+2} + β E_t π_{t+3}]`. With `ξ c = κ x − (κ/ω_mc) μ` (`eq120`) and
`E_t μ_{t+2} = 0` (`d = 2`) this is (2.1). -/
theorem eq21 {α β ϕ : ℝ} (hα : 0 < α) (hϕ : 0 < ϕ) (hϕ1 : ϕ ≤ 1) {q infl c : ℕ → Ω → ℝ}
    (hrec : CalvoRec 𝔼 α β q infl c) (hidx : IndexLaw2 𝔼 α ϕ q infl) (t : ℕ) :
    infl (t + 2) = (1 / (1 + psiRW α ϕ)) • (calvoXi α β • 𝔼.E (t + 1) (c (t + 2)) +
        β • 𝔼.E (t + 1) (infl (t + 3))) +
      (psiRW α ϕ / (1 + psiRW α ϕ)) • (calvoXi α β • 𝔼.E t (c (t + 2)) +
        β • 𝔼.E t (infl (t + 3))) := by
  have ha := hidx t
  have hk1 : 𝔼.E (t + 1) (infl (t + 2)) = infl (t + 2) := by
    rw [ha]
    simp only [map_smul, map_add, 𝔼.E_E_self, 𝔼.known (Nat.le_succ t)]
  have h0 : 𝔼.E t (infl (t + 2)) = (1 - α) • 𝔼.E t (q (t + 2)) := by
    rw [ha]
    simp only [map_smul, map_add, 𝔼.tower (Nat.le_succ t), 𝔼.E_E_self]
    module
  have hA := congrArg (𝔼.E (t + 1)) (hrec (t + 2))
  simp only [map_add, map_smul, 𝔼.tower (by omega : t + 1 ≤ t + 2), hk1] at hA
  have hB := congrArg (𝔼.E t) (hrec (t + 2))
  simp only [map_add, map_smul, 𝔼.tower (by omega : t ≤ t + 2)] at hB
  have hn := hidx (t + 1)
  have hq1 := congrArg (𝔼.E (t + 1)) hn
  simp only [map_smul, map_add, 𝔼.E_E_self, 𝔼.tower (by omega : t + 1 ≤ t + 1 + 1)] at hq1
  have hq0 := congrArg (𝔼.E t) hn
  simp only [map_smul, map_add, 𝔼.tower (by omega : t ≤ t + 1 + 1),
    𝔼.tower (by omega : t ≤ t + 1)] at hq0
  rw [show t + 1 + 2 = t + 3 by omega, show t + 2 + 1 = t + 3 by omega] at *
  funext ω
  have ea := congrFun ha ω
  have e0 := congrFun h0 ω
  have eA := congrFun hA ω
  have eB := congrFun hB ω
  have eq1 := congrFun hq1 ω
  have eq0 := congrFun hq0 ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ea e0 eA eB eq1 eq0 ⊢
  set π0 := infl (t + 3) with hπ0
  set A := 𝔼.E (t + 1) (q (t + 2)) ω
  set B := 𝔼.E t (q (t + 2)) ω
  set E1c := 𝔼.E (t + 1) (c (t + 2)) ω
  set E0c := 𝔼.E t (c (t + 2)) ω
  set E1p := 𝔼.E (t + 1) (infl (t + 3)) ω
  set E0p := 𝔼.E t (infl (t + 3)) ω
  set E1q := 𝔼.E (t + 1) (q (t + 3)) ω
  set E0q := 𝔼.E t (q (t + 3)) ω
  set E0π := 𝔼.E t (infl (t + 2)) ω
  set p := infl (t + 2) ω
  have K1 : (1 - (1 - α) * ϕ) * p =
      ϕ * (1 - α) * (1 - α * β) * E1c + α * β * ϕ * E1p + (1 - ϕ) * E0π := by
    linear_combination ea + (1 - α) * ϕ * eA - α * β * ϕ * eq1 - (1 - ϕ) * e0
  have K2 : α * E0π = (1 - α) * (1 - α * β) * E0c + α * β * E0p := by
    linear_combination e0 + (1 - α) * eB - α * β * eq0
  have hξ : α * calvoXi α β = (1 - α) * (1 - α * β) := by
    unfold calvoXi; field_simp
  have K2' : E0π = calvoXi α β * E0c + β * E0p := by
    apply mul_left_cancel₀ hα.ne'
    linear_combination K2 - E0c * hξ
  have hψ : α * ϕ * psiRW α ϕ = 1 - ϕ := by
    unfold psiRW; field_simp
  have hpos : 0 < 1 + psiRW α ϕ := by
    unfold psiRW
    have : 0 ≤ (1 - ϕ) / (ϕ * α) := div_nonneg (by linarith) (by positivity)
    linarith
  have hD : α * ϕ * (1 + psiRW α ϕ) = 1 - (1 - α) * ϕ := by linear_combination hψ
  have key : (1 + psiRW α ϕ) * p = (calvoXi α β * E1c + β * E1p) +
      psiRW α ϕ * (calvoXi α β * E0c + β * E0p) := by
    apply mul_left_cancel₀ (mul_pos hα hϕ).ne'
    linear_combination K1 + (1 - ϕ) * K2' + p * hD - ϕ * E1c * hξ
      - calvoXi α β * E0c * hψ - β * E0p * hψ
  field_simp
  linear_combination key

/-- Woodford (2003), eq. (2.1), pp. 336–337, **in the book's form**: with average real marginal
cost `ŝ = ω_mc x − μ` entering the Calvo condition as `c = ŝ/(1 + ωθ)`, expenditure
predetermined two quarters ((1.6) with `d = 2`, so `E_t μ_{t+2} = 0`) and `κ = ξ ω_mc/(1 + ωθ)`:
`π_{t+2} = (1/(1+ψ))[κ E_{t+1} x_{t+2} − (κ/ω_mc) E_{t+1} μ_{t+2} + β E_{t+1} π_{t+3}]
  + (ψ/(1+ψ))[κ E_t x_{t+2} + β E_t π_{t+3}]`. -/
theorem eq21_book {α β ϕ ωmc A σ : ℝ} (hα : 0 < α) (hϕ : 0 < ϕ) (hϕ1 : ϕ ≤ 1) (hω : ωmc ≠ 0)
    (hA : A ≠ 0) (hσ : σ ≠ 0) {q infl c x Y g lam : ℕ → Ω → ℝ}
    (hrec : CalvoRec 𝔼 α β q infl c) (hidx : IndexLaw2 𝔼 α ϕ q infl)
    (hc : ∀ r, c r = A⁻¹ • (ωmc • x r - mu σ lam g Y r)) (h16 : Eq16 𝔼 σ 2 Y g lam) (t : ℕ) :
    infl (t + 2) = (1 / (1 + psiRW α ϕ)) •
        ((calvoXi α β * (ωmc / A)) • 𝔼.E (t + 1) (x (t + 2)) -
          (calvoXi α β * (ωmc / A) / ωmc) • 𝔼.E (t + 1) (mu σ lam g Y (t + 2)) +
          β • 𝔼.E (t + 1) (infl (t + 3))) +
      (psiRW α ϕ / (1 + psiRW α ϕ)) • ((calvoXi α β * (ωmc / A)) • 𝔼.E t (x (t + 2)) +
        β • 𝔼.E t (infl (t + 3))) := by
  rw [eq21 𝔼 hα hϕ hϕ1 hrec hidx t, hc, map_smul, map_sub, map_smul, map_smul, map_sub,
    map_smul, E_mu_zero 𝔼 hσ h16 t]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  field_simp
  ring

/-! ### (2.2): `E_{t−1} μ_t` when `d = 2` -/

/-- Woodford (2003), eq. (2.2), p. 337 (**derived** from (1.21) and (1.8) with `d = 2`): along a
solution of the bond-pricing relation, of (1.6) and of (1.8) with `d = 2`,
`E_{t+1} μ_{t+2} = E_{t+1}(î_{t+2} − π_{t+3}) + σ⁻¹[(Ŷ − g)_{t+2} − (Ŷ − g)_{t+3}]`; the second
term needs no expectation because `(Ŷ − g)_{t+3}` is known at `t + 1`. -/
theorem eq22 {σ : ℝ} (hσ : σ ≠ 0) {Y g i infl lam : ℕ → Ω → ℝ} (hla : 𝔼.Adapted lam)
    (hlam : LamEq 𝔼 i infl lam) (h16 : Eq16 𝔼 σ 2 Y g lam) (h18 : IS18 𝔼 σ 2 Y g i infl)
    (t : ℕ) :
    𝔼.E (t + 1) (mu σ lam g Y (t + 2)) = 𝔼.E (t + 1) (i (t + 2) - infl (t + 3)) +
      σ⁻¹ • ((Y (t + 2) - g (t + 2)) - (Y (t + 3) - g (t + 3))) := by
  have hmu := mu_observables 𝔼 hσ hla hlam h16 (t + 2)
  have hW2 : 𝔼.E (t + 1) (Y (t + 2) - g (t + 2)) = Y (t + 2) - g (t + 2) := by
    have := (is18_iterate 𝔼 h18 t 0).symm
    simp only [add_zero, Finset.range_zero, Finset.sum_empty, smul_zero, sub_zero] at this
    exact ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) this
  have h3 := h18 (t + 1)
  rw [show t + 1 + 2 = t + 3 by omega, show t + 3 + 1 = t + 4 by omega] at h3
  rw [hmu]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, add_zero,
    map_add, map_smul, map_sub, 𝔼.tower (by omega : t + 1 ≤ t + 2)]
  rw [show t + 2 + 2 = t + 4 by omega, show t + 2 + 1 = t + 3 by omega,
    show t + 2 + 1 + 1 = t + 4 by omega, show t + 3 + 1 = t + 4 by omega] at *
  have hW2' := hW2
  rw [map_sub] at hW2'
  rw [hW2']
  funext ω
  have e3 := congrFun h3 ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub] at e3 ⊢
  field_simp
  linear_combination e3

/-! ### (2.4)–(2.5): the Giannoni–Woodford IS block with habit and `d = 2` -/

omit 𝔼 in
/-- Woodford (2003), p. 333 (used in (2.4)): the habit-adjusted gap
`x̃_s = (x_s − η x_{s−1}) − βη E_s(x_{s+1} − η x_s)` (for `s ≥ 1`). -/
def xTilde (𝔼 : ExpectationSystem Ω) (β η : ℝ) (x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun s => (x s - η • x (s - 1)) - (β * η) • 𝔼.E s (x (s + 1) - η • x s)

/-- Woodford (2003), eq. (2.4), p. 348 (**derived**, conditional on the habit analogue of (1.6)
from §1.2): if `E_t λ̂_{t+2} = −ϕ E_t(x̃_{t+2} − z_{t+2})` for an exogenous composite `z`
(expenditure predetermined two quarters) and the natural rate is `r̂ⁿ_s = ϕ E_s(z_s − z_{s+1})`,
then along a solution of the bond-pricing relation
`E_t x̃_{t+2} = E_t x̃_{t+3} − ϕ⁻¹ E_t(î_{t+2} − π_{t+3} − r̂ⁿ_{t+2})`. -/
theorem eq24 {ϕ : ℝ} (hϕ : ϕ ≠ 0) {xt z i infl lam rn : ℕ → Ω → ℝ}
    (hlam : LamEq 𝔼 i infl lam)
    (hmu : ∀ t, 𝔼.E t (lam (t + 2)) = -ϕ • 𝔼.E t (xt (t + 2) - z (t + 2)))
    (hrn : ∀ s, rn s = ϕ • 𝔼.E s (z s - z (s + 1))) (t : ℕ) :
    𝔼.E t (xt (t + 2)) = 𝔼.E t (xt (t + 3)) -
      ϕ⁻¹ • 𝔼.E t (i (t + 2) - infl (t + 3) - rn (t + 2)) := by
  have hL := congrArg (𝔼.E t) (hlam (t + 2))
  simp only [map_add, map_sub, 𝔼.tower (by omega : t ≤ t + 2)] at hL
  have h1 := congrArg (𝔼.E t) (hmu (t + 1))
  simp only [map_smul, map_sub, 𝔼.tower (Nat.le_succ t)] at h1
  rw [show t + 1 + 2 = t + 3 by omega] at h1
  have h0 := hmu t
  have hR : 𝔼.E t (rn (t + 2)) = ϕ • (𝔼.E t (z (t + 2)) - 𝔼.E t (z (t + 3))) := by
    simp only [hrn, map_smul, map_sub, 𝔼.tower (by omega : t ≤ t + 2)]
  rw [show t + 2 + 1 = t + 3 by omega] at hL
  funext ω
  have eL := congrFun hL ω
  have e1 := congrFun h1 ω
  have e0 := congrFun h0 ω
  have eR := congrFun hR ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub] at eL e1 e0 eR ⊢
  rw [e0, e1] at eL
  field_simp
  linear_combination eL - eR

omit 𝔼 in
/-- Woodford (2003), (2.5), p. 348 (the composite disturbances the identity (2.5) requires; the
book does not define `ğ`, `Ỹⁿ`): `ğ_s = (1 + βη²) g_s − η g_{s−1}`. -/
def gBreve (β η : ℝ) (g : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun s => (1 + β * η ^ 2) • g s - η • g (s - 1)

omit 𝔼 in
/-- Woodford (2003), (2.5), p. 348: `Ỹⁿ_s = (1 + βη²) Ŷⁿ_s − η Ŷⁿ_{s−1} − βη E_s Ŷⁿ_{s+1}`. -/
def YnTilde (𝔼 : ExpectationSystem Ω) (β η : ℝ) (Yn : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun s => (1 + β * η ^ 2) • Yn s - η • Yn (s - 1) - (β * η) • 𝔼.E s (Yn (s + 1))

/-- Woodford (2003), eq. (2.5), p. 348 (**as an identity**): if interest-sensitive expenditure
`c = Ŷ − g` is predetermined two quarters (`c_{s+2}` known at `s`, `c_1` known at `0`) and
`x = Ŷ − Ŷⁿ`, then with `ğ`, `Ỹⁿ` as above
`x̃_{t+2} = E_t x̃_{t+2} + (ğ − Ỹⁿ)_{t+2} − E_t(ğ − Ỹⁿ)_{t+2}
  − βη[E_{t+2}(x_{t+3} + Ŷⁿ_{t+3}) − E_t(x_{t+3} + Ŷⁿ_{t+3})]`. -/
theorem eq25 {β η : ℝ} {x Y g Yn : ℕ → Ω → ℝ} (hxa : 𝔼.Adapted x)
    (hx : ∀ s, x s = Y s - Yn s)
    (hc : ∀ s, 𝔼.E s (Y (s + 2) - g (s + 2)) = Y (s + 2) - g (s + 2))
    (hc0 : 𝔼.E 0 (Y 1 - g 1) = Y 1 - g 1) (t : ℕ) :
    xTilde 𝔼 β η x (t + 2) = 𝔼.E t (xTilde 𝔼 β η x (t + 2)) +
      ((gBreve β η g (t + 2) - YnTilde 𝔼 β η Yn (t + 2)) -
        𝔼.E t (gBreve β η g (t + 2) - YnTilde 𝔼 β η Yn (t + 2))) -
      (β * η) • (𝔼.E (t + 2) (x (t + 3) + Yn (t + 3)) - 𝔼.E t (x (t + 3) + Yn (t + 3))) := by
  have hc1 : 𝔼.E t (Y (t + 1) - g (t + 1)) = Y (t + 1) - g (t + 1) := by
    cases t with
    | zero => exact hc0
    | succ t =>
      have := hc t
      rw [show t + 2 = t + 1 + 1 by omega] at this
      exact ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) this
  have hc2 := hc t
  have hsub : t + 2 - 1 = t + 1 := by omega
  have hE2 : 𝔼.E (t + 2) (x (t + 2 + 1) - η • x (t + 2)) = 𝔼.E (t + 2) (x (t + 3) + Yn (t + 3)) -
      𝔼.E (t + 2) (Yn (t + 3)) - η • x (t + 2) := by
    rw [map_sub, map_smul, hxa, map_add, show t + 2 + 1 = t + 3 by omega]
    abel
  -- the decomposition `x̃ = [(1 + βη²) c − η c₋₁] + (ğ − Ỹⁿ) − βη E(x₊ + Ŷⁿ₊)`
  have hdec : xTilde 𝔼 β η x (t + 2) = ((1 + β * η ^ 2) • (Y (t + 2) - g (t + 2)) -
      η • (Y (t + 1) - g (t + 1))) + (gBreve β η g (t + 2) - YnTilde 𝔼 β η Yn (t + 2)) -
      (β * η) • 𝔼.E (t + 2) (x (t + 3) + Yn (t + 3)) := by
    unfold xTilde
    rw [hE2, hsub]
    funext ω
    simp only [gBreve, YnTilde, hsub, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      show t + 2 + 1 = t + 3 by omega, hx (t + 2), hx (t + 1)]
    ring
  have hE := congrArg (𝔼.E t) hdec
  funext ω
  have e1 := congrFun hdec ω
  have e2 := congrFun hE ω
  have e3 := congrFun hc1 ω
  have e4 := congrFun hc2 ω
  simp only [map_add, map_sub, map_smul, 𝔼.tower (by omega : t ≤ t + 2), Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 e4 ⊢
  linear_combination e1 - e2 - (1 + β * η ^ 2) * e4 + η * e3

/-- Woodford (2003), (2.5), p. 348: the last bracket of (2.5) is
`(c_{t+3} − E_t c_{t+3}) + (E_{t+2} g_{t+3} − E_t g_{t+3})`, with `c = Ŷ − g`; it contains the
revision of expenditure decided at `t + 1`. -/
theorem eq25_bracket {x Y g Yn : ℕ → Ω → ℝ} (hx : ∀ s, x s = Y s - Yn s)
    (hc : ∀ s, 𝔼.E s (Y (s + 2) - g (s + 2)) = Y (s + 2) - g (s + 2)) (t : ℕ) :
    𝔼.E (t + 2) (x (t + 3) + Yn (t + 3)) - 𝔼.E t (x (t + 3) + Yn (t + 3)) =
      ((Y (t + 3) - g (t + 3)) - 𝔼.E t (Y (t + 3) - g (t + 3))) +
        (𝔼.E (t + 2) (g (t + 3)) - 𝔼.E t (g (t + 3))) := by
  have hk : 𝔼.E (t + 2) (Y (t + 3) - g (t + 3)) = Y (t + 3) - g (t + 3) := by
    have := hc (t + 1)
    rw [show t + 1 + 2 = t + 3 by omega] at this
    exact ForwardSolution.E_of_known 𝔼 (by omega) this
  have hY : x (t + 3) + Yn (t + 3) = (Y (t + 3) - g (t + 3)) + g (t + 3) := by
    rw [hx]; abel
  rw [hY, map_add, map_add, hk]
  abel

/-- Woodford (2003), p. 348 (**"a purely exogenous term" is imprecise**): on the coin-flip tree,
expenditure `c_s = ε_{s−2}` (the coin shock, chosen two periods ahead) satisfies the
two-period predetermination of `eq25`, yet the revision `c_3 − E_0 c_3` that enters the last
bracket of (2.5) (`eq25_bracket`, `t = 0`) is `±1`, not `0`; it is a revision of an endogenous
expenditure decision, not an exogenous disturbance. -/
theorem eq25_bracket_not_forecastable :
    (∀ s, ExpectationsFiniteTree.coinSystem.E s
        (ExpectationsFiniteTree.coinAR1 0 (s + 2 - 2)) =
          ExpectationsFiniteTree.coinAR1 0 (s + 2 - 2)) ∧
      ExpectationsFiniteTree.coinAR1 0 (3 - 2) (true, true) -
        ExpectationsFiniteTree.coinSystem.E 0 (ExpectationsFiniteTree.coinAR1 0 (3 - 2))
          (true, true) = 1 := by
  have hAR := ExpectationsFiniteTree.coinAR1_isAR1 0
  have hnd := ExpectationsFiniteTree.coinAR1_nondegenerate 0
  refine ⟨fun s => ?_, ?_⟩
  · rw [Nat.add_sub_cancel]
    exact hAR.1 s
  · simp only [show (3 : ℕ) - 2 = 1 from rfl, hnd.2.2, hnd.1, Pi.zero_apply, sub_zero]

/-! ### (2.6)–(2.7): price and wage inflation with indexation -/

/-- Woodford (2003), p. 348 (tool): the expectation system shifted by `n` dates,
`E'_s = E_{s+n}`. -/
def shiftSystem (n : ℕ) : ExpectationSystem Ω where
  E := fun s => 𝔼.E (s + n)
  const := fun s c => 𝔼.const (s + n) c
  mono := fun s _ _ h => 𝔼.mono (s + n) h
  tower := fun h x => 𝔼.tower (by omega) x
  known := fun h x => 𝔼.known (by omega) x

omit 𝔼 in
/-- Woodford (2003), eq. (2.6), p. 348, at date `t + 2`:
`π_{t+2} − γ_p π_{t+1} = ξ_p ω_p E_{t+1} x_{t+2} + ξ_p E_{t+1}(w_{t+2} − wⁿ_{t+2})
  + β E_{t+1}(π_{t+3} − γ_p π_{t+2})`. -/
def Eq26 (𝔼 : ExpectationSystem Ω) (ξp ωp β γp : ℝ) (infl x w wn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl (t + 2) - γp • infl (t + 1) = (ξp * ωp) • 𝔼.E (t + 1) (x (t + 2)) +
    ξp • 𝔼.E (t + 1) (w (t + 2) - wn (t + 2)) +
    β • 𝔼.E (t + 1) (infl (t + 3) - γp • infl (t + 2))

omit 𝔼 in
/-- Woodford (2003), eq. (2.7), p. 348, at date `t + 2`:
`π^w_{t+2} − γ_w π_{t+1} = ξ_w E_{t+1}(ω_w x_{t+2} + ϕ x̃_{t+2}) − ξ_w E_{t+1} μ_{t+2}
  + ξ_w E_{t+1}(wⁿ_{t+2} − w_{t+2}) + β E_{t+1}(π^w_{t+3} − γ_w π_{t+2})`. -/
def Eq27 (𝔼 : ExpectationSystem Ω) (ξw ωw ϕ β γw : ℝ) (inflw infl x xt m w wn : ℕ → Ω → ℝ) :
    Prop :=
  ∀ t, inflw (t + 2) - γw • infl (t + 1) =
    ξw • 𝔼.E (t + 1) (ωw • x (t + 2) + ϕ • xt (t + 2)) - ξw • 𝔼.E (t + 1) (m (t + 2)) +
    ξw • 𝔼.E (t + 1) (wn (t + 2) - w (t + 2)) +
    β • 𝔼.E (t + 1) (inflw (t + 3) - γw • infl (t + 2))

omit 𝔼 in
/-- Woodford (2003), p. 348: the identity linking the log real wage to wage and price
inflation, `w_{s+1} = w_s + π^w_{s+1} − π_{s+1}`. -/
def RealWageId (w inflw infl : ℕ → Ω → ℝ) : Prop :=
  ∀ s, w (s + 1) = w s + inflw (s + 1) - infl (s + 1)

/-- Woodford (2003), p. 348: under (2.6), quasi-differenced inflation `π_{t+2} − γ_p π_{t+1}` is
known at `t + 1` (price revisions are predetermined one quarter). -/
theorem eq26_predetermined {ξp ωp β γp : ℝ} {infl x w wn : ℕ → Ω → ℝ}
    (h : Eq26 𝔼 ξp ωp β γp infl x w wn) (t : ℕ) :
    𝔼.E (t + 1) (infl (t + 2) - γp • infl (t + 1)) = infl (t + 2) - γp • infl (t + 1) := by
  rw [h t]
  simp only [map_add, map_smul, 𝔼.E_E_self]

/-- Woodford (2003), (2.6), p. 348 (**the unique bounded solution**): with `0 ≤ β < 1` and a
bounded driving term, quasi-differenced inflation is the forward sum
`π_{t+2} − γ_p π_{t+1} = ∑_k βᵏ E_{t+1} v_{t+1+k}`,
`v_s = ξ_p E_s[ω_p x_{s+1} + w_{s+1} − wⁿ_{s+1}]`, for every bounded inflation process. -/
theorem eq26_forward_unique {ξp ωp β γp M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {infl x w wn : ℕ → Ω → ℝ} (h : Eq26 𝔼 ξp ωp β γp infl x w wn) (hinfl : BoundedProc infl)
    (hv : ∀ s ω, |ξp • 𝔼.E s ((ωp • x (s + 1)) + (w (s + 1) - wn (s + 1))) ω| ≤ M) :
    (fun t => infl (t + 2) - γp • infl (t + 1)) =
      (shiftSystem 𝔼 1).forwardSeries β
        (fun s => ξp • 𝔼.E (s + 1) ((ωp • x (s + 2)) + (w (s + 2) - wn (s + 2)))) := by
  set 𝔼' := shiftSystem 𝔼 1
  set u : ℕ → Ω → ℝ := fun s => ξp • 𝔼.E (s + 1) ((ωp • x (s + 2)) + (w (s + 2) - wn (s + 2)))
  have hu : ∀ t ω, |u t ω| ≤ M := fun t ω => hv (t + 1) ω
  have hua : 𝔼'.Adapted u := by
    intro t
    change 𝔼.E (t + 1) _ = _
    simp only [u, map_smul, 𝔼.E_E_self]
  have hz : ∀ t, (fun t => infl (t + 2) - γp • infl (t + 1)) t =
      β • 𝔼'.E t ((fun t => infl (t + 2) - γp • infl (t + 1)) (t + 1)) + u t := by
    intro t
    change infl (t + 2) - γp • infl (t + 1) =
      β • 𝔼.E (t + 1) (infl (t + 1 + 2) - γp • infl (t + 1 + 1)) + u t
    rw [h t, show t + 1 + 2 = t + 3 by omega, show t + 1 + 1 = t + 2 by omega]
    simp only [u, map_add, map_smul]
    module
  obtain ⟨K, hK⟩ := hinfl
  exact 𝔼'.eq_forwardSeries hβ0 hβ1 hu hua hz ⟨K + |γp| * K, fun t ω => by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add (hK _ ω) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hK _ ω) (abs_nonneg _)⟩

/-- Woodford (2003), (2.7), p. 348 and Table 5.4 ("flexible wages, `ξ_w⁻¹ = 0`"): for
`ξ_w ≠ 0`, (2.7) is equivalent to
`ξ_w⁻¹[π^w_{t+2} − γ_w π_{t+1} − β E_{t+1}(π^w_{t+3} − γ_w π_{t+2})]
  = E_{t+1}[ω_w x_{t+2} + ϕ x̃_{t+2} − μ_{t+2} + wⁿ_{t+2} − w_{t+2}]`; the restricted model
`ξ_w⁻¹ = 0` is the flexible-wage condition that the expected real wage equals the expected
desired wage `wⁿ + ω_w x + ϕ x̃ − μ`. -/
theorem eq27_iff {ξw ωw ϕ β γw : ℝ} (hξ : ξw ≠ 0) {inflw infl x xt m w wn : ℕ → Ω → ℝ} :
    Eq27 𝔼 ξw ωw ϕ β γw inflw infl x xt m w wn ↔ ∀ t,
      ξw⁻¹ • (inflw (t + 2) - γw • infl (t + 1) -
        β • 𝔼.E (t + 1) (inflw (t + 3) - γw • infl (t + 2))) =
      𝔼.E (t + 1) (ωw • x (t + 2) + ϕ • xt (t + 2) - m (t + 2) + (wn (t + 2) - w (t + 2))) := by
  refine forall_congr' fun t => ?_
  simp only [map_add, map_sub]
  constructor
  · intro h
    rw [h]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    field_simp at e
    linear_combination e

/-! ### Table 5.1 (Rotemberg–Woodford) -/

/-- Woodford (2003), fn. 19, p. 341: with labour elasticity `.75` and markup `1.15`, the labour
share is `.75/1.15 ≈ .652`, "about .65". -/
theorem table51_labour_share : (0.652 : ℝ) < 0.75 / 1.15 ∧ (0.75 : ℝ) / 1.15 < 0.653 := by
  norm_num

/-- Woodford (2003), p. 341: `f(h) = h^{.75}` gives `ω_p = (1 − .75)/.75 = 1/3 ≈ .33`. -/
theorem table51_omega_p : (1 - (0.75 : ℝ)) / 0.75 = 1 / 3 := by norm_num

/-- Woodford (2003), p. 342: `ω_mc = ω + σ⁻¹ = .47 + .16 = .63` and `ω = ω_w + ω_p`,
`ω_w = .47 − .33 = .14`. -/
theorem table51_omega : (0.47 : ℝ) + 0.16 = 0.63 ∧ (0.47 : ℝ) - 0.33 = 0.14 := by norm_num

/-- Woodford (2003), p. 342: `ν = ω_w/φ_h = .75 × .14 = .105`, printed "0.11". -/
theorem table51_nu : (0.75 : ℝ) * 0.14 = 0.105 := by norm_num

/-- Woodford (2003), p. 342: `α = .66` implies a mean time between price changes of
`1/(1 − α) ≈ 2.94`, "three quarters". -/
theorem table51_duration : (2.9 : ℝ) < 1 / (1 - 0.66) ∧ 1 / (1 - (0.66 : ℝ)) < 3 := by
  norm_num

/-- Woodford (2003), p. 342: `ψ = .88` and `α = .66` imply `ϕ = 1/(1 + αψ) ≈ .6326`, "ϕ = .63";
conversely `ϕ = .63` gives `ψ = .37/(.63 · .66) ≈ .890` (rounding). -/
theorem table51_phi :
    (0.632 : ℝ) < 1 / (1 + 0.66 * 0.88) ∧ 1 / (1 + (0.66 : ℝ) * 0.88) < 0.633 ∧
      (0.889 : ℝ) < psiRW 0.66 0.63 ∧ psiRW 0.66 0.63 < 0.890 := by
  unfold psiRW
  norm_num

omit 𝔼 in
/-- Woodford (2003), p. 342 and Ch. 3 (2.12): `κ = ((1 − α)(1 − αβ)/α) ζ`, i.e. `ξ ζ` with the
Calvo coefficient `ξ = Predetermined.calvoXi α β`. -/
noncomputable def kappaRW (α β ζ : ℝ) : ℝ := calvoXi α β * ζ

omit 𝔼 in
/-- Woodford (2003), p. 342: the real-rigidity measure `ζ = ω_mc/(1 + ωθ)`. -/
noncomputable def zetaRW (ωmc ω θ : ℝ) : ℝ := ωmc / (1 + ω * θ)

/-- Woodford (2003), p. 342 (**survey error 11 confirmed**): with `ω_mc = .63`, `ω = .47`,
`θ = 7.88` the real rigidity is `ζ ≈ .1339`, not the printed `.14`. -/
theorem table51_zeta_from_theta :
    (0.1339 : ℝ) < zetaRW 0.63 0.47 7.88 ∧ zetaRW 0.63 0.47 7.88 < 0.134 := by
  unfold zetaRW
  norm_num

/-- Woodford (2003), p. 342 (survey error 11): `ζ = .14` (with `α = .66`, `β = .99`) gives
`κ ≈ .0250`, which does not round to the printed `κ = .024`; `θ = 7.88`'s `ζ` gives
`κ ≈ .0239`, which does. -/
theorem table51_kappa_from_zeta :
    (0.02499 : ℝ) < kappaRW 0.66 0.99 0.14 ∧ kappaRW 0.66 0.99 0.14 < 0.0250 ∧
      (0.0235 : ℝ) < kappaRW 0.66 0.99 (zetaRW 0.63 0.47 7.88) ∧
      kappaRW 0.66 0.99 (zetaRW 0.63 0.47 7.88) < 0.0245 := by
  unfold kappaRW calvoXi zetaRW
  norm_num

/-- Woodford (2003), p. 342 (survey error 11): `ζ = .14` would require `θ ≈ 7.447`, and
`κ = .024` exactly gives `ζ ≈ .1344`. -/
theorem table51_theta_from_zeta :
    (7.44 : ℝ) < (0.63 / 0.14 - 1) / 0.47 ∧ (0.63 / 0.14 - 1) / (0.47 : ℝ) < 7.45 ∧
      (0.1344 : ℝ) < 0.024 / ((1 - 0.66) * (1 - 0.66 * 0.99) / 0.66) ∧
      (0.024 : ℝ) / ((1 - 0.66) * (1 - 0.66 * 0.99) / 0.66) < 0.1345 := by
  norm_num

/-- Woodford (2003), p. 342 (survey error 11, exact bounds): for every `θ` that rounds to `7.88`
(`7.875 ≤ θ < 7.885`), `ζ = .63/(1 + .47θ)` lies in `(.1338, .1341)`, so it rounds to `.13`. -/
theorem table51_zeta_rounds_013 {θ : ℝ} (h1 : 7.875 ≤ θ) (h2 : θ < 7.885) :
    (0.1338 : ℝ) < zetaRW 0.63 0.47 θ ∧ zetaRW 0.63 0.47 θ < 0.1341 := by
  unfold zetaRW
  have hpos : (0 : ℝ) < 1 + 0.47 * θ := by linarith
  constructor
  · rw [lt_div_iff₀ hpos]; nlinarith
  · rw [div_lt_iff₀ hpos]; nlinarith

/-- Woodford (2003), p. 342: `θ = 7.88` gives `(θ − 1)⁻¹ ≈ .1453` (printed `.15`) and a markup
`θ/(θ − 1) < 1.15` ("less than 15%"). -/
theorem table51_markup :
    (0.145 : ℝ) < 1 / (7.88 - 1) ∧ 1 / ((7.88 : ℝ) - 1) < 0.146 ∧
      (7.88 : ℝ) / (7.88 - 1) < 1.15 := by
  norm_num

/-! ### Table 5.2 (Amato–Laubach) -/

/-- Woodford (2003), Table 5.2 and Ch. 3 (`κ_p = ξ_p ω_p`, `κ_w = ξ_w(ω_w + σ⁻¹)`):
`.058 × .33 ≈ .0191` (printed `.019`) and `.066 × (.27 + .26) ≈ .0350` (printed `.035`). -/
theorem table52_kappas :
    (0.019 : ℝ) < 0.058 * 0.33 ∧ (0.058 : ℝ) * 0.33 < 0.0195 ∧
      (0.0345 : ℝ) < 0.066 * (0.27 + 0.26) ∧ (0.066 : ℝ) * (0.27 + 0.26) < 0.0355 := by
  norm_num

/-! ### Table 5.3 (Giannoni–Woodford) -/

/-- Woodford (2003), p. 351: the Frisch elasticity `ν⁻¹ = 1/14.7 ≈ .068` ("only 0.07"). -/
theorem table53_frisch : (0.065 : ℝ) < 1 / 14.7 ∧ 1 / (14.7 : ℝ) < 0.07 := by norm_num

/-- Woodford (2003), Table 5.3: `ω_w = ν φ_h = 14.7/.75 = 19.6`. -/
theorem table53_omega_w : (14.7 : ℝ) / 0.75 = 19.6 := by norm_num

/-- Woodford (2003), p. 351: the gross markups `μ_w = 1 + (θ_w − 1)⁻¹ = 1.54`,
`μ_p = 1 + (θ_p − 1)⁻¹ = 1.004`. -/
theorem table53_markups : (1 : ℝ) + 0.54 = 1.54 ∧ (1 : ℝ) + 0.004 = 1.004 := by norm_num

/-- Woodford (2003), p. 351: `ϕ = .75` gives `ϕ⁻¹ ≈ 1.33` ("1.3"), and Table 5.3
`κ_p = ξ_p ω_p = .0020 × .33 = .00066` (printed `.0007`). -/
theorem table53_phi_kappa :
    (1.33 : ℝ) < 1 / 0.75 ∧ 1 / (0.75 : ℝ) < 1.34 ∧ (0.0020 : ℝ) * 0.33 = 0.00066 := by
  norm_num

/-! ### Survey error 8: rule (1.12) and the long-run responses of fn. 35 -/

omit 𝔼 in
/-- Woodford (2003), eq. (1.12), p. 327 (= Ch. 4 (2.35)), on deviations from target
(`ĩ = î − π̄`, `π̃ = π − π̄`, `x̃ = x − x̄`):
`ĩ_{t+1} = ρ ĩ_t + φ_π(π̃_{t+1} − ρ π̃_t) + (φ_x/4)(x̃_{t+1} − ρ x̃_t) + ε_{t+1}`. -/
def Rule112 (ρ φπ φx : ℝ) (it pt xt ε : ℕ → Ω → ℝ) : Prop :=
  ∀ t, it (t + 1) = ρ • it t + φπ • (pt (t + 1) - ρ • pt t) +
    (φx / 4) • (xt (t + 1) - ρ • xt t) + ε (t + 1)

omit 𝔼 in
/-- Woodford (2003), Ch. 4, p. 281: the intercept residual `v = ĩ − φ_π π̃ − (φ_x/4) x̃`. -/
noncomputable def resid112 (φπ φx : ℝ) (it pt xt : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => it t - φπ • pt t - (φx / 4) • xt t

omit 𝔼 in
/-- Woodford (2003), p. 327 and Ch. 4, p. 281 (**(1.12) is (1.14) with an AR(1) intercept**):
(1.12) holds iff `v_{t+1} = ρ v_t + ε_{t+1}` for `v = ĩ − φ_π π̃ − (φ_x/4) x̃`. -/
theorem rule112_iff (ρ φπ φx : ℝ) (it pt xt ε : ℕ → Ω → ℝ) :
    Rule112 ρ φπ φx it pt xt ε ↔ ∀ t, resid112 φπ φx it pt xt (t + 1) =
      ρ • resid112 φπ φx it pt xt t + ε (t + 1) := by
  unfold Rule112 resid112
  refine forall_congr' fun t => ?_
  constructor
  · intro h; rw [h]; module
  · intro h
    have : it (t + 1) = (it (t + 1) - φπ • pt (t + 1) - (φx / 4) • xt (t + 1)) +
        φπ • pt (t + 1) + (φx / 4) • xt (t + 1) := by abel
    rw [this, h]; module

omit 𝔼 in
/-- Woodford (2003), p. 327: the intercept path `ī_t = π̄ + v_t` driven by `v_0 = v⁰`,
`v_{t+1} = ρ v_t + ε_{t+1}`. -/
noncomputable def vpath (ρ : ℝ) (v0 : Ω → ℝ) (ε : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => v0
  | t + 1 => ρ • vpath ρ v0 ε t + ε (t + 1)

/-- Woodford (2003), p. 327: an equilibrium of the basic model (1.12)–(1.13) of Chapter 4 under
rule (1.12) with initial residual `v⁰` (the interest rate `î` is part of the solution). -/
def Eqm112 (β σ κ φπ φx ρ πbar : ℝ) (rn ε : ℕ → Ω → ℝ) (v0 : Ω → ℝ)
    (infl x i : ℕ → Ω → ℝ) : Prop :=
  IS112 𝔼 σ x i infl rn ∧ NKPCurve 𝔼 β κ infl x ∧
    Rule112 ρ φπ φx (fun t => i t - fun _ => πbar) (fun t => infl t - fun _ => πbar)
      (fun t => x t - fun _ => xbar β κ πbar) ε ∧
    resid112 φπ φx (fun t => i t - fun _ => πbar) (fun t => infl t - fun _ => πbar)
      (fun t => x t - fun _ => xbar β κ πbar) 0 = v0

/-- Woodford (2003), p. 327 and Ch. 4, p. 281: the equilibria under (1.12) are exactly the
equilibria under the Taylor rule (1.14) with intercept `ī = π̄ + v`, `v = vpath ρ v⁰ ε`. -/
theorem eqm112_iff {β σ κ φπ φx ρ πbar : ℝ} (rn ε : ℕ → Ω → ℝ) (v0 : Ω → ℝ)
    (infl x i : ℕ → Ω → ℝ) :
    Eqm112 𝔼 β σ κ φπ φx ρ πbar rn ε v0 infl x i ↔
      i = taylorRate β κ φπ φx πbar (fun t => (fun _ => πbar) + vpath ρ v0 ε t) infl x ∧
        TaylorEqm 𝔼 β σ κ φπ φx πbar rn (fun t => (fun _ => πbar) + vpath ρ v0 ε t) infl x := by
  set r := resid112 φπ φx (fun t => i t - fun _ => πbar) (fun t => infl t - fun _ => πbar)
    (fun t => x t - fun _ => xbar β κ πbar) with hr
  have hri : ∀ t, i t = taylorRate β κ φπ φx πbar (fun s => (fun _ => πbar) + r s) infl x t := by
    intro t
    simp only [hr, resid112, taylorRate]
    abel
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hv : r = vpath ρ v0 ε := by
      funext t
      induction t with
      | zero => exact h4
      | succ t ih =>
        have h5 := (rule112_iff _ _ _ _ _ _ _).mp h3 t
        rw [← hr] at h5
        rw [h5, ih]
        rfl
    have hi : i = taylorRate β κ φπ φx πbar (fun t => (fun _ => πbar) + vpath ρ v0 ε t) infl x := by
      funext t; rw [hri t, hv]
    exact ⟨hi, by rw [← hi]; exact h1, h2⟩
  · rintro ⟨hi, h1, h2⟩
    have hv : r = vpath ρ v0 ε := by
      funext t
      simp only [hr, resid112, hi, taylorRate]
      abel_nf
    refine ⟨by rw [hi]; exact h1, h2, ?_, ?_⟩
    · rw [rule112_iff]
      intro t
      change r (t + 1) = ρ • r t + ε (t + 1)
      rw [hv]; rfl
    · change r 0 = v0
      rw [hv]; rfl

/-- Woodford (2003), p. 327 (determinacy under (1.12), genuine sense): for every bounded adapted
natural rate `r̂ⁿ`, shock `ε` and initial residual `v⁰` known at `0`, there is exactly one bounded
adapted `(π, x)` that is an equilibrium under (1.12) for some interest-rate path. -/
def Determinate112 (β σ κ φπ φx ρ πbar : ℝ) : Prop :=
  ∀ (rn ε : ℕ → Ω → ℝ) (v0 : Ω → ℝ), BoundedProc rn → BoundedProc ε → 𝔼.Adapted rn →
    𝔼.Adapted ε → 𝔼.E 0 v0 = v0 → (∃ K, ∀ ω, |v0 ω| ≤ K) →
    ∃! p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), BoundedProc p.1 ∧ BoundedProc p.2 ∧
      𝔼.Adapted p.1 ∧ 𝔼.Adapted p.2 ∧ ∃ i, Eqm112 𝔼 β σ κ φπ φx ρ πbar rn ε v0 p.1 p.2 i

omit 𝔼 in
/-- Woodford (2003), p. 327 (tool): the intercept path is bounded for `|ρ| < 1`. -/
theorem vpath_bounded {ρ K Kε : ℝ} (hρ : |ρ| < 1) {v0 : Ω → ℝ} {ε : ℕ → Ω → ℝ}
    (hv0 : ∀ ω, |v0 ω| ≤ K) (hε : ∀ t ω, |ε t ω| ≤ Kε) :
    BoundedProc (vpath ρ v0 ε) := by
  have h1 : 0 < 1 - |ρ| := by linarith
  set B := |K| + |Kε| / (1 - |ρ|) with hB
  have hq : 0 ≤ |Kε| / (1 - |ρ|) := div_nonneg (abs_nonneg _) h1.le
  have hkey : |Kε| = (1 - |ρ|) * (|Kε| / (1 - |ρ|)) := by field_simp
  refine ⟨B, fun t ω => ?_⟩
  induction t with
  | zero => exact (hv0 ω).trans ((le_abs_self K).trans (by linarith))
  | succ t ih =>
    simp only [vpath, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have e1 : |ρ| * |vpath ρ v0 ε t ω| ≤ |ρ| * B :=
      mul_le_mul_of_nonneg_left ih (abs_nonneg _)
    have e2 : |ε (t + 1) ω| ≤ |Kε| := (hε _ ω).trans (le_abs_self _)
    have e4 : |ρ| * B + |Kε| ≤ B := by
      have h5 : 0 ≤ (1 - |ρ|) * |K| := mul_nonneg h1.le (abs_nonneg _)
      have h6 : B - |ρ| * B = (1 - |ρ|) * |K| + (1 - |ρ|) * (|Kε| / (1 - |ρ|)) := by
        rw [hB]; ring
      linarith
    linarith

/-- Woodford (2003), p. 327 (tool): the intercept path is adapted when `v⁰` is known at `0` and
`ε` is adapted. -/
theorem vpath_adapted {ρ : ℝ} {v0 : Ω → ℝ} {ε : ℕ → Ω → ℝ} (hv0 : 𝔼.E 0 v0 = v0)
    (hε : 𝔼.Adapted ε) : 𝔼.Adapted (vpath ρ v0 ε) := by
  intro t
  induction t with
  | zero => exact hv0
  | succ t ih =>
    simp only [vpath, map_add, map_smul, hε (t + 1),
      ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih]

/-- Woodford (2003), p. 327: being an equilibrium under (1.12) for some interest-rate path is
being a Taylor-rule equilibrium with intercept `π̄ + vpath ρ v⁰ ε`. -/
theorem exists_eqm112_iff {β σ κ φπ φx ρ πbar : ℝ} (rn ε : ℕ → Ω → ℝ) (v0 : Ω → ℝ)
    (infl x : ℕ → Ω → ℝ) :
    (∃ i, Eqm112 𝔼 β σ κ φπ φx ρ πbar rn ε v0 infl x i) ↔
      TaylorEqm 𝔼 β σ κ φπ φx πbar rn (fun t => (fun _ => πbar) + vpath ρ v0 ε t) infl x := by
  constructor
  · rintro ⟨i, h⟩
    exact ((eqm112_iff 𝔼 rn ε v0 infl x i).mp h).2
  · intro h
    exact ⟨_, (eqm112_iff 𝔼 rn ε v0 infl x _).mpr ⟨rfl, h⟩⟩

/-- Woodford (2003), p. 327 with Ch. 4 Proposition 4.3 (**determinacy under (1.12)**): for
`|ρ| < 1` the rule (1.12) is determinate iff (2.7)/(1.14), `φ_π + (1 − β)φ_x/(4κ) > 1` — the
partial-adjustment form of (1.12) does not relax the Taylor principle on `φ_π, φ_x`. -/
theorem rule112_determinate_iff [Nonempty Ω] {β σ κ φπ φx ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hκ : 0 < κ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (hρ : |ρ| < 1) (πbar : ℝ) :
    Determinate112 𝔼 β σ κ φπ φx ρ πbar ↔ 1 < taylorLHS β κ φπ φx := by
  rw [← prop_4_3 𝔼 hβ0 hβ1 hσ hκ hφπ hφx πbar]
  constructor
  · intro hD R IB hR hIB haR haIB
    set v : ℕ → Ω → ℝ := fun t => IB t - fun _ => πbar with hv
    set ε : ℕ → Ω → ℝ := fun t => if t = 0 then 0 else v t - ρ • v (t - 1) with hε
    have hvp : vpath ρ (v 0) ε = v := by
      funext t
      induction t with
      | zero => rfl
      | succ t ih =>
        simp only [vpath]
        rw [ih]
        simp only [hε, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        abel
    have hIBeq : (fun t => (fun _ => πbar) + vpath ρ (v 0) ε t) = IB := by
      rw [hvp]; funext t; simp [hv]
    obtain ⟨MI, hMI⟩ := hIB
    have hvb : ∀ t ω, |v t ω| ≤ MI + |πbar| := fun t ω => by
      simp only [hv, Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (hMI t ω) le_rfl)
    have hεb : BoundedProc ε := ⟨(MI + |πbar|) + |ρ| * (MI + |πbar|), fun t ω => by
      simp only [hε]
      split_ifs
      · simp only [Pi.zero_apply, abs_zero]
        have := (abs_nonneg _).trans (hvb 0 ω)
        positivity
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        refine (abs_sub _ _).trans (add_le_add (hvb t ω) ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hvb _ ω) (abs_nonneg _)⟩
    have hva : 𝔼.Adapted v := fun t => by simp only [hv, map_sub, haIB t, 𝔼.const]
    have hεa : 𝔼.Adapted ε := fun t => by
      simp only [hε]
      split_ifs
      · exact map_zero _
      · simp only [map_sub, map_smul, hva t,
          ForwardSolution.E_of_known 𝔼 (Nat.sub_le t 1) (hva (t - 1))]
    have h := hD R ε (v 0) hR hεb haR hεa (hva 0) ⟨MI + |πbar|, hvb 0⟩
    simp only [exists_eqm112_iff, hIBeq] at h
    exact h
  · intro hM rn ε v0 hrn hε harn haε hv0 hv0b
    obtain ⟨K, hK⟩ := hv0b
    obtain ⟨Kε, hKε⟩ := hε
    obtain ⟨Kv, hKv⟩ := vpath_bounded (ρ := ρ) hρ hK hKε
    have hib : BoundedProc (fun t => (fun _ => πbar) + vpath ρ v0 ε t) :=
      ⟨|πbar| + Kv, fun t ω => (abs_add_le _ _).trans (add_le_add le_rfl (hKv t ω))⟩
    have hiba : 𝔼.Adapted (fun t => (fun _ => πbar) + vpath ρ v0 ε t) := fun t => by
      simp only [map_add, 𝔼.const, vpath_adapted 𝔼 hv0 haε t]
    have h := hM rn _ hrn hib harn hiba
    simp only [exists_eqm112_iff]
    exact h

/-- Woodford (2003), p. 368, Figure 5.8 and fn. 35 (**survey error 8 confirmed**): rule (1.12)
with `φ_π = .6`, `φ_x = .3`, `ρ = .7` and the Table 5.1 structure (`β = .99`, `κ = .024`,
`σ = 1/.16`) leaves equilibrium indeterminate (`.6 + .01·.3/.096 ≈ .63 < 1`), so it cannot
generate the unique responses plotted. -/
theorem fig58_rule112_indeterminate [Nonempty Ω] (πbar : ℝ) :
    ¬ Determinate112 𝔼 0.99 (1 / 0.16) 0.024 0.6 0.3 0.7 πbar := by
  rw [rule112_determinate_iff 𝔼 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [abs_of_pos])]
  unfold taylorLHS
  norm_num

/-- Woodford (2003), fn. 35 (the corrected reading): rule (1.12) with the Chapter 4 baseline
`φ_π = 2`, `φ_x = 1` and `ρ = .7` is determinate, and its long-run responses are `2` and `1`
(`rule112_longrun`). -/
theorem fig58_rule112_baseline_determinate [Nonempty Ω] (πbar : ℝ) :
    Determinate112 𝔼 0.99 (1 / 0.16) 0.024 2 1 0.7 πbar := by
  rw [rule112_determinate_iff 𝔼 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [abs_of_pos])]
  unfold taylorLHS
  norm_num

/-- Woodford (2003), p. 327 (**long-run responses under (1.12)**): for `ρ ≠ 1`, a constant path
`ĩ = I`, `π̃ = P`, `x̃ = X` with no shock satisfies (1.12),
`I = ρI + φ_π(P − ρP) + (φ_x/4)(X − ρX)`, iff `I = φ_π P + (φ_x/4) X`: the long-run response to
inflation is `φ_π` itself, not `φ_π/(1 − ρ)`. -/
theorem rule112_longrun {ρ φπ φx : ℝ} (hρ : ρ ≠ 1) (I P X : ℝ) :
    I = ρ * I + φπ * (P - ρ * P) + φx / 4 * (X - ρ * X) ↔ I = φπ * P + φx / 4 * X := by
  have h1 : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  constructor
  · intro h
    apply mul_left_cancel₀ h1
    linear_combination h
  · intro h
    rw [h]; ring

/-- Woodford (2003), Ch. 4 eq. (2.8), p. 255 (the rule whose long-run responses are
`Φ = φ/(1 − ρ)`): a constant path satisfies `I = ρI + φ_π P + (φ_x/4) X` iff
`I = (φ_π P + (φ_x/4) X)/(1 − ρ)`. -/
theorem rule28_longrun {ρ φπ φx : ℝ} (hρ : ρ ≠ 1) (I P X : ℝ) :
    I = ρ * I + φπ * P + φx / 4 * X ↔ I = (φπ * P + φx / 4 * X) / (1 - ρ) := by
  have h1 : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  rw [eq_div_iff h1]
  constructor <;> intro h <;> linarith

/-- Woodford (2003), fn. 35, p. 368 (survey error 8): `Φ_π = 2`, `Φ_x = 1` are the long-run
responses of rule (2.8) with `φ_π = .6`, `φ_x = .3`, `ρ = .7` (`.6/.3 = 2`, `.3/.3 = 1`), which
also satisfies the Proposition 4.4 condition (2.9) `.6 + .01·.3/.096 > 1 − .7`; under (1.12)
the same coefficients give long-run response `.6` to inflation (`rule112_longrun`). -/
theorem fn35_rule28_longrun :
    (0.6 : ℝ) / (1 - 0.7) = 2 ∧ (0.3 : ℝ) / (1 - 0.7) = 1 ∧
      1 - (0.7 : ℝ) < taylorLHS 0.99 0.024 0.6 0.3 ∧ (0.6 : ℝ) ≠ 2 := by
  unfold taylorLHS
  norm_num

/-! ### Proposition 4.4 of Chapter 4, sufficiency, and Figure 5.8 under rule (2.8)

Restated from the Woodford Chapter 4 project: Proposition C.1/C.2 root location
(`NeoWicksellianFramework.SchurCohn`), the Blanchard–Kahn sufficiency theorem with one
predetermined variable (`BlanchardKahn.determinate3_of`), and the sufficiency half of the
corrected Proposition 4.4 (`ThreeByThree.prop44`). The forward-system existence step uses
`ForwardSystems.fwd_existsUnique`; the shared vector tools are in `ForwardSystems`. -/

namespace Prop44

open ComplexConjugate
open scoped Matrix

/-! ### Proposition C.1 -/

/-- Woodford (2003), Prop. C.1, p. 670: both roots of `λ² − Tλ + D` lie strictly outside the
unit circle. -/
def BothOutside (T D : ℝ) : Prop := 1 < ‖root₁ T D‖ ∧ 1 < ‖root₂ T D‖

/-- Woodford (2003), Prop. C.1, (C.1)–(C.3), p. 670: Case I, `det A > 1`, `det A − tr A > −1`,
`det A + tr A > −1`. -/
def CaseI2 (T D : ℝ) : Prop := 1 < D ∧ -1 < D - T ∧ -1 < D + T

/-- Woodford (2003), Prop. C.1, (C.4)–(C.5), p. 671: Case II, `det A − tr A < −1`,
`det A + tr A < −1`. -/
def CaseII2 (T D : ℝ) : Prop := D - T < -1 ∧ D + T < -1

/-- Woodford (2003), Prop. C.1, proof, p. 671: for two real roots `u, v`, both lie outside the
unit circle iff Case I or Case II holds for `T = u + v`, `D = u v`. -/
theorem real_roots_iff (u v : ℝ) :
    (1 < |u| ∧ 1 < |v|) ↔ CaseI2 (u + v) (u * v) ∨ CaseII2 (u + v) (u * v) := by
  unfold CaseI2 CaseII2
  constructor
  · rintro ⟨hu, hv⟩
    rcases lt_abs.mp hu with hu | hu <;> rcases lt_abs.mp hv with hv | hv
    · left; refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
    · right; constructor <;> nlinarith
    · right; constructor <;> nlinarith
    · left; refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
    · have e1 : 0 < (u - 1) * (v - 1) := by nlinarith
      have e2 : 0 < (u + 1) * (v + 1) := by nlinarith
      by_contra hc
      have hc' : |u| ≤ 1 ∨ |v| ≤ 1 := by
        by_contra h
        push Not at h
        exact hc ⟨h.1, h.2⟩
      rcases hc' with hc' | hc'
      · obtain ⟨hl, hr⟩ := abs_le.mp hc'
        rcases eq_or_lt_of_le hr with hr | hr
        · subst hr; nlinarith
        rcases eq_or_lt_of_le hl with hl | hl
        · rw [← hl] at e2; nlinarith
        have hv1 : v < 1 := by nlinarith
        have hv2 : -1 < v := by nlinarith
        nlinarith
      · obtain ⟨hl, hr⟩ := abs_le.mp hc'
        rcases eq_or_lt_of_le hr with hr | hr
        · subst hr; nlinarith
        rcases eq_or_lt_of_le hl with hl | hl
        · rw [← hl] at e2; nlinarith
        have hu1 : u < 1 := by nlinarith
        have hu2 : -1 < u := by nlinarith
        nlinarith
    · have e1 : (u - 1) * (v - 1) < 0 := by nlinarith
      have e2 : (u + 1) * (v + 1) < 0 := by nlinarith
      rcases lt_or_ge 1 u with hu | hu
      · have hv : v < 1 := by nlinarith
        have hv' : v < -1 := by nlinarith
        exact ⟨lt_abs.mpr (Or.inl hu), lt_abs.mpr (Or.inr (by linarith))⟩
      · have hv : 1 < v := by
          rcases eq_or_lt_of_le hu with h | h
          · subst h; nlinarith
          · nlinarith
        have hu' : u < -1 := by nlinarith
        exact ⟨lt_abs.mpr (Or.inr (by linarith)), lt_abs.mpr (Or.inl hv)⟩

/-- **Proposition C.1** (Woodford (2003), p. 670): both roots of the characteristic polynomial
`λ² − Tλ + D` lie strictly outside the unit circle if and only if Case I or Case II holds.
Exact, with no boundary case excluded. -/
theorem bothOutside_iff_cases (T D : ℝ) : BothOutside T D ↔ CaseI2 T D ∨ CaseII2 T D := by
  unfold BothOutside
  by_cases h : 0 ≤ disc T D
  · obtain ⟨h1, h2⟩ := norm_root_of_nonneg h
    rw [h1, h2]
    have hs2 : Real.sqrt (disc T D) ^ 2 = T ^ 2 - 4 * D := by rw [Real.sq_sqrt h]; rfl
    have key := real_roots_iff ((T + Real.sqrt (disc T D)) / 2) ((T - Real.sqrt (disc T D)) / 2)
    have hsum : (T + Real.sqrt (disc T D)) / 2 + (T - Real.sqrt (disc T D)) / 2 = T := by ring
    have hprod : (T + Real.sqrt (disc T D)) / 2 * ((T - Real.sqrt (disc T D)) / 2) = D := by
      nlinarith [hs2]
    rw [hsum, hprod] at key
    exact key
  · have hneg : disc T D < 0 := not_le.mp h
    obtain ⟨h1, h2⟩ := normSq_root_of_neg hneg
    have hd : disc T D = T ^ 2 - 4 * D := rfl
    have hD0 : 0 < D := by nlinarith [sq_nonneg T]
    have n1 := norm_nonneg (root₁ T D)
    have n2 := norm_nonneg (root₂ T D)
    unfold CaseI2 CaseII2
    constructor
    · rintro ⟨r1, -⟩
      have hD1 : 1 < D := by nlinarith
      have hsq : T ^ 2 < (1 + D) ^ 2 := by nlinarith [sq_nonneg (1 - D)]
      have hT : |T| < 1 + D := abs_lt_of_sq_lt_sq hsq (by linarith)
      obtain ⟨hT1, hT2⟩ := abs_lt.mp hT
      left; exact ⟨hD1, by linarith, by linarith⟩
    · rintro (⟨hD1, -, -⟩ | ⟨e1, e2⟩)
      · constructor <;> nlinarith
      · exfalso; linarith

/-- Woodford (2003), Prop. C.1, p. 670 (the clean form, survey §4.1): both roots outside iff
`1 < |D|` and `|T| < |1 + D|`. -/
theorem bothOutside_iff_abs (T D : ℝ) : BothOutside T D ↔ 1 < |D| ∧ |T| < |1 + D| := by
  rw [bothOutside_iff_cases]
  unfold CaseI2 CaseII2
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
    · rw [abs_of_pos (by linarith : (0 : ℝ) < D), abs_of_pos (by linarith : (0 : ℝ) < 1 + D)]
      exact ⟨h1, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
    · rw [abs_of_neg (by linarith : D < 0), abs_of_neg (by linarith : 1 + D < 0)]
      exact ⟨by linarith, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  · rintro ⟨hD, hT⟩
    obtain ⟨hT1, hT2⟩ := abs_lt.mp hT
    rcases lt_abs.mp hD with hD | hD
    · rw [abs_of_pos (by linarith : (0 : ℝ) < 1 + D)] at hT1 hT2
      left; exact ⟨hD, by linarith, by linarith⟩
    · rw [abs_of_neg (by linarith : 1 + D < 0)] at hT1 hT2
      right; exact ⟨by linarith, by linarith⟩

/-- Woodford (2003), Prop. C.1, p. 670: both roots of `λ² − Tλ + D` outside the unit circle iff
`D ≠ 0` and both roots of the reciprocal polynomial `λ² − (T/D)λ + 1/D` (the eigenvalues of
`A⁻¹`) are inside (the core Schur–Cohn condition). -/
theorem bothOutside_iff_schurStable_inv (T D : ℝ) :
    BothOutside T D ↔ D ≠ 0 ∧ SchurStable (T / D) (1 / D) := by
  rw [bothOutside_iff_abs]
  unfold SchurStable
  constructor
  · rintro ⟨hD, hT⟩
    have hD0 : D ≠ 0 := by
      rintro rfl; norm_num at hD
    refine ⟨hD0, ?_, ?_⟩
    · rw [abs_div, abs_one, div_lt_one (by linarith)]; exact hD
    · rcases lt_abs.mp hD with hD' | hD'
      · rw [abs_of_pos (by linarith : (0 : ℝ) < 1 + D)] at hT
        rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < D), div_lt_iff₀ (by linarith),
          add_mul, one_div_mul_cancel hD0]
        linarith
      · rw [abs_of_neg (by linarith : 1 + D < 0)] at hT
        rw [abs_div, abs_of_neg (by linarith : D < 0), div_lt_iff₀ (by linarith),
          add_mul, one_mul, one_div, inv_mul_eq_div, neg_div, div_self hD0]
        linarith
  · rintro ⟨hD0, h1, h2⟩
    rw [abs_div, abs_one, div_lt_one (abs_pos.mpr hD0)] at h1
    refine ⟨h1, ?_⟩
    rcases lt_abs.mp h1 with hD' | hD'
    · rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < D), div_lt_iff₀ (by linarith),
        add_mul, one_div_mul_cancel hD0] at h2
      rw [abs_of_pos (by linarith : (0 : ℝ) < 1 + D)]
      linarith
    · rw [abs_div, abs_of_neg (by linarith : D < 0), div_lt_iff₀ (by linarith),
        add_mul, one_mul, one_div, inv_mul_eq_div, neg_div, div_self hD0] at h2
      rw [abs_of_neg (by linarith : 1 + D < 0)]
      linarith

/-- Woodford (2003), Prop. C.1, p. 671: the roots of `λ² − Tλ + D` are exactly `root₁`, `root₂`,
so "both roots outside" is the intrinsic statement "every root has modulus above one". -/
theorem bothOutside_iff_forall (T D : ℝ) :
    BothOutside T D ↔ ∀ z : ℂ, z ^ 2 - T * z + D = 0 → 1 < ‖z‖ := by
  constructor
  · rintro ⟨h1, h2⟩ z hz
    rcases eq_root_of_eq hz with rfl | rfl
    · exact h1
    · exact h2
  · intro h
    exact ⟨h _ (root_eq T D _ (Or.inl rfl)), h _ (root_eq T D _ (Or.inr rfl))⟩

/-- Woodford (2003), Prop. C.1, p. 671: `λ² − Tλ + D = (λ − λ₁)(λ − λ₂)`. -/
theorem quadratic_factor (T D : ℝ) (z : ℂ) :
    z ^ 2 - T * z + D = (z - root₁ T D) * (z - root₂ T D) := by
  have hs := root_sum T D
  have hp := root_prod T D
  linear_combination z * hs - hp

/-- Woodford (2003), Prop. C.1, p. 671: if `λ² − Tλ + D = (λ − p)(λ − q)`, the roots `root₁`,
`root₂` are `p` and `q`. -/
theorem roots_of_factor {T D : ℝ} {p q : ℂ}
    (h : ∀ z : ℂ, z ^ 2 - T * z + D = (z - p) * (z - q)) :
    (root₁ T D = p ∨ root₁ T D = q) ∧ (root₂ T D = p ∨ root₂ T D = q) := by
  have e : ∀ r : ℂ, r ^ 2 - T * r + D = 0 → r = p ∨ r = q := by
    intro r hr
    rw [h r] at hr
    rcases mul_eq_zero.mp hr with h' | h'
    · exact Or.inl (sub_eq_zero.mp h')
    · exact Or.inr (sub_eq_zero.mp h')
  exact ⟨e _ (root_eq T D _ (Or.inl rfl)), e _ (root_eq T D _ (Or.inr rfl))⟩

/-- Woodford (2003), Prop. C.1, p. 671: if `λ² − Tλ + D = (λ − p)(λ − q)` with `|p|, |q| > 1`,
both roots are outside the unit circle. -/
theorem bothOutside_of_factor {T D : ℝ} {p q : ℂ}
    (h : ∀ z : ℂ, z ^ 2 - T * z + D = (z - p) * (z - q)) (hp : 1 < ‖p‖) (hq : 1 < ‖q‖) :
    BothOutside T D := by
  obtain ⟨h1, h2⟩ := roots_of_factor h
  refine ⟨?_, ?_⟩
  · rcases h1 with e | e <;> rw [e] <;> assumption
  · rcases h2 with e | e <;> rw [e] <;> assumption

/-- Woodford (2003), Prop. C.1, p. 671 (the inside version): if `λ² − Tλ + D = (λ − p)(λ − q)`
with `|p|, |q| < 1`, the Schur–Cohn condition holds. -/
theorem schurStable_of_factor {T D : ℝ} {p q : ℂ}
    (h : ∀ z : ℂ, z ^ 2 - T * z + D = (z - p) * (z - q)) (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) :
    SchurStable T D := by
  obtain ⟨h1, h2⟩ := roots_of_factor h
  rw [schurStable_iff_roots]
  refine ⟨?_, ?_⟩
  · rcases h1 with e | e <;> rw [e] <;> assumption
  · rcases h2 with e | e <;> rw [e] <;> assumption

/-- Woodford (2003), Prop. C.1, p. 671: two real numbers of modulus above one are the roots of a
quadratic with both roots outside the unit circle. -/
theorem bothOutside_of_reals {u v : ℝ} (hu : 1 < |u|) (hv : 1 < |v|) :
    BothOutside (u + v) (u * v) :=
  bothOutside_of_factor (p := u) (q := v) (fun z => by push_cast; ring)
    (by rwa [Complex.norm_real, Real.norm_eq_abs]) (by rwa [Complex.norm_real, Real.norm_eq_abs])

/-- Woodford (2003), Prop. C.1, p. 671: two real numbers of modulus below one are the roots of a
quadratic satisfying the Schur–Cohn condition. -/
theorem schurStable_of_reals {u v : ℝ} (hu : |u| < 1) (hv : |v| < 1) :
    SchurStable (u + v) (u * v) :=
  schurStable_of_factor (p := u) (q := v) (fun z => by push_cast; ring)
    (by rwa [Complex.norm_real, Real.norm_eq_abs]) (by rwa [Complex.norm_real, Real.norm_eq_abs])

/-- Woodford (2003), proof of Prop. C.1, p. 671, corrected step (survey E24): for real roots,
(C.6) `λ₁λ₂ > 1` together with (C.7) and (C.8) puts both roots below `−1` or both above `1`. -/
theorem e24_corrected_step {u v : ℝ} (h6 : 1 < u * v) (h7 : 0 < (u - 1) * (v - 1))
    (h8 : 0 < (u + 1) * (v + 1)) : (u < -1 ∧ v < -1) ∨ (1 < u ∧ 1 < v) := by
  have hc : CaseI2 (u + v) (u * v) := ⟨h6, by nlinarith, by nlinarith⟩
  obtain ⟨hu, hv⟩ := (real_roots_iff u v).mpr (Or.inl hc)
  rcases lt_abs.mp hu with hu | hu <;> rcases lt_abs.mp hv with hv | hv
  · exact Or.inr ⟨hu, hv⟩
  · nlinarith
  · nlinarith
  · exact Or.inl ⟨by linarith, by linarith⟩

/-- Woodford (2003), proof of Prop. C.1, p. 671 (survey E24, the gap): the printed step "(C.7) and
(C.8) imply both roots are below `−1` or both above `1`" is false — the roots `1/2, 1/2` satisfy
(C.7) and (C.8) but lie inside the unit circle; (C.6) is needed to exclude them. -/
theorem e24_printed_step_fails :
    ∃ u v : ℝ, 0 < (u - 1) * (v - 1) ∧ 0 < (u + 1) * (v + 1) ∧
      ¬ ((u < -1 ∧ v < -1) ∨ (1 < u ∧ 1 < v)) :=
  ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num⟩

/-! ### Proposition C.2: the cubic -/

/-- Woodford (2003), Prop. C.2, p. 672: the characteristic polynomial
`P(λ) = λ³ + A₂λ² + A₁λ + A₀` at a complex point. -/
def cubic (a2 a1 a0 : ℝ) (z : ℂ) : ℂ := z ^ 3 + a2 * z ^ 2 + a1 * z + a0

/-- Woodford (2003), Prop. C.2, p. 672: `P(λ)` at a real point. -/
def cubicR (a2 a1 a0 x : ℝ) : ℝ := x ^ 3 + a2 * x ^ 2 + a1 * x + a0

/-- Woodford (2003), Prop. C.2, p. 674: `P(λ) = (λ − λ₁)(λ − λ₂)(λ − λ₃)`, the roots listed with
multiplicity. -/
def Factors (a2 a1 a0 : ℝ) (l1 l2 l3 : ℂ) : Prop :=
  ∀ z : ℂ, cubic a2 a1 a0 z = (z - l1) * (z - l2) * (z - l3)

/-- Woodford (2003), Prop. C.2, p. 672: exactly one root (with multiplicity) in the open unit disc
and two strictly outside the closed unit disc. -/
def OneInTwoOut (a2 a1 a0 : ℝ) : Prop :=
  ∃ l1 l2 l3 : ℂ, Factors a2 a1 a0 l1 l2 l3 ∧ ‖l1‖ < 1 ∧ 1 < ‖l2‖ ∧ 1 < ‖l3‖

/-- Woodford (2003), Prop. C.2, p. 674: the real factorisation
`P(λ) = (λ − μ)(λ² − Tλ + D)` written through the coefficients. -/
def RealSplit (a2 a1 a0 μ T D : ℝ) : Prop :=
  a2 = -(μ + T) ∧ a1 = D + μ * T ∧ a0 = -(μ * D)

/-- Woodford (2003), (C.11)/(C.13), p. 673: `P(1) = 1 + A₂ + A₁ + A₀`. -/
def P1 (a2 a1 a0 : ℝ) : ℝ := 1 + a2 + a1 + a0

/-- Woodford (2003), (C.12)/(C.14), p. 673: `P(−1) = −1 + A₂ − A₁ + A₀`. -/
def Pm1 (a2 a1 a0 : ℝ) : ℝ := -1 + a2 - a1 + a0

/-- Woodford (2003), (C.15)/(C.16), p. 673: `A₀² − A₀A₂ + A₁ − 1`. -/
def C15 (a2 a1 a0 : ℝ) : ℝ := a0 ^ 2 - a0 * a2 + a1 - 1

/-- Woodford (2003), Prop. C.2, Case I, (C.11)–(C.12), p. 673. -/
def CaseI3 (a2 a1 a0 : ℝ) : Prop := P1 a2 a1 a0 < 0 ∧ 0 < Pm1 a2 a1 a0

/-- Woodford (2003), Prop. C.2, Case II, (C.13)–(C.15), p. 673. -/
def CaseII3 (a2 a1 a0 : ℝ) : Prop :=
  0 < P1 a2 a1 a0 ∧ Pm1 a2 a1 a0 < 0 ∧ 0 < C15 a2 a1 a0

/-- Woodford (2003), Prop. C.2, Case III as printed, (C.13), (C.14), (C.16), (C.17), p. 673. -/
def CaseIII3 (a2 a1 a0 : ℝ) : Prop :=
  0 < P1 a2 a1 a0 ∧ Pm1 a2 a1 a0 < 0 ∧ C15 a2 a1 a0 < 0 ∧ 3 < |a2|

/-- Woodford (2003), Prop. C.2, fn. 3, p. 673: Case III without (C.16), which the footnote says
is only there to make the cases disjoint. -/
def CaseIII3' (a2 a1 a0 : ℝ) : Prop := 0 < P1 a2 a1 a0 ∧ Pm1 a2 a1 a0 < 0 ∧ 3 < |a2|

/-- Woodford (2003), Prop. C.2, p. 674: the cubic at a real point is the real cubic. -/
theorem cubic_ofReal (a2 a1 a0 x : ℝ) : cubic a2 a1 a0 x = (cubicR a2 a1 a0 x : ℂ) := by
  unfold cubic cubicR; push_cast; ring

/-- Woodford (2003), Prop. C.2, p. 674: the cubic has real coefficients, `P(z̄) = conj P(z)`. -/
theorem cubic_conj (a2 a1 a0 : ℝ) (z : ℂ) : cubic a2 a1 a0 (conj z) = conj (cubic a2 a1 a0 z) := by
  unfold cubic; simp [map_add, map_mul, map_pow]

/-- Woodford (2003), (C.11)/(C.13), p. 673: `P(1)` is the cubic at `1`. -/
theorem P1_eq (a2 a1 a0 : ℝ) : P1 a2 a1 a0 = cubicR a2 a1 a0 1 := by unfold P1 cubicR; ring

/-- Woodford (2003), (C.12)/(C.14), p. 673: `P(−1)` is the cubic at `−1`. -/
theorem Pm1_eq (a2 a1 a0 : ℝ) : Pm1 a2 a1 a0 = cubicR a2 a1 a0 (-1) := by
  unfold Pm1 cubicR; ring

/-- Woodford (2003), Prop. C.2, p. 674: the real factorisation `P(x) = (x − μ)(x² − Tx + D)`. -/
theorem cubicR_of_realSplit {a2 a1 a0 μ T D : ℝ} (h : RealSplit a2 a1 a0 μ T D) (x : ℝ) :
    cubicR a2 a1 a0 x = (x - μ) * (x ^ 2 - T * x + D) := by
  obtain ⟨h2, h1, h0⟩ := h
  subst h2 h1 h0
  unfold cubicR; ring

/-- Woodford (2003), Prop. C.2, p. 674: the real factorisation, at complex points. -/
theorem cubic_of_realSplit {a2 a1 a0 μ T D : ℝ} (h : RealSplit a2 a1 a0 μ T D) (z : ℂ) :
    cubic a2 a1 a0 z = (z - μ) * (z ^ 2 - T * z + D) := by
  obtain ⟨h2, h1, h0⟩ := h
  subst h2 h1 h0
  unfold cubic; push_cast; ring

/-- Woodford (2003), Prop. C.2, p. 674: a real factorisation gives a complex factorisation with
roots `μ`, `root₁ T D`, `root₂ T D`. -/
theorem factors_of_realSplit {a2 a1 a0 μ T D : ℝ} (h : RealSplit a2 a1 a0 μ T D) :
    Factors a2 a1 a0 μ (root₁ T D) (root₂ T D) := by
  intro z
  rw [cubic_of_realSplit h, quadratic_factor, mul_assoc]

/-- Woodford (2003), (C.11)/(C.13), p. 673: `P(1) = (1 − μ)(1 − T + D)`. -/
theorem P1_of_realSplit {a2 a1 a0 μ T D : ℝ} (h : RealSplit a2 a1 a0 μ T D) :
    P1 a2 a1 a0 = (1 - μ) * (1 - T + D) := by
  rw [P1_eq, cubicR_of_realSplit h]; ring

/-- Woodford (2003), (C.12)/(C.14), p. 673: `P(−1) = −(1 + μ)(1 + T + D)`. -/
theorem Pm1_of_realSplit {a2 a1 a0 μ T D : ℝ} (h : RealSplit a2 a1 a0 μ T D) :
    Pm1 a2 a1 a0 = -((1 + μ) * (1 + T + D)) := by
  rw [Pm1_eq, cubicR_of_realSplit h]; ring

/-- Woodford (2003), (C.15), p. 674 (real form of the key identity): with the root `μ` split off,
`A₀² − A₀A₂ + A₁ − 1 = (Dμ² − Tμ + 1)(D − 1)`, i.e. `(λ₁λ₂ − 1)(λ₁λ₃ − 1) · (λ₂λ₃ − 1)`. -/
theorem C15_eq_of_realSplit {a2 a1 a0 μ T D : ℝ} (h : RealSplit a2 a1 a0 μ T D) :
    C15 a2 a1 a0 = (D * μ ^ 2 - T * μ + 1) * (D - 1) := by
  obtain ⟨h2, h1, h0⟩ := h
  subst h2 h1 h0
  unfold C15; ring

/-- Woodford (2003), p. 674 (Vieta): `A₀ = −λ₁λ₂λ₃`, `A₁ = λ₁λ₂ + λ₁λ₃ + λ₂λ₃`,
`A₂ = −λ₁ − λ₂ − λ₃`. -/
theorem factors_vieta {a2 a1 a0 : ℝ} {l1 l2 l3 : ℂ} (h : Factors a2 a1 a0 l1 l2 l3) :
    (a2 : ℂ) = -(l1 + l2 + l3) ∧ (a1 : ℂ) = l1 * l2 + l1 * l3 + l2 * l3 ∧
      (a0 : ℂ) = -(l1 * l2 * l3) := by
  have e0 := h 0
  have e1 := h 1
  have e2 := h (-1)
  unfold cubic at e0 e1 e2
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (e1 + e2) / 2 - e0
  · linear_combination (e1 - e2) / 2
  · linear_combination e0

/-- **The key identity** (Woodford (2003), (C.15), p. 674):
`A₀² − A₀A₂ + A₁ − 1 = (λ₁λ₂ − 1)(λ₁λ₃ − 1)(λ₂λ₃ − 1)`. -/
theorem C15_eq_prod {a2 a1 a0 : ℝ} {l1 l2 l3 : ℂ} (h : Factors a2 a1 a0 l1 l2 l3) :
    (C15 a2 a1 a0 : ℂ) = (l1 * l2 - 1) * (l1 * l3 - 1) * (l2 * l3 - 1) := by
  obtain ⟨h2, h1, h0⟩ := factors_vieta h
  unfold C15
  push_cast
  rw [h2, h1, h0]
  ring

/-- Woodford (2003), (C.11)/(C.13), p. 674: `P(1) = (1 − λ₁)(1 − λ₂)(1 − λ₃)`. -/
theorem P1_eq_prod {a2 a1 a0 : ℝ} {l1 l2 l3 : ℂ} (h : Factors a2 a1 a0 l1 l2 l3) :
    (P1 a2 a1 a0 : ℂ) = (1 - l1) * (1 - l2) * (1 - l3) := by
  rw [P1_eq, ← cubic_ofReal]; push_cast; exact h 1

/-- Woodford (2003), (C.12)/(C.14), p. 674: `P(−1) = −(1 + λ₁)(1 + λ₂)(1 + λ₃)`. -/
theorem Pm1_eq_prod {a2 a1 a0 : ℝ} {l1 l2 l3 : ℂ} (h : Factors a2 a1 a0 l1 l2 l3) :
    (Pm1 a2 a1 a0 : ℂ) = -((1 + l1) * (1 + l2) * (1 + l3)) := by
  rw [Pm1_eq, ← cubic_ofReal]; push_cast; rw [h (-1)]; ring

/-- Woodford (2003), Prop. C.2, p. 673: a real root splits off a real quadratic factor. -/
theorem realSplit_of_root {a2 a1 a0 μ : ℝ} (h : cubicR a2 a1 a0 μ = 0) :
    RealSplit a2 a1 a0 μ (-(a2 + μ)) (a1 + μ * a2 + μ ^ 2) := by
  unfold cubicR at h
  refine ⟨by ring, by ring, by linear_combination h⟩

/-- Woodford (2003), Prop. C.2, p. 673 ("the `λ³` term dominates"): a real cubic has a real root
(intermediate value theorem on `[−M, M]`, `M = 1 + |A₂| + |A₁| + |A₀|`). -/
theorem exists_real_root (a2 a1 a0 : ℝ) : ∃ r : ℝ, cubicR a2 a1 a0 r = 0 := by
  set M : ℝ := 1 + |a2| + |a1| + |a0| with hM
  have hM1 : 1 ≤ M := by
    have := abs_nonneg a2; have := abs_nonneg a1; have := abs_nonneg a0; linarith
  have hM0 : 0 < M := by linarith
  have hb2 := neg_abs_le a2
  have hb1 := neg_abs_le a1
  have hb0 := neg_abs_le a0
  have hc2 := le_abs_self a2
  have hc1 := le_abs_self a1
  have hc0 := le_abs_self a0
  have hMM : M ≤ M ^ 2 := by nlinarith
  have hpos : 0 < cubicR a2 a1 a0 M := by
    unfold cubicR
    have e1 : -|a2| * M ^ 2 ≤ a2 * M ^ 2 := by nlinarith [sq_nonneg M]
    have e2 : -|a1| * M ^ 2 ≤ a1 * M := by nlinarith [abs_nonneg a1]
    have e3 : -|a0| * M ^ 2 ≤ a0 := by nlinarith [abs_nonneg a0]
    have e4 : M ^ 3 = M ^ 2 * (1 + |a2| + |a1| + |a0|) := by rw [← hM]; ring
    nlinarith [sq_nonneg M]
  have hneg : cubicR a2 a1 a0 (-M) < 0 := by
    unfold cubicR
    have e1 : a2 * (-M) ^ 2 ≤ |a2| * M ^ 2 := by nlinarith [sq_nonneg M]
    have e2 : a1 * (-M) ≤ |a1| * M ^ 2 := by nlinarith [abs_nonneg a1]
    have e3 : a0 ≤ |a0| * M ^ 2 := by nlinarith [abs_nonneg a0]
    have e4 : M ^ 3 = M ^ 2 * (1 + |a2| + |a1| + |a0|) := by rw [← hM]; ring
    nlinarith [sq_nonneg M]
  have hcont : ContinuousOn (cubicR a2 a1 a0) (Set.Icc (-M) M) := by
    unfold cubicR; fun_prop
  obtain ⟨r, -, hr⟩ := intermediate_value_Icc (by linarith) hcont ⟨hneg.le, hpos.le⟩
  exact ⟨r, hr⟩

/-- Woodford (2003), Prop. C.2, p. 674: every real cubic splits as `(λ − r)(λ² − Tλ + D)` with
`r, T, D` real (hence, by `factors_of_realSplit`, into three linear factors over `ℂ`). -/
theorem exists_realSplit (a2 a1 a0 : ℝ) : ∃ r T D : ℝ, RealSplit a2 a1 a0 r T D := by
  obtain ⟨r, hr⟩ := exists_real_root a2 a1 a0
  exact ⟨r, _, _, realSplit_of_root hr⟩

/-- Woodford (2003), Prop. C.2, p. 674: a root in the open unit disc, when the other two roots
are outside the closed disc, is real (the conjugate of a root is a root). -/
theorem real_of_factors {a2 a1 a0 : ℝ} {l1 l2 l3 : ℂ} (h : Factors a2 a1 a0 l1 l2 l3)
    (h1 : ‖l1‖ < 1) (h2 : 1 < ‖l2‖) (h3 : 1 < ‖l3‖) : ((l1.re : ℝ) : ℂ) = l1 := by
  have hz : cubic a2 a1 a0 l1 = 0 := by rw [h l1]; ring
  have hc : cubic a2 a1 a0 (conj l1) = 0 := by rw [cubic_conj, hz, map_zero]
  rw [h (conj l1)] at hc
  rcases mul_eq_zero.mp hc with hc | hc
  · rcases mul_eq_zero.mp hc with hc | hc
    · exact Complex.conj_eq_iff_re.mp (sub_eq_zero.mp hc)
    · exfalso
      have : ‖conj l1‖ = ‖l2‖ := by rw [sub_eq_zero.mp hc]
      rw [Complex.norm_conj] at this
      linarith
  · exfalso
    have : ‖conj l1‖ = ‖l3‖ := by rw [sub_eq_zero.mp hc]
    rw [Complex.norm_conj] at this
    linarith

/-- Woodford (2003), Prop. C.2, p. 674: "one root inside, two outside" in real terms — a real root
`|μ| < 1` splits off a quadratic factor with both roots outside the unit circle. -/
theorem oneInTwoOut_iff_real (a2 a1 a0 : ℝ) :
    OneInTwoOut a2 a1 a0 ↔ ∃ μ T D : ℝ, |μ| < 1 ∧ BothOutside T D ∧ RealSplit a2 a1 a0 μ T D := by
  constructor
  · rintro ⟨l1, l2, l3, h, h1, h2, h3⟩
    have hre := real_of_factors h h1 h2 h3
    set μ := l1.re with hμ
    have hμ1 : |μ| < 1 := by rwa [← hre, Complex.norm_real, Real.norm_eq_abs] at h1
    have hroot : cubicR a2 a1 a0 μ = 0 := by
      have e := h μ
      rw [hre, sub_self, zero_mul, zero_mul, ← hre, cubic_ofReal] at e
      exact_mod_cast e
    have hs := realSplit_of_root hroot
    refine ⟨μ, _, _, hμ1, ?_, hs⟩
    obtain ⟨v2, v1, -⟩ := factors_vieta h
    refine bothOutside_of_factor (p := l2) (q := l3) (fun z => ?_) h2 h3
    push_cast
    rw [v2, v1, hre]
    ring
  · rintro ⟨μ, T, D, hμ, hT, hs⟩
    refine ⟨μ, root₁ T D, root₂ T D, factors_of_realSplit hs, ?_, hT.1, hT.2⟩
    rwa [Complex.norm_real, Real.norm_eq_abs]

/-- Woodford (2003), proof of Prop. C.2, p. 674 (Case II, the step "all three inside contradicts
(C.15)", in real form): if `|μ| < 1`, `D ≤ 1` and `|T| < 1 + D` then `Dμ² − Tμ + 1 > 0`. -/
theorem key_pos {μ T D : ℝ} (hμ : |μ| < 1) (hD : D ≤ 1) (hT : |T| < 1 + D) :
    0 < D * μ ^ 2 - T * μ + 1 := by
  have hm0 := abs_nonneg μ
  have hTm : T * μ ≤ |T| * |μ| := by rw [← abs_mul]; exact le_abs_self _
  have hTm' : |T| * |μ| ≤ (1 + D) * |μ| := mul_le_mul_of_nonneg_right hT.le hm0
  have hsq : μ ^ 2 = |μ| ^ 2 := (sq_abs μ).symm
  have hDm : D * |μ| < 1 := by
    rcases le_or_gt D 0 with h | h
    · nlinarith
    · nlinarith
  nlinarith

/-- Woodford (2003), proof of Prop. C.2, (b2), pp. 675–676, in real form: if `|μ| < 1`, `D > 1`,
`|T| < 1 + D` and `Dμ² − Tμ + 1 ≤ 0`, then `|μ + T| > 3`, i.e. (C.17). -/
theorem three_lt_of_key_nonpos {μ T D : ℝ} (hμ : |μ| < 1) (hD : 1 < D) (hT : |T| < 1 + D)
    (hk : D * μ ^ 2 - T * μ + 1 ≤ 0) : 3 < |μ + T| := by
  obtain ⟨hT1, hT2⟩ := abs_lt.mp hT
  obtain ⟨hm1, hm2⟩ := abs_lt.mp hμ
  rcases lt_trichotomy μ 0 with h | h | h
  · -- `μ < 0`, then `T < 0`
    have hT0 : T < 0 := by nlinarith
    rw [abs_of_neg (by linarith : μ + T < 0)]
    have hDm : 1 < D * (-μ) := by nlinarith
    nlinarith
  · subst h; nlinarith
  · have hT0 : 0 < T := by nlinarith
    rw [abs_of_pos (by linarith : 0 < μ + T)]
    have hDm : 1 < D * μ := by nlinarith
    nlinarith

/-- **Proposition C.2, sufficiency** (Woodford (2003), pp. 673–675): Case I, Case II, or Case III
without (C.16) implies exactly one root inside and two outside the unit circle. The root
`μ ∈ (−1, 1)` comes from the intermediate value theorem; Prop. C.1 locates the other two. -/
theorem oneInTwoOut_of_cases {a2 a1 a0 : ℝ}
    (h : CaseI3 a2 a1 a0 ∨ CaseII3 a2 a1 a0 ∨ CaseIII3' a2 a1 a0) : OneInTwoOut a2 a1 a0 := by
  have hcont : ContinuousOn (cubicR a2 a1 a0) (Set.Icc (-1) 1) := by
    unfold cubicR; fun_prop
  -- a root in `[−1, 1]`
  obtain ⟨μ, hμI, hμ⟩ : ∃ μ ∈ Set.Icc (-1 : ℝ) 1, cubicR a2 a1 a0 μ = 0 := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
    · rw [P1_eq] at h1; rw [Pm1_eq] at h2
      exact intermediate_value_Icc' (by norm_num) hcont ⟨h1.le, h2.le⟩
    · rw [P1_eq] at h1; rw [Pm1_eq] at h2
      exact intermediate_value_Icc (by norm_num) hcont ⟨h2.le, h1.le⟩
    · rw [P1_eq] at h1; rw [Pm1_eq] at h2
      exact intermediate_value_Icc (by norm_num) hcont ⟨h2.le, h1.le⟩
  have hs := realSplit_of_root hμ
  set T := -(a2 + μ) with hT
  set D := a1 + μ * a2 + μ ^ 2 with hD
  have hp1 := P1_of_realSplit hs
  have hpm := Pm1_of_realSplit hs
  have hc := C15_eq_of_realSplit hs
  have hne1 : μ ≠ 1 := by
    rintro rfl
    have e : P1 a2 a1 a0 = 0 := by rw [P1_eq]; exact hμ
    rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> linarith
  have hne2 : μ ≠ -1 := by
    rintro rfl
    have e : Pm1 a2 a1 a0 = 0 := by rw [Pm1_eq]; exact hμ
    rcases h with ⟨-, h1⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩ <;> linarith
  have hμ1 : |μ| < 1 := abs_lt.mpr ⟨lt_of_le_of_ne hμI.1 (Ne.symm hne2),
    lt_of_le_of_ne hμI.2 hne1⟩
  obtain ⟨hl, hr⟩ := abs_lt.mp hμ1
  refine (oneInTwoOut_iff_real a2 a1 a0).mpr ⟨μ, T, D, hμ1, ?_, hs⟩
  rw [bothOutside_iff_cases]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · -- Case I: `q(1) < 0`, `q(−1) < 0`, so Case II of Prop. C.1
    right
    rw [hp1] at h1; rw [hpm] at h2
    have e1 : 1 - T + D < 0 := by
      by_contra hc'; push Not at hc'; nlinarith
    have e2 : 1 + T + D < 0 := by
      by_contra hc'; push Not at hc'; nlinarith
    exact ⟨by linarith, by linarith⟩
  · -- Case II
    left
    rw [hp1] at h1; rw [hpm] at h2
    have e1 : 0 < 1 - T + D := by
      by_contra hc'; push Not at hc'; nlinarith
    have e2 : 0 < 1 + T + D := by
      by_contra hc'; push Not at hc'; nlinarith
    refine ⟨?_, by linarith, by linarith⟩
    by_contra hD1
    push Not at hD1
    have hk := key_pos (T := T) hμ1 hD1 (abs_lt.mpr ⟨by linarith, by linarith⟩)
    rw [hc] at h3
    nlinarith
  · -- Case III′
    left
    rw [hp1] at h1; rw [hpm] at h2
    have e1 : 0 < 1 - T + D := by
      by_contra hc'; push Not at hc'; nlinarith
    have e2 : 0 < 1 + T + D := by
      by_contra hc'; push Not at hc'; nlinarith
    refine ⟨?_, by linarith, by linarith⟩
    by_contra hD1
    push Not at hD1
    have ha2 : a2 = -(μ + T) := hs.1
    rw [ha2, abs_neg] at h3
    have : |μ + T| < 3 := by
      rw [abs_lt]; constructor <;> linarith
    linarith

/-- **Proposition C.2, necessity** (Woodford (2003), pp. 675–676), in exact form: one root inside
and two outside implies Case I, Case II, or Case III without (C.16). Covers three real roots and
a real root with a complex pair alike. -/
theorem cases_of_oneInTwoOut {a2 a1 a0 : ℝ} (h : OneInTwoOut a2 a1 a0) :
    CaseI3 a2 a1 a0 ∨ CaseII3 a2 a1 a0 ∨ CaseIII3' a2 a1 a0 := by
  obtain ⟨μ, T, D, hμ, hTD, hs⟩ := (oneInTwoOut_iff_real a2 a1 a0).mp h
  obtain ⟨hl, hr⟩ := abs_lt.mp hμ
  have hp1 := P1_of_realSplit hs
  have hpm := Pm1_of_realSplit hs
  have hc := C15_eq_of_realSplit hs
  rcases (bothOutside_iff_cases T D).mp hTD with ⟨hD, e1, e2⟩ | ⟨e1, e2⟩
  · have q1 : 0 < P1 a2 a1 a0 := by rw [hp1]; nlinarith
    have q2 : Pm1 a2 a1 a0 < 0 := by rw [hpm]; nlinarith
    by_cases hk : 0 < D * μ ^ 2 - T * μ + 1
    · right; left
      refine ⟨q1, q2, ?_⟩
      rw [hc]; nlinarith
    · right; right
      push Not at hk
      refine ⟨q1, q2, ?_⟩
      rw [hs.1, abs_neg]
      exact three_lt_of_key_nonpos (T := T) hμ hD (abs_lt.mpr ⟨by linarith, by linarith⟩) hk
  · left
    constructor
    · rw [hp1]; nlinarith
    · rw [hpm]; nlinarith

/-- **Proposition C.2** (Woodford (2003), pp. 672–676), exact form: exactly one root inside and
two outside the unit circle iff Case I, Case II, or Case III without (C.16). -/
theorem oneInTwoOut_iff_cases (a2 a1 a0 : ℝ) :
    OneInTwoOut a2 a1 a0 ↔ CaseI3 a2 a1 a0 ∨ CaseII3 a2 a1 a0 ∨ CaseIII3' a2 a1 a0 :=
  ⟨cases_of_oneInTwoOut, oneInTwoOut_of_cases⟩

/-- Woodford (2003), App. C.1, p. 670: the inverse `A⁻¹ = (det A)⁻¹ adj A` of a `2 × 2` matrix
(the forward-form matrix `B` of `E_t z_{t+1} = A z_t + …`). -/
noncomputable def inv2 (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![A 1 1 / det2 A, -A 0 1 / det2 A; -A 1 0 / det2 A, A 0 0 / det2 A]

/-- Woodford (2003), App. C.1, p. 670: `tr A⁻¹ = tr A / det A`. -/
theorem tr2_inv2 (A : Matrix (Fin 2) (Fin 2) ℝ) : tr2 (inv2 A) = tr2 A / det2 A := by
  simp only [inv2, tr2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- Woodford (2003), App. C.1, p. 670: `det A⁻¹ = (det A)⁻¹` (also when `det A = 0`, both sides
then being `0`). -/
theorem det2_inv2 (A : Matrix (Fin 2) (Fin 2) ℝ) : det2 (inv2 A) = (det2 A)⁻¹ := by
  have e : det2 (inv2 A) = det2 A * (det2 A)⁻¹ ^ 2 := by
    change inv2 A 0 0 * inv2 A 1 1 - inv2 A 0 1 * inv2 A 1 0 = _
    simp only [inv2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [show det2 A = A 0 0 * A 1 1 - A 0 1 * A 1 0 from rfl]
    ring
  rw [e]
  by_cases h : det2 A = 0
  · simp [h]
  · field_simp

/-- Woodford (2003), App. C.1, p. 670: `A⁻¹ A = I` when `det A ≠ 0`. -/
theorem inv2_mul {A : Matrix (Fin 2) (Fin 2) ℝ} (h : det2 A ≠ 0) : inv2 A * A = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inv2, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    (try rw [show det2 A = A 0 0 * A 1 1 - A 0 1 * A 1 0 from rfl]) <;> ring

/-- Woodford (2003), App. C.1, p. 670: `A A⁻¹ = I` when `det A ≠ 0`. -/
theorem mul_inv2 {A : Matrix (Fin 2) (Fin 2) ℝ} (h : det2 A ≠ 0) : A * inv2 A = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inv2, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    (try rw [show det2 A = A 0 0 * A 1 1 - A 0 1 * A 1 0 from rfl]) <;> ring

/-- Woodford (2003), Prop. C.1, p. 670: for `det A ≠ 0`, `E_t z_{t+1} = A z_t + w_t` is the forward
system `z_t = A⁻¹ E_t z_{t+1} − A⁻¹ w_t`. -/
theorem solvesE2_iff {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : det2 A ≠ 0)
    (w z : ℕ → Fin 2 → Ω → ℝ) :
    ExpSys 𝔼 A w z ↔ FSolves 𝔼 (inv2 A) (fun t => -rvMul (inv2 A) (w t)) z := by
  constructor
  · intro h t
    have e : (fun j => 𝔼.E t (z (t + 1) j)) = rvMul A (z t) + w t := by
      funext j; rw [Pi.add_apply]; exact h t j
    rw [e, rvMul_add, rvMul_rvMul, inv2_mul hA, rvMul_one]
    funext i ω
    simp
  · intro h t i
    have e := h t
    have e2 : rvMul A (z t) = rvMul A (rvMul (inv2 A) (fun j => 𝔼.E t (z (t + 1) j)))
        - rvMul A (rvMul (inv2 A) (w t)) := by
      conv_lhs => rw [e]
      rw [← sub_eq_add_neg, rvMul_sub]
    rw [rvMul_rvMul, rvMul_rvMul, mul_inv2 hA, rvMul_one, rvMul_one] at e2
    have := congrFun e2 i
    simp only [Pi.sub_apply] at this
    rw [this]
    abel

/-- **Proposition C.1, sufficiency** (Woodford (2003), p. 670): if both eigenvalues of `A` lie
outside the unit circle, then for every bounded adapted forcing `E_t z_{t+1} = A z_t + w_t` has
exactly one bounded adapted solution, the forward solution `z_t = −∑ A^{−k−1} E_t w_{t+k}`. -/
theorem existsUnique2 {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : BothOutside (tr2 A) (det2 A))
    {w : ℕ → Fin 2 → Ω → ℝ} (hwb : VBounded w) (hwa : VAdapted 𝔼 w) :
    ∃! z, ExpSys 𝔼 A w z ∧ VAdapted 𝔼 z ∧ VBounded z := by
  obtain ⟨hD, hS⟩ := (bothOutside_iff_schurStable_inv _ _).mp hA
  have hK : SchurStable (tr2 (inv2 A)) (det2 (inv2 A)) := by
    rw [tr2_inv2, det2_inv2, ← one_div]; exact hS
  have hfb : VBounded (fun t => -rvMul (inv2 A) (w t)) := by
    obtain ⟨B, hB⟩ := vBounded_rvMul (inv2 A) hwb
    exact ⟨B, fun t i ω => by simpa using hB t i ω⟩
  have hfa : VAdapted 𝔼 (fun t => -rvMul (inv2 A) (w t)) := by
    intro t i
    have := vAdapted_rvMul 𝔼 (inv2 A) hwa t i
    simp only [Pi.neg_apply, map_neg]
    exact congrArg Neg.neg this
  obtain ⟨z, ⟨hz, hza, hzb⟩, hzu⟩ := fwd_existsUnique 𝔼 hK hfb hfa
  refine ⟨z, ⟨(solvesE2_iff 𝔼 hD w z).mpr ((solves_iff_fsolves 𝔼 _ _ z).mp hz), hza, hzb⟩,
    fun y ⟨hy, hya, hyb⟩ => ?_⟩
  exact hzu y ⟨(solves_iff_fsolves 𝔼 _ _ y).mpr ((solvesE2_iff 𝔼 hD w y).mp hy), hya, hyb⟩

/-! ### Three variables, one predetermined: the characteristic polynomial -/

/-- Woodford (2003), Prop. C.2, p. 672: the coefficient `A₂ = −tr A` of `det(λI − A)`. -/
def ch2 (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := -(A 0 0 + A 1 1 + A 2 2)

/-- Woodford (2003), Prop. C.2, p. 672: the coefficient `A₁` of `det(λI − A)` (the sum of the
principal `2 × 2` minors). -/
def ch1 (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  A 0 0 * A 1 1 - A 0 1 * A 1 0 + A 0 0 * A 2 2 - A 0 2 * A 2 0 + A 1 1 * A 2 2 - A 1 2 * A 2 1

/-- Woodford (2003), Prop. C.2, p. 672: the coefficient `A₀ = −det A` of `det(λI − A)`. -/
def ch0 (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  -(A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2
    + A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0)

/-- Woodford (2003), Prop. C.2, p. 672: `det(xI − A) = x³ + A₂x² + A₁x + A₀`. -/
theorem det_sub_eq (A : Matrix (Fin 3) (Fin 3) ℝ) (x : ℝ) :
    (Matrix.scalar (Fin 3) x - A).det = cubicR (ch2 A) (ch1 A) (ch0 A) x := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.scalar_apply, Fin.isValue, Matrix.sub_apply, Matrix.diagonal_apply_eq, ne_eq,
    Fin.reduceEq, not_false_eq_true, Matrix.diagonal_apply_ne, zero_sub, mul_neg, neg_mul, neg_neg,
    zero_ne_one, one_ne_zero]
  unfold cubicR ch2 ch1 ch0
  ring

/-- Woodford (2003), Prop. C.2, p. 672: a real root of the characteristic polynomial is an
eigenvalue with a real eigenvector. -/
theorem exists_eigvec {A : Matrix (Fin 3) (Fin 3) ℝ} {μ : ℝ}
    (h : cubicR (ch2 A) (ch1 A) (ch0 A) μ = 0) :
    ∃ v : Fin 3 → ℝ, v ≠ 0 ∧ A *ᵥ v = μ • v := by
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr (by rw [det_sub_eq]; exact h)
  refine ⟨v, hv0, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero] at hv
  rw [← hv]
  funext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

/-- Woodford (2003), Prop. C.2, p. 672 and (C.19): `E_t y_{t+1} = A y_t + w_t` for the state
`y_t = (z_t, x_t)`, `z_t` the two non-predetermined variables (indices `0, 1`) and `x_t` the
predetermined one (index `2`). -/
def Solves3 (A : Matrix (Fin 3) (Fin 3) ℝ) (w y : ℕ → Fin 3 → Ω → ℝ) : Prop :=
  ∀ t i, 𝔼.E t (y (t + 1) i) = rvMul A (y t) i + w t i

/-- Woodford (2003), Prop. C.2, p. 672: a (bounded) rational-expectations equilibrium: `y` solves
the system, is adapted and bounded, the predetermined variable `x_{t+1}` is known at date `t`, and
its initial value is `x₀`. -/
def Equil3 (A : Matrix (Fin 3) (Fin 3) ℝ) (w : ℕ → Fin 3 → Ω → ℝ) (x0 : ℝ)
    (y : ℕ → Fin 3 → Ω → ℝ) : Prop :=
  Solves3 𝔼 A w y ∧ VAdapted 𝔼 y ∧ (∀ t, 𝔼.E t (y (t + 1) 2) = y (t + 1) 2) ∧
    y 0 2 = (fun _ => x0) ∧ VBounded y

/-- Woodford (2003), Prop. C.2, p. 672: determinacy — for every bounded adapted forcing and every
initial value of the predetermined variable there is exactly one bounded equilibrium. -/
def Determinate3 (A : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ w : ℕ → Fin 3 → Ω → ℝ, VBounded w → VAdapted 𝔼 w → ∀ x0 : ℝ, ∃! y, Equil3 𝔼 A w x0 y

/-- Woodford (2003), (C.19), p. 677: determinacy of the model `E_t y_{t+1} = A y_t + a e_t` with a
scalar exogenous disturbance `e_t` entering in the direction `a`. -/
def DeterminateFor (A : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) : Prop :=
  ∀ e : ℕ → Ω → ℝ, BoundedProc e → 𝔼.Adapted e → ∀ x0 : ℝ,
    ∃! y, Equil3 𝔼 A (fun t i => a i • e t) x0 y

/-- Woodford (2003), p. 672, fn. 2 (the genericity the book leaves implicit): no eigenvector of an
eigenvalue in the open unit disc has a zero predetermined component. -/
def Generic (A : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ (μ : ℝ) (v : Fin 3 → ℝ), |μ| < 1 → A *ᵥ v = μ • v → v 2 = 0 → v = 0

/-- Woodford (2003), (C.19), p. 677: general determinacy implies determinacy of every model with a
scalar disturbance. -/
theorem determinateFor_of_determinate3 {A : Matrix (Fin 3) (Fin 3) ℝ} (h : Determinate3 𝔼 A)
    (a : Fin 3 → ℝ) : DeterminateFor 𝔼 A a := by
  intro e ⟨M, hM⟩ he x0
  refine h _ ⟨(∑ i, |a i|) * max M 0, fun t i ω => ?_⟩ (fun t i => ?_) x0
  · simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    calc |a i| * |e t ω| ≤ |a i| * max M 0 :=
          mul_le_mul_of_nonneg_left ((hM t ω).trans (le_max_left _ _)) (abs_nonneg _)
      _ ≤ (∑ i, |a i|) * max M 0 := by
          refine mul_le_mul_of_nonneg_right ?_ (le_max_right _ _)
          exact Finset.single_le_sum (f := fun i => |a i|) (fun i _ => abs_nonneg _)
            (Finset.mem_univ i)
  · simp only [map_smul, he t]

/-! ### Sufficiency: the Blanchard–Kahn reduction -/

/-- Woodford (2003), Prop. C.2, p. 672 (the reduction): `C = A_zz − g A_xz`, the matrix governing
`ẑ_t = z_t − g x_t` when `(g, 1)` is the stable eigenvector. -/
def redC (A : Matrix (Fin 3) (Fin 3) ℝ) (g0 g1 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![A 0 0 - g0 * A 2 0, A 0 1 - g0 * A 2 1; A 1 0 - g1 * A 2 0, A 1 1 - g1 * A 2 1]

/-- Woodford (2003), Prop. C.2, p. 672 (the reduction): `ẑ_t = z_t − g x_t`. -/
def zhat (g0 g1 : ℝ) (y : ℕ → Fin 3 → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun t => ![y t 0 - g0 • y t 2, y t 1 - g1 • y t 2]

/-- Woodford (2003), Prop. C.2, p. 674: with `(g₀, g₁, 1)` an eigenvector of `μ`, the
characteristic polynomial factors as `(λ − μ) det(λI − C)`. -/
theorem realSplit_redC {A : Matrix (Fin 3) (Fin 3) ℝ} {μ g0 g1 : ℝ}
    (e0 : A 0 0 * g0 + A 0 1 * g1 + A 0 2 = μ * g0)
    (e1 : A 1 0 * g0 + A 1 1 * g1 + A 1 2 = μ * g1)
    (e2 : A 2 0 * g0 + A 2 1 * g1 + A 2 2 = μ) :
    RealSplit (ch2 A) (ch1 A) (ch0 A) μ (tr2 (redC A g0 g1)) (det2 (redC A g0 g1)) := by
  have h02 : A 0 2 = μ * g0 - A 0 0 * g0 - A 0 1 * g1 := by linarith
  have h12 : A 1 2 = μ * g1 - A 1 0 * g0 - A 1 1 * g1 := by linarith
  have h22 : A 2 2 = μ - A 2 0 * g0 - A 2 1 * g1 := by linarith
  unfold RealSplit ch2 ch1 ch0 tr2 det2 redC
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [h02, h12, h22]
  refine ⟨by ring, by ring, by ring⟩

/-- Woodford (2003), Prop. C.2, p. 672 (the reduction): in an equilibrium, `ẑ` solves the
two-variable system `E_t ẑ_{t+1} = C ẑ_t + ŵ_t`, and the predetermined variable follows
`x_{t+1} = A_xz ẑ_t + μ x_t + w^x_t`. -/
theorem reduce_equil {A : Matrix (Fin 3) (Fin 3) ℝ} {μ g0 g1 : ℝ}
    (e0 : A 0 0 * g0 + A 0 1 * g1 + A 0 2 = μ * g0)
    (e1 : A 1 0 * g0 + A 1 1 * g1 + A 1 2 = μ * g1)
    (e2 : A 2 0 * g0 + A 2 1 * g1 + A 2 2 = μ) {w : ℕ → Fin 3 → Ω → ℝ} {x0 : ℝ}
    {y : ℕ → Fin 3 → Ω → ℝ} (hy : Equil3 𝔼 A w x0 y) :
    ExpSys 𝔼 (redC A g0 g1) (zhat g0 g1 w) (zhat g0 g1 y) ∧ VAdapted 𝔼 (zhat g0 g1 y) ∧
      VBounded (zhat g0 g1 y) ∧
      ∀ t, y (t + 1) 2 = A 2 0 • zhat g0 g1 y t 0 + A 2 1 • zhat g0 g1 y t 1 + μ • y t 2 + w t 2
    := by
  obtain ⟨hs, ha, hp, -, ⟨M, hM⟩⟩ := hy
  have hx : ∀ t, y (t + 1) 2 = A 2 0 • zhat g0 g1 y t 0 + A 2 1 • zhat g0 g1 y t 1 +
      μ • y t 2 + w t 2 := by
    intro t
    rw [← hp t, hs t 2]
    funext ω
    have h22 : A 2 2 = μ - A 2 0 * g0 - A 2 1 * g1 := by linarith
    simp only [zhat, rvMul_apply, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h22]
    ring
  refine ⟨fun t i => ?_, fun t i => ?_, ⟨M + (|g0| + |g1|) * M, fun t i ω => ?_⟩, hx⟩
  · have h02 : A 0 2 = μ * g0 - A 0 0 * g0 - A 0 1 * g1 := by linarith
    have h12 : A 1 2 = μ * g1 - A 1 0 * g0 - A 1 1 * g1 := by linarith
    have h22 : A 2 2 = μ - A 2 0 * g0 - A 2 1 * g1 := by linarith
    have s0 := hs t 0
    have s1 := hs t 1
    have s2 := hs t 2
    funext ω
    have t0 := congrFun s0 ω
    have t1 := congrFun s1 ω
    have t2 := congrFun s2 ω
    simp only [rvMul_apply, Fin.sum_univ_three, Pi.add_apply] at t0 t1 t2
    fin_cases i
    · simp only [zhat, rvMul_apply, Fin.sum_univ_two, redC, map_sub, map_smul, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue]
      rw [t0, t2, h02, h22]
      ring
    · simp only [zhat, rvMul_apply, Fin.sum_univ_two, redC, map_sub, map_smul, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Fin.mk_one, Fin.isValue]
      rw [t1, t2, h12, h22]
      ring
  · fin_cases i
    · simp [zhat, map_sub, map_smul, ha t 0, ha t 2]
    · simp [zhat, map_sub, map_smul, ha t 1, ha t 2]
  · have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0 ω)
    fin_cases i
    · change |y t 0 ω - g0 * y t 2 ω| ≤ _
      calc |y t 0 ω - g0 * y t 2 ω| ≤ |y t 0 ω| + |g0| * |y t 2 ω| := by
            rw [← abs_mul]; exact abs_sub _ _
        _ ≤ M + (|g0| + |g1|) * M := by
            have := hM t 0 ω; have := hM t 2 ω
            have := abs_nonneg g1
            nlinarith [abs_nonneg g0]
    · change |y t 1 ω - g1 * y t 2 ω| ≤ _
      calc |y t 1 ω - g1 * y t 2 ω| ≤ |y t 1 ω| + |g1| * |y t 2 ω| := by
            rw [← abs_mul]; exact abs_sub _ _
        _ ≤ M + (|g0| + |g1|) * M := by
            have := hM t 1 ω; have := hM t 2 ω
            have := abs_nonneg g0
            nlinarith [abs_nonneg g1]

/-- Woodford (2003), Prop. C.2, p. 672 (the backward-looking block): the predetermined variable
generated by `x₀` and `x_{t+1} = c_t + μ x_t`. -/
noncomputable def xrec (c : ℕ → Ω → ℝ) (μ x0 : ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => x0
  | t + 1 => c t + μ • xrec c μ x0 t

omit 𝔼 in
/-- Woodford (2003), Prop. C.2, p. 672: with `|μ| < 1` and bounded `c` the backward recursion is
bounded. -/
theorem xrec_bounded {c : ℕ → Ω → ℝ} {μ K : ℝ} (x0 : ℝ) (hc : ∀ t ω, |c t ω| ≤ K)
    (hμ : |μ| < 1) : ∀ t ω, |xrec c μ x0 t ω| ≤ max |x0| (K / (1 - |μ|)) := fun t ω =>
  abs_rec_le hμ (u := fun t => c t ω) (x := fun t => xrec c μ x0 t ω) (fun t => hc t ω) le_rfl
    (fun t => by change c t ω + μ * xrec c μ x0 t ω = _; ring) t

/-- Woodford (2003), Prop. C.2, p. 672: with `c` adapted, `x_{t+1}` is known at date `t`. -/
theorem xrec_known {c : ℕ → Ω → ℝ} {μ : ℝ} (x0 : ℝ) (hc : 𝔼.Adapted c) :
    ∀ t, 𝔼.E t (xrec c μ x0 t) = xrec c μ x0 t ∧
      𝔼.E t (xrec c μ x0 (t + 1)) = xrec c μ x0 (t + 1) := by
  intro t
  induction t with
  | zero =>
    have h0 : 𝔼.E 0 (xrec c μ x0 0) = xrec c μ x0 0 := 𝔼.const 0 x0
    refine ⟨h0, ?_⟩
    change 𝔼.E 0 (c 0 + μ • xrec c μ x0 0) = c 0 + μ • xrec c μ x0 0
    rw [map_add, map_smul, hc 0, h0]
  | succ t ih =>
    have h1 : 𝔼.E (t + 1) (xrec c μ x0 (t + 1)) = xrec c μ x0 (t + 1) := by
      rw [← ih.2, 𝔼.known (Nat.le_succ t)]
    refine ⟨h1, ?_⟩
    change 𝔼.E (t + 1) (c (t + 1) + μ • xrec c μ x0 (t + 1)) = c (t + 1) + μ • xrec c μ x0 (t + 1)
    rw [map_add, map_smul, hc (t + 1), h1]

/-- **The Blanchard–Kahn theorem, sufficiency** (Woodford (2003), Prop. C.2, p. 672, which the
book assumes, fns. 1–2): if `A` has a real eigenvalue `|μ| < 1` with eigenvector `(g₀, g₁, 1)` and
the reduced matrix `C = A_zz − g A_xz` has both eigenvalues outside the unit circle, then for every
bounded adapted forcing and every initial value of the predetermined variable there is exactly one
bounded equilibrium. -/
theorem determinate3_of_reduction {A : Matrix (Fin 3) (Fin 3) ℝ} {μ g0 g1 : ℝ} (hμ : |μ| < 1)
    (e0 : A 0 0 * g0 + A 0 1 * g1 + A 0 2 = μ * g0)
    (e1 : A 1 0 * g0 + A 1 1 * g1 + A 1 2 = μ * g1)
    (e2 : A 2 0 * g0 + A 2 1 * g1 + A 2 2 = μ)
    (hC : BothOutside (tr2 (redC A g0 g1)) (det2 (redC A g0 g1))) : Determinate3 𝔼 A := by
  intro w hwb hwa x0
  -- the forcing of the reduced system
  have hfb : VBounded (zhat g0 g1 w) := by
    obtain ⟨M, hM⟩ := hwb
    refine ⟨M + (|g0| + |g1|) * M, fun t i ω => ?_⟩
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0 ω)
    fin_cases i
    · change |w t 0 ω - g0 * w t 2 ω| ≤ _
      calc |w t 0 ω - g0 * w t 2 ω| ≤ |w t 0 ω| + |g0| * |w t 2 ω| := by
            rw [← abs_mul]; exact abs_sub _ _
        _ ≤ M + (|g0| + |g1|) * M := by
            have := hM t 0 ω; have := hM t 2 ω; have := abs_nonneg g1
            nlinarith [abs_nonneg g0]
    · change |w t 1 ω - g1 * w t 2 ω| ≤ _
      calc |w t 1 ω - g1 * w t 2 ω| ≤ |w t 1 ω| + |g1| * |w t 2 ω| := by
            rw [← abs_mul]; exact abs_sub _ _
        _ ≤ M + (|g0| + |g1|) * M := by
            have := hM t 1 ω; have := hM t 2 ω; have := abs_nonneg g0
            nlinarith [abs_nonneg g1]
  have hfa : VAdapted 𝔼 (zhat g0 g1 w) := by
    intro t i
    fin_cases i
    · simp [zhat, map_sub, map_smul, hwa t 0, hwa t 2]
    · simp [zhat, map_sub, map_smul, hwa t 1, hwa t 2]
  obtain ⟨zh, ⟨hzs, hza, hzb⟩, hzu⟩ := existsUnique2 𝔼 hC hfb hfa
  -- the predetermined variable
  set c : ℕ → Ω → ℝ := fun t => A 2 0 • zh t 0 + A 2 1 • zh t 1 + w t 2 with hc_def
  have hca : 𝔼.Adapted c := fun t => by
    simp only [hc_def, map_add, map_smul, hza t 0, hza t 1, hwa t 2]
  obtain ⟨Mz, hMz⟩ := hzb
  obtain ⟨Mw, hMw⟩ := hwb
  have hcb : ∀ t ω, |c t ω| ≤ |A 2 0| * Mz + |A 2 1| * Mz + Mw := by
    intro t ω
    simp only [hc_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc |A 2 0 * zh t 0 ω + A 2 1 * zh t 1 ω + w t 2 ω|
        ≤ |A 2 0 * zh t 0 ω| + |A 2 1 * zh t 1 ω| + |w t 2 ω| := abs_add_three _ _ _
      _ ≤ _ := by
          rw [abs_mul, abs_mul]
          gcongr
          · exact hMz t 0 ω
          · exact hMz t 1 ω
          · exact hMw t 2 ω
  set x := xrec c μ x0 with hx_def
  have hxk := xrec_known 𝔼 (μ := μ) x0 hca
  have hxb := xrec_bounded x0 hcb hμ
  set y : ℕ → Fin 3 → Ω → ℝ := fun t => ![zh t 0 + g0 • x t, zh t 1 + g1 • x t, x t] with hy_def
  have h02 : A 0 2 = μ * g0 - A 0 0 * g0 - A 0 1 * g1 := by linarith
  have h12 : A 1 2 = μ * g1 - A 1 0 * g0 - A 1 1 * g1 := by linarith
  have h22 : A 2 2 = μ - A 2 0 * g0 - A 2 1 * g1 := by linarith
  have hyeq : Equil3 𝔼 A w x0 y := by
    refine ⟨fun t i => ?_, fun t i => ?_, fun t => (hxk t).2, rfl, ?_⟩
    · have z0 := congrFun (hzs t 0)
      have z1 := congrFun (hzs t 1)
      fin_cases i
      · change 𝔼.E t (zh (t + 1) 0 + g0 • x (t + 1)) = _
        rw [map_add, map_smul, (hxk t).2, show xrec c μ x0 (t + 1) = c t + μ • x t from rfl]
        funext ω
        have := z0 ω
        simp only [rvMul_apply, Fin.sum_univ_two, redC, zhat, Pi.add_apply, Matrix.of_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
          Matrix.cons_val_fin_one, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
        simp only [rvMul_apply, Fin.sum_univ_three, hy_def, hc_def, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.isValue]
        rw [this, h02]
        ring
      · change 𝔼.E t (zh (t + 1) 1 + g1 • x (t + 1)) = _
        rw [map_add, map_smul, (hxk t).2, show xrec c μ x0 (t + 1) = c t + μ • x t from rfl]
        funext ω
        have := z1 ω
        simp only [rvMul_apply, Fin.sum_univ_two, redC, zhat, Pi.add_apply, Matrix.of_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
          Matrix.cons_val_fin_one, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
        simp only [rvMul_apply, Fin.sum_univ_three, hy_def, hc_def, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.mk_one, Fin.isValue]
        rw [this, h12]
        ring
      · change 𝔼.E t (x (t + 1)) = _
        rw [(hxk t).2, show xrec c μ x0 (t + 1) = c t + μ • x t from rfl]
        funext ω
        simp only [rvMul_apply, Fin.sum_univ_three, hy_def, hc_def, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.reduceFinMk, Fin.isValue]
        rw [h22]
        ring
    · fin_cases i
      · change 𝔼.E t (zh t 0 + g0 • x t) = zh t 0 + g0 • x t
        rw [map_add, map_smul, hza t 0, (hxk t).1]
      · change 𝔼.E t (zh t 1 + g1 • x t) = zh t 1 + g1 • x t
        rw [map_add, map_smul, hza t 1, (hxk t).1]
      · exact (hxk t).1
    · refine ⟨Mz + (|g0| + |g1| + 1) * max |x0| ((|A 2 0| * Mz + |A 2 1| * Mz + Mw) / (1 - |μ|)),
        fun t i ω => ?_⟩
      set B := max |x0| ((|A 2 0| * Mz + |A 2 1| * Mz + Mw) / (1 - |μ|))
      have hB0 : 0 ≤ B := (abs_nonneg _).trans (le_max_left _ _)
      have hMz0 : 0 ≤ Mz := (abs_nonneg _).trans (hMz 0 0 ω)
      have hxt := hxb t ω
      fin_cases i
      · change |zh t 0 ω + g0 * x t ω| ≤ _
        calc |zh t 0 ω + g0 * x t ω| ≤ |zh t 0 ω| + |g0| * |x t ω| := by
              rw [← abs_mul]; exact abs_add_le _ _
          _ ≤ _ := by
              have := hMz t 0 ω
              nlinarith [abs_nonneg g0, abs_nonneg g1, abs_nonneg (x t ω)]
      · change |zh t 1 ω + g1 * x t ω| ≤ _
        calc |zh t 1 ω + g1 * x t ω| ≤ |zh t 1 ω| + |g1| * |x t ω| := by
              rw [← abs_mul]; exact abs_add_le _ _
          _ ≤ _ := by
              have := hMz t 1 ω
              nlinarith [abs_nonneg g0, abs_nonneg g1, abs_nonneg (x t ω)]
      · change |x t ω| ≤ _
        nlinarith [abs_nonneg g0, abs_nonneg g1]
  refine ⟨y, hyeq, fun y' hy' => ?_⟩
  -- uniqueness
  obtain ⟨r1, r2, r3, r4⟩ := reduce_equil 𝔼 e0 e1 e2 hy'
  have hz' : zhat g0 g1 y' = zh := hzu _ ⟨r1, r2, r3⟩
  have hx' : ∀ t, y' t 2 = x t := by
    intro t
    induction t with
    | zero => rw [hy'.2.2.2.1]; rfl
    | succ t ih =>
      rw [r4 t, ih, hz']
      change _ = c t + μ • x t
      simp only [hc_def]
      abel
  funext t i
  fin_cases i
  · have := congrFun (congrFun hz' t) 0
    change y' t 0 - g0 • y' t 2 = zh t 0 at this
    change y' t 0 = zh t 0 + g0 • x t
    rw [← hx' t, ← this]; abel
  · have := congrFun (congrFun hz' t) 1
    change y' t 1 - g1 • y' t 2 = zh t 1 at this
    change y' t 1 = zh t 1 + g1 • x t
    rw [← hx' t, ← this]; abel
  · exact hx' t

/-- **The Blanchard–Kahn theorem, sufficiency** (Woodford (2003), Prop. C.2, p. 672): exactly one
eigenvalue in the open unit disc and two outside the closed disc, together with the genericity
condition (the stable eigenvector has a nonzero predetermined component), imply determinacy. -/
theorem determinate3_of {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : OneInTwoOut (ch2 A) (ch1 A) (ch0 A)) (hg : Generic A) : Determinate3 𝔼 A := by
  obtain ⟨μ, T, D, hμ, hTD, hs⟩ := (oneInTwoOut_iff_real _ _ _).mp hA
  have hroot : cubicR (ch2 A) (ch1 A) (ch0 A) μ = 0 := by
    rw [cubicR_of_realSplit hs]; ring
  obtain ⟨v, hv0, hv⟩ := exists_eigvec hroot
  have hv2 : v 2 ≠ 0 := fun h => hv0 (hg μ v hμ hv h)
  have hrow : ∀ i, A i 0 * v 0 + A i 1 * v 1 + A i 2 * v 2 = μ * v i := by
    intro i
    have := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply,
      smul_eq_mul] at this
    exact this
  have hi : v 2 * (v 2)⁻¹ = 1 := mul_inv_cancel₀ hv2
  set g0 := v 0 / v 2 with hg0
  set g1 := v 1 / v 2 with hg1
  have e0 : A 0 0 * g0 + A 0 1 * g1 + A 0 2 = μ * g0 := by
    have := hrow 0
    rw [hg0, hg1, div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (v 2)⁻¹ * this - A 0 2 * hi
  have e1 : A 1 0 * g0 + A 1 1 * g1 + A 1 2 = μ * g1 := by
    have := hrow 1
    rw [hg0, hg1, div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (v 2)⁻¹ * this - A 1 2 * hi
  have e2 : A 2 0 * g0 + A 2 1 * g1 + A 2 2 = μ := by
    have := hrow 2
    rw [hg0, hg1, div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (v 2)⁻¹ * this - (A 2 2 - μ) * hi
  have hs' := realSplit_redC e0 e1 e2
  have hT : T = tr2 (redC A g0 g1) := by
    have := hs.1.symm.trans hs'.1; linarith
  have hD : D = det2 (redC A g0 g1) := by
    have h1 := hs.2.1.symm.trans hs'.2.1
    rw [hT] at h1; linarith
  rw [hT, hD] at hTD
  exact determinate3_of_reduction 𝔼 hμ e0 e1 e2 hTD

/-- Woodford (2003), (C.19), p. 677: the disturbance direction `a = (0, −σ, 0)` of the IS relation
(the disturbance is `e_t = r̂ⁿ_t − ī_t + π̄`). -/
def aIS (σ : ℝ) : Fin 3 → ℝ := ![0, -σ, 0]

/-! ### Proposition 4.4: the inertial Taylor rule (2.8) -/

/-- Woodford (2003), (1.12), (1.13), (2.8), pp. 246, 255 (App. C.3, (C.21)): equilibrium of the
basic model under the inertial rule, in deviations from the target steady state:
`y_t = (π_t − π̄, x_t − x̄, ı̂_{t−1} − ī_{t−1})`, so `ı̂_t − ī_t` is `y_{t+1,2}`. The NKPC (1.13),
the IS relation (1.12) with disturbance `e_t = r̂ⁿ_t − ī_t + π̄`, and the rule (2.8) hold at every
date; `ı̂_{−1} − ī_{−1} = i₀` is given; the solution is adapted and bounded. -/
def Equil44 (β κ σ ρ φπ φx : ℝ) (e : ℕ → Ω → ℝ) (i0 : ℝ) (y : ℕ → Fin 3 → Ω → ℝ) : Prop :=
  (∀ t, y t 0 = κ • y t 1 + β • 𝔼.E t (y (t + 1) 0)) ∧
  (∀ t, y t 1 = 𝔼.E t (y (t + 1) 1) - σ • (y (t + 1) 2 - 𝔼.E t (y (t + 1) 0)) + σ • e t) ∧
  (∀ t, y (t + 1) 2 = ρ • y t 2 + φπ • y t 0 + (φx / 4) • y t 1) ∧
  y 0 2 = (fun _ => i0) ∧ VAdapted 𝔼 y ∧ VBounded y

/-- Woodford (2003), Prop. 4.4, p. 255: equilibrium under the rule (2.8) is determinate — for
every bounded adapted disturbance and every initial interest rate there is exactly one bounded
equilibrium. -/
def Determinate44 (β κ σ ρ φπ φx : ℝ) : Prop :=
  ∀ e : ℕ → Ω → ℝ, BoundedProc e → 𝔼.Adapted e → ∀ i0 : ℝ,
    ∃! y, Equil44 𝔼 β κ σ ρ φπ φx e i0 y

/-- Woodford (2003), (C.21), p. 678: the matrix `A` of the inertial-rule system. -/
noncomputable def A44 (β κ σ ρ φπ φx : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![β⁻¹, -(β⁻¹ * κ), 0; σ * (φπ - β⁻¹), 1 + σ * (φx / 4 + β⁻¹ * κ), σ * ρ; φπ, φx / 4, ρ]

/-- Woodford (2003), (C.21), p. 678: `A v` written out. -/
theorem mulVec_A44 (β κ σ ρ φπ φx : ℝ) (v : Fin 3 → ℝ) :
    A44 β κ σ ρ φπ φx *ᵥ v = ![β⁻¹ * v 0 - β⁻¹ * κ * v 1,
      σ * (φπ - β⁻¹) * v 0 + (1 + σ * (φx / 4 + β⁻¹ * κ)) * v 1 + σ * ρ * v 2,
      φπ * v 0 + φx / 4 * v 1 + ρ * v 2] := by
  funext i
  fin_cases i <;> simp [A44, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- Woodford (2003), (C.21), p. 678: `q A` written out. -/
theorem vecMul_A44 (β κ σ ρ φπ φx : ℝ) (q : Fin 3 → ℝ) :
    q ᵥ* A44 β κ σ ρ φπ φx = ![β⁻¹ * q 0 + σ * (φπ - β⁻¹) * q 1 + φπ * q 2,
      -(β⁻¹ * κ) * q 0 + (1 + σ * (φx / 4 + β⁻¹ * κ)) * q 1 + φx / 4 * q 2,
      σ * ρ * q 1 + ρ * q 2] := by
  funext i
  fin_cases i <;> simp [A44, Matrix.vecMul, dotProduct, Fin.sum_univ_three] <;> ring

/-- Woodford (2003), (C.21), p. 678: the model (1.12), (1.13), (2.8) is exactly the system
`E_t y_{t+1} = A y_t + a e_t` with one predetermined variable. -/
theorem equil44_iff {β κ σ ρ φπ φx : ℝ} (hβ : β ≠ 0) (e : ℕ → Ω → ℝ) (i0 : ℝ)
    (y : ℕ → Fin 3 → Ω → ℝ) :
    Equil44 𝔼 β κ σ ρ φπ φx e i0 y ↔
      Equil3 𝔼 (A44 β κ σ ρ φπ φx) (fun t i => aIS σ i • e t) i0 y := by
  have hb : β⁻¹ * β = 1 := inv_mul_cancel₀ hβ
  constructor
  · rintro ⟨hN, hI, hR, h0, ha, hbd⟩
    have hp : ∀ t, 𝔼.E t (y (t + 1) 2) = y (t + 1) 2 := by
      intro t
      rw [hR t, map_add, map_add, map_smul, map_smul, map_smul, ha t 0, ha t 1, ha t 2]
    refine ⟨fun t i => ?_, ha, hp, h0, hbd⟩
    funext ω
    have n := congrFun (hN t) ω
    have s := congrFun (hI t) ω
    have r := congrFun (hR t) ω
    have p := congrFun (hp t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at n s r p
    fin_cases i <;> simp [rvMul_apply, Fin.sum_univ_three, A44, aIS]
    · linear_combination (-β⁻¹) * n - (𝔼.E t (y (t + 1) 0) ω) * hb
    · linear_combination (-1 : ℝ) * s + σ * r + σ * β⁻¹ * n + σ * (𝔼.E t (y (t + 1) 0) ω) * hb
    · linear_combination p + r
  · rintro ⟨hs, ha, hp, h0, hbd⟩
    have row : ∀ t (i : Fin 3) ω, 𝔼.E t (y (t + 1) i) ω =
        (rvMul (A44 β κ σ ρ φπ φx) (y t) i + aIS σ i • e t) ω := fun t i ω => congrFun (hs t i) ω
    have r0 : ∀ t ω, 𝔼.E t (y (t + 1) 0) ω = β⁻¹ * y t 0 ω - β⁻¹ * κ * y t 1 ω := by
      intro t ω
      rw [row]
      simp [rvMul_apply, Fin.sum_univ_three, A44, aIS]
      ring
    have r1 : ∀ t ω, 𝔼.E t (y (t + 1) 1) ω = σ * (φπ - β⁻¹) * y t 0 ω +
        (1 + σ * (φx / 4 + β⁻¹ * κ)) * y t 1 ω + σ * ρ * y t 2 ω - σ * e t ω := by
      intro t ω
      rw [row]
      simp [rvMul_apply, Fin.sum_univ_three, A44, aIS]
      ring
    have r2 : ∀ t ω, y (t + 1) 2 ω = φπ * y t 0 ω + φx / 4 * y t 1 ω + ρ * y t 2 ω := by
      intro t ω
      rw [← hp t, row]
      simp [rvMul_apply, Fin.sum_univ_three, A44, aIS]
    refine ⟨fun t => ?_, fun t => ?_, fun t => ?_, h0, ha, hbd⟩ <;> funext ω <;>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    · rw [r0]; linear_combination (-(y t 0 ω - κ * y t 1 ω)) * hb
    · rw [r1, r0, r2]; ring
    · rw [r2]; ring

/-- Woodford (2003), Prop. 4.4, p. 255: determinacy of the model is determinacy of the system
`E_t y_{t+1} = A y_t + a e_t` in the sense of `BlanchardKahn.DeterminateFor`. -/
theorem determinate44_iff_for {β κ σ ρ φπ φx : ℝ} (hβ : β ≠ 0) :
    Determinate44 𝔼 β κ σ ρ φπ φx ↔ DeterminateFor 𝔼 (A44 β κ σ ρ φπ φx) (aIS σ) := by
  unfold Determinate44 DeterminateFor
  simp only [equil44_iff 𝔼 hβ]

/-- Woodford (2003), p. 678 (App. C.3): `A₂ = −β⁻¹(1 + κσ) − 1 − ρ − σφ_x/4`. -/
theorem ch2_A44 (β κ σ ρ φπ φx : ℝ) :
    ch2 (A44 β κ σ ρ φπ φx) = -(β⁻¹ * (1 + κ * σ)) - 1 - ρ - σ * φx / 4 := by
  simp [ch2, A44]; ring

/-- Woodford (2003), p. 678 (App. C.3): `A₁ = ρ + β⁻¹(1 + ρ(1 + κσ)) + β⁻¹σ(κφ_π + φ_x/4)`. -/
theorem ch1_A44 (β κ σ ρ φπ φx : ℝ) :
    ch1 (A44 β κ σ ρ φπ φx) =
      ρ + β⁻¹ * (1 + ρ * (1 + κ * σ)) + β⁻¹ * σ * (κ * φπ + φx / 4) := by
  simp [ch1, A44]; ring

/-- Woodford (2003), p. 678 (App. C.3): `A₀ = −β⁻¹ρ`. -/
theorem ch0_A44 (β κ σ ρ φπ φx : ℝ) : ch0 (A44 β κ σ ρ φπ φx) = -(β⁻¹ * ρ) := by
  simp [ch0, A44]; ring

/-- Woodford (2003), (C.22), p. 678: `P(1) = (σκ/β)[φ_π + (1 − β)φ_x/(4κ) − (1 − ρ)]`, so (C.13)
is the Taylor principle (2.9). -/
theorem P1_A44 {β κ σ ρ φπ φx : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0) :
    P1 (ch2 (A44 β κ σ ρ φπ φx)) (ch1 (A44 β κ σ ρ φπ φx)) (ch0 (A44 β κ σ ρ φπ φx)) =
      σ * κ / β * (φπ + (1 - β) / (4 * κ) * φx - (1 - ρ)) := by
  rw [P1, ch2_A44, ch1_A44, ch0_A44]
  field_simp
  ring

/-- Woodford (2003), p. 678 (App. C.3): `P(−1) = −[2 + 2ρ + β⁻¹(2 + κσ + 2ρ + ρκσ) + β⁻¹σκφ_π +
(1 + β⁻¹)σφ_x/4]`. -/
theorem Pm1_A44 (β κ σ ρ φπ φx : ℝ) :
    Pm1 (ch2 (A44 β κ σ ρ φπ φx)) (ch1 (A44 β κ σ ρ φπ φx)) (ch0 (A44 β κ σ ρ φπ φx)) =
      -(2 + 2 * ρ + β⁻¹ * (2 + κ * σ + 2 * ρ + ρ * κ * σ) + β⁻¹ * σ * κ * φπ
        + (1 + β⁻¹) * σ * φx / 4) := by
  rw [Pm1, ch2_A44, ch1_A44, ch0_A44]
  ring

/-- Woodford (2003), p. 678 (App. C.3): under the sign restrictions (C.14) `P(−1) < 0` always
holds, so (C.12) is violated and Case I is excluded. -/
theorem Pm1_A44_neg {β κ σ ρ φπ φx : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 ≤ ρ)
    (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    Pm1 (ch2 (A44 β κ σ ρ φπ φx)) (ch1 (A44 β κ σ ρ φπ φx)) (ch0 (A44 β κ σ ρ φπ φx)) < 0 := by
  rw [Pm1_A44]
  have hb : 0 < β⁻¹ := inv_pos.mpr hβ
  have : 0 ≤ β⁻¹ * σ * κ * φπ := by positivity
  have : 0 ≤ (1 + β⁻¹) * σ * φx / 4 := by positivity
  have : 0 < β⁻¹ * (2 + κ * σ + 2 * ρ + ρ * κ * σ) := by positivity
  linarith

/-- Woodford (2003), (C.23), p. 678: the left-hand side
`φ_π + (1 − ρ)φ_x/(4κ) + (β⁻¹ − 1)[(κσ)⁻¹(1 − ρ)(β − ρ) − ρ]` (the bracket that pdftotext drops,
restored from the page image). -/
noncomputable def lhs23 (β κ σ ρ φπ φx : ℝ) : ℝ :=
  φπ + (1 - ρ) / (4 * κ) * φx + (β⁻¹ - 1) * ((1 - ρ) * (β - ρ) / (κ * σ) - ρ)

/-- Woodford (2003), (C.15) and (C.23), p. 678: `A₀² − A₀A₂ + A₁ − 1 = (σκ/β) · LHS(C.23)`, so
(C.15) is (C.23). -/
theorem C15_A44 {β κ σ ρ φπ φx : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0) (hσ : σ ≠ 0) :
    C15 (ch2 (A44 β κ σ ρ φπ φx)) (ch1 (A44 β κ σ ρ φπ φx)) (ch0 (A44 β κ σ ρ φπ φx)) =
      σ * κ / β * lhs23 β κ σ ρ φπ φx := by
  rw [C15, ch2_A44, ch1_A44, ch0_A44, lhs23]
  field_simp
  ring

/-- Woodford (2003), (C.24), p. 679: `β⁻¹(1 + κσ) + ρ + σφ_x/4 > 2`. -/
def C24 (β κ σ ρ φx : ℝ) : Prop := 2 < β⁻¹ * (1 + κ * σ) + ρ + σ * φx / 4

/-- Woodford (2003), (C.24) and fn. 4, p. 679: (C.24) is exactly `A₂ < −3`, the relevant half of
(C.17). -/
theorem C24_iff (β κ σ ρ φπ φx : ℝ) : C24 β κ σ ρ φx ↔ ch2 (A44 β κ σ ρ φπ φx) < -3 := by
  rw [C24, ch2_A44]
  constructor <;> intro h <;> linarith

/-- Woodford (2003), p. 679: `β + β⁻¹ > 2` for `0 < β < 1`. -/
theorem add_inv_gt_two {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : 2 < β + β⁻¹ := by
  have h : β⁻¹ * β = 1 := inv_mul_cancel₀ hβ0.ne'
  have hb : 1 < β⁻¹ := one_lt_inv₀ hβ0 |>.mpr hβ1
  nlinarith

/-- Woodford (2003), p. 679: "(C.24) can fail to hold only if `ρ < β`". -/
theorem rho_lt_beta_of_not_C24 {β κ σ ρ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hφx : 0 ≤ φx) (h : ¬ C24 β κ σ ρ φx) : ρ < β := by
  unfold C24 at h
  push Not at h
  have := add_inv_gt_two hβ0 hβ1
  have hb : 0 < β⁻¹ := inv_pos.mpr hβ0
  have : 0 ≤ β⁻¹ * (κ * σ) := by positivity
  have : 0 ≤ σ * φx / 4 := by positivity
  nlinarith

/-- **The corner argument** (Woodford (2003), App. C.3, pp. 679–680, Fig. C.1), formalised: with
`ρ_m = 2 − β⁻¹(1 + κσ) − σφ_x/4` the largest `ρ` at which (C.24) is (weakly) violated and
`F = φ_x/(4κ)`,
`LHS(C.23) = [φ_π + (1 − β)F − (1 − ρ)] + (ρ_m − ρ) K + (β − ρ_m)²/(βκσ)`
with `K = β⁻¹ + F + (β⁻¹ − 1)(1 + β − ρ − ρ_m)/(κσ)`: the first term is the slack in (C.22), the
second the monotonicity of LHS(C.23) in `ρ` (and in `φ_π`), the third the corner value. -/
theorem lhs23_decomp {β κ σ ρ φπ φx : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0) (hσ : σ ≠ 0) :
    lhs23 β κ σ ρ φπ φx =
      (φπ + (1 - β) / (4 * κ) * φx - (1 - ρ)) +
      ((2 - β⁻¹ * (1 + κ * σ) - σ * φx / 4) - ρ) *
        (β⁻¹ + φx / (4 * κ) + (β⁻¹ - 1) * (1 + β - ρ - (2 - β⁻¹ * (1 + κ * σ) - σ * φx / 4))
          / (κ * σ)) +
      (β - (2 - β⁻¹ * (1 + κ * σ) - σ * φx / 4)) ^ 2 / (β * (κ * σ)) := by
  rw [lhs23]
  field_simp
  ring

/-- Woodford (2003), App. C.3, p. 680: (C.22) and the failure of (C.24) imply (C.23) — the values
of Fig. C.1 where (C.22) holds and (C.24) fails lie inside the region where (C.23) holds. -/
theorem lhs23_pos_of_not_C24 {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hφx : 0 ≤ φx)
    (h22 : 1 - ρ < φπ + (1 - β) / (4 * κ) * φx) (h24 : ¬ C24 β κ σ ρ φx) :
    0 < lhs23 β κ σ ρ φπ φx := by
  have hρβ := rho_lt_beta_of_not_C24 hβ0 hβ1 hκ hσ hφx h24
  unfold C24 at h24
  push Not at h24
  set ρm := 2 - β⁻¹ * (1 + κ * σ) - σ * φx / 4 with hρm
  have hm1 : ρ ≤ ρm := by rw [hρm]; linarith
  have hm2 : ρm < β := by
    have := add_inv_gt_two hβ0 hβ1
    have hb : 0 < β⁻¹ := inv_pos.mpr hβ0
    have : 0 ≤ β⁻¹ * (κ * σ) := by positivity
    have : 0 ≤ σ * φx / 4 := by positivity
    rw [hρm]; nlinarith
  rw [lhs23_decomp hβ0.ne' hκ.ne' hσ.ne', ← hρm]
  have hb1 : 1 < β⁻¹ := one_lt_inv₀ hβ0 |>.mpr hβ1
  have hu : 0 < κ * σ := mul_pos hκ hσ
  have t1 : 0 < φπ + (1 - β) / (4 * κ) * φx - (1 - ρ) := by linarith
  have hK : 0 ≤ β⁻¹ + φx / (4 * κ) + (β⁻¹ - 1) * (1 + β - ρ - ρm) / (κ * σ) := by
    have : 0 ≤ (β⁻¹ - 1) * (1 + β - ρ - ρm) := mul_nonneg (by linarith) (by linarith)
    have : 0 ≤ φx / (4 * κ) := by positivity
    have : 0 ≤ (β⁻¹ - 1) * (1 + β - ρ - ρm) / (κ * σ) := by positivity
    linarith
  have t2 : 0 ≤ (ρm - ρ) * (β⁻¹ + φx / (4 * κ) + (β⁻¹ - 1) * (1 + β - ρ - ρm) / (κ * σ)) :=
    mul_nonneg (by linarith) hK
  have t3 : 0 ≤ (β - ρm) ^ 2 / (β * (κ * σ)) := by positivity
  linarith

/-- Woodford (2003), App. C.3, p. 679: under the sign restrictions and the Taylor principle (2.9),
Case II or Case III′ of Prop. C.2 holds, so `A` has one eigenvalue inside and two outside the
unit circle. -/
theorem oneInTwoOut_A44 {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (h29 : 1 - ρ < φπ + (1 - β) / (4 * κ) * φx) :
    OneInTwoOut (ch2 (A44 β κ σ ρ φπ φx)) (ch1 (A44 β κ σ ρ φπ φx)) (ch0 (A44 β κ σ ρ φπ φx)) := by
  have hP1 : 0 < P1 (ch2 (A44 β κ σ ρ φπ φx)) (ch1 (A44 β κ σ ρ φπ φx))
      (ch0 (A44 β κ σ ρ φπ φx)) := by
    rw [P1_A44 hβ0.ne' hκ.ne']
    have : 0 < σ * κ / β := by positivity
    exact mul_pos this (by linarith)
  have hPm1 := Pm1_A44_neg hβ0 hκ hσ hρ hφπ hφx
  apply oneInTwoOut_of_cases
  by_cases h24 : C24 β κ σ ρ φx
  · right; right
    refine ⟨hP1, hPm1, ?_⟩
    have := (C24_iff β κ σ ρ φπ φx).mp h24
    rw [abs_of_neg (by linarith)]
    linarith
  · right; left
    refine ⟨hP1, hPm1, ?_⟩
    rw [C15_A44 hβ0.ne' hκ.ne' hσ.ne']
    exact mul_pos (by positivity) (lhs23_pos_of_not_C24 hβ0 hβ1 hκ hσ hφx h29 h24)

/-- Woodford (2003), Prop. 4.4 (the genericity the book leaves implicit): if the rule responds to
inflation or the output gap (`φ_π > 0` or `φ_x > 0`), no eigenvector of an eigenvalue in the unit
disc has a zero lagged-interest-rate component. -/
theorem generic_A44 {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (hφ : 0 < φπ ∨ 0 < φx) : Generic (A44 β κ σ ρ φπ φx) := by
  intro μ v hμ hv h2
  rw [mulVec_A44] at hv
  have r0 : β⁻¹ * v 0 - β⁻¹ * κ * v 1 = μ * v 0 := congrFun hv 0
  have r2 : φπ * v 0 + φx / 4 * v 1 + ρ * v 2 = μ * v 2 := congrFun hv 2
  rw [h2] at r2
  have hb1 : 1 < β⁻¹ := one_lt_inv₀ hβ0 |>.mpr hβ1
  have hμ1 : μ < 1 := (abs_lt.mp hμ).2
  have hcoef : 0 < 4 * β⁻¹ * κ * φπ + φx * (β⁻¹ - μ) := by
    rcases hφ with h | h
    · have : 0 ≤ φx * (β⁻¹ - μ) := mul_nonneg hφx (by linarith)
      have : 0 < 4 * β⁻¹ * κ * φπ := by positivity
      linarith
    · have : 0 < φx * (β⁻¹ - μ) := mul_pos h (by linarith)
      have : 0 ≤ 4 * β⁻¹ * κ * φπ := by positivity
      linarith
  have hv0 : v 0 = 0 := by
    have e : v 0 * (4 * β⁻¹ * κ * φπ + φx * (β⁻¹ - μ)) = 0 := by
      linear_combination (4 * β⁻¹ * κ) * r2 + φx * r0
    rcases mul_eq_zero.mp e with e | e
    · exact e
    · linarith
  have hv1 : v 1 = 0 := by
    rw [hv0] at r0
    have hbk : β⁻¹ * κ ≠ 0 := by positivity
    have : β⁻¹ * κ * v 1 = 0 := by linarith
    rcases mul_eq_zero.mp this with e | e
    · exact absurd e hbk
    · exact e
  funext i
  fin_cases i
  · exact hv0
  · exact hv1
  · exact h2

/-- **Proposition 4.4, sufficiency** (Woodford (2003), p. 255, proof App. C.3, pp. 677–680;
restated from the Chapter 4 project's corrected `prop44`): for `0 < β < 1`, `κ, σ > 0`,
`ρ, φ_π, φ_x ≥ 0`, if (2.9) `φ_π + (1 − β)φ_x/(4κ) > 1 − ρ` holds and the rule responds to
inflation or the output gap, equilibrium under the inertial rule (2.8) is determinate. -/
theorem prop44_sufficient {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (h29 : 1 - ρ < φπ + (1 - β) / (4 * κ) * φx) (hφ : 0 < φπ ∨ 0 < φx) :
    Determinate44 𝔼 β κ σ ρ φπ φx := by
  rw [determinate44_iff_for 𝔼 hβ0.ne']
  exact determinateFor_of_determinate3 𝔼
    (determinate3_of 𝔼 (oneInTwoOut_A44 hβ0 hβ1 hκ hσ hρ hφπ hφx h29)
      (generic_A44 hβ0 hβ1 hκ hφπ hφx hφ)) _

/-- Woodford (2003), p. 368, Fig. 5.8 and fn. 35 (**the alternative reading of survey error 8,
proved**): rule (2.8) with `φ_π = .6`, `φ_x = .3`, `ρ = .7` at the Table 5.1 values
`β = .99`, `κ = .024`, `σ = 1/.16` gives a determinate equilibrium (Proposition 4.4: (2.9)
`.6 + .01·.3/.096 ≈ .63 > .3`), with long-run responses `Φ_π = 2`, `Φ_x = 1`
(`fn35_rule28_longrun`) — whereas rule (1.12) with the same coefficients is indeterminate
(`fig58_rule112_indeterminate`). -/
theorem fig58_rule28_determinate : Determinate44 𝔼 0.99 0.024 (1 / 0.16) 0.7 0.6 0.3 :=
  prop44_sufficient 𝔼 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))

end Prop44

end Woodford.PolicyResponseDynamics.SmallModels
