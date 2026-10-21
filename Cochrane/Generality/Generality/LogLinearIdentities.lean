/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.Money
import Generality.LongTermDebt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Linearized flow, present-value, and bond-return identities

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.5, pp. 62–71, and Online
Appendix A1.2–A1.3, pp. 556–564.

## The nonlinear identities and their exact linearization (A1.2)

* (1.4)–(1.6): `marketValue`, `overnightValue`, `nominalReturn`, `flow_value_identity`.
* (1.7)–(1.8): `flow_gdp`, `pv_gdp_finite`, `pv_gdp_iff`.
* (1.9): `log_flow_identity`.
* (1.10)–(1.13): `logFlow`, `logFlow_hasFDerivAt` (exact derivative at the steady state),
  `rho_eq` (`ρ = e^{−(r−g)}`, survey E11; the printed `e^{r−g}` of p. 63 is wrong:
  `printed_rho_eq_iff`, `printed_rho_lt_one_iff`), `rho_lt_one_iff`, `logFlow_hasFDerivAt_rho`,
  `constant_1_11`, `constant_zero_of_rg`, `tangent_1_11`; the scaling of the surplus `stilde_eq`.

## The linear model (§3.5) on an arbitrary `ExpectationSystem`

* (3.17): `Flow317`; `LinearEconomy` (bounded "stationary" processes, `0 < ρ < 1`).
* (3.18): `pv_318`; (3.19): `pv_318_E`, `pv_319_iff`, `terminal_of_bounded`, `pv_319`,
  `pv_319_E_outside`, and the `ρ = 1` version in deviations from the mean `pv_rho_one`.
* p. 64: `price_expected_return`.
* Innovations `innov` (`ΔE_{t+1} = E_{t+1} − E_t`): `innov_apply`, `innov_known`, `abs_innov_le`,
  `summable_innov`; `innov_pv` and (3.20) `innov_identity_3_20`.
* A1.3: `return_indep_weights` (1.21), `geomQ` (1.23), `geomQ_short`, `geomQ_perpetuity`,
  `geom_portfolio_return`, `bondReturn_hasFDerivAt` (1.22, exact coefficient `ω/(1+i)`),
  `bondReturn_steady` and `omega_hat_eq_iff` (survey E15).
* The linear bond identity with free parameter `ω̂` (`= ω/(1+i)` for the exact derivative, `= ω`
  in (1.24)): `BondRet`, `BondPriceOK`, `bondPrice_forward` (`q_t = −∑_{j≥1} ω̂^{j−1} r^n_{t+j}`),
  survey E16 `printed_bondPrice_iff`, `printed_bondPrice_counterexample`; (3.21)/(1.25)
  `bondReturn_innov`, `bondReturn_innov_real`; `EH_bond`; (3.22) `weighted_inflation_identity`.
* Special cases: `short_debt_return_known`, `short_debt_EH`, `innov_r_zero`,
  `special_constant_short` (§3.5.2, (3.27)), `special_varying_short`, `special_constant_long`
  (3.23), `identity_3_24`, `identity_3_25`, `monetary_disinflation` (3.28),
  `perpetuity_no_discount_terms` (§3.5.4), `weights_close`, `scaling_ratio`.
* Sequences and Figure 3.1: `perm_inflation_equiv`, `zero_current_inflation_possible`,
  `disinflation_seq`, `fig31_jump`, `fig31_value`, `fig31_path`, `expected_rise_no_jump`,
  `announcement_jump`, `disinflation_monotone_omega`, `disinflation_monotone_length`; the exact
  nonlinear jump of A1 (1.14)–(1.16) is `LongTermDebt.jumpRatio` (`LongTermDebt.geom_value`,
  `LongTermDebt.price_jump_of_valuation`, 3.41% in `LongTermDebt.omega_08_example`);
  `fig31_log` (log drop 3.47%, the text's "3.5%"), `fig31_linear_exact_coeff` (3.48% with
  `ω̂ = ω/(1+i)`) (survey E15).
-/

namespace Cochrane.Generality.LogLinearIdentities

open Filter Topology

/-! ### The nonlinear flow and present-value identities (A1.2) -/

/-- Cochrane (2023), A1.2, p. 556: the nominal end-of-period market value of the debt,
`V_t = M_t + ∑_{j≥0} Q_t^{(t+1+j)} B_t^{(t+1+j)}` (`Q t n` is the date-`t` price of the zero-coupon
bond due at `n`, `B t n` the face value outstanding at the end of `t`). -/
noncomputable def marketValue (M : ℕ → ℝ) (Q B : ℕ → ℕ → ℝ) (t : ℕ) : ℝ :=
  M t + ∑' j, Q t (t + 1 + j) * B t (t + 1 + j)

/-- Cochrane (2023), A1 (1.4), p. 557: the value at the beginning of `t + 1` of the debt held
overnight, `M_t + ∑_{j≥0} Q_{t+1}^{(t+1+j)} B_t^{(t+1+j)}`. -/
noncomputable def overnightValue (M : ℕ → ℝ) (Q B : ℕ → ℕ → ℝ) (t : ℕ) : ℝ :=
  M t + ∑' j, Q (t + 1) (t + 1 + j) * B t (t + 1 + j)

/-- Cochrane (2023), A1 (1.4), p. 557: the nominal return on the government debt portfolio. -/
noncomputable def nominalReturn (M : ℕ → ℝ) (Q B : ℕ → ℕ → ℝ) (t : ℕ) : ℝ :=
  overnightValue M Q B t / marketValue M Q B t

/-- Cochrane (2023), A1 (1.5)–(1.6), p. 557: the flow identity (1.5), overnight value equals
`P_{t+1}sp_{t+1} + V_{t+1}`, is exactly `V_t R^n_{t+1} = P_{t+1}sp_{t+1} + V_{t+1}`. -/
theorem flow_value_identity (M : ℕ → ℝ) (Q B : ℕ → ℕ → ℝ) (P sp : ℕ → ℝ) (t : ℕ)
    (hV : marketValue M Q B t ≠ 0) :
    overnightValue M Q B t = P (t + 1) * sp (t + 1) + marketValue M Q B (t + 1) ↔
      marketValue M Q B t * nominalReturn M Q B t =
        P (t + 1) * sp (t + 1) + marketValue M Q B (t + 1) := by
  rw [nominalReturn, mul_div_cancel₀ _ hV]

/-- Cochrane (2023), A1 (1.7), p. 557: the flow identity in ratios to GDP,
`V_t/(P_t y_t) · R^n_{t+1}/(G_{t+1}Π_{t+1}) = sp_{t+1}/y_{t+1} + V_{t+1}/(P_{t+1}y_{t+1})`, with
`Π_{t+1} = P_{t+1}/P_t`, `G_{t+1} = y_{t+1}/y_t`. -/
theorem flow_gdp {V R P y sp : ℕ → ℝ} (t : ℕ) (hP : ∀ n, P n ≠ 0) (hy : ∀ n, y n ≠ 0)
    (h16 : V t * R t = P (t + 1) * sp (t + 1) + V (t + 1)) :
    V t / (P t * y t) * (R t / (y (t + 1) / y t * (P (t + 1) / P t))) =
      sp (t + 1) / y (t + 1) + V (t + 1) / (P (t + 1) * y (t + 1)) := by
  have h1 := hP t
  have h2 := hP (t + 1)
  have h3 := hy t
  have h4 := hy (t + 1)
  have e : V t / (P t * y t) * (R t / (y (t + 1) / y t * (P (t + 1) / P t))) =
      V t * R t / (P (t + 1) * y (t + 1)) := by
    field_simp
  rw [e, h16]
  field_simp

/-- Cochrane (2023), A1 (1.8), p. 557, finite horizon: with `x_t = V_t/(P_ty_t)`, discount
`D_{t+1} = Π_{t+1}G_{t+1}/R^n_{t+1}` and `sy = sp/y`, the flow (1.7) iterates to
`x_t = ∑_{j<T} (∏_{k≤j} D_{t+1+k}) sy_{t+1+j} + (∏_{k<T} D_{t+1+k}) x_{t+T}`. -/
theorem pv_gdp_finite {x D sy : ℕ → ℝ} (h17 : ∀ n, x n = D (n + 1) * (sy (n + 1) + x (n + 1)))
    (t T : ℕ) :
    x t = ∑ j ∈ Finset.range T, (∏ k ∈ Finset.range j, D (t + k + 1)) *
        (D (t + j + 1) * sy (t + j + 1)) +
      (∏ k ∈ Finset.range T, D (t + k + 1)) * x (t + T) :=
  Money.iterate_discount (x := x) (a := fun n => D (n + 1) * sy (n + 1)) (b := fun n => D (n + 1))
    (fun n => by rw [h17 n]; ring) t T

/-- Cochrane (2023), A1 (1.8), p. 557 ("I assume here that the right-hand side converges.
Otherwise, keep the limiting debt term"): given summability, the nonlinear present-value identity
holds iff the discounted terminal debt/GDP ratio tends to zero. -/
theorem pv_gdp_iff {x D sy : ℕ → ℝ} (h17 : ∀ n, x n = D (n + 1) * (sy (n + 1) + x (n + 1)))
    (t : ℕ) (hs : Summable fun j => (∏ k ∈ Finset.range j, D (t + k + 1)) *
      (D (t + j + 1) * sy (t + j + 1))) :
    Tendsto (fun T => (∏ k ∈ Finset.range T, D (t + k + 1)) * x (t + T)) atTop (𝓝 0) ↔
      x t = ∑' j, (∏ k ∈ Finset.range j, D (t + k + 1)) * (D (t + j + 1) * sy (t + j + 1)) :=
  Money.pv_discount_iff (x := x) (a := fun n => D (n + 1) * sy (n + 1)) (b := fun n => D (n + 1))
    (fun n => by rw [h17 n]; ring) t hs

/-- Cochrane (2023), A1 (1.9), p. 558: taking logs of (1.7),
`v_t + r^n_{t+1} − π_{t+1} − g_{t+1} = log(sy_{t+1} + e^{v_{t+1}})`, where `v = log(V/(Py))`,
`r^n = log R^n`, `π = log Π`, `g = log G` (all exact, for positive values). -/
theorem log_flow_identity {x x' R Pi G sy : ℝ} (hx : 0 < x) (hx' : 0 < x') (hR : 0 < R)
    (hPi : 0 < Pi) (hG : 0 < G) (h17 : x * (R / (G * Pi)) = sy + x') :
    Real.log x + Real.log R - Real.log Pi - Real.log G =
      Real.log (sy + Real.exp (Real.log x')) := by
  rw [Real.exp_log hx', ← h17, Real.log_mul hx.ne' (div_pos hR (mul_pos hG hPi)).ne',
    Real.log_div hR.ne' (mul_pos hG hPi).ne', Real.log_mul hG.ne' hPi.ne']
  ring

/-- Cochrane (2023), A1 (1.9)–(1.10), p. 558: the right-hand side of the log flow identity as a
function of `(v_{t+1}, sy_{t+1})`: `log(sy + e^v)`. -/
noncomputable def logFlow (p : ℝ × ℝ) : ℝ := Real.log (p.2 + Real.exp p.1)

/-- Cochrane (2023), A1 (1.10)–(1.11), p. 558: the exact derivative of `log(sy + e^{v'})` at
`(v, sy)` is `(e^v/(e^v + sy), 1/(e^v + sy))`. -/
theorem logFlow_hasFDerivAt {v sy : ℝ} (h : 0 < Real.exp v + sy) :
    HasFDerivAt logFlow ((Real.exp v / (Real.exp v + sy)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (1 / (Real.exp v + sy)) • ContinuousLinearMap.snd ℝ ℝ ℝ) (v, sy) := by
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => p.2 + Real.exp p.1)
      (ContinuousLinearMap.snd ℝ ℝ ℝ + Real.exp (v, sy).1 • ContinuousLinearMap.fst ℝ ℝ ℝ)
      (v, sy) :=
    hasFDerivAt_snd.add hasFDerivAt_fst.exp
  have hne : (fun p : ℝ × ℝ => p.2 + Real.exp p.1) (v, sy) ≠ 0 := by
    simp only
    linarith
  refine (h1.log hne).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun p => ?_
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  field_simp
  ring

/-- Cochrane (2023), A1 (1.11)–(1.12), p. 558 (and survey E11): at a steady state
`r − g = log((e^v + sy)/e^v)`, the coefficient `e^v/(e^v + sy)` equals `ρ = e^{−(r−g)}`. -/
theorem rho_eq {v sy rg : ℝ} (h : 0 < Real.exp v + sy)
    (hss : rg = Real.log ((Real.exp v + sy) / Real.exp v)) :
    Real.exp v / (Real.exp v + sy) = Real.exp (-rg) := by
  rw [hss, Real.exp_neg, Real.exp_log (div_pos h (Real.exp_pos v)), inv_div]

/-- Cochrane (2023), p. 63 (survey E11): the printed `ρ = e^{r−g}` agrees with the correct
`ρ = e^{−(r−g)}` only when `r = g`. -/
theorem printed_rho_eq_iff (rg : ℝ) : Real.exp rg = Real.exp (-rg) ↔ rg = 0 := by
  rw [Real.exp_eq_exp]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 63 ("everyone is so used to `ρ < 1`", survey E11): with the correct
`ρ = e^{−(r−g)}`, `ρ < 1` iff `r > g`, iff the steady-state surplus is positive. -/
theorem rho_lt_one_iff {v sy rg : ℝ} (h : 0 < Real.exp v + sy)
    (hss : rg = Real.log ((Real.exp v + sy) / Real.exp v)) :
    (Real.exp (-rg) < 1 ↔ 0 < rg) ∧ (Real.exp (-rg) < 1 ↔ 0 < sy) := by
  refine ⟨by rw [Real.exp_lt_one_iff]; constructor <;> intro h <;> linarith, ?_⟩
  rw [← rho_eq h hss, div_lt_one h]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 63 (survey E11): the printed `e^{r−g}` is below one iff `r < g`, the
opposite of the steady state with positive surpluses. -/
theorem printed_rho_lt_one_iff (rg : ℝ) : Real.exp rg < 1 ↔ rg < 0 := Real.exp_lt_one_iff

/-- Cochrane (2023), A1 (1.11)–(1.12), p. 558: the exact derivative written with
`ρ = e^{−(r−g)}`: `D logFlow (v, sy) = ρ dv' + (ρ/e^v) dsy'`. -/
theorem logFlow_hasFDerivAt_rho {v sy rg : ℝ} (h : 0 < Real.exp v + sy)
    (hss : rg = Real.log ((Real.exp v + sy) / Real.exp v)) :
    HasFDerivAt logFlow (Real.exp (-rg) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (Real.exp (-rg) / Real.exp v) • ContinuousLinearMap.snd ℝ ℝ ℝ) (v, sy) := by
  have hρ : Real.exp (-rg) / Real.exp v = 1 / (Real.exp v + sy) := by
    rw [← rho_eq h hss]
    field_simp
  rw [hρ, ← rho_eq h hss]
  exact logFlow_hasFDerivAt h

/-- Cochrane (2023), A1 (1.11), p. 558: the constant of the linearization,
`log(e^v + sy) − ρv − ρ sy/e^v = r − g + (1 − ρ)(v − 1)`. -/
theorem constant_1_11 {v sy rg : ℝ} (h : 0 < Real.exp v + sy)
    (hss : rg = Real.log ((Real.exp v + sy) / Real.exp v)) :
    logFlow (v, sy) - Real.exp (-rg) * v - Real.exp (-rg) * (sy / Real.exp v) =
      rg + (1 - Real.exp (-rg)) * (v - 1) := by
  have hl : logFlow (v, sy) = v + rg := by
    rw [logFlow, hss, Real.log_div h.ne' (Real.exp_pos v).ne', Real.log_exp]
    simp only [add_comm sy]
    ring
  rw [hl, ← rho_eq h hss]
  have he := (Real.exp_pos v).ne'
  have hne := h.ne'
  field_simp
  ring

/-- Cochrane (2023), A1 p. 558 ("There is nothing wrong with expanding about `r = g`, `ρ = 1`, in
which case the constant in the identity is zero"). -/
theorem constant_zero_of_rg {v sy rg : ℝ} (h : 0 < Real.exp v + sy)
    (hss : rg = Real.log ((Real.exp v + sy) / Real.exp v)) (hrg : rg = 0) :
    logFlow (v, sy) - Real.exp (-rg) * v - Real.exp (-rg) * (sy / Real.exp v) = 0 ∧
      Real.exp (-rg) = 1 := by
  rw [constant_1_11 h hss, hrg, neg_zero, Real.exp_zero]
  ring_nf
  simp

/-- Cochrane (2023), A1 (1.11), p. 558: the right-hand side of (1.11),
`[r − g + (1 − ρ)(v − 1)] + ρv_{t+1} + ρ sy_{t+1}/e^v`, is exactly the first-order Taylor
polynomial (tangent) of `log(sy + e^{v'})` at the steady state. -/
theorem tangent_1_11 {v sy rg : ℝ} (h : 0 < Real.exp v + sy)
    (hss : rg = Real.log ((Real.exp v + sy) / Real.exp v)) (v' sy' : ℝ) :
    logFlow (v, sy) + (Real.exp (-rg) * (v' - v) + Real.exp (-rg) / Real.exp v * (sy' - sy)) =
      (rg + (1 - Real.exp (-rg)) * (v - 1)) + Real.exp (-rg) * v' +
        Real.exp (-rg) * (sy' / Real.exp v) := by
  rw [← constant_1_11 h hss]
  ring

/-- Cochrane (2023), p. 63 and A1 p. 558: the scaled surplus `s̃ = ρ sy/e^v` is the book's
`ρ/(V/(Py)) · s/y`, since `e^v` is the steady-state debt/GDP ratio `V/(Py)`. -/
theorem stilde_eq {ρ v VPy sy : ℝ} (hv : Real.exp v = VPy) :
    ρ * (sy / Real.exp v) = ρ / VPy * sy := by
  rw [hv]
  ring

/-! ### The linear model: (3.17)–(3.19) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), (3.17), p. 63: the linearized flow identity
`ρv_{t+1} = v_t + r_{t+1} − g_{t+1} − s̃_{t+1}` with real return `r = r^n − π`. -/
def Flow317 (ρ : ℝ) (v rn infl g sT : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, ρ * v (t + 1) ω = v t ω + (rn (t + 1) ω - infl (t + 1) ω) - g (t + 1) ω - sT (t + 1) ω

/-- Cochrane (2023), (3.18), p. 63: the flow "dividend" `s̃ + g − r` discounted in (3.18)–(3.19). -/
def zp (rn infl g sT : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := sT + g - (rn - infl)

/-- Cochrane (2023), (3.18), p. 63, exact and pathwise:
`v_t = ∑_{j=1}^{T} ρ^{j−1}(s̃_{t+j} + g_{t+j} − r_{t+j}) + ρ^T v_{t+T}`. -/
theorem pv_318 {ρ : ℝ} {v rn infl g sT : ℕ → Ω → ℝ} (hf : Flow317 ρ v rn infl g sT)
    (t T : ℕ) (ω : Ω) :
    v t ω = ∑ j ∈ Finset.range T, ρ ^ j * zp rn infl g sT (t + j + 1) ω + ρ ^ T * v (t + T) ω := by
  have h := Money.iterate_discount (x := fun n => v n ω)
    (a := fun n => zp rn infl g sT (n + 1) ω) (b := fun _ => ρ)
    (fun n => by simp only [zp, Pi.add_apply, Pi.sub_apply]; linarith [hf n ω]) t T
  simp only [Finset.prod_const, Finset.card_range] at h
  exact h

/-- Cochrane (2023), (3.18), p. 63 ("it holds ex-post, so it holds ex-ante. We can take `E_t`"):
`v_t = ∑_{j<T} ρ^j E_t(s̃ + g − r)_{t+1+j} + ρ^T E_t v_{t+T}` for adapted `v`. -/
theorem pv_318_E {ρ : ℝ} {v rn infl g sT : ℕ → Ω → ℝ} (hf : Flow317 ρ v rn infl g sT)
    (hv : 𝔼.Adapted v) (t T : ℕ) :
    v t = ∑ j ∈ Finset.range T, ρ ^ j • 𝔼.E t (zp rn infl g sT (t + j + 1)) +
      ρ ^ T • 𝔼.E t (v (t + T)) := by
  have hfun : v t = ∑ j ∈ Finset.range T, ρ ^ j • zp rn infl g sT (t + j + 1) +
      ρ ^ T • v (t + T) := by
    funext ω
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact pv_318 hf t T ω
  have h := congrArg (𝔼.E t) hfun
  rw [hv t, map_add, map_sum, map_smul] at h
  simp only [map_smul] at h
  exact h

/-- Cochrane (2023), (3.19), p. 64: given summability, the infinite present-value identity
`v_t = ∑_{j≥1} ρ^{j−1} E_t(s̃ + g − r)_{t+j}` holds iff the terminal term
`ρ^T E_t v_{t+T}` vanishes. -/
theorem pv_319_iff {ρ : ℝ} {v rn infl g sT : ℕ → Ω → ℝ} (hf : Flow317 ρ v rn infl g sT)
    (hv : 𝔼.Adapted v) (t : ℕ) (ω : Ω)
    (hs : Summable fun j => ρ ^ j * 𝔼.E t (zp rn infl g sT (t + j + 1)) ω) :
    Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 0) ↔
      v t ω = ∑' j, ρ ^ j * 𝔼.E t (zp rn infl g sT (t + j + 1)) ω := by
  have he : ∀ T, ρ ^ T * 𝔼.E t (v (t + T)) ω =
      v t ω - ∑ j ∈ Finset.range T, ρ ^ j * 𝔼.E t (zp rn infl g sT (t + j + 1)) ω := by
    intro T
    have h := congrFun (pv_318_E 𝔼 hf hv t T) ω
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    linarith
  have hlim : Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop
      (𝓝 (v t ω - ∑' j, ρ ^ j * 𝔼.E t (zp rn infl g sT (t + j + 1)) ω)) := by
    simp_rw [he]
    exact tendsto_const_nhds.sub hs.hasSum.tendsto_sum_nat
  constructor
  · intro h0
    have := tendsto_nhds_unique hlim h0
    linarith
  · intro h
    rwa [h, sub_self] at hlim

/-- Cochrane (2023), p. 64 ("The assumption or observation that debt/GDP is a stationary process
is enough"): for bounded `v` and `|ρ| < 1`, `ρ^T E_t v_{t+T} → 0`. -/
theorem terminal_of_bounded {ρ : ℝ} (hρ : |ρ| < 1) {v : ℕ → Ω → ℝ} (hv : BoundedProc v)
    (t : ℕ) (ω : Ω) : Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := hv
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm (a := fun T => |ρ| ^ T * K) (fun T => ?_) ?_
  · rw [sub_zero, norm_norm, Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hK (t + T)) t ω) (pow_nonneg (abs_nonneg ρ) T)
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg ρ) hρ).mul_const K

/-- Cochrane (2023), p. 64 ("If we use `ρ = 1`, then `E_t v_{t+T} → E(v)`, and equation (3.19)
continues to hold describing deviations from this mean"): with `ρ = 1`, if `E_t v_{t+T} → v̄`
and the series converges, `v_t − v̄ = ∑_j E_t(s̃ + g − r)_{t+1+j}`. -/
theorem pv_rho_one {v rn infl g sT : ℕ → Ω → ℝ} (hf : Flow317 1 v rn infl g sT)
    (hv : 𝔼.Adapted v) (t : ℕ) (ω : Ω) {vbar : ℝ}
    (hlim : Tendsto (fun T => 𝔼.E t (v (t + T)) ω) atTop (𝓝 vbar))
    (hs : Summable fun j => 𝔼.E t (zp rn infl g sT (t + j + 1)) ω) :
    v t ω - vbar = ∑' j, 𝔼.E t (zp rn infl g sT (t + j + 1)) ω := by
  have he : ∀ T, ∑ j ∈ Finset.range T, 𝔼.E t (zp rn infl g sT (t + j + 1)) ω =
      v t ω - 𝔼.E t (v (t + T)) ω := by
    intro T
    have h := congrFun (pv_318_E 𝔼 hf hv t T) ω
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, one_pow,
      one_mul] at h
    linarith
  have h1 : Tendsto (fun T => ∑ j ∈ Finset.range T, 𝔼.E t (zp rn infl g sT (t + j + 1)) ω)
      atTop (𝓝 (v t ω - vbar)) := by
    simp_rw [he]
    exact tendsto_const_nhds.sub hlim
  exact tendsto_nhds_unique h1 hs.hasSum.tendsto_sum_nat

variable (ρ : ℝ) (v rn infl g sT : ℕ → Ω → ℝ)

/-- Cochrane (2023), §3.5, pp. 63–65: the linear model with the standing assumptions used for the
innovation identities: (3.17) at every date, adapted processes, `0 < ρ < 1`, and bounded
("stationary", p. 64) debt, returns, inflation, growth and surpluses. -/
structure LinearEconomy where
  flow : Flow317 ρ v rn infl g sT
  v_adapted : 𝔼.Adapted v
  rn_adapted : 𝔼.Adapted rn
  infl_adapted : 𝔼.Adapted infl
  g_adapted : 𝔼.Adapted g
  s_adapted : 𝔼.Adapted sT
  rho_pos : 0 < ρ
  rho_lt_one : ρ < 1
  v_bdd : BoundedProc v
  rn_bdd : BoundedProc rn
  infl_bdd : BoundedProc infl
  g_bdd : BoundedProc g
  s_bdd : BoundedProc sT

variable {𝔼 ρ v rn infl g sT}

/-- Cochrane (2023), (3.18), p. 63: the discounted flow `s̃ + g − r` is bounded when its
components are. -/
theorem zp_bdd (hL : LinearEconomy 𝔼 ρ v rn infl g sT) :
    ∃ K, ∀ n ω, |zp rn infl g sT n ω| ≤ K := by
  obtain ⟨K1, h1⟩ := hL.s_bdd
  obtain ⟨K2, h2⟩ := hL.g_bdd
  obtain ⟨K3, h3⟩ := hL.rn_bdd
  obtain ⟨K4, h4⟩ := hL.infl_bdd
  refine ⟨K1 + K2 + (K3 + K4), fun n ω => ?_⟩
  simp only [zp, Pi.add_apply, Pi.sub_apply]
  refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (h1 n ω)
    (h2 n ω))) ((abs_sub _ _).trans (add_le_add (h3 n ω) (h4 n ω))))

/-- Cochrane (2023), (3.18), p. 63: `s̃ + g − r` is adapted. -/
theorem zp_adapted (hL : LinearEconomy 𝔼 ρ v rn infl g sT) : 𝔼.Adapted (zp rn infl g sT) := by
  intro n
  simp only [zp, Pi.add_apply, Pi.sub_apply, map_add, map_sub, hL.s_adapted n, hL.g_adapted n,
    hL.rn_adapted n, hL.infl_adapted n]

/-- Cochrane (2023), (3.19), p. 64: in the linear economy the infinite present-value identity
`v_t = ∑_{j≥1} ρ^{j−1} E_t(s̃_{t+j} + g_{t+j} − r_{t+j})` holds, as a genuine convergent sum. -/
theorem pv_319 (hL : LinearEconomy 𝔼 ρ v rn infl g sT) (t : ℕ) (ω : Ω) :
    HasSum (fun j => ρ ^ j * 𝔼.E t (zp rn infl g sT (t + j + 1)) ω) (v t ω) := by
  obtain ⟨K, hK⟩ := zp_bdd hL
  have hs : Summable fun j => ρ ^ j * 𝔼.E t (zp rn infl g sT (t + j + 1)) ω := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hL.rho_pos.le hL.rho_lt_one).mul_right K) fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hL.rho_pos]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hK _) t ω) (pow_nonneg hL.rho_pos.le j)
  have hρ : |ρ| < 1 := by rw [abs_of_pos hL.rho_pos]; exact hL.rho_lt_one
  have h := (pv_319_iff 𝔼 hL.flow hL.v_adapted t ω hs).mp
    (terminal_of_bounded 𝔼 hρ hL.v_bdd t ω)
  rw [h]
  exact hs.hasSum

/-- Cochrane (2023), (3.19), p. 64, with `E_t` outside the sum as printed:
`v_t = E_t ∑_{j≥1} ρ^{j−1}(s̃ + g − r)_{t+j}`. -/
theorem pv_319_E_outside (hL : LinearEconomy 𝔼 ρ v rn infl g sT) (t : ℕ) (ω : Ω) :
    v t ω = 𝔼.E t (fun ω' => ∑' j, ρ ^ j * zp rn infl g sT (t + j + 1) ω') ω := by
  obtain ⟨K, hK⟩ := zp_bdd hL
  have hb : ∀ k ω', |(ρ ^ k • zp rn infl g sT (t + k + 1)) ω'| ≤ ρ ^ k * K := by
    intro k ω'
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow, abs_of_pos hL.rho_pos]
    exact mul_le_mul_of_nonneg_left (hK _ ω') (pow_nonneg hL.rho_pos.le k)
  have h := 𝔼.E_tsum hL.rho_pos.le hL.rho_lt_one hb t ω
  simp only [Pi.smul_apply, smul_eq_mul, map_smul] at h
  rw [h]
  exact (pv_319 hL t ω).tsum_eq.symm

/-- Cochrane (2023), p. 64: the asset-pricing identity `p_t = E_t(d_{t+1} + p_{t+1})/E_t R_{t+1}`
for the return `R_{t+1} = (d_{t+1} + p_{t+1})/p_t`, given pull-out of the known `p_t⁻¹`. -/
theorem price_expected_return (hpo : 𝔼.PullOut) {p d : ℕ → Ω → ℝ}
    (hp : 𝔼.Adapted fun n ω => (p n ω)⁻¹) (t : ℕ) (ω : Ω) (hp0 : p t ω ≠ 0)
    (hR : 𝔼.E t (fun ω' => d (t + 1) ω' + p (t + 1) ω') ω ≠ 0) :
    p t ω = 𝔼.E t (fun ω' => d (t + 1) ω' + p (t + 1) ω') ω /
      𝔼.E t (fun ω' => (d (t + 1) ω' + p (t + 1) ω') / p t ω') ω := by
  have hk : 𝔼.E t (fun ω' => (p t ω')⁻¹) = fun ω' => (p t ω')⁻¹ := hp t
  have he : (fun ω' => (d (t + 1) ω' + p (t + 1) ω') / p t ω') =
      (fun ω' => (p t ω')⁻¹) * fun ω' => d (t + 1) ω' + p (t + 1) ω' := by
    funext ω'
    simp only [Pi.mul_apply]
    ring
  rw [he, hpo t _ _ hk, Pi.mul_apply]
  field_simp

/-! ### Innovations and the unexpected-inflation identity (3.20) -/

variable (𝔼) in
/-- Cochrane (2023), p. 64 and Notation p. xxv: the innovation operator
`ΔE_{t+1} = E_{t+1} − E_t`. -/
def innov (t : ℕ) : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) := 𝔼.E (t + 1) - 𝔼.E t

/-- Cochrane (2023), p. 64: `ΔE_{t+1} x = E_{t+1} x − E_t x`. -/
theorem innov_apply (t : ℕ) (x : Ω → ℝ) (ω : Ω) :
    innov 𝔼 t x ω = 𝔼.E (t + 1) x ω - 𝔼.E t x ω := rfl

/-- Cochrane (2023), p. 65 ("Since `v_t` is known at time `t`, it usefully disappears from this
innovation accounting"): a variable known at `t` has no innovation at `t + 1`. -/
theorem innov_known {t : ℕ} {x : Ω → ℝ} (hx : 𝔼.E t x = x) : innov 𝔼 t x = 0 := by
  funext ω
  rw [innov_apply, ← hx, 𝔼.known (Nat.le_succ t), 𝔼.E_E_self, sub_self]
  rfl

/-- Cochrane (2023), p. 65: innovations of a variable bounded by `K` are bounded by `2K`. -/
theorem abs_innov_le {x : Ω → ℝ} {K : ℝ} (hx : ∀ ω, |x ω| ≤ K) (t : ℕ) (ω : Ω) :
    |innov 𝔼 t x ω| ≤ 2 * K := by
  rw [innov_apply, two_mul]
  exact (abs_sub _ _).trans (add_le_add (𝔼.abs_E_le hx _ ω) (𝔼.abs_E_le hx _ ω))

variable (𝔼) in
/-- Cochrane (2023), (3.20)–(3.22), p. 65: weighted sums of innovations of a bounded process
converge for summable weights. -/
theorem summable_innov {w : ℕ → ℝ} (hw : Summable w) {x : ℕ → Ω → ℝ} {K : ℝ}
    (hx : ∀ n ω, |x n ω| ≤ K) (f : ℕ → ℕ) (t : ℕ) (ω : Ω) :
    Summable fun j => w j * innov 𝔼 t (x (f j)) ω := by
  refine Summable.of_norm_bounded ((summable_abs_iff.mpr hw).mul_right (2 * K)) fun j => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_innov_le (hx (f j)) t ω) (abs_nonneg _)

/-- Cochrane (2023), (3.20)–(3.22), p. 65: `∑ a^{j+1}` converges for `|a| < 1`. -/
theorem summable_pow_succ {a : ℝ} (ha : |a| < 1) : Summable fun j : ℕ => a ^ (j + 1) :=
  (summable_nat_add_iff 1).mpr (summable_geometric_of_abs_lt_one ha)

/-- Cochrane (2023), p. 64, "Taking time `t + 1` innovations of (3.19)": the innovations of the
discounted flow sum to zero, `∑_{j≥0} ρ^j ΔE_{t+1}(s̃ + g − r)_{t+1+j} = 0`. -/
theorem innov_pv (hL : LinearEconomy 𝔼 ρ v rn infl g sT) (t : ℕ) (ω : Ω) :
    HasSum (fun j => ρ ^ j * innov 𝔼 t (zp rn infl g sT (t + j + 1)) ω) 0 := by
  have ha := pv_319 hL t ω
  have hb := pv_319 hL (t + 1) ω
  have hz := zp_adapted hL (t + 1)
  have hflow : v t ω - zp rn infl g sT (t + 1) ω = ρ * v (t + 1) ω := by
    simp only [zp, Pi.add_apply, Pi.sub_apply]
    linarith [hL.flow t ω]
  have hb' : HasSum (fun j => ρ ^ j * 𝔼.E (t + 1) (zp rn infl g sT (t + j + 1)) ω) (v t ω) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, add_zero]
    rw [hz, hflow]
    convert hb.mul_left ρ using 1
    funext j
    rw [show t + (j + 1) + 1 = t + 1 + j + 1 by omega, pow_succ]
    ring
  have h := hb'.sub ha
  rw [sub_self] at h
  convert h using 1
  funext j
  rw [innov_apply]
  ring

/-- Cochrane (2023), (3.20), p. 65, the unexpected-inflation identity:
`ΔE_{t+1}π_{t+1} − ΔE_{t+1}r^n_{t+1} = −∑_{j≥0} ρ^j ΔE_{t+1}s̃_{t+1+j}
  − ∑_{j≥0} ρ^j ΔE_{t+1}g_{t+1+j} + ∑_{j≥1} ρ^j ΔE_{t+1}r_{t+1+j}`. -/
theorem innov_identity_3_20 (hL : LinearEconomy 𝔼 ρ v rn infl g sT) (t : ℕ) (ω : Ω) :
    innov 𝔼 t (infl (t + 1)) ω - innov 𝔼 t (rn (t + 1)) ω =
      -(∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω) -
        (∑' j, ρ ^ j * innov 𝔼 t (g (t + j + 1)) ω) +
        ∑' j, ρ ^ (j + 1) * innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω := by
  have h := (innov_pv hL t ω).tsum_eq
  have hgeo : Summable fun j : ℕ => ρ ^ j :=
    summable_geometric_of_lt_one hL.rho_pos.le hL.rho_lt_one
  obtain ⟨K1, h1⟩ := hL.s_bdd
  obtain ⟨K2, h2⟩ := hL.g_bdd
  obtain ⟨K3, h3⟩ := hL.rn_bdd
  obtain ⟨K4, h4⟩ := hL.infl_bdd
  have hr : ∀ n ω, |(rn - infl) n ω| ≤ K3 + K4 := fun n ω =>
    (abs_sub _ _).trans (add_le_add (h3 n ω) (h4 n ω))
  have hs := summable_innov 𝔼 hgeo h1 (fun j => t + j + 1) t ω
  have hg := summable_innov 𝔼 hgeo h2 (fun j => t + j + 1) t ω
  have hR := summable_innov 𝔼 hgeo hr (fun j => t + j + 1) t ω
  have hsplit : ∀ j, ρ ^ j * innov 𝔼 t (zp rn infl g sT (t + j + 1)) ω =
      ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω + ρ ^ j * innov 𝔼 t (g (t + j + 1)) ω -
        ρ ^ j * innov 𝔼 t ((rn - infl) (t + j + 1)) ω := by
    intro j
    simp only [zp, Pi.add_apply, Pi.sub_apply, map_add, map_sub]
    ring
  rw [tsum_congr hsplit, (hs.add hg).tsum_sub hR, hs.tsum_add hg] at h
  have hr0 : ∑' j, ρ ^ j * innov 𝔼 t ((rn - infl) (t + j + 1)) ω =
      (innov 𝔼 t (rn (t + 1)) ω - innov 𝔼 t (infl (t + 1)) ω) +
        ∑' j, ρ ^ (j + 1) * innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω := by
    rw [hR.tsum_eq_zero_add]
    congr 1
    simp only [pow_zero, one_mul, add_zero, Pi.sub_apply, map_sub]
  rw [hr0] at h
  linarith

/-! ### The bond return (A1.3) -/

/-- Cochrane (2023), A1 (1.21), p. 562 ("at the steady state … all portfolios of bonds give the
same return"): at steady-state prices `Q^{(j+1)} = (1+i)^{−(j+1)}`, the portfolio with any
maturity weights `w_j` earns `1 + i`. -/
theorem return_indep_weights {i : ℝ} (w : ℕ → ℝ)
    (hden : ∑' j, w j / (1 + i) ^ (j + 1) ≠ 0) :
    (∑' j, w j / (1 + i) ^ j) / ∑' j, w j / (1 + i) ^ (j + 1) = 1 + i := by
  have hi : 1 + i ≠ 0 := by
    intro h0
    apply hden
    simp [h0]
  have he : ∑' j, w j / (1 + i) ^ j = (1 + i) * ∑' j, w j / (1 + i) ^ (j + 1) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [pow_succ]
    field_simp
  rw [he, mul_div_assoc, div_self hden, mul_one]

/-- Cochrane (2023), A1 (1.23), p. 563: the steady-state price of the geometric portfolio,
`Q = ∑_{j≥1} ω^{j−1}/(1+i)^j = 1/(1 + i − ω)`, for `|ω| < |1 + i|`. -/
theorem geomQ {i ω : ℝ} (h : |ω| < |1 + i|) :
    ∑' j : ℕ, ω ^ j / (1 + i) ^ (j + 1) = 1 / (1 + i - ω) := by
  have := ForwardSolution.tsum_geometric_ratio (A := 1 + i) (B := ω) 1 h
  simpa only [one_mul] using this

/-- Cochrane (2023), A1 p. 563: one-period bonds (`ω = 0`) give `Q = 1/(1+i)`. -/
theorem geomQ_short {i : ℝ} (hi : 0 < 1 + i) :
    ∑' j : ℕ, (0 : ℝ) ^ j / (1 + i) ^ (j + 1) = 1 / (1 + i) := by
  rw [geomQ (by rw [abs_zero]; exact abs_pos.mpr hi.ne'), sub_zero]

/-- Cochrane (2023), A1 p. 563: perpetuities (`ω = 1`) give `Q = 1/i` (for `i > 0`). -/
theorem geomQ_perpetuity {i : ℝ} (hi : 0 < i) :
    ∑' j : ℕ, (1 : ℝ) ^ j / (1 + i) ^ (j + 1) = 1 / i := by
  rw [geomQ (by rw [abs_one, abs_of_pos (by linarith)]; linarith)]
  ring_nf

/-- Cochrane (2023), A1 p. 563 (first display): with geometric weights `ω^j` and the maturing bond
priced at one, the numerator of (1.21) is `1 + ω Q_{t+1}`:
`∑_{k≥0} ω^k x_k = 1 + ω ∑_{m≥0} ω^m x_{m+1}` when `x_0 = 1`. -/
theorem geom_portfolio_return {ω : ℝ} {x : ℕ → ℝ} (hx0 : x 0 = 1)
    (hs : Summable fun k => ω ^ k * x k) :
    ∑' k, ω ^ k * x k = 1 + ω * ∑' m, ω ^ m * x (m + 1) := by
  rw [hs.tsum_eq_zero_add, ← tsum_mul_left, pow_zero, one_mul, hx0]
  congr 1
  refine tsum_congr fun m => ?_
  rw [pow_succ]
  ring

/-- Cochrane (2023), A1 (1.22), p. 563: the log bond return as a function of
`(q_{t+1}, q_t)`, `r^n_{t+1} = log(1 + ω e^{q_{t+1}}) − q_t`. -/
noncomputable def bondReturn (ω : ℝ) (p : ℝ × ℝ) : ℝ := Real.log (1 + ω * Real.exp p.1) - p.2

/-- Cochrane (2023), A1 (1.22), p. 563: the exact derivative of the log bond return at the
steady state `q = log Q`: coefficient `ωQ/(1 + ωQ)` on `q_{t+1}` and `−1` on `q_t`. -/
theorem bondReturn_hasFDerivAt {ω Q : ℝ} (hQ : 0 < Q) (h : 0 < 1 + ω * Q) :
    HasFDerivAt (bondReturn ω) ((ω * Q / (1 + ω * Q)) • ContinuousLinearMap.fst ℝ ℝ ℝ -
      ContinuousLinearMap.snd ℝ ℝ ℝ) (Real.log Q, Real.log Q) := by
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => 1 + ω * Real.exp p.1)
      (ω • (Real.exp (Real.log Q, Real.log Q).1 • ContinuousLinearMap.fst ℝ ℝ ℝ))
      (Real.log Q, Real.log Q) :=
    (hasFDerivAt_fst.exp.const_mul ω).const_add 1
  have hne : (fun p : ℝ × ℝ => 1 + ω * Real.exp p.1) (Real.log Q, Real.log Q) ≠ 0 := by
    simp only [Real.exp_log hQ]
    exact h.ne'
  refine ((h1.log hne).sub hasFDerivAt_snd).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun p => ?_
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, Real.exp_log hQ]
  field_simp

/-- Cochrane (2023), A1 (1.22)–(1.23), p. 563: at `Q = 1/(1 + i − ω)` the constant of the
bond-return linearization is `log((1 + ωQ)/Q) = log(1 + i)` and the coefficient is
`ωQ/(1 + ωQ) = ω/(1 + i)`. -/
theorem bondReturn_steady {i ω : ℝ} (h : 0 < 1 + i - ω) (hi : 0 < 1 + i) :
    bondReturn ω (Real.log (1 / (1 + i - ω)), Real.log (1 / (1 + i - ω))) = Real.log (1 + i) ∧
      ω * (1 / (1 + i - ω)) / (1 + ω * (1 / (1 + i - ω))) = ω / (1 + i) := by
  have hQ : 0 < 1 / (1 + i - ω) := one_div_pos.mpr h
  have hne := h.ne'
  have hine := hi.ne'
  have hnum : 1 + ω * (1 / (1 + i - ω)) = (1 + i) / (1 + i - ω) := by
    field_simp
    ring
  constructor
  · rw [bondReturn, Real.exp_log hQ, hnum, Real.log_div hine hne, Real.log_div one_ne_zero hne,
      Real.log_one]
    ring
  · rw [hnum]
    field_simp

/-- Cochrane (2023), A1 (1.22)–(1.24), p. 563 (survey E15): the exact first-order coefficient
`ω/(1 + i)` equals the approximation `ω` of (1.24) only if `ω = 0` or `i = 0`. -/
theorem omega_hat_eq_iff {i ω : ℝ} (hi : 0 < 1 + i) : ω / (1 + i) = ω ↔ ω = 0 ∨ i = 0 := by
  rw [div_eq_iff hi.ne']
  constructor
  · intro h
    by_contra hc
    push Not at hc
    apply hc.2
    have : ω * i = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hc.1
    · exact h0
  · rintro (h | h) <;> simp [h]

/-- Cochrane (2023), A1 (1.22)/(1.24), p. 563, in deviations from the steady state: the linear
bond-return identity `r^n_{t+1} = ω̂ q_{t+1} − q_t` (`ω̂ = ω/(1+i)` for the exact derivative,
`ω̂ = ω` in (1.24)). -/
def BondRet (ωh : ℝ) (q rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, rn (t + 1) ω = ωh * q (t + 1) ω - q t ω

variable (𝔼) in
/-- Cochrane (2023), A1 (1.24)–(1.25), p. 564: a bounded adapted log bond price with `|ω̂| < 1`. -/
def BondPriceOK (ωh : ℝ) (q : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted q ∧ BoundedProc q ∧ |ωh| < 1

/-- Cochrane (2023), A1 p. 564 (the corrected box formula, survey E16): for a bounded log bond
price and `|ω̂| < 1`, iterating (1.24) forward gives `q_t = −∑_{j≥1} ω̂^{j−1} r^n_{t+j}`. -/
theorem bondPrice_forward {ωh : ℝ} {q rn : ℕ → Ω → ℝ} (hret : BondRet ωh q rn)
    (hq : BoundedProc q) (hω : |ωh| < 1) (t : ℕ) (ω : Ω) :
    HasSum (fun j => ωh ^ j * rn (t + j + 1) ω) (-q t ω) := by
  obtain ⟨K, hK⟩ := hq
  have hrec : ∀ n, q n ω = -rn (n + 1) ω + ωh * q (n + 1) ω := fun n => by
    rw [hret n ω]; ring
  have hs : Summable fun j => (∏ k ∈ Finset.range j, ωh) * -rn (t + j + 1) ω := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_abs_lt_one (by rwa [abs_abs])).mul_right (|ωh| * K + K))
      fun j => ?_
    rw [Finset.prod_const, Finset.card_range, Real.norm_eq_abs, abs_mul, abs_neg, abs_pow,
      hret]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (abs_nonneg _) j)
    refine (abs_sub _ _).trans (add_le_add ?_ (hK _ ω))
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hK _ ω) (abs_nonneg _)
  have hterm : Tendsto (fun T => (∏ k ∈ Finset.range T, ωh) * q (t + T) ω) atTop (𝓝 0) := by
    simp only [Finset.prod_const, Finset.card_range]
    simpa [perfectForesight] using terminal_of_bounded perfectForesight hω
      (v := fun n _ => q n ω) ⟨K, fun n _ => hK n ω⟩ t ()
  have h := (Money.pv_discount_iff (x := fun n => q n ω) (a := fun n => -rn (n + 1) ω)
    (b := fun _ => ωh) hrec t hs).mp hterm
  simp only [Finset.prod_const, Finset.card_range] at h hs
  have h2 : HasSum (fun j => ωh ^ j * rn (t + j + 1) ω) (-(∑' j, ωh ^ j * -rn (t + j + 1) ω)) := by
    have := hs.hasSum.neg
    convert this using 1
    funext j
    ring
  rw [← h] at h2
  exact h2

/-- Cochrane (2023), A1 p. 561 box and p. 564 (survey E16): the printed
`q_t = −∑_{j≥1} ω̂^j r^n_{t+j}` holds (for bounded `q`, `|ω̂| < 1`) only where `q_t = 0`. -/
theorem printed_bondPrice_iff {ωh : ℝ} {q rn : ℕ → Ω → ℝ} (hret : BondRet ωh q rn)
    (hq : BoundedProc q) (hω : |ωh| < 1) (t : ℕ) (ω : Ω) :
    q t ω = -∑' j, ωh ^ (j + 1) * rn (t + j + 1) ω ↔ q t ω = 0 := by
  have h := (bondPrice_forward hret hq hω t ω).tsum_eq
  have he : ∑' j, ωh ^ (j + 1) * rn (t + j + 1) ω = ωh * -q t ω := by
    rw [← h, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    ring
  have h1 : ωh ≠ 1 := by
    intro h1
    rw [h1, abs_one] at hω
    exact lt_irrefl _ hω
  rw [he]
  constructor
  · intro h2
    have : (1 - ωh) * q t ω = 0 := by linarith
    rcases mul_eq_zero.mp this with h3 | h3
    · exact absurd (by linarith) h1
    · exact h3
  · intro h2
    rw [h2]
    ring

/-- Cochrane (2023), A1 p. 561 box and p. 564 (survey E16, counterexample): with `ω̂ = 1/2`,
`q ≡ 1`, `r^n ≡ −1/2` satisfies (1.24) but violates the printed formula. -/
theorem printed_bondPrice_counterexample :
    BondRet (1 / 2) (fun _ (_ : Unit) => (1 : ℝ)) (fun _ _ => -1 / 2) ∧
      (1 : ℝ) ≠ -∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) * (-1 / 2) := by
  have hret : BondRet (1 / 2) (fun _ (_ : Unit) => (1 : ℝ)) (fun _ _ => -1 / 2) := by
    intro t ω
    norm_num
  refine ⟨hret, fun h => ?_⟩
  have := (printed_bondPrice_iff hret ⟨1, fun _ _ => by norm_num⟩
    (by rw [abs_of_pos (by norm_num)]; norm_num) 0 ()).mp h
  norm_num at this

/-- Cochrane (2023), A1 p. 564: under the expectations hypothesis `E_t r^n_{t+1} = i_t`,
equivalently `ω̂ E_t q_{t+1} − q_t = i_t`. -/
theorem EH_bond {ωh : ℝ} {q rn i : ℕ → Ω → ℝ} (hret : BondRet ωh q rn) (hq : 𝔼.Adapted q)
    (t : ℕ) : 𝔼.E t (rn (t + 1)) = i t ↔ ωh • 𝔼.E t (q (t + 1)) - q t = i t := by
  have he : rn (t + 1) = ωh • q (t + 1) - q t := by
    funext ω
    rw [hret t ω]
    rfl
  rw [he, map_sub, map_smul, hq t]

/-- Cochrane (2023), A1 (1.24), p. 563: the bond return `r^n_{t+1} = ω̂q_{t+1} − q_t` is bounded
when `q` is. -/
theorem rn_bound {ωh : ℝ} {q rn : ℕ → Ω → ℝ} (hret : BondRet ωh q rn) {K : ℝ}
    (hK : ∀ n ω, |q n ω| ≤ K) (n : ℕ) (ω : Ω) : |rn (n + 1) ω| ≤ |ωh| * K + K := by
  rw [hret]
  refine (abs_sub _ _).trans (add_le_add ?_ (hK n ω))
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hK _ ω) (abs_nonneg _)

/-- Cochrane (2023), (3.21) and A1 (1.25), p. 564: the bond-return innovation identity
`ΔE_{t+1}r^n_{t+1} = −∑_{j≥1} ω̂^j ΔE_{t+1}r^n_{t+1+j}`. -/
theorem bondReturn_innov {ωh : ℝ} {q rn : ℕ → Ω → ℝ} (hret : BondRet ωh q rn)
    (hok : BondPriceOK 𝔼 ωh q) (t : ℕ) (ω : Ω) :
    innov 𝔼 t (rn (t + 1)) ω = -∑' j, ωh ^ (j + 1) * innov 𝔼 t (rn (t + j + 2)) ω := by
  obtain ⟨hqa, ⟨K, hK⟩, hω⟩ := hok
  have hfwd : q (t + 1) = fun ω' => -∑' j, ωh ^ j * rn (t + j + 2) ω' := by
    funext ω'
    have h := (bondPrice_forward hret ⟨K, hK⟩ hω (t + 1) ω').tsum_eq
    have e : ∑' j, ωh ^ j * rn (t + j + 2) ω' = ∑' j, ωh ^ j * rn (t + 1 + j + 1) ω' :=
      tsum_congr fun j => by rw [show t + 1 + j + 1 = t + j + 2 by omega]
    rw [e, h, neg_neg]
  have hu : Summable fun j : ℕ => |ωh| ^ j * (|ωh| * K + K) :=
    (summable_geometric_of_abs_lt_one (by rwa [abs_abs])).mul_right _
  have hb : ∀ j ω', |(ωh ^ j • rn (t + j + 2)) ω'| ≤ |ωh| ^ j * (|ωh| * K + K) := by
    intro j ω'
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (rn_bound hret hK (t + j + 1) ω') (pow_nonneg
      (abs_nonneg _) j)
  have hE : ∀ s, 𝔼.E s (q (t + 1)) ω = -∑' j, ωh ^ j * 𝔼.E s (rn (t + j + 2)) ω := by
    intro s
    have h := ForwardSolution.E_tsum_dom 𝔼 hu hb s ω
    simp only [Pi.smul_apply, smul_eq_mul, map_smul] at h
    rw [hfwd, show (fun ω' => -∑' j, ωh ^ j * rn (t + j + 2) ω') =
      -(fun ω' => ∑' j, ωh ^ j * rn (t + j + 2) ω') from rfl, map_neg, Pi.neg_apply, h]
  have hsum : ∀ s, Summable fun j => ωh ^ j * 𝔼.E s (rn (t + j + 2)) ω := fun s =>
    Summable.of_norm_bounded hu fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (fun ω' => rn_bound hret hK (t + j + 1) ω')
        s ω) (pow_nonneg (abs_nonneg _) j)
  have hrn : rn (t + 1) = ωh • q (t + 1) - q t := by
    funext ω'
    rw [hret t ω']
    rfl
  have hq0 : innov 𝔼 t (q t) = 0 := innov_known (hqa t)
  have key : ∑' j, ωh ^ (j + 1) * innov 𝔼 t (rn (t + j + 2)) ω =
      ωh * (∑' j, ωh ^ j * 𝔼.E (t + 1) (rn (t + j + 2)) ω -
        ∑' j, ωh ^ j * 𝔼.E t (rn (t + j + 2)) ω) := by
    rw [← (hsum (t + 1)).tsum_sub (hsum t), ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [innov_apply, pow_succ]
    ring
  rw [hrn, map_sub, map_smul, hq0, sub_zero, Pi.smul_apply, smul_eq_mul, innov_apply, hE, hE,
    key]
  ring

/-- Cochrane (2023), (3.21), p. 65, second form: `ΔE_{t+1}r^n_{t+1}
= −∑_{j≥1} ω̂^j ΔE_{t+1}(r_{t+1+j} + π_{t+1+j})` with `r = r^n − π`. -/
theorem bondReturn_innov_real {ωh : ℝ} {q rn infl' : ℕ → Ω → ℝ} (hret : BondRet ωh q rn)
    (hok : BondPriceOK 𝔼 ωh q) (t : ℕ) (ω : Ω) :
    innov 𝔼 t (rn (t + 1)) ω = -∑' j, ωh ^ (j + 1) *
      innov 𝔼 t ((rn (t + j + 2) - infl' (t + j + 2)) + infl' (t + j + 2)) ω := by
  rw [bondReturn_innov hret hok t ω]
  simp only [sub_add_cancel]

/-! ### The weighted inflation identity (3.22) and special cases -/

/-- Cochrane (2023), (3.22), p. 65: eliminating the bond return between (3.20) and (3.21),
`∑_{j≥0} ω̂^j ΔE_{t+1}π_{t+1+j} = −∑ ρ^j ΔE_{t+1}s̃_{t+1+j} − ∑ ρ^j ΔE_{t+1}g_{t+1+j}
  + ∑_{j≥1} (ρ^j − ω̂^j) ΔE_{t+1}r_{t+1+j}`. -/
theorem weighted_inflation_identity (hL : LinearEconomy 𝔼 ρ v rn infl g sT) {ωh : ℝ}
    {q : ℕ → Ω → ℝ} (hret : BondRet ωh q rn) (hok : BondPriceOK 𝔼 ωh q) (t : ℕ) (ω : Ω) :
    ∑' j, ωh ^ j * innov 𝔼 t (infl (t + j + 1)) ω =
      -(∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω) -
        (∑' j, ρ ^ j * innov 𝔼 t (g (t + j + 1)) ω) +
        ∑' j, (ρ ^ (j + 1) - ωh ^ (j + 1)) *
          innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω := by
  have h20 := innov_identity_3_20 hL t ω
  have h21 := bondReturn_innov hret hok t ω
  have hω := hok.2.2
  have hρ : |ρ| < 1 := by rw [abs_of_pos hL.rho_pos]; exact hL.rho_lt_one
  obtain ⟨K3, h3⟩ := hL.rn_bdd
  obtain ⟨K4, h4⟩ := hL.infl_bdd
  have hr : ∀ n ω, |(rn - infl) n ω| ≤ K3 + K4 := fun n ω =>
    (abs_sub _ _).trans (add_le_add (h3 n ω) (h4 n ω))
  have hRρ := summable_innov 𝔼 (summable_pow_succ hρ) hr (fun j => t + j + 2) t ω
  have hRω := summable_innov 𝔼 (summable_pow_succ hω) hr (fun j => t + j + 2) t ω
  have hPiω := summable_innov 𝔼 (summable_pow_succ hω) h4 (fun j => t + j + 2) t ω
  have hPi0 := summable_innov 𝔼 (summable_geometric_of_abs_lt_one hω) h4 (fun j => t + j + 1) t ω
  have hsplit : ∀ j, ωh ^ (j + 1) * innov 𝔼 t (rn (t + j + 2)) ω =
      ωh ^ (j + 1) * innov 𝔼 t ((rn - infl) (t + j + 2)) ω +
        ωh ^ (j + 1) * innov 𝔼 t (infl (t + j + 2)) ω := by
    intro j
    simp only [Pi.sub_apply, map_sub]
    ring
  rw [tsum_congr hsplit, hRω.tsum_add hPiω] at h21
  have hL0 : ∑' j, ωh ^ j * innov 𝔼 t (infl (t + j + 1)) ω =
      innov 𝔼 t (infl (t + 1)) ω + ∑' j, ωh ^ (j + 1) * innov 𝔼 t (infl (t + j + 2)) ω := by
    rw [hPi0.tsum_eq_zero_add]
    simp only [pow_zero, one_mul, add_zero]
    rfl
  have hdiff : ∑' j, (ρ ^ (j + 1) - ωh ^ (j + 1)) *
      innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω =
      ∑' j, ρ ^ (j + 1) * innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω -
        ∑' j, ωh ^ (j + 1) * innov 𝔼 t ((rn - infl) (t + j + 2)) ω := by
    rw [← Summable.tsum_sub
      (f := fun j => ρ ^ (j + 1) * innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω) hRρ hRω]
    refine tsum_congr fun j => ?_
    simp only [Pi.sub_apply]
    ring
  rw [hL0, hdiff]
  change _ = -(∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω) -
      (∑' j, ρ ^ j * innov 𝔼 t (g (t + j + 1)) ω) +
      (∑' j, ρ ^ (j + 1) * innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω -
        ∑' j, ωh ^ (j + 1) * innov 𝔼 t ((rn - infl) (t + j + 2)) ω)
  linarith

/-- Cochrane (2023), p. 65–66 ("With one-period debt `ω = 0`, `r^n_{t+1} = i_t` and is known
ahead of time"): with `ω̂ = 0` the bond return is known at `t` and has no innovation. -/
theorem short_debt_return_known {q rn : ℕ → Ω → ℝ} (hret : BondRet 0 q rn)
    (hq : 𝔼.Adapted q) (t : ℕ) :
    𝔼.E t (rn (t + 1)) = rn (t + 1) ∧ innov 𝔼 t (rn (t + 1)) = 0 := by
  have he : rn (t + 1) = -q t := by
    funext ω
    rw [hret t ω, zero_mul, zero_sub]
    rfl
  have hk : 𝔼.E t (rn (t + 1)) = rn (t + 1) := by rw [he, map_neg, hq t]
  exact ⟨hk, innov_known hk⟩

/-- Cochrane (2023), p. 65–66 and A1 p. 564: with one-period debt and the expectations
hypothesis, `r^n_{t+1} = i_t`. -/
theorem short_debt_EH {q rn i : ℕ → Ω → ℝ} (hret : BondRet 0 q rn) (hq : 𝔼.Adapted q) (t : ℕ)
    (hEH : 𝔼.E t (rn (t + 1)) = i t) : rn (t + 1) = i t := by
  rw [← hEH, (short_debt_return_known hret hq t).1]

/-- Cochrane (2023), p. 66 ("A constant expected return occurs with `E_t r_{t+1} = 0`"): with
constant expected real returns, real returns beyond `t + 1` have no innovation at `t + 1`. -/
theorem innov_r_zero {rn infl : ℕ → Ω → ℝ} (hc : ∀ n, 𝔼.E n (rn (n + 1) - infl (n + 1)) = 0)
    (t j : ℕ) : innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) = 0 := by
  have h1 : 𝔼.E (t + 1) (rn (t + j + 2) - infl (t + j + 2)) = 0 := by
    rw [← 𝔼.tower (show t + 1 ≤ t + j + 1 by omega), hc (t + j + 1), map_zero]
  have h2 : 𝔼.E t (rn (t + j + 2) - infl (t + j + 2)) = 0 := by
    rw [← 𝔼.tower (show t ≤ t + j + 1 by omega), hc (t + j + 1), map_zero]
  simp only [innov, LinearMap.sub_apply, h1, h2, sub_zero]

/-- Cochrane (2023), §3.5.2, p. 66, and (3.27), p. 69: with constant expected returns, one-period
debt (`ω̂ = 0`) and no growth, `ΔE_{t+1}π_{t+1} = −∑_{j≥0} ρ^j ΔE_{t+1}s̃_{t+1+j}`. -/
theorem special_constant_short (hL : LinearEconomy 𝔼 ρ v rn infl g sT) {q : ℕ → Ω → ℝ}
    (hret : BondRet 0 q rn) (hq : 𝔼.Adapted q) (hg : ∀ n ω, g n ω = 0)
    (hc : ∀ n, 𝔼.E n (rn (n + 1) - infl (n + 1)) = 0) (t : ℕ) (ω : Ω) :
    innov 𝔼 t (infl (t + 1)) ω = -∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω := by
  have h := innov_identity_3_20 hL t ω
  have hg0 : ∀ n, g n = 0 := fun n => funext (hg n)
  simp only [hg0, map_zero, Pi.zero_apply, mul_zero, tsum_zero, sub_zero, innov_r_zero hc,
    add_zero, (short_debt_return_known hret hq t).2] at h
  exact h

/-- Cochrane (2023), p. 67: with time-varying expected returns, one-period debt and no growth,
`ΔE_{t+1}π_{t+1} = −∑_{j≥0} ρ^j ΔE_{t+1}s̃_{t+1+j} + ∑_{j≥1} ρ^j ΔE_{t+1}r_{t+1+j}`. -/
theorem special_varying_short (hL : LinearEconomy 𝔼 ρ v rn infl g sT) {q : ℕ → Ω → ℝ}
    (hret : BondRet 0 q rn) (hq : 𝔼.Adapted q) (hg : ∀ n ω, g n ω = 0) (t : ℕ) (ω : Ω) :
    innov 𝔼 t (infl (t + 1)) ω = -(∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω) +
      ∑' j, ρ ^ (j + 1) * innov 𝔼 t (rn (t + j + 2) - infl (t + j + 2)) ω := by
  have h := innov_identity_3_20 hL t ω
  have hg0 : ∀ n, g n = 0 := fun n => funext (hg n)
  simp only [hg0, map_zero, Pi.zero_apply, mul_zero, tsum_zero, sub_zero,
    (short_debt_return_known hret hq t).2] at h
  exact h

/-- Cochrane (2023), (3.23), p. 67: with constant expected returns and no growth,
`∑_{j≥0} ω̂^j ΔE_{t+1}π_{t+1+j} = −∑_{j≥0} ρ^j ΔE_{t+1}s̃_{t+1+j}`. -/
theorem special_constant_long (hL : LinearEconomy 𝔼 ρ v rn infl g sT) {ωh : ℝ}
    {q : ℕ → Ω → ℝ} (hret : BondRet ωh q rn) (hok : BondPriceOK 𝔼 ωh q)
    (hg : ∀ n ω, g n ω = 0) (hc : ∀ n, 𝔼.E n (rn (n + 1) - infl (n + 1)) = 0) (t : ℕ)
    (ω : Ω) :
    ∑' j, ωh ^ j * innov 𝔼 t (infl (t + j + 1)) ω =
      -∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω := by
  have h := weighted_inflation_identity hL hret hok t ω
  have hg0 : ∀ n, g n = 0 := fun n => funext (hg n)
  simp only [hg0, map_zero, Pi.zero_apply, mul_zero, tsum_zero, sub_zero, innov_r_zero hc,
    add_zero] at h
  exact h

/-- Cochrane (2023), (3.24), p. 68: with constant expected returns and no growth,
`ΔE_{t+1}π_{t+1} − ΔE_{t+1}r^n_{t+1} = −∑_{j≥0} ρ^j ΔE_{t+1}s̃_{t+1+j}`. -/
theorem identity_3_24 (hL : LinearEconomy 𝔼 ρ v rn infl g sT) (hg : ∀ n ω, g n ω = 0)
    (hc : ∀ n, 𝔼.E n (rn (n + 1) - infl (n + 1)) = 0) (t : ℕ) (ω : Ω) :
    innov 𝔼 t (infl (t + 1)) ω - innov 𝔼 t (rn (t + 1)) ω =
      -∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω := by
  have h := innov_identity_3_20 hL t ω
  have hg0 : ∀ n, g n = 0 := fun n => funext (hg n)
  simp only [hg0, map_zero, Pi.zero_apply, mul_zero, tsum_zero, sub_zero, innov_r_zero hc,
    add_zero] at h
  exact h

/-- Cochrane (2023), (3.25), p. 68: with constant expected returns,
`ΔE_{t+1}r^n_{t+1} = −∑_{j≥1} ω̂^j ΔE_{t+1}π_{t+1+j}`. -/
theorem identity_3_25 {ωh : ℝ} {q rn infl : ℕ → Ω → ℝ} (hret : BondRet ωh q rn)
    (hok : BondPriceOK 𝔼 ωh q) (hc : ∀ n, 𝔼.E n (rn (n + 1) - infl (n + 1)) = 0) (t : ℕ)
    (ω : Ω) :
    innov 𝔼 t (rn (t + 1)) ω = -∑' j, ωh ^ (j + 1) * innov 𝔼 t (infl (t + j + 2)) ω := by
  rw [bondReturn_innov_real (infl' := infl) hret hok t ω]
  congr 1
  refine tsum_congr fun j => ?_
  rw [map_add, innov_r_zero hc, zero_add]

/-- Cochrane (2023), (3.28), p. 69: a monetary policy change with no change in surpluses
(`ΔE_{t+1}s̃_{t+1+j} = 0`), constant expected returns and no growth gives
`∑_{j≥0} ω̂^j ΔE_{t+1}π_{t+1+j} = 0`, hence `ΔE_{t+1}π_{t+1} = −∑_{j≥1} ω̂^j ΔE_{t+1}π_{t+1+j}`. -/
theorem monetary_disinflation (hL : LinearEconomy 𝔼 ρ v rn infl g sT) {ωh : ℝ}
    {q : ℕ → Ω → ℝ} (hret : BondRet ωh q rn) (hok : BondPriceOK 𝔼 ωh q)
    (hg : ∀ n ω, g n ω = 0) (hc : ∀ n, 𝔼.E n (rn (n + 1) - infl (n + 1)) = 0) (t : ℕ)
    (ω : Ω) (hs : ∀ j, innov 𝔼 t (sT (t + j + 1)) ω = 0) :
    ∑' j, ωh ^ j * innov 𝔼 t (infl (t + j + 1)) ω = 0 ∧
      innov 𝔼 t (infl (t + 1)) ω = -∑' j, ωh ^ (j + 1) * innov 𝔼 t (infl (t + j + 2)) ω := by
  have h := special_constant_long hL hret hok hg hc t ω
  simp only [hs, mul_zero, tsum_zero, neg_zero] at h
  refine ⟨h, ?_⟩
  obtain ⟨K4, h4⟩ := hL.infl_bdd
  have hPi0 := summable_innov 𝔼 (summable_geometric_of_abs_lt_one hok.2.2) h4
    (fun j => t + j + 1) t ω
  rw [hPi0.tsum_eq_zero_add] at h
  simp only [pow_zero, one_mul, add_zero] at h
  change innov 𝔼 t (infl (t + 1)) ω + ∑' j, ωh ^ (j + 1) * innov 𝔼 t (infl (t + j + 2)) ω = 0
    at h
  linarith

/-- Cochrane (2023), §3.5.4, p. 71: with perpetuities, `ρ = ω̂`, the discount-rate terms drop out
of (3.22): `∑ ω̂^j ΔE_{t+1}π_{t+1+j} = −∑ ρ^j ΔE_{t+1}s̃_{t+1+j} − ∑ ρ^j ΔE_{t+1}g_{t+1+j}`. -/
theorem perpetuity_no_discount_terms (hL : LinearEconomy 𝔼 ρ v rn infl g sT)
    {q : ℕ → Ω → ℝ} (hret : BondRet ρ q rn) (hok : BondPriceOK 𝔼 ρ q) (t : ℕ) (ω : Ω) :
    ∑' j, ρ ^ j * innov 𝔼 t (infl (t + j + 1)) ω =
      -(∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω) -
        ∑' j, ρ ^ j * innov 𝔼 t (g (t + j + 1)) ω := by
  have h := weighted_inflation_identity hL hret hok t ω
  simp only [sub_self, zero_mul, tsum_zero, add_zero] at h
  exact h

/-- Cochrane (2023), pp. 70–71 ("the difference between `ρ^j` and `(ρ^j − ω^j)` only affects the
first few terms"): the weights differ by `ω^j ≤ 0.8^j`, below `1%` from `j = 21` on. -/
theorem weights_close {ρ ω : ℝ} (hω0 : 0 ≤ ω) (hω : ω ≤ 0.8) (j : ℕ) :
    |ρ ^ j - (ρ ^ j - ω ^ j)| = ω ^ j ∧ ω ^ j ≤ 0.8 ^ j ∧
      (21 ≤ j → (0.8 : ℝ) ^ j < 0.01) := by
  refine ⟨by rw [sub_sub_cancel, abs_of_nonneg (pow_nonneg hω0 j)],
    pow_le_pow_left₀ hω0 hω j, fun hj => ?_⟩
  calc (0.8 : ℝ) ^ j ≤ 0.8 ^ 21 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
    _ < 0.01 := by norm_num

/-- Cochrane (2023), p. 66 ("When debt is 100% of GDP … it takes four times as much actual
surplus-to-GDP to produce the same effect as when debt is 25% of GDP"): equal scaled surpluses
`ρ sy/(V/Py)` at debt ratios `1` and `1/4` require `sy₁ = 4 sy₂`. -/
theorem scaling_ratio {ρ sy₁ sy₂ : ℝ} (hρ : ρ ≠ 0) (h : ρ * (sy₁ / 1) = ρ * (sy₂ / (1 / 4))) :
    sy₁ = 4 * sy₂ := by
  have := mul_left_cancel₀ hρ h
  rw [div_one] at this
  rw [this]
  ring

/-! ### Sequences of innovations and Figure 3.1 -/

/-- Cochrane (2023), p. 67 ("with `ω = 0.7`, a permanent 1% rise in inflation soaks up the same
surplus as a `1/(1 − 0.7) = 3.3%` price-level jump"): `∑_{j≥0} ω^j = 1/(1 − ω)`, and
`1/(1 − 0.7) = 10/3 ∈ (3.33, 3.34)`. -/
theorem perm_inflation_equiv {ω : ℝ} (h0 : 0 ≤ ω) (h1 : ω < 1) :
    ∑' j : ℕ, ω ^ j = 1 / (1 - ω) ∧ (1 : ℝ) / (1 - 0.7) = 10 / 3 ∧
      (3.33 : ℝ) < 10 / 3 ∧ (10 / 3 : ℝ) < 3.34 := by
  refine ⟨by rw [tsum_geometric_of_lt_one h0 h1, one_div], by norm_num, by norm_num,
    by norm_num⟩

/-- Cochrane (2023), p. 67 ("It is even possible that the fiscal shock comes with no
contemporaneous inflation at all"): for `0 < ω < 1` and any fiscal shock `S`, there is an
inflation-innovation path with `x_0 = 0` and `∑ ω^j x_j = S` (namely
`x_j = S(1 − ω)/ω`, `j ≥ 1`). -/
theorem zero_current_inflation_possible {ω : ℝ} (h0 : 0 < ω) (h1 : ω < 1) (S : ℝ) :
    ∃ x : ℕ → ℝ, x 0 = 0 ∧ HasSum (fun j => ω ^ j * x j) S := by
  set c := S * (1 - ω) / ω
  refine ⟨fun j => if j = 0 then 0 else c, by simp, ?_⟩
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, ↓reduceIte, sub_zero,
    Nat.add_one_ne_zero, ↓reduceIte]
  have hg := (hasSum_geometric_of_lt_one h0.le h1).mul_left (ω * c)
  convert hg using 1
  · funext j
    rw [pow_succ]
    ring
  · have : ω ≠ 0 := h0.ne'
    have : 1 - ω ≠ 0 := by linarith
    simp only [c]
    field_simp

/-- Cochrane (2023), (3.28), p. 69, on a sequence of innovations `x_j = ΔE_{t+1}π_{t+1+j}`:
`∑ ω^j x_j = 0` gives `x_0 = −∑_{j≥1} ω^j x_j`. -/
theorem disinflation_seq {ω : ℝ} {x : ℕ → ℝ} (hs : Summable fun j => ω ^ j * x j)
    (h : ∑' j, ω ^ j * x j = 0) : x 0 = -∑' j, ω ^ (j + 1) * x (j + 1) := by
  rw [hs.tsum_eq_zero_add, pow_zero, one_mul] at h
  linarith

/-- Cochrane (2023), p. 69 and Figure 3.1: an unexpected permanent rise (`x_j = 1` for `j ≥ 1`)
with no surplus change forces the initial jump `x_0 = −ω/(1 − ω)`. -/
theorem fig31_jump {ω : ℝ} (h0 : 0 ≤ ω) (h1 : ω < 1) {x : ℕ → ℝ} (hx : ∀ j, x (j + 1) = 1)
    (hs : Summable fun j => ω ^ j * x j) (h : ∑' j, ω ^ j * x j = 0) :
    x 0 = -(ω / (1 - ω)) := by
  rw [disinflation_seq hs h]
  simp only [hx, mul_one]
  rw [show (fun j : ℕ => ω ^ (j + 1)) = fun j => ω * ω ^ j from funext fun j => pow_succ' ω j,
    tsum_mul_left, tsum_geometric_of_lt_one h0 h1, div_eq_mul_inv]

/-- Cochrane (2023), p. 69 and Figure 3.1: with `ω = 0.8` the initial jump is `−4` (percent), and
it is a genuine solution: the path `x_0 = −4`, `x_j = 1` satisfies `∑ 0.8^j x_j = 0`. -/
theorem fig31_value :
    (0.8 : ℝ) / (1 - 0.8) = 4 ∧
      HasSum (fun j : ℕ => (0.8 : ℝ) ^ j * (if j = 0 then -4 else 1)) 0 := by
  refine ⟨by norm_num, ?_⟩
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, ↓reduceIte,
    Nat.add_one_ne_zero, ↓reduceIte, mul_one]
  have hg := (hasSum_geometric_of_lt_one (r := (0.8 : ℝ)) (by norm_num) (by norm_num)).mul_left
    (0.8 : ℝ)
  convert hg using 1
  · funext j
    rw [pow_succ']
  · norm_num

/-- Cochrane (2023), Figure 3.1, p. 70: the log price level relative to its pre-shock path,
`p_n = ∑_{k<n} x_k`, is `−ω/(1 − ω)` on impact and then rises by one per period. -/
theorem fig31_path {ω : ℝ} {x : ℕ → ℝ} (hx0 : x 0 = -(ω / (1 - ω))) (hx : ∀ j, x (j + 1) = 1)
    (n : ℕ) : ∑ k ∈ Finset.range (n + 1), x k = -(ω / (1 - ω)) + n := by
  induction n with
  | zero => simp [hx0]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, hx n]
    push_cast
    ring

/-- Cochrane (2023), p. 70 ("If the interest-rate rise is completely expected … The long-term bond
case follows exactly the same path as the short-term bond case"): if the news at `t + 1` does not
change expected future inflation (`x_j = 0`, `j ≥ 1`) and surpluses do not change, there is no
price-level jump, whatever `ω`. -/
theorem expected_rise_no_jump {ω : ℝ} {x : ℕ → ℝ} (hx : ∀ j, x (j + 1) = 0)
    (hs : Summable fun j => ω ^ j * x j) (h : ∑' j, ω ^ j * x j = 0) : x 0 = 0 := by
  rw [disinflation_seq hs h]
  simp [hx]

/-- Cochrane (2023), p. 69–70 ("announced `k` periods ahead"): if the news at `t + 1` raises
inflation by one from `k ≥ 1` periods later on (`x_j = 0` for `1 ≤ j < k`, `x_j = 1` for
`j ≥ k`), the jump on announcement is `x_0 = −ω^k/(1 − ω)`. -/
theorem announcement_jump {ω : ℝ} (h0 : 0 ≤ ω) (h1 : ω < 1) {k : ℕ} (hk : 1 ≤ k) {x : ℕ → ℝ}
    (hx : ∀ j, 1 ≤ j → x j = if j < k then 0 else 1)
    (hs : Summable fun j => ω ^ j * x j) (h : ∑' j, ω ^ j * x j = 0) :
    x 0 = -(ω ^ k / (1 - ω)) := by
  have hs' := (summable_nat_add_iff 1).mpr hs
  rw [disinflation_seq hs h]
  congr 1
  have hval : ∀ j, ω ^ (j + 1) * x (j + 1) = if j + 1 < k then 0 else ω ^ (j + 1) := by
    intro j
    rw [hx (j + 1) (by omega)]
    split_ifs <;> ring
  have hsk : Summable fun j => if j + 1 < k then (0 : ℝ) else ω ^ (j + 1) :=
    hs'.congr fun j => hval j
  rw [tsum_congr hval, ← hsk.sum_add_tsum_nat_add (k - 1)]
  rw [Finset.sum_eq_zero fun j hj => by
    rw [Finset.mem_range] at hj
    simp only [show j + 1 < k by omega, ↓reduceIte], zero_add]
  have he : ∀ j, (if j + (k - 1) + 1 < k then (0 : ℝ) else ω ^ (j + (k - 1) + 1)) =
      ω ^ k * ω ^ j := by
    intro j
    simp only [show ¬ (j + (k - 1) + 1 < k) by omega, ↓reduceIte]
    rw [← pow_add]
    congr 1
    omega
  rw [tsum_congr he, tsum_mul_left, tsum_geometric_of_lt_one h0 h1, div_eq_mul_inv]

/-- Cochrane (2023), p. 69 ("The deflationary effect is larger if there is more long-term debt
outstanding, if `ω` is larger"): the jump size `ω/(1 − ω)` is strictly increasing on `[0, 1)`. -/
theorem disinflation_monotone_omega :
    StrictMonoOn (fun ω : ℝ => ω / (1 - ω)) (Set.Ico 0 1) := by
  intro a ha b hb hab
  simp only
  have ha1 : 0 < 1 - a := by linarith [ha.2]
  have hb1 : 0 < 1 - b := by linarith [hb.2]
  rw [div_lt_div_iff₀ ha1 hb1]
  nlinarith

/-- Cochrane (2023), p. 69 ("A credible, persistent interest-rate rise – more terms
`ΔE_{t+1}π_{t+1+j}` – … has a stronger disinflationary effect"): a rise lasting `n` periods gives
the jump `−∑_{j=1}^{n} ω^j`, strictly larger in size for longer rises when `ω > 0`. -/
theorem disinflation_monotone_length {ω : ℝ} (h0 : 0 < ω) :
    StrictMono fun n => ∑ j ∈ Finset.range n, ω ^ (j + 1) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  rw [Finset.sum_range_succ]
  linarith [pow_pos h0 (n + 1)]

/-- Cochrane (2023), A1 p. 560 (survey E15): the exact *log* price drop
`−log(P_0/P) = −log(1133/1173)` lies in `(3.46%, 3.48%)`, which is the text's "3.5%". -/
theorem fig31_log :
    0.0346 < -Real.log (LongTermDebt.jumpRatio 0.02 0.03 0.8) ∧
      -Real.log (LongTermDebt.jumpRatio 0.02 0.03 0.8) < 0.0348 := by
  rw [LongTermDebt.omega_08_example.1]
  have hx0 : (0 : ℝ) < 40 / 1173 := by norm_num
  have hx : |(40 / 1173 : ℝ)| < 1 := by rw [abs_of_pos hx0]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 2
  have e : (1 : ℝ) - 40 / 1173 = 1133 / 1173 := by norm_num
  rw [e, abs_of_pos hx0] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [abs_le] at h
  norm_num at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- Cochrane (2023), §3.5.3 and A1 (1.22) (survey E15): the linearized jump with the printed
weight `ω = 0.8` is `4%` (Figure 3.1), while with the exact first-order weight
`ω̂ = ω/(1+i)` at `i = 3%` it is `ω̂/(1 − ω̂) = ω/(1 + i − ω) = 80/23 ≈ 3.48%`. -/
theorem fig31_linear_exact_coeff :
    (0.8 : ℝ) / (1 - 0.8) = 4 ∧ (0.8 / 1.03 : ℝ) / (1 - 0.8 / 1.03) = 80 / 23 ∧
      (3.47 : ℝ) < 80 / 23 ∧ (80 / 23 : ℝ) < 3.48 := by
  norm_num

end Cochrane.Generality.LogLinearIdentities
