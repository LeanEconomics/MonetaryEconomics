/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DebtDeficitsInflation.LinearizedIdentities
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The linearised identities as exact derivatives

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix §1.2, eqs.
(1.4)–(1.13), pp. 556–559, and §1.3, eqs. (1.21)–(1.25), pp. 561–564; used for (3.17) and
(3.21), pp. 63–65.

The linear model of `LinearizedIdentities` (`Flow`, `BondReturn`) is linked to the nonlinear
identities as an EXACT first derivative at the steady state.

* Flow identity. The exact identity `V_t R^n_{t+1} = P_{t+1}sp_{t+1} + V_{t+1}` (1.6) gives
  the ratio form (1.7) (`flow_ratio`) and its log (1.9) (`log_flow`):
  `v_t + rⁿ_{t+1} − π_{t+1} − g_{t+1} = log(sy_{t+1} + e^{v_{t+1}})`. The right-hand side
  `flowLog (v', sy) = log(sy + e^{v'})` has, at a steady state `(v, sy)` with `e^v + sy > 0`,
  the derivative `ρ dv + (ρ/e^v) dsy` with `ρ = e^v/(e^v + sy) = e^{−(r−g)}`
  (`flowLog_hasFDerivAt`, `rhoLin_eq_exp`, `steady_state_flow`). The constant of (1.11) is
  `flow_constant`, and the first-order identity (1.13) is exactly `Flow` with
  `s̃ = ρ sy/e^v` (`flow_iff_first_order`).
* Bond return. With geometric maturity, the portfolio return is
  `rⁿ_{t+1} = log(1 + ω e^{q_{t+1}}) − q_t` (1.22, `bondLog`). The steady-state price is
  `Q = ∑ ω^{j−1}/(1+i)^j = 1/(1 + i − ω)` (1.23, `bondQ_hasSum`), and the steady-state return is
  `(1 + ωQ)/Q = 1 + i` (`bond_steady_return`). The exact derivative at the steady state is
  `(ω/(1+i)) dq' − dq` (`bondLog_hasFDerivAt`). The first-order identity is exactly
  `BondReturn (ω/(1+i))` (`bondReturn_iff_first_order`).
* Survey E23: (1.24) replaces the exact coefficient `ω/(1+i)` by `ω`
  (`approx_1_24_differs`). Survey E22: iterating the return identity gives
  `q_t = −∑_{j≥1} ω^{j−1} rⁿ_{t+j}` (`bond_price_series`), not `−∑ ωʲ rⁿ_{t+j}`
  (`printed_bond_price_counterexample`).
-/

namespace Cochrane.DebtDeficitsInflation.LinearizationDerivation

open Filter Topology
open Cochrane.DebtDeficitsInflation.LinearizedIdentities

variable {Ω : Type*}

/-! ### The nonlinear flow identity -/

/-- Cochrane (2023), A1 eqs. (1.6)–(1.7), p. 557: the exact flow identity
`V_t R_{t+1} = P_{t+1} sp_{t+1} + V_{t+1}`, in ratios to GDP, is
`(V_t/(P_t y_t)) R_{t+1} (P_t/P_{t+1}) / G_{t+1} = sp_{t+1}/y_{t+1} + V_{t+1}/(P_{t+1}y_{t+1})`,
with `G_{t+1} = y_{t+1}/y_t`. -/
theorem flow_ratio {V R P sp V' P' y y' : ℝ} (hP : P ≠ 0) (hP' : P' ≠ 0) (hy : y ≠ 0)
    (hy' : y' ≠ 0) (h : V * R = P' * sp + V') :
    V / (P * y) * R * (P / P') / (y' / y) = sp / y' + V' / (P' * y') := by
  field_simp
  rw [← h]

/-- Cochrane (2023), A1 eq. (1.9), p. 558: the logarithm of the ratio flow identity (1.7),
`v_t + rⁿ_{t+1} − π_{t+1} − g_{t+1} = log(sy_{t+1} + e^{v_{t+1}})`, with
`v = log(V/(Py))`, `rⁿ = log Rⁿ`, `π = log Π`, `g = log G`. -/
theorem log_flow {a R Pi G sy b : ℝ} (ha : 0 < a) (hR : 0 < R) (hPi : 0 < Pi) (hG : 0 < G)
    (hb : 0 < b) (h : a * R / Pi / G = sy + b) :
    Real.log a + Real.log R - Real.log Pi - Real.log G = Real.log (sy + Real.exp (Real.log b)) := by
  rw [Real.exp_log hb, ← h, Real.log_div (by positivity) hG.ne', Real.log_div (by positivity)
    hPi.ne', Real.log_mul ha.ne' hR.ne']

/-- Cochrane (2023), A1 eq. (1.9), p. 558: the right-hand side of the log flow identity as a
function of `(v_{t+1}, sy_{t+1})`, `log(sy + e^{v'})`. -/
noncomputable def flowLog (p : ℝ × ℝ) : ℝ := Real.log (p.2 + Real.exp p.1)

/-- Cochrane (2023), A1 eq. (1.12), p. 558: the linearisation constant
`ρ = e^v/(e^v + sy)` at the steady state `(v, sy)`. -/
noncomputable def rhoLin (v sy : ℝ) : ℝ := Real.exp v / (Real.exp v + sy)

/-- Cochrane (2023), A1 p. 558: the steady-state `r − g = log((e^v + sy)/e^v)`. -/
noncomputable def ssRate (v sy : ℝ) : ℝ := Real.log ((Real.exp v + sy) / Real.exp v)

/-- Cochrane (2023), A1 p. 558: at a steady state the log flow identity reads
`v + (r − g) = log(sy + e^v)`. -/
theorem steady_state_flow {v sy : ℝ} (h : 0 < Real.exp v + sy) :
    flowLog (v, sy) = v + ssRate v sy := by
  unfold flowLog ssRate
  rw [Real.log_div h.ne' (Real.exp_pos v).ne', Real.log_exp, add_comm sy]
  ring

/-- Cochrane (2023), A1 eq. (1.12), p. 558: `ρ = e^{−(r−g)}`. -/
theorem rhoLin_eq_exp {v sy : ℝ} (h : 0 < Real.exp v + sy) :
    rhoLin v sy = Real.exp (-ssRate v sy) := by
  unfold rhoLin ssRate
  rw [Real.exp_neg, Real.exp_log (div_pos h (Real.exp_pos v)), inv_div]

/-- Cochrane (2023), A1 eq. (1.12), p. 558: `0 < ρ`, and `ρ < 1` exactly when the steady-state
surplus is positive. -/
theorem rhoLin_pos_lt_one_iff {v sy : ℝ} (h : 0 < Real.exp v + sy) :
    0 < rhoLin v sy ∧ (rhoLin v sy < 1 ↔ 0 < sy) := by
  unfold rhoLin
  refine ⟨div_pos (Real.exp_pos v) h, ?_⟩
  rw [div_lt_one h]
  constructor <;> intro <;> linarith

/-- Cochrane (2023), A1 eq. (1.11), p. 558: the derivative of `log(sy + e^{v'})` at the steady
state, `(dv, dsy) ↦ ρ dv + (ρ/e^v) dsy`. -/
noncomputable def flowDeriv (v sy : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  rhoLin v sy • ContinuousLinearMap.fst ℝ ℝ ℝ +
    (rhoLin v sy / Real.exp v) • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- Cochrane (2023), A1 eq. (1.11), p. 558: `Df(dv, dsy) = ρ dv + (ρ/e^v) dsy`. -/
theorem flowDeriv_apply (v sy : ℝ) (p : ℝ × ℝ) :
    flowDeriv v sy p = rhoLin v sy * p.1 + rhoLin v sy / Real.exp v * p.2 := by
  simp [flowDeriv]

/-- Cochrane (2023), A1 eqs. (1.9)–(1.11), p. 558: the linearisation of the flow identity is the
EXACT Fréchet derivative of `log(sy + e^{v'})` at the steady state. -/
theorem flowLog_hasFDerivAt {v sy : ℝ} (h : 0 < Real.exp v + sy) :
    HasFDerivAt flowLog (flowDeriv v sy) (v, sy) := by
  have hin : HasFDerivAt (fun p : ℝ × ℝ => p.2 + Real.exp p.1)
      (ContinuousLinearMap.snd ℝ ℝ ℝ + Real.exp v • ContinuousLinearMap.fst ℝ ℝ ℝ) (v, sy) :=
    hasFDerivAt_snd.add ((Real.hasDerivAt_exp v).comp_hasFDerivAt (f := Prod.fst) (v, sy)
      hasFDerivAt_fst)
  have hne : (fun p : ℝ × ℝ => p.2 + Real.exp p.1) (v, sy) ≠ 0 := by
    simp only; linarith
  refine (hin.log hne).congr_fderiv ?_
  ext <;> simp [flowDeriv, rhoLin] <;> field_simp <;> ring

/-- Cochrane (2023), A1 eq. (1.11), p. 558: the constant of the first-order expansion,
`log(e^v + sy) − ρv − (ρ/e^v)sy = r − g + (1 − ρ)(v − 1)`. -/
theorem flow_constant {v sy : ℝ} (h : 0 < Real.exp v + sy) :
    flowLog (v, sy) - flowDeriv v sy (v, sy) = ssRate v sy + (1 - rhoLin v sy) * (v - 1) := by
  rw [steady_state_flow h]
  have hev := Real.exp_pos v
  rw [flowDeriv_apply]
  simp only [rhoLin]
  field_simp
  ring

/-- Cochrane (2023), A1 eq. (1.13), p. 558, and eq. (3.17), p. 63: in deviations from the steady
state, the first-order flow identity `v_t + r_{t+1} − g_{t+1} = Df(v_{t+1}, sy_{t+1})` is exactly
the linear `Flow` with `ρ = e^v/(e^v + sy)` and `s̃ = ρ sy/e^v`. -/
theorem flow_iff_first_order (v0 sy0 : ℝ) (v r g sy : ℕ → Ω → ℝ) :
    Flow (rhoLin v0 sy0) v r g (fun t => (rhoLin v0 sy0 / Real.exp v0) • sy t) ↔
      ∀ t ω, v t ω + r (t + 1) ω - g (t + 1) ω = flowDeriv v0 sy0 (v (t + 1) ω, sy (t + 1) ω) := by
  simp only [Flow, flowDeriv_apply]
  constructor
  · intro h t ω
    have := congrFun (h t) ω
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul] at this
    linarith
  · intro h t
    funext ω
    have := h t ω
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
    linarith

/-! ### The geometric-maturity bond return -/

/-- Cochrane (2023), A1 eq. (1.23), p. 563: the steady-state portfolio price
`Q = 1/(1 + i − ω)`. -/
noncomputable def bondQ (i om : ℝ) : ℝ := 1 / (1 + i - om)

/-- Cochrane (2023), A1 eq. (1.23), p. 563: `Q = ∑_{j ≥ 1} ω^{j−1}/(1+i)^j = 1/(1 + i − ω)` for
`0 ≤ ω < 1 + i`. -/
theorem bondQ_hasSum {i om : ℝ} (hom : 0 ≤ om) (h : om < 1 + i) :
    HasSum (fun j : ℕ => om ^ j / (1 + i) ^ (j + 1)) (bondQ i om) := by
  have hi : 0 < 1 + i := by linarith
  have hq : |om / (1 + i)| < 1 := by
    rw [abs_of_nonneg (div_nonneg hom hi.le), div_lt_one hi]; exact h
  have := (hasSum_geometric_of_abs_lt_one hq).mul_left (1 / (1 + i))
  convert this using 1
  · funext j
    rw [div_pow, pow_succ]
    field_simp
  · unfold bondQ
    have : 1 + i - om ≠ 0 := by linarith
    field_simp

/-- Cochrane (2023), A1 eq. (1.21) at the steady state, p. 563: `(1 + ωQ)/Q = 1 + i`. -/
theorem bond_steady_return {i om : ℝ} (h : om < 1 + i) :
    (1 + om * bondQ i om) / bondQ i om = 1 + i := by
  unfold bondQ
  have : 1 + i - om ≠ 0 := by linarith
  field_simp
  ring

/-- Cochrane (2023), A1 eq. (1.22), p. 563: the log portfolio return as a function of
`(q_{t+1}, q_t)`, `log(1 + ω e^{q_{t+1}}) − q_t`. -/
noncomputable def bondLog (om : ℝ) (p : ℝ × ℝ) : ℝ := Real.log (1 + om * Real.exp p.1) - p.2

/-- Cochrane (2023), A1 eq. (1.22), p. 563: the derivative at the steady state,
`(dq', dq) ↦ (ω/(1+i)) dq' − dq`. -/
noncomputable def bondDeriv (i om : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  (om / (1 + i)) • ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ

/-- Cochrane (2023), A1 eq. (1.22), p. 563: `Df(dq', dq) = (ω/(1+i)) dq' − dq`. -/
theorem bondDeriv_apply (i om : ℝ) (p : ℝ × ℝ) :
    bondDeriv i om p = om / (1 + i) * p.1 - p.2 := by
  simp [bondDeriv]

/-- Cochrane (2023), A1 eq. (1.22), p. 563: at the steady state the log return is
`log(1 + i)`. -/
theorem bond_steady_log {i om : ℝ} (hom : 0 ≤ om) (h : om < 1 + i) :
    bondLog om (Real.log (bondQ i om), Real.log (bondQ i om)) = Real.log (1 + i) := by
  have hQ : 0 < bondQ i om := by unfold bondQ; exact div_pos one_pos (by linarith)
  unfold bondLog
  rw [Real.exp_log hQ, ← Real.log_div (by positivity) hQ.ne', bond_steady_return h]

/-- Cochrane (2023), A1 eq. (1.22), p. 563: the linearised bond return is the EXACT Fréchet
derivative of `log(1 + ω e^{q'}) − q` at the steady state `q' = q = log Q`; its coefficient is
`ωQ/(1 + ωQ) = ω/(1 + i)`. -/
theorem bondLog_hasFDerivAt {i om : ℝ} (hom : 0 ≤ om) (h : om < 1 + i) :
    HasFDerivAt (bondLog om) (bondDeriv i om)
      (Real.log (bondQ i om), Real.log (bondQ i om)) := by
  set x : ℝ × ℝ := (Real.log (bondQ i om), Real.log (bondQ i om)) with hx
  have hQ : 0 < bondQ i om := by unfold bondQ; exact div_pos one_pos (by linarith)
  have hin : HasFDerivAt (fun p : ℝ × ℝ => 1 + om * Real.exp p.1)
      (om • (Real.exp x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ)) x :=
    (((Real.hasDerivAt_exp x.1).comp_hasFDerivAt x hasFDerivAt_fst).const_mul om).const_add 1
  have hne : (fun p : ℝ × ℝ => 1 + om * Real.exp p.1) x ≠ 0 := by
    simp only; positivity
  have h2 := (hin.log hne).sub (hasFDerivAt_snd (p := x))
  refine h2.congr_fderiv ?_
  have hex : Real.exp x.1 = bondQ i om := by rw [hx]; exact Real.exp_log hQ
  have hi : 1 + i - om ≠ 0 := by linarith
  have hi' : 1 + i ≠ 0 := by linarith
  ext
  · simp [bondDeriv, hex, bondQ]
    field_simp
    linear_combination om * mul_inv_cancel₀ hi'
  · simp [bondDeriv]

/-- Cochrane (2023), A1 eqs. (1.22) and (1.24), p. 563, and eq. (3.21), p. 65: in deviations, the
first-order bond-return identity `rⁿ_{t+1} = Df(q_{t+1}, q_t)` is exactly
`BondReturn (ω/(1+i))`. -/
theorem bondReturn_iff_first_order (i om : ℝ) (q rn : ℕ → Ω → ℝ) :
    BondReturn (om / (1 + i)) q rn ↔
      ∀ t ω, rn (t + 1) ω = bondDeriv i om (q (t + 1) ω, q t ω) := by
  simp only [BondReturn, bondDeriv_apply]
  constructor
  · intro h t ω
    have := congrFun (h t) ω
    simpa using this
  · intro h t
    funext ω
    simpa using h t ω

/-- Cochrane (2023), A1 eq. (1.24), p. 563 (survey E23): the approximation `ω/(1+i) ≈ ω` is not
exact; for `ω ≠ 0` the two coefficients differ whenever `i ≠ 0`. -/
theorem approx_1_24_differs {i om : ℝ} (hom : om ≠ 0) (hi : i ≠ 0) (hi1 : 1 + i ≠ 0) :
    om / (1 + i) ≠ om := by
  intro h
  rw [div_eq_iff hi1] at h
  have : om * i = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · exact hom h1
  · exact hi h1

/-- Cochrane (2023), A1 p. 564, corrected (survey E22): iterating `rⁿ_{t+1} = ω q_{t+1} − q_t`
forward with `ωᵀ q_{t+T} → 0` gives `q_t = −∑_{j ≥ 1} ω^{j−1} rⁿ_{t+j}`. -/
theorem bond_price_series {om : ℝ} {q rn : ℕ → Ω → ℝ} (hb : BondReturn om q rn) {t : ℕ} {ω : Ω}
    (hT : Tendsto (fun T => om ^ T * q (t + T) ω) atTop (𝓝 0)) :
    SeriesTo (fun j => om ^ j * (-rn (t + 1 + j) ω)) (q t ω) := by
  have hrec : Recursion om q (fun t => -rn t) := fun t => by
    funext ω
    have := congrFun (hb t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    linarith
  exact rec_seriesTo_map LinearMap.id hrec hT

/-- Cochrane (2023), A1 p. 564 (survey E22, counterexample): with `ω = 1/2`, constant
`rⁿ = 1` and `q = −2` the return identity holds and `q = −∑ ω^{j−1} rⁿ = −2`, but the printed
`−∑_{j≥1} ωʲ rⁿ_{t+j}` is `−1`. -/
theorem printed_bond_price_counterexample :
    BondReturn (Ω := Unit) (1 / 2) (fun _ _ => -2) (fun _ _ => 1) ∧
      ∑' j : ℕ, (1 / 2 : ℝ) ^ j * 1 = 2 ∧ ∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) * 1 = 1 := by
  refine ⟨fun t => by funext ω; norm_num, ?_, ?_⟩
  · simp only [mul_one]
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  · simp only [mul_one, pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num

end Cochrane.DebtDeficitsInflation.LinearizationDerivation
