/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import StickyPriceFiscal.CTSimple

/-!
# Sims' model

Cochrane (2023), Chapter 5, §5.7.6 "Sims' model", pp. 179–181, eqs. (5.118)–(5.125), and the
long-run claim of §§5.7.6/5.8 ("This model is Fisherian in the long run", p. 180).

The model is written in continuous time. As in the rest of the continuous-time material, the
responses are perfect-foresight paths after a date-`0` shock: functions `ℝ → ℝ` satisfying the
differential equations (`HasDerivAt`) at every `t > 0` and continuous on `[0, ∞)`; the shocks
`dε`, `dδ` are the initial jumps. The numerical responses of Figs. 5.14–5.15 are out of scope.

## Main results

* `SimsSys`: the system (5.118)–(5.125), with consumption `c = x` in the Phillips curve (5.119)
  (the book writes `κc_t`; with no investment or government purchases in the model, consumption
  equals output — a notational imprecision).
* **Exact linearisations**: the perpetuity price (5.120) — `perpetuity_log_ode` (the exact
  nonlinear law of `q = log(rQ)` under the expectations hypothesis) and
  `perpetuity_linearization` (its exact derivative `r q + i` at the steady state);
  `yield_ode` (Sims' yield `y = 1/Q` obeys `y' = y(y − R)` exactly along a perfect-foresight
  path — the "Ito or jump nonlinearity" arises only with uncertainty); the value of debt
  (5.122) — `debt_value_ode` (`V' = (R − Π)V − S` for long-term debt) , `debt_log_ode` and
  `debt_linearization` (exact derivative `r v + i − π − s̃`); `marginal_utility_log` (5.123).
* **Forward solutions** (`forward_ode_limit`, `forward_ode_unique`): a bounded solution of
  `y' = a y + z`, `a > 0`, is `y_t = −∫_t^∞ e^{−a(s−t)} z_s ds`. Hence the bond price is minus the
  present value of future rates (`bond_price_pv`), inflation is the present value of future
  output (`inflation_pv`), and — since the surplus rule (5.121) has no response to debt — the
  value of debt is the present value of surpluses at the real rate (`debt_pv`).
* (5.121): `surplus_level` — the surplus level moves one-for-one (times `θ_sx`) with output.
* (5.118): `rate_decay_noRule` — without reactions the rate decays as `i_0 e^{−ζt}`.
* **Long-run Fisher relation** ("This model is Fisherian in the long run"):
  `fisherian_long_run` (if `i − π` converges along a path with bounded marginal utility, the
  limit is zero), `fisherian_inflation`, and the steady states: `steady_state_peg` (under a
  constant interest rate `ī`, every steady state has `π = ī`, `x = ρī/κ`, `λ = −σx`, `q = −ī/r`,
  `v = s̄/r`), `steady_state_rule` (with the rule (5.118) the only steady state has zero
  inflation, output and rate when `κ(1 − θ_iπ) ≠ ρθ_ix`).
* (5.124)–(5.125): `habit_roots` — for `σψ > 0` the output block has one positive and one
  negative root.
-/

namespace Cochrane.StickyPriceFiscal.Sims

open Filter Topology

/-! ### The model -/

/-- Cochrane (2023), (5.118)–(5.125), p. 179: the parameters of the modified Sims model. -/
structure SimsParams where
  /-- `ζ_i`, the speed of partial adjustment of the interest rate in (5.118). -/
  zeta : ℝ
  /-- `θ_iπ`, the interest-rate target's reaction to inflation in (5.118). -/
  thIpi : ℝ
  /-- `θ_ix`, the interest-rate target's reaction to output in (5.118). -/
  thIx : ℝ
  /-- `ρ`, the discount rate in the Phillips curve (5.119). -/
  rho : ℝ
  /-- `κ`, the Phillips-curve slope in (5.119). -/
  kappa : ℝ
  /-- `r`, the steady-state real rate in (5.120), (5.122), (5.125). -/
  r : ℝ
  /-- `θ_sx`, the surplus reaction to output growth in (5.121). -/
  thSx : ℝ
  /-- `ψ`, the habit parameter in (5.125) (Sims' `1/ψ`). -/
  psi : ℝ
  /-- `σ`, the intertemporal substitution parameter in (5.125). -/
  sigma : ℝ

/-- Cochrane (2023), (5.118)–(5.125), p. 179: a perfect-foresight path of the modified Sims model
after a date-0 shock: interest rate `i`, inflation `π` (`p`), log bond price `q`, surplus `s̃`
(`s`), value of debt `v`, marginal utility `λ` (`lam`), output `x` and its growth `ẋ` (`xd`)
satisfy, at every `t > 0`: (5.118) `i' = −ζ(i − θ_iπ π − θ_ix x)`, (5.119) `π' = ρπ − κx`,
(5.120) `q' = r q + i`, (5.121) `s̃' = θ_sx ẋ`, (5.122) `v' = r v + i − π − s̃`,
(5.123) `λ' = −(i − π)`, (5.124) `x' = ẋ`, (5.125) `ẋ' = ψλ + σψx + rẋ`. -/
def SimsSys (S : SimsParams) (i p q s v lam x xd : ℝ → ℝ) : Prop :=
  ∀ t, 0 < t →
    HasDerivAt i (-(S.zeta * (i t - S.thIpi * p t - S.thIx * x t))) t ∧
    HasDerivAt p (S.rho * p t - S.kappa * x t) t ∧ HasDerivAt q (S.r * q t + i t) t ∧
    HasDerivAt s (S.thSx * xd t) t ∧ HasDerivAt v (S.r * v t + i t - p t - s t) t ∧
    HasDerivAt lam (-(i t - p t)) t ∧ HasDerivAt x (xd t) t ∧
    HasDerivAt xd (S.psi * lam t + S.sigma * S.psi * x t + S.r * xd t) t

/-! ### Exact linearisations -/

/-- Cochrane (2023), (5.120), p. 179 ("the perpetuity price under the expectations hypothesis"):
if a perpetuity paying one per unit time has price `Q > 0` with instantaneous return
`(1 + Q')/Q = R` (expectations hypothesis, perfect foresight), then `q = log(rQ)` obeys exactly
`q' = R − r e^{−q}`. -/
theorem perpetuity_log_ode {r : ℝ} (hr : 0 < r) {Q R : ℝ → ℝ} {t : ℝ} (hQ : 0 < Q t)
    (hd : HasDerivAt Q (R t * Q t - 1) t) :
    HasDerivAt (fun s => Real.log (r * Q s)) (R t - r * Real.exp (-Real.log (r * Q t))) t := by
  have hrQ : 0 < r * Q t := mul_pos hr hQ
  have h1 := (hd.const_mul r).log hrQ.ne'
  convert h1 using 1
  rw [Real.exp_neg, Real.exp_log hrQ]
  field_simp

/-- Cochrane (2023), (5.120), p. 179: the exact derivative of the perpetuity law
`(q, i) ↦ r + i − r e^{−q}` at the steady state `(0, 0)` is `(q, i) ↦ r q + i`, so the linearised
law is `dq = (r q + i) dt`. -/
theorem perpetuity_linearization (r : ℝ) :
    (fun z : ℝ × ℝ => r + z.2 - r * Real.exp (-z.1)) (0, 0) = 0 ∧
    HasFDerivAt (fun z : ℝ × ℝ => r + z.2 - r * Real.exp (-z.1))
      (r • ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 0) := by
  refine ⟨by simp, ?_⟩
  have h := ((hasFDerivAt_const r ((0 : ℝ), (0 : ℝ))).add hasFDerivAt_snd).sub
    ((hasFDerivAt_fst.neg.exp).const_mul r)
  convert h using 1
  ext <;> simp

/-- Cochrane (2023), p. 180 ("Sims uses the bond yield `y_t = 1/Q_t` … which … requires one to
approximate away an Ito or jump nonlinearity term"): along a perfect-foresight path the yield
obeys `y' = y (y − R)` exactly — the nonlinearity in question arises only with uncertainty. -/
theorem yield_ode {Q R : ℝ → ℝ} {t : ℝ} (hQ : Q t ≠ 0) (hd : HasDerivAt Q (R t * Q t - 1) t) :
    HasDerivAt (fun s => 1 / Q s) (1 / Q t * (1 / Q t - R t)) t := by
  have h := hd.inv hQ
  simp only [one_div]
  convert h using 1
  field_simp
  ring

/-- Cochrane (2023), (5.122), p. 179 ("the fiscal flow condition with long-term debt"): with `B`
perpetuities of price `Q` outstanding (`Q' = RQ − 1`), new issues financing the coupon net of the
real surplus (`Q B' = B − P S`) and inflation `P' = Π P`, the real market value `V = QB/P`
obeys exactly `V' = (R − Π) V − S`. -/
theorem debt_value_ode {Q B P R infl S : ℝ → ℝ} {t : ℝ} (hQ : Q t ≠ 0) (hP : P t ≠ 0)
    (hdQ : HasDerivAt Q (R t * Q t - 1) t) (hdB : HasDerivAt B ((B t - P t * S t) / Q t) t)
    (hdP : HasDerivAt P (infl t * P t) t) :
    HasDerivAt (fun s => Q s * B s / P s) ((R t - infl t) * (Q t * B t / P t) - S t) t := by
  have h := (hdQ.mul hdB).div hdP hP
  convert h using 1
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- Cochrane (2023), (5.122), p. 179: in logs `v = log(V/V̄)` the debt law `V' = (R − Π)V − S` is
exactly `v' = R − Π − (S/V̄) e^{−v}`. -/
theorem debt_log_ode {V R infl S : ℝ → ℝ} {Vbar t : ℝ} (hVbar : 0 < Vbar) (hV : 0 < V t)
    (hd : HasDerivAt V ((R t - infl t) * V t - S t) t) :
    HasDerivAt (fun s => Real.log (V s / Vbar))
      (R t - infl t - S t / Vbar * Real.exp (-Real.log (V t / Vbar))) t := by
  have hq : 0 < V t / Vbar := div_pos hV hVbar
  have h := (hd.div_const Vbar).log hq.ne'
  convert h using 1
  rw [Real.exp_neg, Real.exp_log hq]
  field_simp

/-- Cochrane (2023), (5.122), p. 179: with `R = r + i`, `Π = π` and `S = V̄(r + s̃)` (`s̃` the
surplus scaled by steady-state debt), the exact derivative of
`(v, i, π, s̃) ↦ r + i − π − (r + s̃) e^{−v}` at the steady state is `r v + i − π − s̃`, i.e.
`dv = (r v + i − π − s̃) dt`. -/
theorem debt_linearization (r : ℝ) :
    (fun z : ℝ × ℝ × ℝ × ℝ => r + z.2.1 - z.2.2.1 - (r + z.2.2.2) * Real.exp (-z.1)) 0 = 0 ∧
    HasFDerivAt (fun z : ℝ × ℝ × ℝ × ℝ => r + z.2.1 - z.2.2.1 - (r + z.2.2.2) * Real.exp (-z.1))
      (r • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ × ℝ) +
        (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ)) -
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ)) -
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ))) 0 := by
  refine ⟨by simp, ?_⟩
  have hi := (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ × ℝ))).fst
  have hp := (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ × ℝ))).snd.fst
  have hs := (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ × ℝ))).snd.snd
  have he := (hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ × ℝ))).neg.exp
  have h := (((hasFDerivAt_const r (0 : ℝ × ℝ × ℝ × ℝ)).add hi).sub hp).sub
    (((hasFDerivAt_const r (0 : ℝ × ℝ × ℝ × ℝ)).add hs).mul he)
  convert h using 1
  ext <;> simp

/-- Cochrane (2023), (5.123), p. 179 ("the evolution of the marginal utility of wealth"): if
marginal utility `Λ > 0` obeys the consumer's first-order condition `Λ' = −(R − Π − r) Λ` (`r` the
discount rate, `R` the nominal rate), then `λ = log Λ` obeys exactly `λ' = −((R − r) − Π)`, i.e.
`dλ = −(i − π) dt` with `i = R − r`. -/
theorem marginal_utility_log {Λ R infl : ℝ → ℝ} {r t : ℝ} (hΛ : 0 < Λ t)
    (hd : HasDerivAt Λ (-(R t - infl t - r) * Λ t) t) :
    HasDerivAt (fun s => Real.log (Λ s)) (-((R t - r) - infl t)) t := by
  have h := hd.log hΛ.ne'
  convert h using 1
  field_simp
  ring

/-! ### Forward solutions -/

/-- Cochrane (2023), (5.119)–(5.122), pp. 179–180 (the forward solution of an unstable linear
equation; A1 §1.12's `ode_forward_bounded`): if `y' = a y + z` on `(0, ∞)` with `a > 0`, `y`
continuous and bounded on `[0, ∞)` and `z` continuous there, then for every `t ≥ 0`,
`∫_t^T e^{−a(s−t)} z_s ds → −y_t` as `T → ∞`, i.e. `y_t = −∫_t^∞ e^{−a(s−t)} z_s ds`. -/
theorem forward_ode_limit {a : ℝ} (ha : 0 < a) {y z : ℝ → ℝ} (hyc : ContinuousOn y (Set.Ici 0))
    (hzc : ContinuousOn z (Set.Ici 0)) (hy : ∀ s, 0 < s → HasDerivAt y (a * y s + z s) s)
    (hb : ∃ M, ∀ s, 0 ≤ s → |y s| ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun T => ∫ s in t..T, Real.exp (-(a * (s - t))) * z s) atTop (𝓝 (-y t)) := by
  obtain ⟨M, hM⟩ := hb
  have hftc : ∀ T, t ≤ T → ∫ s in t..T, Real.exp (-(a * (s - t))) * z s =
      Real.exp (-(a * (T - t))) * y T - y t := by
    intro T hT
    have hcont : ContinuousOn (fun s => Real.exp (-(a * (s - t))) * y s) (Set.Icc t T) := by
      refine ContinuousOn.mul (by fun_prop) (hyc.mono fun s hs => ?_)
      exact le_trans ht hs.1
    have hder : ∀ s ∈ Set.Ioo t T, HasDerivAt (fun s => Real.exp (-(a * (s - t))) * y s)
        (Real.exp (-(a * (s - t))) * z s) s := by
      intro s hs
      have hs0 : 0 < s := lt_of_le_of_lt ht hs.1
      have h1 : HasDerivAt (fun s => Real.exp (-(a * (s - t))))
          (Real.exp (-(a * (s - t))) * (-(a * 1))) s := by
        have := ((((hasDerivAt_id s).sub_const t).const_mul a).neg).exp
        simpa using this
      convert h1.mul (hy s hs0) using 1
      ring
    have hint : IntervalIntegrable (fun s => Real.exp (-(a * (s - t))) * z s)
        MeasureTheory.volume t T := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hT]
      refine ContinuousOn.mul (by fun_prop) (hzc.mono fun s hs => ?_)
      exact le_trans ht hs.1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hcont hder hint]
    simp
  have hexp : Tendsto (fun T => Real.exp (-(a * (T - t)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T => a * (T - t)) atTop atTop := by
      refine tendsto_atTop_atTop.mpr fun b => ⟨b / a + t, fun T hT => ?_⟩
      have : b / a ≤ T - t := by linarith
      calc b = a * (b / a) := by field_simp
        _ ≤ a * (T - t) := mul_le_mul_of_nonneg_left this ha.le
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  have hlim : Tendsto (fun T => Real.exp (-(a * (T - t))) * y T - y t) atTop (𝓝 (-y t)) := by
    have h0 : Tendsto (fun T => Real.exp (-(a * (T - t))) * y T) atTop (𝓝 0) := by
      have hg : Tendsto (fun T => Real.exp (-(a * (T - t))) * M) atTop (𝓝 0) := by
        simpa using hexp.mul_const M
      refine squeeze_zero_norm' ?_ hg
      filter_upwards [eventually_ge_atTop t] with T hT
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hM T (le_trans ht hT)) (Real.exp_pos _).le
    simpa using h0.sub_const (y t)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop t] with T hT
  exact (hftc T hT).symm

/-- Cochrane (2023), pp. 179–180: two bounded solutions of `y' = a y + z` (`a > 0`) with the same
forcing coincide on `[0, ∞)` — the forward root pins the jump variable. -/
theorem forward_ode_unique {a : ℝ} (ha : 0 < a) {y₁ y₂ z : ℝ → ℝ}
    (hc₁ : ContinuousOn y₁ (Set.Ici 0)) (hc₂ : ContinuousOn y₂ (Set.Ici 0))
    (hzc : ContinuousOn z (Set.Ici 0)) (h₁ : ∀ s, 0 < s → HasDerivAt y₁ (a * y₁ s + z s) s)
    (h₂ : ∀ s, 0 < s → HasDerivAt y₂ (a * y₂ s + z s) s)
    (hb₁ : ∃ M, ∀ s, 0 ≤ s → |y₁ s| ≤ M) (hb₂ : ∃ M, ∀ s, 0 ≤ s → |y₂ s| ≤ M) {t : ℝ}
    (ht : 0 ≤ t) : y₁ t = y₂ t := by
  have e := tendsto_nhds_unique (forward_ode_limit ha hc₁ hzc h₁ hb₁ ht)
    (forward_ode_limit ha hc₂ hzc h₂ hb₂ ht)
  linarith

/-- Cochrane (2023), (5.120), p. 179: along a bounded path the log bond price is minus the present
value of future interest rates, `q_t = −∫_t^∞ e^{−r(s−t)} i_s ds`. -/
theorem bond_price_pv {r : ℝ} (hr : 0 < r) {q i : ℝ → ℝ} (hqc : ContinuousOn q (Set.Ici 0))
    (hic : ContinuousOn i (Set.Ici 0)) (hq : ∀ s, 0 < s → HasDerivAt q (r * q s + i s) s)
    (hb : ∃ M, ∀ s, 0 ≤ s → |q s| ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun T => ∫ s in t..T, Real.exp (-(r * (s - t))) * i s) atTop (𝓝 (-q t)) :=
  forward_ode_limit hr hqc hic hq hb ht

/-- Cochrane (2023), (5.119), p. 179: along a bounded path inflation is the present value of future
output, `π_t = κ∫_t^∞ e^{−ρ(s−t)} x_s ds`. -/
theorem inflation_pv {ρ κ : ℝ} (hρ : 0 < ρ) {p x : ℝ → ℝ} (hpc : ContinuousOn p (Set.Ici 0))
    (hxc : ContinuousOn x (Set.Ici 0)) (hp : ∀ s, 0 < s → HasDerivAt p (ρ * p s - κ * x s) s)
    (hb : ∃ M, ∀ s, 0 ≤ s → |p s| ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun T => ∫ s in t..T, Real.exp (-(ρ * (s - t))) * (κ * x s)) atTop (𝓝 (p t)) := by
  have h := forward_ode_limit (z := fun s => -(κ * x s)) hρ hpc
    (by fun_prop) (fun s hs => by simpa [sub_eq_add_neg] using hp s hs) hb ht
  have h' := h.neg
  simp only [neg_neg] at h'
  refine h'.congr fun T => ?_
  rw [← intervalIntegral.integral_neg]
  congr 1
  funext s
  ring

/-- Cochrane (2023), (5.121)–(5.122), pp. 179–180 ("Fiscal policy (5.121) … does not contain a
response to debt"): with a surplus that does not respond to debt, the debt equation has the
unstable root `r > 0`, and along a bounded path the value of debt is the present value of
surpluses discounted at the real rate, `v_t = ∫_t^∞ e^{−r(s−t)} (s̃_s − i_s + π_s) ds`. -/
theorem debt_pv {r : ℝ} (hr : 0 < r) {v i p s : ℝ → ℝ} (hvc : ContinuousOn v (Set.Ici 0))
    (hic : ContinuousOn i (Set.Ici 0)) (hpc : ContinuousOn p (Set.Ici 0))
    (hsc : ContinuousOn s (Set.Ici 0))
    (hv : ∀ u, 0 < u → HasDerivAt v (r * v u + i u - p u - s u) u)
    (hb : ∃ M, ∀ u, 0 ≤ u → |v u| ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun T => ∫ u in t..T, Real.exp (-(r * (u - t))) * (s u - i u + p u)) atTop
      (𝓝 (v t)) := by
  have h := forward_ode_limit (z := fun u => i u - p u - s u) hr hvc
    ((hic.sub hpc).sub hsc) (fun u hu => by simpa [add_sub_assoc, add_assoc] using hv u hu) hb ht
  have h' := h.neg
  simp only [neg_neg] at h'
  refine h'.congr fun T => ?_
  rw [← intervalIntegral.integral_neg]
  congr 1
  funext u
  ring

/-! ### The surplus and interest-rate rules -/

/-- Cochrane (2023), (5.121), p. 179 ("Fiscal policy responds to output growth"): along a path
the surplus level moves with output, `s̃_t − s̃_0 = θ_sx (x_t − x_0)`. -/
theorem surplus_level {θ : ℝ} {s x xd : ℝ → ℝ} (hsc : ContinuousOn s (Set.Ici 0))
    (hxc : ContinuousOn x (Set.Ici 0)) (hs : ∀ u, 0 < u → HasDerivAt s (θ * xd u) u)
    (hx : ∀ u, 0 < u → HasDerivAt x (xd u) u) {t : ℝ} (ht : 0 ≤ t) :
    s t - s 0 = θ * (x t - x 0) := by
  rcases ht.eq_or_lt with h | h
  · rw [← h]; ring
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (fun u => s u - θ * x u) (fun _ => 0) h
      ((hsc.mono Set.Icc_subset_Ici_self).sub
        (continuousOn_const.mul (hxc.mono Set.Icc_subset_Ici_self)))
      (fun u hu => by
        have := (hs u hu.1).sub ((hx u hu.1).const_mul θ)
        convert this using 1
        ring)
    have hne : t - 0 ≠ 0 := by linarith
    rw [eq_div_iff hne, zero_mul] at hcd
    linarith

/-- Cochrane (2023), (5.118), p. 179: without reactions (`θ_iπ = θ_ix = 0`) the partial-adjustment
rule makes the interest rate decay geometrically after its jump, `i_t = i_0 e^{−ζt}`. -/
theorem rate_decay_noRule {ζ : ℝ} {i : ℝ → ℝ} (hic : ContinuousOn i (Set.Ici 0))
    (hi : ∀ u, 0 < u → HasDerivAt i (-(ζ * i u)) u) {t : ℝ} (ht : 0 ≤ t) :
    i t = i 0 * Real.exp (-(ζ * t)) := by
  rw [CTSimple.decay_unique hic (fun u hu => (hi u hu).congr_deriv (by ring)) t ht, mul_comm]

/-! ### The long run is Fisherian -/

/-- Cochrane (2023), p. 180 ("This model is Fisherian in the long run"): by (5.123),
`λ' = −(i − π)`; if marginal utility stays bounded and the real rate `i − π` converges, its limit
is zero. -/
theorem fisherian_long_run {i p lam : ℝ → ℝ} (hlc : ContinuousOn lam (Set.Ici 0))
    (hl : ∀ s, 0 < s → HasDerivAt lam (-(i s - p s)) s) (hb : ∃ M, ∀ s, 0 ≤ s → |lam s| ≤ M)
    {L : ℝ} (hL : Tendsto (fun s => i s - p s) atTop (𝓝 L)) : L = 0 := by
  obtain ⟨M, hM⟩ := hb
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · -- `i − π → L < 0`: marginal utility grows without bound
    obtain ⟨S, hS⟩ := eventually_atTop.mp
      ((hL.eventually (gt_mem_nhds (by linarith : L < L / 2))).and (eventually_gt_atTop 0))
    have key : ∀ T, S < T → lam T - lam S ≥ (-(L / 2)) * (T - S) := by
      intro T hT
      have hS0 : 0 < S := (hS S le_rfl).2
      obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope lam (fun s => -(i s - p s)) hT
        (hlc.mono fun u hu => le_trans hS0.le hu.1)
        (fun u hu => hl u (lt_trans hS0 hu.1))
      have hc1 := (hS c hc.1.le).1
      have hpos' : 0 < T - S := by linarith
      rw [eq_div_iff hpos'.ne'] at hcd
      nlinarith
    have hS0 : 0 < S := (hS S le_rfl).2
    obtain ⟨T, hT1, hT2⟩ : ∃ T, S < T ∧ 2 * M + 1 < (-(L / 2)) * (T - S) := by
      refine ⟨S + (2 * M + 2) / (-(L / 2)) + 1, by
        have : 0 ≤ (2 * M + 2) / (-(L / 2)) := by
          apply div_nonneg _ (by linarith)
          have := hM 0 le_rfl
          linarith [abs_nonneg (lam 0)]
        linarith, ?_⟩
      have hl2 : 0 < -(L / 2) := by linarith
      have : (-(L / 2)) * ((2 * M + 2) / (-(L / 2)) + 1) = 2 * M + 2 + (-(L / 2)) := by
        rw [mul_add, mul_div_cancel₀ _ hl2.ne', mul_one]
      nlinarith
    have h1 := key T hT1
    have h2 := hM T (by linarith)
    have h3 := hM S hS0.le
    rw [abs_le] at h2 h3
    linarith
  · obtain ⟨S, hS⟩ := eventually_atTop.mp
      ((hL.eventually (lt_mem_nhds (by linarith : L / 2 < L))).and (eventually_gt_atTop 0))
    have key : ∀ T, S < T → lam T - lam S ≤ (-(L / 2)) * (T - S) := by
      intro T hT
      have hS0 : 0 < S := (hS S le_rfl).2
      obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope lam (fun s => -(i s - p s)) hT
        (hlc.mono fun u hu => le_trans hS0.le hu.1)
        (fun u hu => hl u (lt_trans hS0 hu.1))
      have hc1 := (hS c hc.1.le).1
      have hpos' : 0 < T - S := by linarith
      rw [eq_div_iff hpos'.ne'] at hcd
      nlinarith
    have hS0 : 0 < S := (hS S le_rfl).2
    obtain ⟨T, hT1, hT2⟩ : ∃ T, S < T ∧ 2 * M + 1 < (L / 2) * (T - S) := by
      refine ⟨S + (2 * M + 2) / (L / 2) + 1, by
        have : 0 ≤ (2 * M + 2) / (L / 2) := by
          apply div_nonneg _ (by linarith)
          have := hM 0 le_rfl
          linarith [abs_nonneg (lam 0)]
        linarith, ?_⟩
      have hl2 : 0 < L / 2 := by linarith
      have : (L / 2) * ((2 * M + 2) / (L / 2) + 1) = 2 * M + 2 + L / 2 := by
        rw [mul_add, mul_div_cancel₀ _ hl2.ne', mul_one]
      nlinarith
    have h1 := key T hT1
    have h2 := hM T (by linarith)
    have h3 := hM S hS0.le
    rw [abs_le] at h2 h3
    linarith

/-- Cochrane (2023), p. 180 ("inflation eventually rises" to the interest rate): along a path with
bounded marginal utility, if the interest rate converges to `ī` and inflation converges to `π̄`,
then `π̄ = ī`. -/
theorem fisherian_inflation {i p lam : ℝ → ℝ} (hlc : ContinuousOn lam (Set.Ici 0))
    (hl : ∀ s, 0 < s → HasDerivAt lam (-(i s - p s)) s) (hb : ∃ M, ∀ s, 0 ≤ s → |lam s| ≤ M)
    {ibar pbar : ℝ} (hi : Tendsto i atTop (𝓝 ibar)) (hp : Tendsto p atTop (𝓝 pbar)) :
    pbar = ibar := by
  have := fisherian_long_run hlc hl hb (hi.sub hp)
  linarith

/-- Cochrane (2023), (5.118)–(5.125), p. 179 (steady states): constant paths solve the system iff
the right-hand sides vanish: `ζ(ī − θ_iπ π̄ − θ_ix x̄) = 0`, `ρπ̄ = κx̄`, `r q̄ + ī = 0`,
`θ_sx ẋ̄ = 0`, `r v̄ + ī − π̄ − s̄ = 0`, `ī = π̄`, `ẋ̄ = 0`, `ψλ̄ + σψx̄ + rẋ̄ = 0`. -/
theorem steady_state_iff (S : SimsParams) (i p q s v lam x xd : ℝ) :
    SimsSys S (fun _ => i) (fun _ => p) (fun _ => q) (fun _ => s) (fun _ => v) (fun _ => lam)
      (fun _ => x) (fun _ => xd) ↔
    S.zeta * (i - S.thIpi * p - S.thIx * x) = 0 ∧ S.rho * p - S.kappa * x = 0 ∧
      S.r * q + i = 0 ∧ S.thSx * xd = 0 ∧ S.r * v + i - p - s = 0 ∧ i - p = 0 ∧ xd = 0 ∧
      S.psi * lam + S.sigma * S.psi * x + S.r * xd = 0 := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h 1 one_pos
    have u := fun c d (hd : HasDerivAt (fun _ : ℝ => (c : ℝ)) d 1) =>
      (hasDerivAt_const (1 : ℝ) c).unique hd
    refine ⟨?_, (u _ _ h2).symm, (u _ _ h3).symm, (u _ _ h4).symm, (u _ _ h5).symm, ?_,
      (u _ _ h7).symm, (u _ _ h8).symm⟩
    · have := u _ _ h1
      linarith
    · have := u _ _ h6
      linarith
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ t _
    have c := fun (c : ℝ) => hasDerivAt_const t c
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · convert c i using 1; linarith
    · convert c p using 1
    · convert c q using 1
    · convert c s using 1
    · convert c v using 1
    · convert c lam using 1; linarith
    · convert c x using 1
    · convert c xd using 1

/-- Cochrane (2023), p. 180 ("This model is Fisherian in the long run") under an interest-rate
peg (`ζ_i = 0`, so the rate stays at `ī`): with `κ, r, ψ ≠ 0`, the steady states are exactly
`π̄ = ī`, `x̄ = ρī/κ`, `λ̄ = −σx̄`, `q̄ = −ī/r`, `v̄ = s̄/r`, `ẋ̄ = 0` — inflation equals the
interest rate one for one. -/
theorem steady_state_peg {S : SimsParams} (hζ : S.zeta = 0) (hκ : S.kappa ≠ 0) (hr : S.r ≠ 0)
    (hψ : S.psi ≠ 0) (i p q s v lam x xd : ℝ) :
    SimsSys S (fun _ => i) (fun _ => p) (fun _ => q) (fun _ => s) (fun _ => v) (fun _ => lam)
      (fun _ => x) (fun _ => xd) ↔
    p = i ∧ x = S.rho * i / S.kappa ∧ lam = -(S.sigma * x) ∧ q = -(i / S.r) ∧ v = s / S.r ∧
      xd = 0 := by
  rw [steady_state_iff]
  constructor
  · rintro ⟨-, h2, h3, -, h5, h6, h7, h8⟩
    have hp : p = i := by linarith
    refine ⟨hp, ?_, ?_, ?_, ?_, h7⟩
    · field_simp; rw [hp] at h2; linarith
    · rw [h7, mul_zero, add_zero] at h8
      have : S.psi * (lam + S.sigma * x) = 0 := by linarith
      have := (mul_eq_zero.mp this).resolve_left hψ
      linarith
    · field_simp; linarith
    · field_simp; rw [hp] at h5; linarith
  · rintro ⟨hp, hx, hl, hq, hv, hxd⟩
    subst hp hxd
    refine ⟨by rw [hζ]; ring, ?_, ?_, by ring, ?_, by ring, rfl, ?_⟩
    · rw [hx]; field_simp; ring
    · rw [hq]; field_simp; ring
    · rw [hv]; field_simp; ring
    · rw [hl]; ring

/-- Cochrane (2023), (5.118), p. 179, with the rule in place: if `ζ_i, κ, r, ψ ≠ 0` and
`κ(1 − θ_iπ) ≠ ρθ_ix`, the only steady state has zero interest rate, inflation, output, marginal
utility and bond price (and `v̄ = s̄/r`). -/
theorem steady_state_rule {S : SimsParams} (hζ : S.zeta ≠ 0) (hκ : S.kappa ≠ 0) (hr : S.r ≠ 0)
    (hψ : S.psi ≠ 0) (hdeg : S.kappa * (1 - S.thIpi) ≠ S.rho * S.thIx)
    (i p q s v lam x xd : ℝ)
    (h : SimsSys S (fun _ => i) (fun _ => p) (fun _ => q) (fun _ => s) (fun _ => v)
      (fun _ => lam) (fun _ => x) (fun _ => xd)) :
    i = 0 ∧ p = 0 ∧ x = 0 ∧ lam = 0 ∧ q = 0 ∧ xd = 0 ∧ v = s / S.r := by
  rw [steady_state_iff] at h
  obtain ⟨h1, h2, h3, -, h5, h6, h7, h8⟩ := h
  have hrule : i - S.thIpi * p - S.thIx * x = 0 := (mul_eq_zero.mp h1).resolve_left hζ
  have hpi : p = i := by linarith
  have hx : x = S.rho * p / S.kappa := by field_simp; linarith
  have hp0 : p = 0 := by
    rw [hx, hpi] at hrule
    have : i * (S.kappa * (1 - S.thIpi) - S.rho * S.thIx) = 0 := by
      field_simp at hrule
      linear_combination hrule
    rcases mul_eq_zero.mp this with h | h
    · rw [hpi]; exact h
    · exact absurd (sub_eq_zero.mp h) hdeg
  have hi0 : i = 0 := by rw [← hpi]; exact hp0
  have hx0 : x = 0 := by rw [hx, hp0]; simp
  rw [h7, mul_zero, add_zero, hx0, mul_zero, add_zero] at h8
  have hl0 : lam = 0 := (mul_eq_zero.mp h8).resolve_left hψ
  refine ⟨hi0, hp0, hx0, hl0, ?_, h7, ?_⟩
  · rw [hi0, add_zero] at h3
    exact (mul_eq_zero.mp h3).resolve_left hr
  · field_simp
    rw [hi0, hp0] at h5
    linarith

/-! ### Habit: the output block -/

/-- Cochrane (2023), (5.124)–(5.125), p. 179 (habit): for given marginal utility, output solves
`ẍ = rẋ + σψx + ψλ`, with characteristic roots `μ² − rμ − σψ = 0`. For `σψ > 0` the roots are
real and of opposite sign — one forward-looking (positive) and one stable (negative) root. -/
theorem habit_roots {r σ ψ : ℝ} (h : 0 < σ * ψ) :
    let μp := (r + Real.sqrt (r ^ 2 + 4 * (σ * ψ))) / 2
    let μm := (r - Real.sqrt (r ^ 2 + 4 * (σ * ψ))) / 2
    μp ^ 2 - r * μp - σ * ψ = 0 ∧ μm ^ 2 - r * μm - σ * ψ = 0 ∧ 0 < μp ∧ μm < 0 := by
  intro μp μm
  have hd : 0 ≤ r ^ 2 + 4 * (σ * ψ) := by positivity
  have hs := Real.sq_sqrt hd
  have hgt : |r| < Real.sqrt (r ^ 2 + 4 * (σ * ψ)) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg r) (by linarith)
  have h1 := neg_abs_le r
  have h2 := le_abs_self r
  refine ⟨by simp only [μp]; nlinarith, by simp only [μm]; nlinarith, ?_, ?_⟩
  · simp only [μp]; linarith
  · simp only [μm]; linarith

end Cochrane.StickyPriceFiscal.Sims
