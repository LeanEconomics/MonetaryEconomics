/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.ContinuousShort
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Continuous time with long-term debt

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.6 (box pp. 71–72) and
§3.6.2, pp. 74–75; Online Appendix A1.2.1 (continuous-time geometric maturity, pp. 559–561) and
A1.5, pp. 565–566.

Deterministic (perfect-foresight) paths. A geometric maturity structure is a bundle of
government bonds paying the nominal coupon flow `e^{−ω(u−t)}` at date `u ≥ t`; `B(t)` is the
number of bundles outstanding (so the debt density due at date `m` is `B(t)e^{−ω(m−t)}`, which is
the book's `ϖe^{−ϖj}B_t` up to the constant `ϖ`). We prove:

* the bundle price `Q(t) = ∫_t^∞ exp(−∫_t^u i)e^{−ω(u−t)}du` solves `Q' = (i + ω)Q − 1`, is the
  unique solution with its transversality condition, is positive, equals `1/(i + ω)` for a
  constant rate, and in the book's normalisation `ωQ → 1` as `ω → ∞` (instantaneous debt, E20);
* the flow (3.34) for the geometric structure reduces to `Q(B' + ωB) = B − Ps`; the market value
  `QB` then obeys the short-debt flow `(QB)' = i·QB − Ps`, and `V = QB/P` obeys (3.38)–(3.39)
  `V' = (R − π)V − s` with `R = (1 + Q' − ωQ)/Q` the ex-post nominal return, `R = i` under the
  bond-pricing equation; the same for an arbitrary finite portfolio of bonds (3.37);
* the valuation equations (3.35)–(3.36) iff the transversality condition, and the price level;
* A1.5: the integrated form of (1.27) with its limit term, (1.28) **with the transversality
  condition as a hypothesis**, and the counterexample showing that (1.27) does not imply the
  vanishing of the limit (E23); `V/W` is nonincreasing when surpluses are nonnegative; the
  stock-price analogue (1.29)–(1.30); `(ΛW)' = 0` and `ΛV = ∫Λs`; jumps leave `V/W` unchanged,
  with `W⁺/W⁻ = V⁺/V⁻` (the printed `dW/W = dP/P` has the wrong sign for short debt);
* A1.2.1: the steady state, the price jump `P(0)/P(0⁻) = (r + ω)/(i + ω)` (1.17)–(1.18) for an
  unexpected permanent rise of the nominal rate, with an explicit post-jump equilibrium path,
  the perpetuity case `r/i` (1.20), the instantaneous-debt limit (no jump), and forward guidance
  `P(0)/P(0⁻) − 1 = e^{−(r+ω)T}((r + ω)/(i + ω) − 1)` with its comparative statics.
-/

namespace Cochrane.Generality.ContinuousLong

open MeasureTheory Filter Topology Cochrane.Generality.ContinuousShort

/-! ## The geometric bond bundle and its price -/

/-- Cochrane (2023), A1.2.1, p. 559–560, and eq. (3.47): the nominal price at `t` of a bundle
paying the coupon flow `e^{−ω(u−t)}` at `u ≥ t`, discounted at the nominal rate `i`:
`Q(t) = ∫_t^∞ exp(−∫_t^u (i + ω))du`. -/
noncomputable def bondPrice (i : ℝ → ℝ) (ω t : ℝ) : ℝ := pv (fun u => i u + ω) (fun _ => 1) t

/-- Cochrane (2023), A1.2.1: the discounted coupons of the bundle are integrable on `(t, ∞)`. -/
def BondIntegrable (i : ℝ → ℝ) (ω t : ℝ) : Prop := PVIntegrable (fun u => i u + ω) (fun _ => 1) t

/-- Cochrane (2023), A1.2.1: `∫_t^u (i + ω) = ∫_t^u i + ω(u − t)`. -/
theorem cumRate_add_const {i : ℝ → ℝ} {t : ℝ} (hi : ContinuousOn i (Set.Ici t)) (ω : ℝ) {u : ℝ}
    (hu : t ≤ u) : cumRate (fun x => i x + ω) t u = cumRate i t u + ω * (u - t) := by
  rw [cumRate, intervalIntegral.integral_add (intervalIntegrable_of_ici hi le_rfl hu)
    intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul, cumRate]
  ring

/-- Cochrane (2023), A1.2.1, p. 559: the bundle's discount factor is the zero-coupon price
`exp(−∫_t^u i)` times the geometric coupon `e^{−ω(u−t)}`. -/
theorem disc_add_const {i : ℝ → ℝ} {t : ℝ} (hi : ContinuousOn i (Set.Ici t)) (ω : ℝ) {u : ℝ}
    (hu : t ≤ u) :
    disc (fun x => i x + ω) t u = disc i t u * Real.exp (-(ω * (u - t))) := by
  rw [disc, disc, cumRate_add_const hi ω hu, ← Real.exp_add, neg_add]

/-- Cochrane (2023), eq. (3.35) and A1.2.1, p. 559: the nominal market value of one bundle is
`∫_t^∞ Q_t^{(u)} e^{−ω(u−t)}du`, zero-coupon prices `Q_t^{(u)} = exp(−∫_t^u i)` weighted by the
geometric maturity structure. -/
theorem bondPrice_eq {i : ℝ → ℝ} {t : ℝ} (hi : ContinuousOn i (Set.Ici t)) (ω : ℝ) :
    bondPrice i ω t = ∫ u in Set.Ioi t, disc i t u * Real.exp (-(ω * (u - t))) := by
  refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
  rw [mul_one, disc_add_const hi ω (le_of_lt hu)]

/-- Cochrane (2023), A1.2.1: if `i + ω ≥ c > 0` on `[t, ∞)` the bundle price is a convergent
integral (e.g. any nonnegative nominal rate with `ω > 0`). -/
theorem bondIntegrable_of_ge {i : ℝ → ℝ} {ω c t : ℝ} (hi : ContinuousOn i (Set.Ici t))
    (hc : 0 < c) (hge : ∀ u, t ≤ u → c ≤ i u + ω) : BondIntegrable i ω t := by
  have hri : ContinuousOn (fun u => i u + ω) (Set.Ici t) := hi.add continuousOn_const
  have hg : IntegrableOn (fun u => Real.exp (c * t) * Real.exp (-c * u)) (Set.Ioi t) :=
    (integrableOn_exp_mul_Ioi (by linarith) t).const_mul _
  refine Integrable.mono' hg ?_ ?_
  · exact (((continuousOn_disc hri).mul continuousOn_const).mono
      Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have hu' : t ≤ u := le_of_lt hu
    rw [mul_one, Real.norm_eq_abs, abs_of_pos (disc_pos _ _ _), disc, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h := intervalIntegral.integral_mono_on hu' intervalIntegrable_const
      (intervalIntegrable_of_ici hri le_rfl hu') (fun x hx => hge x hx.1)
    have h' : c * (u - t) ≤ cumRate (fun u => i u + ω) t u := by
      rw [intervalIntegral.integral_const, smul_eq_mul] at h
      rw [cumRate]
      linarith
    linarith

/-- Cochrane (2023), eq. (3.47) context and A1.2.1: the bundle price solves the bond-pricing
equation `Q' = (i + ω)Q − 1` on `[t, ∞)` (survey `ct_bond_price_ode`). -/
theorem bondPrice_flow {i : ℝ → ℝ} {ω t : ℝ} (hi : ContinuousOn i (Set.Ici t))
    (hQ : BondIntegrable i ω t) :
    FlowOn (fun u => i u + ω) (fun _ => 1) (bondPrice i ω) t :=
  flowOn_pv (hi.add continuousOn_const) continuousOn_const hQ

/-- Cochrane (2023), A1.2.1: the bundle price satisfies its transversality condition. -/
theorem bondPrice_tvc {i : ℝ → ℝ} {ω t : ℝ} (hi : ContinuousOn i (Set.Ici t))
    (hQ : BondIntegrable i ω t) : TVC (fun u => i u + ω) (bondPrice i ω) t :=
  tvc_pv (hi.add continuousOn_const) continuousOn_const hQ

/-- Cochrane (2023), A1.2.1: the bundle price is the unique solution of `Q' = (i + ω)Q − 1`
satisfying the transversality condition `exp(−∫_t^T (i + ω))Q(T) → 0`. -/
theorem bondPrice_unique {i Q : ℝ → ℝ} {ω t : ℝ} (hi : ContinuousOn i (Set.Ici t))
    (hQ : BondIntegrable i ω t) (hF : FlowOn (fun u => i u + ω) (fun _ => 1) Q t)
    (hT : TVC (fun u => i u + ω) Q t) : Set.EqOn Q (bondPrice i ω) (Set.Ici t) :=
  eqOn_pv_of_tvc (hi.add continuousOn_const) continuousOn_const hF hT hQ

/-- Cochrane (2023), eq. (3.47) and A1 (1.17): with a constant nominal rate `i₀`, `i₀ + ω > 0`,
the bundle price is `Q = 1/(i₀ + ω)`. -/
theorem bondPrice_const {i₀ ω : ℝ} (h : 0 < i₀ + ω) (t : ℝ) :
    bondPrice (fun _ => i₀) ω t = 1 / (i₀ + ω) :=
  pv_const_const h 1 t

/-- Cochrane (2023), A1 (1.17): with a constant nominal rate, `i₀ + ω > 0`, the bundle price is a
convergent integral. -/
theorem bondIntegrable_const {i₀ ω : ℝ} (h : 0 < i₀ + ω) (t : ℝ) :
    BondIntegrable (fun _ => i₀) ω t :=
  pvIntegrable_const h 1 t

/-- Cochrane (2023), A1.2.1: the bundle price is positive. -/
theorem bondPrice_pos {i : ℝ → ℝ} {ω t : ℝ} (hi : ContinuousOn i (Set.Ici t))
    (hQ : BondIntegrable i ω t) : 0 < bondPrice i ω t := by
  have hri : ContinuousOn (fun u => i u + ω) (Set.Ici t) := hi.add continuousOn_const
  have hcont : ContinuousOn (fun u => disc (fun u => i u + ω) t u * 1) (Set.Ici t) :=
    (continuousOn_disc hri).mul continuousOn_const
  have h1 : 0 < ∫ u in t..t + 1, disc (fun u => i u + ω) t u * 1 :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (intervalIntegrable_of_ici hcont le_rfl (by linarith))
      (fun u _ => by rw [mul_one]; exact disc_pos _ _ _) (by linarith)
  have h2 : 0 ≤ ∫ u in Set.Ioi (t + 1), disc (fun u => i u + ω) t u * 1 :=
    setIntegral_nonneg measurableSet_Ioi (fun u _ => by rw [mul_one]; exact (disc_pos _ _ _).le)
  have h3 := intervalIntegral.integral_interval_add_Ioi hQ
    (hQ.mono_set (Set.Ioi_subset_Ioi (by linarith : t ≤ t + 1)))
  rw [bondPrice, pv, ← h3]
  linarith

/-- Cochrane (2023), A1.2.1, p. 560 ("`ϖ = ∞` is instantaneous debt") and E20: in the book's
normalisation (debt density `ϖe^{−ϖj}B`), the value of a bundle per unit of debt due is
`ωQ = ω/(i₀ + ω) → 1` as `ω → ∞`, the value of instantaneous (short-term) debt; the perpetuity
is `ω = 0`, not short-term debt. -/
theorem tendsto_book_bondValue (i₀ : ℝ) :
    Tendsto (fun ω : ℝ => ω * (1 / (i₀ + ω))) atTop (𝓝 1) := by
  have h1 : Tendsto (fun ω : ℝ => i₀ + ω) atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_id
  have h : Tendsto (fun ω : ℝ => 1 - i₀ / (i₀ + ω)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop h1)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (-i₀)] with ω hω
  have hω1 : i₀ + ω ≠ 0 := by linarith
  field_simp
  ring

/-! ## The flow (3.34) with a geometric maturity structure, and (3.37)–(3.39) -/

/-- Cochrane (2023), eq. (3.34) and Notation p. xxvi (E31): with geometric maturity structure the
nominal debt due at date `m` held at `t` has density `B(t)e^{−ω(m−t)}`. -/
noncomputable def debtDensity (B : ℝ → ℝ) (ω t m : ℝ) : ℝ := B t * Real.exp (-(ω * (m - t)))

/-- Cochrane (2023), eq. (3.34): the debt due at `t` itself (`m = t`) is `B(t)`, the coupon flow
the government pays at `t`. -/
theorem debtDensity_self (B : ℝ → ℝ) (ω t : ℝ) : debtDensity B ω t t = B t := by
  simp [debtDensity]

/-- Cochrane (2023), eq. (3.34): net sales `dB_t^{(m)}` of debt due at `m`: the time derivative of
the density is `(B' + ωB)e^{−ω(m−t)}` (geometric roll-over, A1 p. 561). -/
theorem hasDerivAt_debtDensity {B : ℝ → ℝ} {dB ω τ : ℝ} (hB : HasDerivAt B dB τ) (m : ℝ) :
    HasDerivAt (fun x => debtDensity B ω x m) ((dB + ω * B τ) * Real.exp (-(ω * (m - τ)))) τ := by
  have h3 : HasDerivAt (fun x => -(ω * (m - x))) ω τ :=
    ((((hasDerivAt_id τ).const_sub m).const_mul ω).neg).congr_deriv (by ring)
  change HasDerivAt (fun x => B x * Real.exp (-(ω * (m - x)))) _ τ
  convert hB.mul h3.exp using 1
  ring

/-- Cochrane (2023), eq. (3.34), p. 74, geometric case: the value of net debt sales
`∫ Q_t^{(m)} dB_t^{(m)} dm` equals `Q(t)(B'(t) + ωB(t))`, so the flow (3.34)
`B_t^{(t)} = P_t s_t + ∫Q dB` is `Q(B' + ωB) = B − Ps`. -/
theorem flow_LT_geometric {i B P s : ℝ → ℝ} {ω τ dB : ℝ} (hi : ContinuousOn i (Set.Ici τ)) :
    (debtDensity B ω τ τ = P τ * s τ +
        ∫ m in Set.Ioi τ, disc i τ m * ((dB + ω * B τ) * Real.exp (-(ω * (m - τ))))) ↔
      bondPrice i ω τ * (dB + ω * B τ) = B τ - P τ * s τ := by
  have h : ∫ m in Set.Ioi τ, disc i τ m * ((dB + ω * B τ) * Real.exp (-(ω * (m - τ)))) =
      bondPrice i ω τ * (dB + ω * B τ) := by
    rw [bondPrice_eq hi ω, ← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioi (fun m _ => ?_)
    ring
  rw [h, debtDensity_self]
  constructor <;> intro h' <;> linarith

/-- Cochrane (2023), eqs. (3.34) and (3.37)–(3.38): the nominal market value `QB` of a geometric
portfolio obeying the flow `Q(B' + ωB) = B − Ps` grows by the coupon plus capital gain net of
decay, `(QB)' = (1 + Q' − ωQ)B − Ps`, for any differentiable price path `Q`. -/
theorem hasDerivAt_nominal_value {Q B P s : ℝ → ℝ} {ω dQ dB τ : ℝ} (hQ : HasDerivAt Q dQ τ)
    (hB : HasDerivAt B dB τ) (hflow : Q τ * (dB + ω * B τ) = B τ - P τ * s τ) :
    HasDerivAt (fun x => Q x * B x) ((1 + dQ - ω * Q τ) * B τ - P τ * s τ) τ := by
  convert hQ.mul hB using 1
  linear_combination (-1 : ℝ) * hflow

/-- Cochrane (2023), eqs. (3.37)–(3.39), pp. 75: for any differentiable bond-price path, the real
market value `V = QB/P` obeys `V' = (R − π)V − s` with the ex-post nominal portfolio return
`R = (1 + Q' − ωQ)/Q` (coupon yield plus capital gain, `dR^n = (dt + dQ)/Q − ω dt`, (3.47)) and
`π = P'/P`: the value grows at its ex-post real return less surpluses. -/
theorem hasDerivAt_value_LT {Q B P s : ℝ → ℝ} {ω dQ dB dP τ : ℝ} (hQ : HasDerivAt Q dQ τ)
    (hB : HasDerivAt B dB τ) (hP : HasDerivAt P dP τ)
    (hflow : Q τ * (dB + ω * B τ) = B τ - P τ * s τ) (hQ0 : Q τ ≠ 0) (hP0 : P τ ≠ 0) :
    HasDerivAt (fun x => Q x * B x / P x)
      (((1 + dQ - ω * Q τ) / Q τ - dP / P τ) * (Q τ * B τ / P τ) - s τ) τ := by
  convert (hasDerivAt_nominal_value hQ hB hflow).div hP hP0 using 1
  field_simp
  ring

/-- Cochrane (2023), eq. (3.47): under the bond-pricing equation `Q' = (i + ω)Q − 1` the ex-post
nominal return on the geometric bundle is the short rate, `(1 + Q' − ωQ)/Q = i`. -/
theorem nominalReturn_eq {i₀ ω Q₀ dQ : ℝ} (hQ0 : Q₀ ≠ 0) (hdQ : dQ = (i₀ + ω) * Q₀ - 1) :
    (1 + dQ - ω * Q₀) / Q₀ = i₀ := by
  rw [hdQ]
  field_simp
  ring

/-- Cochrane (2023), eq. (3.39) with the bond-pricing equation: the nominal market value obeys
the short-debt flow (3.29), `(QB)' = i·QB − Ps`. -/
theorem hasDerivAt_nominal_value_priced {i Q B P s : ℝ → ℝ} {ω dB τ : ℝ}
    (hQ : HasDerivAt Q ((i τ + ω) * Q τ - 1) τ) (hB : HasDerivAt B dB τ)
    (hflow : Q τ * (dB + ω * B τ) = B τ - P τ * s τ) :
    HasDerivAt (fun x => Q x * B x) (i τ * (Q τ * B τ) - P τ * s τ) τ := by
  convert hasDerivAt_nominal_value hQ hB hflow using 1
  ring

/-- Cochrane (2023), eq. (3.39), p. 75: with nominal debt `B` in geometric bundles priced by
`Q = bondPrice i ω` and obeying the flow (3.34) on `(t, ∞)`, and a positive price level (free to
jump at `t`), the real market value `V = QB/P` solves the flow identity `V' = (i − π)V − s` on
`[t, ∞)` — the same equation as with short-term debt (3.30). -/
theorem flowOn_value_LT {i s B P dP dB : ℝ → ℝ} {ω t : ℝ} (hi : ContinuousOn i (Set.Ici t))
    (hQ : BondIntegrable i ω t) (hBc : ContinuousOn B (Set.Ici t))
    (hPc : ContinuousOn P (Set.Ici t)) (hPpos : ∀ τ, t ≤ τ → 0 < P τ)
    (hP : ∀ τ, t < τ → HasDerivAt P (dP τ) τ) (hB : ∀ τ, t < τ → HasDerivAt B (dB τ) τ)
    (hflow : ∀ τ, t < τ → bondPrice i ω τ * (dB τ + ω * B τ) = B τ - P τ * s τ) :
    FlowOn (fun τ => i τ - dP τ / P τ) s (fun τ => bondPrice i ω τ * B τ / P τ) t := by
  have hF := bondPrice_flow hi hQ
  exact flowOn_of_nominal (B := fun τ => bondPrice i ω τ * B τ) (hF.1.mul hBc) hPc hPpos
    (fun τ hτ => hasDerivAt_nominal_value_priced (hF.2 τ hτ) (hB τ hτ) (hflow τ hτ)) hP

/-- Cochrane (2023), eq. (3.35), p. 75: with long-term debt, along the flow identity (3.39), the
valuation equation `QB/P = ∫_t^∞ D(t,τ)s(τ)dτ` holds iff the transversality condition holds
(the real rate is `i − π`). -/
theorem valuation_LT_iff {i s B P dP dB : ℝ → ℝ} {ω t : ℝ} (hi : ContinuousOn i (Set.Ici t))
    (hr : ContinuousOn (fun τ => i τ - dP τ / P τ) (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hI : PVIntegrable (fun τ => i τ - dP τ / P τ) s t)
    (hQ : BondIntegrable i ω t) (hBc : ContinuousOn B (Set.Ici t))
    (hPc : ContinuousOn P (Set.Ici t)) (hPpos : ∀ τ, t ≤ τ → 0 < P τ)
    (hP : ∀ τ, t < τ → HasDerivAt P (dP τ) τ) (hB : ∀ τ, t < τ → HasDerivAt B (dB τ) τ)
    (hflow : ∀ τ, t < τ → bondPrice i ω τ * (dB τ + ω * B τ) = B τ - P τ * s τ) :
    bondPrice i ω t * B t / P t = pv (fun τ => i τ - dP τ / P τ) s t ↔
      TVC (fun τ => i τ - dP τ / P τ) (fun τ => bondPrice i ω τ * B τ / P τ) t :=
  valuation_iff_tvc hr hs (flowOn_value_LT hi hQ hBc hPc hPpos hP hB hflow) hI

/-- Cochrane (2023), eq. (3.35): price-level determination with long-term debt. With the flow
(3.34), the transversality condition, and nonzero debt and present value,
`P(t) = Q(t)B(t)/∫_t^∞ D(t,τ)s(τ)dτ`: the bond price `Q(t)` enters the price level. -/
theorem price_level_LT {i s B P dP dB : ℝ → ℝ} {ω t : ℝ} (hi : ContinuousOn i (Set.Ici t))
    (hr : ContinuousOn (fun τ => i τ - dP τ / P τ) (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hI : PVIntegrable (fun τ => i τ - dP τ / P τ) s t)
    (hQ : BondIntegrable i ω t) (hBc : ContinuousOn B (Set.Ici t))
    (hPc : ContinuousOn P (Set.Ici t)) (hPpos : ∀ τ, t ≤ τ → 0 < P τ)
    (hP : ∀ τ, t < τ → HasDerivAt P (dP τ) τ) (hB : ∀ τ, t < τ → HasDerivAt B (dB τ) τ)
    (hflow : ∀ τ, t < τ → bondPrice i ω τ * (dB τ + ω * B τ) = B τ - P τ * s τ)
    (hT : TVC (fun τ => i τ - dP τ / P τ) (fun τ => bondPrice i ω τ * B τ / P τ) t)
    (hB0 : B t ≠ 0) (hpv : pv (fun τ => i τ - dP τ / P τ) s t ≠ 0) :
    P t = bondPrice i ω t * B t / pv (fun τ => i τ - dP τ / P τ) s t :=
  (price_level_determined hr hs hI (mul_ne_zero (bondPrice_pos hi hQ).ne' hB0) hpv).1
    ⟨_, flowOn_value_LT hi hQ hBc hPc hPpos hP hB hflow, hT, rfl⟩

/-- Cochrane (2023), eq. (3.36), p. 75: with long-term debt, discounting at the cumulative real
return `W` on the government bond portfolio (`W' = (i − π)W`, `W ≠ 0`),
`V(t)/W(t) = ∫_t^∞ s/W` holds iff `V(T)/W(T) → 0`. -/
theorem valuation_LT_W_iff {i s B P dP dB W : ℝ → ℝ} {ω t : ℝ}
    (hi : ContinuousOn i (Set.Ici t))
    (hr : ContinuousOn (fun τ => i τ - dP τ / P τ) (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hI : PVIntegrable (fun τ => i τ - dP τ / P τ) s t)
    (hQ : BondIntegrable i ω t) (hBc : ContinuousOn B (Set.Ici t))
    (hPc : ContinuousOn P (Set.Ici t)) (hPpos : ∀ τ, t ≤ τ → 0 < P τ)
    (hP : ∀ τ, t < τ → HasDerivAt P (dP τ) τ) (hB : ∀ τ, t < τ → HasDerivAt B (dB τ) τ)
    (hflow : ∀ τ, t < τ → bondPrice i ω τ * (dB τ + ω * B τ) = B τ - P τ * s τ)
    (hWc : ContinuousOn W (Set.Ici t))
    (hW : ∀ τ, t < τ → HasDerivAt W ((i τ - dP τ / P τ) * W τ) τ)
    (hW0 : ∀ τ, t ≤ τ → W τ ≠ 0) :
    bondPrice i ω t * B t / P t / W t = ∫ τ in Set.Ioi t, s τ / W τ ↔
      Tendsto (fun T => bondPrice i ω T * B T / P T / W T) atTop (𝓝 0) :=
  valuation_W_iff hr hs (flowOn_value_LT hi hQ hBc hPc hPpos hP hB hflow) hI hWc hW hW0

/-- Cochrane (2023), eqs. (3.37)–(3.38), p. 75, an arbitrary finite portfolio: bonds `k ∈ S` with
prices `Q_k`, quantities `B_k` and nominal coupon flows `c_k`, financed by the flow
`Σ c_k B_k = Ps + Σ Q_k B_k'`. Then the real market value `V = Σ Q_k B_k/P` obeys
`V' = Σ(Q_k' + c_k)B_k/P − πV − s` (value grows by coupons and capital gains less surpluses). -/
theorem hasDerivAt_value_portfolio {ι : Type*} (S : Finset ι) {Q B c : ι → ℝ → ℝ}
    {dQ dB : ι → ℝ} {P s : ℝ → ℝ} {dP τ : ℝ} (hQ : ∀ k ∈ S, HasDerivAt (Q k) (dQ k) τ)
    (hB : ∀ k ∈ S, HasDerivAt (B k) (dB k) τ) (hP : HasDerivAt P dP τ) (hP0 : P τ ≠ 0)
    (hflow : ∑ k ∈ S, c k τ * B k τ = P τ * s τ + ∑ k ∈ S, Q k τ * dB k) :
    HasDerivAt (fun x => (∑ k ∈ S, Q k x * B k x) / P x)
      ((∑ k ∈ S, (dQ k + c k τ) * B k τ) / P τ -
        dP / P τ * ((∑ k ∈ S, Q k τ * B k τ) / P τ) - s τ) τ := by
  have hsum : HasDerivAt (fun x => ∑ k ∈ S, Q k x * B k x)
      (∑ k ∈ S, (dQ k * B k τ + Q k τ * dB k)) τ := by
    have := HasDerivAt.fun_sum (u := S) (fun k hk => (hQ k hk).mul (hB k hk))
    exact this
  have hval : ∑ k ∈ S, (dQ k * B k τ + Q k τ * dB k) =
      ∑ k ∈ S, (dQ k + c k τ) * B k τ - P τ * s τ := by
    simp only [add_mul, Finset.sum_add_distrib]
    linarith
  convert hsum.div hP hP0 using 1
  rw [hval]
  field_simp
  ring

/-- Cochrane (2023), eq. (3.37), p. 75: the portfolio's coupon-plus-capital-gain flow is the
value-weighted sum of the individual bond returns `(Q_k' + c_k)/Q_k` with weights
`Q_k B_k`. -/
theorem portfolio_return_weights {ι : Type*} (S : Finset ι) {Q B c : ι → ℝ → ℝ} {dQ : ι → ℝ}
    {τ : ℝ} (hQ0 : ∀ k ∈ S, Q k τ ≠ 0) :
    ∑ k ∈ S, (dQ k + c k τ) * B k τ =
      ∑ k ∈ S, (dQ k + c k τ) / Q k τ * (Q k τ * B k τ) := by
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have := hQ0 k hk
  field_simp

/-- Cochrane (2023), eq. (3.39), p. 75, finite portfolio priced under perfect foresight: if every
bond satisfies `Q_k' = iQ_k − c_k`, the portfolio's ex-post nominal return is `i` and
`V' = (i − π)V − s`. -/
theorem hasDerivAt_value_portfolio_priced {ι : Type*} (S : Finset ι) {Q B c : ι → ℝ → ℝ}
    {dB : ι → ℝ} {i P s : ℝ → ℝ} {dP τ : ℝ}
    (hQ : ∀ k ∈ S, HasDerivAt (Q k) (i τ * Q k τ - c k τ) τ)
    (hB : ∀ k ∈ S, HasDerivAt (B k) (dB k) τ) (hP : HasDerivAt P dP τ) (hP0 : P τ ≠ 0)
    (hflow : ∑ k ∈ S, c k τ * B k τ = P τ * s τ + ∑ k ∈ S, Q k τ * dB k) :
    HasDerivAt (fun x => (∑ k ∈ S, Q k x * B k x) / P x)
      ((i τ - dP / P τ) * ((∑ k ∈ S, Q k τ * B k τ) / P τ) - s τ) τ := by
  convert hasDerivAt_value_portfolio S hQ hB hP hP0 hflow using 1
  have : ∑ k ∈ S, (i τ * Q k τ - c k τ + c k τ) * B k τ = i τ * ∑ k ∈ S, Q k τ * B k τ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [this]
  field_simp

/-! ## A1.5: the ex-post return as discount factor -/

/-- Cochrane (2023), A1.5, (1.27)–(1.28), p. 566 (the "Integrating" line, with its limit term):
if `d(V/W) = −(s/W)dt` on `(t, ∞)` (`V/W` continuous on `[t, ∞)`) and `s/W` is integrable, then
`V(T)/W(T) → V(t)/W(t) − ∫_t^∞ s/W`. -/
theorem A15_integrated {s V W : ℝ → ℝ} {t : ℝ}
    (hG : ContinuousOn (fun x => V x / W x) (Set.Ici t))
    (hdG : ∀ τ, t < τ → HasDerivAt (fun x => V x / W x) (-(s τ / W τ)) τ)
    (hsW : ContinuousOn (fun x => s x / W x) (Set.Ici t))
    (hI : IntegrableOn (fun x => s x / W x) (Set.Ioi t)) :
    Tendsto (fun T => V T / W T) atTop (𝓝 (V t / W t - ∫ τ in Set.Ioi t, s τ / W τ)) := by
  have h := (intervalIntegral_tendsto_integral_Ioi t hI tendsto_id).const_sub (V t / W t)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop t] with T hT
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
    (hG.mono Set.Icc_subset_Ici_self) (fun x hx => hdG x hx.1)
    (intervalIntegrable_of_ici hsW.neg le_rfl hT)
  rw [intervalIntegral.integral_neg] at hF
  simp only [id]
  linarith

/-- Cochrane (2023), A1.5, eq. (1.28), p. 566, corrected (E23): along `d(V/W) = −(s/W)dt`,
`V(t)/W(t) = ∫_t^∞ s/W` holds **iff** the transversality condition `V(T)/W(T) → 0` holds; the
limit is an assumption, not a consequence of (1.27). -/
theorem A15_valuation_iff {s V W : ℝ → ℝ} {t : ℝ}
    (hG : ContinuousOn (fun x => V x / W x) (Set.Ici t))
    (hdG : ∀ τ, t < τ → HasDerivAt (fun x => V x / W x) (-(s τ / W τ)) τ)
    (hsW : ContinuousOn (fun x => s x / W x) (Set.Ici t))
    (hI : IntegrableOn (fun x => s x / W x) (Set.Ioi t)) :
    V t / W t = ∫ τ in Set.Ioi t, s τ / W τ ↔ Tendsto (fun T => V T / W T) atTop (𝓝 0) := by
  have h := A15_integrated hG hdG hsW hI
  constructor
  · intro he
    rw [he, sub_self] at h
    exact h
  · intro h0
    have := tendsto_nhds_unique h h0
    linarith

/-- Cochrane (2023), A1.5, p. 566, E23: "From (1.27), V grows more slowly than W, so the limit is
zero" is false. Counterexample: `r = 1`, `s ≡ 0`, `W = V = e^τ`. Then `V' = rV − s` (1.27),
`W' = rW`, `d(V/W) = 0 = −s/W`, `s/W` is integrable, yet `V(T)/W(T) → 1 ≠ 0` and
`V(0)/W(0) = 1 ≠ 0 = ∫_0^∞ s/W`. -/
theorem A15_counterexample :
    ∃ r s V W : ℝ → ℝ, FlowOn r s V 0 ∧ (∀ τ, HasDerivAt W (r τ * W τ) τ) ∧ (∀ τ, 0 < W τ) ∧
      (∀ τ, HasDerivAt (fun x => V x / W x) (-(s τ / W τ)) τ) ∧
      IntegrableOn (fun x => s x / W x) (Set.Ioi 0) ∧
      V 0 / W 0 ≠ ∫ τ in Set.Ioi (0 : ℝ), s τ / W τ ∧
      Tendsto (fun T => V T / W T) atTop (𝓝 1) := by
  refine ⟨fun _ => 1, fun _ => 0, Real.exp, Real.exp, ⟨Real.continuous_exp.continuousOn,
    fun τ _ => ?_⟩, fun τ => ?_, Real.exp_pos, fun τ => ?_, ?_, ?_, ?_⟩
  · convert Real.hasDerivAt_exp τ using 1
    ring
  · convert Real.hasDerivAt_exp τ using 1
    ring
  · have hev : (fun x => Real.exp x / Real.exp x) =ᶠ[𝓝 τ] fun _ => (1 : ℝ) :=
      Eventually.of_forall fun x => div_self (Real.exp_pos x).ne'
    convert (hasDerivAt_const τ (1 : ℝ)).congr_of_eventuallyEq hev using 1
    simp
  · simp only [zero_div]
    exact integrableOn_zero
  · simp
  · refine tendsto_const_nhds.congr (fun T => ?_)
    rw [div_self (Real.exp_pos T).ne']

/-- Cochrane (2023), A1.5, p. 566, E23 in general: for any real rate and surplus stream, every
bubble path `pv + κ·exp(∫_t^· r)` with `κ ≠ 0` solves the flow identity (1.27)/(3.39) but violates
both the transversality condition and the valuation equation (1.28). -/
theorem bubble_not_valuation {r s : ℝ → ℝ} {t : ℝ} (hr : ContinuousOn r (Set.Ici t))
    (hs : ContinuousOn s (Set.Ici t)) (hI : PVIntegrable r s t) {κ : ℝ} (hκ : κ ≠ 0) :
    FlowOn r s (fun τ => pv r s τ + κ * Real.exp (cumRate r t τ)) t ∧
      ¬ TVC r (fun τ => pv r s τ + κ * Real.exp (cumRate r t τ)) t ∧
      pv r s t + κ * Real.exp (cumRate r t t) ≠ pv r s t := by
  refine ⟨flowOn_bubble hr hs hI κ, fun h => hκ ((tvc_bubble_iff hr hs hI κ).1 h), ?_⟩
  rw [cumRate_self, Real.exp_zero, mul_one]
  intro h
  exact hκ (by linarith)

/-- Cochrane (2023), A1.5, p. 566, the correct content of "V grows more slowly than W": with
nonnegative surpluses and positive `W`, `d(V/W) = −(s/W)dt ≤ 0`, so `V/W` is nonincreasing on
`[t, ∞)` (it need not tend to zero, see `A15_counterexample`). -/
theorem V_over_W_antitone {s V W : ℝ → ℝ} {t : ℝ}
    (hG : ContinuousOn (fun x => V x / W x) (Set.Ici t))
    (hdG : ∀ τ, t < τ → HasDerivAt (fun x => V x / W x) (-(s τ / W τ)) τ)
    (hs : ∀ τ, t < τ → 0 ≤ s τ) (hW : ∀ τ, t < τ → 0 < W τ) :
    AntitoneOn (fun x => V x / W x) (Set.Ici t) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici t) hG (fun x hx => ?_) (fun x hx => ?_)
  · rw [interior_Ici] at hx
    exact (hdG x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ici] at hx
    rw [(hdG x hx).deriv]
    have := div_nonneg (hs x hx) (hW x hx).le
    linarith

/-- Cochrane (2023), A1.5, eq. (1.29), p. 566: the ex-post return on a stock with price `p` and
dividend `d`, `dW/W = (d/p)dt + dp/p`, is the statement `p' = Rp − d` with `R = d/p + p'/p`. -/
theorem stock_return_iff {R₀ d₀ p₀ dp : ℝ} (hp : p₀ ≠ 0) :
    dp = R₀ * p₀ - d₀ ↔ R₀ = d₀ / p₀ + dp / p₀ := by
  constructor
  · intro h
    rw [h]
    field_simp
    ring
  · intro h
    rw [h]
    field_simp
    ring

/-- Cochrane (2023), A1.5, eq. (1.30), p. 566: a stock price `p` with dividends `d`, growing at
its ex-post return `R` (`p' = Rp − d`), discounted by the cumulative return `W' = RW`:
`p(t)/W(t) = ∫_t^∞ d/W` holds iff `p(T)/W(T) → 0`. -/
theorem stock_price_valuation {R d p W : ℝ → ℝ} {t : ℝ} (hR : ContinuousOn R (Set.Ici t))
    (hd : ContinuousOn d (Set.Ici t)) (hp : FlowOn R d p t) (hI : PVIntegrable R d t)
    (hWc : ContinuousOn W (Set.Ici t)) (hW : ∀ τ, t < τ → HasDerivAt W (R τ * W τ) τ)
    (hW0 : ∀ τ, t ≤ τ → W τ ≠ 0) :
    p t / W t = ∫ τ in Set.Ioi t, d τ / W τ ↔ Tendsto (fun T => p T / W T) atTop (𝓝 0) :=
  valuation_W_iff hR hd hp hI hWc hW hW0

/-- Cochrane (2023), A1.5, p. 566: the basic pricing relation `E_t[d(Λ_tW_t)] = 0`
(deterministic): with `Λ' = −rΛ` and `W' = rW`, `ΛW` is constant on `[t, ∞)`. -/
theorem Lambda_W_const {r Λ W : ℝ → ℝ} {t : ℝ} (hΛc : ContinuousOn Λ (Set.Ici t))
    (hWc : ContinuousOn W (Set.Ici t)) (hΛ : ∀ τ, t < τ → HasDerivAt Λ (-(r τ) * Λ τ) τ)
    (hW : ∀ τ, t < τ → HasDerivAt W (r τ * W τ) τ) {τ : ℝ} (hτ : t ≤ τ) :
    Λ τ * W τ = Λ t * W t := by
  refine eq_of_hasDerivAt_zero (hΛc.mul hWc) (fun x hx => ?_) hτ
  convert (hΛ x hx).mul (hW x hx) using 1
  ring

/-- Cochrane (2023), A1.5, p. 566 (last lines): with `Λ' = −rΛ`, the flow identity gives
`d(ΛV) = −Λs` and, with the transversality condition `Λ(T)V(T) → 0`,
`Λ(t)V(t) = ∫_t^∞ Λ(τ)s(τ)dτ`. -/
theorem Lambda_valuation {r s V Λ : ℝ → ℝ} {t : ℝ} (hr : ContinuousOn r (Set.Ici t))
    (hs : ContinuousOn s (Set.Ici t)) (hV : FlowOn r s V t) (hI : PVIntegrable r s t)
    (hΛc : ContinuousOn Λ (Set.Ici t)) (hΛ : ∀ τ, t < τ → HasDerivAt Λ (-(r τ) * Λ τ) τ)
    (hΛ0 : Λ t ≠ 0) (hT : Tendsto (fun T => Λ T * V T) atTop (𝓝 0)) :
    (∀ τ, t < τ → HasDerivAt (fun x => Λ x * V x) (-(Λ τ * s τ)) τ) ∧
      Λ t * V t = ∫ τ in Set.Ioi t, Λ τ * s τ := by
  refine ⟨fun τ hτ => (flow_iff_Lambda (hΛ τ hτ) ?_).1 (hV.2 τ hτ), ?_⟩
  · rw [discountFactor_eq hr hΛc hΛ hτ.le]
    exact mul_ne_zero hΛ0 (disc_pos r t τ).ne'
  · rw [(valuation_Lambda_iff hr hs hV hI hΛc hΛ hΛ0).2 hT, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun τ _ => ?_)
    field_simp

/-- Cochrane (2023), A1.5, p. 566 ("At the jump points d(V_t/W_t) = 0"): with nominal debt `B`
predetermined across a jump of the bond price `Q⁻ → Q⁺` and of the price level `P⁻ → P⁺`, the
cumulative return jumps by the real bond return `(Q⁺/P⁺)/(Q⁻/P⁻)`; then `V/W` does not jump, and
`W⁺/W⁻ = V⁺/V⁻` (the jump of `W` equals that of `V`). -/
theorem jump_V_over_W {Qm Qp Pm Pp B Wm : ℝ} (hQm : Qm ≠ 0) (hQp : Qp ≠ 0) (hPm : Pm ≠ 0)
    (hPp : Pp ≠ 0) (hWm : Wm ≠ 0) (hB : B ≠ 0) :
    Qp * B / Pp / (Wm * (Qp / Pp / (Qm / Pm))) = Qm * B / Pm / Wm ∧
      Wm * (Qp / Pp / (Qm / Pm)) / Wm = Qp * B / Pp / (Qm * B / Pm) := by
  constructor <;> field_simp

/-- Cochrane (2023), A1.5, p. 566, imprecision: the printed jump relation `dW/W = dP/P` has the
wrong sign. With short-term debt (`Q = 1`) the return jumps by `W⁺/W⁻ = P⁻/P⁺`, so for any
genuine jump `P⁺ ≠ P⁻` the proportional jumps of `W` and of `P` have opposite signs. -/
theorem jump_short_return_sign {Pm Pp : ℝ} (hPm : 0 < Pm) (hPp : 0 < Pp) (hne : Pm ≠ Pp) :
    (Pm / Pp - 1) * (Pp / Pm - 1) < 0 := by
  have h : (Pm / Pp - 1) * (Pp / Pm - 1) = -((Pm - Pp) ^ 2 / (Pm * Pp)) := by
    field_simp
    ring
  rw [h, neg_neg_iff_pos]
  have hsub : Pm - Pp ≠ 0 := sub_ne_zero.2 hne
  exact div_pos (by positivity) (mul_pos hPm hPp)

/-! ## A1.2.1 (continuous time): steady state and price-level jumps -/

/-- Cochrane (2023), A1.2.1, pp. 559–561: the steady state with a constant real rate `r > 0`, zero
inflation (`i = r`), constant surplus `s₀` and price level `P̄ ≠ 0`. With `Q̄ = 1/(r + ω)` (which
solves `Q' = (r + ω)Q − 1` with `Q' = 0`), a constant debt level `B̄` obeys the flow
`Q̄(0 + ωB̄) = B̄ − P̄s₀` iff `B̄ = s₀(r + ω)P̄/r`; it then satisfies the valuation
`Q̄B̄/P̄ = s₀/r = ∫_t^∞ e^{−r(τ−t)}s₀dτ`, and the government sells `ωB̄` new bundles per unit time
(the roll-over of A1 p. 561). -/
theorem steady_state_LT {r ω s₀ Pbar Bbar : ℝ} (hr : 0 < r) (hrω : 0 < r + ω) (hP : Pbar ≠ 0)
    (t : ℝ) :
    (0 = (r + ω) * (1 / (r + ω)) - 1) ∧
      (1 / (r + ω) * (0 + ω * Bbar) = Bbar - Pbar * s₀ ↔ Bbar = s₀ * (r + ω) * Pbar / r) ∧
      (Bbar = s₀ * (r + ω) * Pbar / r →
        bondPrice (fun _ => r) ω t * Bbar / Pbar = pv (fun _ => r) (fun _ => s₀) t) := by
  refine ⟨by field_simp; ring, ⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
  · field_simp at h
    field_simp
    linarith
  · rw [h]
    field_simp
    ring
  · rw [bondPrice_const hrω, pv_const_const hr, h]
    field_simp

/-- Cochrane (2023), A1.2.1, eqs. (1.17)–(1.18): the price-level jump from the valuation
equation. If nominal debt `B ≠ 0` is predetermined and the real value of surpluses `v ≠ 0` is the
same before and after the news, `Q⁻B/P⁻ = v = Q₀B/P₀`, then `P₀/P⁻ = Q₀/Q⁻`. -/
theorem price_jump_of_valuation {Qm Q0 B Pm P0 v : ℝ} (hv : v ≠ 0) (hB : B ≠ 0) (hQm : Qm ≠ 0)
    (hPm : Pm ≠ 0) (hpre : Qm * B / Pm = v) (hpost : Q0 * B / P0 = v) : P0 / Pm = Q0 / Qm := by
  have hP0 : P0 ≠ 0 := by
    rintro rfl
    rw [div_zero] at hpost
    exact hv hpost.symm
  rw [← hpost] at hpre
  field_simp at hpre ⊢
  linear_combination hpre

/-- Cochrane (2023), A1.2.1, eq. (1.18), p. 560: an unexpected permanent rise of the nominal rate
from `r` to `i` at date 0, with a constant real rate `r > 0` (so inflation `i − r`) and constant
surplus `s₀ ≠ 0`. Before: the steady state, valuation `Q⁻B/P⁻ = s₀/r` with `Q⁻ = 1/(r + ω)`.
After: any path `V` solving the flow identity with the transversality condition and
`V(0) = Q(0)B/P(0)`, `Q(0) = 1/(i + ω)` the new bundle price. Then `P(0)/P(0⁻) = (r+ω)/(i+ω)`. -/
theorem price_jump_permanent {r i ω s₀ B Pm P0 : ℝ} {V : ℝ → ℝ} (hr : 0 < r)
    (hrω : 0 < r + ω) (hiω : 0 < i + ω) (hs : s₀ ≠ 0) (hB : B ≠ 0) (hPm : Pm ≠ 0)
    (hpre : bondPrice (fun _ => r) ω 0 * B / Pm = pv (fun _ => r) (fun _ => s₀) 0)
    (hV : FlowOn (fun _ => r) (fun _ => s₀) V 0) (hT : TVC (fun _ => r) V 0)
    (hV0 : V 0 = bondPrice (fun _ => i) ω 0 * B / P0) :
    P0 / Pm = (r + ω) / (i + ω) := by
  have hv := value_const_const hr hV hT (le_refl 0)
  rw [pv_const_const hr, bondPrice_const hrω] at hpre
  rw [bondPrice_const hiω] at hV0
  rw [price_jump_of_valuation (div_ne_zero hs hr.ne') hB (by positivity) hPm hpre
    (hV0 ▸ hv)]
  field_simp

/-- Cochrane (2023), A1.2.1, eq. (1.18): the post-jump equilibrium exists. With `P̄ > 0`, let
`P(τ) = P̄((r+ω)/(i+ω))e^{(i−r)τ}` (inflation `i − r`) and `B(τ) = s₀(i + ω)P(τ)/r`. Then `B(0)` is
the predetermined steady-state debt `s₀(r+ω)P̄/r`, the geometric flow (3.34) holds with the bundle
price `Q = 1/(i + ω)`, and `V = QB/P` solves the flow identity with real rate `r` and satisfies
the transversality condition. -/
theorem post_jump_equilibrium {r i ω s₀ Pbar : ℝ} (hr : 0 < r) (hiω : 0 < i + ω)
    (hrω : 0 < r + ω) (hP : 0 < Pbar) :
    (s₀ * (i + ω) * (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * 0)) / r =
        s₀ * (r + ω) * Pbar / r) ∧
      (∀ τ, HasDerivAt (fun x => Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * x))
        ((i - r) * (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ))) τ) ∧
      (∀ τ, bondPrice (fun _ => i) ω τ *
          ((i - r) * (s₀ * (i + ω) * (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ)) / r) +
            ω * (s₀ * (i + ω) * (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ)) / r)) =
        s₀ * (i + ω) * (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ)) / r -
          Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ) * s₀) ∧
      FlowOn (fun _ => r) (fun _ => s₀) (fun τ => bondPrice (fun _ => i) ω τ *
        (s₀ * (i + ω) * (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ)) / r) /
          (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ))) 0 ∧
      TVC (fun _ => r) (fun τ => bondPrice (fun _ => i) ω τ *
        (s₀ * (i + ω) * (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ)) / r) /
          (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ))) 0 := by
  have hV : ∀ τ, bondPrice (fun _ => i) ω τ *
      (s₀ * (i + ω) * (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ)) / r) /
        (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ)) = s₀ / r := by
    intro τ
    rw [bondPrice_const hiω]
    have := Real.exp_pos ((i - r) * τ)
    field_simp
  have hF : FlowOn (fun _ => r) (fun _ => s₀) (fun τ => bondPrice (fun _ => i) ω τ *
      (s₀ * (i + ω) * (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ)) / r) /
        (Pbar * ((r + ω) / (i + ω)) * Real.exp ((i - r) * τ))) 0 := by
    simp only [hV]
    refine ⟨continuousOn_const, fun τ _ => ?_⟩
    convert hasDerivAt_const τ (s₀ / r) using 1
    field_simp
    ring
  refine ⟨?_, fun τ => ?_, fun τ => ?_, hF, ?_⟩
  · rw [mul_zero, Real.exp_zero]
    field_simp
  · have h := (((hasDerivAt_id τ).const_mul (i - r)).exp).const_mul (Pbar * ((r + ω) / (i + ω)))
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  · rw [bondPrice_const hiω]
    field_simp
    ring
  · refine (valuation_iff_tvc continuousOn_const continuousOn_const hF
      (pvIntegrable_const hr s₀ 0)).1 ?_
    rw [hV, pv_const_const hr]

/-- Cochrane (2023), A1.2.1, eq. (1.20), p. 560: for a perpetuity (`ω = 0`) the permanent rate
rise gives `P(0) = (r/i)P(0⁻)`. -/
theorem price_jump_perpetuity {r i s₀ B Pm P0 : ℝ} {V : ℝ → ℝ} (hr : 0 < r) (hi : 0 < i)
    (hs : s₀ ≠ 0) (hB : B ≠ 0) (hPm : Pm ≠ 0)
    (hpre : bondPrice (fun _ => r) 0 0 * B / Pm = pv (fun _ => r) (fun _ => s₀) 0)
    (hV : FlowOn (fun _ => r) (fun _ => s₀) V 0) (hT : TVC (fun _ => r) V 0)
    (hV0 : V 0 = bondPrice (fun _ => i) 0 0 * B / P0) : P0 = r / i * Pm := by
  have h := price_jump_permanent hr (by linarith) (by linarith) hs hB hPm hpre hV hT hV0
  rw [add_zero, add_zero] at h
  field_simp at h ⊢
  linarith

/-- Cochrane (2023), A1.2.1, p. 560: "a rise in interest rates from `r = 3%` to `i = 4%`
occasions a 25% price level drop" for a perpetuity: `r/i = 3/4`. -/
theorem price_jump_perpetuity_numeric : ((0.03 : ℝ) + 0) / ((0.04 : ℝ) + 0) = 3 / 4 := by
  norm_num

/-- Cochrane (2023), A1.2.1, p. 560 and E20: for instantaneous (short-term) debt, `ω → ∞`, the
jump ratio `(r + ω)/(i + ω) → 1`: no price-level jump ("`ϖ = ∞` … `P₀ = P` and there is no
downward jump"). -/
theorem price_jump_tendsto_one (r i : ℝ) :
    Tendsto (fun ω : ℝ => (r + ω) / (i + ω)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun ω : ℝ => i + ω) atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_id
  have h : Tendsto (fun ω : ℝ => 1 - (i - r) / (i + ω)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop h1)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (-i)] with ω hω
  have hω1 : i + ω ≠ 0 := by linarith
  field_simp
  ring

/-- Cochrane (2023), A1.2.1, p. 560 ("The price level P₀ jumps down as the interest-rate rises"):
for `r < i` and `r + ω > 0` the jump ratio lies in `(0, 1)`. -/
theorem price_jump_lt_one {r i ω : ℝ} (hri : r < i) (hrω : 0 < r + ω) :
    0 < (r + ω) / (i + ω) ∧ (r + ω) / (i + ω) < 1 := by
  have hiω : 0 < i + ω := by linarith
  refine ⟨div_pos hrω hiω, (div_lt_one hiω).2 (by linarith)⟩

/-- Cochrane (2023), A1.2.1, p. 560 ("governments maintain much shorter maturity structures …
reducing the size of the effect"): for `r ≤ i` the ratio `(r+ω)/(i+ω)` is nondecreasing in `ω`,
so shorter maturity (larger `ω`) means a smaller downward jump. -/
theorem price_jump_mono {r i ω₁ ω₂ : ℝ} (hri : r ≤ i) (hrω : 0 < r + ω₁) (hω : ω₁ ≤ ω₂) :
    (r + ω₁) / (i + ω₁) ≤ (r + ω₂) / (i + ω₂) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-! ### Forward guidance (A1 p. 561) -/

/-- Cochrane (2023), A1.2.1, p. 561: the forward-guidance path of the nominal rate, `r` until
`T` and `i` after (announced at date 0). -/
noncomputable def fgRate (r i T u : ℝ) : ℝ := if u ≤ T then r else i

/-- Cochrane (2023), A1.2.1, p. 561: the cumulated bundle rate under forward guidance up to
`u ∈ [0, T]` is `(r + ω)u`. -/
theorem cumRate_fg_le {r i T ω u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T) :
    cumRate (fun x => fgRate r i T x + ω) 0 u = (r + ω) * u := by
  rw [cumRate, intervalIntegral.integral_congr (g := fun _ => r + ω) (fun x hx => ?_),
    intervalIntegral.integral_const, smul_eq_mul]
  · ring
  · rw [Set.uIcc_of_le hu] at hx
    simp only [fgRate, hx.2.trans huT, ↓reduceIte]

/-- Cochrane (2023), A1.2.1, p. 561: the cumulated bundle rate under forward guidance up to
`u ≥ T ≥ 0` is `(r + ω)T + (i + ω)(u − T)`. -/
theorem cumRate_fg_ge {r i T ω u : ℝ} (hT : 0 ≤ T) (hTu : T ≤ u) :
    cumRate (fun x => fgRate r i T x + ω) 0 u = (r + ω) * T + (i + ω) * (u - T) := by
  have h1 : IntervalIntegrable (fun x => fgRate r i T x + ω) volume 0 T := by
    refine (intervalIntegrable_const (c := r + ω)).congr_ae ?_
    refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun x hx => ?_)
    rw [Set.uIoc_of_le hT] at hx
    simp only [fgRate, hx.2, ↓reduceIte]
  have h2 : IntervalIntegrable (fun x => fgRate r i T x + ω) volume T u := by
    refine (intervalIntegrable_const (c := i + ω)).congr_ae ?_
    refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun x hx => ?_)
    rw [Set.uIoc_of_le hTu] at hx
    simp only [fgRate, not_le.2 hx.1, ↓reduceIte]
  have e2 : ∫ x in T..u, fgRate r i T x + ω = ∫ _ in T..u, i + ω := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun x hx => ?_)
    rw [Set.uIoc_of_le hTu] at hx
    simp only [fgRate, not_le.2 hx.1, ↓reduceIte]
  rw [cumRate, ← intervalIntegral.integral_add_adjacent_intervals h1 h2, e2,
    intervalIntegral.integral_const, smul_eq_mul]
  have e1 := cumRate_fg_le (r := r) (i := i) (ω := ω) hT le_rfl
  rw [cumRate] at e1
  rw [e1]
  ring

/-- Cochrane (2023), A1.2.1, p. 561: the bundle price at date 0 under forward guidance,
`Q(0) = (1 − e^{−(r+ω)T})/(r + ω) + e^{−(r+ω)T}/(i + ω)` (the bracket of the book's continuous
forward-guidance valuation equation). -/
theorem bondPrice_fg {r i T ω : ℝ} (hT : 0 ≤ T) (hrω : 0 < r + ω) (hiω : 0 < i + ω) :
    bondPrice (fgRate r i T) ω 0 =
      (1 - Real.exp (-(r + ω) * T)) / (r + ω) + Real.exp (-(r + ω) * T) / (i + ω) := by
  set f : ℝ → ℝ := fun u => disc (fun x => fgRate r i T x + ω) 0 u * 1 with hf
  have hleft : ∀ u, 0 ≤ u → u ≤ T → f u = Real.exp (-(r + ω) * u) := by
    intro u hu huT
    simp only [hf, mul_one, disc, cumRate_fg_le hu huT]
    ring_nf
  have hright : ∀ u, T ≤ u →
      f u = Real.exp ((i - r) * T) * Real.exp (-(i + ω) * u) := by
    intro u hu
    simp only [hf, mul_one, disc, cumRate_fg_ge hT hu, ← Real.exp_add]
    ring_nf
  have hR : IntegrableOn f (Set.Ioi T) := by
    exact IntegrableOn.congr_fun
      ((integrableOn_exp_mul_Ioi (a := -(i + ω)) (by linarith) T).const_mul
        (Real.exp ((i - r) * T))) (fun u hu => (hright u (le_of_lt hu)).symm) measurableSet_Ioi
  have hL : IntervalIntegrable f volume 0 T := by
    refine ((by fun_prop : Continuous fun u : ℝ => Real.exp (-(r + ω) * u)).intervalIntegrable
      0 T).congr_ae ?_
    refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun x hx => ?_)
    rw [Set.uIoc_of_le hT] at hx
    exact (hleft x hx.1.le hx.2).symm
  have hsplit := intervalIntegral.integral_interval_add_Ioi' hL hR
  have eL : ∫ u in (0 : ℝ)..T, f u = (1 - Real.exp (-(r + ω) * T)) / (r + ω) := by
    rw [intervalIntegral.integral_congr (g := fun u => Real.exp (-(r + ω) * u)) (fun x hx => ?_)]
    · rw [← intervalIntegral.integral_Ioi_sub_Ioi (integrableOn_exp_mul_Ioi (by linarith) 0) hT,
        integral_exp_mul_Ioi (by linarith), integral_exp_mul_Ioi (by linarith), mul_zero,
        Real.exp_zero]
      field_simp
    · rw [Set.uIcc_of_le hT] at hx
      exact hleft x hx.1 hx.2
  have eR : ∫ u in Set.Ioi T, f u = Real.exp (-(r + ω) * T) / (i + ω) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu => hright u (le_of_lt hu)),
      integral_const_mul, integral_exp_mul_Ioi (by linarith)]
    have hE : Real.exp ((i - r) * T) * Real.exp (-(i + ω) * T) = Real.exp (-(r + ω) * T) := by
      rw [← Real.exp_add]
      ring_nf
    rw [← hE]
    field_simp
  rw [bondPrice, pv, ← hsplit, eL, eR]

/-- Cochrane (2023), A1.2.1, p. 561: forward guidance. The nominal rate is announced at date 0 to
rise from `r` to `i` at `T ≥ 0`, with a constant real rate `r > 0`, constant surplus `s₀ ≠ 0`,
and the pre-announcement steady state `Q⁻B/P⁻ = s₀/r`, `Q⁻ = 1/(r + ω)`. For any post-news path
solving the flow identity with the transversality condition and `V(0) = Q(0)B/P(0)`, `Q(0)` the
forward-guidance bundle price:
`P(0)/P(0⁻) − 1 = e^{−(r+ω)T}((r + ω)/(i + ω) − 1)`. -/
theorem price_jump_fg {r i T ω s₀ B Pm P0 : ℝ} {V : ℝ → ℝ} (hr : 0 < r) (hT : 0 ≤ T)
    (hrω : 0 < r + ω) (hiω : 0 < i + ω) (hs : s₀ ≠ 0) (hB : B ≠ 0) (hPm : Pm ≠ 0)
    (hpre : bondPrice (fun _ => r) ω 0 * B / Pm = pv (fun _ => r) (fun _ => s₀) 0)
    (hV : FlowOn (fun _ => r) (fun _ => s₀) V 0) (hTv : TVC (fun _ => r) V 0)
    (hV0 : V 0 = bondPrice (fgRate r i T) ω 0 * B / P0) :
    P0 / Pm - 1 = Real.exp (-(r + ω) * T) * ((r + ω) / (i + ω) - 1) := by
  have hv := value_const_const hr hV hTv (le_refl 0)
  rw [pv_const_const hr, bondPrice_const hrω] at hpre
  rw [price_jump_of_valuation (div_ne_zero hs hr.ne') hB (by positivity) hPm hpre (hV0 ▸ hv),
    bondPrice_fg hT hrω hiω]
  field_simp
  ring

/-- Cochrane (2023), A1.2.1, p. 561: with `T = 0` the forward-guidance formula is the immediate
permanent rise (1.18). -/
theorem fg_jump_at_zero (r i ω : ℝ) :
    Real.exp (-(r + ω) * 0) * ((r + ω) / (i + ω) - 1) = (r + ω) / (i + ω) - 1 := by
  simp

/-- Cochrane (2023), A1.2.1, p. 561 ("As T → ∞, the downward price-level jump goes to zero"). -/
theorem fg_jump_tendsto_zero {r i ω : ℝ} (hrω : 0 < r + ω) :
    Tendsto (fun T => Real.exp (-(r + ω) * T) * ((r + ω) / (i + ω) - 1)) atTop (𝓝 0) := by
  have h : Tendsto (fun T => Real.exp (-(r + ω) * T)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  simpa using h.mul_const ((r + ω) / (i + ω) - 1)

/-- Cochrane (2023), A1.2.1, p. 561 ("forward guidance works"): for `r < i` the price level still
jumps down at date 0, by `e^{−(r+ω)T}(i − r)/(i + ω) > 0`. -/
theorem fg_jump_neg {r i ω T : ℝ} (hri : r < i) (hrω : 0 < r + ω) :
    Real.exp (-(r + ω) * T) * ((r + ω) / (i + ω) - 1) =
        -(Real.exp (-(r + ω) * T) * ((i - r) / (i + ω))) ∧
      0 < Real.exp (-(r + ω) * T) * ((i - r) / (i + ω)) := by
  have hiω : 0 < i + ω := by linarith
  refine ⟨by field_simp; ring, mul_pos (Real.exp_pos _) (div_pos (by linarith) hiω)⟩

/-- Cochrane (2023), A1.2.1, p. 561 ("Longer T … give a smaller price-level jump"): the size of
the jump `e^{−(r+ω)T}(i − r)/(i + ω)` is nonincreasing in the announcement horizon `T`. -/
theorem fg_jump_antitone_T {r i ω T₁ T₂ : ℝ} (hri : r ≤ i) (hrω : 0 < r + ω) (hT : T₁ ≤ T₂) :
    Real.exp (-(r + ω) * T₂) * ((i - r) / (i + ω)) ≤
      Real.exp (-(r + ω) * T₁) * ((i - r) / (i + ω)) := by
  have hiω : 0 < i + ω := by linarith
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith))
    (div_nonneg (by linarith) hiω.le)

/-- Cochrane (2023), A1.2.1, p. 561 ("shorter maturity structures — lower ω or larger ϖ — give a
smaller price-level jump"): for `T ≥ 0` the size of the jump is nonincreasing in `ω`. -/
theorem fg_jump_antitone_ω {r i ω₁ ω₂ T : ℝ} (hri : r ≤ i) (hrω : 0 < r + ω₁) (hω : ω₁ ≤ ω₂)
    (hT : 0 ≤ T) :
    Real.exp (-(r + ω₂) * T) * ((i - r) / (i + ω₂)) ≤
      Real.exp (-(r + ω₁) * T) * ((i - r) / (i + ω₁)) := by
  have hiω : 0 < i + ω₁ := by linarith
  refine mul_le_mul (Real.exp_le_exp.2 (by nlinarith))
    (div_le_div_of_nonneg_left (by linarith) hiω (by linarith))
    (div_nonneg (by linarith) (by linarith)) (Real.exp_pos _).le

/-! ## (3.34)–(3.39) for an arbitrary continuum of maturities

The book's general maturity structure: at date `x` the government owes the nominal density
`b(x, m)` of zero-coupon debt due at date `m` (the book's `B_x^{(m)}`), priced at `q(x, m)` (the
book's `Q_x^{(m)}`), and the market value is `∫_0^∞ q(x, x+j)b(x, x+j)dj`. The book differentiates
this integral without stating any regularity. We state it explicitly (`MaturityRegularAt`):
joint differentiability of `q` and `b` in `(date, maturity)` with partials `(qt, qm)`, `(bt, bm)`;
integrability of the value, of new issues and of the maturity-direction derivative; decay of
the value density at long maturities; and a locally uniform integrable bound on the date
derivative (the hypotheses of Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le`).
`bt(x, m)` is the book's `dB_x^{(m)}/dx` (sales of the bond due at `m`), `qt/q` its return. -/

/-- Cochrane (2023), §3.6.2, p. 75: the linear map `(u, v) ↦ a·u + c·v`, the derivative of a
function of `(date, maturity)` with partial derivatives `a` and `c`. -/
noncomputable def partialsCLM (a c : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ + c • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- Cochrane (2023), §3.6.2: `partialsCLM a c (u, v) = a·u + c·v`. -/
theorem partialsCLM_apply (a c u v : ℝ) : partialsCLM a c (u, v) = a * u + c * v := by
  simp [partialsCLM]

/-- Cochrane (2023), §3.6.2: along a fixed time to maturity `j`, `d/dx f(x, x+j) = f_t + f_m`. -/
theorem hasDerivAt_diag {f ft fm : ℝ → ℝ → ℝ} {x j : ℝ}
    (h : HasFDerivAt (fun p : ℝ × ℝ => f p.1 p.2) (partialsCLM (ft x (x + j)) (fm x (x + j)))
      (x, x + j)) :
    HasDerivAt (fun y => f y (y + j)) (ft x (x + j) + fm x (x + j)) x := by
  have hl : HasDerivAt (fun y : ℝ => (y, y + j)) ((1 : ℝ), (1 : ℝ)) x :=
    (hasDerivAt_id' x).prodMk ((hasDerivAt_id' x).add_const j)
  have := h.comp_hasDerivAt x hl
  rw [partialsCLM_apply] at this
  simpa [Function.comp_def] using this

/-- Cochrane (2023), §3.6.2: at a fixed date `x`, `d/dj f(x, x+j) = f_m`. -/
theorem hasDerivAt_maturity {f ft fm : ℝ → ℝ → ℝ} {x j : ℝ}
    (h : HasFDerivAt (fun p : ℝ × ℝ => f p.1 p.2) (partialsCLM (ft x (x + j)) (fm x (x + j)))
      (x, x + j)) :
    HasDerivAt (fun k => f x (x + k)) (fm x (x + j)) j := by
  have hl : HasDerivAt (fun k : ℝ => (x, x + k)) ((0 : ℝ), (1 : ℝ)) j :=
    (hasDerivAt_const j x).prodMk ((hasDerivAt_id' j).const_add x)
  have := h.comp_hasDerivAt j hl
  rw [partialsCLM_apply] at this
  simpa [Function.comp_def] using this

/-- Cochrane (2023), eq. (3.35), p. 74–75: the nominal market value of the debt,
`∫_0^∞ Q_x^{(x+j)}B_x^{(x+j)}dj`. -/
noncomputable def mktValue (q b : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ j in Set.Ioi 0, q x (x + j) * b x (x + j)

/-- Cochrane (2023), eq. (3.34), p. 74: the value of net debt sales `∫_0^∞ Q dB dj`. -/
noncomputable def issuanceValue (q bt : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ j in Set.Ioi 0, q x (x + j) * bt x (x + j)

/-- Cochrane (2023), eq. (3.37), p. 75: the nominal capital gain on the portfolio,
`∫_0^∞ (dQ_x^{(x+j)}/dx)B_x^{(x+j)}dj`. -/
noncomputable def capitalGain (qt b : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ j in Set.Ioi 0, qt x (x + j) * b x (x + j)

/-- Cochrane (2023), eq. (3.37), p. 75: the value-weighted nominal return on the portfolio. -/
noncomputable def valueWeightedReturn (q b qt : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  capitalGain qt b x / mktValue q b x

/-- Cochrane (2023), §3.6.2, regularity left implicit by the book: the conditions at date `τ`
under which the market value `∫_0^∞ q b dj` may be differentiated under the integral sign —
joint differentiability on a neighbourhood `s` of `τ`, integrability of the value, of new issues
and of the maturity derivative, decay at long maturities, measurability of the capital gain and
an integrable bound on the date derivative uniformly over `s`. -/
def MaturityRegularAt (q b qt qm bt bm : ℝ → ℝ → ℝ) (τ : ℝ) : Prop :=
  ∃ s ∈ 𝓝 τ, ∃ bound : ℝ → ℝ,
    (∀ x ∈ s, ∀ j, 0 ≤ j → HasFDerivAt (fun p : ℝ × ℝ => q p.1 p.2)
      (partialsCLM (qt x (x + j)) (qm x (x + j))) (x, x + j)) ∧
    (∀ x ∈ s, ∀ j, 0 ≤ j → HasFDerivAt (fun p : ℝ × ℝ => b p.1 p.2)
      (partialsCLM (bt x (x + j)) (bm x (x + j))) (x, x + j)) ∧
    IntegrableOn (fun j => q τ (τ + j) * b τ (τ + j)) (Set.Ioi 0) ∧
    IntegrableOn (fun j => q τ (τ + j) * bt τ (τ + j)) (Set.Ioi 0) ∧
    AEStronglyMeasurable (fun j => qt τ (τ + j) * b τ (τ + j)) (volume.restrict (Set.Ioi 0)) ∧
    IntegrableOn (fun j => qm τ (τ + j) * b τ (τ + j) + q τ (τ + j) * bm τ (τ + j))
      (Set.Ioi 0) ∧
    Tendsto (fun j => q τ (τ + j) * b τ (τ + j)) atTop (𝓝 0) ∧
    IntegrableOn bound (Set.Ioi 0) ∧
    ∀ j, 0 < j → ∀ x ∈ s, ‖(qt x (x + j) + qm x (x + j)) * b x (x + j) +
      q x (x + j) * (bt x (x + j) + bm x (x + j))‖ ≤ bound j

/-- Cochrane (2023), eqs. (3.37)–(3.38), p. 75, general maturity structure: under
`MaturityRegularAt`, the market value is differentiable with
`d/dx ∫q b = ∫(∂_x q)b + ∫q ∂_x b − q(τ,τ)b(τ,τ)`: capital gains plus net sales minus the debt
maturing now. -/
theorem hasDerivAt_mktValue {q b qt qm bt bm : ℝ → ℝ → ℝ} {τ : ℝ}
    (h : MaturityRegularAt q b qt qm bt bm τ) :
    HasDerivAt (mktValue q b)
      (capitalGain qt b τ + issuanceValue q bt τ - q τ τ * b τ τ) τ := by
  obtain ⟨s, hs, bound, hq, hb, hI, hIss, hCGm, hM, hlim, hbI, hbd⟩ := h
  have hτs : τ ∈ s := mem_of_mem_nhds hs
  have hG : ∀ x ∈ s, ∀ j, 0 ≤ j → HasDerivAt (fun y => q y (y + j) * b y (y + j))
      ((qt x (x + j) + qm x (x + j)) * b x (x + j) +
        q x (x + j) * (bt x (x + j) + bm x (x + j))) x :=
    fun x hx j hj => (hasDerivAt_diag (hq x hx j hj)).mul (hasDerivAt_diag (hb x hx j hj))
  have hGm : ∀ x ∈ s, ∀ j, 0 ≤ j → HasDerivAt (fun k => q x (x + k) * b x (x + k))
      (qm x (x + j) * b x (x + j) + q x (x + j) * bm x (x + j)) j :=
    fun x hx j hj => (hasDerivAt_maturity (hq x hx j hj)).mul (hasDerivAt_maturity (hb x hx j hj))
  have hcont : ∀ x ∈ s, ContinuousOn (fun j => q x (x + j) * b x (x + j)) (Set.Ici 0) :=
    fun x hx j hj => (hGm x hx j hj).continuousAt.continuousWithinAt
  have hmeas : ∀ᶠ x in 𝓝 τ, AEStronglyMeasurable (fun j => q x (x + j) * b x (x + j))
      (volume.restrict (Set.Ioi 0)) := by
    filter_upwards [hs] with x hx
    exact ((hcont x hx).mono Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  have hsplit : (fun j => (qt τ (τ + j) + qm τ (τ + j)) * b τ (τ + j) +
      q τ (τ + j) * (bt τ (τ + j) + bm τ (τ + j))) = fun j =>
      (qt τ (τ + j) * b τ (τ + j) + q τ (τ + j) * bt τ (τ + j)) +
        (qm τ (τ + j) * b τ (τ + j) + q τ (τ + j) * bm τ (τ + j)) := by
    funext j
    ring
  have hF'meas : AEStronglyMeasurable (fun j => (qt τ (τ + j) + qm τ (τ + j)) * b τ (τ + j) +
      q τ (τ + j) * (bt τ (τ + j) + bm τ (τ + j))) (volume.restrict (Set.Ioi 0)) := by
    rw [hsplit]
    exact (hCGm.add hIss.aestronglyMeasurable).add hM.aestronglyMeasurable
  obtain ⟨hTint, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi 0)) (F := fun x j => q x (x + j) * b x (x + j))
    (F' := fun x j => (qt x (x + j) + qm x (x + j)) * b x (x + j) +
      q x (x + j) * (bt x (x + j) + bm x (x + j))) (bound := bound) hs hmeas hI hF'meas
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun j hj x hx => hbd j hj x hx))
    hbI ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun j hj x hx => hG x hx j (le_of_lt hj)))
  have hTint' : IntegrableOn (fun j => (qt τ (τ + j) * b τ (τ + j) + q τ (τ + j) * bt τ (τ + j)) +
      (qm τ (τ + j) * b τ (τ + j) + q τ (τ + j) * bm τ (τ + j))) (Set.Ioi 0) := by
    rw [← hsplit]
    exact hTint
  have hA : IntegrableOn (fun j => qt τ (τ + j) * b τ (τ + j) + q τ (τ + j) * bt τ (τ + j))
      (Set.Ioi 0) := by
    have := hTint'.sub hM
    refine this.congr_fun (fun j _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    ring
  have hCG : IntegrableOn (fun j => qt τ (τ + j) * b τ (τ + j)) (Set.Ioi 0) := by
    have := hA.sub hIss
    refine this.congr_fun (fun j _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    ring
  have hMval : ∫ j in Set.Ioi 0, (qm τ (τ + j) * b τ (τ + j) + q τ (τ + j) * bm τ (τ + j)) =
      0 - q τ (τ + 0) * b τ (τ + 0) :=
    integral_Ioi_of_hasDerivAt_of_tendsto (hcont τ hτs 0 (Set.mem_Ici.2 le_rfl))
      (fun j hj => hGm τ hτs j (le_of_lt hj)) hM hlim
  refine hD.congr_deriv ?_
  rw [hsplit, integral_add hA hM, integral_add hCG hIss, hMval, add_zero]
  unfold capitalGain issuanceValue
  ring

/-- Cochrane (2023), eqs. (3.34) and (3.38), p. 75, general maturity structure: if the maturing
bond is worth its face value, `q(τ,τ) = 1`, and the flow (3.34)
`B_τ^{(τ)} = P_τ s_τ + ∫Q dB dj` holds, then `d/dx ∫q b = ∫(∂_x q)b − P s`. -/
theorem hasDerivAt_mktValue_flow {q b qt qm bt bm : ℝ → ℝ → ℝ} {P s : ℝ → ℝ} {τ : ℝ}
    (h : MaturityRegularAt q b qt qm bt bm τ) (hmat : q τ τ = 1)
    (hflow : b τ τ = P τ * s τ + issuanceValue q bt τ) :
    HasDerivAt (mktValue q b) (capitalGain qt b τ - P τ * s τ) τ := by
  refine (hasDerivAt_mktValue h).congr_deriv ?_
  rw [hmat, hflow]
  ring

/-- Cochrane (2023), eq. (3.37), p. 75: the value-weighted return is the average of the
individual bond returns `(∂_x Q^{(m)})/Q^{(m)}` with weights `Q^{(m)}B^{(m)}/∫QB`. -/
theorem valueWeightedReturn_eq {q b qt : ℝ → ℝ → ℝ} {τ : ℝ}
    (hq0 : ∀ j, 0 < j → q τ (τ + j) ≠ 0) :
    valueWeightedReturn q b qt τ = ∫ j in Set.Ioi 0,
      qt τ (τ + j) / q τ (τ + j) * (q τ (τ + j) * b τ (τ + j) / mktValue q b τ) := by
  rw [valueWeightedReturn, capitalGain, ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi (fun j hj => ?_)
  have := hq0 j hj
  field_simp

/-- Cochrane (2023), eq. (3.39), p. 75, general maturity structure: the real value
`V = ∫QB dj/P` obeys `dV = −s dt + V dR` with `dR = R − π`, `R` the value-weighted nominal
return (3.37) and `π = P'/P`. -/
theorem hasDerivAt_value_general {q b qt qm bt bm : ℝ → ℝ → ℝ} {P s : ℝ → ℝ} {τ dP : ℝ}
    (h : MaturityRegularAt q b qt qm bt bm τ) (hmat : q τ τ = 1)
    (hflow : b τ τ = P τ * s τ + issuanceValue q bt τ) (hP : HasDerivAt P dP τ)
    (hA : mktValue q b τ ≠ 0) (hP0 : P τ ≠ 0) :
    HasDerivAt (fun x => mktValue q b x / P x)
      ((valueWeightedReturn q b qt τ - dP / P τ) * (mktValue q b τ / P τ) - s τ) τ := by
  convert (hasDerivAt_mktValue_flow h hmat hflow).div hP hP0 using 1
  rw [valueWeightedReturn]
  field_simp
  ring

/-- Cochrane (2023), §3.6.2 under perfect foresight: zero-coupon bond prices
`q(x, m) = exp(−∫_x^m i)` satisfy `∂_x q = i(x)q`, `∂_m q = −i(m)q` and `q(m, m) = 1`. -/
theorem zeroPrice_partials {i : ℝ → ℝ} (hi : Continuous i) (x m : ℝ) :
    HasDerivAt (fun y => disc i y m) (i x * disc i x m) x ∧
      HasDerivAt (fun y => disc i x y) (-(i m) * disc i x m) m ∧ disc i m m = 1 := by
  refine ⟨?_, ?_, disc_self i m⟩
  · have h1 : HasDerivAt (fun y => ∫ u in y..m, i u) (-(i x)) x :=
      intervalIntegral.integral_hasDerivAt_left (hi.intervalIntegrable _ _)
        (hi.stronglyMeasurableAtFilter _ _) hi.continuousAt
    refine h1.neg.exp.congr_deriv ?_
    simp only [disc, cumRate, Pi.neg_apply]
    ring
  · have h1 : HasDerivAt (fun y => ∫ u in x..y, i u) (i m) m :=
      intervalIntegral.integral_hasDerivAt_right (hi.intervalIntegrable _ _)
        (hi.stronglyMeasurableAtFilter _ _) hi.continuousAt
    refine h1.neg.exp.congr_deriv ?_
    simp only [disc, cumRate, Pi.neg_apply]
    ring

/-- Cochrane (2023), eq. (3.39) with perfect-foresight pricing: if `∂_x q = i q` for all bonds
outstanding, the capital gain is `i·∫q b`, i.e. the value-weighted nominal return is `i`. -/
theorem capitalGain_priced {q b qt : ℝ → ℝ → ℝ} {i : ℝ → ℝ} {τ : ℝ}
    (hprice : ∀ j, 0 < j → qt τ (τ + j) = i τ * q τ (τ + j)) :
    capitalGain qt b τ = i τ * mktValue q b τ := by
  rw [capitalGain, mktValue, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun j hj => ?_)
  rw [hprice j hj]
  ring

/-- Cochrane (2023), eqs. (3.34), (3.38)–(3.39) with perfect-foresight pricing, general
maturity structure: the nominal market value obeys the short-debt flow (3.29),
`d/dx ∫q b = i ∫q b − P s`. -/
theorem hasDerivAt_mktValue_priced {q b qt qm bt bm : ℝ → ℝ → ℝ} {i P s : ℝ → ℝ} {τ : ℝ}
    (h : MaturityRegularAt q b qt qm bt bm τ) (hmat : q τ τ = 1)
    (hprice : ∀ j, 0 < j → qt τ (τ + j) = i τ * q τ (τ + j))
    (hflow : b τ τ = P τ * s τ + issuanceValue q bt τ) :
    HasDerivAt (mktValue q b) (i τ * mktValue q b τ - P τ * s τ) τ := by
  have := hasDerivAt_mktValue_flow h hmat hflow
  rwa [capitalGain_priced hprice] at this

/-- Cochrane (2023), eq. (3.39), general maturity structure: with regularity on `[t, ∞)`,
maturing bonds at par, perfect-foresight pricing and the flow (3.34) on `(t, ∞)`, and a positive
price level (free to jump at `t`), the real value `V = ∫q b dj/P` solves the flow identity
`V' = (i − π)V − s` on `[t, ∞)`. -/
theorem flowOn_value_general {q b qt qm bt bm : ℝ → ℝ → ℝ} {i P s dP : ℝ → ℝ} {t : ℝ}
    (hreg : ∀ τ, t ≤ τ → MaturityRegularAt q b qt qm bt bm τ)
    (hmat : ∀ τ, t ≤ τ → q τ τ = 1)
    (hprice : ∀ τ, t ≤ τ → ∀ j, 0 < j → qt τ (τ + j) = i τ * q τ (τ + j))
    (hflow : ∀ τ, t ≤ τ → b τ τ = P τ * s τ + issuanceValue q bt τ)
    (hPc : ContinuousOn P (Set.Ici t)) (hPpos : ∀ τ, t ≤ τ → 0 < P τ)
    (hP : ∀ τ, t < τ → HasDerivAt P (dP τ) τ) :
    FlowOn (fun τ => i τ - dP τ / P τ) s (fun τ => mktValue q b τ / P τ) t := by
  have hD : ∀ τ, t ≤ τ → HasDerivAt (mktValue q b) (i τ * mktValue q b τ - P τ * s τ) τ :=
    fun τ hτ => hasDerivAt_mktValue_priced (hreg τ hτ) (hmat τ hτ) (hprice τ hτ) (hflow τ hτ)
  exact flowOn_of_nominal (B := mktValue q b)
    (fun τ hτ => (hD τ hτ).continuousAt.continuousWithinAt) hPc hPpos
    (fun τ hτ => hD τ hτ.le) hP

/-- Cochrane (2023), eq. (3.35), p. 75, general maturity structure: along the flow, the
valuation equation `∫Q B dj/P = ∫_t^∞ D(t,τ)s(τ)dτ` holds iff the transversality condition
holds; and then the price level is `P(t) = ∫Q B dj/∫D s`. -/
theorem valuation_general_iff {q b qt qm bt bm : ℝ → ℝ → ℝ} {i P s dP : ℝ → ℝ} {t : ℝ}
    (hreg : ∀ τ, t ≤ τ → MaturityRegularAt q b qt qm bt bm τ)
    (hmat : ∀ τ, t ≤ τ → q τ τ = 1)
    (hprice : ∀ τ, t ≤ τ → ∀ j, 0 < j → qt τ (τ + j) = i τ * q τ (τ + j))
    (hflow : ∀ τ, t ≤ τ → b τ τ = P τ * s τ + issuanceValue q bt τ)
    (hPc : ContinuousOn P (Set.Ici t)) (hPpos : ∀ τ, t ≤ τ → 0 < P τ)
    (hP : ∀ τ, t < τ → HasDerivAt P (dP τ) τ)
    (hr : ContinuousOn (fun τ => i τ - dP τ / P τ) (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hI : PVIntegrable (fun τ => i τ - dP τ / P τ) s t) :
    (mktValue q b t / P t = pv (fun τ => i τ - dP τ / P τ) s t ↔
      TVC (fun τ => i τ - dP τ / P τ) (fun τ => mktValue q b τ / P τ) t) ∧
    (TVC (fun τ => i τ - dP τ / P τ) (fun τ => mktValue q b τ / P τ) t →
      mktValue q b t ≠ 0 → pv (fun τ => i τ - dP τ / P τ) s t ≠ 0 →
      P t = mktValue q b t / pv (fun τ => i τ - dP τ / P τ) s t) := by
  have hF := flowOn_value_general hreg hmat hprice hflow hPc hPpos hP
  refine ⟨valuation_iff_tvc hr hs hF hI, fun hT hA hpv => ?_⟩
  exact (price_level_determined hr hs hI hA hpv).1 ⟨_, hF, hT, rfl⟩

/-- Cochrane (2023), §3.6.2 and A1.2.1, geometric special case: with zero-coupon prices
`exp(−∫_x^m i)` and the density `b(x, m) = B(x)e^{−ω(m−x)}`, the general market value is the
bundle value, `∫q b dj = Q(x)B(x)`. -/
theorem mktValue_geometric {i B : ℝ → ℝ} {ω x : ℝ} (hi : ContinuousOn i (Set.Ici x)) :
    mktValue (fun y m => disc i y m) (fun y m => B y * Real.exp (-(ω * (m - y)))) x =
      bondPrice i ω x * B x := by
  have h := integral_Ioi_shift (fun u => disc i x u * (B x * Real.exp (-(ω * (u - x))))) x
  rw [mktValue]
  rw [h, bondPrice_eq hi, ← integral_mul_const]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  ring

/-- Cochrane (2023), (3.34), geometric special case: with net sales of the bond due at `m` equal
to `(B' + ωB)e^{−ω(m−x)}` (`hasDerivAt_debtDensity`), the general flow (3.34)
`b(τ,τ) = Ps + ∫q ∂_x b dj` is the geometric flow `Q(B' + ωB) = B − Ps`. -/
theorem flow_general_geometric_iff {i B dB P s : ℝ → ℝ} {ω τ : ℝ}
    (hi : ContinuousOn i (Set.Ici τ)) :
    ((fun y m => B y * Real.exp (-(ω * (m - y)))) τ τ = P τ * s τ +
        issuanceValue (fun y m => disc i y m)
          (fun y m => (dB y + ω * B y) * Real.exp (-(ω * (m - y)))) τ) ↔
      bondPrice i ω τ * (dB τ + ω * B τ) = B τ - P τ * s τ := by
  have h : issuanceValue (fun y m => disc i y m)
      (fun y m => (dB y + ω * B y) * Real.exp (-(ω * (m - y)))) τ =
      bondPrice i ω τ * (dB τ + ω * B τ) :=
    mktValue_geometric (B := fun y => dB y + ω * B y) hi
  rw [h]
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
  constructor <;> intro h' <;> linarith

/-- Cochrane (2023), §3.6.2, finite-portfolio special case: if the debt density is a finite
combination `b(x, m) = Σ_k B_k(x)φ_k(m)` of fixed coupon schedules `φ_k` (bond `k` pays
`φ_k(m)` at `m`), the market value is `Σ_k Q_k(x)B_k(x)` with `Q_k(x) = ∫_0^∞ q(x,x+j)φ_k(x+j)dj`;
the same formula with `B_k'` gives the value of net sales. -/
theorem mktValue_finite {ι : Type*} (S : Finset ι) (q : ℝ → ℝ → ℝ) (Bk φ : ι → ℝ → ℝ) (x : ℝ)
    (hint : ∀ k ∈ S, IntegrableOn (fun j => q x (x + j) * φ k (x + j)) (Set.Ioi 0)) :
    mktValue q (fun y m => ∑ k ∈ S, Bk k y * φ k m) x =
      ∑ k ∈ S, (∫ j in Set.Ioi 0, q x (x + j) * φ k (x + j)) * Bk k x := by
  rw [mktValue]
  have he : (fun j => q x (x + j) * ∑ k ∈ S, Bk k x * φ k (x + j)) =
      fun j => ∑ k ∈ S, q x (x + j) * φ k (x + j) * Bk k x := by
    funext j
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [he, integral_finsetSum S (fun k hk => (hint k hk).mul_const _)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [integral_mul_const]

/-- Cochrane (2023), (3.34), finite-portfolio special case: with `b = Σ_k B_kφ_k` and net sales
`∂_x b = Σ_k B_k'φ_k`, the general flow (3.34) is the finite-portfolio flow
`Σ_k φ_k(τ)B_k(τ) = P s + Σ_k Q_k B_k'` of `hasDerivAt_value_portfolio` (coupon `c_k = φ_k`). -/
theorem flow_general_finite_iff {ι : Type*} (S : Finset ι) (q : ℝ → ℝ → ℝ)
    (Bk dBk φ : ι → ℝ → ℝ) (P s : ℝ → ℝ) (τ : ℝ)
    (hint : ∀ k ∈ S, IntegrableOn (fun j => q τ (τ + j) * φ k (τ + j)) (Set.Ioi 0)) :
    ((fun y m => ∑ k ∈ S, Bk k y * φ k m) τ τ = P τ * s τ +
        issuanceValue q (fun y m => ∑ k ∈ S, dBk k y * φ k m) τ) ↔
      ∑ k ∈ S, φ k τ * Bk k τ = P τ * s τ +
        ∑ k ∈ S, (∫ j in Set.Ioi 0, q τ (τ + j) * φ k (τ + j)) * dBk k τ := by
  have h := mktValue_finite S q dBk φ τ hint
  rw [show issuanceValue q (fun y m => ∑ k ∈ S, dBk k y * φ k m) τ =
    mktValue q (fun y m => ∑ k ∈ S, dBk k y * φ k m) τ from rfl, h]
  beta_reduce
  rw [Finset.sum_congr rfl (fun k _ => mul_comm (Bk k τ) (φ k τ))]

end Cochrane.Generality.ContinuousLong
