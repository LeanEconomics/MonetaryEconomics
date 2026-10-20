/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.KingForm
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Hyperinflations and central-bank destabilisation

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 16, §16.3 "What's wrong with
hyperinflations?" (pp. 368–369) and §16.4 "Central bank destabilization?" (pp. 369–370).

§16.3: "There is no violation of the consumer's transversality condition in a path
`π_t = φᵗ π_0`" — nominal explosions are equilibria once fiscal policy is passive — while the
fiscal theory's transversality condition rules out real explosions of `B_{t−1}/P_t`. To state
these claims precisely we use the explicit frictionless economy of the book (the nonlinear Fisher
equation (16.25), the flow condition and the valuation equation (16.26), with the passive surplus
rule `s_t = (r/(1+r)) B_{t−1}/P_t` of p. 379). This module is the canonical home of the §16.8
fiscal block: `LowerBound` uses `real_debt_flow_scalar`, `passive_real_debt_const_real`,
`pv_partial` and `zero_bound_iff_scalar` from here, and `Links` connects `LowerBound`'s
equilibrium and transversality results to the ones below. Nominal debt is indexed by the date
it is redeemed: `D_t = B_{t−1}`, and real debt is `b_t = D_t/P_t`. The transversality
condition is the explicit limit `(1+r)^{−T} b_T → 0`, and the valuation equation is a genuine
`HasSum`.

## Main results

* (16.30): `real_debt_flow_scalar`, `real_debt_flow` (`b_{t+1} = (1+r)(b_t − s_t)`, from the
  Fisher equation and the flow condition, exactly); `pv_partial` (the iterated flow).
* Passive fiscal policy: `passive_real_debt_const_real`, `passive_real_debt_const` (real debt
  is constant), `passive_tvc`,
  `passive_valuation` ((16.26) holds), `any_price_path_eqm` (EVERY positive price path, however
  explosive, is a full perfect-foresight equilibrium with the transversality condition),
  `zero_bound_iff_scalar`, `zero_bound_iff` (error E2: the bound is weak).
* The hyperinflation `π_t = φᵗ π_0` as an exact nonlinear path: `hyperP`, `hyper_log_inflation`,
  `hyper_linear_eqm` (it solves (16.4) with `u = 0`), `hyper_rule` (it obeys the exact rule
  `1 + i_t = (1+r) Π_t^φ`, (16.27)–(16.29) with `Φ(Π) = Π^φ`), `hyper_explodes` (the price level
  and inflation go to infinity), `hyperinflation_satisfies_tvc` (yet it is an equilibrium with
  the transversality condition and constant real debt).
* Under uncertainty: `stoch_real_debt_martingale`, `stoch_expected_real_debt`, `stoch_tvc`,
  `stoch_valuation` (with passive fiscal policy every equilibrium price process satisfies the
  expected-value transversality condition and (16.26)).
* The fiscal theory (active fiscal policy, exogenous surpluses): `ftpl_discounted_debt`,
  `ftpl_tvc_iff` (TVC iff `b_0 = PV`), `ftpl_real_explosion` (a too-low price level makes real
  debt explode), `ftpl_price_level_iff` (`P_0 = B_{−1}/PV`).
* §16.4: `stable_of_abs_lt_one`, `unstable_of_one_lt_abs` (with `φ < 1` expectations converge;
  with `φ > 1` the bank makes them diverge), `oscillating_of_lt_neg_one` and
  `determinate_of_lt_neg_one` (`φ < −1` also gives local determinacy, with oscillating
  explosions).
-/

namespace Cochrane.NewKeynesianSelection.Hyperinflation

open Filter Topology Innovation SimplestModel

/-! ### The nonlinear perfect-foresight economy -/

/-- Cochrane (2023), eqs. (16.25) and (16.28), pp. 377–378: the perfect-foresight Fisher equation
`1 + i_t = (1 + r) P_{t+1}/P_t`. -/
def FisherPF (r : ℝ) (P i : ℕ → ℝ) : Prop := ∀ t, 1 + i t = (1 + r) * (P (t + 1) / P t)

/-- Cochrane (2023), p. 379 (flow condition, "proceeds of new debt sales + taxes = old debt
redemption"): `B_t/(1 + i_t) + P_t s_t = B_{t−1}`, with `D_t = B_{t−1}`. -/
def Flow (P D i s : ℕ → ℝ) : Prop := ∀ t, D (t + 1) / (1 + i t) + P t * s t = D t

/-- Cochrane (2023), p. 379: the passive surplus rule `s_t = (r/(1+r)) B_{t−1}/P_t`. -/
def PassiveRule (r : ℝ) (P D s : ℕ → ℝ) : Prop := ∀ t, s t = r / (1 + r) * (D t / P t)

/-- Cochrane (2023), §16.3, p. 368 (the consumer's transversality condition, as in Chapter 2):
`(1 + r)^{−T} B_{T−1}/P_T → 0`. -/
def TVC (r : ℝ) (P D : ℕ → ℝ) : Prop :=
  Tendsto (fun T => (1 + r)⁻¹ ^ T * (D T / P T)) atTop (𝓝 0)

/-- Cochrane (2023), eq. (16.26), p. 377 (perfect foresight): the valuation equation
`B_{t−1}/P_t = ∑_{j ≥ 0} βʲ s_{t+j}`, `β = 1/(1+r)`, at every date, as a genuine sum. -/
def Valuation (r : ℝ) (P D s : ℕ → ℝ) : Prop :=
  ∀ t, HasSum (fun j => (1 + r)⁻¹ ^ j * s (t + j)) (D t / P t)

/-- Cochrane (2023), p. 379, eq. (16.30), one date at a time: from the flow condition
`B_t/(1 + i_t) + P_t s_t = B_{t−1}` and `1 + i_t = (1 + r)P_{t+1}/P_t`, real debt evolves as
`B_t/P_{t+1} = (1 + r)(B_{t−1}/P_t − s_t)`. Here `D = B_{t−1}`, `D' = B_t`. -/
theorem real_debt_flow_scalar {r i P P' D D' s : ℝ} (hr : 0 < 1 + r) (hP : 0 < P) (hP' : 0 < P')
    (hrate : 1 + i = (1 + r) * (P' / P)) (hflow : D' / (1 + i) + P * s = D) :
    D' / P' = (1 + r) * (D / P - s) := by
  have hi : 0 < 1 + i := by rw [hrate]; positivity
  have hD' : D' = (1 + i) * (D - P * s) := by
    field_simp at hflow
    linarith
  rw [hD', hrate]
  field_simp

/-- Cochrane (2023), eq. (16.30), p. 379: with the Fisher equation, the flow condition gives the
evolution of real debt, `B_t/P_{t+1} = (1 + r)(B_{t−1}/P_t − s_t)`. -/
theorem real_debt_flow {r : ℝ} (hr : 0 < 1 + r) {P D i s : ℕ → ℝ} (hP : ∀ t, 0 < P t)
    (hF : FisherPF r P i) (hflow : Flow P D i s) (t : ℕ) :
    D (t + 1) / P (t + 1) = (1 + r) * (D t / P t - s t) :=
  real_debt_flow_scalar hr (hP t) (hP (t + 1)) (hF t) (hflow t)

/-- Cochrane (2023), p. 379: under the passive rule `s_t = (r/(1+r)) B_{t−1}/P_t`, (16.30) gives
`B_t/P_{t+1} = B_{t−1}/P_t`: real debt `b_t` is constant. -/
theorem passive_real_debt_const_real {r : ℝ} {b s : ℕ → ℝ} (hr : 0 < 1 + r)
    (hflow : ∀ t, b (t + 1) = (1 + r) * (b t - s t)) (hrule : ∀ t, s t = r / (1 + r) * b t) :
    ∀ t, b t = b 0 := by
  intro t
  induction t with
  | zero => rfl
  | succ n ih =>
    rw [hflow, hrule, ← ih]
    field_simp
    ring

/-- Cochrane (2023), p. 379 ("then the real value of government debt is constant"): with the
passive rule, real debt is constant, `B_{t−1}/P_t = B_{−1}/P_0`. -/
theorem passive_real_debt_const {r : ℝ} (hr : 0 < 1 + r) {P D i s : ℕ → ℝ} (hP : ∀ t, 0 < P t)
    (hF : FisherPF r P i) (hflow : Flow P D i s) (hpas : PassiveRule r P D s) (t : ℕ) :
    D t / P t = D 0 / P 0 :=
  passive_real_debt_const_real (b := fun t => D t / P t) hr (real_debt_flow hr hP hF hflow) hpas t

/-- Cochrane (2023), p. 379 ("With constant real debt and the flow condition (16.30) the
transversality condition holds"): with `r > 0` and the passive rule the transversality condition
holds, for every price path. -/
theorem passive_tvc {r : ℝ} (hr : 0 < r) {P D i s : ℕ → ℝ} (hP : ∀ t, 0 < P t)
    (hF : FisherPF r P i) (hflow : Flow P D i s) (hpas : PassiveRule r P D s) : TVC r P D := by
  have h1 : 0 < 1 + r := by linarith
  have e : (fun T => (1 + r)⁻¹ ^ T * (D T / P T)) = fun T => (1 + r)⁻¹ ^ T * (D 0 / P 0) := by
    funext T
    rw [passive_real_debt_const h1 hP hF hflow hpas T]
  unfold TVC
  rw [e]
  have hβ0 : 0 ≤ (1 + r)⁻¹ := by positivity
  have hβ1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const (D 0 / P 0)

/-- Cochrane (2023), p. 379 ("and (16.30) implies (16.26)"): with `r > 0` and the passive rule the
valuation equation (16.26) holds at every date, for every price path. -/
theorem passive_valuation {r : ℝ} (hr : 0 < r) {P D i s : ℕ → ℝ} (hP : ∀ t, 0 < P t)
    (hF : FisherPF r P i) (hflow : Flow P D i s) (hpas : PassiveRule r P D s) :
    Valuation r P D s := by
  intro t
  have h1 : 0 < 1 + r := by linarith
  have hβ0 : 0 ≤ (1 + r)⁻¹ := by positivity
  have hβ1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hs : ∀ j, s (t + j) = r / (1 + r) * (D 0 / P 0) := fun j => by
    rw [hpas (t + j), passive_real_debt_const h1 hP hF hflow hpas (t + j)]
  have hg := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right (r / (1 + r) * (D 0 / P 0))
  have hv : (1 - (1 + r)⁻¹)⁻¹ * (r / (1 + r) * (D 0 / P 0)) = D t / P t := by
    rw [passive_real_debt_const h1 hP hF hflow hpas t]
    have hr0 := hr.ne'
    have hP0 := (hP 0).ne'
    field_simp
    rw [add_sub_cancel_left]
    field_simp
  rw [hv] at hg
  simpa only [hs] using hg

/-- Cochrane (2023), §16.3, p. 368 ("Economics does not rule out nominal explosions") and
p. 379 ("There are lots of ways the government can implement such a policy. We only need to
exhibit one"): for `r > 0`, EVERY positive price path `P` and every initial real debt `b_0` is a
full perfect-foresight equilibrium: with `B_{t−1} = b_0 P_t`, the Fisher rate
`1 + i_t = (1+r)P_{t+1}/P_t` and the passive surplus, the Fisher equation, the flow condition,
the passive rule, the transversality condition and the valuation equation (16.26) all hold. -/
theorem any_price_path_eqm {r : ℝ} (hr : 0 < r) {P : ℕ → ℝ} (hP : ∀ t, 0 < P t) (b0 : ℝ) :
    let D : ℕ → ℝ := fun t => b0 * P t
    let i : ℕ → ℝ := fun t => (1 + r) * (P (t + 1) / P t) - 1
    let s : ℕ → ℝ := fun _ => r / (1 + r) * b0
    FisherPF r P i ∧ Flow P D i s ∧ PassiveRule r P D s ∧ TVC r P D ∧ Valuation r P D s ∧
      ∀ t, D t / P t = b0 := by
  intro D i s
  have h1 : 0 < 1 + r := by linarith
  have hF : FisherPF r P i := fun t => by simp only [i]; ring
  have hD : ∀ t, D t / P t = b0 := fun t => by
    simp only [D]
    field_simp [(hP t).ne']
  have hflow : Flow P D i s := by
    intro t
    have hPt := (hP t).ne'
    have hPt1 := (hP (t + 1)).ne'
    simp only [D, i, s, add_sub_cancel]
    field_simp
  have hpas : PassiveRule r P D s := fun t => by simp only [s]; rw [hD t]
  exact ⟨hF, hflow, hpas, passive_tvc hr hP hF hflow hpas,
    passive_valuation hr hP hF hflow hpas, hD⟩

/-- Cochrane (2023), p. 379, corrected (error E2), one date at a time: under perfect foresight
(16.28) `Π_{t+1} = β(1 + i_t)` the zero bound `i_t ≥ 0` is equivalent to `Π_{t+1} ≥ β` (the book
writes "we cannot have `Π_{t+1} ≤ β`"; the bound is weak). -/
theorem zero_bound_iff_scalar {r i Pi1 : ℝ} (hr : 0 < 1 + r) (h : Pi1 = (1 + r)⁻¹ * (1 + i)) :
    0 ≤ i ↔ (1 + r)⁻¹ ≤ Pi1 := by
  rw [h]
  constructor
  · intro hi
    have := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ 1 + i)
      (inv_nonneg.mpr hr.le)
    simpa using this
  · intro hle
    have h2 : (1 + r)⁻¹ * 1 ≤ (1 + r)⁻¹ * (1 + i) := by simpa using hle
    have := le_of_mul_le_mul_left h2 (inv_pos.mpr hr)
    linarith

/-- Cochrane (2023), p. 379 ("the bound `i ≥ 0` means we cannot have `Π_{t+1} < β`"): in the
perfect-foresight equilibrium the nominal rate is nonnegative iff gross inflation is at least
`β = 1/(1+r)`. -/
theorem zero_bound_iff {r : ℝ} (hr : 0 < 1 + r) {P i : ℕ → ℝ} (hF : FisherPF r P i) (t : ℕ) :
    0 ≤ i t ↔ (1 + r)⁻¹ ≤ P (t + 1) / P t :=
  zero_bound_iff_scalar hr (by rw [hF t, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul])

/-! ### The hyperinflation `π_t = φᵗ π_0` -/

/-- Cochrane (2023), §16.3, p. 368 (the path `π_t = φᵗ π_0`): the price level with log inflation
`π_t = φᵗ π_0`, `P_{t+1} = P_t exp(φ^{t+1} π_0)`. -/
noncomputable def hyperP (P0 φ π0 : ℝ) : ℕ → ℝ
  | 0 => P0
  | t + 1 => hyperP P0 φ π0 t * Real.exp (φ ^ (t + 1) * π0)

/-- Cochrane (2023), §16.3, p. 368: the hyperinflation price level is positive. -/
theorem hyperP_pos {P0 : ℝ} (hP0 : 0 < P0) (φ π0 : ℝ) (t : ℕ) : 0 < hyperP P0 φ π0 t := by
  induction t with
  | zero => exact hP0
  | succ t ih => exact mul_pos ih (Real.exp_pos _)

/-- Cochrane (2023), §16.3, p. 368: log inflation along the path is
`log(P_{t+1}/P_t) = φ^{t+1} π_0 = φ · φᵗ π_0`. -/
theorem hyper_log_inflation {P0 : ℝ} (hP0 : 0 < P0) (φ π0 : ℝ) (t : ℕ) :
    Real.log (hyperP P0 φ π0 (t + 1) / hyperP P0 φ π0 t) = φ * (φ ^ t * π0) := by
  have h := (hyperP_pos hP0 φ π0 t).ne'
  change Real.log (hyperP P0 φ π0 t * Real.exp (φ ^ (t + 1) * π0) / hyperP P0 φ π0 t) = _
  rw [mul_div_cancel_left₀ _ h, Real.log_exp, pow_succ]
  ring

/-- Cochrane (2023), §16.3, p. 368 and (16.4), p. 364: the log-inflation path `π_t = φᵗ π_0` is
an equilibrium of the linear model (16.4) with `u = 0` (under perfect foresight). -/
theorem hyper_linear_eqm (φ π0 : ℝ) :
    Eq164 perfectForesight φ 0 (fun t _ => φ ^ t * π0) := by
  intro t
  funext ω
  change φ ^ (t + 1) * π0 = φ * (φ ^ t * π0) + 0
  rw [pow_succ]
  ring

/-- Cochrane (2023), eqs. (16.27)–(16.29), p. 378, with `Φ(Π) = Π^φ` (the exact nonlinear form of
`i_t = φ π_t` in logs): along the path, gross inflation `Π_t = exp(φᵗ π_0)` obeys
`Π_{t+1} = Φ(Π_t) = Π_t^φ`, and with the Fisher equation the rate obeys the rule
`1 + i_t = (1 + r) Π_t^φ`. -/
theorem hyper_rule {P0 : ℝ} (hP0 : 0 < P0) (r φ π0 : ℝ) {i : ℕ → ℝ}
    (hF : FisherPF r (hyperP P0 φ π0) i) (t : ℕ) :
    hyperP P0 φ π0 (t + 1) / hyperP P0 φ π0 t = Real.exp (φ ^ t * π0) ^ φ ∧
      1 + i t = (1 + r) * Real.exp (φ ^ t * π0) ^ φ := by
  have hd : hyperP P0 φ π0 (t + 1) / hyperP P0 φ π0 t = Real.exp (φ ^ t * π0) ^ φ := by
    have h := (hyperP_pos hP0 φ π0 t).ne'
    change hyperP P0 φ π0 t * Real.exp (φ ^ (t + 1) * π0) / hyperP P0 φ π0 t = _
    rw [mul_div_cancel_left₀ _ h, ← Real.exp_mul, pow_succ]
    ring_nf
  exact ⟨hd, by rw [hF t, hd]⟩

/-- Cochrane (2023), §16.3, p. 368 (a nominal explosion): for `φ > 1` and `π_0 > 0`, the price
level and gross inflation both go to infinity. -/
theorem hyper_explodes {P0 φ π0 : ℝ} (hP0 : 0 < P0) (hφ : 1 < φ) (hπ0 : 0 < π0) :
    Tendsto (hyperP P0 φ π0) atTop atTop ∧
      Tendsto (fun t => hyperP P0 φ π0 (t + 1) / hyperP P0 φ π0 t) atTop atTop := by
  have hlow : ∀ t : ℕ, P0 * (1 + t * π0) ≤ hyperP P0 φ π0 t := by
    intro t
    induction t with
    | zero => simp [hyperP]
    | succ t ih =>
      rw [Nat.cast_succ]
      change P0 * (1 + ((t : ℝ) + 1) * π0) ≤ hyperP P0 φ π0 t * Real.exp (φ ^ (t + 1) * π0)
      have hp : 1 ≤ φ ^ (t + 1) := one_le_pow₀ hφ.le
      have he : 1 + π0 ≤ Real.exp (φ ^ (t + 1) * π0) := by
        have := Real.add_one_le_exp (φ ^ (t + 1) * π0)
        nlinarith
      have hpos : 0 ≤ P0 * (1 + t * π0) := by positivity
      calc P0 * (1 + ((t : ℝ) + 1) * π0) ≤ P0 * (1 + t * π0) * (1 + π0) := by
            nlinarith [mul_pos hP0 (mul_pos hπ0 hπ0), Nat.cast_nonneg (α := ℝ) t]
        _ ≤ hyperP P0 φ π0 t * Real.exp (φ ^ (t + 1) * π0) :=
            mul_le_mul ih he (by linarith) (hyperP_pos hP0 φ π0 t).le
  refine ⟨tendsto_atTop_mono hlow ?_, ?_⟩
  · refine Tendsto.const_mul_atTop hP0 (tendsto_atTop_add_const_left _ 1 ?_)
    exact Tendsto.atTop_mul_const hπ0 tendsto_natCast_atTop_atTop
  · have e : (fun t => hyperP P0 φ π0 (t + 1) / hyperP P0 φ π0 t) =
        fun t => Real.exp (φ ^ (t + 1) * π0) := by
      funext t
      change hyperP P0 φ π0 t * Real.exp (φ ^ (t + 1) * π0) / hyperP P0 φ π0 t = _
      rw [mul_div_cancel_left₀ _ (hyperP_pos hP0 φ π0 t).ne']
    rw [e]
    exact Real.tendsto_exp_atTop.comp
      (((tendsto_pow_atTop_atTop_of_one_lt hφ).comp (tendsto_add_atTop_nat 1)).atTop_mul_const hπ0)

/-- Cochrane (2023), §16.3, p. 368 ("There is no violation of the consumer's transversality
condition in a path `π_t = φᵗ π_0`"): for `r > 0`, `φ > 1`, `π_0 > 0` and any initial real debt
`b_0`, the hyperinflation path is a full perfect-foresight equilibrium under the passive surplus
rule: the Fisher equation, the flow condition, the transversality condition and the valuation
equation (16.26) hold, the rate obeys the exact rule `1 + i_t = (1+r) Π_t^φ`, real debt stays at
`b_0`, and yet the price level explodes. -/
theorem hyperinflation_satisfies_tvc {r P0 φ π0 : ℝ} (hr : 0 < r) (hP0 : 0 < P0) (hφ : 1 < φ)
    (hπ0 : 0 < π0) (b0 : ℝ) :
    ∃ D i s : ℕ → ℝ, FisherPF r (hyperP P0 φ π0) i ∧ Flow (hyperP P0 φ π0) D i s ∧
      PassiveRule r (hyperP P0 φ π0) D s ∧ TVC r (hyperP P0 φ π0) D ∧
      Valuation r (hyperP P0 φ π0) D s ∧ (∀ t, D t / hyperP P0 φ π0 t = b0) ∧
      (∀ t, 1 + i t = (1 + r) * Real.exp (φ ^ t * π0) ^ φ) ∧
      Tendsto (hyperP P0 φ π0) atTop atTop := by
  obtain ⟨hF, hfl, hpas, htvc, hval, hD⟩ := any_price_path_eqm hr (hyperP_pos hP0 φ π0) b0
  exact ⟨_, _, _, hF, hfl, hpas, htvc, hval, hD, fun t => (hyper_rule hP0 r φ π0 hF t).2,
    (hyper_explodes hP0 hφ hπ0).1⟩

/-! ### Under uncertainty -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), eq. (16.25), p. 377: the Fisher equation under uncertainty,
`1/(1 + i_t) = β E_t(P_t/P_{t+1})`, `β = 1/(1+r)`. -/
def FisherE (r : ℝ) (P i : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, 1 / (1 + i t ω) = (1 + r)⁻¹ * 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω

/-- Cochrane (2023), p. 379: the flow condition `B_t/(1 + i_t) + P_t s_t = B_{t−1}` in every
state (`D_t = B_{t−1}`). -/
def FlowE (P D i s : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, D (t + 1) ω / (1 + i t ω) + P t ω * s t ω = D t ω

/-- Cochrane (2023), p. 379: real debt `b_t = B_{t−1}/P_t`. -/
noncomputable def realDebt (P D : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t ω => D t ω / P t ω

/-- Cochrane (2023), p. 379, under uncertainty: with the passive rule
`s_t = (r/(1+r)) B_{t−1}/P_t`, real debt is a martingale, `E_t b_{t+1} = b_t`. Hypotheses: the
pull-out property, positive prices, `B_t/P_t` known at `t` (debt is chosen at `t`). -/
theorem stoch_real_debt_martingale (hPO : 𝔼.PullOut) {r : ℝ} (hr : 0 < 1 + r)
    {P D i s : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (hk : ∀ t, 𝔼.E t (fun ω => D (t + 1) ω / P t ω) = fun ω => D (t + 1) ω / P t ω)
    (hF : FisherE 𝔼 r P i) (hflow : FlowE P D i s)
    (hpas : ∀ t ω, s t ω = r / (1 + r) * (D t ω / P t ω)) (t : ℕ) :
    𝔼.E t (realDebt P D (t + 1)) = realDebt P D t := by
  have hsplit : realDebt P D (t + 1) =
      (fun ω => D (t + 1) ω / P t ω) * fun ω => P t ω / P (t + 1) ω := by
    funext ω
    have h1 := (hP t ω).ne'
    have h2 := (hP (t + 1) ω).ne'
    simp only [realDebt, Pi.mul_apply]
    field_simp
  rw [hsplit, hPO t _ _ (hk t)]
  funext ω
  have h1 := (hP t ω).ne'
  have hr' := hr.ne'
  have hi' := hi t ω
  have hE : 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω = (1 + r) / (1 + i t ω) := by
    have := hF t ω
    field_simp at this ⊢
    linarith
  have hfl := hflow t ω
  rw [hpas t ω] at hfl
  simp only [Pi.mul_apply, realDebt]
  rw [hE]
  field_simp at hfl ⊢
  linear_combination hfl

/-- Cochrane (2023), p. 379, under uncertainty: with passive fiscal policy expected real debt is
constant at every horizon, `E_t b_{t+j} = b_t` (real debt adapted). -/
theorem stoch_expected_real_debt (hPO : 𝔼.PullOut) {r : ℝ} (hr : 0 < 1 + r)
    {P D i s : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (hk : ∀ t, 𝔼.E t (fun ω => D (t + 1) ω / P t ω) = fun ω => D (t + 1) ω / P t ω)
    (hb : 𝔼.Adapted (realDebt P D)) (hF : FisherE 𝔼 r P i) (hflow : FlowE P D i s)
    (hpas : ∀ t ω, s t ω = r / (1 + r) * (D t ω / P t ω)) (t j : ℕ) :
    𝔼.E t (realDebt P D (t + j)) = realDebt P D t := by
  induction j with
  | zero => exact hb t
  | succ j ih =>
    rw [← add_assoc, ← 𝔼.tower (Nat.le_add_right t j),
      stoch_real_debt_martingale 𝔼 hPO hr hP hi hk hF hflow hpas (t + j), ih]

/-- Cochrane (2023), §16.3, p. 368, under uncertainty: with `r > 0` and passive fiscal policy,
every equilibrium price process satisfies the transversality condition
`β^T E_t b_{t+T} → 0`, however explosive the price level. -/
theorem stoch_tvc (hPO : 𝔼.PullOut) {r : ℝ} (hr : 0 < r)
    {P D i s : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (hk : ∀ t, 𝔼.E t (fun ω => D (t + 1) ω / P t ω) = fun ω => D (t + 1) ω / P t ω)
    (hb : 𝔼.Adapted (realDebt P D)) (hF : FisherE 𝔼 r P i) (hflow : FlowE P D i s)
    (hpas : ∀ t ω, s t ω = r / (1 + r) * (D t ω / P t ω)) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => (1 + r)⁻¹ ^ T * 𝔼.E t (realDebt P D (t + T)) ω) atTop (𝓝 0) := by
  have h1 : 0 < 1 + r := by linarith
  have e : (fun T => (1 + r)⁻¹ ^ T * 𝔼.E t (realDebt P D (t + T)) ω) =
      fun T => (1 + r)⁻¹ ^ T * realDebt P D t ω := by
    funext T
    rw [stoch_expected_real_debt 𝔼 hPO h1 hP hi hk hb hF hflow hpas t T]
  rw [e]
  have hβ0 : 0 ≤ (1 + r)⁻¹ := by positivity
  have hβ1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const (realDebt P D t ω)

/-- Cochrane (2023), eq. (16.26), p. 377, under uncertainty: with `r > 0` and passive fiscal
policy, every equilibrium satisfies the valuation equation
`B_{t−1}/P_t = ∑_{j ≥ 0} βʲ E_t s_{t+j}`, as a genuine sum. -/
theorem stoch_valuation (hPO : 𝔼.PullOut) {r : ℝ} (hr : 0 < r)
    {P D i s : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (hk : ∀ t, 𝔼.E t (fun ω => D (t + 1) ω / P t ω) = fun ω => D (t + 1) ω / P t ω)
    (hb : 𝔼.Adapted (realDebt P D)) (hF : FisherE 𝔼 r P i) (hflow : FlowE P D i s)
    (hpas : ∀ t ω, s t ω = r / (1 + r) * (D t ω / P t ω)) (t : ℕ) (ω : Ω) :
    HasSum (fun j => (1 + r)⁻¹ ^ j * 𝔼.E t (s (t + j)) ω) (realDebt P D t ω) := by
  have h1 : 0 < 1 + r := by linarith
  have hβ0 : 0 ≤ (1 + r)⁻¹ := by positivity
  have hβ1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hs : ∀ j, 𝔼.E t (s (t + j)) ω = r / (1 + r) * realDebt P D t ω := by
    intro j
    have e : s (t + j) = (r / (1 + r)) • realDebt P D (t + j) := by
      funext ω'
      rw [hpas (t + j) ω']
      rfl
    rw [e, map_smul, stoch_expected_real_debt 𝔼 hPO h1 hP hi hk hb hF hflow hpas t j]
    rfl
  have hg := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right (r / (1 + r) * realDebt P D t ω)
  have hv : (1 - (1 + r)⁻¹)⁻¹ * (r / (1 + r) * realDebt P D t ω) = realDebt P D t ω := by
    have hr0 := hr.ne'
    have h1' := h1.ne'
    field_simp
    rw [add_sub_cancel_left]
    field_simp
  rw [hv] at hg
  simpa only [hs] using hg

/-! ### The fiscal theory: real explosions violate the transversality condition -/

/-- Cochrane (2023), eq. (16.30), p. 379, with an exogenous surplus sequence (active fiscal
policy): `b_{t+1} = (1 + r)(b_t − s_t)` for real debt `b_t = B_{t−1}/P_t`. -/
def RealDebtFlow (r : ℝ) (b s : ℕ → ℝ) : Prop := ∀ t, b (t + 1) = (1 + r) * (b t - s t)

/-- Cochrane (2023), (16.30) ⇒ (16.26), p. 379: iterating the real flow
`b_{t+1} = (1 + r)(b_t − s_t)` gives `b_t = Σ_{j<T} βʲ s_{t+j} + βᵀ b_{t+T}`, `β = (1 + r)⁻¹`. -/
theorem pv_partial {r : ℝ} {b s : ℕ → ℝ} (hr : 0 < 1 + r)
    (hflow : ∀ t, b (t + 1) = (1 + r) * (b t - s t)) (t T : ℕ) :
    b t = ∑ j ∈ Finset.range T, (1 + r)⁻¹ ^ j * s (t + j) + (1 + r)⁻¹ ^ T * b (t + T) := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [ih, Finset.sum_range_succ, ← add_assoc t n 1, hflow (t + n), pow_succ]
    field_simp
    ring

/-- Cochrane (2023), eq. (16.30), p. 379, iterated: `β^T b_T = b_0 − ∑_{j<T} βʲ s_j`. -/
theorem ftpl_discounted_debt {r : ℝ} (hr : 0 < 1 + r) {b s : ℕ → ℝ} (h : RealDebtFlow r b s)
    (T : ℕ) : (1 + r)⁻¹ ^ T * b T = b 0 - ∑ j ∈ Finset.range T, (1 + r)⁻¹ ^ j * s j := by
  have := pv_partial hr h 0 T
  simp only [zero_add] at this
  linarith

/-- Cochrane (2023), §16.3, p. 369 ("The transversality condition rules out real explosions,
explosions of `B_{t−1}/P_t`"): with `r > 0`, bounded exogenous surpluses and (16.30), the
transversality condition `β^T b_T → 0` holds iff real debt equals the present value of
surpluses, `b_0 = ∑ βʲ s_j`. -/
theorem ftpl_tvc_iff {r M : ℝ} (hr : 0 < r) {b s : ℕ → ℝ} (hs : ∀ t, |s t| ≤ M)
    (h : RealDebtFlow r b s) :
    Tendsto (fun T => (1 + r)⁻¹ ^ T * b T) atTop (𝓝 0) ↔
      b 0 = ∑' j, (1 + r)⁻¹ ^ j * s j := by
  have h1 : 0 < 1 + r := by linarith
  have hβ0 : 0 ≤ (1 + r)⁻¹ := by positivity
  have hβ1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hsum : Summable (fun j => (1 + r)⁻¹ ^ j * s j) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right M)
      (fun j => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (hs j) (pow_nonneg hβ0 j)
  have hlim : Tendsto (fun T => (1 + r)⁻¹ ^ T * b T) atTop
      (𝓝 (b 0 - ∑' j, (1 + r)⁻¹ ^ j * s j)) := by
    have e : (fun T => (1 + r)⁻¹ ^ T * b T) =
        fun T => b 0 - ∑ j ∈ Finset.range T, (1 + r)⁻¹ ^ j * s j := by
      funext T
      exact ftpl_discounted_debt h1 h T
    rw [e]
    exact hsum.hasSum.tendsto_sum_nat.const_sub (b 0)
  constructor
  · intro h0
    have := tendsto_nhds_unique hlim h0
    linarith
  · intro h0
    rw [h0, sub_self] at hlim
    exact hlim

/-- Cochrane (2023), §16.3, p. 369 ("If the price level is too low, nominal government bonds
appear as net wealth"): with `r > 0` and bounded exogenous surpluses, real debt above the present
value of surpluses explodes, `b_T → ∞` (a real explosion). -/
theorem ftpl_real_explosion {r M : ℝ} (hr : 0 < r) {b s : ℕ → ℝ} (hs : ∀ t, |s t| ≤ M)
    (h : RealDebtFlow r b s) (hb : ∑' j, (1 + r)⁻¹ ^ j * s j < b 0) :
    Tendsto b atTop atTop := by
  have h1 : 0 < 1 + r := by linarith
  have hβ0 : 0 ≤ (1 + r)⁻¹ := by positivity
  have hβ1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hsum : Summable (fun j => (1 + r)⁻¹ ^ j * s j) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right M)
      (fun j => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (hs j) (pow_nonneg hβ0 j)
  have hlim : Tendsto (fun T => (1 + r)⁻¹ ^ T * b T) atTop
      (𝓝 (b 0 - ∑' j, (1 + r)⁻¹ ^ j * s j)) := by
    have e : (fun T => (1 + r)⁻¹ ^ T * b T) =
        fun T => b 0 - ∑ j ∈ Finset.range T, (1 + r)⁻¹ ^ j * s j := by
      funext T
      exact ftpl_discounted_debt h1 h T
    rw [e]
    exact hsum.hasSum.tendsto_sum_nat.const_sub (b 0)
  have hpow : Tendsto (fun T : ℕ => (1 + r) ^ T) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by linarith)
  have e : b = fun T => (1 + r) ^ T * ((1 + r)⁻¹ ^ T * b T) := by
    funext T
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ h1.ne', one_pow, one_mul]
  rw [e]
  exact hpow.atTop_mul_pos (sub_pos.mpr hb) hlim

/-- Cochrane (2023), §16.3, p. 369, and Chapter 2: with outstanding nominal debt `B_{−1} > 0`, a
positive present value of surpluses and `b_0 = B_{−1}/P_0`, the transversality condition holds
iff `P_0 = B_{−1}/PV`; a lower price level makes real debt explode. -/
theorem ftpl_price_level_iff {r M Bm P0 : ℝ} (hr : 0 < r) (hBm : 0 < Bm) (hP0 : 0 < P0)
    {b s : ℕ → ℝ} (hs : ∀ t, |s t| ≤ M) (h : RealDebtFlow r b s) (hb0 : b 0 = Bm / P0)
    (hpv : 0 < ∑' j, (1 + r)⁻¹ ^ j * s j) :
    (Tendsto (fun T => (1 + r)⁻¹ ^ T * b T) atTop (𝓝 0) ↔
      P0 = Bm / ∑' j, (1 + r)⁻¹ ^ j * s j) ∧
      (P0 < Bm / ∑' j, (1 + r)⁻¹ ^ j * s j → Tendsto b atTop atTop) := by
  rw [ftpl_tvc_iff hr hs h, hb0]
  refine ⟨?_, fun hlow => ftpl_real_explosion hr hs h ?_⟩
  · constructor
    · intro e
      rw [← e, div_div_cancel₀ hBm.ne']
    · intro e
      rw [e, div_div_cancel₀ hBm.ne']
  · rw [hb0, lt_div_iff₀ hP0]
    rwa [lt_div_iff₀ hpv, mul_comm] at hlow

/-! ### §16.4: central-bank destabilisation -/

/-- Cochrane (2023), §16.4, p. 369 (`E_t π_{t+1} = φ π_t`, no disturbance): in every equilibrium
`E_t π_{t+j} = φʲ π_t`. -/
theorem expected_path {φ : ℝ} {π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (h : Eq164 𝔼 φ 0 π)
    (t j : ℕ) : 𝔼.E t (π (t + j)) = φ ^ j • π t := by
  have h0 : Eq164 𝔼 φ 0 (0 : ℕ → Ω → ℝ) := fun t => by simp
  have := sunspot_expected 𝔼 (π := 0) (π' := π) (fun t => by simp) hπ h0 h t j
  simpa using this

/-- Cochrane (2023), §16.4, p. 369 ("with `φ < 1`, this economy is stable"): for `|φ| < 1`
expected inflation converges to zero from any initial value. -/
theorem stable_of_abs_lt_one {φ : ℝ} (hφ : |φ| < 1) {π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (h : Eq164 𝔼 φ 0 π) (t : ℕ) (ω : Ω) :
    Tendsto (fun j => 𝔼.E t (π (t + j)) ω) atTop (𝓝 0) := by
  have e : (fun j => 𝔼.E t (π (t + j)) ω) = fun j => φ ^ j * π t ω := by
    funext j
    rw [expected_path 𝔼 hπ h t j, Pi.smul_apply, smul_eq_mul]
  rw [e]
  simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hφ).mul_const (π t ω)

/-- Cochrane (2023), §16.4, p. 369 ("The central bank deliberately makes the economy unstable by
following `φ > 1`"): for `|φ| > 1`, wherever inflation is nonzero expected inflation diverges,
`|E_t π_{t+j}| → ∞`. -/
theorem unstable_of_one_lt_abs {φ : ℝ} (hφ : 1 < |φ|) {π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (h : Eq164 𝔼 φ 0 π) {t : ℕ} {ω : Ω} (hω : π t ω ≠ 0) :
    Tendsto (fun j => |𝔼.E t (π (t + j)) ω|) atTop atTop := by
  have e : (fun j => |𝔼.E t (π (t + j)) ω|) = fun j => |φ| ^ j * |π t ω| := by
    funext j
    rw [expected_path 𝔼 hπ h t j, Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
  rw [e]
  exact (tendsto_pow_atTop_atTop_of_one_lt hφ).atTop_mul_const (abs_pos.mpr hω)

/-- Cochrane (2023), §16.4, p. 370 ("oscillating inflation and deflation are even ghastlier"):
for `φ < −1`, every equilibrium with `π_t > 0` is expected to alternate in sign,
`E_t π_{t+2j} > 0 > E_t π_{t+2j+1}`, with exploding magnitude. -/
theorem oscillating_of_lt_neg_one {φ : ℝ} (hφ : φ < -1) {π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (h : Eq164 𝔼 φ 0 π) {t : ℕ} {ω : Ω} (hω : 0 < π t ω) :
    (∀ j, 0 < 𝔼.E t (π (t + 2 * j)) ω ∧ 𝔼.E t (π (t + (2 * j + 1))) ω < 0) ∧
      Tendsto (fun j => |𝔼.E t (π (t + j)) ω|) atTop atTop := by
  have habs : 1 < |φ| := by
    rw [abs_of_neg (by linarith)]
    linarith
  refine ⟨fun j => ?_, unstable_of_one_lt_abs 𝔼 habs hπ h hω.ne'⟩
  rw [expected_path 𝔼 hπ h t, expected_path 𝔼 hπ h t]
  simp only [Pi.smul_apply, smul_eq_mul]
  have h2 : 0 < φ ^ (2 * j) := by
    rw [pow_mul]
    exact pow_pos (by nlinarith) j
  constructor
  · exact mul_pos h2 hω
  · rw [pow_succ]
    have : φ ^ (2 * j) * φ < 0 := mul_neg_of_pos_of_neg h2 (by linarith)
    exact mul_neg_of_neg_of_pos this hω

/-- Cochrane (2023), §16.4, p. 370 ("In this model `φ < −1` is as good as `φ > 1` to produce local
determinacy"): for `φ < −1`, (16.4) has exactly one bounded equilibrium for every bounded adapted
disturbance. -/
theorem determinate_of_lt_neg_one [Nonempty Ω] {φ : ℝ} (hφ : φ < -1) :
    ∀ u : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u → ∃! π, BoundedProc π ∧ Eq164 𝔼 φ u π := by
  refine (determinate_iff 𝔼 φ).mpr ?_
  rw [abs_of_neg (by linarith)]
  linarith

end Cochrane.NewKeynesianSelection.Hyperinflation
