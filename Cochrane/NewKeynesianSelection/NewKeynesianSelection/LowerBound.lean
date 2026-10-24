/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.Expectations
import NewKeynesianSelection.GlobalDynamics
import NewKeynesianSelection.Hyperinflation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# A full nonlinear model and the lower bound

Cochrane (2023), Chapter 16, §16.8, pp. 377–380.

The frictionless model with the nonlinear Fisher equation (16.25) and the government debt
valuation equation (16.26); the interest-rate rule (16.27) `1 + i_t = (1 + r)Φ(Π_t)`; perfect
foresight (16.28) `Π_{t+1} = β(1 + i_t)`, `β = 1/(1+r)`; hence the inflation dynamics (16.29)
`Π_{t+1} = Φ(Π_t)` of Figure 16.2.

## Main results

* (16.25): `bondPricing_perfectForesight_iff` (the general bond-pricing equation for an arbitrary
  `ExpectationSystem` reduces to (16.28) under perfect foresight), `fisher_pf_iff`.
* Linearisation, exact: `hasDerivAt_log_bondPricing` — under any `ExpectationSystem`, the
  derivative of `log(1 + i_t)` with respect to the scale `ε` of log inflation `επ_{t+1}` at the
  zero-inflation steady state is `E_t π_{t+1}`, which is (16.1); `gateaux_log_bondPricing` (the
  same Gateaux derivative at any steady state `π*`, along every bounded direction, with
  `E_exp_pos`); `log_fisher_pf` (exact log
  Fisher equation); `hasDerivAt_log_rule` (the slope of the rule (16.27) in logs at `Π*` is
  `Φ′(Π*)`, so the linearised Taylor coefficient is `φ = Φ′(Π*)`).
* (16.27)–(16.29): `dynamics_iff`, `eq_orbit`.
* p. 378: `target_unique_locally_bounded` (with `Φ′(Π*) > 1`, `Π*` is the unique locally bounded
  equilibrium), `target_repelling`.
* p. 379, the zero bound: `Hyperinflation.zero_bound_iff_scalar` (`i ≥ 0 ⇔ Π_{t+1} ≥ β`,
  error E2: `Π_{t+1} = β` is allowed), `zero_bound_eq_iff`, `rule_respects_bound_iff`.
* p. 379, Π_L, corrected (E2): `lower_steady_state` (existence of a largest fixed point
  `Π_L ∈ [β, Π*)` with `Φ < id` on `(Π_L, Π*)` and `Φ′(Π_L) ≤ 1`); counterexample to
  `Φ′(Π_L) < 1` (`phiTan`, `e2_tangency_counterexample`, orbits from `(1, 2)` still converge,
  `phiTan_deflation_tendsto`, but `Π_L` is not two-sided stable, `phiTan_left_unstable`);
  continuity is needed (`phiJump`, `e2_discontinuous_counterexample`).
* pp. 379–380: deflations "trundle down gently" to Π_L (`deflation_tendsto_lower`,
  `deflation_strictAnti`); local indeterminacy near Π_L when `|Φ′(Π_L)| < 1`
  (`lower_locally_indeterminate`).
* p. 379, fiscal policy: (16.30) and the passive rule ⇒ constant real debt are the canonical
  `Hyperinflation.real_debt_flow_scalar`, `Hyperinflation.passive_real_debt_const_real` and
  `Hyperinflation.pv_partial` (§16.3 restates the §16.8 fiscal block); valuation (16.26) ⇔
  transversality given the flow
  (`valuation_of_tvc`, `tvc_of_valuation`, `valuation_iff_tvc`); the general passive rule
  `s_t = γB_{t−1}/P_t` satisfies the TVC for all debt iff `0 < γ < 2`
  (`passive_gamma_tvc_iff`, `passive_coefficient_mem`); the full equilibrium
  definition `IsEquilibrium`, its dynamics `equilibrium_dynamics`, and existence of an
  equilibrium for every initial inflation (`equilibrium_exists`, `continuum_of_equilibria`),
  including the deflations converging to Π_L (`deflationary_equilibria`).
* p. 379, the 2%/1% example: the truncated linear rule `truncRule`; `truncRule_orbit_gap`,
  `truncRule_hits_bound` (paths below `Π*` reach `i = 0` in finite time and stay);
  `example_two_one` (`Π* = 1.02`, `r = 1%`, start `1.0199`, inflation `β − 1 = −1/101`);
  `negative_real_rate_example` (p. 380: `r = −1%` puts `Π_L` near `1%`).
-/

namespace Cochrane.NewKeynesianSelection.LowerBound

open Filter Topology
open Cochrane.NewKeynesianSelection.GlobalDynamics

/-! ## (16.25): the nonlinear Fisher equation -/

/-- Cochrane (2023), eq. (16.25), p. 377: the bond-pricing (nonlinear Fisher) equation
`1/(1 + i_t) = (1 + r)⁻¹ E_t(1/Π_{t+1})` for an arbitrary expectation system (gross inflation
`Π_{t+1} = P_{t+1}/P_t`). -/
def BondPricing {Ω : Type*} (𝔼 : ExpectationSystem Ω) (r : ℝ) (i infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (fun ω => 1 / (1 + i t ω)) = (1 + r)⁻¹ • 𝔼.E t (fun ω => 1 / infl (t + 1) ω)

/-- Cochrane (2023), eqs. (16.25) and (16.28), p. 378: under perfect foresight the bond-pricing
equation is `Π_{t+1} = β(1 + i_t)` with `β = 1/(1 + r)` (given `1 + i_t > 0`, `Π_{t+1} > 0`). -/
theorem bondPricing_perfectForesight_iff {r : ℝ} {i infl : ℕ → Unit → ℝ} (hr : 0 < 1 + r)
    (hi : ∀ t, 0 < 1 + i t ()) (hP : ∀ t, 0 < infl (t + 1) ()) :
    BondPricing perfectForesight r i infl ↔ ∀ t, infl (t + 1) () = (1 + r)⁻¹ * (1 + i t ()) := by
  refine forall_congr' fun t => ?_
  have h1 := hi t
  have h2 := hP t
  constructor
  · intro h
    have h' := congrFun h ()
    simp only [perfectForesight, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul] at h'
    field_simp at h'
    rw [eq_inv_mul_iff_mul_eq₀ hr.ne']
    linarith
  · intro h
    funext ω
    simp only [perfectForesight, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [h]
    field_simp

/-- Cochrane (2023), eq. (16.25), p. 377, perfect foresight with price levels:
`1/(1 + i_t) = β P_t/P_{t+1}` if and only if `P_{t+1}/P_t = β(1 + i_t)`, `β = (1 + r)⁻¹`. -/
theorem fisher_pf_iff {r i P P' : ℝ} (hr : 0 < 1 + r) (hi : 0 < 1 + i) (hP : 0 < P)
    (hP' : 0 < P') : 1 / (1 + i) = (1 + r)⁻¹ * (P / P') ↔ P' / P = (1 + r)⁻¹ * (1 + i) := by
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    field_simp at h ⊢
    linarith

/-- Cochrane (2023), (16.25) ⇒ (16.1), pp. 377–378, exact in logs: under perfect foresight
`log(1 + i_t) = log(1 + r) + log Π_{t+1}`, i.e. `i = r + π` with log rates. -/
theorem log_fisher_pf {r i Pi1 : ℝ} (hr : 0 < 1 + r) (hi : 0 < 1 + i)
    (h : Pi1 = (1 + r)⁻¹ * (1 + i)) : Real.log (1 + i) = Real.log (1 + r) + Real.log Pi1 := by
  rw [h, Real.log_mul (inv_ne_zero hr.ne') hi.ne', Real.log_inv]
  ring

/-- Cochrane (2023), (16.25), pp. 377–378: a second-order bound used for the exact
linearisation; for `|z| ≤ 1`, `|e^z − 1 − z| ≤ z²`. -/
theorem abs_exp_sub_le {z : ℝ} (hz : |z| ≤ 1) : |Real.exp z - 1 - z| ≤ z ^ 2 :=
  Real.abs_exp_sub_one_sub_id_le hz

/-- Cochrane (2023), (16.25) ⇒ (16.1), pp. 377–378, the exact linearisation under uncertainty:
for an arbitrary expectation system and a bounded log-inflation variable `x = π_{t+1}`, the map
`ε ↦ E_t[exp(−εx)]` (the expected inverse gross inflation along the ray `επ_{t+1}` through the
zero-inflation steady state) has derivative `−E_t x` at `ε = 0`. -/
theorem hasDerivAt_E_exp {Ω : Type*} (𝔼 : ExpectationSystem Ω) {x : Ω → ℝ} {M : ℝ}
    (hM : 0 < M) (hx : ∀ ω, |x ω| ≤ M) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => 𝔼.E t (fun ω' => Real.exp (-(ε * x ω'))) ω) (-(𝔼.E t x ω)) 0 := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hball : ∀ᶠ ε in 𝓝 (0 : ℝ), |ε| < min (1 / M) (c / M ^ 2) :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds (0 : ℝ)
      (show 0 < min (1 / M) (c / M ^ 2) from lt_min (by positivity) (by positivity)))
      fun ε hε => by rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hε; exact hε
  filter_upwards [hball] with ε hε
  have hε1 : |ε| * M ≤ 1 := by
    have := (lt_min_iff.mp hε).1
    rw [lt_div_iff₀ hM] at this
    linarith
  have hε2 : |ε| * M ^ 2 ≤ c := by
    have := (lt_min_iff.mp hε).2
    rw [lt_div_iff₀ (by positivity)] at this
    linarith
  -- the remainder `R(ω') = exp(−εx) − 1 + εx` is bounded by `ε²M²`
  set R : Ω → ℝ := fun ω' => Real.exp (-(ε * x ω')) - 1 - (-(ε * x ω')) with hR
  have hRb : ∀ ω', |R ω'| ≤ ε ^ 2 * M ^ 2 := by
    intro ω'
    have hz : |-(ε * x ω')| ≤ 1 := by
      rw [abs_neg, abs_mul]
      exact le_trans (mul_le_mul_of_nonneg_left (hx ω') (abs_nonneg ε)) hε1
    have h := abs_exp_sub_le hz
    have hsq : (-(ε * x ω')) ^ 2 ≤ ε ^ 2 * M ^ 2 := by
      have : (-(ε * x ω')) ^ 2 = ε ^ 2 * (x ω') ^ 2 := by ring
      rw [this]
      have : (x ω') ^ 2 ≤ M ^ 2 := by
        have := hx ω'
        nlinarith [abs_nonneg (x ω'), sq_abs (x ω')]
      exact mul_le_mul_of_nonneg_left this (sq_nonneg ε)
    exact h.trans hsq
  have hdecomp : (fun ω' => Real.exp (-(ε * x ω'))) =
      (fun _ => (1 : ℝ)) + (-ε) • x + R := by
    funext ω'
    simp only [hR, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hE0 : 𝔼.E t (fun ω' => Real.exp (-(0 * x ω'))) ω = 1 := by
    simp only [zero_mul, neg_zero, Real.exp_zero]
    exact congrFun (𝔼.const t 1) ω
  have hEε : 𝔼.E t (fun ω' => Real.exp (-(ε * x ω'))) ω =
      1 + (-ε) * 𝔼.E t x ω + 𝔼.E t R ω := by
    rw [hdecomp, map_add, map_add, map_smul, 𝔼.const]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hER := 𝔼.abs_E_le hRb t ω
  simp only [Real.norm_eq_abs, smul_eq_mul, sub_zero]
  rw [hEε, hE0]
  have : 1 + -ε * 𝔼.E t x ω + 𝔼.E t R ω - 1 - ε * -𝔼.E t x ω = 𝔼.E t R ω := by ring
  rw [this]
  calc |𝔼.E t R ω| ≤ ε ^ 2 * M ^ 2 := hER
    _ = |ε| * (|ε| * M ^ 2) := by rw [← sq_abs]; ring
    _ ≤ |ε| * c := mul_le_mul_of_nonneg_left hε2 (abs_nonneg ε)
    _ = c * |ε| := mul_comm _ _

/-- Cochrane (2023), (16.25) ⇒ (16.1), pp. 377–378, exact linearisation: write the bond-pricing
equation as `log(1 + i_t(ε)) = log(1 + r) − log E_t[exp(−επ_{t+1})]` along the ray `επ_{t+1}`
of log inflation through the zero-inflation steady state. For an arbitrary expectation system and
bounded `π_{t+1}`, its derivative at `ε = 0` is `E_t π_{t+1}`: the linearised Fisher equation
`i_t = r + E_t π_{t+1}` (16.1). -/
theorem hasDerivAt_log_bondPricing {Ω : Type*} (𝔼 : ExpectationSystem Ω) (r : ℝ) {x : Ω → ℝ}
    {M : ℝ} (hM : 0 < M) (hx : ∀ ω, |x ω| ≤ M) (t : ℕ) (ω : Ω) :
    HasDerivAt
      (fun ε => Real.log (1 + r) - Real.log (𝔼.E t (fun ω' => Real.exp (-(ε * x ω'))) ω))
      (𝔼.E t x ω) 0 := by
  have h := hasDerivAt_E_exp 𝔼 hM hx t ω
  have h1 : 𝔼.E t (fun ω' => Real.exp (-((0 : ℝ) * x ω'))) ω = 1 := by
    simp only [zero_mul, neg_zero, Real.exp_zero]
    exact congrFun (𝔼.const t 1) ω
  have hlog := h.log (by rw [h1]; exact one_ne_zero)
  rw [h1, div_one] at hlog
  have := (hasDerivAt_const (0 : ℝ) (Real.log (1 + r))).sub hlog
  convert this using 1
  ring

/-- Cochrane (2023), (16.25), pp. 377–378: for bounded `x` (`|x| ≤ M`) and every `ε`, the
conditional expectation `E_t[exp(−εx)]` is at least `exp(−|ε|M) > 0`. -/
theorem E_exp_pos {Ω : Type*} (𝔼 : ExpectationSystem Ω) {x : Ω → ℝ} {M : ℝ}
    (hx : ∀ ω, |x ω| ≤ M) (t : ℕ) (ω : Ω) (ε : ℝ) :
    0 < 𝔼.E t (fun ω' => Real.exp (-(ε * x ω'))) ω := by
  have hle : (fun _ : Ω => Real.exp (-(|ε| * M))) ≤ fun ω' => Real.exp (-(ε * x ω')) := by
    intro ω'
    apply Real.exp_le_exp.mpr
    have h1 : |ε * x ω'| ≤ |ε| * M := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hx ω') (abs_nonneg ε)
    linarith [le_abs_self (ε * x ω')]
  have := 𝔼.mono t hle ω
  rw [𝔼.const] at this
  exact lt_of_lt_of_le (Real.exp_pos _) this

/-- Cochrane (2023), (16.25) ⇒ (16.1), pp. 377–378, the exact linearisation as a Gateaux
derivative: at any deterministic steady state with log inflation `π*`, along *every* bounded
direction `x` of log inflation `π_{t+1} = π* + εx`, the map
`ε ↦ log(1 + i_t(ε)) = log(1 + r) − log E_t[exp(−(π* + εx))]` takes the value `log(1+r) + π*` at
`ε = 0` and has derivative `E_t x` there, for an arbitrary expectation system. So the linearised
Fisher equation `i_t = r + E_t π_{t+1}` (16.1) holds in every bounded direction, not only along
one ray. -/
theorem gateaux_log_bondPricing {Ω : Type*} (𝔼 : ExpectationSystem Ω) (r pis : ℝ) {x : Ω → ℝ}
    {M : ℝ} (hM : 0 < M) (hx : ∀ ω, |x ω| ≤ M) (t : ℕ) (ω : Ω) :
    Real.log (1 + r) - Real.log (𝔼.E t (fun ω' => Real.exp (-(pis + 0 * x ω'))) ω) =
        Real.log (1 + r) + pis ∧
      HasDerivAt
        (fun ε => Real.log (1 + r) - Real.log (𝔼.E t (fun ω' => Real.exp (-(pis + ε * x ω'))) ω))
        (𝔼.E t x ω) 0 := by
  have hsplit : ∀ ε : ℝ, 𝔼.E t (fun ω' => Real.exp (-(pis + ε * x ω'))) ω =
      Real.exp (-pis) * 𝔼.E t (fun ω' => Real.exp (-(ε * x ω'))) ω := by
    intro ε
    have : (fun ω' => Real.exp (-(pis + ε * x ω'))) =
        Real.exp (-pis) • fun ω' => Real.exp (-(ε * x ω')) := by
      funext ω'
      simp only [Pi.smul_apply, smul_eq_mul, neg_add, Real.exp_add]
    rw [this, map_smul]
    rfl
  have hfun : (fun ε => Real.log (1 + r) -
      Real.log (𝔼.E t (fun ω' => Real.exp (-(pis + ε * x ω'))) ω)) =
      fun ε => (Real.log (1 + r) + pis) -
        Real.log (𝔼.E t (fun ω' => Real.exp (-(ε * x ω'))) ω) := by
    funext ε
    rw [hsplit, Real.log_mul (Real.exp_pos _).ne' (E_exp_pos 𝔼 hx t ω ε).ne', Real.log_exp]
    ring
  have h1 : 𝔼.E t (fun ω' => Real.exp (-((0 : ℝ) * x ω'))) ω = 1 := by
    simp only [zero_mul, neg_zero, Real.exp_zero]
    exact congrFun (𝔼.const t 1) ω
  refine ⟨?_, ?_⟩
  · rw [hsplit, h1, mul_one, Real.log_exp]
    ring
  · rw [hfun]
    have := hasDerivAt_log_bondPricing 𝔼 (r := r) hM hx t ω
    have h2 := this.const_add pis
    convert h2 using 1
    funext ε
    ring

/-- Cochrane (2023), eq. (16.27), p. 378, exact linearisation of the rule: if `Φ(Π*) = Π*` and
`Φ′(Π*) = d`, the rule in logs, `π ↦ log Φ(e^π)`, has slope `d` at `log Π*`; so the linearised
rule is `i_t − r = φ(π_t − π*)` with `φ = Φ′(Π*)`, and the linearised dynamics (16.29) are
`π_{t+1} − π* = φ(π_t − π*)`. -/
theorem hasDerivAt_log_rule {Φ : ℝ → ℝ} {Pis d : ℝ} (hPis : 0 < Pis) (hfix : Φ Pis = Pis)
    (hd : HasDerivAt Φ d Pis) :
    HasDerivAt (fun p => Real.log (Φ (Real.exp p))) d (Real.log Pis) := by
  have he : HasDerivAt Real.exp Pis (Real.log Pis) := by
    have := Real.hasDerivAt_exp (Real.log Pis)
    rwa [Real.exp_log hPis] at this
  have hd' : HasDerivAt Φ d (Real.exp (Real.log Pis)) := by rwa [Real.exp_log hPis]
  have hc := hd'.comp (Real.log Pis) he
  have hΦ : Φ (Real.exp (Real.log Pis)) ≠ 0 := by rw [Real.exp_log hPis, hfix]; exact hPis.ne'
  have hl := hc.log hΦ
  simp only [Function.comp_apply, Real.exp_log hPis, hfix] at hl
  convert hl using 1
  field_simp

/-! ## (16.27)–(16.29): the inflation dynamics -/

/-- Cochrane (2023), eqs. (16.27)–(16.29), p. 378: with `β(1 + r) = 1`, the rule
`1 + i_t = (1 + r)Φ(Π_t)` and perfect foresight `Π_{t+1} = β(1 + i_t)` hold at every date if and
only if the interest rate is given by the rule and inflation follows `Π_{t+1} = Φ(Π_t)`. -/
theorem dynamics_iff {r : ℝ} {Φ : ℝ → ℝ} {infl i : ℕ → ℝ} (hr : 0 < 1 + r) :
    ((∀ t, 1 + i t = (1 + r) * Φ (infl t)) ∧ ∀ t, infl (t + 1) = (1 + r)⁻¹ * (1 + i t)) ↔
      (∀ t, 1 + i t = (1 + r) * Φ (infl t)) ∧ ∀ t, infl (t + 1) = Φ (infl t) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun t => ?_⟩
    rw [h2, h1, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun t => ?_⟩
    rw [h2, h1, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

/-- Cochrane (2023), eq. (16.29), p. 378: "initial inflation `Π₀` is the only indeterminacy":
a path of (16.29) is the orbit of `Φ` from `Π₀`. -/
theorem eq_orbit {Φ : ℝ → ℝ} {infl : ℕ → ℝ} (h : ∀ t, infl (t + 1) = Φ (infl t)) (t : ℕ) :
    infl t = Φ^[t] (infl 0) := by
  induction t with
  | zero => rfl
  | succ n ih => rw [h, ih, Function.iterate_succ_apply']

/-- Cochrane (2023), eq. (16.29), p. 378: the orbit `Φ^[t](Π₀)` solves (16.29). -/
theorem orbit_succ (Φ : ℝ → ℝ) (Pi0 : ℝ) (t : ℕ) :
    Φ^[t + 1] Pi0 = Φ (Φ^[t] Pi0) :=
  Function.iterate_succ_apply' _ _ _

/-! ## p. 378: the active steady state -/

/-- Cochrane (2023), p. 378, "any `Π_t` that is `ε` above or below `Π*` leads away from `Π*`":
if `Φ(Π*) = Π*` and `Φ′(Π*) > 1`, there is `δ > 0` such that every path of (16.29) not starting at
`Π*` is at distance at least `δ` from `Π*` at some date. -/
theorem target_repelling {Φ : ℝ → ℝ} {Pis d : ℝ} (hfix : Φ Pis = Pis)
    (hd : HasDerivAt Φ d Pis) (hd1 : 1 < d) :
    ∃ δ > 0, ∀ infl : ℕ → ℝ, (∀ t, infl (t + 1) = Φ (infl t)) → infl 0 ≠ Pis →
      ∃ t, δ ≤ |infl t - Pis| :=
  repelling_of_one_lt_abs_deriv hfix hd (by rw [abs_of_pos (by linarith)]; exact hd1)

/-- Cochrane (2023), p. 378, "the equilibrium `Π*` is a unique 'locally bounded' equilibrium":
with `Φ′(Π*) > 1` there is `δ > 0` such that the only path of (16.29) staying within `δ` of `Π*`
at all dates is `Π_t ≡ Π*`. -/
theorem target_unique_locally_bounded {Φ : ℝ → ℝ} {Pis d : ℝ} (hfix : Φ Pis = Pis)
    (hd : HasDerivAt Φ d Pis) (hd1 : 1 < d) :
    ∃ δ > 0, ∀ infl : ℕ → ℝ, (∀ t, infl (t + 1) = Φ (infl t)) →
      (∀ t, |infl t - Pis| < δ) → ∀ t, infl t = Pis := by
  obtain ⟨δ, hδ, hrep⟩ := target_repelling hfix hd hd1
  refine ⟨δ, hδ, fun infl hpath hbd t => ?_⟩
  by_contra hne
  obtain ⟨s, hs⟩ := hrep (fun s => infl (t + s)) (fun s => by rw [← add_assoc]; exact hpath _)
    (by simpa using hne)
  linarith [hbd (t + s)]

/-! ## p. 379: the zero bound -/

/-- Cochrane (2023), p. 379, error E2: `Π_{t+1} = β` exactly when `i_t = 0`, which the zero bound
allows. -/
theorem zero_bound_eq_iff {r i Pi1 : ℝ} (hr : 0 < 1 + r) (h : Pi1 = (1 + r)⁻¹ * (1 + i)) :
    i = 0 ↔ Pi1 = (1 + r)⁻¹ := by
  rw [h]
  constructor
  · intro hi; rw [hi]; ring
  · intro he
    have h2 : (1 + r)⁻¹ * (1 + i) = (1 + r)⁻¹ * 1 := by rw [he]; ring
    have := mul_left_cancel₀ (inv_ne_zero hr.ne') h2
    linarith

/-- Cochrane (2023), pp. 378–379: the rule (16.27) respects the zero bound at `Π` iff
`Φ(Π) ≥ β`. -/
theorem rule_respects_bound_iff {r x : ℝ} {Φ : ℝ → ℝ} (hr : 0 < 1 + r) :
    0 ≤ (1 + r) * Φ x - 1 ↔ (1 + r)⁻¹ ≤ Φ x := by
  rw [inv_le_iff_one_le_mul₀' hr]
  constructor <;> intro h <;> linarith

/-! ## p. 379: the second steady state `Π_L` (error E2) -/

/-- Cochrane (2023), p. 379, "the function `Φ(Π)` must also have another stationary point,
labeled `Π_L`", corrected (error E2). If `Φ` is continuous on `[β, Π*]`, respects the zero bound
there (`Φ ≥ β`), `Φ(Π*) = Π*` and `Φ′(Π*) > 1`, then there is a largest fixed point
`Π_L ∈ [β, Π*)` below `Π*`: `Φ(Π) < Π` on `(Π_L, Π*)`, and `Φ′(Π_L) ≤ 1` whenever `Φ` is
differentiable at `Π_L`. (Only the weak inequality follows: see `e2_tangency_counterexample`.) -/
theorem lower_steady_state {Φ : ℝ → ℝ} {β Pis d : ℝ} (hβPis : β < Pis)
    (hcont : ContinuousOn Φ (Set.Icc β Pis)) (hbound : ∀ x ∈ Set.Icc β Pis, β ≤ Φ x)
    (hfix : Φ Pis = Pis) (hd : HasDerivAt Φ d Pis) (hd1 : 1 < d) :
    ∃ PL, β ≤ PL ∧ PL < Pis ∧ Φ PL = PL ∧ (∀ x, PL < x → x < Pis → Φ x < x) ∧
      ∀ d', HasDerivAt Φ d' PL → d' ≤ 1 := by
  set f : ℝ → ℝ := fun x => Φ x - x with hf
  have hfd : ∀ {x e}, HasDerivAt Φ e x → HasDerivAt f (e - 1) x :=
    fun h => h.sub (hasDerivAt_id _)
  have hfc : ∀ a b, β ≤ a → b ≤ Pis → ContinuousOn f (Set.Icc a b) := fun a b ha hb =>
    ((hcont.mono fun y hy => ⟨ha.trans hy.1, hy.2.trans hb⟩).sub continuousOn_id)
  have hfPis : f Pis = 0 := by simp [hf, hfix]
  have hfβ : 0 ≤ f β := by simp only [hf]; linarith [hbound β ⟨le_rfl, hβPis.le⟩]
  obtain ⟨δ, hδ, hleft, -⟩ := sign_near_of_deriv_pos (hfd hd) (by linarith)
  have hneg : ∀ y, Pis - δ < y → y < Pis → f y < 0 := fun y h1 h2 => by
    have := hleft y h1 h2; rwa [hfPis] at this
  set y1 := max β (Pis - δ / 2) with hy1
  have hy1lt : y1 < Pis := max_lt hβPis (by linarith)
  have hfy1 : f y1 < 0 := hneg y1 (lt_max_of_lt_right (by linarith)) hy1lt
  have hβy1 : β ≤ y1 := le_max_left _ _
  set S := Set.Icc β y1 ∩ f ⁻¹' {0} with hS
  have hSne : S.Nonempty := by
    obtain ⟨c, hc, hfc0⟩ := intermediate_value_Icc' hβy1 (hfc β y1 le_rfl hy1lt.le)
      ⟨hfy1.le, hfβ⟩
    exact ⟨c, hc, hfc0⟩
  have hSclosed : IsClosed S :=
    (hfc β y1 le_rfl hy1lt.le).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hSbdd : BddAbove S := ⟨y1, fun z hz => hz.1.2⟩
  have hmem := hSclosed.csSup_mem hSne hSbdd
  set PL := sSup S with hPL
  have hPLβ : β ≤ PL := hmem.1.1
  have hPLy1 : PL ≤ y1 := hmem.1.2
  have hPLfix : f PL = 0 := hmem.2
  have hbelow : ∀ x, PL < x → x < Pis → Φ x < x := by
    intro x hx1 hx2
    suffices f x < 0 by simp only [hf] at this; linarith
    by_cases hxy : x ≤ y1
    · by_contra hcon
      push Not at hcon
      obtain ⟨c, hc, hfc0⟩ := intermediate_value_Icc' hxy
        (hfc x y1 (by linarith) hy1lt.le) ⟨hfy1.le, hcon⟩
      have hcS : c ∈ S := ⟨⟨by linarith [hc.1], hc.2⟩, hfc0⟩
      have := le_csSup hSbdd hcS
      linarith [hc.1]
    · push Not at hxy
      exact hneg x (by linarith [le_max_right β (Pis - δ / 2)]) hx2
  refine ⟨PL, hPLβ, by linarith, by simpa [hf, sub_eq_zero] using hPLfix, hbelow,
    fun d' hd' => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨ε, hε, -, hright⟩ := sign_near_of_deriv_pos (hfd hd') (by linarith)
  set y := min (PL + ε / 2) ((PL + Pis) / 2) with hy
  have hPLP : PL < Pis := by linarith
  have hy1' : PL < y := lt_min (by linarith) (by linarith)
  have hy2 : y < Pis := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have h1 := hright y hy1' (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  have h2 := hbelow y hy1' hy2
  rw [hPLfix] at h1
  simp only [hf] at h1
  linarith

/-- Cochrane (2023), p. 379, error E2 counterexample: the rule
`Φ(Π) = max(1/2, Π + (Π − 1/2)(Π − 1)²(Π − 2))` (with `β = 1/2`, i.e. `r = 1`). -/
noncomputable def phiTan (x : ℝ) : ℝ := max (1 / 2) (x + (x - 1 / 2) * (x - 1) ^ 2 * (x - 2))

/-- Cochrane (2023), p. 379, error E2: the polynomial branch of `phiTan` is at least `1/2` on
`[1/2, ∞)`. -/
theorem phiTan_poly_ge {x : ℝ} (hx : 1 / 2 ≤ x) :
    1 / 2 ≤ x + (x - 1 / 2) * (x - 1) ^ 2 * (x - 2) := by
  have h : (x - 1) ^ 2 * (x - 2) ≥ -1 := by
    rcases le_or_gt 2 x with h2 | h2
    · nlinarith [sq_nonneg (x - 1)]
    · have hb : (x - 1) ^ 2 * (2 - x) ≤ 1 := by
        rcases le_or_gt x (3 / 2) with h3 | h3
        · have ha : (x - 1) ^ 2 ≤ 1 / 4 := by nlinarith
          have := mul_le_mul ha (by linarith : 2 - x ≤ 3 / 2) (by linarith) (by norm_num)
          linarith
        · have ha : (x - 1) ^ 2 ≤ 1 := by nlinarith
          have := mul_le_mul ha (by linarith : 2 - x ≤ 1 / 2) (by linarith) (by norm_num)
          linarith
      nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ x - 1 / 2)]

/-- Cochrane (2023), p. 379, error E2: on `[1/2, ∞)` the rule `phiTan` is its polynomial
branch. -/
theorem phiTan_eq {x : ℝ} (hx : 1 / 2 ≤ x) :
    phiTan x = x + (x - 1 / 2) * (x - 1) ^ 2 * (x - 2) :=
  max_eq_right (phiTan_poly_ge hx)

/-- Cochrane (2023), p. 379, error E2: the derivative of the polynomial branch of `phiTan`. -/
theorem hasDerivAt_tanPoly (x : ℝ) :
    HasDerivAt (fun y : ℝ => y + (y - 1 / 2) * (y - 1) ^ 2 * (y - 2))
      (1 + ((x - 1) ^ 2 * (x - 2) + (x - 1 / 2) * (2 * (x - 1)) * (x - 2) +
        (x - 1 / 2) * (x - 1) ^ 2)) x := by
  have ha : HasDerivAt (fun y : ℝ => y - 1 / 2) 1 x := (hasDerivAt_id x).sub_const _
  have hb : HasDerivAt (fun y : ℝ => (y - 1) ^ 2) (2 * (x - 1)) x := by
    have := ((hasDerivAt_id x).sub_const (1 : ℝ)).pow 2
    convert this using 1
    · funext y; simp
    · simp
  have hc : HasDerivAt (fun y : ℝ => y - 2) 1 x := (hasDerivAt_id x).sub_const _
  have h := (hasDerivAt_id x).add ((ha.mul hb).mul hc)
  convert h using 1
  · funext y; simp only [id_eq, Pi.add_apply, Pi.mul_apply]
  · simp only [Pi.mul_apply]; ring

/-- Cochrane (2023), p. 379, error E2: `phiTan` equals its polynomial branch near any
`x > 1/2`, so it has the polynomial's derivative there. -/
theorem hasDerivAt_phiTan {x : ℝ} (hx : 1 / 2 < x) :
    HasDerivAt phiTan
      (1 + ((x - 1) ^ 2 * (x - 2) + (x - 1 / 2) * (2 * (x - 1)) * (x - 2) +
        (x - 1 / 2) * (x - 1) ^ 2)) x := by
  refine (hasDerivAt_tanPoly x).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact phiTan_eq (le_of_lt hy)

/-- Cochrane (2023), p. 379, error E2, the tangency counterexample: with `β = 1/2` the rule
`phiTan` is continuous, respects the zero bound everywhere (`Φ ≥ β`), has the active steady state
`Π* = 2` with `Φ′(Π*) = 5/2 > 1`, and the lower steady state given by `lower_steady_state` is
forced to be `Π_L = 1`, where `Φ′(Π_L) = 1`: the printed "`Φ′(Π_L) < 1`" fails. -/
theorem e2_tangency_counterexample :
    Continuous phiTan ∧ (∀ x, 1 / 2 ≤ phiTan x) ∧ phiTan 2 = 2 ∧ HasDerivAt phiTan (5 / 2) 2 ∧
      (∀ PL : ℝ, 1 / 2 ≤ PL → PL < 2 → phiTan PL = PL →
        (∀ x, PL < x → x < 2 → phiTan x < x) → PL = 1) ∧
      phiTan 1 = 1 ∧ (∀ x, 1 < x → x < 2 → phiTan x < x) ∧ HasDerivAt phiTan 1 1 ∧
      ¬ ((1 : ℝ) < 1) := by
  have hd2 := hasDerivAt_phiTan (by norm_num : (1 / 2 : ℝ) < 2)
  have hd1 := hasDerivAt_phiTan (by norm_num : (1 / 2 : ℝ) < 1)
  have hbelow : ∀ x : ℝ, 1 < x → x < 2 → phiTan x < x := by
    intro x h1 h2
    rw [phiTan_eq (by linarith)]
    have : (x - 1 / 2) * (x - 1) ^ 2 * (x - 2) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos (by linarith) (by positivity)) (by linarith)
    linarith
  refine ⟨by unfold phiTan; fun_prop, fun x => le_max_left _ _,
    by rw [phiTan_eq (by norm_num)]; norm_num, by convert hd2 using 1; norm_num, ?_,
    by rw [phiTan_eq (by norm_num)]; norm_num, hbelow, by convert hd1 using 1; norm_num,
    lt_irrefl 1⟩
  intro PL h1 h2 hfix hb
  rw [phiTan_eq h1] at hfix
  have h0 : (PL - 1 / 2) * (PL - 1) ^ 2 * (PL - 2) = 0 := by linarith
  rcases mul_eq_zero.mp h0 with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exfalso
      have := hb 1 (by linarith) (by norm_num)
      rw [phiTan_eq (by norm_num)] at this
      norm_num at this
    · nlinarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.mp h']
  · linarith

/-- Cochrane (2023), p. 379, error E2: in the tangency counterexample `Π_L = 1` is not stable
from the left: every path of (16.29) starting in `(1/2, 1)` stays at or below its initial value
(it drifts down towards the zero-bound rate `1/2`), so it never converges to `Π_L`. -/
theorem phiTan_left_unstable {infl : ℕ → ℝ} (hpath : ∀ t, infl (t + 1) = phiTan (infl t))
    (h0 : infl 0 ∈ Set.Ioo (1 / 2) 1) :
    (∀ t, 1 / 2 ≤ infl t ∧ infl t ≤ infl 0) ∧ ¬ Tendsto infl atTop (𝓝 1) := by
  have hstep : ∀ t, 1 / 2 ≤ infl t ∧ infl t ≤ infl 0 := by
    intro t
    induction t with
    | zero => exact ⟨h0.1.le, le_rfl⟩
    | succ n ih =>
      rw [hpath]
      refine ⟨le_max_left _ _, ?_⟩
      rw [phiTan_eq ih.1]
      have : (infl n - 1 / 2) * (infl n - 1) ^ 2 * (infl n - 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith [ih.1]) (sq_nonneg _))
          (by linarith [ih.2, h0.2])
      linarith [ih.2]
  refine ⟨hstep, fun hlim => ?_⟩
  have := le_of_tendsto' hlim fun t => (hstep t).2
  linarith [h0.2]

/-- Cochrane (2023), p. 379, error E2: continuity is needed for the existence of `Π_L`. The
discontinuous rule `Φ(Π) = Π + 1` for `Π < 3/2`, `Φ(Π) = 2Π − 2` for `Π ≥ 3/2`. -/
noncomputable def phiJump (x : ℝ) : ℝ := if x < 3 / 2 then x + 1 else 2 * x - 2

/-- Cochrane (2023), p. 379, error E2: with `β = 1/2`, `phiJump` respects the zero bound on
`(0, ∞)`, has `Π* = 2` with `Φ′(Π*) = 2 > 1`, and yet has no fixed point in `[β, Π*)`: without
continuity there need be no second steady state. -/
theorem e2_discontinuous_counterexample :
    (∀ x : ℝ, 0 < x → 1 / 2 ≤ phiJump x) ∧ phiJump 2 = 2 ∧ HasDerivAt phiJump 2 2 ∧
      ¬ ∃ PL : ℝ, 1 / 2 ≤ PL ∧ PL < 2 ∧ phiJump PL = PL := by
  refine ⟨fun x hx => ?_, by norm_num [phiJump], ?_, ?_⟩
  · unfold phiJump
    split_ifs with h
    · linarith
    · push Not at h; linarith
  · have h : HasDerivAt (fun x : ℝ => 2 * x - 2) 2 2 := by
      simpa using ((hasDerivAt_id (2 : ℝ)).const_mul 2).sub_const 2
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (by norm_num : (3 / 2 : ℝ) < 2)] with x hx
    have : ¬ x < 3 / 2 := not_lt.mpr (le_of_lt hx)
    simp [phiJump, this]
  · rintro ⟨PL, -, h2, hfix⟩
    unfold phiJump at hfix
    split_ifs at hfix with h
    · linarith
    · linarith

/-! ## pp. 379–380: deflations converge to `Π_L` -/

/-- Cochrane (2023), pp. 379–380, "equilibria that start below `Π*` … trundle down gently to the
zero bound": if `Φ` is continuous on `[Π_L, Π*]`, `Φ(Π_L) = Π_L`, `Φ(Π) < Π` on `(Π_L, Π*)` and
`Φ(Π) ≥ Π_L` there (e.g. `Φ` nondecreasing), every path of (16.29) starting in `(Π_L, Π*)` is
nonincreasing, stays in `[Π_L, Π₀]` and converges to `Π_L`. -/
theorem deflation_tendsto_lower {Φ : ℝ → ℝ} {PL Pis : ℝ} {infl : ℕ → ℝ}
    (hcont : ContinuousOn Φ (Set.Icc PL Pis)) (hfix : Φ PL = PL)
    (hbelow : ∀ x, PL < x → x < Pis → Φ x < x) (hge : ∀ x, PL < x → x < Pis → PL ≤ Φ x)
    (hpath : ∀ t, infl (t + 1) = Φ (infl t)) (h0 : infl 0 ∈ Set.Ioo PL Pis) :
    Antitone infl ∧ (∀ t, PL ≤ infl t ∧ infl t ≤ infl 0) ∧ Tendsto infl atTop (𝓝 PL) := by
  have hstep : ∀ t, (PL ≤ infl t ∧ infl t ≤ infl 0) ∧ infl (t + 1) ≤ infl t := by
    have hinv : ∀ t, PL ≤ infl t ∧ infl t ≤ infl 0 := by
      intro t
      induction t with
      | zero => exact ⟨h0.1.le, le_rfl⟩
      | succ n ih =>
        rw [hpath]
        rcases ih.1.lt_or_eq with hlt | heq
        · have h2 : infl n < Pis := lt_of_le_of_lt ih.2 h0.2
          exact ⟨hge _ hlt h2, ((hbelow _ hlt h2).le.trans ih.2)⟩
        · rw [← heq, hfix]; exact ⟨le_rfl, h0.1.le⟩
    intro t
    refine ⟨hinv t, ?_⟩
    rw [hpath]
    rcases (hinv t).1.lt_or_eq with hlt | heq
    · exact (hbelow _ hlt (lt_of_le_of_lt (hinv t).2 h0.2)).le
    · rw [← heq, hfix]
  have hanti : Antitone infl := antitone_nat_of_succ_le fun t => (hstep t).2
  refine ⟨hanti, fun t => (hstep t).1, ?_⟩
  have hbdd : BddBelow (Set.range infl) := ⟨PL, by rintro _ ⟨t, rfl⟩; exact (hstep t).1.1⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ t, infl t with hL
  have hLPL : PL ≤ L := le_ciInf fun t => (hstep t).1.1
  have hL0 : L ≤ infl 0 := ciInf_le hbdd 0
  have hmem : ∀ t, infl t ∈ Set.Icc PL Pis := fun t =>
    ⟨(hstep t).1.1, ((hstep t).1.2.trans h0.2.le)⟩
  have hLmem : L ∈ Set.Icc PL Pis := ⟨hLPL, hL0.trans h0.2.le⟩
  have hwithin : Tendsto infl atTop (𝓝[Set.Icc PL Pis] L) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hmem⟩
  have h1 : Tendsto (fun t => Φ (infl t)) atTop (𝓝 (Φ L)) :=
    (hcont L hLmem).tendsto.comp hwithin
  have h2 : Tendsto (fun t => Φ (infl t)) atTop (𝓝 L) := by
    have : (fun t => Φ (infl t)) = fun t => infl (t + 1) := funext fun t => (hpath t).symm
    rw [this]
    exact (tendsto_add_atTop_iff_nat 1).mpr hlim
  have hfixL : Φ L = L := tendsto_nhds_unique h1 h2
  rcases hLPL.lt_or_eq with hlt | heq
  · exfalso
    have := hbelow L hlt (lt_of_le_of_lt hL0 h0.2)
    linarith
  · rw [← heq] at hlim; exact hlim

/-- Cochrane (2023), pp. 379–380: if moreover `Φ(Π) > Π_L` on `(Π_L, Π*)` (e.g. `Φ` strictly
increasing), inflation declines strictly and never reaches `Π_L`. -/
theorem deflation_strictAnti {Φ : ℝ → ℝ} {PL Pis : ℝ} {infl : ℕ → ℝ}
    (hbelow : ∀ x, PL < x → x < Pis → Φ x < x) (hgt : ∀ x, PL < x → x < Pis → PL < Φ x)
    (hpath : ∀ t, infl (t + 1) = Φ (infl t)) (h0 : infl 0 ∈ Set.Ioo PL Pis) :
    StrictAnti infl ∧ ∀ t, PL < infl t := by
  have hstep : ∀ t, (PL < infl t ∧ infl t ≤ infl 0) ∧ infl (t + 1) < infl t := by
    have hinv : ∀ t, PL < infl t ∧ infl t ≤ infl 0 := by
      intro t
      induction t with
      | zero => exact ⟨h0.1, le_rfl⟩
      | succ n ih =>
        rw [hpath]
        have h2 : infl n < Pis := lt_of_le_of_lt ih.2 h0.2
        exact ⟨hgt _ ih.1 h2, ((hbelow _ ih.1 h2).le.trans ih.2)⟩
    intro t
    refine ⟨hinv t, ?_⟩
    rw [hpath]
    exact hbelow _ (hinv t).1 (lt_of_le_of_lt (hinv t).2 h0.2)
  exact ⟨strictAnti_nat_of_succ_lt fun t => (hstep t).2, fun t => (hstep t).1.1⟩

/-- Cochrane (2023), p. 379, error E2: in the tangency counterexample the economic conclusion
survives: every path starting in `(Π_L, Π*) = (1, 2)` converges to `Π_L = 1`. -/
theorem phiTan_deflation_tendsto {infl : ℕ → ℝ} (hpath : ∀ t, infl (t + 1) = phiTan (infl t))
    (h0 : infl 0 ∈ Set.Ioo 1 2) : Tendsto infl atTop (𝓝 1) := by
  obtain ⟨-, -, -, -, -, hfix1, hbelow, -, -⟩ := e2_tangency_counterexample
  refine (deflation_tendsto_lower (Pis := 2) ?_ hfix1 hbelow ?_ hpath h0).2.2
  · unfold phiTan; fun_prop
  · intro x h1 h2
    rw [phiTan_eq (by linarith)]
    have hq : -(1 / 4 : ℝ) ≤ (x - 1) * (x - 2) := by nlinarith [sq_nonneg (x - 3 / 2)]
    have hq2 : (x - 1) * (x - 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith)
      (by linarith)
    have hp : -(3 / 8 : ℝ) ≤ (x - 1 / 2) * ((x - 1) * (x - 2)) := by
      nlinarith [mul_le_mul_of_nonneg_right (by linarith : x - 1 / 2 ≤ 3 / 2)
        (by linarith : (0 : ℝ) ≤ -((x - 1) * (x - 2)))]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 1)
      (by linarith : (0 : ℝ) ≤ 1 + (x - 1 / 2) * ((x - 1) * (x - 2)))]

/-- Cochrane (2023), p. 379, "many paths lead to `Π_L` and there are 'multiple local equilibria'
near this point": if `|Φ′(Π_L)| < 1`, there is `δ > 0` such that every `Π₀` within `δ` of `Π_L`
starts a path of (16.29) that stays within `δ` and converges to `Π_L`, and distinct `Π₀` give
distinct paths (a continuum of locally bounded equilibria). -/
theorem lower_locally_indeterminate {Φ : ℝ → ℝ} {PL d : ℝ} (hfix : Φ PL = PL)
    (hd : HasDerivAt Φ d PL) (hd1 : |d| < 1) :
    ∃ δ > 0, Set.InjOn (fun Pi0 t => Φ^[t] Pi0) (Set.Ioo (PL - δ) (PL + δ)) ∧
      ∀ Pi0 ∈ Set.Ioo (PL - δ) (PL + δ),
        (∀ t, |Φ^[t] Pi0 - PL| < δ) ∧ Tendsto (fun t => Φ^[t] Pi0) atTop (𝓝 PL) := by
  obtain ⟨δ, hδ, hatt⟩ := attracting_of_abs_deriv_lt_one hfix hd hd1
  refine ⟨δ, hδ, fun a _ b _ hab => by simpa using congrFun hab 0, fun Pi0 hP => ?_⟩
  exact hatt (fun t => Φ^[t] Pi0) (fun t => orbit_succ Φ Pi0 t)
    (by rw [Function.iterate_zero_apply, abs_lt]; constructor <;> linarith [hP.1, hP.2])

/-! ## p. 379: fiscal policy, (16.26) and (16.30) -/

/-- Cochrane (2023), (16.30) ⇒ (16.26), p. 379, "with … the flow condition (16.30) the
transversality condition holds, and (16.30) implies (16.26)": given the real flow, absolute
summability of discounted surpluses and the transversality condition `βᵀ b_{t+T} → 0`, the
valuation equation (16.26) `b_t = Σ βʲ s_{t+j}` holds as a genuine sum. -/
theorem valuation_of_tvc {r : ℝ} {b s : ℕ → ℝ} (hr : 0 < 1 + r)
    (hflow : ∀ t, b (t + 1) = (1 + r) * (b t - s t)) (t : ℕ)
    (hsum : Summable fun j => (1 + r)⁻¹ ^ j * s (t + j))
    (htvc : Tendsto (fun T => (1 + r)⁻¹ ^ T * b (t + T)) atTop (𝓝 0)) :
    HasSum (fun j => (1 + r)⁻¹ ^ j * s (t + j)) (b t) := by
  have h1 := hsum.hasSum.tendsto_sum_nat
  have h2 : Tendsto (fun T => ∑ j ∈ Finset.range T, (1 + r)⁻¹ ^ j * s (t + j)) atTop
      (𝓝 (b t)) := by
    have : (fun T => ∑ j ∈ Finset.range T, (1 + r)⁻¹ ^ j * s (t + j)) =
        fun T => b t - (1 + r)⁻¹ ^ T * b (t + T) := by
      funext T; rw [Hyperinflation.pv_partial hr hflow t T]; ring
    rw [this]
    simpa using (tendsto_const_nhds (x := b t)).sub htvc
  rw [← tendsto_nhds_unique h1 h2]
  exact hsum.hasSum

/-- Cochrane (2023), (16.26), p. 379: conversely, the valuation equation (as a genuine sum)
together with the flow implies the transversality condition. -/
theorem tvc_of_valuation {r : ℝ} {b s : ℕ → ℝ} (hr : 0 < 1 + r)
    (hflow : ∀ t, b (t + 1) = (1 + r) * (b t - s t)) (t : ℕ)
    (h : HasSum (fun j => (1 + r)⁻¹ ^ j * s (t + j)) (b t)) :
    Tendsto (fun T => (1 + r)⁻¹ ^ T * b (t + T)) atTop (𝓝 0) := by
  have h1 := h.tendsto_sum_nat
  have : (fun T => (1 + r)⁻¹ ^ T * b (t + T)) =
      fun T => b t - ∑ j ∈ Finset.range T, (1 + r)⁻¹ ^ j * s (t + j) := by
    funext T; rw [Hyperinflation.pv_partial hr hflow t T]; ring
  rw [this]
  simpa using (tendsto_const_nhds (x := b t)).sub h1

/-- Cochrane (2023), (16.26) ⇔ transversality, p. 379: given the flow (16.30) and absolute
summability of the discounted surpluses, the valuation equation holds at `t` if and only if the
transversality condition holds at `t`. -/
theorem valuation_iff_tvc {r : ℝ} {b s : ℕ → ℝ} (hr : 0 < 1 + r)
    (hflow : ∀ t, b (t + 1) = (1 + r) * (b t - s t)) (t : ℕ)
    (hsum : Summable fun j => (1 + r)⁻¹ ^ j * s (t + j)) :
    HasSum (fun j => (1 + r)⁻¹ ^ j * s (t + j)) (b t) ↔
      Tendsto (fun T => (1 + r)⁻¹ ^ T * b (t + T)) atTop (𝓝 0) :=
  ⟨tvc_of_valuation hr hflow t, valuation_of_tvc hr hflow t hsum⟩

/-- Cochrane (2023), p. 379, "(This is a specific version of the specification
`s_t = γ(B_{t−1}/P_t)` that produces passive fiscal policy.)": with `r > −1`, under
`s_t = γ b_t` real debt follows `b_{t+1} = (1 + r)(1 − γ)b_t`, and the transversality condition
`βᵗb_t → 0` holds for every initial real debt iff `0 < γ < 2`; `γ = r/(1+r)` lies in this range
for `r > 0`. -/
theorem passive_gamma_tvc_iff {r γ : ℝ} (hr : 0 < 1 + r) :
    (∀ b : ℕ → ℝ, (∀ t, b (t + 1) = (1 + r) * (b t - γ * b t)) →
      Tendsto (fun t => (1 + r)⁻¹ ^ t * b t) atTop (𝓝 0)) ↔ 0 < γ ∧ γ < 2 := by
  have hsol : ∀ b : ℕ → ℝ, (∀ t, b (t + 1) = (1 + r) * (b t - γ * b t)) →
      ∀ t, (1 + r)⁻¹ ^ t * b t = (1 - γ) ^ t * b 0 := by
    intro b hb t
    induction t with
    | zero => simp
    | succ n ih =>
      have e : (1 + r)⁻¹ ^ (n + 1) * b (n + 1) = ((1 + r)⁻¹ ^ n * b n) * (1 - γ) := by
        rw [hb, pow_succ]
        field_simp
      rw [e, ih, pow_succ]
      ring
  have habs : |1 - γ| < 1 ↔ 0 < γ ∧ γ < 2 := by
    rw [abs_lt]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [← habs]
  constructor
  · intro h
    set b : ℕ → ℝ := fun t => ((1 + r) * (1 - γ)) ^ t with hbdef
    have hb : ∀ t, b (t + 1) = (1 + r) * (b t - γ * b t) := fun t => by
      simp only [hbdef, pow_succ]; ring
    have h1 := h b hb
    rw [show (fun t => (1 + r)⁻¹ ^ t * b t) = fun t => (1 - γ) ^ t * b 0 from
      funext (hsol b hb)] at h1
    simp only [hbdef, pow_zero, mul_one] at h1
    by_contra hcon
    push Not at hcon
    have hge : ∀ t : ℕ, 1 ≤ |(1 - γ) ^ t| := fun t => by rw [abs_pow]; exact one_le_pow₀ hcon
    have h2 := h1.abs
    rw [abs_zero] at h2
    have := ge_of_tendsto' h2 hge
    linarith
  · intro h b hb
    simp only [hsol b hb]
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one h).mul_const (b 0)

/-- Cochrane (2023), p. 379: for `r > 0` the passive coefficient `γ = r/(1 + r)` satisfies
`0 < γ < 2`. -/
theorem passive_coefficient_mem {r : ℝ} (hr : 0 < r) : 0 < r / (1 + r) ∧ r / (1 + r) < 2 := by
  refine ⟨by positivity, ?_⟩
  rw [div_lt_iff₀ (by linarith)]
  linarith

/-! ## The perfect-foresight equilibrium of §16.8 -/

/-- Cochrane (2023), eq. (16.27), p. 378: the previous price level, `P_{t−1}` (with the
predetermined initial `P_{−1}` at `t = 0`). -/
def prevP (Pm1 : ℝ) (P : ℕ → ℝ) : ℕ → ℝ
  | 0 => Pm1
  | t + 1 => P t

/-- Cochrane (2023), eq. (16.27), p. 378: gross inflation `Π_t = P_t/P_{t−1}`. -/
noncomputable def infl (Pm1 : ℝ) (P : ℕ → ℝ) (t : ℕ) : ℝ := P t / prevP Pm1 P t

/-- Cochrane (2023), §16.8, pp. 377–379: a perfect-foresight equilibrium of the full model with
interest-rate rule `Φ`, real rate `r`, initial price `P_{−1} = Pm1`: positive prices, the zero
bound `i_t ≥ 0`, the Fisher equation (16.25), the rule (16.27), the flow condition
`B_t/(1 + i_t) + P_t s_t = B_{t−1}` (with `D t = B_{t−1}`), and the valuation equation (16.26)
`B_{t−1}/P_t = Σ βʲ s_{t+j}` at every date, as a genuine sum. -/
def IsEquilibrium (r : ℝ) (Φ : ℝ → ℝ) (Pm1 : ℝ) (P i s D : ℕ → ℝ) : Prop :=
  0 < Pm1 ∧ (∀ t, 0 < P t) ∧ (∀ t, 0 ≤ i t) ∧
    (∀ t, 1 / (1 + i t) = (1 + r)⁻¹ * (P t / P (t + 1))) ∧
    (∀ t, 1 + i t = (1 + r) * Φ (infl Pm1 P t)) ∧
    (∀ t, D (t + 1) / (1 + i t) + P t * s t = D t) ∧
    ∀ t, HasSum (fun j => (1 + r)⁻¹ ^ j * s (t + j)) (D t / P t)

/-- Cochrane (2023), eqs. (16.28)–(16.30), pp. 378–379: in any equilibrium inflation follows
(16.29) `Π_{t+1} = Φ(Π_t)`, respects the zero bound `Π_{t+1} ≥ β`, real debt follows (16.30), and
the transversality condition holds at every date. -/
theorem equilibrium_dynamics {r : ℝ} {Φ : ℝ → ℝ} {Pm1 : ℝ} {P i s D : ℕ → ℝ} (hr : 0 < 1 + r)
    (h : IsEquilibrium r Φ Pm1 P i s D) :
    (∀ t, infl Pm1 P (t + 1) = Φ (infl Pm1 P t)) ∧ (∀ t, (1 + r)⁻¹ ≤ infl Pm1 P (t + 1)) ∧
      (∀ t, D (t + 1) / P (t + 1) = (1 + r) * (D t / P t - s t)) ∧
      ∀ t, Tendsto (fun T => (1 + r)⁻¹ ^ T * (D (t + T) / P (t + T))) atTop (𝓝 0) := by
  obtain ⟨-, hP, hi, hfis, hrule, hflow, hval⟩ := h
  have hfis' : ∀ t, infl Pm1 P (t + 1) = (1 + r)⁻¹ * (1 + i t) := fun t => by
    have := (fisher_pf_iff hr (by linarith [hi t]) (hP t) (hP (t + 1))).mp (hfis t)
    simpa [infl, prevP] using this
  have hrate : ∀ t, 1 + i t = (1 + r) * (P (t + 1) / P t) := fun t => by
    have := hfis' t
    simp only [infl, prevP] at this
    rw [this, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  have hreal : ∀ t, D (t + 1) / P (t + 1) = (1 + r) * (D t / P t - s t) := fun t =>
    Hyperinflation.real_debt_flow_scalar hr (hP t) (hP (t + 1)) (hrate t) (hflow t)
  refine ⟨fun t => ?_, fun t => (Hyperinflation.zero_bound_iff_scalar hr (hfis' t)).mp (hi t),
    hreal,
    fun t => tvc_of_valuation (b := fun t => D t / P t) hr hreal t (hval t)⟩
  rw [hfis', hrule, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

/-- Cochrane (2023), p. 379, "all of the paths graphed in Figure 16.2 are perfect-foresight
equilibria … we only need to exhibit one [fiscal policy]: `s_t = (r/(1+r))B_{t−1}/P_t`": for
`r > 0`, any `P_{−1} > 0`, initial nominal debt `B_{−1}`, and any initial inflation `Π₀ > 0`
whose orbit under `Φ` respects the zero bound, there is an equilibrium with `Π_t = Φ^[t](Π₀)`,
the passive surplus rule, and constant real debt. -/
theorem equilibrium_exists {r : ℝ} {Φ : ℝ → ℝ} {Pm1 Pi0 : ℝ} (D0 : ℝ) (hr : 0 < r)
    (hPm1 : 0 < Pm1) (hPi0 : 0 < Pi0) (hbound : ∀ t, (1 + r)⁻¹ ≤ Φ (Φ^[t] Pi0)) :
    ∃ P i s D : ℕ → ℝ, IsEquilibrium r Φ Pm1 P i s D ∧ D 0 = D0 ∧
      (∀ t, infl Pm1 P t = Φ^[t] Pi0) ∧ (∀ t, s t = r / (1 + r) * (D t / P t)) ∧
      ∀ t, D t / P t = D0 / (Pm1 * Pi0) := by
  have hr1 : 0 < 1 + r := by linarith
  set π : ℕ → ℝ := fun t => Φ^[t] Pi0 with hπ
  have hπpos : ∀ t, 0 < π t := by
    intro t
    cases t with
    | zero => simpa [hπ] using hPi0
    | succ n =>
      simp only [hπ, orbit_succ]
      exact lt_of_lt_of_le (inv_pos.mpr hr1) (hbound n)
  have hπsucc : ∀ t, π (t + 1) = Φ (π t) := fun t => orbit_succ Φ Pi0 t
  set P : ℕ → ℝ := fun t => Pm1 * ∏ k ∈ Finset.range (t + 1), π k with hPdef
  set D : ℕ → ℝ := fun t => D0 * ∏ k ∈ Finset.range t, π (k + 1) with hDdef
  set c : ℝ := D0 / (Pm1 * Pi0) with hc
  have hPpos : ∀ t, 0 < P t := fun t =>
    mul_pos hPm1 (Finset.prod_pos fun k _ => hπpos k)
  have hPsucc : ∀ t, P (t + 1) = P t * π (t + 1) := fun t => by
    simp only [hPdef, Finset.prod_range_succ _ (t + 1)]; ring
  have hDsucc : ∀ t, D (t + 1) = D t * π (t + 1) := fun t => by
    simp only [hDdef, Finset.prod_range_succ]; ring
  have hreal : ∀ t, D t / P t = c := by
    intro t
    induction t with
    | zero =>
      simp only [hDdef, hPdef, hc, Finset.range_zero, Finset.prod_empty, mul_one, zero_add,
        Finset.prod_range_one]
      simp [hπ]
    | succ n ih =>
      rw [hDsucc, hPsucc, mul_div_mul_right _ _ (hπpos (n + 1)).ne', ih]
  have hinfl : ∀ t, infl Pm1 P t = π t := by
    intro t
    cases t with
    | zero =>
      simp only [infl, prevP, hPdef, zero_add, Finset.prod_range_one]
      field_simp
    | succ n =>
      simp only [infl, prevP]
      rw [hPsucc n]
      field_simp [(hPpos n).ne']
  set i : ℕ → ℝ := fun t => (1 + r) * Φ (π t) - 1 with hidef
  set s : ℕ → ℝ := fun _ => r / (1 + r) * c with hsdef
  have hone : ∀ t, 1 + i t = (1 + r) * π (t + 1) := fun t => by
    simp only [hidef, hπsucc]; ring
  refine ⟨P, i, s, D, ⟨hPm1, hPpos, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_,
    fun t => ?_⟩, by simp [hDdef], fun t => hinfl t, fun t => by rw [hreal t],
    hreal⟩
  · have := (rule_respects_bound_iff (x := π t) (Φ := Φ) hr1).mpr (hbound t)
    simpa [hidef] using this
  · rw [hone, hPsucc]
    have := hπpos (t + 1)
    have := hPpos t
    field_simp
  · rw [hinfl, hone, hπsucc]
  · rw [hone, hDsucc]
    have h1 : P t * s t = r / (1 + r) * D t := by
      simp only [hsdef, ← hreal t]
      field_simp [(hPpos t).ne']
    rw [h1]
    have := hπpos (t + 1)
    field_simp
  · rw [hreal t]
    have hq0 : 0 ≤ (1 + r)⁻¹ := (inv_pos.mpr hr1).le
    have hq1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    have hg := (hasSum_geometric_of_lt_one hq0 hq1).mul_right (r / (1 + r) * c)
    convert hg using 1
    field_simp
    rw [show 1 + r - 1 = r by ring, mul_div_assoc, div_self hr.ne', mul_one]

/-- Cochrane (2023), p. 379, "all of the paths … are perfect-foresight equilibria": if the rule
respects the zero bound everywhere (`Φ ≥ β` on `(0, ∞)`), then for every `Π₀ > 0` there is an
equilibrium with initial inflation `Π₀` — a continuum of equilibria, one for each `Π₀`. -/
theorem continuum_of_equilibria {r : ℝ} {Φ : ℝ → ℝ} {Pm1 : ℝ} (D0 : ℝ) (hr : 0 < r)
    (hPm1 : 0 < Pm1) (hbound : ∀ x, 0 < x → (1 + r)⁻¹ ≤ Φ x) (Pi0 : ℝ) (hPi0 : 0 < Pi0) :
    ∃ P i s D : ℕ → ℝ, IsEquilibrium r Φ Pm1 P i s D ∧ infl Pm1 P 0 = Pi0 := by
  have hr1 : 0 < 1 + r := by linarith
  have hpos : ∀ t, 0 < Φ^[t] Pi0 := by
    intro t
    induction t with
    | zero => simpa using hPi0
    | succ n ih => rw [orbit_succ]; exact lt_of_lt_of_le (inv_pos.mpr hr1) (hbound _ ih)
  obtain ⟨P, i, s, D, h, -, hinfl, -⟩ := equilibrium_exists D0 hr hPm1 hPi0 fun t =>
    hbound _ (hpos t)
  exact ⟨P, i, s, D, h, by simpa using hinfl 0⟩

/-- Cochrane (2023), p. 379, "deflationary equilibria that start anywhere below `Π*` and approach
`Π_L` are also valid equilibria, as is `Π_L` itself": under the hypotheses of
`deflation_tendsto_lower` with `Π_L ≥ β`, every `Π₀ ∈ [Π_L, Π*)` is the initial inflation of an
equilibrium (passive fiscal policy) whose inflation converges to `Π_L`. -/
theorem deflationary_equilibria {r : ℝ} {Φ : ℝ → ℝ} {Pm1 PL Pis Pi0 : ℝ} (D0 : ℝ) (hr : 0 < r)
    (hPm1 : 0 < Pm1) (hβPL : (1 + r)⁻¹ ≤ PL) (hcont : ContinuousOn Φ (Set.Icc PL Pis))
    (hfix : Φ PL = PL) (hbelow : ∀ x, PL < x → x < Pis → Φ x < x)
    (hge : ∀ x, PL < x → x < Pis → PL ≤ Φ x) (h0 : Pi0 ∈ Set.Ico PL Pis) :
    ∃ P i s D : ℕ → ℝ, IsEquilibrium r Φ Pm1 P i s D ∧ infl Pm1 P 0 = Pi0 ∧
      Tendsto (fun t => infl Pm1 P t) atTop (𝓝 PL) := by
  have hr1 : 0 < 1 + r := by linarith
  have hPL0 : 0 < PL := lt_of_lt_of_le (inv_pos.mpr hr1) hβPL
  -- the orbit stays in `[Π_L, Π₀]` and converges to `Π_L`
  have horb : (∀ t, PL ≤ Φ^[t] Pi0) ∧ Tendsto (fun t => Φ^[t] Pi0) atTop (𝓝 PL) := by
    rcases h0.1.lt_or_eq with hlt | heq
    · have := deflation_tendsto_lower (infl := fun t => Φ^[t] Pi0) hcont hfix hbelow hge
        (fun t => orbit_succ Φ Pi0 t) (by simpa using (⟨hlt, h0.2⟩ : Pi0 ∈ Set.Ioo PL Pis))
      exact ⟨fun t => (this.2.1 t).1, this.2.2⟩
    · have hc : ∀ t, Φ^[t] Pi0 = PL := by
        intro t
        induction t with
        | zero => simp [heq]
        | succ n ih => rw [orbit_succ, ih, hfix]
      refine ⟨fun t => (hc t).ge, ?_⟩
      simp only [hc]
      exact tendsto_const_nhds
  obtain ⟨P, i, s, D, h, -, hinfl, -⟩ := equilibrium_exists (Φ := Φ) (Pi0 := Pi0) D0 hr hPm1
    (by linarith [h0.1]) fun t => by rw [← orbit_succ Φ Pi0 t]; exact hβPL.trans (horb.1 (t + 1))
  refine ⟨P, i, s, D, h, by simpa using hinfl 0, ?_⟩
  simp only [hinfl]
  exact horb.2

/-! ## p. 379: the 2%/1% example -/

/-- Cochrane (2023), p. 379: a linear Taylor rule `Φ(Π) = Π* + φ(Π − Π*)` truncated at the zero
bound, `Φ(Π) = max(β, Π* + φ(Π − Π*))`. -/
noncomputable def truncRule (β Pis φ : ℝ) (x : ℝ) : ℝ := max β (Pis + φ * (x - Pis))

/-- Cochrane (2023), p. 379: for `β < Π*` and `φ > 1`, the truncated rule has the active steady
state `Π*` with slope `φ`, the zero-bound steady state `Π_L = β`, and respects the bound. -/
theorem truncRule_props {β Pis φ : ℝ} (hβPis : β < Pis) (hφ : 1 < φ) :
    truncRule β Pis φ Pis = Pis ∧ truncRule β Pis φ β = β ∧ (∀ x, β ≤ truncRule β Pis φ x) ∧
      HasDerivAt (truncRule β Pis φ) φ Pis ∧ Continuous (truncRule β Pis φ) := by
  refine ⟨by simp [truncRule, hβPis.le], ?_, fun x => le_max_left _ _, ?_, by
    unfold truncRule; fun_prop⟩
  · unfold truncRule
    apply max_eq_left
    nlinarith
  · have h : HasDerivAt (fun x => Pis + φ * (x - Pis)) φ Pis := by
      simpa using (((hasDerivAt_id Pis).sub_const Pis).const_mul φ).const_add Pis
    refine h.congr_of_eventuallyEq ?_
    have hlt : Pis - (Pis - β) / φ < Pis := by
      have : 0 < (Pis - β) / φ := div_pos (by linarith) (by linarith)
      linarith
    filter_upwards [Ioi_mem_nhds hlt] with x hx
    unfold truncRule
    apply max_eq_right
    have hx' : Pis - x < (Pis - β) / φ := by simp only [Set.mem_Ioi] at hx; linarith
    rw [lt_div_iff₀ (by linarith)] at hx'
    nlinarith

/-- Cochrane (2023), p. 379: along a path of the truncated rule starting at `Π₀ ≥ β`, the gap
below target is `Π* − Π_t = min(Π* − β, φᵗ(Π* − Π₀))`. -/
theorem truncRule_orbit_gap {β Pis φ x0 : ℝ} (hβPis : β < Pis) (hφ : 1 < φ) (hx0 : β ≤ x0)
    (t : ℕ) :
    Pis - (truncRule β Pis φ)^[t] x0 = min (Pis - β) (φ ^ t * (Pis - x0)) := by
  induction t with
  | zero =>
    simp only [Function.iterate_zero_apply, pow_zero, one_mul]
    exact (min_eq_right (by linarith)).symm
  | succ n ih =>
    rw [orbit_succ]
    have hstep : Pis - truncRule β Pis φ ((truncRule β Pis φ)^[n] x0) =
        min (Pis - β) (φ * (Pis - (truncRule β Pis φ)^[n] x0)) := by
      unfold truncRule
      rw [← min_sub_sub_left]
      congr 1
      ring
    rw [hstep, ih, mul_min_of_nonneg _ _ (by linarith : (0 : ℝ) ≤ φ), pow_succ]
    have hA : Pis - β ≤ φ * (Pis - β) := by nlinarith
    rw [← min_assoc, min_eq_left hA]
    congr 1
    ring

/-- Cochrane (2023), p. 379, "paths that start at `Π_t = 1.99%` and drift down to … `i_t = 0%`,
and stay there": with the truncated rule, every path starting in `[β, Π*)` reaches the zero
bound `Π = β` (`i = 0`) in finite time and stays there. -/
theorem truncRule_hits_bound {β Pis φ x0 : ℝ} (hβPis : β < Pis) (hφ : 1 < φ) (hx0 : β ≤ x0)
    (hx0P : x0 < Pis) : ∃ T, ∀ t, T ≤ t → (truncRule β Pis φ)^[t] x0 = β := by
  have hg : 0 < Pis - x0 := by linarith
  obtain ⟨T, hT⟩ := pow_unbounded_of_one_lt ((Pis - β) / (Pis - x0)) hφ
  refine ⟨T, fun t ht => ?_⟩
  have h1 : Pis - β ≤ φ ^ t * (Pis - x0) := by
    rw [div_lt_iff₀ hg] at hT
    have := pow_le_pow_right₀ hφ.le ht
    nlinarith
  have := truncRule_orbit_gap hβPis hφ hx0 t
  rw [min_eq_left h1] at this
  linarith

/-- Cochrane (2023), p. 379, the example: "if `Π* = 2%` … and the real interest rate is `r = 1%`,
then we have to rule out paths that start at `Π_t = 1.99%` and drift down to `Π_t = −1%`,
`i_t = 0%`, and stay there". With `β = 1/1.01`, `Π* = 1.02` and the truncated rule with `φ = 3/2`,
the path from `Π₀ = 1.0199` is an equilibrium path that reaches `Π = β` in finite time and stays
there, with `i = 0` and net inflation `β − 1 = −1/101 ∈ (−1%, −0.99%)`. -/
theorem example_two_one :
    (∃ T, ∀ t, T ≤ t →
      (truncRule (1 + 1 / 100)⁻¹ (102 / 100) (3 / 2))^[t] (10199 / 10000) = (1 + 1 / 100)⁻¹) ∧
      (1 + 1 / 100 : ℝ) * (1 + 1 / 100)⁻¹ - 1 = 0 ∧
      (1 + 1 / 100 : ℝ)⁻¹ - 1 = -1 / 101 ∧ (-1 / 100 : ℝ) < -1 / 101 ∧
      (-1 / 101 : ℝ) < -99 / 10000 := by
  refine ⟨truncRule_hits_bound (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Cochrane (2023), p. 380, "if negative real interest rates endure, `Π_L` may occur at, say, 1%
inflation, only one percentage point below the 2% target, corresponding to a −1% real rate": with
`r = −1%` the zero-bound inflation rate is `β − 1 = 1/99 ≈ 1.01%`, about one percentage point
below `2%`. -/
theorem negative_real_rate_example :
    (1 + (-1 / 100) : ℝ)⁻¹ - 1 = 1 / 99 ∧ (101 / 10000 : ℝ) < 1 / 99 ∧ (1 / 99 : ℝ) < 102 / 10000 ∧
      (98 / 10000 : ℝ) < 2 / 100 - 1 / 99 ∧ (2 / 100 : ℝ) - 1 / 99 < 99 / 10000 := by
  norm_num

end Cochrane.NewKeynesianSelection.LowerBound
