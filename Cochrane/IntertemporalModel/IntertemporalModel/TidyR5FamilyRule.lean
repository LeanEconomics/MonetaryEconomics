/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.TidyR5Family

/-!
# A smooth family of exact nonlinear equilibria under an interest-rate rule

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.6 "Interest-rate rules",
pp. 39–42, eqs. (2.20)–(2.25): the linear model `i_t = E_t π_{t+1}`,
`ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}`, `i_t = θ π_t + u_t`, as the derivative of a family of exact
nonlinear equilibria.

The exact rule is `log(1 + i_t) = r + θ π_t + ε u_t` with `r = −log β`, `π_t = log(P_t/P_{t−1})`
and `P_{−1} = B_{−1}/V` the steady-state price level (`RuleExact`), for every `θ ∈ ℝ` and a
disturbance `u` scaled by the shock size `ε`; surpluses are `s_t(ε) = s̄ + ε ŝ_t`
(`TidyR5Family.surpFam`).

## Main results

* `ruleInfl`, `ruleRate`: inflation and the rate of the family in closed form (the recursion
  `π_{t+1} = r + θ π_t + ε u_t + log PVex_t(ε) − log PV_{t+1}(ε)`).
* `rule_equilibrium`, `rule_exact`: for every `ε` in `TidyR5Family.famDom` the target path for
  the rate `ruleRate ε` is an exact equilibrium (`FiscalMonetary.Equilibrium`) and satisfies the
  exact rule; `rule_unique`: every equilibrium satisfying the exact rule is this one, so the
  family is unique.
* `ruleInfl_contDiffOn`, `ruleRate_contDiffOn`, `rule_price_contDiffOn`: smooth in `ε` (every
  `n`, including `∞` and analytic).
* `ruleInfl_hasDerivAt`, `rule_infl_hasDerivAt`, `rule_rate_hasDerivAt`: the derivatives at
  `ε = 0` of inflation and of the log gross rate are the solution (2.25) of the linear model,
  `LinearFTMP.ruleSol θ u ε_{Σs} π̂_0`, and its rate `θ π̂_t + u_t`;
  `rule_family_linearization`: everything together, with uniqueness of the linear solution
  (`LinearFTMP.rule_existsUnique`, every `θ`: no Taylor principle in the nonlinear model's
  linearisation either); `tree_rule_linearization` on every finite event tree.

Hypotheses: pull-out and `FunctionsKnown` (the rate depends on the price level through the
logarithm), both true for perfect foresight and every finite event tree.
-/

namespace Cochrane.IntertemporalModel.TidyR5FamilyRule

open Filter Topology ExpectationTools TidyR5Family

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), p. 40: inflation `π_t = log(P_t/P_{t−1})` of a price path, with
`P_{−1} = B_{−1}/V` (the steady-state price level) at date `0`. -/
noncomputable def logInfl (Bm1 : Ω → ℝ) (V : ℝ) (P : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun ω => Real.log (P 0 ω / (Bm1 ω / V))
  | t + 1 => fun ω => Real.log (P (t + 1) ω / P t ω)

/-- Cochrane (2023), eq. (2.22), p. 40, exact form: the rule
`log(1 + i_t) = −log β + θ π_t + ε u_t` at every date and state. -/
def RuleExact (β θ : ℝ) (Bm1 : Ω → ℝ) (V : ℝ) (u : ℕ → Ω → ℝ) (ε : ℝ) (P i : ℕ → Ω → ℝ) :
    Prop :=
  ∀ t ω, Real.log (1 + i t ω) = -Real.log β + θ * logInfl Bm1 V P t ω + ε * u t ω

/-- Cochrane (2023), eqs. (2.20)–(2.22), p. 40: inflation along the family under the rule, in
closed form: `π_0 = log V − log PV_0(ε)`,
`π_{t+1} = −log β + θ π_t + ε u_t + log PVex_t(ε) − log PV_{t+1}(ε)`. -/
noncomputable def ruleInfl (β sbar : ℝ) (shat : ℕ → Ω → ℝ) (θ : ℝ) (u : ℕ → Ω → ℝ) (ε : ℝ) :
    ℕ → Ω → ℝ
  | 0 => fun ω => Real.log (ssV β sbar) -
      Real.log (FiscalMonetary.pv 𝔼 β (surpFam sbar shat ε) 0 ω)
  | t + 1 => fun ω => -Real.log β + θ * ruleInfl β sbar shat θ u ε t ω + ε * u t ω +
      Real.log (FiscalMonetary.pvEx 𝔼 β (surpFam sbar shat ε) t ω) -
      Real.log (FiscalMonetary.pv 𝔼 β (surpFam sbar shat ε) (t + 1) ω)

/-- Cochrane (2023), eq. (2.22), p. 40: the rate of the family, from the exact rule,
`1 + i_t(ε) = β⁻¹ exp(θ π_t(ε) + ε u_t)`. -/
noncomputable def ruleRate (β sbar : ℝ) (shat : ℕ → Ω → ℝ) (θ : ℝ) (u : ℕ → Ω → ℝ) (ε : ℝ) :
    ℕ → Ω → ℝ :=
  fun t ω => β⁻¹ * Real.exp (θ * ruleInfl 𝔼 β sbar shat θ u ε t ω + ε * u t ω) - 1

variable {β sbar M θ : ℝ} {shat u : ℕ → Ω → ℝ} {Bm1 : Ω → ℝ}

omit 𝔼 in
/-- Cochrane (2023), p. 40: `logInfl` of the family's price level is the family's inflation
`TidyR5Family.inflFam`. -/
theorem logInfl_priceFam (iF : ℝ → ℕ → Ω → ℝ) (ε : ℝ) (𝔼' : ExpectationSystem Ω) (t : ℕ) :
    logInfl Bm1 (ssV β sbar) (priceFam 𝔼' β sbar shat Bm1 iF ε) t =
      inflFam 𝔼' β sbar shat Bm1 iF ε t := by
  cases t <;> rfl

/-- Cochrane (2023), eq. (2.22), p. 40: the rule's rate exceeds `−1` (`β > 0`). -/
theorem ruleRate_gt (hβ0 : 0 < β) (ε : ℝ) (t : ℕ) (ω : Ω) :
    -1 < ruleRate 𝔼 β sbar shat θ u ε t ω := by
  simp only [ruleRate]
  have := mul_pos (inv_pos.mpr hβ0) (Real.exp_pos (θ * ruleInfl 𝔼 β sbar shat θ u ε t ω +
    ε * u t ω))
  linarith

/-- Cochrane (2023), eq. (2.22), p. 40: `log(1 + i_t(ε)) = −log β + θ π_t(ε) + ε u_t`
exactly (`β > 0`). -/
theorem log_one_add_ruleRate (hβ0 : 0 < β) (ε : ℝ) (t : ℕ) (ω : Ω) :
    Real.log (1 + ruleRate 𝔼 β sbar shat θ u ε t ω) =
      -Real.log β + θ * ruleInfl 𝔼 β sbar shat θ u ε t ω + ε * u t ω := by
  simp only [ruleRate, add_sub_cancel]
  rw [Real.log_mul (inv_pos.mpr hβ0).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_inv]
  ring

/-- Cochrane (2023), p. 40: with `FunctionsKnown`, inflation along the family is
adapted (bounded `ŝ`, adapted `u`, `0 ≤ β < 1`). -/
theorem ruleInfl_adapted (hFK : FunctionsKnown 𝔼) (hu : 𝔼.Adapted u)
    (ε : ℝ) : 𝔼.Adapted (ruleInfl 𝔼 β sbar shat θ u ε) := by
  have hlog : ∀ {t : ℕ} {x : Ω → ℝ}, 𝔼.E t x = x →
      𝔼.E t (fun ω => Real.log (x ω)) = fun ω => Real.log (x ω) :=
    fun {t} {x} hx => hFK t x Real.log hx
  intro t
  induction t with
  | zero =>
    have e : ruleInfl 𝔼 β sbar shat θ u ε 0 = (fun _ => Real.log (ssV β sbar)) -
        fun ω => Real.log (FiscalMonetary.pv 𝔼 β (surpFam sbar shat ε) 0 ω) := rfl
    rw [e, map_sub, 𝔼.const, hlog (FiscalMonetary.pv_adapted 𝔼 β _ 0)]
  | succ t ih =>
    have hk : ∀ {x : Ω → ℝ}, 𝔼.E t x = x → 𝔼.E (t + 1) x = x :=
      fun hx => ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) hx
    have e : ruleInfl 𝔼 β sbar shat θ u ε (t + 1) = (fun _ => -Real.log β) +
        θ • ruleInfl 𝔼 β sbar shat θ u ε t + ε • u t +
        (fun ω => Real.log (FiscalMonetary.pvEx 𝔼 β (surpFam sbar shat ε) t ω)) -
        (fun ω => Real.log (FiscalMonetary.pv 𝔼 β (surpFam sbar shat ε) (t + 1) ω)) := rfl
    rw [e, map_sub, map_add, map_add, map_add, 𝔼.const, map_smul, map_smul, hk ih, hk (hu t),
      hk (hlog (FiscalMonetary.pvEx_adapted 𝔼 β _ t)),
      hlog (FiscalMonetary.pv_adapted 𝔼 β _ (t + 1))]

/-- Cochrane (2023), eq. (2.22), p. 40: with `FunctionsKnown`, the rule's rate is adapted. -/
theorem ruleRate_adapted (hFK : FunctionsKnown 𝔼) (hu : 𝔼.Adapted u)
    (ε : ℝ) : 𝔼.Adapted (ruleRate 𝔼 β sbar shat θ u ε) := by
  intro t
  have hg : 𝔼.E t (θ • ruleInfl 𝔼 β sbar shat θ u ε t + ε • u t) =
      θ • ruleInfl 𝔼 β sbar shat θ u ε t + ε • u t := by
    rw [map_add, map_smul, map_smul, ruleInfl_adapted 𝔼 hFK hu ε t, hu t]
  exact hFK t _ (fun y => β⁻¹ * Real.exp y - 1) hg

/-- Cochrane (2023), p. 40: on `famDom` the family's inflation `TidyR5Family.inflFam` (for the
rate `ruleRate`) is the closed form `ruleInfl`. -/
theorem inflFam_eq_ruleInfl (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar)
    (hs : ∀ t ω, |shat t ω| ≤ M) (hB : ∀ ω, 0 < Bm1 ω) {ε : ℝ} (hε : ε ∈ famDom sbar M)
    (t : ℕ) (ω : Ω) :
    inflFam 𝔼 β sbar shat Bm1 (ruleRate 𝔼 β sbar shat θ u) ε t ω =
      ruleInfl 𝔼 β sbar shat θ u ε t ω := by
  have hV : 0 < ssV β sbar := mul_pos (inv_pos.mpr (by linarith)) hsbar
  have hiG : ∀ ε ∈ famDom sbar M, ∀ t ω, -1 < ruleRate 𝔼 β sbar shat θ u ε t ω :=
    fun ε _ t ω => ruleRate_gt 𝔼 hβ0 ε t ω
  cases t with
  | zero =>
    change Real.log (priceFam 𝔼 β sbar shat Bm1 (ruleRate 𝔼 β sbar shat θ u) ε 0 ω /
      (Bm1 ω / ssV β sbar)) = Real.log (ssV β sbar) -
        Real.log (FiscalMonetary.pv 𝔼 β (surpFam sbar shat ε) 0 ω)
    have h3 := pv_surpFam_pos 𝔼 hβ0.le hβ1 hs hε 0 ω
    rw [priceFam_zero]
    have hB' := (hB ω).ne'
    rw [show Bm1 ω / FiscalMonetary.pv 𝔼 β (surpFam sbar shat ε) 0 ω / (Bm1 ω / ssV β sbar) =
        ssV β sbar / FiscalMonetary.pv 𝔼 β (surpFam sbar shat ε) 0 ω by field_simp,
      Real.log_div hV.ne' h3.ne']
  | succ t =>
    change Real.log (priceFam 𝔼 β sbar shat Bm1 (ruleRate 𝔼 β sbar shat θ u) ε (t + 1) ω /
      priceFam 𝔼 β sbar shat Bm1 (ruleRate 𝔼 β sbar shat θ u) ε t ω) = _
    have hP := priceFam_pos 𝔼 hβ0 hβ1 hs hB hiG hε t ω
    have h1 : 0 < 1 + ruleRate 𝔼 β sbar shat θ u ε t ω := by linarith [hiG ε hε t ω]
    have h2 := pvEx_surpFam_pos 𝔼 hβ0 hβ1 hs hε t ω
    have h3 := pv_surpFam_pos 𝔼 hβ0.le hβ1 hs hε (t + 1) ω
    rw [priceFam_succ]
    have hP' := hP.ne'
    rw [show (1 + ruleRate 𝔼 β sbar shat θ u ε t ω) *
        priceFam 𝔼 β sbar shat Bm1 (ruleRate 𝔼 β sbar shat θ u) ε t ω *
        FiscalMonetary.pvEx 𝔼 β (surpFam sbar shat ε) t ω /
        FiscalMonetary.pv 𝔼 β (surpFam sbar shat ε) (t + 1) ω /
        priceFam 𝔼 β sbar shat Bm1 (ruleRate 𝔼 β sbar shat θ u) ε t ω =
        (1 + ruleRate 𝔼 β sbar shat θ u ε t ω) *
        FiscalMonetary.pvEx 𝔼 β (surpFam sbar shat ε) t ω /
        FiscalMonetary.pv 𝔼 β (surpFam sbar shat ε) (t + 1) ω by field_simp,
      Real.log_div (mul_pos h1 h2).ne' h3.ne', Real.log_mul h1.ne' h2.ne',
      log_one_add_ruleRate 𝔼 hβ0]
    rfl

/-- Cochrane (2023), eqs. (2.20)–(2.22), p. 40: for every shock size in `famDom` (and every
`θ`), the family is an exact equilibrium (pull-out, `FunctionsKnown`, `0 < β < 1`, bounded `ŝ`,
adapted `u`, positive initial debt known at `0`). -/
theorem rule_equilibrium (hPO : 𝔼.PullOut) (hFK : FunctionsKnown 𝔼) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hs : ∀ t ω, |shat t ω| ≤ M) (hu : 𝔼.Adapted u) (hBm1 : 𝔼.E 0 Bm1 = Bm1)
    (hB : ∀ ω, 0 < Bm1 ω) {ε : ℝ} (hε : ε ∈ famDom sbar M) :
    FiscalMonetary.Equilibrium 𝔼 β Bm1 (surpFam sbar shat ε)
      (debtFam 𝔼 β sbar shat Bm1 (ruleRate 𝔼 β sbar shat θ u) ε)
      (priceFam 𝔼 β sbar shat Bm1 (ruleRate 𝔼 β sbar shat θ u) ε)
      (ruleRate 𝔼 β sbar shat θ u ε) :=
  fam_equilibrium 𝔼 hPO hβ0 hβ1 hs hBm1 hB (fun ε _ => ruleRate_adapted 𝔼 hFK hu ε)
    (fun ε _ t ω => ruleRate_gt 𝔼 hβ0 ε t ω) hε

/-- Cochrane (2023), eq. (2.22), p. 40: the family satisfies the exact rule
`log(1 + i_t) = −log β + θ π_t + ε u_t` on `famDom`. -/
theorem rule_exact (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar)
    (hs : ∀ t ω, |shat t ω| ≤ M) (hB : ∀ ω, 0 < Bm1 ω) {ε : ℝ} (hε : ε ∈ famDom sbar M) :
    RuleExact β θ Bm1 (ssV β sbar) u ε
      (priceFam 𝔼 β sbar shat Bm1 (ruleRate 𝔼 β sbar shat θ u) ε)
      (ruleRate 𝔼 β sbar shat θ u ε) := by
  intro t ω
  rw [log_one_add_ruleRate 𝔼 hβ0, logInfl_priceFam,
    inflFam_eq_ruleInfl 𝔼 hβ0 hβ1 hsbar hs hB hε t ω]

/-- Cochrane (2023), §2.6, p. 40 (the rule's equilibrium is unique, for every `θ`): for every
shock size in `famDom`, any equilibrium `(B, P, i)` with surpluses `s(ε)` whose rate satisfies
the exact rule is the family member. -/
theorem rule_unique (hPO : 𝔼.PullOut) (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar)
    (hs : ∀ t ω, |shat t ω| ≤ M) (hB : ∀ ω, 0 < Bm1 ω) {ε : ℝ} (hε : ε ∈ famDom sbar M)
    {B P i : ℕ → Ω → ℝ} (h : FiscalMonetary.Equilibrium 𝔼 β Bm1 (surpFam sbar shat ε) B P i)
    (hr : RuleExact β θ Bm1 (ssV β sbar) u ε P i) :
    i = ruleRate 𝔼 β sbar shat θ u ε ∧
      P = priceFam 𝔼 β sbar shat Bm1 (ruleRate 𝔼 β sbar shat θ u) ε ∧
      B = debtFam 𝔼 β sbar shat Bm1 (ruleRate 𝔼 β sbar shat θ u) ε := by
  have hV : 0 < ssV β sbar := mul_pos (inv_pos.mpr (by linarith)) hsbar
  have hpv := pv_surpFam_pos 𝔼 hβ0.le hβ1 hs hε
  have hpvEx := pvEx_surpFam_pos 𝔼 hβ0 hβ1 hs hε
  have hinfl : ∀ t ω, logInfl Bm1 (ssV β sbar) P t ω = ruleInfl 𝔼 β sbar shat θ u ε t ω := by
    intro t
    induction t with
    | zero =>
      intro ω
      change Real.log (P 0 ω / (Bm1 ω / ssV β sbar)) = Real.log (ssV β sbar) -
        Real.log (FiscalMonetary.pv 𝔼 β (surpFam sbar shat ε) 0 ω)
      rw [FiscalMonetary.price_zero h ω (hpv 0 ω).ne']
      have hB' := (hB ω).ne'
      rw [show Bm1 ω / FiscalMonetary.pv 𝔼 β (surpFam sbar shat ε) 0 ω /
          (Bm1 ω / ssV β sbar) = ssV β sbar / FiscalMonetary.pv 𝔼 β (surpFam sbar shat ε) 0 ω
          by field_simp, Real.log_div hV.ne' (hpv 0 ω).ne']
    | succ t ih =>
      intro ω
      change Real.log (P (t + 1) ω / P t ω) = -Real.log β +
        θ * ruleInfl 𝔼 β sbar shat θ u ε t ω + ε * u t ω +
        Real.log (FiscalMonetary.pvEx 𝔼 β (surpFam sbar shat ε) t ω) -
        Real.log (FiscalMonetary.pv 𝔼 β (surpFam sbar shat ε) (t + 1) ω)
      have hP := (h.2.1 t ω).ne'
      have h1 : 0 < 1 + i t ω := by linarith [h.2.2.2.2.1 t ω]
      rw [FiscalMonetary.price_succ h t ω (hpv (t + 1) ω).ne', FiscalMonetary.debt_eq hPO h t ω,
        show (1 + i t ω) * P t ω * FiscalMonetary.pvEx 𝔼 β (surpFam sbar shat ε) t ω /
          FiscalMonetary.pv 𝔼 β (surpFam sbar shat ε) (t + 1) ω / P t ω =
          (1 + i t ω) * FiscalMonetary.pvEx 𝔼 β (surpFam sbar shat ε) t ω /
          FiscalMonetary.pv 𝔼 β (surpFam sbar shat ε) (t + 1) ω by field_simp,
        Real.log_div (mul_pos h1 (hpvEx t ω)).ne' (hpv (t + 1) ω).ne',
        Real.log_mul h1.ne' (hpvEx t ω).ne', hr t ω, ih ω]
  have hi : i = ruleRate 𝔼 β sbar shat θ u ε := by
    funext t ω
    have h1 : 0 < 1 + i t ω := by linarith [h.2.2.2.2.1 t ω]
    have e := hr t ω
    rw [hinfl t ω] at e
    have e2 := congrArg Real.exp e
    rw [Real.exp_log h1, Real.exp_add, Real.exp_add, Real.exp_neg, Real.exp_log hβ0] at e2
    simp only [ruleRate]
    rw [mul_assoc, ← Real.exp_add] at e2
    linarith
  subst hi
  obtain ⟨hP, hBB⟩ := FiscalMonetary.peg_unique hPO (fun t ω => (hpv t ω).ne') h
  exact ⟨rfl, hP, hBB⟩

/-! ### Smoothness and the derivative -/

/-- Cochrane (2023), p. 40: inflation of the rule family is `C^n` in `ε` on `famDom`, for every
`n` (including `∞` and analytic). -/
theorem ruleInfl_contDiffOn (hβ0 : 0 < β) (hβ1 : β < 1) (hs : ∀ t ω, |shat t ω| ≤ M)
    {n : WithTop ℕ∞} (t : ℕ) (ω : Ω) :
    ContDiffOn ℝ n (fun ε => ruleInfl 𝔼 β sbar shat θ u ε t ω) (famDom sbar M) := by
  induction t with
  | zero =>
    exact contDiffOn_const.sub ((pv_contDiff 𝔼 hβ0.le hβ1 hs 0 ω).contDiffOn.log
      fun ε hε => (pv_surpFam_pos 𝔼 hβ0.le hβ1 hs hε 0 ω).ne')
  | succ t ih =>
    exact ((((contDiffOn_const.add (contDiffOn_const.mul ih)).add
      (contDiffOn_id.mul contDiffOn_const)).add
      ((pvEx_contDiff 𝔼 hβ0.le hβ1 hs t ω).contDiffOn.log
        fun ε hε => (pvEx_surpFam_pos 𝔼 hβ0 hβ1 hs hε t ω).ne')).sub
      ((pv_contDiff 𝔼 hβ0.le hβ1 hs (t + 1) ω).contDiffOn.log
        fun ε hε => (pv_surpFam_pos 𝔼 hβ0.le hβ1 hs hε (t + 1) ω).ne'))

/-- Cochrane (2023), eq. (2.22), p. 40: the rule family's rate is `C^n` in `ε` on `famDom`. -/
theorem ruleRate_contDiffOn (hβ0 : 0 < β) (hβ1 : β < 1) (hs : ∀ t ω, |shat t ω| ≤ M)
    {n : WithTop ℕ∞} (t : ℕ) (ω : Ω) :
    ContDiffOn ℝ n (fun ε => ruleRate 𝔼 β sbar shat θ u ε t ω) (famDom sbar M) :=
  (contDiffOn_const.mul ((contDiffOn_const.mul (ruleInfl_contDiffOn 𝔼 hβ0 hβ1 hs t ω)).add
    (contDiffOn_id.mul contDiffOn_const)).exp).sub contDiffOn_const

/-- Cochrane (2023), §2.6, p. 40: the price level, the debt and the inflation of the rule family
are `C^n` in `ε` on `famDom`, for every `n`. -/
theorem rule_price_contDiffOn (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar)
    (hs : ∀ t ω, |shat t ω| ≤ M) (hB : ∀ ω, 0 < Bm1 ω) (n : WithTop ℕ∞) (t : ℕ) (ω : Ω) :
    ContDiffOn ℝ n (fun ε => priceFam 𝔼 β sbar shat Bm1 (ruleRate 𝔼 β sbar shat θ u) ε t ω)
      (famDom sbar M) ∧
    ContDiffOn ℝ n (fun ε => debtFam 𝔼 β sbar shat Bm1 (ruleRate 𝔼 β sbar shat θ u) ε t ω)
      (famDom sbar M) ∧
    ContDiffOn ℝ n (fun ε => inflFam 𝔼 β sbar shat Bm1 (ruleRate 𝔼 β sbar shat θ u) ε t ω)
      (famDom sbar M) := by
  have hiC := fun t ω =>
    ruleRate_contDiffOn 𝔼 (sbar := sbar) (θ := θ) (u := u) (n := n) hβ0 hβ1 hs t ω
  exact ⟨price_contDiffOn 𝔼 hβ0.le hβ1 hs hiC t ω, debt_contDiffOn 𝔼 hβ0.le hβ1 hs hiC t ω,
    infl_contDiffOn 𝔼 hβ0 hβ1 hsbar hs hB (fun ε _ t ω => ruleRate_gt 𝔼 hβ0 ε t ω) hiC t ω⟩

/-- Cochrane (2023), eq. (2.25), p. 40: the derivative at `ε = 0` of the closed-form inflation of
the rule family is the solution of the linear model, `π̂_0 = −PV_0(ŝ)/V` and
`π̂_{t+1} = θ π̂_t + u_t − ε_{Σs,t+1}` (`LinearFTMP.ruleSol`), for every `θ`. -/
theorem ruleInfl_hasDerivAt (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar)
    (hs : ∀ t ω, |shat t ω| ≤ M) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => ruleInfl 𝔼 β sbar shat θ u ε t ω)
      (LinearFTMP.ruleSol θ u (fiscShock 𝔼 β sbar shat) (infl0 𝔼 β sbar shat) t ω) 0 := by
  have hV : 0 < ssV β sbar := mul_pos (inv_pos.mpr (by linarith)) hsbar
  have hpvF : ∀ t, (fun ε => FiscalMonetary.pv 𝔼 β (surpFam sbar shat ε) t ω) =
      fun ε => ssV β sbar + ε * FiscalMonetary.pv 𝔼 β shat t ω :=
    fun t => funext fun ε => by rw [pv_surpFam 𝔼 hβ0.le hβ1 hs]
  have hpvExF : ∀ t, (fun ε => FiscalMonetary.pvEx 𝔼 β (surpFam sbar shat ε) t ω) =
      fun ε => β * ssV β sbar + ε * FiscalMonetary.pvEx 𝔼 β shat t ω :=
    fun t => funext fun ε => by rw [pvEx_surpFam 𝔼 hβ0.le hβ1 hs]
  have hlogpv : ∀ t, HasDerivAt
      (fun ε => Real.log (FiscalMonetary.pv 𝔼 β (surpFam sbar shat ε) t ω))
      (FiscalMonetary.pv 𝔼 β shat t ω / ssV β sbar) 0 := by
    intro t
    have hA : HasDerivAt (fun ε => FiscalMonetary.pv 𝔼 β (surpFam sbar shat ε) t ω)
        (FiscalMonetary.pv 𝔼 β shat t ω) 0 := by
      rw [hpvF t]
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (FiscalMonetary.pv 𝔼 β shat t ω)).const_add
        (ssV β sbar)
    have h0 : FiscalMonetary.pv 𝔼 β (surpFam sbar shat 0) t ω = ssV β sbar := by
      rw [pv_surpFam 𝔼 hβ0.le hβ1 hs]
      ring
    have := hA.log (by rw [h0]; exact hV.ne')
    rwa [h0] at this
  have hlogpvEx : ∀ t, HasDerivAt
      (fun ε => Real.log (FiscalMonetary.pvEx 𝔼 β (surpFam sbar shat ε) t ω))
      (FiscalMonetary.pvEx 𝔼 β shat t ω / (β * ssV β sbar)) 0 := by
    intro t
    have hA : HasDerivAt (fun ε => FiscalMonetary.pvEx 𝔼 β (surpFam sbar shat ε) t ω)
        (FiscalMonetary.pvEx 𝔼 β shat t ω) 0 := by
      rw [hpvExF t]
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const
        (FiscalMonetary.pvEx 𝔼 β shat t ω)).const_add (β * ssV β sbar)
    have h0 : FiscalMonetary.pvEx 𝔼 β (surpFam sbar shat 0) t ω = β * ssV β sbar := by
      rw [pvEx_surpFam 𝔼 hβ0.le hβ1 hs]
      ring
    have := hA.log (by rw [h0]; exact (mul_pos hβ0 hV).ne')
    rwa [h0] at this
  induction t with
  | zero =>
    refine ((hlogpv 0).const_sub (Real.log (ssV β sbar))).congr_deriv ?_
    change -(FiscalMonetary.pv 𝔼 β shat 0 ω / ssV β sbar) =
      -((ssV β sbar)⁻¹ * FiscalMonetary.pv 𝔼 β shat 0 ω)
    rw [div_eq_inv_mul]
  | succ t ih =>
    have hL := HasDerivAt.sub (HasDerivAt.add (HasDerivAt.add (HasDerivAt.const_add
      (-Real.log β) (ih.const_mul θ)) ((hasDerivAt_id (0 : ℝ)).mul_const (u t ω)))
      (hlogpvEx t)) (hlogpv (t + 1))
    refine hL.congr_deriv ?_
    have hshock := scaled_innov_pv 𝔼 (sbar := sbar) hβ0.le hβ1 hs t ω
    have hXe : FiscalMonetary.pvEx 𝔼 β shat t ω =
        β * 𝔼.E t (FiscalMonetary.pv 𝔼 β shat (t + 1)) ω := by
      rw [FiscalMonetary.pvEx_eq]
      rfl
    have hin : innov 𝔼 t (FiscalMonetary.pv 𝔼 β shat (t + 1)) ω =
        FiscalMonetary.pv 𝔼 β shat (t + 1) ω -
          𝔼.E t (FiscalMonetary.pv 𝔼 β shat (t + 1)) ω := by
      unfold innov
      rw [FiscalMonetary.pv_adapted 𝔼 β shat (t + 1)]
      rfl
    change θ * LinearFTMP.ruleSol θ u (fiscShock 𝔼 β sbar shat) (infl0 𝔼 β sbar shat) t ω +
        id 1 * u t ω + FiscalMonetary.pvEx 𝔼 β shat t ω / (β * ssV β sbar) -
        FiscalMonetary.pv 𝔼 β shat (t + 1) ω / ssV β sbar =
      θ * LinearFTMP.ruleSol θ u (fiscShock 𝔼 β sbar shat) (infl0 𝔼 β sbar shat) t ω +
        u t ω - fiscShock 𝔼 β sbar shat (t + 1) ω
    rw [← hshock, hin, hXe, id]
    have := hV.ne'
    have := hβ0.ne'
    field_simp
    ring

/-- Cochrane (2023), eq. (2.25), p. 40: the derivative at `ε = 0` of inflation along the rule
family of exact equilibria (`TidyR5Family.inflFam` for the rate `ruleRate`) is the solution
`LinearFTMP.ruleSol θ u ε_{Σs} π̂_0` of the linear model. -/
theorem rule_infl_hasDerivAt (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar)
    (hs : ∀ t ω, |shat t ω| ≤ M) (hB : ∀ ω, 0 < Bm1 ω) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => inflFam 𝔼 β sbar shat Bm1 (ruleRate 𝔼 β sbar shat θ u) ε t ω)
      (LinearFTMP.ruleSol θ u (fiscShock 𝔼 β sbar shat) (infl0 𝔼 β sbar shat) t ω) 0 := by
  refine (ruleInfl_hasDerivAt 𝔼 hβ0 hβ1 hsbar hs t ω).congr_of_eventuallyEq ?_
  filter_upwards [famDom_mem_nhds hsbar M] with ε hε
  exact inflFam_eq_ruleInfl 𝔼 hβ0 hβ1 hsbar hs hB hε t ω

/-- Cochrane (2023), eqs. (2.22) and (2.25), p. 40: the derivative at `ε = 0` of the log gross
rate `log(1 + i_t(ε))` of the rule family is the linear model's rate `θ π̂_t + u_t`. -/
theorem rule_rate_hasDerivAt (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar)
    (hs : ∀ t ω, |shat t ω| ≤ M) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => Real.log (1 + ruleRate 𝔼 β sbar shat θ u ε t ω))
      (θ * LinearFTMP.ruleSol θ u (fiscShock 𝔼 β sbar shat) (infl0 𝔼 β sbar shat) t ω +
        u t ω) 0 := by
  have e : (fun ε => Real.log (1 + ruleRate 𝔼 β sbar shat θ u ε t ω)) =
      fun ε => -Real.log β + θ * ruleInfl 𝔼 β sbar shat θ u ε t ω + ε * u t ω :=
    funext fun ε => log_one_add_ruleRate 𝔼 hβ0 ε t ω
  rw [e]
  have h := HasDerivAt.add (((ruleInfl_hasDerivAt 𝔼 (θ := θ) (u := u) hβ0 hβ1 hsbar hs t
    ω).const_mul θ).const_add (-Real.log β)) ((hasDerivAt_id (0 : ℝ)).mul_const (u t ω))
  exact h.congr_deriv (by simp)

/-- Cochrane (2023), §2.6, pp. 39–42, **the linear rule model is the derivative of the family of
exact equilibria**, for every `θ ∈ ℝ`. With pull-out, `FunctionsKnown`, `0 < β < 1`, `s̄ > 0`,
bounded adapted `ŝ`, adapted `u` and positive initial debt known at `0`, on the open
neighbourhood `famDom` of `ε = 0`:
* for each `ε` the family member is an equilibrium satisfying the exact rule, and the only one;
* price level, debt and inflation are `C^n` in `ε` for every `n`;
* the linear model (2.20)–(2.22) with `π̂_0 = −PV_0(ŝ)/V` has exactly one solution `(π̂, î)`
  with `π̂` adapted, and it is the derivative at `ε = 0` of (inflation, log gross rate) along the
  family. -/
theorem rule_family_linearization (hPO : 𝔼.PullOut) (hFK : FunctionsKnown 𝔼) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hsbar : 0 < sbar) (hs : ∀ t ω, |shat t ω| ≤ M) (hu : 𝔼.Adapted u)
    (hBm1 : 𝔼.E 0 Bm1 = Bm1) (hB : ∀ ω, 0 < Bm1 ω) :
    (∀ ε ∈ famDom sbar M, FiscalMonetary.Equilibrium 𝔼 β Bm1 (surpFam sbar shat ε)
      (debtFam 𝔼 β sbar shat Bm1 (ruleRate 𝔼 β sbar shat θ u) ε)
      (priceFam 𝔼 β sbar shat Bm1 (ruleRate 𝔼 β sbar shat θ u) ε)
      (ruleRate 𝔼 β sbar shat θ u ε) ∧
      RuleExact β θ Bm1 (ssV β sbar) u ε
        (priceFam 𝔼 β sbar shat Bm1 (ruleRate 𝔼 β sbar shat θ u) ε)
        (ruleRate 𝔼 β sbar shat θ u ε)) ∧
    (∀ ε ∈ famDom sbar M, ∀ B P i : ℕ → Ω → ℝ,
      FiscalMonetary.Equilibrium 𝔼 β Bm1 (surpFam sbar shat ε) B P i →
      RuleExact β θ Bm1 (ssV β sbar) u ε P i →
        i = ruleRate 𝔼 β sbar shat θ u ε ∧
        P = priceFam 𝔼 β sbar shat Bm1 (ruleRate 𝔼 β sbar shat θ u) ε ∧
        B = debtFam 𝔼 β sbar shat Bm1 (ruleRate 𝔼 β sbar shat θ u) ε) ∧
    (∀ (n : WithTop ℕ∞) t ω,
      ContDiffOn ℝ n (fun ε => priceFam 𝔼 β sbar shat Bm1 (ruleRate 𝔼 β sbar shat θ u) ε t ω)
        (famDom sbar M) ∧
      ContDiffOn ℝ n (fun ε => debtFam 𝔼 β sbar shat Bm1 (ruleRate 𝔼 β sbar shat θ u) ε t ω)
        (famDom sbar M) ∧
      ContDiffOn ℝ n (fun ε => inflFam 𝔼 β sbar shat Bm1 (ruleRate 𝔼 β sbar shat θ u) ε t ω)
        (famDom sbar M)) ∧
    (∃! q : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), 𝔼.Adapted q.1 ∧ q.1 0 = infl0 𝔼 β sbar shat ∧
      LinearFTMP.RuleModel 𝔼 θ q.2 u (fiscShock 𝔼 β sbar shat) q.1) ∧
    ∀ q : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), 𝔼.Adapted q.1 → q.1 0 = infl0 𝔼 β sbar shat →
      LinearFTMP.RuleModel 𝔼 θ q.2 u (fiscShock 𝔼 β sbar shat) q.1 →
        ∀ t ω,
          HasDerivAt (fun ε => inflFam 𝔼 β sbar shat Bm1 (ruleRate 𝔼 β sbar shat θ u) ε t ω)
            (q.1 t ω) 0 ∧
          HasDerivAt (fun ε => Real.log (1 + ruleRate 𝔼 β sbar shat θ u ε t ω)) (q.2 t ω) 0 := by
  have hk := infl0_known 𝔼 (β := β) (sbar := sbar) (shat := shat)
  have hsh := fiscShock_isShock 𝔼 (sbar := sbar) hβ0.le hβ1 hs
  have hex := LinearFTMP.rule_existsUnique 𝔼 θ hk hu hsh
  refine ⟨fun ε hε => ⟨rule_equilibrium 𝔼 hPO hFK hβ0 hβ1 hs hu hBm1 hB hε,
      rule_exact 𝔼 hβ0 hβ1 hsbar hs hB hε⟩,
    fun ε hε B P i h hr => rule_unique 𝔼 hPO hβ0 hβ1 hsbar hs hB hε h hr,
    fun n t ω => rule_price_contDiffOn 𝔼 hβ0 hβ1 hsbar hs hB n t ω, hex, ?_⟩
  rintro ⟨π, i⟩ hπ hπ0 hm t ω
  obtain ⟨hi, h224⟩ := (LinearFTMP.ruleModel_iff 𝔼).mp hm
  have h := (LinearFTMP.eq224_iff 𝔼 hπ hu hsh).mp h224
  dsimp only at hπ0 hi h
  have hπeq : π = LinearFTMP.ruleSol θ u (fiscShock 𝔼 β sbar shat) (infl0 𝔼 β sbar shat) := by
    funext t
    induction t with
    | zero => exact hπ0
    | succ t ih =>
      rw [h t, ih]
      rfl
  refine ⟨?_, ?_⟩
  · dsimp only
    rw [hπeq]
    exact rule_infl_hasDerivAt 𝔼 hβ0 hβ1 hsbar hs hB t ω
  · dsimp only
    rw [hi t, hπeq]
    exact rule_rate_hasDerivAt 𝔼 hβ0 hβ1 hsbar hs t ω

/-- Cochrane (2023), §2.6, pp. 39–42, on every finite event tree: for every `θ`, the rule family
of exact equilibria exists on `famDom`, and every adapted solution of the linear rule model
with `π̂_0 = −PV_0(ŝ)/V` is the derivative at `ε = 0` of inflation and of the log gross rate
along it. -/
theorem tree_rule_linearization {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar)
    {shat' u' : ℕ → Ω' → ℝ} (hs : ∀ t ω, |shat' t ω| ≤ M) (hu : T.toExpectationSystem.Adapted u')
    {Bm1' : Ω' → ℝ} (hBm1 : T.toExpectationSystem.E 0 Bm1' = Bm1') (hB : ∀ ω, 0 < Bm1' ω)
    (ε : ℝ) (hε : ε ∈ famDom sbar M) :
    FiscalMonetary.Equilibrium T.toExpectationSystem β Bm1' (surpFam sbar shat' ε)
      (debtFam T.toExpectationSystem β sbar shat' Bm1'
        (ruleRate T.toExpectationSystem β sbar shat' θ u') ε)
      (priceFam T.toExpectationSystem β sbar shat' Bm1'
        (ruleRate T.toExpectationSystem β sbar shat' θ u') ε)
      (ruleRate T.toExpectationSystem β sbar shat' θ u' ε) ∧
    ∀ q : (ℕ → Ω' → ℝ) × (ℕ → Ω' → ℝ), T.toExpectationSystem.Adapted q.1 →
      q.1 0 = infl0 T.toExpectationSystem β sbar shat' →
      LinearFTMP.RuleModel T.toExpectationSystem θ q.2 u'
        (fiscShock T.toExpectationSystem β sbar shat') q.1 →
        ∀ t ω, HasDerivAt (fun ε => inflFam T.toExpectationSystem β sbar shat' Bm1'
          (ruleRate T.toExpectationSystem β sbar shat' θ u') ε t ω) (q.1 t ω) 0 := by
  have h := rule_family_linearization T.toExpectationSystem (θ := θ)
    (ExpectationsFiniteTree.finiteTree_pullOut T) (finiteTree_functionsKnown T) hβ0 hβ1 hsbar
    hs hu hBm1 hB
  exact ⟨(h.1 ε hε).1, fun q h1 h2 h3 t ω => (h.2.2.2.2 q h1 h2 h3 t ω).1⟩

end Cochrane.IntertemporalModel.TidyR5FamilyRule
