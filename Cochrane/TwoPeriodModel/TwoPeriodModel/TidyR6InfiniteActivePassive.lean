/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TwoPeriodModel.TidyR6InfiniteHorizon

/-!
# Active and passive surplus rules with an infinite horizon

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 1, §1.8, pp. 15–18 (the
passive rule (1.16) `s₁ = B₀/P₁` and active policy) and §1.9, pp. 18–19 (the rule
`s = α B₀/P* + γ(B₀/P − B₀/P*)`; "The coefficient `γ = 1` (`γ > 0` in the later intertemporal
model) indicates passive policy"). The two-period module `ActivePassive` proves that the
two-period `γ`-rule is determinate iff `γ ≠ 1`. This module states and proves the
infinite-horizon analogue in the setting of `TidyR6InfiniteHorizon`.

## The rule

The surplus responds to the real value of the debt coming due, `v_t = B_{t−1}/P_t`:
`s_t = γ v_t + ŝ_t` (`ruleSurplus`), with `ŝ` bounded and adapted. `RuleEqm` is an
equilibrium of `TidyR6InfiniteHorizon` whose surplus follows the rule. With `c = 1 − γ` the
equilibrium conditions become `c v_t = ŝ_t + βE_t v_{t+1}` (`rule_rec`).

## Main results

* `passive_tvc` (**passive, `0 < γ < 2`**): every adapted solution of the rule recursion
  satisfies the transversality condition, whatever its initial value;
  `passive_every_price`: every positive adapted price path, from any initial debt, is an
  equilibrium path (with a debt policy constructed from it, `passiveDebt`);
  `passive_indeterminate`: every `P₀ > 0` is an equilibrium price level.
* `active_valuation` (**active, `γ ≤ 0` or `γ ≥ 2`**): in every equilibrium
  `v_t = ∑_j (β/(1 − γ))^j E_t ŝ_{t+j}/(1 − γ)` (`ruleF`); `active_existsUnique`: given a
  positive known debt policy and a positive `ruleF`, exactly one equilibrium.
* `determinate0_iff`: the date-0 price level is pinned down by `B_{−1}` (whatever the later
  debt policy) **iff `γ ≤ 0` or `γ ≥ 2`**. With a last day the condition is `γ ≠ 1`
  (`ActivePassive.gamma_rule_determinate_iff`); with an infinite horizon and the
  transversality condition the passive set is the interval `(0, 2)`.
* `gamma_three_active`: correction of the parenthetical on p. 19, "`γ > 0` in the later
  intertemporal model indicates passive policy": `γ = 3 > 0` is active, with the explicit
  unique equilibrium `P_t = (2 + β)B_{t−1}` for `ŝ = −1` under perfect foresight.
* `E_pos_of_pos` (restated from the IntertemporalModel project): `E_t` of a positive variable is
  positive, from the expectation axioms alone.
-/

namespace Cochrane.TwoPeriodModel.TidyR6InfiniteActivePassive

open Filter Topology Cochrane.TwoPeriodModel.TwoPeriod Cochrane.TwoPeriodModel.ForwardSolution
open Cochrane.TwoPeriodModel.TidyR6InfiniteHorizon

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Strict positivity of `E_t` (restated from the IntertemporalModel project) -/

/-- Cochrane (2023), eq. (1.3), p. 8 (`E_t` of a positive payoff is positive), from the core
axioms alone (restated from the IntertemporalModel project, TidyR5BondPrice.E_pos_of_pos): if
`X > 0` in every state, then `E_t X > 0` in every state. -/
theorem E_pos_of_pos {X : Ω → ℝ} (hX : ∀ ω, 0 < X ω) (t : ℕ) (ω : Ω) : 0 < 𝔼.E t X ω := by
  classical
  have hex : ∀ ω', ∃ n : ℕ, 1 ≤ ((n : ℝ) + 1) * X ω' := fun ω' => by
    obtain ⟨n, hn⟩ := exists_nat_gt (X ω')⁻¹
    refine ⟨n, ?_⟩
    have hx := hX ω'
    have h1 : (X ω')⁻¹ * X ω' = 1 := inv_mul_cancel₀ hx.ne'
    nlinarith
  set K : Ω → ℝ := fun ω' => (Nat.find (hex ω') : ℝ) with hK
  have hbound : ∀ n : ℕ, (fun _ => (1 : ℝ)) ≤ ((n : ℝ) + 1) • X + ((n : ℝ) + 1)⁻¹ • K := by
    intro n ω'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    have hK0 : 0 ≤ K ω' := Nat.cast_nonneg _
    by_cases h : 1 ≤ ((n : ℝ) + 1) * X ω'
    · have : 0 ≤ ((n : ℝ) + 1)⁻¹ * K ω' := mul_nonneg (inv_nonneg.mpr hpos.le) hK0
      linarith
    · have hlt : n < Nat.find (hex ω') := by
        by_contra hle
        push Not at hle
        have hs := Nat.find_spec (hex ω')
        have hmono : ((Nat.find (hex ω') : ℝ) + 1) * X ω' ≤ ((n : ℝ) + 1) * X ω' := by
          refine mul_le_mul_of_nonneg_right ?_ (hX ω').le
          have : (Nat.find (hex ω') : ℝ) ≤ n := by exact_mod_cast hle
          linarith
        exact h (hs.trans hmono)
      have hKn : (n : ℝ) + 1 ≤ K ω' := by
        simp only [hK]
        exact_mod_cast hlt
      have e : ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1) = 1 := inv_mul_cancel₀ hpos.ne'
      have h2 : 1 ≤ ((n : ℝ) + 1)⁻¹ * K ω' := by
        calc (1 : ℝ) = ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1) := e.symm
          _ ≤ ((n : ℝ) + 1)⁻¹ * K ω' :=
            mul_le_mul_of_nonneg_left hKn (inv_nonneg.mpr hpos.le)
      have : 0 ≤ ((n : ℝ) + 1) * X ω' := mul_nonneg hpos.le (hX ω').le
      linarith
  have hE : ∀ n : ℕ, 1 ≤ ((n : ℝ) + 1) * 𝔼.E t X ω + ((n : ℝ) + 1)⁻¹ * 𝔼.E t K ω := by
    intro n
    have h := 𝔼.mono t (hbound n) ω
    rw [𝔼.const, map_add, map_smul, map_smul] at h
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
  have h0 : 0 ≤ 𝔼.E t X ω := by
    have h := 𝔼.mono t (fun ω' => (hX ω').le : (fun _ => (0 : ℝ)) ≤ X) ω
    rwa [𝔼.const] at h
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨n, hn⟩ := exists_nat_gt (𝔼.E t K ω)
    have h1 := hE n
    rw [← h, mul_zero, zero_add] at h1
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
    rw [mul_one, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at h2
    linarith

/-! ### The rule -/

/-- Cochrane (2023), §1.9, pp. 18–19, infinite horizon: the surplus rule
`s_t = γ B_{t−1}/P_t + ŝ_t`, responding with coefficient `γ` to the real value of the debt. -/
noncomputable def ruleSurplus (γ : ℝ) (shat Bm P : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => γ • realDebt Bm P t + shat t

/-- Cochrane (2023), §1.9, pp. 18–19, infinite horizon: an equilibrium under the surplus rule. -/
def RuleEqm (β γ : ℝ) (shat Bm P Q : ℕ → Ω → ℝ) : Prop :=
  Equilibrium 𝔼 β Bm (ruleSurplus γ shat Bm P) P Q

/-- Cochrane (2023), §1.9, pp. 18–19: the forward value of the rule,
`F_t = ∑_j (β/(1 − γ))^j E_t[ŝ_{t+j}/(1 − γ)]`. -/
noncomputable def ruleF (β γ : ℝ) (shat : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  𝔼.forwardSeries (β / (1 - γ)) (fun t => (1 - γ)⁻¹ • shat t)

/-- Cochrane (2023), §1.9, pp. 18–19, infinite horizon: in a rule equilibrium the real debt
satisfies `(1 − γ)v_t = ŝ_t + βE_t v_{t+1}` (debt known, `ExpectationSystem.PullOut`). -/
theorem rule_rec (hPO : 𝔼.PullOut) {β γ : ℝ} {shat Bm P Q : ℕ → Ω → ℝ}
    (hB : DebtKnown 𝔼 Bm) (he : RuleEqm 𝔼 β γ shat Bm P Q) (t : ℕ) :
    (1 - γ) • realDebt Bm P t = shat t + β • 𝔼.E t (realDebt Bm P (t + 1)) := by
  obtain ⟨hP, hPa, hF, hQ, -⟩ := he
  have h := realDebt_rec 𝔼 hPO hP hPa hB t (hF t) (hQ t)
  funext ω
  have e := congrFun h ω
  simp only [ruleSurplus, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
  linarith

/-! ### A stable recursion with vanishing input -/

/-- Cochrane (2023), §1.9, p. 19 (the passive range): if `w_{n+1} = c w_n − β^n e_n` with
`|c| < 1`, `0 < β < 1` and `|e_n| ≤ M`, then `w_n → 0`. -/
theorem stable_tendsto_zero {c β M : ℝ} (hc : |c| < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    {w e : ℕ → ℝ} (he : ∀ n, |e n| ≤ M) (hw : ∀ n, w (n + 1) = c * w n - β ^ n * e n) :
    Tendsto w atTop (𝓝 0) := by
  set r := max |c| β with hr
  have hr0 : 0 < r := lt_of_lt_of_le hβ0 (le_max_right _ _)
  have hr1 : r < 1 := max_lt hc hβ1
  have hM : 0 ≤ M := (abs_nonneg _).trans (he 0)
  have hbound : ∀ n : ℕ, |w n| ≤ (|w 0| + n * (M / r)) * r ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [hw n]
      have h1 : |c * w n| ≤ r * ((|w 0| + n * (M / r)) * r ^ n) := by
        rw [abs_mul]
        exact mul_le_mul (le_max_left _ _) ih (abs_nonneg _) hr0.le
      have h2 : |β ^ n * e n| ≤ r ^ n * M := by
        rw [abs_mul, abs_pow, abs_of_pos hβ0]
        exact mul_le_mul (pow_le_pow_left₀ hβ0.le (le_max_right _ _) n) (he n) (abs_nonneg _)
          (pow_nonneg hr0.le n)
      have h3 : r ^ n * M = (M / r) * r ^ (n + 1) := by
        field_simp; ring
      calc |c * w n - β ^ n * e n| ≤ |c * w n| + |β ^ n * e n| := abs_sub _ _
        _ ≤ r * ((|w 0| + n * (M / r)) * r ^ n) + r ^ n * M := add_le_add h1 h2
        _ = (|w 0| + ((n : ℕ) + 1 : ℕ) * (M / r)) * r ^ (n + 1) := by
          rw [h3]; push_cast; ring
  have hlim : Tendsto (fun n : ℕ => (|w 0| + n * (M / r)) * r ^ n) atTop (𝓝 0) := by
    have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).const_mul |w 0|
    have h2 := (tendsto_self_mul_const_pow_of_lt_one hr0.le hr1).const_mul (M / r)
    have := h1.add h2
    simp only [mul_zero, add_zero] at this
    refine this.congr fun n => ?_
    ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm (fun n => ?_) hlim
  rw [sub_zero, norm_norm, Real.norm_eq_abs]
  exact hbound n

/-! ### Passive rules: `0 < γ < 2` -/

/-- Cochrane (2023), §1.9, p. 19 (**passive policy, infinite horizon**): for `0 < γ < 2`,
`0 < β < 1` and bounded adapted `ŝ`, every adapted solution of `(1 − γ)v_t = ŝ_t + βE_t v_{t+1}`
satisfies the transversality condition `β^T E_t v_{t+T} → 0`, whatever its initial value. -/
theorem passive_tvc {β γ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {shat v : ℕ → Ω → ℝ} (hs : ∀ t ω, |shat t ω| ≤ M)
    (hv : ∀ t, (1 - γ) • v t = shat t + β • 𝔼.E t (v (t + 1))) (t : ℕ) (ω : Ω) :
    Tendsto (fun T : ℕ => β ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 0) := by
  have hc : |1 - γ| < 1 := by rw [abs_lt]; constructor <;> linarith
  refine stable_tendsto_zero hc hβ0 hβ1 (e := fun T => 𝔼.E t (shat (t + T)) ω)
    (fun T => 𝔼.abs_E_le (hs (t + T)) t ω) fun T => ?_
  have h := congrArg (fun x => 𝔼.E t x ω) (hv (t + T))
  simp only [map_smul, map_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    𝔼.tower (Nat.le_add_right t T)] at h
  rw [show t + (T + 1) = t + T + 1 by omega, pow_succ]
  have hβT : 0 < β ^ T := pow_pos hβ0 T
  calc β ^ T * β * 𝔼.E t (v (t + T + 1)) ω
      = β ^ T * (β * 𝔼.E t (v (t + T + 1)) ω) := by ring
    _ = β ^ T * ((1 - γ) * 𝔼.E t (v (t + T)) ω - 𝔼.E t (shat (t + T)) ω) := by
        rw [h]; ring
    _ = (1 - γ) * (β ^ T * 𝔼.E t (v (t + T)) ω) - β ^ T * 𝔼.E t (shat (t + T)) ω := by ring

/-- Cochrane (2023), §1.9, p. 19, infinite horizon: the debt policy that makes a given price
path an equilibrium under the passive rule: `B_{−1}` given and
`B_t = ((1 − γ)v_t − ŝ_t)/(βE_t(1/P_{t+1}))`. -/
noncomputable def passiveDebt (β γ : ℝ) (shat P : ℕ → Ω → ℝ) (Bm1 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => Bm1
  | t + 1 => fun ω => ((1 - γ) * (passiveDebt β γ shat P Bm1 t ω / P t ω) - shat t ω) /
      (β * 𝔼.E t (fun ω' => 1 / P (t + 1) ω') ω)

/-- Cochrane (2023), §1.9, p. 19 (**passive policy: every price path is an equilibrium**): for
`0 < γ < 2`, `0 < β < 1`, bounded adapted `ŝ`, any initial debt `B_{−1}` known at 0 and any
positive adapted price process `P`, the debt policy `passiveDebt` makes `P` an equilibrium of
the rule (`ExpectationSystem.PullOut`). -/
theorem passive_every_price (hPO : 𝔼.PullOut) {β γ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {shat : ℕ → Ω → ℝ} (hs : ∀ t ω, |shat t ω| ≤ M)
    (hsa : 𝔼.Adapted shat) {Bm1 : Ω → ℝ} (hB1 : Known 𝔼 0 Bm1) {P : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) (hPa : 𝔼.Adapted P) :
    DebtKnown 𝔼 (passiveDebt 𝔼 β γ shat P Bm1) ∧
      RuleEqm 𝔼 β γ shat (passiveDebt 𝔼 β γ shat P Bm1) P
        (fun t => β • 𝔼.E t (P t / P (t + 1))) := by
  set Bm := passiveDebt 𝔼 β γ shat P Bm1 with hBm
  have hden : ∀ t ω, 0 < β * 𝔼.E t (fun ω' => 1 / P (t + 1) ω') ω := fun t ω =>
    mul_pos hβ0 (E_pos_of_pos 𝔼 (fun ω' => one_div_pos.mpr (hP (t + 1) ω')) t ω)
  have hstep : ∀ t, Bm (t + 1) = ((1 - γ) • (Bm t / P t) - shat t) /
      (β • 𝔼.E t (fun ω' => 1 / P (t + 1) ω')) := fun t => by
    funext ω; rfl
  have hknown : ∀ t, Known 𝔼 t (Bm t) := by
    intro t
    induction t with
    | zero => exact hB1
    | succ t ih =>
      have hnum : Known 𝔼 t ((1 - γ) • (Bm t / P t) - shat t) :=
        known_sub 𝔼 (known_smul 𝔼 _ (known_div 𝔼 hPO ih (hPa t) fun ω => (hP t ω).ne'))
          (hsa t)
      have hd : Known 𝔼 t (β • 𝔼.E t (fun ω' => 1 / P (t + 1) ω')) :=
        known_smul 𝔼 β (known_E 𝔼 t _)
      have hk := known_div 𝔼 hPO hnum hd fun ω => (hden t ω).ne'
      rw [← hstep t] at hk
      exact known_mono 𝔼 (Nat.le_succ t) hk
  have hB : DebtKnown 𝔼 Bm := ⟨hknown 0, fun t => by
    have hnum : Known 𝔼 t ((1 - γ) • (Bm t / P t) - shat t) :=
      known_sub 𝔼 (known_smul 𝔼 _ (known_div 𝔼 hPO (hknown t) (hPa t)
        fun ω => (hP t ω).ne')) (hsa t)
    have hd : Known 𝔼 t (β • 𝔼.E t (fun ω' => 1 / P (t + 1) ω')) :=
      known_smul 𝔼 β (known_E 𝔼 t _)
    have hk := known_div 𝔼 hPO hnum hd fun ω => (hden t ω).ne'
    rwa [← hstep t] at hk⟩
  -- the rule recursion
  have hrec : ∀ t, realDebt Bm P t =
      ruleSurplus γ shat Bm P t + β • 𝔼.E t (realDebt Bm P (t + 1)) := by
    intro t
    have hEv : 𝔼.E t (realDebt Bm P (t + 1)) =
        Bm (t + 1) * 𝔼.E t (fun ω' => 1 / P (t + 1) ω') := by
      rw [← hPO t _ _ (hB.2 t)]
      congr 1
      funext ω
      simp only [realDebt, Pi.mul_apply, Pi.div_apply]
      ring
    rw [hEv]
    funext ω
    have hd := (hden t ω).ne'
    have hdE : 𝔼.E t (fun ω' => 1 / P (t + 1) ω') ω ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hd; exact hd rfl
    simp only [ruleSurplus, realDebt, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul,
      Pi.div_apply]
    rw [hstep t]
    simp only [Pi.div_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hrec' : ∀ t, (1 - γ) • realDebt Bm P t = shat t + β • 𝔼.E t (realDebt Bm P (t + 1)) :=
    fun t => by
      funext ω
      have e := congrFun (hrec t) ω
      simp only [ruleSurplus, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
      linarith
  have hQ : ∀ t, BondPrice 𝔼 β P (fun t => β • 𝔼.E t (P t / P (t + 1))) t := fun _ => rfl
  refine ⟨hB, hP, hPa, fun t => flow_of_rec 𝔼 hPO hP hPa hB t (hQ t) (hrec t), hQ, ?_⟩
  exact passive_tvc 𝔼 hβ0 hβ1 hγ0 hγ2 hs hrec'

/-- Cochrane (2023), §1.9, p. 19 (**passive policy is indeterminate**): for `0 < γ < 2`, every
`P₀ > 0` is the date-0 price level of an equilibrium of the rule, from any initial debt
`B_{−1}` known at 0 (`ExpectationSystem.PullOut`). -/
theorem passive_indeterminate (hPO : 𝔼.PullOut) {β γ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {shat : ℕ → Ω → ℝ} (hs : ∀ t ω, |shat t ω| ≤ M)
    (hsa : 𝔼.Adapted shat) {Bm1 : Ω → ℝ} (hB1 : Known 𝔼 0 Bm1) {p0 : ℝ} (hp0 : 0 < p0) :
    ∃ Bm P Q : ℕ → Ω → ℝ, Bm 0 = Bm1 ∧ DebtKnown 𝔼 Bm ∧ RuleEqm 𝔼 β γ shat Bm P Q ∧
      P 0 = fun _ => p0 := by
  have h := passive_every_price 𝔼 hPO hβ0 hβ1 hγ0 hγ2 hs hsa hB1 (P := fun _ _ => p0)
    (fun _ _ => hp0) (fun t => 𝔼.const t p0)
  exact ⟨_, _, _, rfl, h.1, h.2, rfl⟩

/-! ### Active rules: `γ ≤ 0` or `γ ≥ 2` -/

/-- Cochrane (2023), §1.9, p. 19 (**active policy, infinite horizon**): for `γ ≤ 0` or `γ ≥ 2`,
`0 < β < 1` and bounded adapted `ŝ`, an adapted solution of `(1 − γ)v_t = ŝ_t + βE_t v_{t+1}`
satisfies the transversality condition iff `v = ruleF`, the forward value
`∑_j (β/(1 − γ))^j E_t[ŝ_{t+j}/(1 − γ)]`. -/
theorem active_tvc_iff {β γ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : γ ≤ 0 ∨ 2 ≤ γ)
    {shat v : ℕ → Ω → ℝ} (hs : ∀ t ω, |shat t ω| ≤ M) (hsa : 𝔼.Adapted shat)
    (hv : ∀ t, (1 - γ) • v t = shat t + β • 𝔼.E t (v (t + 1))) :
    (∀ t ω, Tendsto (fun T : ℕ => β ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 0)) ↔
      v = ruleF 𝔼 β γ shat := by
  have hc : 1 ≤ |1 - γ| := by
    rcases hγ with h | h
    · rw [abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonpos (by linarith)]; linarith
  have hc0 : (1 - γ) ≠ 0 := fun h => by rw [h, abs_zero] at hc; linarith
  set c := 1 - γ with hcdef
  set a := β / c with ha
  have hcpos : 0 < |c| := lt_of_lt_of_le one_pos hc
  have ha1 : |a| < 1 := by
    rw [ha, abs_div, abs_of_pos hβ0, div_lt_one hcpos]; linarith
  set u : ℕ → Ω → ℝ := fun t => c⁻¹ • shat t with hu
  have huM : ∀ t ω, |u t ω| ≤ |c|⁻¹ * M := fun t ω => by
    simp only [hu, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv]
    exact mul_le_mul_of_nonneg_left (hs t ω) (inv_nonneg.mpr (abs_nonneg _))
  have hua : 𝔼.Adapted u := fun t => by simp only [hu, map_smul, hsa t]
  set F := ruleF 𝔼 β γ shat with hF
  have hFsol : Solves 𝔼 a u F := forwardSeries_solves_abs 𝔼 ha1 huM hua
  obtain ⟨MF, hMF⟩ := forwardSeries_bounded_abs 𝔼 ha1 huM
  -- the difference solves the homogeneous forward equation
  set z : ℕ → Ω → ℝ := fun t => v t - F t with hz
  have hzrec : ∀ t, z t = a • 𝔼.E t (z (t + 1)) := by
    intro t
    have h1 := hv t
    have h2 := hFsol t
    funext ω
    have e1 := congrFun h1 ω
    have e2 := congrFun h2 ω
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, hu] at e1 e2
    simp only [hz, Pi.smul_apply, smul_eq_mul, map_sub, Pi.sub_apply]
    rw [e2, ha]
    field_simp
    linear_combination e1
  -- `β^T E_t v_{t+T} = c^T z_t + β^T E_t F_{t+T}`
  have hdecomp : ∀ t T ω, β ^ T * 𝔼.E t (v (t + T)) ω =
      c ^ T * z t ω + β ^ T * 𝔼.E t (F (t + T)) ω := by
    intro t T ω
    have hit := congrFun (𝔼.forward_iterate hzrec t T) ω
    simp only [Pi.smul_apply, smul_eq_mul] at hit
    have hEz : 𝔼.E t (z (t + T)) ω = 𝔼.E t (v (t + T)) ω - 𝔼.E t (F (t + T)) ω := by
      simp only [hz, map_sub, Pi.sub_apply]
    rw [hEz, ha, div_pow] at hit
    have hcT : c ^ T ≠ 0 := pow_ne_zero T hc0
    rw [hit]
    field_simp
    ring
  have hFlim : ∀ t ω, Tendsto (fun T : ℕ => β ^ T * 𝔼.E t (F (t + T)) ω) atTop (𝓝 0) := by
    intro t ω
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm (a := fun T => β ^ T * MF) (fun T => ?_) ?_
    · rw [sub_zero, norm_norm, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hβ0]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hMF (t + T)) t ω) (pow_nonneg hβ0.le T)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const MF
  constructor
  · intro hT
    funext t ω
    have h1 : Tendsto (fun T : ℕ => c ^ T * z t ω) atTop (𝓝 0) := by
      have := (hT t ω).sub (hFlim t ω)
      simp only [sub_zero] at this
      refine this.congr fun T => ?_
      rw [hdecomp]; ring
    by_contra hne
    have hz0 : z t ω ≠ 0 := fun h => hne (by simp only [hz, Pi.sub_apply] at h; linarith)
    have hge : ∀ T : ℕ, |z t ω| ≤ |c ^ T * z t ω| := fun T => by
      rw [abs_mul, abs_pow]
      exact le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ hc)
    have hlim0 := h1.abs
    simp only [abs_zero] at hlim0
    have := ge_of_tendsto' hlim0 hge
    exact hz0 (abs_nonpos_iff.mp this)
  · intro hvF t ω
    have hz0 : z t ω = 0 := by simp only [hz, hvF, sub_self, Pi.zero_apply]
    refine (hFlim t ω).congr fun T => ?_
    rw [hdecomp, hz0, mul_zero, zero_add]

/-- Cochrane (2023), §1.9, p. 19 (**active policy determines the price level**): for `γ ≤ 0`
or `γ ≥ 2`, `0 < β < 1`, bounded adapted `ŝ`, known debt and `ExpectationSystem.PullOut`, every
rule equilibrium
has `B_{t−1}/P_t = ruleF_t` at every date. -/
theorem active_valuation (hPO : 𝔼.PullOut) {β γ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : γ ≤ 0 ∨ 2 ≤ γ) {shat Bm P Q : ℕ → Ω → ℝ} (hs : ∀ t ω, |shat t ω| ≤ M)
    (hsa : 𝔼.Adapted shat) (hB : DebtKnown 𝔼 Bm) (he : RuleEqm 𝔼 β γ shat Bm P Q) :
    realDebt Bm P = ruleF 𝔼 β γ shat :=
  (active_tvc_iff 𝔼 hβ0 hβ1 hγ hs hsa (rule_rec 𝔼 hPO hB he)).mp he.2.2.2.2

/-- Cochrane (2023), §1.9, p. 19 (**active policy, existence and uniqueness**): for `γ ≤ 0` or
`γ ≥ 2`, `0 < β < 1`, bounded adapted `ŝ`, a positive known debt policy and a positive forward
value `ruleF`, there is exactly one rule equilibrium, `P_t = B_{t−1}/ruleF_t`
(`ExpectationSystem.PullOut`). -/
theorem active_existsUnique (hPO : 𝔼.PullOut) {β γ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : γ ≤ 0 ∨ 2 ≤ γ) {shat Bm : ℕ → Ω → ℝ} (hs : ∀ t ω, |shat t ω| ≤ M)
    (hsa : 𝔼.Adapted shat) (hBpos : ∀ t ω, 0 < Bm t ω) (hB : DebtKnown 𝔼 Bm)
    (hFpos : ∀ t ω, 0 < ruleF 𝔼 β γ shat t ω) :
    ∃! x : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), RuleEqm 𝔼 β γ shat Bm x.1 x.2 := by
  have hc : 1 ≤ |1 - γ| := by
    rcases hγ with h | h
    · rw [abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonpos (by linarith)]; linarith
  have hc0 : (1 - γ) ≠ 0 := fun h => by rw [h, abs_zero] at hc; linarith
  have hcpos : 0 < |1 - γ| := lt_of_lt_of_le one_pos hc
  have ha1 : |β / (1 - γ)| < 1 := by
    rw [abs_div, abs_of_pos hβ0, div_lt_one hcpos]; linarith
  have huM : ∀ t ω, |((1 - γ)⁻¹ • shat t) ω| ≤ |1 - γ|⁻¹ * M := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv]
    exact mul_le_mul_of_nonneg_left (hs t ω) (inv_nonneg.mpr (abs_nonneg _))
  have hua : 𝔼.Adapted (fun t => (1 - γ)⁻¹ • shat t) := fun t => by simp only [map_smul, hsa t]
  set F := ruleF 𝔼 β γ shat with hF
  have hFa : 𝔼.Adapted F := forwardSeries_adapted_abs 𝔼 ha1 huM
  have hFsol : Solves 𝔼 (β / (1 - γ)) (fun t => (1 - γ)⁻¹ • shat t) F :=
    forwardSeries_solves_abs 𝔼 ha1 huM hua
  set P : ℕ → Ω → ℝ := fun t => Bm t / F t with hPdef
  set Q : ℕ → Ω → ℝ := fun t => β • 𝔼.E t (P t / P (t + 1)) with hQdef
  have hP : ∀ t ω, 0 < P t ω := fun t ω => div_pos (hBpos t ω) (hFpos t ω)
  have hPa : 𝔼.Adapted P := fun t =>
    known_div 𝔼 hPO (debtKnown_at 𝔼 hB t) (hFa t) fun ω => (hFpos t ω).ne'
  have hvF : realDebt Bm P = F := by
    funext t ω
    simp only [realDebt, hPdef, Pi.div_apply]
    field_simp [(hFpos t ω).ne', (hBpos t ω).ne']
  have hrec' : ∀ t, (1 - γ) • realDebt Bm P t = shat t + β • 𝔼.E t (realDebt Bm P (t + 1)) := by
    intro t
    rw [hvF]
    funext ω
    have e := congrFun (hFsol t) ω
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at e ⊢
    rw [e]
    field_simp
    ring
  have hrec : ∀ t, realDebt Bm P t =
      ruleSurplus γ shat Bm P t + β • 𝔼.E t (realDebt Bm P (t + 1)) := fun t => by
    have h := hrec' t
    funext ω
    have e := congrFun h ω
    simp only [ruleSurplus, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at e ⊢
    linarith
  have hQ : ∀ t, BondPrice 𝔼 β P Q t := fun _ => rfl
  have heq : RuleEqm 𝔼 β γ shat Bm P Q :=
    ⟨hP, hPa, fun t => flow_of_rec 𝔼 hPO hP hPa hB t (hQ t) (hrec t), hQ,
      (active_tvc_iff 𝔼 hβ0 hβ1 hγ hs hsa hrec').mpr hvF⟩
  refine ⟨(P, Q), heq, ?_⟩
  rintro ⟨P', Q'⟩ h'
  have hv' := active_valuation 𝔼 hPO hβ0 hβ1 hγ hs hsa hB h'
  have hPP : P' = P := by
    funext t ω
    have e := congrFun (congrFun hv' t) ω
    simp only [realDebt, Pi.div_apply] at e
    have e2 : F t ω = Bm t ω / P' t ω := e.symm
    simp only [hPdef, Pi.div_apply]
    rw [e2]
    field_simp [(h'.1 t ω).ne', (hBpos t ω).ne']
  have hQQ : Q' = Q := by
    funext t
    have h1 : Q' t = β • 𝔼.E t (P' t / P' (t + 1)) := h'.2.2.2.1 t
    rw [h1, hPP]
  exact Prod.ext hPP hQQ

/-! ### Determinacy of the date-0 price level -/

/-- Cochrane (2023), §1.9, p. 19, infinite horizon: **`P₀` is determined iff `γ ≤ 0` or
`γ ≥ 2`.** For `0 < β < 1`, bounded adapted `ŝ`, a nonempty state space,
`ExpectationSystem.PullOut` and an
initial debt `B_{−1}` known at 0 and nowhere zero: all rule equilibria starting from `B_{−1}`
(with any known debt policy) have the same `P₀` iff `γ ≤ 0` or `γ ≥ 2`. -/
theorem determinate0_iff [Nonempty Ω] (hPO : 𝔼.PullOut) {β γ M : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) {shat : ℕ → Ω → ℝ} (hs : ∀ t ω, |shat t ω| ≤ M) (hsa : 𝔼.Adapted shat)
    {Bm1 : Ω → ℝ} (hB1 : Known 𝔼 0 Bm1) (hB10 : ∀ ω, Bm1 ω ≠ 0) :
    (∀ Bm P Q Bm' P' Q' : ℕ → Ω → ℝ, Bm 0 = Bm1 → Bm' 0 = Bm1 → DebtKnown 𝔼 Bm →
      DebtKnown 𝔼 Bm' → RuleEqm 𝔼 β γ shat Bm P Q → RuleEqm 𝔼 β γ shat Bm' P' Q' →
        P 0 = P' 0) ↔ (γ ≤ 0 ∨ 2 ≤ γ) := by
  constructor
  · intro h
    by_contra hγ
    push Not at hγ
    obtain ⟨Bm, P, Q, h0, hB, he, hP0⟩ :=
      passive_indeterminate 𝔼 hPO hβ0 hβ1 hγ.1 hγ.2 hs hsa hB1 (p0 := 1) one_pos
    obtain ⟨Bm', P', Q', h0', hB', he', hP0'⟩ :=
      passive_indeterminate 𝔼 hPO hβ0 hβ1 hγ.1 hγ.2 hs hsa hB1 (p0 := 2) two_pos
    have := congrFun (h Bm P Q Bm' P' Q' h0 h0' hB hB' he he') (Classical.arbitrary Ω)
    rw [hP0, hP0'] at this
    norm_num at this
  · intro hγ Bm P Q Bm' P' Q' h0 h0' hB hB' he he'
    have hv := congrFun (active_valuation 𝔼 hPO hβ0 hβ1 hγ hs hsa hB he) 0
    have hv' := congrFun (active_valuation 𝔼 hPO hβ0 hβ1 hγ hs hsa hB' he') 0
    funext ω
    have e := congrFun hv ω
    have e' := congrFun hv' ω
    simp only [realDebt, Pi.div_apply, h0, h0'] at e e'
    have hP := (he.1 0 ω).ne'
    have hP' := (he'.1 0 ω).ne'
    rw [← e'] at e
    rw [div_eq_div_iff hP hP'] at e
    exact (mul_left_cancel₀ (hB10 ω) (by linarith : Bm1 ω * P' 0 ω = Bm1 ω * P 0 ω)).symm

/-- Cochrane (2023), p. 19 (**correction of "`γ > 0` in the later intertemporal model"
indicates passive policy**): `γ = 3 > 0` is active. Under perfect foresight with constant debt
`B_{t−1} = 1`, `ŝ = −1` (the rule `s_t = 3B_{t−1}/P_t − 1`) and `0 < β < 1`, there is exactly
one equilibrium, and in it `P_t = 2 + β` at every date. -/
theorem gamma_three_active {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∃! x : (ℕ → Unit → ℝ) × (ℕ → Unit → ℝ),
      RuleEqm perfectForesight β 3 (fun _ _ => -1) (fun _ _ => 1) x.1 x.2) ∧
    ∀ P Q : ℕ → Unit → ℝ, RuleEqm perfectForesight β 3 (fun _ _ => -1) (fun _ _ => 1) P Q →
      ∀ t, P t () = 2 + β := by
  have hβ : |β / (1 - 3)| < 1 := by
    rw [abs_div, abs_of_pos hβ0]; norm_num; linarith
  have hF : ∀ t, ruleF perfectForesight β 3 (fun _ _ => -1) t () = 1 / (2 + β) := by
    intro t
    simp only [ruleF, ExpectationSystem.forwardSeries]
    have h1 : ∀ k : ℕ, (β / (1 - 3)) ^ k * perfectForesight.E t
        ((fun t : ℕ => ((1 : ℝ) - 3)⁻¹ • (fun (_ : ℕ) (_ : Unit) => (-1 : ℝ)) t) (t + k)) () =
          (β / (1 - 3)) ^ k * (1 / 2) := by
      intro k
      simp only [perfectForesight, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul]
      norm_num
    rw [tsum_congr h1, tsum_mul_right, tsum_geometric_of_abs_lt_one hβ]
    have hne : (2 + β : ℝ) ≠ 0 := by linarith
    have e : (1 : ℝ) - β / (1 - 3) = (2 + β) / 2 := by ring
    rw [e]
    field_simp
  have hFpos : ∀ t ω, 0 < ruleF perfectForesight β 3 (fun _ _ => -1) t ω := by
    intro t ω
    rw [hF t]
    positivity
  have hB : DebtKnown perfectForesight (fun _ _ => (1 : ℝ)) :=
    ⟨rfl, fun _ => rfl⟩
  have hs : ∀ (t : ℕ) (ω : Unit), |((fun _ _ => (-1 : ℝ)) : ℕ → Unit → ℝ) t ω| ≤ 1 :=
    fun _ _ => by norm_num
  refine ⟨active_existsUnique perfectForesight perfectForesight_pullOut hβ0 hβ1
    (Or.inr (by norm_num)) hs (fun _ => rfl) (fun _ _ => one_pos) hB hFpos, ?_⟩
  intro P Q he t
  have hv := congrFun (congrFun (active_valuation perfectForesight perfectForesight_pullOut
    hβ0 hβ1 (Or.inr (by norm_num)) hs (fun _ => rfl) hB he) t) ()
  rw [hF t] at hv
  simp only [realDebt, Pi.div_apply] at hv
  have hP := (he.1 t ()).ne'
  rw [div_eq_div_iff hP (by positivity)] at hv
  linarith

end Cochrane.TwoPeriodModel.TidyR6InfiniteActivePassive
