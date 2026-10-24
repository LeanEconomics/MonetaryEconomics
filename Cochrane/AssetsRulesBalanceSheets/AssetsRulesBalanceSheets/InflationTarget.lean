/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.ExpectationsFiniteTree
import AssetsRulesBalanceSheets.PresentValue
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# A simple model of an inflation target

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.2
"A simple model of an inflation target", eqs. (9.1)–(9.6), pp. 263–264.

The government keeps a state variable `V*_t`, the real value the debt would have if the price
level were always at the target `P*_t` ((9.1)–(9.2)); the surplus repays it,
`s_t = s_{0,t} + α V*_t` (9.4); the central bank sets the bond price consistent with the target,
`Q_t = β E_t (P*_t / P*_{t+1})` (9.5). The book concludes that `P_t = P*_t` is the unique
equilibrium price level.

## Dating convention

Lean date `t` is book date `t + 1`. `B t` is the nominal debt outstanding at the *start* of date
`t` (book `B_{t-1}`), so the one-period flow condition reads `B_t/P_t = s_t + Q_t B_{t+1}/P_t`
and `B (t + 1)` is chosen (known) at date `t`. (9.1) is `V 0 = B 0 / P* 0`.

## Main results

* `eq_9_3`, `eq_9_6`, `eq_9_6_rule`: the book's algebra, under an arbitrary `ExpectationSystem`
  with the pull-out property.
* `tendsto_state_forecast`: `β^T E_t V*_{t+T} → 0` for bounded `s₀` **when `0 < α < 2`**;
  `tendsto_state_forecast_iff`: with `s₀ = 0` this limit is zero iff `0 < α < 2`;
  `tendsto_state_forecast_alpha_zero`: at `α = 0` the limit is `V*_t − E_t ∑ βʲ s_{0,t+j}`.
  The book's claim "for bounded `{s_{0,t}}`" omits the condition `0 < α < 2` (error E9.1).
* `hasSum_state`: `V*_t = E_t ∑ βʲ s_{t+j}` as a genuine absolutely convergent series.
* `realDebt_eq_state`: `B_t/P_t = V*_t` at every date and state.
* `price_eq_target` (**Theorem IT**): `P = P*`. The base step is `P_1 = P*_1` in book dating
  (the book writes `P_0 = P_0^*`, error E9.2) and the induction step needs `V*_t ≠ s_t`;
  `price_eq_target_perfectForesight`: under perfect foresight `V*_t ≠ s_t` is not needed;
  `zero_debt_sunspot`: under genuine uncertainty it is (a coin-flip counterexample).
* `target_alone_insufficient`, `rule_alone_insufficient`: the book's two insufficiency claims
  ("the interest-rate target alone is insufficient", "the surplus rule is also insufficient";
  doubling nominal debt doubles the future price level).
-/

namespace Cochrane.AssetsRulesBalanceSheets.InflationTarget

open Filter Topology

/-! ### A contraction lemma -/

/-- Cochrane (2023), §9.2, p. 264 (the limit `β^T E_t V*_{t+T} → 0`): a sequence obeying
`|x_{T+1} − c x_T| ≤ βᵀ M` is bounded by `mᵀ (|x_0| + T M / m)` with `m = max |c| β`. -/
theorem abs_le_of_contraction {x : ℕ → ℝ} {c β M : ℝ} (hβ : 0 < β) (hM : 0 ≤ M)
    (hx : ∀ T, |x (T + 1) - c * x T| ≤ β ^ T * M) (T : ℕ) :
    |x T| ≤ max |c| β ^ T * (|x 0| + T * M / max |c| β) := by
  set m := max |c| β with hm_def
  have hm : 0 < m := lt_of_lt_of_le hβ (le_max_right _ _)
  induction T with
  | zero => simp
  | succ T ih =>
    have hcm : |c| ≤ m := le_max_left _ _
    have hβm : β ^ T ≤ m ^ T := pow_le_pow_left₀ hβ.le (le_max_right _ _) T
    calc |x (T + 1)| = |(x (T + 1) - c * x T) + c * x T| := by ring_nf
      _ ≤ |x (T + 1) - c * x T| + |c * x T| := abs_add_le _ _
      _ ≤ β ^ T * M + m * (m ^ T * (|x 0| + T * M / m)) := by
          gcongr
          · exact hx T
          · rw [abs_mul]
            exact mul_le_mul hcm ih (abs_nonneg _) hm.le
      _ ≤ m ^ T * M + m * (m ^ T * (|x 0| + T * M / m)) := by gcongr
      _ = m ^ (T + 1) * (|x 0| + ((T + 1 : ℕ) : ℝ) * M / m) := by
          push_cast
          field_simp
          ring

/-- Cochrane (2023), §9.2, p. 264: a sequence obeying `|x_{T+1} − c x_T| ≤ βᵀ M` with `|c| < 1`
and `0 < β < 1` converges to zero. -/
theorem tendsto_zero_of_contraction {x : ℕ → ℝ} {c β M : ℝ} (hc : |c| < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hM : 0 ≤ M) (hx : ∀ T, |x (T + 1) - c * x T| ≤ β ^ T * M) :
    Tendsto x atTop (𝓝 0) := by
  set m := max |c| β with hm_def
  have hm : 0 < m := lt_of_lt_of_le hβ (le_max_right _ _)
  have hm1 : m < 1 := max_lt hc hβ1
  have hlim : Tendsto (fun T : ℕ => m ^ T * |x 0| + (T * m ^ T) * (M / m)) atTop (𝓝 0) := by
    have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hm.le hm1).mul_const |x 0|
    have h2 := (tendsto_self_mul_const_pow_of_lt_one hm.le hm1).mul_const (M / m)
    simpa using h1.add h2
  refine squeeze_zero_norm (fun T => ?_) hlim
  rw [Real.norm_eq_abs]
  refine (abs_le_of_contraction hβ hM hx T).trans (le_of_eq ?_)
  rw [← hm_def]
  field_simp

/-- Cochrane (2023), §9.2, p. 264: a sequence obeying `|x_{T+1} − c x_T| ≤ βᵀ M` with `|c| < 1`
and `0 < β < 1` is absolutely summable. -/
theorem summable_of_contraction {x : ℕ → ℝ} {c β M : ℝ} (hc : |c| < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hM : 0 ≤ M) (hx : ∀ T, |x (T + 1) - c * x T| ≤ β ^ T * M) :
    Summable x := by
  set m := max |c| β with hm_def
  have hm : 0 < m := lt_of_lt_of_le hβ (le_max_right _ _)
  have hm1 : m < 1 := max_lt hc hβ1
  have hg : Summable (fun T : ℕ => m ^ T * |x 0| + ((T : ℝ) ^ 1 * m ^ T) * (M / m)) := by
    refine ((summable_geometric_of_lt_one hm.le hm1).mul_right _).add ?_
    refine (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := m) ?_).mul_right _
    rw [Real.norm_eq_abs, abs_of_pos hm]
    exact hm1
  have hb : ∀ T : ℕ, ‖x T‖ ≤ m ^ T * |x 0| + ((T : ℝ) ^ 1 * m ^ T) * (M / m) := by
    intro T
    rw [Real.norm_eq_abs, pow_one]
    have h := abs_le_of_contraction hβ hM hx T
    rw [← hm_def] at h
    calc |x T| ≤ m ^ T * (|x 0| + T * M / m) := h
      _ = m ^ T * |x 0| + (T * m ^ T) * (M / m) := by ring
  exact Summable.of_norm_bounded hg hb

/-! ### Known random variables under the pull-out property -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §9.2, p. 264 (the book's use of `E_t` on products): under `PullOut`, a
product of two variables known at `t` is known at `t`. -/
theorem known_mul (h𝔼 : 𝔼.PullOut) {t : ℕ} {a b : Ω → ℝ} (ha : 𝔼.E t a = a)
    (hb : 𝔼.E t b = b) : 𝔼.E t (a * b) = a * b := by
  rw [h𝔼 t a b ha, hb]

/-- Cochrane (2023), §9.2, p. 264: under `PullOut`, the reciprocal of a nowhere-zero variable
known at `t` is known at `t`. -/
theorem known_inv (h𝔼 : 𝔼.PullOut) {t : ℕ} {a : Ω → ℝ} (ha : 𝔼.E t a = a)
    (h0 : ∀ ω, a ω ≠ 0) : 𝔼.E t a⁻¹ = a⁻¹ := by
  have h1 := h𝔼 t a a⁻¹ ha
  have hone : a * a⁻¹ = fun _ => (1 : ℝ) := by
    funext ω
    simp only [Pi.mul_apply, Pi.inv_apply]
    exact mul_inv_cancel₀ (h0 ω)
  rw [hone, 𝔼.const] at h1
  funext ω
  have h2 : (1 : ℝ) = a ω * 𝔼.E t a⁻¹ ω := congrFun h1 ω
  have ha0 := h0 ω
  change 𝔼.E t a⁻¹ ω = (a ω)⁻¹
  calc 𝔼.E t a⁻¹ ω = (a ω)⁻¹ * (a ω * 𝔼.E t a⁻¹ ω) := by field_simp
    _ = (a ω)⁻¹ := by rw [← h2, mul_one]

/-- Cochrane (2023), §9.2, p. 264: under `PullOut`, a ratio of variables known at `t` (nowhere
zero denominator) is known at `t`. -/
theorem known_div (h𝔼 : 𝔼.PullOut) {t : ℕ} {a b : Ω → ℝ} (ha : 𝔼.E t a = a)
    (hb : 𝔼.E t b = b) (h0 : ∀ ω, b ω ≠ 0) : 𝔼.E t (a / b) = a / b := by
  rw [div_eq_mul_inv]
  exact known_mul 𝔼 h𝔼 ha (known_inv 𝔼 h𝔼 hb h0)

/-! ### The model -/

/-- Cochrane (2023), eq. (9.1), p. 263: the target state starts at `V*_1 = B_0 / P*_1`
(Lean date `0` is book date `1`). -/
def StateInit (B Pstar V : ℕ → Ω → ℝ) : Prop := V 0 = B 0 / Pstar 0

/-- Cochrane (2023), eq. (9.2), p. 263: `V*_{t+1} = (1/Q_t)(P*_t/P*_{t+1})(V*_t − s_t)`, the
real debt accumulated at the price-level target, with bond price `Q`. -/
def StateRec (Q Pstar s V : ℕ → Ω → ℝ) : Prop :=
  ∀ t, V (t + 1) = (Q t)⁻¹ * (Pstar t / Pstar (t + 1)) * (V t - s t)

/-- Cochrane (2023), eq. (9.4), p. 263: the surplus rule `s_t = s_{0,t} + α V*_t`. -/
def SurplusRule (α : ℝ) (s0 V s : ℕ → Ω → ℝ) : Prop := ∀ t, s t = s0 t + α • V t

/-- Cochrane (2023), eq. (9.5), p. 264: the interest-rate target `Q_t = β E_t (P*_t/P*_{t+1})`. -/
def RateTarget (β : ℝ) (Pstar Q : ℕ → Ω → ℝ) : Prop :=
  ∀ t, Q t = β • 𝔼.E t (Pstar t / Pstar (t + 1))

variable (β : ℝ) (B P Q s : ℕ → Ω → ℝ)

/-- Cochrane (2023), §9.2, p. 263 (and §3.1 for the frictionless economy): the private-sector
equilibrium conditions with one-period nominal debt — positive prices, adapted variables, debt
`B_{t+1}` chosen at `t`, the flow condition `B_t/P_t = s_t + Q_t B_{t+1}/P_t`, bond pricing with a
constant real rate `Q_t = β E_t (P_t/P_{t+1})`, and the transversality condition
`β^T E_t (B_{t+T}/P_{t+T}) → 0`. -/
structure Economy where
  pos_P : ∀ t ω, 0 < P t ω
  pos_Q : ∀ t ω, 0 < Q t ω
  adapted_P : 𝔼.Adapted P
  adapted_Q : 𝔼.Adapted Q
  known_B0 : 𝔼.E 0 (B 0) = B 0
  predetermined_B : ∀ t, 𝔼.E t (B (t + 1)) = B (t + 1)
  flow : ∀ t, B t / P t = s t + Q t * B (t + 1) / P t
  pricing : ∀ t, Q t = β • 𝔼.E t (P t / P (t + 1))
  tvc : ∀ t ω, Tendsto (fun T => β ^ T * 𝔼.E t (B (t + T) / P (t + T)) ω) atTop (𝓝 0)

variable {𝔼 β B P Q s}

/-- Cochrane (2023), eq. (9.3), p. 263: the flow condition rearranged,
`B_{t+1}/P_{t+1} = (1/Q_t)(P_t/P_{t+1})(B_t/P_t − s_t)`. -/
theorem eq_9_3 (hE : Economy 𝔼 β B P Q s) (t : ℕ) :
    B (t + 1) / P (t + 1) = (Q t)⁻¹ * (P t / P (t + 1)) * (B t / P t - s t) := by
  funext ω
  have h := congrFun (hE.flow t) ω
  simp only [Pi.div_apply, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.inv_apply] at h ⊢
  have hP := (hE.pos_P t ω).ne'
  have hP1 := (hE.pos_P (t + 1) ω).ne'
  have hQ := (hE.pos_Q t ω).ne'
  rw [h]
  field_simp
  ring

/-- Cochrane (2023), §9.2, p. 264: the target state `V*` is adapted (known at each date). -/
theorem state_adapted (h𝔼 : 𝔼.PullOut) {α : ℝ} {Pstar s0 V : ℕ → Ω → ℝ}
    (hQ : ∀ t ω, 0 < Q t ω) (hQa : 𝔼.Adapted Q) (hPs : ∀ t ω, 0 < Pstar t ω)
    (hPsa : 𝔼.Adapted Pstar) (hs0a : 𝔼.Adapted s0) (hB0 : 𝔼.E 0 (B 0) = B 0)
    (h91 : StateInit B Pstar V) (h92 : StateRec Q Pstar s V) (h94 : SurplusRule α s0 V s) :
    𝔼.Adapted V := by
  intro t
  induction t with
  | zero =>
    rw [h91]
    exact known_div 𝔼 h𝔼 hB0 (hPsa 0) (fun ω => (hPs 0 ω).ne')
  | succ t ih =>
    have hup : ∀ {x : Ω → ℝ}, 𝔼.E t x = x → 𝔼.E (t + 1) x = x :=
      fun hx => ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) hx
    have hs : 𝔼.E t (s t) = s t := by
      rw [h94 t, map_add, map_smul, hs0a t, ih]
    rw [h92 t]
    refine known_mul 𝔼 h𝔼 (known_mul 𝔼 h𝔼 ?_ ?_) ?_
    · exact known_inv 𝔼 h𝔼 (hup (hQa t)) (fun ω => (hQ t ω).ne')
    · exact known_div 𝔼 h𝔼 (hup (hPsa t)) (hPsa (t + 1)) (fun ω => (hPs (t + 1) ω).ne')
    · rw [map_sub, hup ih, hup hs]

/-- Cochrane (2023), eq. (9.6), p. 264: substituting the target (9.5) into (9.2),
`β E_t V*_{t+1} = V*_t − s_t`. -/
theorem eq_9_6 (h𝔼 : 𝔼.PullOut) (hβ : β ≠ 0) {Pstar V : ℕ → Ω → ℝ}
    (hQ : ∀ t ω, 0 < Q t ω) (hVa : 𝔼.Adapted V)
    (hQa : 𝔼.Adapted Q) (hsa : 𝔼.Adapted s) (h92 : StateRec Q Pstar s V)
    (h95 : RateTarget 𝔼 β Pstar Q) (t : ℕ) :
    β • 𝔼.E t (V (t + 1)) = V t - s t := by
  have hk : 𝔼.E t ((Q t)⁻¹ * (V t - s t)) = (Q t)⁻¹ * (V t - s t) := by
    refine known_mul 𝔼 h𝔼 (known_inv 𝔼 h𝔼 (hQa t) (fun ω => (hQ t ω).ne')) ?_
    rw [map_sub, hVa t, hsa t]
  have hV : V (t + 1) = ((Q t)⁻¹ * (V t - s t)) * (Pstar t / Pstar (t + 1)) := by
    rw [h92 t]
    ring
  rw [hV, h𝔼 t _ _ hk]
  funext ω
  have hT := congrFun (h95 t) ω
  simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.inv_apply, Pi.sub_apply] at hT ⊢
  have hQ0 := (hQ t ω).ne'
  have hE : 𝔼.E t (Pstar t / Pstar (t + 1)) ω = Q t ω / β := by
    rw [hT]
    field_simp
  rw [hE]
  field_simp

/-- Cochrane (2023), §9.2, p. 264 (display after (9.6)): with the rule (9.4),
`β E_t V*_{t+1} = (1 − α) V*_t − s_{0,t}`. -/
theorem eq_9_6_rule (h𝔼 : 𝔼.PullOut) (hβ : β ≠ 0) {α : ℝ} {Pstar s0 V : ℕ → Ω → ℝ}
    (hQ : ∀ t ω, 0 < Q t ω) (hVa : 𝔼.Adapted V)
    (hQa : 𝔼.Adapted Q) (hsa : 𝔼.Adapted s) (h92 : StateRec Q Pstar s V)
    (h94 : SurplusRule α s0 V s) (h95 : RateTarget 𝔼 β Pstar Q) (t : ℕ) :
    β • 𝔼.E t (V (t + 1)) = (1 - α) • V t - s0 t := by
  rw [eq_9_6 h𝔼 hβ hQ hVa hQa hsa h92 h95 t, h94 t]
  funext ω
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), §9.2, p. 264: the forecasts `x_T = βᵀ E_t V*_{t+T}` obey
`x_{T+1} = (1 − α) x_T − βᵀ E_t s_{0,t+T}`. -/
theorem state_forecast_succ {α : ℝ} {s0 V : ℕ → Ω → ℝ}
    (h6 : ∀ t, β • 𝔼.E t (V (t + 1)) = (1 - α) • V t - s0 t) (t T : ℕ) (ω : Ω) :
    β ^ (T + 1) * 𝔼.E t (V (t + (T + 1))) ω =
      (1 - α) * (β ^ T * 𝔼.E t (V (t + T)) ω) - β ^ T * 𝔼.E t (s0 (t + T)) ω := by
  have key := congrArg (𝔼.E t) (h6 (t + T))
  rw [map_smul, 𝔼.tower (Nat.le_add_right t T), map_sub, map_smul] at key
  have h := congrFun key ω
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h
  rw [show t + (T + 1) = t + T + 1 by ring, pow_succ]
  linear_combination (β ^ T) * h

/-- Cochrane (2023), §9.2, p. 264 (corrected, error E9.1): for bounded `{s_{0,t}}` and
**`0 < α < 2`**, `lim_T βᵀ E_t V*_{t+T} = 0`. -/
theorem tendsto_state_forecast (hβ0 : 0 < β) (hβ1 : β < 1) {α M : ℝ} (hα0 : 0 < α)
    (hα2 : α < 2) {s0 V : ℕ → Ω → ℝ} (hM : ∀ t ω, |s0 t ω| ≤ M)
    (h6 : ∀ t, β • 𝔼.E t (V (t + 1)) = (1 - α) • V t - s0 t) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => β ^ T * 𝔼.E t (V (t + T)) ω) atTop (𝓝 0) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ω)
  have hc : |1 - α| < 1 := by rw [abs_lt]; constructor <;> linarith
  refine tendsto_zero_of_contraction hc hβ0 hβ1 hM0 (fun T => ?_)
  rw [state_forecast_succ h6 t T ω]
  rw [show (1 - α) * (β ^ T * 𝔼.E t (V (t + T)) ω) - β ^ T * 𝔼.E t (s0 (t + T)) ω -
      (1 - α) * (β ^ T * 𝔼.E t (V (t + T)) ω) = -(β ^ T * 𝔼.E t (s0 (t + T)) ω) by ring,
    abs_neg, abs_mul, abs_of_pos (pow_pos hβ0 T)]
  exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hM (t + T)) t ω) (pow_pos hβ0 T).le

/-- Cochrane (2023), §9.2, p. 264: with `s₀ = 0` the forecasts are
`βᵀ E_t V*_{t+T} = (1 − α)ᵀ V*_t`. -/
theorem state_forecast_of_s0_zero {α : ℝ} {V : ℕ → Ω → ℝ} (hVa : 𝔼.Adapted V)
    (h6 : ∀ t, β • 𝔼.E t (V (t + 1)) = (1 - α) • V t - 0) (t T : ℕ) (ω : Ω) :
    β ^ T * 𝔼.E t (V (t + T)) ω = (1 - α) ^ T * V t ω := by
  induction T with
  | zero => simp [hVa t]
  | succ T ih =>
    have h := state_forecast_succ (s0 := fun _ => 0) h6 t T ω
    rw [h, ih]
    have h0 : 𝔼.E t (fun _ : Ω => (0 : ℝ)) = fun _ => 0 := 𝔼.const t 0
    simp only [map_zero, Pi.zero_apply, mul_zero, sub_zero]
    ring

/-- Cochrane (2023), §9.2, p. 264 (error E9.1, necessity and sufficiency): with `s₀ = 0` and
`V*_t ≠ 0`, `βᵀ E_t V*_{t+T} → 0` holds if and only if `0 < α < 2`. -/
theorem tendsto_state_forecast_iff {α : ℝ} {V : ℕ → Ω → ℝ} (hVa : 𝔼.Adapted V)
    (h6 : ∀ t, β • 𝔼.E t (V (t + 1)) = (1 - α) • V t - 0) (t : ℕ) (ω : Ω) (hV : V t ω ≠ 0) :
    Tendsto (fun T => β ^ T * 𝔼.E t (V (t + T)) ω) atTop (𝓝 0) ↔ 0 < α ∧ α < 2 := by
  have hx := state_forecast_of_s0_zero hVa h6 t
  simp_rw [hx]
  constructor
  · intro h
    by_contra hα
    have hc : 1 ≤ |1 - α| := by
      rcases not_and_or.mp hα with h1 | h1
      · rw [abs_of_nonneg (by linarith [not_lt.mp h1])]
        linarith [not_lt.mp h1]
      · rw [abs_of_nonpos (by linarith [not_lt.mp h1])]
        linarith [not_lt.mp h1]
    have hlow : ∀ T : ℕ, |V t ω| ≤ |(1 - α) ^ T * V t ω| := fun T => by
      rw [abs_mul, abs_pow]
      exact le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ hc)
    have habs := h.abs
    rw [abs_zero] at habs
    have : |V t ω| ≤ 0 := ge_of_tendsto' habs hlow
    exact hV (abs_nonpos_iff.mp this)
  · rintro ⟨h0, h2⟩
    have hc : |1 - α| < 1 := by rw [abs_lt]; constructor <;> linarith
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hc).mul_const (V t ω)

/-- Cochrane (2023), §9.2, p. 264 (error E9.1): at `α = 0` the limit of `βᵀ E_t V*_{t+T}` is
`V*_t − ∑ⱼ βʲ E_t s_{0,t+j}`, which is not zero unless `V*_t` happens to equal the present
value of `s₀`. -/
theorem tendsto_state_forecast_alpha_zero (hβ0 : 0 < β) (hβ1 : β < 1) {M : ℝ}
    {s0 V : ℕ → Ω → ℝ} (hM : ∀ t ω, |s0 t ω| ≤ M) (hVa : 𝔼.Adapted V)
    (h6 : ∀ t, β • 𝔼.E t (V (t + 1)) = (1 - (0 : ℝ)) • V t - s0 t) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => β ^ T * 𝔼.E t (V (t + T)) ω) atTop
      (𝓝 (V t ω - ∑' j, β ^ j * 𝔼.E t (s0 (t + j)) ω)) := by
  have hab : |β| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
  have hsum := ForwardSolution.summable_A16 𝔼 hab hM t ω
  have hx : ∀ T, β ^ T * 𝔼.E t (V (t + T)) ω =
      V t ω - ∑ j ∈ Finset.range T, β ^ j * 𝔼.E t (s0 (t + j)) ω := by
    intro T
    induction T with
    | zero => simp [hVa t]
    | succ T ih =>
      rw [state_forecast_succ h6 t T ω, ih, Finset.sum_range_succ]
      ring
  simp_rw [hx]
  exact hsum.hasSum.tendsto_sum_nat.const_sub _

/-- Cochrane (2023), §9.2, p. 264: iterating (9.6) forward with `0 < α < 2`, the target state is
the present value of surpluses, `V*_t = E_t ∑ⱼ βʲ s_{t+j}` (an absolutely convergent series). -/
theorem hasSum_state (hβ0 : 0 < β) (hβ1 : β < 1) {α M : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {s0 V : ℕ → Ω → ℝ} (hM : ∀ t ω, |s0 t ω| ≤ M) (hsa : 𝔼.Adapted s)
    (h94 : SurplusRule α s0 V s) (h6s : ∀ t, β • 𝔼.E t (V (t + 1)) = V t - s t)
    (h6 : ∀ t, β • 𝔼.E t (V (t + 1)) = (1 - α) • V t - s0 t) (t : ℕ) (ω : Ω) :
    HasSum (fun j => β ^ j * 𝔼.E t (s (t + j)) ω) (V t ω) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ω)
  have hc : |1 - α| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hsolves : ForwardSolution.Solves 𝔼 β s V := by
    intro t
    rw [h6s t]
    abel
  have hpart := PresentValue.tendsto_partialSums_of_tvc 𝔼 hsa hsolves t ω
    (tendsto_state_forecast hβ0 hβ1 hα0 hα2 hM h6 t ω)
  have hx : ∀ T, |β ^ (T + 1) * 𝔼.E t (V (t + (T + 1))) ω -
      (1 - α) * (β ^ T * 𝔼.E t (V (t + T)) ω)| ≤ β ^ T * M := by
    intro T
    rw [state_forecast_succ h6 t T ω]
    rw [show (1 - α) * (β ^ T * 𝔼.E t (V (t + T)) ω) - β ^ T * 𝔼.E t (s0 (t + T)) ω -
        (1 - α) * (β ^ T * 𝔼.E t (V (t + T)) ω) = -(β ^ T * 𝔼.E t (s0 (t + T)) ω) by ring,
      abs_neg, abs_mul, abs_of_pos (pow_pos hβ0 T)]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hM (t + T)) t ω) (pow_pos hβ0 T).le
  have hsV := summable_of_contraction (x := fun T => β ^ T * 𝔼.E t (V (t + T)) ω) hc hβ0 hβ1
    hM0 hx
  have hab : |β| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
  have hs0 := ForwardSolution.summable_A16 𝔼 hab hM t ω
  have hsum : Summable (fun j => β ^ j * 𝔼.E t (s (t + j)) ω) := by
    have heq : (fun j => β ^ j * 𝔼.E t (s (t + j)) ω) = fun j =>
        β ^ j * 𝔼.E t (s0 (t + j)) ω + α * (β ^ j * 𝔼.E t (V (t + j)) ω) := by
      funext j
      rw [h94 (t + j), map_add, map_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact hs0.add (hsV.mul_left α)
  have h := hsum.hasSum
  rwa [tendsto_nhds_unique h.tendsto_sum_nat hpart] at h

/-- Cochrane (2023), §9.2, p. 264 ("the real value of nominal debt is also the present value of
surpluses"): with bond pricing and the pull-out property the real debt `b_t = B_t/P_t` obeys
`b_t = s_t + β E_t b_{t+1}`. -/
theorem realDebt_rec (h𝔼 : 𝔼.PullOut) (hE : Economy 𝔼 β B P Q s) (t : ℕ) :
    B t / P t = s t + β • 𝔼.E t (B (t + 1) / P (t + 1)) := by
  have hP0 : ∀ ω, P t ω ≠ 0 := fun ω => (hE.pos_P t ω).ne'
  have ha : 𝔼.E t (B (t + 1) / P t) = B (t + 1) / P t :=
    known_div 𝔼 h𝔼 (hE.predetermined_B t) (hE.adapted_P t) hP0
  have hprod : B (t + 1) / P (t + 1) = (B (t + 1) / P t) * (P t / P (t + 1)) := by
    funext ω
    simp only [Pi.div_apply, Pi.mul_apply]
    field_simp [hP0 ω]
  rw [hE.flow t, hprod, h𝔼 t _ _ ha, hE.pricing t]
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.div_apply]
  ring

/-- Cochrane (2023), §9.2, p. 264: the real value of nominal debt equals the target state,
`B_t/P_t = V*_t`, at every date and state (both solve `y_t = s_t + β E_t y_{t+1}` and both
satisfy the limit condition). -/
theorem realDebt_eq_state (h𝔼 : 𝔼.PullOut) (hE : Economy 𝔼 β B P Q s) {V : ℕ → Ω → ℝ}
    (h6s : ∀ t, β • 𝔼.E t (V (t + 1)) = V t - s t)
    (hlim : ∀ t ω, Tendsto (fun T => β ^ T * 𝔼.E t (V (t + T)) ω) atTop (𝓝 0)) (t : ℕ) :
    B t / P t = V t := by
  set d : ℕ → Ω → ℝ := fun t => B t / P t - V t with hd_def
  have hd : ∀ t, d t = β • 𝔼.E t (d (t + 1)) := by
    intro t
    simp only [hd_def, map_sub, smul_sub]
    rw [h6s t, realDebt_rec h𝔼 hE t]
    abel
  have htvc : PresentValue.TVC 𝔼 β d := fun t ω => by
    have e : ∀ k, β ^ k * 𝔼.E t (d (t + k)) ω = β ^ k * 𝔼.E t (B (t + k) / P (t + k)) ω -
        β ^ k * 𝔼.E t (V (t + k)) ω := fun k => by
      simp only [hd_def, map_sub, Pi.sub_apply]
      ring
    simp_rw [e]
    simpa using (hE.tvc t ω).sub (hlim t ω)
  have h0 := PresentValue.eq_zero_of_tvc 𝔼 hd htvc t
  rw [hd_def, sub_eq_zero] at h0
  exact h0

/-- Cochrane (2023), §9.2, p. 264 (**Theorem IT**, corrected): under the surplus rule (9.4)
with `0 < α < 2`, the interest-rate target (9.5), bounded `s₀`, nonzero initial debt and
`V*_t ≠ s_t` at every date (so that `B_{t+1} ≠ 0`), the unique equilibrium price level is
`P_t = P*_t`. The base step is `P_1 = P*_1` in the book's dating (error E9.2). -/
theorem price_eq_target (h𝔼 : 𝔼.PullOut) (hβ0 : 0 < β) (hβ1 : β < 1) {α M : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) {Pstar s0 V : ℕ → Ω → ℝ} (hE : Economy 𝔼 β B P Q s)
    (hPs : ∀ t ω, 0 < Pstar t ω) (hPsa : 𝔼.Adapted Pstar) (hs0a : 𝔼.Adapted s0)
    (hM : ∀ t ω, |s0 t ω| ≤ M) (h91 : StateInit B Pstar V) (h92 : StateRec Q Pstar s V)
    (h94 : SurplusRule α s0 V s) (h95 : RateTarget 𝔼 β Pstar Q) (hB0 : ∀ ω, B 0 ω ≠ 0)
    (hVs : ∀ t ω, V t ω ≠ s t ω) : P = Pstar := by
  have hVa := state_adapted h𝔼 hE.pos_Q hE.adapted_Q hPs hPsa hs0a hE.known_B0 h91 h92 h94
  have hsa : 𝔼.Adapted s := fun t => by rw [h94 t, map_add, map_smul, hs0a t, hVa t]
  have h6s := eq_9_6 h𝔼 hβ0.ne' hE.pos_Q hVa hE.adapted_Q hsa h92 h95
  have h6 := eq_9_6_rule h𝔼 hβ0.ne' hE.pos_Q hVa hE.adapted_Q hsa h92 h94 h95
  have hb := realDebt_eq_state h𝔼 hE h6s (tendsto_state_forecast hβ0 hβ1 hα0 hα2 hM h6)
  funext t
  induction t with
  | zero =>
    funext ω
    have h := congrFun (hb 0) ω
    rw [h91] at h
    simp only [Pi.div_apply] at h
    rw [div_eq_div_iff (hE.pos_P 0 ω).ne' (hPs 0 ω).ne'] at h
    exact (mul_left_cancel₀ (hB0 ω) h).symm
  | succ t ih =>
    funext ω
    have h3 := congrFun (eq_9_3 hE t) ω
    have h2 := congrFun (h92 t) ω
    have hbt := congrFun (hb t) ω
    have hbt1 := congrFun (hb (t + 1)) ω
    have hpt := congrFun ih ω
    simp only [Pi.div_apply, Pi.mul_apply, Pi.inv_apply, Pi.sub_apply] at h3 h2 hbt hbt1
    rw [hbt1, hbt, hpt] at h3
    have hk : (Q t ω)⁻¹ * Pstar t ω * (V t ω - s t ω) ≠ 0 := by
      have := sub_ne_zero.mpr (hVs t ω)
      have hq := (inv_pos.mpr (hE.pos_Q t ω)).ne'
      exact mul_ne_zero (mul_ne_zero hq (hPs t ω).ne') this
    have hP1 := (hE.pos_P (t + 1) ω).ne'
    have hPs1 := (hPs (t + 1) ω).ne'
    have h4 : (Q t ω)⁻¹ * Pstar t ω * (V t ω - s t ω) / Pstar (t + 1) ω =
        (Q t ω)⁻¹ * Pstar t ω * (V t ω - s t ω) / P (t + 1) ω := by
      calc _ = (Q t ω)⁻¹ * (Pstar t ω / Pstar (t + 1) ω) * (V t ω - s t ω) := by ring
        _ = (Q t ω)⁻¹ * (Pstar t ω / P (t + 1) ω) * (V t ω - s t ω) := by
          rw [← h2]
          exact h3
        _ = _ := by ring
    rw [div_eq_div_iff hPs1 hP1] at h4
    exact mul_left_cancel₀ hk h4

/-- Cochrane (2023), §9.2, p. 264: in equilibrium the real value of nominal debt is the present
value of surpluses, `B_t/P_t = E_t ∑ⱼ βʲ s_{t+j}`. -/
theorem realDebt_hasSum (h𝔼 : 𝔼.PullOut) (hβ0 : 0 < β) (hβ1 : β < 1) {α M : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) {Pstar s0 V : ℕ → Ω → ℝ} (hE : Economy 𝔼 β B P Q s)
    (hPs : ∀ t ω, 0 < Pstar t ω) (hPsa : 𝔼.Adapted Pstar) (hs0a : 𝔼.Adapted s0)
    (hM : ∀ t ω, |s0 t ω| ≤ M) (h91 : StateInit B Pstar V) (h92 : StateRec Q Pstar s V)
    (h94 : SurplusRule α s0 V s) (h95 : RateTarget 𝔼 β Pstar Q) (t : ℕ) (ω : Ω) :
    HasSum (fun j => β ^ j * 𝔼.E t (s (t + j)) ω) (B t ω / P t ω) := by
  have hVa := state_adapted h𝔼 hE.pos_Q hE.adapted_Q hPs hPsa hs0a hE.known_B0 h91 h92 h94
  have hsa : 𝔼.Adapted s := fun t => by rw [h94 t, map_add, map_smul, hs0a t, hVa t]
  have h6s := eq_9_6 h𝔼 hβ0.ne' hE.pos_Q hVa hE.adapted_Q hsa h92 h95
  have h6 := eq_9_6_rule h𝔼 hβ0.ne' hE.pos_Q hVa hE.adapted_Q hsa h92 h94 h95
  have hb := realDebt_eq_state h𝔼 hE h6s (tendsto_state_forecast hβ0 hβ1 hα0 hα2 hM h6) t
  have h := congrFun hb ω
  simp only [Pi.div_apply] at h
  rw [h]
  exact hasSum_state hβ0 hβ1 hα0 hα2 hM hsa h94 h6s h6 t ω

/-- Cochrane (2023), §9.2, p. 264: under perfect foresight Theorem IT needs no condition
`V*_t ≠ s_t`, because the interest-rate target fixes `P_{t+1}/P_t = P*_{t+1}/P*_t` directly. -/
theorem price_eq_target_perfectForesight {β α M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hα0 : 0 < α) (hα2 : α < 2) {B P Pstar Q s s0 V : ℕ → Unit → ℝ}
    (hE : Economy perfectForesight β B P Q s) (hPs : ∀ t ω, 0 < Pstar t ω)
    (hM : ∀ t ω, |s0 t ω| ≤ M) (h91 : StateInit B Pstar V) (h92 : StateRec Q Pstar s V)
    (h94 : SurplusRule α s0 V s) (h95 : RateTarget perfectForesight β Pstar Q)
    (hB0 : ∀ ω, B 0 ω ≠ 0) : P = Pstar := by
  have h𝔼 := perfectForesight_pullOut
  have hb := realDebt_hasSum h𝔼 hβ0 hβ1 hα0 hα2 hE hPs (fun _ => rfl) (fun _ => rfl) hM
    h91 h92 h94 h95
  have hVa : perfectForesight.Adapted V := fun _ => rfl
  have hsa : perfectForesight.Adapted s := fun _ => rfl
  have h6s := eq_9_6 h𝔼 hβ0.ne' hE.pos_Q hVa hE.adapted_Q hsa h92 h95
  have h6 := eq_9_6_rule h𝔼 hβ0.ne' hE.pos_Q hVa hE.adapted_Q hsa h92 h94 h95
  have hbV := realDebt_eq_state h𝔼 hE h6s (tendsto_state_forecast hβ0 hβ1 hα0 hα2 hM h6)
  clear hb
  funext t
  induction t with
  | zero =>
    funext ω
    have h := congrFun (hbV 0) ω
    rw [h91] at h
    simp only [Pi.div_apply] at h
    rw [div_eq_div_iff (hE.pos_P 0 ω).ne' (hPs 0 ω).ne'] at h
    exact (mul_left_cancel₀ (hB0 ω) h).symm
  | succ t ih =>
    funext ω
    have h1 := congrFun (hE.pricing t) ω
    have h2 := congrFun (h95 t) ω
    have hpt := congrFun ih ω
    change Q t ω = β * (P t ω / P (t + 1) ω) at h1
    change Q t ω = β * (Pstar t ω / Pstar (t + 1) ω) at h2
    rw [h1, hpt] at h2
    have hP1 := (hE.pos_P (t + 1) ω).ne'
    have hPs1 := (hPs (t + 1) ω).ne'
    have hPt := (hPs t ω).ne'
    have h3 := mul_left_cancel₀ hβ0.ne' h2
    rw [div_eq_div_iff hP1 hPs1] at h3
    exact (mul_left_cancel₀ hPt h3).symm

/-- Cochrane (2023), §9.2, p. 264 (existence half of "`P_t = P*_t` is the unique equilibrium
price level"): with the surplus rule (9.4), `0 < α < 2`, bounded `s₀` and the target (9.5), the
price
path `P = P*` with nominal debt `B_t = P*_t V*_t` is an equilibrium (`Economy`) satisfying
(9.1)–(9.5). -/
theorem exists_equilibrium (h𝔼 : 𝔼.PullOut) (hβ0 : 0 < β) (hβ1 : β < 1) {α M : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) {Pstar s0 V : ℕ → Ω → ℝ} (hQ : ∀ t ω, 0 < Q t ω)
    (hQa : 𝔼.Adapted Q) (hPs : ∀ t ω, 0 < Pstar t ω) (hPsa : 𝔼.Adapted Pstar)
    (hs0a : 𝔼.Adapted s0) (hM : ∀ t ω, |s0 t ω| ≤ M) (hV0 : 𝔼.E 0 (V 0) = V 0)
    (h92 : StateRec Q Pstar s V) (h94 : SurplusRule α s0 V s) (h95 : RateTarget 𝔼 β Pstar Q) :
    Economy 𝔼 β (fun t => Pstar t * V t) Pstar Q s ∧
      StateInit (fun t => Pstar t * V t) Pstar V := by
  have hinit : StateInit (fun t => Pstar t * V t) Pstar V := by
    funext ω
    simp only [Pi.div_apply, Pi.mul_apply]
    field_simp [(hPs 0 ω).ne']
  have hB0 : 𝔼.E 0 (Pstar 0 * V 0) = Pstar 0 * V 0 := known_mul 𝔼 h𝔼 (hPsa 0) hV0
  have hVa := state_adapted h𝔼 hQ hQa hPs hPsa hs0a hB0 hinit h92 h94
  have hsa : 𝔼.Adapted s := fun t => by rw [h94 t, map_add, map_smul, hs0a t, hVa t]
  have h6 := eq_9_6_rule h𝔼 hβ0.ne' hQ hVa hQa hsa h92 h94 h95
  have hBV : ∀ t, (fun t => Pstar t * V t) t / Pstar t = V t := fun t => by
    funext ω
    simp only [Pi.div_apply, Pi.mul_apply]
    field_simp [(hPs t ω).ne']
  refine ⟨⟨hPs, hQ, hPsa, hQa, hB0, fun t => ?_, fun t => ?_, h95, fun t ω => ?_⟩, hinit⟩
  · have hkey : Pstar (t + 1) * V (t + 1) = (Q t)⁻¹ * Pstar t * (V t - s t) := by
      rw [h92 t]
      funext ω
      simp only [Pi.mul_apply, Pi.inv_apply, Pi.div_apply, Pi.sub_apply]
      field_simp [(hPs (t + 1) ω).ne']
    change 𝔼.E t (Pstar (t + 1) * V (t + 1)) = Pstar (t + 1) * V (t + 1)
    rw [hkey]
    refine known_mul 𝔼 h𝔼 (known_mul 𝔼 h𝔼 ?_ (hPsa t)) ?_
    · exact known_inv 𝔼 h𝔼 (hQa t) (fun ω => (hQ t ω).ne')
    · rw [map_sub, hVa t, hsa t]
  · rw [hBV t]
    funext ω
    have h2 := congrFun (h92 t) ω
    simp only [Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply, Pi.sub_apply] at h2 ⊢
    rw [h2]
    have hQ0 := (hQ t ω).ne'
    have hP0 := (hPs t ω).ne'
    have hP1 := (hPs (t + 1) ω).ne'
    field_simp
    ring
  · have := tendsto_state_forecast hβ0 hβ1 hα0 hα2 hM h6 t ω
    refine this.congr fun T => ?_
    rw [hBV (t + T)]

/-! ### The two insufficiency claims -/

/-- Cochrane (2023), §9.2, p. 264, witness for "the interest-rate target alone is
insufficient": the target state for the witness `target_alone_insufficient`. -/
noncomputable def witnessState (β : ℝ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => β⁻¹ * (witnessState β t - 2 * (1 - β))

/-- Cochrane (2023), §9.2, p. 264: "The interest-rate target alone is insufficient." Under
perfect foresight, with the target (9.5) in force but a surplus that does not respond to the
target state (`α = 0`, bounded `s₀`), there is an equilibrium with `P ≠ P*` (here
`P ≡ 1/2`, `P* ≡ 1`). -/
theorem target_alone_insufficient {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ B P Pstar Q s s0 V : ℕ → Unit → ℝ, Economy perfectForesight β B P Q s ∧
      (∀ t ω, 0 < Pstar t ω) ∧ (∀ t ω, |s0 t ω| ≤ 2) ∧ StateInit B Pstar V ∧
      StateRec Q Pstar s V ∧ SurplusRule 0 s0 V s ∧ RateTarget perfectForesight β Pstar Q ∧
      (∀ ω, B 0 ω ≠ 0) ∧ P ≠ Pstar := by
  refine ⟨fun _ _ => 1, fun _ _ => 1 / 2, fun _ _ => 1, fun _ _ => β, fun _ _ => 2 * (1 - β),
    fun _ _ => 2 * (1 - β), fun t _ => witnessState β t, ⟨fun _ _ => by norm_num,
    fun _ _ => hβ0, fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl, fun t => ?_, fun t => ?_,
    fun t ω => ?_⟩, fun _ _ => by norm_num, fun _ _ => ?_, ?_, fun t => ?_, fun t => ?_,
    fun t => ?_, fun _ => by norm_num, ?_⟩
  · funext ω
    simp only [Pi.div_apply, Pi.add_apply, Pi.mul_apply]
    ring
  · funext ω
    change β = β * ((1 / 2) / (1 / 2))
    norm_num
  · change Tendsto (fun T => β ^ T * (1 / (1 / 2))) atTop (𝓝 0)
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const (1 / (1 / 2) : ℝ)
  · rw [abs_of_nonneg (by linarith)]
    linarith
  · funext ω
    simp [witnessState]
  · funext ω
    simp [witnessState]
  · funext ω
    simp
  · funext ω
    change β = β * (1 / 1)
    norm_num
  · intro h
    have := congrFun (congrFun h 0) ()
    norm_num at this

/-- Cochrane (2023), §9.2, p. 264, witness for "the surplus rule is also insufficient": the
target state `V*_t = ((1 − α)/β)ᵗ`. -/
noncomputable def ruleState (α β : ℝ) (t : ℕ) : ℝ := ((1 - α) / β) ^ t

/-- Cochrane (2023), §9.2, p. 264: "The surplus rule is also insufficient. Even with the rule
(9.4), a decision to double nominal debt without changing surpluses will have the usual effect
of doubling the future price level." Under perfect foresight with `0 < α < 2`, bounded `s₀`, and
the target state built from the target bond price `Q*_t = β E_t(P*_t/P*_{t+1})`, doubling the debt
sold at date `0` gives an equilibrium with `P_t = 2 P*_t` for `t ≥ 1`; the actual bond price then
misses the target, `Q ≠ Q*`. -/
theorem rule_alone_insufficient {α β : ℝ} (hβ0 : 0 < β) (hα0 : 0 < α)
    (hα2 : α < 2) :
    ∃ B P Pstar Q Qs s s0 V : ℕ → Unit → ℝ, Economy perfectForesight β B P Q s ∧
      (∀ t ω, 0 < Pstar t ω) ∧ (∀ t ω, |s0 t ω| ≤ 0) ∧ StateInit B Pstar V ∧
      StateRec Qs Pstar s V ∧ SurplusRule α s0 V s ∧ RateTarget perfectForesight β Pstar Qs ∧
      (∀ t, 1 ≤ t → ∀ ω, P t ω = 2 * Pstar t ω) ∧ Q ≠ Qs := by
  set P : ℕ → Unit → ℝ := fun t _ => if t = 0 then 1 else 2 with hP
  set V : ℕ → Unit → ℝ := fun t _ => ruleState α β t with hV
  set B : ℕ → Unit → ℝ := fun t _ => if t = 0 then 1 else 2 * ruleState α β t with hB
  have hPpos : ∀ t ω, 0 < P t ω := fun t ω => by
    simp only [hP]
    split_ifs <;> norm_num
  have hβne : β ≠ 0 := hβ0.ne'
  have hq : (1 - α) / β * β = 1 - α := by field_simp
  have hc : |1 - α| < 1 := by rw [abs_lt]; constructor <;> linarith
  refine ⟨B, P, fun _ _ => 1, fun t _ => β * (P t () / P (t + 1) ()), fun _ _ => β,
    fun t ω => α * V t ω, fun _ _ => 0, V, ⟨hPpos, fun t ω => ?_, fun _ => rfl, fun _ => rfl, rfl,
    fun _ => rfl, fun t => ?_, fun t => ?_, fun t ω => ?_⟩, fun _ _ => by norm_num,
    fun _ _ => by norm_num, ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t ht ω => ?_, ?_⟩
  · exact mul_pos hβ0 (div_pos (hPpos t ()) (hPpos (t + 1) ()))
  · funext ω
    simp only [hP, hB, hV, ruleState, Pi.div_apply, Pi.add_apply, Pi.mul_apply]
    have hbb : β * β⁻¹ = 1 := mul_inv_cancel₀ hβne
    rcases t with _ | t
    · simp only [↓reduceIte, pow_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false]
      linear_combination (α - 1) * hbb
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
      linear_combination (α - 1) * ((1 - α) / β) ^ (t + 1) * hbb
  · funext ω
    rfl
  · change Tendsto (fun T => β ^ T * (B (t + T) ω / P (t + T) ω)) atTop (𝓝 0)
    have hev : ∀ T, 1 ≤ T → β ^ T * (B (t + T) ω / P (t + T) ω) =
        ruleState α β t * (1 - α) ^ T := by
      intro T hT
      have h0 : t + T ≠ 0 := by omega
      simp only [hB, hP, h0, ↓reduceIte, ruleState]
      rw [pow_add, show ∀ X : ℝ, 2 * X / 2 = X from fun X => by ring,
        show β ^ T * (((1 - α) / β) ^ t * ((1 - α) / β) ^ T) =
          ((1 - α) / β) ^ t * ((1 - α) / β * β) ^ T by rw [mul_pow]; ring, hq]
    have hlim : Tendsto (fun T : ℕ => ruleState α β t * (1 - α) ^ T) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hc).const_mul (ruleState α β t)
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with T hT
    exact (hev T hT).symm
  · funext ω
    simp [hB, hV, ruleState]
  · funext ω
    simp only [hV, ruleState, Pi.mul_apply, Pi.inv_apply, Pi.div_apply, Pi.sub_apply]
    rw [pow_succ]
    field_simp
  · funext ω
    simp
  · funext ω
    change β = β * (1 / 1)
    norm_num
  · have h0 : t ≠ 0 := by omega
    simp [hP, h0]
  · intro h
    have := congrFun (congrFun h 0) ()
    simp only [hP, ↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false] at this
    have h2 : β * (1 / 2) = β := this
    linarith

/-! ### Why `V*_t ≠ s_t` is needed under uncertainty -/

/-- Cochrane (2023), §9.2, p. 264 (error E9.2): the date-`1` price level of the witness
`zero_debt_sunspot`, `2` if the first coin is heads and `2/3` otherwise. -/
noncomputable def coinPrice (ω : Bool × Bool) : ℝ := if ω.1 then 2 else 2 / 3

/-- Cochrane (2023), §9.2, p. 264: after date `1` the first coin flip is known. -/
theorem coin_first_known {t : ℕ} (ht : 1 ≤ t) {ω ω' : Bool × Bool}
    (h : ExpectationsFiniteTree.coinTree.info t ω' ω) : ω'.1 = ω.1 := by
  change Setoid.ker (ExpectationsFiniteTree.coinObs t) ω' ω at h
  rw [Setoid.ker_def] at h
  simp only [ExpectationsFiniteTree.coinObs, Prod.mk.injEq, ht, ↓reduceIte] at h
  exact h.1

/-- Cochrane (2023), §9.2, p. 264: the coin-flip price `coinPrice` is known from date `1` on. -/
theorem coinPrice_known {t : ℕ} (ht : 1 ≤ t) :
    ExpectationsFiniteTree.coinSystem.E t coinPrice = coinPrice := by
  funext ω
  rw [ExpectationsFiniteTree.coinSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  refine ExpectationsFiniteTree.coinTree.condE_of_const_on_cell fun ω' h => ?_
  simp [coinPrice, coin_first_known ht h]

/-- Cochrane (2023), §9.2, p. 264: at date `0` the expected inverse of `coinPrice` is one,
`E_0 (1/P_1) = (1/2)(1/2) + (1/2)(3/2) = 1`. -/
theorem coinPrice_E0_inv (ω : Bool × Bool) :
    ExpectationsFiniteTree.coinSystem.E 0 (fun ω => 1 / coinPrice ω) ω = 1 := by
  have htriv : ∀ a b, ExpectationsFiniteTree.coinTree.info 0 a b := fun a b => by
    change Setoid.ker (ExpectationsFiniteTree.coinObs 0) a b
    rw [Setoid.ker_def]
    simp [ExpectationsFiniteTree.coinObs]
  rw [ExpectationsFiniteTree.coinSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E,
    ExpectationsFiniteTree.coinTree.condE_of_trivial htriv]
  simp [ExpectationsFiniteTree.coinTree, coinPrice, Fintype.sum_prod_type]
  norm_num

/-- Cochrane (2023), §9.2, p. 264 (error E9.2): the hypothesis `V*_t ≠ s_t` of Theorem IT
cannot be dropped under uncertainty. In the two-coin tree, with `α = 1`, `s₀ = 0`, `P* ≡ 1`,
the debt is fully repaid at date `0` (`V*_0 = s_0`), and every other hypothesis holds, yet the
date-`1` price level is a sunspot (`2` or `2/3`) with `E_0(P_0/P_1) = 1`. -/
theorem zero_debt_sunspot {β : ℝ} (hβ0 : 0 < β) :
    ∃ B P Pstar Q s s0 V : ℕ → Bool × Bool → ℝ,
      Economy ExpectationsFiniteTree.coinSystem β B P Q s ∧ (∀ t ω, 0 < Pstar t ω) ∧
      ExpectationsFiniteTree.coinSystem.Adapted Pstar ∧
      ExpectationsFiniteTree.coinSystem.Adapted s0 ∧ (∀ t ω, |s0 t ω| ≤ 0) ∧
      StateInit B Pstar V ∧ StateRec Q Pstar s V ∧ SurplusRule 1 s0 V s ∧
      RateTarget ExpectationsFiniteTree.coinSystem β Pstar Q ∧ (∀ ω, B 0 ω ≠ 0) ∧
      V 0 = s 0 ∧ P ≠ Pstar := by
  set 𝔼c := ExpectationsFiniteTree.coinSystem with h𝔼c
  set P : ℕ → Bool × Bool → ℝ := fun t ω => if t = 0 then 1 else coinPrice ω with hP
  set B : ℕ → Bool × Bool → ℝ := fun t _ => if t = 0 then 1 else 0 with hB
  have hcp : ∀ ω, 0 < coinPrice ω := fun ω => by
    unfold coinPrice
    split_ifs <;> norm_num
  have hPpos : ∀ t ω, 0 < P t ω := fun t ω => by
    simp only [hP]
    split_ifs
    · norm_num
    · exact hcp ω
  have hconst : ∀ t (c : ℝ), 𝔼c.E t (fun _ => c) = fun _ => c := fun t c => 𝔼c.const t c
  have hBc : ∀ t, B t = fun _ => (if t = 0 then 1 else 0 : ℝ) := fun t => rfl
  refine ⟨B, P, fun _ _ => 1, fun _ _ => β, B, fun _ _ => 0, B, ⟨hPpos, fun _ _ => hβ0,
    fun t => ?_, fun t => hconst t β, ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t ω => ?_⟩,
    fun _ _ => by norm_num, fun t => hconst t 1, fun t => hconst t 0, fun _ _ => by norm_num,
    ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun _ => by simp [hB], rfl, ?_⟩
  · rcases t with _ | t
    · exact hconst 0 1
    · have h : P (t + 1) = coinPrice := by
        funext ω
        simp [hP]
      rw [h]
      exact coinPrice_known (by omega)
  · exact hconst 0 1
  · rw [hBc]
    exact hconst t _
  · funext ω
    simp only [hB, hP, Pi.div_apply, Pi.add_apply, Pi.mul_apply]
    split_ifs <;> simp_all
  · rcases t with _ | t
    · have h : P 0 / P 1 = fun ω => 1 / coinPrice ω := by
        funext ω
        simp [hP]
      rw [h]
      funext ω
      change β = β * 𝔼c.E 0 (fun ω => 1 / coinPrice ω) ω
      rw [coinPrice_E0_inv]
      ring
    · have h : P (t + 1) / P (t + 1 + 1) = fun _ => 1 := by
        funext ω
        simp only [hP, Pi.div_apply, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
        exact div_self (hcp ω).ne'
      rw [h, hconst]
      funext ω
      simp
  · have hev : ∀ T, 1 ≤ T → β ^ T * 𝔼c.E t (B (t + T) / P (t + T)) ω = 0 := by
      intro T hT
      have h0 : t + T ≠ 0 := by omega
      have h : B (t + T) / P (t + T) = fun _ => 0 := by
        funext ω'
        simp only [hB, Pi.div_apply, h0, ↓reduceIte, zero_div]
      rw [h, hconst]
      simp
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with T hT
    exact (hev T hT).symm
  · funext ω
    simp [hB]
  · funext ω
    simp only [hB, Pi.mul_apply, Pi.inv_apply, Pi.div_apply, Pi.sub_apply]
    simp
  · funext ω
    simp
  · funext ω
    change β = β * 𝔼c.E t (fun _ => 1 / 1) ω
    rw [hconst]
    norm_num
  · intro h
    have := congrFun (congrFun h 1) (true, true)
    simp [hP, coinPrice] at this

end Cochrane.AssetsRulesBalanceSheets.InflationTarget
