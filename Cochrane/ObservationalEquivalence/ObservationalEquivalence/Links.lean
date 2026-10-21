/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.MoneyRegimes
import ObservationalEquivalence.PresentValueIdentity
import ObservationalEquivalence.MarkovRegimes

/-!
# Links between the two chains of the observational-equivalence project

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §§22.1–22.3 and 22.7,
pp. 495–509; Chapter 24, §24.2, pp. 522–523; Online Appendix Chapter 2, §2.3, p. 606.

Chain A (the frictionless linear model, regimes and observational equivalence) and chain B
(regressions, Granger causality, present-value identities, discount factors, Markov switching)
formalised overlapping book objects. This module proves that they agree.

* Full information and present values: `perfectForesight_eq_fullInfo`, `pvExPost_eq_pv`,
  `valueOfDebt_eq_valuation` (chain B's value of debt is chain A's valuation equation).
* The valuation formula for unexpected inflation (p. 495) from the ex-post present-value
  identity of Online Appendix §2.3 (p. 606): `unexpected_inflation_of_identity` — no
  transversality hypothesis beyond bounded debt, and agreeing with `unexpected_inflation_news`.
* The discount-factor valuation (p. 499) in the money model of §22.1 (p. 496):
  `sdf_of_const_step`, `moneyEqm_debtFlow`, `moneyEqm_sdfStep`, `moneyEqm_sdf_valuation`.
* The s-shaped surplus of p. 502 is exogenous and has zero present value, yet gives a positive
  regression coefficient of surpluses on debt (p. 501, Theorem RG): `sshape_summable`,
  `sshape_regression_pos`.
* The equilibrium criterion (§22.7, p. 508; Woodford (2003), Prop. 4.11, pp. 311–314):
  `uniqueB_iff_not_ricardian`, `ricardian_passive_not_unique`.
* Markov switching with a constant regime (pp. 522–523) is the Taylor principle:
  `dl_const_iff`, `markov_const_determinate_iff`, `markov_const_iff_starred_determinate`,
  `markov_const_iff_forward`.
* OE-2 and OE-1 (pp. 495–497): `moneyOutcome`, `moneyOutcome_consistent`,
  `moneyOutcome_admissible`, `oe2_oe1`.
* Geometric decay (p. 523; Online Appendix p. 605): `powDecay_of_schur` (a Schur-stable `2 × 2`
  matrix has geometrically decaying powers, chain B's `PowDecay`).
-/

namespace Cochrane.ObservationalEquivalence.Links

open Filter Topology
open Cochrane.ObservationalEquivalence.ExpectationTools (innov innov_apply fullInfo pvExPost
  tendsto_pow_mul_of_bounded)

variable {Ω : Type*}

/-! ### Full information and present values -/

/-- Cochrane (2023), §22.7, p. 508: the core perfect-foresight system is full information on
the one-point state space. -/
theorem perfectForesight_eq_fullInfo : perfectForesight = fullInfo Unit := rfl

/-- Cochrane (2023), §22.1, pp. 495–496: the ex-post present value of the linear model is, state
by state, the money model's present value `∑ βʲ s_{t+j}` started one period later. -/
theorem pvExPost_eq_pv (ρ : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    pvExPost ρ s t ω = MoneyRegimes.pv ρ (fun k => s k ω) (t + 1) := rfl

/-- Cochrane (2023), p. 501 and Online Appendix (2.22), p. 602: in the frictionless model
(Fisher equation, flow condition, transversality condition, bounded surpluses), the value of debt
is chain B's `valueOfDebt`, the expected discounted surplus stream. -/
theorem valueOfDebt_eq_valuation (𝔼 : ExpectationSystem Ω) {ρ M : ℝ} (hρ : |ρ| < 1)
    {v i π s : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M) (hF : Valuation.Fisher 𝔼 i π)
    (h : Valuation.Flow ρ v i π s) (hv : 𝔼.Adapted v) (htvc : Valuation.TVC 𝔼 ρ v) (t : ℕ) :
    v t = SurplusRegression.valueOfDebt 𝔼 ρ s t :=
  Valuation.valuation_E_exPost 𝔼 hρ hs hF h hv htvc t

/-! ### Unexpected inflation from the ex-post identity -/

/-- Cochrane (2023), §22.1, p. 495, from Online Appendix §2.3, p. 606 ("It always holds ex-post,
so it always holds ex-ante"): in the frictionless model with bounded adapted `v`, `i`, `π` and
bounded surpluses, the ex-post identity `ΔE_{t+1} ∑ ρʲ s_{t+1+j} = ΔE_{t+1} ∑ ρʲ r_{t+1+j}`
(`PresentValueIdentity.as_eq_ar_innov`, with the ex-post real return `r_{t+1} = i_t − π_{t+1}`)
gives the valuation formula for unexpected inflation, `ΔE_{t+1}π_{t+1} = −ΔE_{t+1} ∑ ρʲ s_{t+1+j}`
(`Valuation.unexpected_inflation_news`) — with no transversality hypothesis beyond bounded debt,
and without assuming the surplus adapted. -/
theorem unexpected_inflation_of_identity (𝔼 : ExpectationSystem Ω) {ρ Mv Mi Mπ Ms : ℝ}
    (hρ : |ρ| < 1) {v i π s : ℕ → Ω → ℝ} (hv : ∀ t ω, |v t ω| ≤ Mv)
    (hi : ∀ t ω, |i t ω| ≤ Mi) (hπ : ∀ t ω, |π t ω| ≤ Mπ) (hs : ∀ t ω, |s t ω| ≤ Ms)
    (hva : 𝔼.Adapted v) (hia : 𝔼.Adapted i) (hπa : 𝔼.Adapted π) (hF : Valuation.Fisher 𝔼 i π)
    (h : Valuation.Flow ρ v i π s) (t : ℕ) :
    Valuation.surprise 𝔼 π t = -innov 𝔼 t (pvExPost ρ s t) := by
  set r : ℕ → Ω → ℝ := fun k => Valuation.realReturn i π (k - 1) with hr
  have hrb : ∀ k ω, |r k ω| ≤ Mi + Mπ := fun k ω => by
    simp only [hr, Valuation.realReturn, Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hi _ ω) (hπ _ ω))
  have hflow : ∀ k, ρ • v (k + 1) = v k + r (k + 1) - s (k + 1) := fun k => by
    simp only [hr, Nat.add_sub_cancel, Valuation.realReturn]
    rw [h k]
    abel
  have hid := PresentValueIdentity.as_eq_ar_innov 𝔼 hρ hv hrb hs hflow hva t
  have hE0 : 𝔼.E t (pvExPost ρ r t) = 0 := by
    rw [Valuation.E_pvExPost 𝔼 hρ hrb]
    funext ω
    simp only [Valuation.pvE, Pi.zero_apply]
    refine (tsum_congr fun j => ?_).trans tsum_zero
    change ρ ^ j * 𝔼.E t (Valuation.realReturn i π (t + 1 + j - 1)) ω = 0
    rw [show t + 1 + j - 1 = t + j by omega, Valuation.E_realReturn 𝔼 hF t j, Pi.zero_apply,
      mul_zero]
  have hE1 : 𝔼.E (t + 1) (pvExPost ρ r t) = i t - π (t + 1) := by
    rw [Valuation.E_pvExPost 𝔼 hρ hrb]
    funext ω
    simp only [Valuation.pvE]
    rw [tsum_eq_single 0 fun j hj => ?_]
    · change ρ ^ 0 * 𝔼.E (t + 1) (Valuation.realReturn i π (t + 1 + 0 - 1)) ω =
        (i t - π (t + 1)) ω
      rw [show t + 1 + 0 - 1 = t by omega, Valuation.realReturn, map_sub,
        ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hia t), hπa (t + 1), pow_zero, one_mul]
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      change ρ ^ (k + 1) * 𝔼.E (t + 1) (Valuation.realReturn i π (t + 1 + (k + 1) - 1)) ω = 0
      rw [show t + 1 + (k + 1) - 1 = t + 1 + k by omega, Valuation.E_realReturn 𝔼 hF (t + 1) k,
        Pi.zero_apply, mul_zero]
  have hinn : innov 𝔼 t (pvExPost ρ r t) = -Valuation.surprise 𝔼 π t := by
    rw [innov_apply, hE1, hE0, sub_zero, Valuation.surprise, hF t]
    abel
  rw [hid, hinn, neg_neg]

/-! ### The discount factor in the money model -/

/-- Cochrane (2023), p. 499: with a constant one-period discount factor `Λ_{t+1}/Λ_t = β`, the
ex-post discount factor is `Λ_t = βᵗ`. -/
theorem sdf_of_const_step {P Q : ℕ → ℝ} {β : ℝ}
    (h : ∀ t, PresentValueIdentity.sdfStep P Q t = β) (t : ℕ) :
    PresentValueIdentity.sdf P Q t = β ^ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change PresentValueIdentity.sdf P Q t * PresentValueIdentity.sdfStep P Q t = β ^ (t + 1)
    rw [ih, h t, pow_succ]

/-- Cochrane (2023), §22.1, p. 496, and p. 499: an equilibrium of the money model satisfies the
nominal flow constraint `W_t = P_t s_t + Q_t W_{t+1}` of p. 499 with bond price
`Q_t = β P_t/P_{t+1}`. -/
theorem moneyEqm_debtFlow {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {V y P M W s : ℕ → ℝ}
    (hs : ∀ t, |s t| ≤ K) (h : MoneyRegimes.Eqm β V y P M W s) :
    PresentValueIdentity.DebtFlow W P (fun t => β * P t / P (t + 1)) s :=
  fun t => MoneyRegimes.flow_of_valuation hβ0 hβ1 hs h t

/-- Cochrane (2023), §22.1, p. 496, and p. 499: in the money model the one-period discount
factor `Q_t P_{t+1}/P_t` is the constant `β`. -/
theorem moneyEqm_sdfStep {β : ℝ} {V y P M W s : ℕ → ℝ} (h : MoneyRegimes.Eqm β V y P M W s)
    (t : ℕ) : PresentValueIdentity.sdfStep P (fun t => β * P t / P (t + 1)) t = β := by
  have h0 := (h t).1.ne'
  have h1 := (h (t + 1)).1.ne'
  simp only [PresentValueIdentity.sdfStep]
  field_simp

/-- Cochrane (2023), p. 499 and §22.1, p. 496: the discount-factor valuation of chain B,
applied to an equilibrium of the money model (`0 < β < 1`, bounded surpluses), has weights
`Λ_{t+j}/Λ_t = βʲ` and reproduces the money model's valuation equation
`W_t/P_t = ∑ βʲ s_{t+j}` (the transversality condition is proved, not assumed). -/
theorem moneyEqm_sdf_valuation {β K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {V y P M W s : ℕ → ℝ}
    (hs : ∀ t, |s t| ≤ K) (h : MoneyRegimes.Eqm β V y P M W s) (t : ℕ) :
    (∀ j, PresentValueIdentity.sdf P (fun t => β * P t / P (t + 1)) (t + j) /
        PresentValueIdentity.sdf P (fun t => β * P t / P (t + 1)) t = β ^ j) ∧
      HasSum (fun j => PresentValueIdentity.sdf P (fun t => β * P t / P (t + 1)) (t + j) /
        PresentValueIdentity.sdf P (fun t => β * P t / P (t + 1)) t * s (t + j))
        (W t / P t) := by
  have hP : ∀ t, 0 < P t := fun t => (h t).1
  have hQ : ∀ t, 0 < β * P t / P (t + 1) := fun t =>
    div_pos (mul_pos hβ0 (hP t)) (hP (t + 1))
  have hsdf := sdf_of_const_step (moneyEqm_sdfStep h)
  have hw : ∀ j, PresentValueIdentity.sdf P (fun t => β * P t / P (t + 1)) (t + j) /
      PresentValueIdentity.sdf P (fun t => β * P t / P (t + 1)) t = β ^ j := fun j => by
    rw [hsdf, hsdf, pow_add, mul_div_cancel_left₀ _ (pow_ne_zero t hβ0.ne')]
  refine ⟨hw, ?_⟩
  have hpvb : ∀ k, |MoneyRegimes.pv β s k| ≤ K / (1 - β) := fun k => by
    have hg : HasSum (fun j : ℕ => K * β ^ j) (K / (1 - β)) := by
      simpa [div_eq_mul_inv] using (hasSum_geometric_of_lt_one hβ0.le hβ1).mul_left K
    have := tsum_of_norm_bounded hg (f := fun j => β ^ j * s (k + j)) fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0.le j), mul_comm K]
      exact mul_le_mul_of_nonneg_left (hs _) (pow_nonneg hβ0.le j)
    simpa [MoneyRegimes.pv, Real.norm_eq_abs] using this
  refine PresentValueIdentity.sdf_valuation_hasSum hP hQ (moneyEqm_debtFlow hβ0.le hβ1 hs h) t
    ?_ ?_
  · simp only [hw]
    refine (tendsto_pow_mul_of_bounded (by rw [abs_of_pos hβ0]; exact hβ1)
      (x := fun T => MoneyRegimes.pv β s (t + T)) fun T => hpvb (t + T)).congr fun T => ?_
    rw [(h (t + T)).2.2]
  · simp only [hw]
    exact MoneyRegimes.pv_summable hβ0.le hβ1 hs t

/-! ### The s-shaped surplus and the regression of surpluses on debt -/

/-- Cochrane (2023), p. 502: when `|1 − α| < ρ`, the s-shaped surplus response is absolutely
summable (a genuine infinite moving average). -/
theorem sshape_summable {α ρ : ℝ} (hρ : 0 < ρ) (hαρ : |1 - α| < ρ) :
    Summable fun k => |NonIdentification.irfS α ρ (k + 1)| := by
  rw [← summable_nat_add_iff 1]
  have hq : |(1 - α) / ρ| < 1 := by
    rw [abs_div, abs_of_pos hρ, div_lt_one hρ]
    exact hαρ
  refine ((summable_geometric_of_lt_one (abs_nonneg _) hq).mul_left (|α| * ρ⁻¹)).congr
    fun k => ?_
  change |α| * ρ⁻¹ * |(1 - α) / ρ| ^ k = |NonIdentification.irfS α ρ (k + 2)|
  simp only [NonIdentification.irfS, NonIdentification.irfV]
  rw [abs_mul, abs_mul, abs_neg, abs_inv, abs_of_pos hρ, abs_pow]
  ring

/-- Cochrane (2023), p. 502 with p. 501 and §24.1, p. 519 (Theorem RG): the s-shaped surplus
response (`0 < α < 2`, `0 < ρ < 1`, `|1 − α| < ρ`) has zero present value
(`NonIdentification.irf_pv_zero`, so it moves no inflation) and, viewed as an exogenous moving
average, it is not white noise, so the population regression of surpluses on lagged debt has a
strictly positive coefficient (`SurplusRegression.regInf_pos_iff`). A positive coefficient is
therefore consistent with the `α = 0` representation: it does not identify `α`. -/
theorem sshape_regression_pos {α ρ : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hαρ : |1 - α| < ρ) :
    HasSum (fun j => ρ ^ j * NonIdentification.irfS α ρ (j + 1)) 0 ∧
      0 < SurplusRegression.covInf ρ (fun k => NonIdentification.irfS α ρ (k + 1 + 1)) /
        ∑' m, SurplusRegression.bInf ρ (fun k => NonIdentification.irfS α ρ (k + 1 + 1)) m ^ 2 := by
  have hρ : |ρ| < 1 := by rw [abs_of_pos hρ0]; exact hρ1
  refine ⟨NonIdentification.irf_pv_zero hα0 hα2 hρ0.ne',
    (SurplusRegression.regInf_pos_iff hρ (a := fun k => NonIdentification.irfS α ρ (k + 1))
      (sshape_summable hρ0 hαρ)).mpr fun hiid => ?_⟩
  have h1 : NonIdentification.irfS α ρ 2 = 0 := hiid 1 le_rfl
  simp only [NonIdentification.irfS, NonIdentification.irfV, pow_zero, mul_one] at h1
  have : 0 < α * ρ⁻¹ := mul_pos hα0 (inv_pos.mpr hρ0)
  linarith

/-! ### The equilibrium criterion: bounded debt and locally Ricardian rules -/

/-- Cochrane (2023), §22.7, p. 508, and Woodford (2003), Prop. 4.11, pp. 311–314 (via
`FiscalRec.LocallyRicardian`): with passive money `|φ| ≤ 1`, the target is the unique equilibrium
under the bounded-debt criterion iff the fiscal rule is not locally Ricardian and is off the
boundary `|1 − γ| = ρ`. -/
theorem uniqueB_iff_not_ricardian (𝔼 : ExpectationSystem Ω) [Nonempty Ω]
    {ρ φ γ bb τg τπ τy τi : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : |φ| ≤ 1)
    {tg : StarredModel.Outcome Ω} (hc : StarredModel.Consistent 𝔼 ρ tg)
    (htg : LeeperRegions.AdmissibleB 𝔼 tg) :
    LeeperRegions.UniqueEqmB 𝔼 ρ φ γ tg ↔
      ¬ FiscalRec.LocallyRicardian Ω ρ bb γ τg τπ τy τi ∧ |1 - γ| ≠ ρ := by
  rw [LeeperRegions.uniqueB_iff 𝔼 hρ0 hρ1 hc htg,
    LeeperRegions.locallyRicardian_iff_gamma (Ω := Ω) hρ0]
  constructor
  · rintro (h | h)
    · linarith
    · exact ⟨by linarith, by intro he; linarith⟩
  · rintro ⟨h1, h2⟩
    exact Or.inr (lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2))

/-- Cochrane (2023), §22.7, p. 508, and Woodford (2003), Prop. 4.11, pp. 311–314: a locally
Ricardian fiscal rule with passive money leaves the equilibrium indeterminate under both
criteria — the transversality condition (`Equivalence.unique_iff`: `|1 − γ| < ρ < 1` is
double-passive) and bounded debt (`LeeperRegions.uniqueB_iff`). -/
theorem ricardian_passive_not_unique (𝔼 : ExpectationSystem Ω) [Nonempty Ω]
    {ρ φ γ bb τg τπ τy τi : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : |φ| ≤ 1)
    (hR : FiscalRec.LocallyRicardian Ω ρ bb γ τg τπ τy τi)
    {tg : StarredModel.Outcome Ω} (hc : StarredModel.Consistent 𝔼 ρ tg)
    (htg : LeeperRegions.AdmissibleB 𝔼 tg) :
    ¬ Equivalence.UniqueEqm 𝔼 ρ φ γ tg ∧ ¬ LeeperRegions.UniqueEqmB 𝔼 ρ φ γ tg := by
  have hγ := (LeeperRegions.locallyRicardian_iff_gamma (Ω := Ω) hρ0).mp hR
  have hρa : |ρ| < 1 := by rw [abs_of_pos hρ0]; exact hρ1
  refine ⟨fun hu => ?_, fun hu => ?_⟩
  · have hd := (Equivalence.unique_iff 𝔼 hρ0.ne' hc
      (LeeperRegions.admissible_of_B 𝔼 hρa htg)).mp hu
    rcases hd with hd | hd <;> linarith
  · rcases (LeeperRegions.uniqueB_iff 𝔼 hρ0 hρ1 hc htg).mp hu with hd | hd <;> linarith

/-! ### Markov switching with one regime: the Taylor principle -/

/-- Cochrane (2023), pp. 522–523: when both regimes have the same `φ > 0`, the Davig–Leeper
condition is the Taylor principle `φ > 1`. -/
theorem dl_const_iff (T : MarkovRegimes.Transition) {φ : ℝ} (hφ : 0 < φ) :
    MarkovRegimes.DLCondition T (fun _ => φ) ↔ 1 < φ := by
  have hp0 := T.nonneg 0 0
  have hq0 := T.nonneg 1 1
  have hp1 : T.P 0 0 ≤ 1 := by have := MarkovRegimes.P01 T; linarith [T.nonneg 0 1]
  have hq1 : T.P 1 1 ≤ 1 := by have := MarkovRegimes.P10 T; linarith [T.nonneg 1 0]
  change 1 < (1 - φ) * T.P 0 0 + (1 - φ) * T.P 1 1 + φ * φ ∧ T.P 0 0 / φ + T.P 1 1 / φ < 2 ↔
    1 < φ
  rw [← add_div, div_lt_iff₀ hφ]
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hle
    push Not at hle
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) (sub_nonneg.mpr hle)]
  · intro h
    refine ⟨by nlinarith, by linarith⟩

/-- Cochrane (2023), pp. 522–523: with a constant regime `φ > 0`, the Markov-switching model has
exactly one bounded equilibrium for every bounded disturbance iff `|φ| > 1`. -/
theorem markov_const_determinate_iff (T : MarkovRegimes.Transition) {φ : ℝ} (hφ : 0 < φ) :
    (∀ u, MarkovRegimes.BoundedFn u →
      ∃! π, MarkovRegimes.Solves T (fun _ => φ) u π ∧ MarkovRegimes.BoundedFn π) ↔
      1 < |φ| := by
  rw [MarkovRegimes.determinate_iff T (fun _ => hφ), dl_const_iff T hφ, abs_of_pos hφ]

/-- Cochrane (2023), pp. 522–523 and p. 495: with one regime and passive fiscal policy
(`0 < γ < 2`), Markov determinacy is exactly the determinacy of the starred system of chain A
(`Equivalence.Determinate`): the Taylor principle. -/
theorem markov_const_iff_starred_determinate (T : MarkovRegimes.Transition) {φ γ : ℝ}
    (hφ : 0 < φ) (hγ : 0 < γ ∧ γ < 2) :
    (∀ u, MarkovRegimes.BoundedFn u →
      ∃! π, MarkovRegimes.Solves T (fun _ => φ) u π ∧ MarkovRegimes.BoundedFn π) ↔
      Equivalence.Determinate φ γ := by
  rw [markov_const_determinate_iff T hφ, Equivalence.determinate_iff]
  constructor
  · exact Or.inl
  · rintro (h | h | h)
    · exact h
    · linarith
    · linarith

/-- Cochrane (2023), pp. 522–523: with one regime the Markov model is the scalar forward
equation `π_t = φ⁻¹ E_t π_{t+1} − φ⁻¹ u_t`, and its determinacy condition is the core's
`|φ⁻¹| < 1` (`ForwardSolution.existsUnique_iff`). -/
theorem markov_const_iff_forward (T : MarkovRegimes.Transition) {φ : ℝ} (hφ : 0 < φ) :
    (∀ u, MarkovRegimes.BoundedFn u →
      ∃! π, MarkovRegimes.Solves T (fun _ => φ) u π ∧ MarkovRegimes.BoundedFn π) ↔
      |φ⁻¹| < 1 := by
  rw [markov_const_determinate_iff T hφ, abs_inv, inv_lt_one_iff₀]
  constructor
  · exact Or.inr
  · rintro (h | h)
    · exact absurd h (not_le.mpr (abs_pos.mpr hφ.ne'))
    · exact h

/-! ### OE-2 and OE-1 -/

/-- Cochrane (2023), §22.1, pp. 495–496: the observable path of a money-model equilibrium in the
variables of the frictionless linear model, under perfect foresight: inflation
`π_t = log P_t − log P_{t−1}` (`π_0 = 0`), the interest rate `i_t = π_{t+1}`, the end-of-period
real debt `v_t = W_{t+1}/P_{t+1}` and the surplus `s_t`. -/
noncomputable def moneyOutcome (P W s : ℕ → ℝ) : StarredModel.Outcome Unit where
  pi := fun t _ => Real.log (P t) - Real.log (P (t - 1))
  i := fun t _ => Real.log (P (t + 1)) - Real.log (P t)
  v := fun t _ => W (t + 1) / P (t + 1)
  s := fun t _ => s t

/-- Cochrane (2023), §22.1, pp. 495–496: a money-model equilibrium (`0 ≤ β < 1`, bounded
surpluses) satisfies the Fisher equation and the flow condition (22.2) of the frictionless model
with `ρ = β` (zero real return). -/
theorem moneyOutcome_consistent {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {V y P M W s : ℕ → ℝ}
    (hs : ∀ t, |s t| ≤ K) (h : MoneyRegimes.Eqm β V y P M W s) :
    StarredModel.Consistent perfectForesight β (moneyOutcome P W s) := by
  refine ⟨fun t => rfl, fun t => ?_⟩
  have e := MoneyRegimes.pv_succ hβ0 hβ1 hs (t + 1)
  rw [← (h (t + 1)).2.2, ← (h (t + 1 + 1)).2.2] at e
  funext u
  simp only [moneyOutcome, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Nat.add_sub_cancel]
  linarith

/-- Cochrane (2023), §22.1, p. 495: the money-model path is admissible in the frictionless model
when inflation is bounded (debt is bounded by `K/(1 − β)`, so the transversality condition
holds). -/
theorem moneyOutcome_admissible {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {V y P M W s : ℕ → ℝ}
    (hs : ∀ t, |s t| ≤ K) (h : MoneyRegimes.Eqm β V y P M W s)
    (hπ : BoundedProc (moneyOutcome P W s).pi) :
    StarredModel.Admissible perfectForesight β (moneyOutcome P W s) := by
  have hpvb : ∀ k, |MoneyRegimes.pv β s k| ≤ K / (1 - β) := fun k => by
    have hg : HasSum (fun j : ℕ => K * β ^ j) (K / (1 - β)) := by
      simpa [div_eq_mul_inv] using (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left K
    have := tsum_of_norm_bounded hg (f := fun j => β ^ j * s (k + j)) fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 j), mul_comm K]
      exact mul_le_mul_of_nonneg_left (hs _) (pow_nonneg hβ0 j)
    simpa [MoneyRegimes.pv, Real.norm_eq_abs] using this
  have hβ : |β| < 1 := by rw [abs_of_nonneg hβ0]; exact hβ1
  refine ⟨fun t => rfl, fun t => rfl, hπ, Valuation.tvc_of_bounded _ hβ ⟨K / (1 - β), ?_⟩⟩
  intro t u
  change |W (t + 1) / P (t + 1)| ≤ K / (1 - β)
  rw [(h (t + 1)).2.2]
  exact hpvb (t + 1)

/-- Cochrane (2023), §22.1, pp. 495–497 (OE-2 and OE-1 together): an equilibrium of the money
model (`0 < β < 1`, bounded surpluses and inflation, positive `V`, `y`, nonzero `W`) is at the
same time (OE-2, `MoneyRegimes.oe2`) the unique price path of the active-money regime given `M`
and the unique equilibrium of the active-fiscal regime given `(W, s)`, and (OE-1,
`Equivalence.recipe`) its observable path is the unique admissible equilibrium of every
determinate interest-rate regime `(φ, γ)` of the frictionless model around itself. -/
theorem oe2_oe1 {β K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {V y P M W s : ℕ → ℝ}
    (hV : ∀ t, 0 < V t) (hy : ∀ t, 0 < y t) (hW : ∀ t, W t ≠ 0) (hs : ∀ t, |s t| ≤ K)
    (h : MoneyRegimes.Eqm β V y P M W s) (hπ : BoundedProc (moneyOutcome P W s).pi) :
    ((∀ P' : ℕ → ℝ, (∀ t, M t * V t = P' t * y t) → P' = P) ∧
      ∀ P' M' : ℕ → ℝ, MoneyRegimes.Eqm β V y P' M' W s → P' = P ∧ M' = M) ∧
      ∀ φ γ, Equivalence.Determinate φ γ →
        StarredModel.Eqm perfectForesight β φ γ (moneyOutcome P W s) (moneyOutcome P W s) ∧
          Equivalence.UniqueEqm perfectForesight β φ γ (moneyOutcome P W s) := by
  have hc := moneyOutcome_consistent hβ0.le hβ1 hs h
  exact ⟨MoneyRegimes.oe2 hV hy hW h, Equivalence.recipe perfectForesight hβ0.ne' hc.1 hc.2
    (moneyOutcome_admissible hβ0.le hβ1 hs h hπ)⟩

/-! ### Geometric decay of matrix powers -/

/-- Cochrane (2023), p. 523 and Online Appendix p. 605 ("the eigenvalues of `A` are less than
one"): the powers of a Schur-stable `2 × 2` matrix (the core's root-location criterion, used by
`MarkovRegimes`) decay geometrically, `|(Aᵏ)_{ij}| ≤ C rᵏ` with `r < 1` — chain B's `PowDecay`.
Hence `MarkovRegimes.summable_pow_entry_of_schur` is also an instance of
`PresentValueIdentity.summable_pow_entry`. -/
theorem powDecay_of_schur {A : Matrix (Fin 2) (Fin 2) ℝ} (h : SchurStable (tr2 A) (det2 A)) :
    PresentValueIdentity.PowDecay A := by
  obtain ⟨h1, h2⟩ := (schurStable_iff_roots _ _).mp h
  set ρ := max ‖root₁ (tr2 A) (det2 A)‖ ‖root₂ (tr2 A) (det2 A)‖ with hρdef
  have hρ0 : 0 ≤ ρ := le_max_of_le_left (norm_nonneg _)
  have hρ1 : ρ < 1 := max_lt h1 h2
  set r : ℝ := (1 + ρ) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  set q : ℝ := ρ / r with hq
  have hq0 : 0 ≤ q := div_nonneg hρ0 hr0.le
  have hq1 : q < 1 := (div_lt_one hr0).mpr (by rw [hr]; linarith)
  set G : ℝ := (1 - q)⁻¹ with hG
  have hG0 : 0 ≤ G := inv_nonneg.mpr (by linarith)
  have key : ∀ n : ℕ, ((n : ℝ) + 1) * ρ ^ n ≤ G * r ^ n := by
    intro n
    have hsum : ∑ j ∈ Finset.range (n + 1), q ^ j ≤ G := by
      rw [hG, ← tsum_geometric_of_lt_one hq0 hq1]
      exact (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _
        (fun j _ => pow_nonneg hq0 j)
    have hle : ((n : ℝ) + 1) * q ^ n ≤ ∑ j ∈ Finset.range (n + 1), q ^ j := by
      have : ∑ _j ∈ Finset.range (n + 1), q ^ n ≤ ∑ j ∈ Finset.range (n + 1), q ^ j :=
        Finset.sum_le_sum fun j hj =>
          pow_le_pow_of_le_one hq0 hq1.le (by simp only [Finset.mem_range] at hj; omega)
      simpa using this
    have hpow : ρ ^ n = q ^ n * r ^ n := by rw [← mul_pow, hq, div_mul_cancel₀ _ hr0.ne']
    rw [hpow]
    have hrn := pow_nonneg hr0.le n
    nlinarith
  set N : ℝ := |A 0 0| + |A 0 1| + |A 1 0| + |A 1 1| with hN
  have hN0 : 0 ≤ N := by positivity
  have a00 := abs_nonneg (A 0 0)
  have a01 := abs_nonneg (A 0 1)
  have a10 := abs_nonneg (A 1 0)
  have a11 := abs_nonneg (A 1 1)
  have hAN : ∀ i j, |A i j| ≤ N :=
    Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨by linarith, by linarith⟩,
      Fin.forall_fin_two.mpr ⟨by linarith, by linarith⟩⟩
  have hD : |det2 A| ≤ 1 := h.1.le
  refine ⟨1 + N / r + G * N / r + G / r ^ 2, r, by positivity, hr0.le, hr1, fun k i j => ?_⟩
  have hNr : 0 ≤ N / r := div_nonneg hN0 hr0.le
  have hGNr : 0 ≤ G * N / r := div_nonneg (mul_nonneg hG0 hN0) hr0.le
  have hGr : 0 ≤ G / r ^ 2 := div_nonneg hG0 (pow_nonneg hr0.le 2)
  rcases k with _ | _ | n
  · rw [pow_zero, pow_zero, mul_one]
    have : |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 := by
      rw [Matrix.one_apply]; split_ifs <;> simp
    linarith
  · rw [pow_one, zero_add, pow_one]
    have e : N = N / r * r := by field_simp
    have : N / r * r ≤ (1 + N / r + G * N / r + G / r ^ 2) * r :=
      mul_le_mul_of_nonneg_right (by linarith) hr0.le
    linarith [hAN i j]
  · have hb := abs_pow_entry_le A n i j
    have hc1 := abs_chSeq_le (tr2 A) (det2 A) (n + 1)
    have hc0 := abs_chSeq_le (tr2 A) (det2 A) n
    rw [← hρdef] at hc1 hc0
    have k1 := key (n + 1)
    have k0 := key n
    push_cast at hc1 k1
    have hA := hAN i j
    have hcs1 : |chSeq (tr2 A) (det2 A) (n + 1)| * |A i j| ≤ G * r ^ (n + 1) * N :=
      mul_le_mul (hc1.trans k1) hA (abs_nonneg _) (by positivity)
    have hcs0 : |det2 A| * |chSeq (tr2 A) (det2 A) n| ≤ 1 * (G * r ^ n) :=
      mul_le_mul hD (hc0.trans k0) (abs_nonneg _) zero_le_one
    have e1 : G * r ^ (n + 1) * N = G * N / r * r ^ (n + 2) := by
      field_simp
      ring
    have e0 : 1 * (G * r ^ n) = G / r ^ 2 * r ^ (n + 2) := by
      field_simp
      ring
    have hrn := pow_nonneg hr0.le (n + 2)
    have hfin : G * N / r * r ^ (n + 2) + G / r ^ 2 * r ^ (n + 2) ≤
        (1 + N / r + G * N / r + G / r ^ 2) * r ^ (n + 2) := by
      nlinarith
    rw [show n + 1 + 1 = n + 2 by omega]
    linarith

end Cochrane.ObservationalEquivalence.Links
