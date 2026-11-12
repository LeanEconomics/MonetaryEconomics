/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.FiscalRulesTargetOpen
import AssetsRulesBalanceSheets.ExpectationsMeasureIID

/-!
# Theorem FR (d): prices bounded away from zero need a bounded real-rate factor

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.3.2,
eqs. (9.8)–(9.12), pp. 266–267 (Theorem FR, error E9.9).

`FiscalRulesTargetMeasure.fr_unique_stochastic_below` proves Theorem FR (d) for prices bounded away
from zero under an extra hypothesis: the target's cumulative real-rate factor
`∏ᵢ E_{t+i}(P*_{t+i}/P*_{t+i+1})⁻¹` is bounded. This module shows the hypothesis is needed, even
when the target's present value is predetermined and initial debt is `b̄`.

## The counterexample

* State space `Ω = ℕ → ℝ` with i.i.d. biased coins (`biasCoin`, `P(up) = p = (4 − 2β)/(8 − 3β)`),
  the natural filtration, and `E_t` = Mathlib's `condExp` (`Sys`, via `ExpectationsMeasureIID`).
  `sys_singleton`: every history is null, so the space is not a finite tree.
* Target: `a_0 = 1`, `a_{t+1} = (a_t + 2 − β)/2` after an up coin at `t` and `1` otherwise, so
  `a_{t+1}` is known at `t`, and `P*_t = a_t − β a_{t+1}`. The two date-`t` values of `P*` stand
  in the fixed ratio `κ = 1 − β/2` (`tgt_eq`).
* A sunspot state `S_t` is a random walk started at `1` and absorbed at `0`. Under the target's
  risk-adjusted measure (step density `∝ 1/P*`), `M_t = c (1 − κ'^{S_t})` is a martingale
  (`qmart`). Under the true coin the walk drifts down; the Lyapunov function `Ψ` contracts
  (`psi_step`, `psi_iter`).
* Equilibrium: `Ã_t = a_t + β^{−t} M_t`, `V_0 = a_0`, `V_{t+1} = V_t B_t/Ã_t` and
  `P_t = V_t P*_t/Ã_t`, with `b_t = b̄ + θ (V_t − a_t)`.

## Main results

* `rate` — (9.12); `bv_flow` — (9.8); `tvc` — transversality; `valuation` — (9.9) as a `HasSum`.
* `counter_ruleEqm` — the construction is a `RuleEqm`.
* `Pv_bounds` — prices are bounded away from zero.
* `fr_below_counterexample` — the counterexample: every other hypothesis of
  `fr_unique_stochastic_below` holds, but `P ≠ P*` and no bound `L` exists.
* `fr_d_dividing_line` — the precise dividing line for `b₀ = b̄`:
  * prices bounded above give uniqueness for every target (`fr_d_news`);
  * prices bounded away from zero do not, without a bounded real-rate factor.
* `fr_below_link` (**link**) — for the book's constant target the hypothesis holds with `L = 1`,
  so the measure theorem gives the core `FiscalRules.fr_unique_bounded` (bounded-away-from-zero
  case) on bridged finite systems.
-/

namespace Cochrane.AssetsRulesBalanceSheets.FiscalRulesBelowCounter

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure ExpectationsMeasureIID FiscalRulesMeasure FiscalRulesTargetMeasure
open FiscalRulesTargetOpen

variable {Ω' : Type*}

/-! ### A biased `±1` coin -/

/-- Cochrane (2023), §9.3.2, p. 267 (the counterexample's shocks): the coin `p δ₁ + (1 − p) δ₋₁`.
-/
noncomputable def biasMeasure (p : ℝ) : Measure ℝ :=
  ENNReal.ofReal p • Measure.dirac 1 + ENNReal.ofReal (1 - p) • Measure.dirac (-1)

/-- Cochrane (2023), §9.3.2, p. 267: for `0 ≤ p ≤ 1` the biased coin has total mass one. -/
theorem biasMeasure_univ {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : biasMeasure p Set.univ = 1 := by
  simp only [biasMeasure, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  simp

/-- Cochrane (2023), §9.3.2, p. 267: the biased coin as a probability measure. -/
noncomputable def biasCoin (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : ProbabilityMeasure ℝ :=
  ⟨biasMeasure p, ⟨biasMeasure_univ h0 h1⟩⟩

/-- Cochrane (2023), §9.3.2, p. 267: `∫ f d(biased coin) = p f(1) + (1 − p) f(−1)`. -/
theorem integral_biasCoin {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (f : ℝ → ℝ) :
    ∫ x, f x ∂(biasCoin p h0 h1 : Measure ℝ) = p * f 1 + (1 - p) * f (-1) := by
  change ∫ x, f x ∂biasMeasure p = _
  rw [biasMeasure, integral_add_measure
    ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul]

/-- Cochrane (2023), §9.3.2, p. 267: **branch forecasts** — on the i.i.d. biased-coin system, a
variable equal to `f` if the date-`t+1` coin is up (`ω_{t+1} > 0`) and to `g` otherwise, with `f`,
`g` bounded and known at `t`, has forecast `E_t = p f + (1 − p) g` a.e. -/
theorem E_branch {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {t : ℕ} {f g : (ℕ → ℝ) → ℝ} {C : ℝ}
    (hf : StronglyMeasurable[(iidSystem (biasCoin p h0 h1)).𝓕 t] f)
    (hg : StronglyMeasurable[(iidSystem (biasCoin p h0 h1)).𝓕 t] g)
    (hfC : ∀ ω, |f ω| ≤ C) (hgC : ∀ ω, |g ω| ≤ C) :
    (iidSystem (biasCoin p h0 h1)).E t (fun ω => if 0 < ω (t + 1) then f ω else g ω)
      =ᵐ[(iidSystem (biasCoin p h0 h1)).μ] fun ω => p * f ω + (1 - p) * g ω := by
  set S := iidSystem (biasCoin p h0 h1) with hS
  set I : ℝ → ℝ := fun x => if 0 < x then 1 else 0 with hI
  have hIm : Measurable I := Measurable.ite measurableSet_Ioi measurable_const measurable_const
  have hIi : Integrable (fun ω : ℕ → ℝ => I (ω (t + 1))) S.μ :=
    Integrable.of_bound (hIm.comp (measurable_pi_apply (t + 1))).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by
        simp only [hI, Real.norm_eq_abs]
        split_ifs <;> simp)
  have hJi : Integrable (fun ω : ℕ → ℝ => 1 - I (ω (t + 1))) S.μ := (integrable_const 1).sub hIi
  have hEI : S.E t (fun ω => I (ω (t + 1))) =ᵐ[S.μ] fun _ => p := by
    filter_upwards [E_shock_fun (biasCoin p h0 h1) t hIm] with ω h
    rw [h, integral_biasCoin]
    simp [hI]
  have hEJ : S.E t (fun ω => 1 - I (ω (t + 1))) =ᵐ[S.μ] fun _ => 1 - p := by
    filter_upwards [S.E_sub (integrable_const 1) hIi t, hEI] with ω e1 e2
    change S.E t ((fun _ => (1 : ℝ)) - fun ω => I (ω (t + 1))) ω = 1 - p
    rw [e1, Pi.sub_apply, S.E_const, e2]
  have e : (fun ω => if 0 < ω (t + 1) then f ω else g ω) =
      f * (fun ω => I (ω (t + 1))) + g * (fun ω => 1 - I (ω (t + 1))) := by
    funext ω
    simp only [Pi.add_apply, Pi.mul_apply, hI]
    split_ifs <;> ring
  rw [e]
  have hf1 := S.E_pullOut hf (Eventually.of_forall hfC) hIi
  have hg1 := S.E_pullOut hg (Eventually.of_forall hgC) hJi
  have hfi : Integrable (f * fun ω => I (ω (t + 1))) S.μ :=
    hIi.bdd_mul (hf.mono (S.𝓕.le t)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hfC ω)
  have hgi : Integrable (g * fun ω => 1 - I (ω (t + 1))) S.μ :=
    hJi.bdd_mul (hg.mono (S.𝓕.le t)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgC ω)
  filter_upwards [S.E_add hfi hgi t, hf1, hg1, hEI, hEJ] with ω e1 e2 e3 e4 e5
  rw [e1, Pi.add_apply, e2, e3, Pi.mul_apply, Pi.mul_apply, e4, e5]
  ring

/-! ### Parameters -/

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the ratio `κ = 1 − β/2` of the target's two
date-`t+1` values. -/
noncomputable def kap (β : ℝ) : ℝ := (2 - β) / 2

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the ratio `κ' = 1 − β/4` of the risk-adjusted
probabilities of the two branches. -/
noncomputable def kq (β : ℝ) : ℝ := (4 - β) / 4

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the probability of an "up" coin,
`p = κ/(κ + κ') = (4 − 2β)/(8 − 3β) < 1/2`. -/
noncomputable def pr (β : ℝ) : ℝ := (4 - 2 * β) / (8 - 3 * β)

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the scale `c = 16/(β(1 − β))` of the
sunspot component. -/
noncomputable def cc (β : ℝ) : ℝ := 16 / (β * (1 - β))

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the base `x = (8 − 3β)/(8 − 4β) > 1` of the
Lyapunov function `x^{S_t}`. -/
noncomputable def xL (β : ℝ) : ℝ := (8 - 3 * β) / (8 - 4 * β)

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the contraction factor
`λ = max(p x + (1 − p)/x, β) < 1`. -/
noncomputable def lam (β : ℝ) : ℝ := max (pr β * xL β + (1 - pr β) / xL β) β

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the parameter facts used below. -/
theorem params {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    0 < kap β ∧ kap β < 1 ∧ 0 < kq β ∧ kq β < 1 ∧ 0 < pr β ∧ pr β < 1 ∧
      pr β * kq β = kap β * (1 - pr β) ∧ 1 ≤ xL β ∧ pr β * xL β = 1 / 2 ∧
      pr β * xL β + (1 - pr β) / xL β < 1 ∧ lam β < 1 ∧ β ≤ lam β ∧
      pr β * xL β + (1 - pr β) / xL β ≤ lam β ∧ cc β * (1 - kq β) = 4 / (1 - β) ∧ 0 < cc β := by
  have h1 : (0 : ℝ) < 8 - 3 * β := by linarith
  have h2 : (0 : ℝ) < 8 - 4 * β := by linarith
  have h3 : (0 : ℝ) < 1 - β := by linarith
  have hpx : pr β * xL β = 1 / 2 := by
    rw [pr, xL, div_mul_div_comm, div_eq_div_iff (mul_pos h1 h2).ne' two_ne_zero]
    ring
  have hq : (1 - pr β) / xL β = (4 - β) * (8 - 4 * β) / (8 - 3 * β) ^ 2 := by
    rw [pr, xL, one_sub_div h1.ne', div_div_div_eq,
      div_eq_div_iff (mul_pos h1 h1).ne' (pow_pos h1 2).ne']
    ring
  have hlt : pr β * xL β + (1 - pr β) / xL β < 1 := by
    rw [hpx, hq, ← sub_pos]
    have e : 1 - (1 / 2 + (4 - β) * (8 - 4 * β) / (8 - 3 * β) ^ 2) =
        β ^ 2 / (2 * (8 - 3 * β) ^ 2) := by
      have hu : (0 : ℝ) < (8 - 3 * β) ^ 2 := pow_pos h1 2
      rw [div_add_div _ _ two_ne_zero hu.ne', one_sub_div (by positivity),
        div_eq_div_iff (by positivity) (by positivity)]
      ring
    rw [e]
    positivity
  refine ⟨by simp only [kap]; linarith, by simp only [kap]; linarith, by simp only [kq]; linarith,
    by simp only [kq]; linarith, by simp only [pr]; exact div_pos (by linarith) h1,
    by rw [pr, div_lt_one h1]; linarith, ?_, by rw [xL, le_div_iff₀ h2]; linarith, hpx, hlt,
    max_lt hlt hβ1, le_max_right _ _, le_max_left _ _, ?_, by simp only [cc]; positivity⟩
  · rw [pr, kq, kap, one_sub_div h1.ne', div_mul_div_comm, div_mul_div_comm,
      div_eq_div_iff (by positivity) (by positivity)]
    ring
  · rw [cc, kq, div_mul_eq_mul_div, div_eq_div_iff (by positivity) h3.ne']
    ring

/-! ### The processes (state space `ℕ → ℝ`, coin `ω_t > 0` = "up") -/

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the target's present value `a_t`, with
`a_0 = 1` and `a_{t+1} = (a_t + 2 − β)/2` after an up coin at `t`, `1` otherwise (known at `t`). -/
noncomputable def av (β : ℝ) : ℕ → (ℕ → ℝ) → ℝ
  | 0 => fun _ => 1
  | t + 1 => fun ω => if 0 < ω t then (av β t ω + 2 - β) / 2 else 1

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the target `P*_t = a_t − β a_{t+1}`. -/
noncomputable def tgt (β : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ := av β t ω - β * av β (t + 1) ω

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the sunspot state `S_t ∈ ℕ` — a random walk
started at `1`, up with an up coin, absorbed at `0`. -/
noncomputable def Sw : ℕ → (ℕ → ℝ) → ℕ
  | 0 => fun _ => 1
  | t + 1 => fun ω => if Sw t ω = 0 then 0 else if 0 < ω (t + 1) then Sw t ω + 1 else Sw t ω - 1

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the sunspot component `M_t = c (1 − κ'^{S_t})`
(a martingale under the target's risk-adjusted measure). -/
noncomputable def Mv (β : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ := cc β * (1 - kq β ^ Sw t ω)

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): `Ã_t = a_t + β^{−t} M_t`. -/
noncomputable def At (β : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ := av β t ω + (β ^ t)⁻¹ * Mv β t ω

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): `B_t = a_{t+1} + β^{−(t+1)} M_t`, known at
`t`, with `β B_t = Ã_t − P*_t`. -/
noncomputable def Bv (β : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ := av β (t + 1) ω + (β ^ (t + 1))⁻¹ * Mv β t ω

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the value of the price path `V_t = ∑ⱼ βʲ
P_{t+j}`, `V_0 = 1 = a_0` (so `b₀ = b̄`), `V_{t+1} = V_t B_t / Ã_t` (known at `t`). -/
noncomputable def Vv (β : ℝ) : ℕ → (ℕ → ℝ) → ℝ
  | 0 => fun _ => 1
  | t + 1 => fun ω => Vv β t ω * Bv β t ω / At β t ω

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the price level `P_t = V_t P*_t / Ã_t`. -/
noncomputable def Pv (β : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ := Vv β t ω * tgt β t ω / At β t ω

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): real debt `b_t = b̄ + θ (V_t − a_t)`. -/
noncomputable def bv (β θ bbar : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ := bbar + θ * (Vv β t ω - av β t ω)

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): after absorption, `Φ_t = β^{t−τ}` (`0`
before absorption). -/
noncomputable def Phi (β : ℝ) : ℕ → (ℕ → ℝ) → ℝ
  | 0 => fun _ => 0
  | t + 1 => fun ω => if Sw t ω = 0 then β * Phi β t ω else if Sw (t + 1) ω = 0 then 1 else 0

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the Lyapunov function
`Ψ_t = x^{S_t} 1{S_t ≥ 1} + Φ_t`. -/
noncomputable def Psi (β : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ :=
  (if Sw t ω = 0 then 0 else xL β ^ Sw t ω) + Phi β t ω

/-! ### Measurability -/

variable (ν : ProbabilityMeasure ℝ)

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the coin at `s ≤ t` is known at `t`. -/
theorem meas_up {s t : ℕ} (hst : s ≤ t) :
    MeasurableSet[(iidSystem ν).𝓕 t] {ω : ℕ → ℝ | 0 < ω s} :=
  measurableSet_lt measurable_const (measurable_shock ν hst)

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): `a_t` is known at `t`. -/
theorem av_meas (β : ℝ) (t : ℕ) : Measurable[(iidSystem ν).𝓕 t] (av β t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact Measurable.ite (meas_up ν (Nat.le_succ t))
      ((((ih.mono ((iidSystem ν).𝓕.mono (Nat.le_succ t)) le_rfl).add_const 2).sub_const
        β).div_const 2)
      measurable_const

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): `a_{t+1}` is known at `t`. -/
theorem av_pred (β : ℝ) (t : ℕ) : Measurable[(iidSystem ν).𝓕 t] (av β (t + 1)) :=
  Measurable.ite (meas_up ν le_rfl) ((((av_meas ν β t).add_const 2).sub_const β).div_const 2)
    measurable_const

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the target is known at `t`. -/
theorem tgt_meas (β : ℝ) (t : ℕ) : Measurable[(iidSystem ν).𝓕 t] (tgt β t) :=
  (av_meas ν β t).sub ((av_pred ν β t).const_mul β)

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the sunspot state is known at `t`. -/
theorem Sw_meas (t : ℕ) : Measurable[(iidSystem ν).𝓕 t] (Sw t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have ih' := ih.mono ((iidSystem ν).𝓕.mono (Nat.le_succ t)) le_rfl
    exact Measurable.ite (ih' (measurableSet_singleton 0)) measurable_const
      (Measurable.ite (meas_up ν le_rfl)
        ((Measurable.of_discrete (f := fun n : ℕ => n + 1)).comp ih')
        ((Measurable.of_discrete (f := fun n : ℕ => n - 1)).comp ih'))

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): any real function of the sunspot state is
known at `t`. -/
theorem Sw_fun_meas (t : ℕ) (f : ℕ → ℝ) :
    Measurable[(iidSystem ν).𝓕 t] (fun ω => f (Sw t ω)) :=
  (Measurable.of_discrete (f := f)).comp (Sw_meas ν t)

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): `M_t`, `Ã_t` and `B_t` are known at `t`. -/
theorem MAB_meas (β : ℝ) (t : ℕ) : Measurable[(iidSystem ν).𝓕 t] (Mv β t) ∧
    Measurable[(iidSystem ν).𝓕 t] (At β t) ∧ Measurable[(iidSystem ν).𝓕 t] (Bv β t) := by
  have hM : Measurable[(iidSystem ν).𝓕 t] (Mv β t) :=
    Sw_fun_meas ν t (fun n => cc β * (1 - kq β ^ n))
  exact ⟨hM, (av_meas ν β t).add (hM.const_mul _), (av_pred ν β t).add (hM.const_mul _)⟩

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): `V_t` is known at `t`. -/
theorem Vv_meas (β : ℝ) (t : ℕ) : Measurable[(iidSystem ν).𝓕 t] (Vv β t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hle := (iidSystem ν).𝓕.mono (Nat.le_succ t)
    obtain ⟨-, hA, hB⟩ := MAB_meas ν β t
    exact ((ih.mul hB).div hA).mono hle le_rfl

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): `V_{t+1}` is known at `t`. -/
theorem Vv_pred (β : ℝ) (t : ℕ) : Measurable[(iidSystem ν).𝓕 t] (Vv β (t + 1)) := by
  obtain ⟨-, hA, hB⟩ := MAB_meas ν β t
  exact ((Vv_meas ν β t).mul hB).div hA

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the price level is known at `t`. -/
theorem Pv_meas (β : ℝ) (t : ℕ) : Measurable[(iidSystem ν).𝓕 t] (Pv β t) :=
  ((Vv_meas ν β t).mul (tgt_meas ν β t)).div (MAB_meas ν β t).2.1

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): `Φ_t` and `Ψ_t` are known at `t`. -/
theorem Phi_meas (β : ℝ) (t : ℕ) : Measurable[(iidSystem ν).𝓕 t] (Phi β t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hle := (iidSystem ν).𝓕.mono (Nat.le_succ t)
    exact Measurable.ite (((Sw_meas ν t).mono hle le_rfl) (measurableSet_singleton 0))
      ((ih.mono hle le_rfl).const_mul β)
      (Measurable.ite ((Sw_meas ν (t + 1)) (measurableSet_singleton 0)) measurable_const
        measurable_const)

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): `Ψ_t` is known at `t`. -/
theorem Psi_meas (β : ℝ) (t : ℕ) : Measurable[(iidSystem ν).𝓕 t] (Psi β t) :=
  (Sw_fun_meas ν t (fun n => if n = 0 then 0 else xL β ^ n)).add (Phi_meas ν β t)

/-! ### Pathwise bounds and invariants -/

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): `1 ≤ a_t ≤ 2 − β`. -/
theorem av_bounds {β : ℝ} (hβ1 : β < 1) (t : ℕ) (ω : ℕ → ℝ) :
    1 ≤ av β t ω ∧ av β t ω ≤ 2 - β := by
  induction t with
  | zero => simp only [av]; constructor <;> linarith
  | succ t ih =>
    simp only [av]
    split_ifs <;> constructor <;> linarith [ih.1, ih.2]

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): `P*_t = κ (a_t − β)` after an up coin at `t`,
`a_t − β` otherwise. -/
theorem tgt_eq (β : ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    tgt β t ω = if 0 < ω t then kap β * (av β t ω - β) else av β t ω - β := by
  simp only [tgt, av, kap]
  split_ifs <;> ring

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): `(2 − β)(1 − β)/2 ≤ P*_t ≤ 2`. -/
theorem tgt_bounds {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (t : ℕ) (ω : ℕ → ℝ) :
    (2 - β) * (1 - β) / 2 ≤ tgt β t ω ∧ tgt β t ω ≤ 2 := by
  rw [tgt_eq]
  obtain ⟨h1, h2⟩ := av_bounds hβ1 t ω
  simp only [kap]
  split_ifs <;> constructor <;> nlinarith

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the target is positive. -/
theorem tgt_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (t : ℕ) (ω : ℕ → ℝ) : 0 < tgt β t ω := by
  have h := (tgt_bounds hβ0 hβ1 t ω).1
  have : 0 < (2 - β) * (1 - β) / 2 := by
    have : 0 < (2 - β) * (1 - β) := mul_pos (by linarith) (by linarith)
    linarith
  linarith

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the sunspot state is absorbed at `0`. -/
theorem Sw_succ_zero {t : ℕ} {ω : ℕ → ℝ} (h : Sw t ω = 0) : Sw (t + 1) ω = 0 := by
  simp [Sw, h]

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): `S_t ≤ t + 1`. -/
theorem Sw_le (t : ℕ) (ω : ℕ → ℝ) : Sw t ω ≤ t + 1 := by
  induction t with
  | zero => simp [Sw]
  | succ t ih =>
    simp only [Sw]
    split_ifs <;> omega

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): `M_t = 0` when absorbed, and
`c (1 − κ') ≤ M_t ≤ c` otherwise. -/
theorem Mv_bounds {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (t : ℕ) (ω : ℕ → ℝ) :
    (Sw t ω = 0 → Mv β t ω = 0) ∧ (Sw t ω ≠ 0 → cc β * (1 - kq β) ≤ Mv β t ω) ∧
      0 ≤ Mv β t ω ∧ Mv β t ω ≤ cc β := by
  obtain ⟨-, -, hk0, hk1, -, -, -, -, -, -, -, -, -, -, hc⟩ := params hβ0 hβ1
  have hpow : kq β ^ Sw t ω ≤ 1 := pow_le_one₀ hk0.le hk1.le
  have hpow0 : 0 ≤ kq β ^ Sw t ω := pow_nonneg hk0.le _
  refine ⟨fun h => by simp [Mv, h], fun h => ?_, ?_, ?_⟩
  · have : kq β ^ Sw t ω ≤ kq β ^ 1 :=
      pow_le_pow_of_le_one hk0.le hk1.le (Nat.one_le_iff_ne_zero.2 h)
    simp only [Mv, pow_one] at this ⊢
    exact mul_le_mul_of_nonneg_left (by linarith) hc.le
  · simp only [Mv]
    exact mul_nonneg hc.le (by linarith)
  · simp only [Mv]
    nlinarith

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): `P*_t < a_t ≤ Ã_t`, so `Ã_t > 0`. -/
theorem At_bounds {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (t : ℕ) (ω : ℕ → ℝ) :
    tgt β t ω < At β t ω ∧ av β t ω ≤ At β t ω ∧ 0 < At β t ω := by
  have h1 := av_bounds hβ1 t ω
  have h2 := av_bounds hβ1 (t + 1) ω
  have h3 := (Mv_bounds hβ0 hβ1 t ω).2.2.1
  have h4 : av β t ω ≤ At β t ω := by
    simp only [At]
    have : 0 ≤ (β ^ t)⁻¹ * Mv β t ω := mul_nonneg (inv_nonneg.2 (pow_pos hβ0 t).le) h3
    linarith
  refine ⟨?_, h4, by linarith⟩
  simp only [tgt]
  nlinarith

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): `β B_t = Ã_t − P*_t`. -/
theorem Bv_eq {β : ℝ} (hβ0 : 0 < β) (t : ℕ) (ω : ℕ → ℝ) :
    β * Bv β t ω = At β t ω - tgt β t ω := by
  have e : β * (β ^ (t + 1))⁻¹ = (β ^ t)⁻¹ := by
    rw [pow_succ, mul_inv, mul_comm ((β ^ t)⁻¹), ← mul_assoc, mul_inv_cancel₀ hβ0.ne', one_mul]
  simp only [Bv, At, tgt]
  linear_combination Mv β t ω * e

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the discounted value evolves by
`β^{t+1} V_{t+1} = β^t V_t (1 − P*_t/Ã_t)`. -/
theorem Vv_fac {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (t : ℕ) (ω : ℕ → ℝ) :
    β ^ (t + 1) * Vv β (t + 1) ω = β ^ t * Vv β t ω * (1 - tgt β t ω / At β t ω) := by
  have hA := (At_bounds hβ0 hβ1 t ω).2.2
  have hB := Bv_eq hβ0 t ω
  change β ^ (t + 1) * (Vv β t ω * Bv β t ω / At β t ω) = _
  rw [one_sub_div hA.ne', ← hB, pow_succ]
  field_simp

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): before absorption `P*_t/Ã_t ≤ (1 − β)βᵗ/2`. -/
theorem ratio_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {t : ℕ} {ω : ℕ → ℝ} (hS : Sw t ω ≠ 0) :
    tgt β t ω / At β t ω ≤ (1 - β) * β ^ t / 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hcq, -⟩ := params hβ0 hβ1
  obtain ⟨-, h2, -, -⟩ := Mv_bounds hβ0 hβ1 t ω
  have hM := h2 hS
  rw [hcq] at hM
  obtain ⟨-, -, hA⟩ := At_bounds hβ0 hβ1 t ω
  have hβt : 0 < β ^ t := pow_pos hβ0 t
  have h1β : 0 < 1 - β := by linarith
  have hav := (av_bounds hβ1 t ω).1
  have htg := (tgt_bounds hβ0 hβ1 t ω).2
  have hA' : (β ^ t)⁻¹ * (4 / (1 - β)) ≤ At β t ω := by
    simp only [At]
    have := mul_le_mul_of_nonneg_left hM (inv_nonneg.2 hβt.le)
    linarith
  rw [div_le_iff₀ hA]
  have e : (1 - β) * β ^ t / 2 * ((β ^ t)⁻¹ * (4 / (1 - β))) = 2 := by
    field_simp
    ring
  have h3 : 0 ≤ (1 - β) * β ^ t / 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hA' h3]

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): **the pathwise invariants** — `V_t > 0`,
`0 ≤ Φ_t ≤ 1`; before absorption `(1 + βᵗ)/2 ≤ βᵗ V_t ≤ 1` and `Φ_t = 0`; after absorption
`a_t ≤ 2(2 − β) V_t` and `βᵗ V_t ≤ a_t Φ_t`. -/
theorem path_invariants {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ω : ℕ → ℝ) (t : ℕ) :
    0 < Vv β t ω ∧ 0 ≤ Phi β t ω ∧ Phi β t ω ≤ 1 ∧
      (Sw t ω ≠ 0 → (1 + β ^ t) / 2 ≤ β ^ t * Vv β t ω ∧ β ^ t * Vv β t ω ≤ 1 ∧
        Phi β t ω = 0) ∧
      (Sw t ω = 0 → av β t ω ≤ 2 * (2 - β) * Vv β t ω ∧
        β ^ t * Vv β t ω ≤ av β t ω * Phi β t ω) := by
  induction t with
  | zero =>
    refine ⟨by simp [Vv], by simp [Phi], by simp [Phi], fun _ => ?_, fun h => by simp [Sw] at h⟩
    simp [Vv, Phi]
  | succ t ih =>
    obtain ⟨hV, hP0, hP1, hA, hB⟩ := ih
    have hβt : 0 < β ^ t := pow_pos hβ0 t
    have hβt1 : β ^ t ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
    have hβs : 0 < β ^ (t + 1) := pow_pos hβ0 (t + 1)
    have hβs1 : β ^ (t + 1) ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
    have hav := av_bounds hβ1 t ω
    have hav' := av_bounds hβ1 (t + 1) ω
    have hfac := Vv_fac hβ0 hβ1 t ω
    by_cases hS : Sw t ω = 0
    · -- already absorbed
      obtain ⟨hB1, hB2⟩ := hB hS
      have hS' := Sw_succ_zero hS
      have hM := (Mv_bounds hβ0 hβ1 t ω).1 hS
      have hPhi : Phi β (t + 1) ω = β * Phi β t ω := by simp [Phi, hS]
      have hVe : Vv β (t + 1) ω = Vv β t ω * av β (t + 1) ω / av β t ω := by
        change Vv β t ω * Bv β t ω / At β t ω = _
        simp only [Bv, At, hM, mul_zero, add_zero]
      have hpos : 0 < Vv β (t + 1) ω := by
        rw [hVe]
        exact div_pos (mul_pos hV (by linarith)) (by linarith)
      refine ⟨hpos, by rw [hPhi]; positivity, by rw [hPhi]; nlinarith, fun h => absurd hS' h,
        fun _ => ⟨?_, ?_⟩⟩
      · rw [hVe]
        have ha0 : 0 < av β t ω := by linarith
        rw [mul_div_assoc', le_div_iff₀ ha0]
        nlinarith
      · rw [hVe, hPhi]
        have ha0 : 0 < av β t ω := by linarith
        rw [pow_succ]
        have e : β ^ t * β * (Vv β t ω * av β (t + 1) ω / av β t ω) =
            β * (β ^ t * Vv β t ω) * av β (t + 1) ω / av β t ω := by ring
        rw [e, div_le_iff₀ ha0]
        have := mul_le_mul_of_nonneg_left hB2 (mul_nonneg hβ0.le (by linarith : (0 : ℝ) ≤
          av β (t + 1) ω))
        nlinarith
    · -- not yet absorbed
      obtain ⟨hA1, hA2, hA3⟩ := hA hS
      have hd := ratio_le hβ0 hβ1 hS
      obtain ⟨hlt, -, hApos⟩ := At_bounds hβ0 hβ1 t ω
      have hd0 : 0 < tgt β t ω / At β t ω := div_pos (tgt_pos hβ0 hβ1 t ω) hApos
      have hd1 : tgt β t ω / At β t ω < 1 := (div_lt_one hApos).2 hlt
      have hpos : 0 < Vv β (t + 1) ω := by
        have : 0 < β ^ (t + 1) * Vv β (t + 1) ω := by
          rw [hfac]
          exact mul_pos (mul_pos hβt hV) (by linarith)
        exact pos_of_mul_pos_right this hβs.le
      have hup : β ^ (t + 1) * Vv β (t + 1) ω ≤ 1 := by
        rw [hfac]
        have : β ^ t * Vv β t ω * (1 - tgt β t ω / At β t ω) ≤ β ^ t * Vv β t ω :=
          mul_le_of_le_one_right (mul_pos hβt hV).le (by linarith)
        linarith
      have hlo : (1 + β ^ (t + 1)) / 2 ≤ β ^ (t + 1) * Vv β (t + 1) ω := by
        rw [hfac, pow_succ]
        have h1 : 0 ≤ 1 - (1 - β) * β ^ t / 2 := by nlinarith
        have h2 := mul_le_mul hA1 (by linarith : 1 - (1 - β) * β ^ t / 2 ≤
          1 - tgt β t ω / At β t ω) h1 (mul_pos hβt hV).le
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - β) hβt.le)
          (by linarith : (0 : ℝ) ≤ 1 - β ^ t)]
      by_cases hS' : Sw (t + 1) ω = 0
      · have hPhi : Phi β (t + 1) ω = 1 := by simp [Phi, hS, hS']
        refine ⟨hpos, by rw [hPhi]; norm_num, by rw [hPhi], fun h => absurd hS' h,
          fun _ => ⟨?_, ?_⟩⟩
        · have : β ^ (t + 1) * Vv β (t + 1) ω ≤ Vv β (t + 1) ω :=
            mul_le_of_le_one_left hpos.le hβs1
          nlinarith
        · rw [hPhi]
          linarith
      · have hPhi : Phi β (t + 1) ω = 0 := by simp [Phi, hS, hS']
        exact ⟨hpos, by rw [hPhi], by rw [hPhi]; norm_num, fun _ => ⟨hlo, hup, hPhi⟩,
          fun h => absurd h hS'⟩

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the lower bound `m_P = m/(2(2 + c))` of the
price level, `m = (2 − β)(1 − β)/2` the lower bound of the target. -/
noncomputable def mP (β : ℝ) : ℝ := (2 - β) * (1 - β) / 2 / (2 * (2 + cc β))

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): `m_P > 0`. -/
theorem mP_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : 0 < mP β := by
  have := (params hβ0 hβ1).2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have h : 0 < (2 - β) * (1 - β) := mul_pos (by linarith) (by linarith)
  unfold mP
  positivity

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): **prices are bounded away from zero**,
`P_t ≥ m_P > 0` on every path, and `P_t ≤ V_t`. -/
theorem Pv_bounds {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (t : ℕ) (ω : ℕ → ℝ) :
    mP β ≤ Pv β t ω ∧ Pv β t ω ≤ Vv β t ω := by
  obtain ⟨hV, -, -, hA, hB⟩ := path_invariants hβ0 hβ1 ω t
  obtain ⟨hlt, -, hApos⟩ := At_bounds hβ0 hβ1 t ω
  have hc := (params hβ0 hβ1).2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have htg := tgt_bounds hβ0 hβ1 t ω
  have htp := tgt_pos hβ0 hβ1 t ω
  have hav := av_bounds hβ1 t ω
  have hm : 0 < (2 - β) * (1 - β) / 2 := by
    have : 0 < (2 - β) * (1 - β) := mul_pos (by linarith) (by linarith)
    linarith
  refine ⟨?_, ?_⟩
  · unfold Pv
    rw [le_div_iff₀ hApos]
    by_cases hS : Sw t ω = 0
    · obtain ⟨hB1, -⟩ := hB hS
      have hM := (Mv_bounds hβ0 hβ1 t ω).1 hS
      have hAe : At β t ω = av β t ω := by simp [At, hM]
      rw [hAe]
      have h1 : mP β * av β t ω ≤ (2 - β) * (1 - β) / 2 / (2 * (2 - β)) * av β t ω := by
        refine mul_le_mul_of_nonneg_right ?_ (by linarith)
        unfold mP
        exact div_le_div_of_nonneg_left hm.le (by linarith) (by linarith)
      have h2 : (2 - β) * (1 - β) / 2 / (2 * (2 - β)) * av β t ω ≤
          (2 - β) * (1 - β) / 2 * Vv β t ω := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith
      nlinarith
    · obtain ⟨hA1, -, -⟩ := hA hS
      have hβt : 0 < β ^ t := pow_pos hβ0 t
      have hβt1 : β ^ t ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
      set y := (β ^ t)⁻¹ with hy
      have hy1 : 1 ≤ y := one_le_inv₀ hβt |>.2 hβt1
      have hVy : y / 2 ≤ Vv β t ω := by
        have : Vv β t ω = y * (β ^ t * Vv β t ω) := by
          rw [hy, ← mul_assoc, inv_mul_cancel₀ hβt.ne', one_mul]
        rw [this]
        nlinarith
      have hAle : At β t ω ≤ 2 + y * cc β := by
        simp only [At]
        have := (Mv_bounds hβ0 hβ1 t ω).2.2.2
        nlinarith [mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ y)]
      have h1 : mP β * At β t ω ≤ mP β * (2 + y * cc β) :=
        mul_le_mul_of_nonneg_left hAle (mP_pos hβ0 hβ1).le
      have h2 : mP β * (2 + y * cc β) ≤ (2 - β) * (1 - β) / 2 * (y / 2) := by
        unfold mP
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      nlinarith [mul_le_mul htg.1 hVy (by positivity) htp.le]
  · unfold Pv
    rw [div_le_iff₀ hApos]
    nlinarith

/-- Cochrane (2023), eq. (9.9), p. 266 (counterexample): the value of the price path obeys
`V_t = P_t + β V_{t+1}` on every path. -/
theorem Vv_rec {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (t : ℕ) (ω : ℕ → ℝ) :
    Vv β t ω = Pv β t ω + β * Vv β (t + 1) ω := by
  have hA := (At_bounds hβ0 hβ1 t ω).2.2
  have hB := Bv_eq hβ0 t ω
  change Vv β t ω = Vv β t ω * tgt β t ω / At β t ω + β * (Vv β t ω * Bv β t ω / At β t ω)
  rw [show β * (Vv β t ω * Bv β t ω / At β t ω) = Vv β t ω * (β * Bv β t ω) / At β t ω by ring,
    hB]
  field_simp
  ring

/-- Cochrane (2023), eq. (9.8), p. 266 (counterexample): real debt obeys the flow
`b_t = (1 − β) b̄ + θ (P_t − P*_t) + β b_{t+1}` on every path. -/
theorem bv_flow {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (θ bbar : ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    bv β θ bbar t ω = (1 - β) * bbar + θ * (Pv β t ω - tgt β t ω) + β * bv β θ bbar (t + 1) ω := by
  simp only [bv]
  rw [Vv_rec hβ0 hβ1 t ω]
  simp only [tgt]
  ring

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): `0 ≤ Ψ_t ≤ x^{t+1} + 1`, `βᵗ V_t ≤ 2 Ψ_t` and
`βᵗ V_t ≤ 2`. -/
theorem Psi_bounds {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (t : ℕ) (ω : ℕ → ℝ) :
    0 ≤ Psi β t ω ∧ Psi β t ω ≤ xL β ^ (t + 1) + 1 ∧ β ^ t * Vv β t ω ≤ 2 * Psi β t ω ∧
      β ^ t * Vv β t ω ≤ 2 := by
  obtain ⟨hV, hP0, hP1, hA, hB⟩ := path_invariants hβ0 hβ1 ω t
  have hx := (params hβ0 hβ1).2.2.2.2.2.2.2.1
  have hav := av_bounds hβ1 t ω
  by_cases hS : Sw t ω = 0
  · obtain ⟨-, hB2⟩ := hB hS
    have e : Psi β t ω = Phi β t ω := by simp [Psi, hS]
    rw [e]
    have : 0 ≤ xL β ^ (t + 1) := pow_nonneg (by linarith) _
    refine ⟨hP0, by linarith, by nlinarith, by nlinarith⟩
  · obtain ⟨-, hA2, hA3⟩ := hA hS
    have e : Psi β t ω = xL β ^ Sw t ω := by simp [Psi, hS, hA3]
    rw [e]
    have h1 : 1 ≤ xL β ^ Sw t ω := one_le_pow₀ hx
    refine ⟨by linarith, ?_, by linarith, by linarith⟩
    have := pow_le_pow_right₀ hx (Sw_le t ω)
    linarith

/-! ### The interest-rate target (9.12) -/

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the genuine probability space — `Ω = ℕ → ℝ`
with i.i.d. biased coins, `P(up) = p = (4 − 2β)/(8 − 3β)`, and the natural filtration. -/
noncomputable abbrev Sys {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : MeasExpectationSystem (ℕ → ℝ) :=
  iidSystem (biasCoin (pr β) (params hβ0 hβ1).2.2.2.2.1.le (params hβ0 hβ1).2.2.2.2.2.1.le)

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): `M_{t+1}` after an up coin. -/
noncomputable def Mup (β : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ :=
  cc β * (1 - kq β ^ (if Sw t ω = 0 then 0 else Sw t ω + 1))

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): `M_{t+1}` after a down coin. -/
noncomputable def Mdn (β : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ :=
  cc β * (1 - kq β ^ (if Sw t ω = 0 then 0 else Sw t ω - 1))

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): `M_{t+1}` is `Mup` or `Mdn` with the coin. -/
theorem Mv_succ (β : ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    Mv β (t + 1) ω = if 0 < ω (t + 1) then Mup β t ω else Mdn β t ω := by
  simp only [Mv, Mup, Mdn, Sw]
  split_ifs <;> rfl

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): **`M` is a martingale under the target's
risk-adjusted measure**, `p M⁺/κ + (1 − p) M⁻ = M (p/κ + 1 − p)` (multiplied by `κ`). -/
theorem qmart {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (t : ℕ) (ω : ℕ → ℝ) :
    pr β * Mup β t ω + (1 - pr β) * kap β * Mdn β t ω =
      Mv β t ω * (pr β + (1 - pr β) * kap β) := by
  have h := (params hβ0 hβ1).2.2.2.2.2.2.1
  simp only [Mup, Mdn, Mv]
  rcases Nat.eq_zero_or_pos (Sw t ω) with hS | hS
  · simp [hS]
  · obtain ⟨k, hk⟩ : ∃ k, Sw t ω = k + 1 := ⟨Sw t ω - 1, by omega⟩
    rw [hk]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    rw [show k + 1 + 1 = k + 2 by ring, pow_add, pow_add, pow_one]
    linear_combination (cc β * kq β ^ k * (1 - kq β)) * h

/-- Cochrane (2023), eq. (9.12), p. 267 (counterexample): **the interest-rate target holds**,
`E_t(P_t/P_{t+1}) = E_t(P*_t/P*_{t+1})` a.e. -/
theorem rate {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (t : ℕ) :
    (Sys hβ0 hβ1).E t (Pv β t / Pv β (t + 1)) =ᵐ[(Sys hβ0 hβ1).μ]
      (Sys hβ0 hβ1).E t (tgt β t / tgt β (t + 1)) := by
  obtain ⟨hk0, hk1, hkq0, hkq1, -, -, -, -, -, -, -, -, -, -, hc⟩ := params hβ0 hβ1
  set ν := biasCoin (pr β) (params hβ0 hβ1).2.2.2.2.1.le (params hβ0 hβ1).2.2.2.2.2.1.le
  set y : ℝ := (β ^ (t + 1))⁻¹ with hy
  have hy0 : 0 < y := inv_pos.2 (pow_pos hβ0 _)
  have h1β : 0 < 1 - β := by linarith
  -- the branch values
  set fp : (ℕ → ℝ) → ℝ := fun ω => tgt β t ω / Bv β t ω * (av β (t + 1) ω + y * Mup β t ω) /
    (kap β * (av β (t + 1) ω - β)) with hfp
  set fm : (ℕ → ℝ) → ℝ := fun ω => tgt β t ω / Bv β t ω * (av β (t + 1) ω + y * Mdn β t ω) /
    (av β (t + 1) ω - β) with hfm
  set gp : (ℕ → ℝ) → ℝ := fun ω => tgt β t ω / (kap β * (av β (t + 1) ω - β)) with hgp
  set gm : (ℕ → ℝ) → ℝ := fun ω => tgt β t ω / (av β (t + 1) ω - β) with hgm
  have hD : ∀ ω, 1 - β ≤ av β (t + 1) ω - β := fun ω => by
    linarith [(av_bounds hβ1 (t + 1) ω).1]
  have hBv : ∀ ω, 1 ≤ Bv β t ω := fun ω => by
    have := (Mv_bounds hβ0 hβ1 t ω).2.2.1
    simp only [Bv]
    nlinarith [(av_bounds hβ1 (t + 1) ω).1]
  -- pointwise branch identities
  have eL : Pv β t / Pv β (t + 1) = fun ω => if 0 < ω (t + 1) then fp ω else fm ω := by
    funext ω
    have hV := (path_invariants hβ0 hβ1 ω t).1
    have hA := (At_bounds hβ0 hβ1 t ω).2.2
    have hA' := (At_bounds hβ0 hβ1 (t + 1) ω).2.2
    have hT := tgt_pos hβ0 hβ1 t ω
    have hT' := tgt_pos hβ0 hβ1 (t + 1) ω
    have hB := hBv ω
    have e1 : Pv β t ω / Pv β (t + 1) ω =
        tgt β t ω / Bv β t ω * At β (t + 1) ω / tgt β (t + 1) ω := by
      change Vv β t ω * tgt β t ω / At β t ω /
        (Vv β t ω * Bv β t ω / At β t ω * tgt β (t + 1) ω / At β (t + 1) ω) = _
      field_simp
    rw [Pi.div_apply, e1]
    have eA : At β (t + 1) ω = av β (t + 1) ω + y * Mv β (t + 1) ω := rfl
    rw [eA, Mv_succ, tgt_eq β (t + 1) ω]
    simp only [hfp, hfm]
    split_ifs <;> ring
  have eR : tgt β t / tgt β (t + 1) = fun ω => if 0 < ω (t + 1) then gp ω else gm ω := by
    funext ω
    rw [Pi.div_apply, tgt_eq β (t + 1) ω]
    simp only [hgp, hgm]
    split_ifs <;> rfl
  -- bounds and measurability of the branch values
  have hpow : ∀ n : ℕ, 0 ≤ kq β ^ n ∧ kq β ^ n ≤ 1 := fun n =>
    ⟨pow_nonneg hkq0.le n, pow_le_one₀ hkq0.le hkq1.le⟩
  have hMup : ∀ ω, 0 ≤ Mup β t ω ∧ Mup β t ω ≤ cc β := fun ω => by
    have := hpow (if Sw t ω = 0 then 0 else Sw t ω + 1)
    simp only [Mup]
    constructor <;> nlinarith
  have hMdn : ∀ ω, 0 ≤ Mdn β t ω ∧ Mdn β t ω ≤ cc β := fun ω => by
    have := hpow (if Sw t ω = 0 then 0 else Sw t ω - 1)
    simp only [Mdn]
    constructor <;> nlinarith
  set C : ℝ := 2 * (2 + y * cc β) / (kap β * (1 - β)) with hC
  have hκ1β : 0 < kap β * (1 - β) := mul_pos hk0 h1β
  have hC1 : 2 * (2 + y * cc β) / (1 - β) ≤ C :=
    div_le_div_of_nonneg_left (by positivity) hκ1β (by nlinarith)
  have hC2 : 2 / (kap β * (1 - β)) ≤ C :=
    div_le_div_of_nonneg_right (by nlinarith [mul_pos hy0 hc]) hκ1β.le
  have hC3 : 2 / (1 - β) ≤ C := (div_le_div_of_nonneg_left (by norm_num) hκ1β
    (by nlinarith)).trans hC2
  have hTB : ∀ ω, 0 ≤ tgt β t ω / Bv β t ω ∧ tgt β t ω / Bv β t ω ≤ 2 := fun ω => by
    have hT := tgt_bounds hβ0 hβ1 t ω
    have hT0 := tgt_pos hβ0 hβ1 t ω
    have hB := hBv ω
    exact ⟨div_nonneg hT0.le (by linarith), by rw [div_le_iff₀ (by linarith)]; nlinarith⟩
  have hfpC : ∀ ω, |fp ω| ≤ C := fun ω => by
    have hav := av_bounds hβ1 (t + 1) ω
    have hN0 : 0 ≤ av β (t + 1) ω + y * Mup β t ω := by nlinarith [(hMup ω).1]
    have hN : av β (t + 1) ω + y * Mup β t ω ≤ 2 + y * cc β := by
      nlinarith [(hMup ω).2, mul_le_mul_of_nonneg_left (hMup ω).2 hy0.le]
    have hden : kap β * (1 - β) ≤ kap β * (av β (t + 1) ω - β) :=
      mul_le_mul_of_nonneg_left (hD ω) hk0.le
    have hpos : 0 ≤ fp ω := div_nonneg (mul_nonneg (hTB ω).1 hN0) (hκ1β.le.trans hden)
    rw [abs_of_nonneg hpos]
    exact div_le_div₀ (by positivity) (mul_le_mul (hTB ω).2 hN hN0 (by norm_num)) hκ1β hden
  have hfmC : ∀ ω, |fm ω| ≤ C := fun ω => by
    have hav := av_bounds hβ1 (t + 1) ω
    have hN0 : 0 ≤ av β (t + 1) ω + y * Mdn β t ω := by nlinarith [(hMdn ω).1]
    have hN : av β (t + 1) ω + y * Mdn β t ω ≤ 2 + y * cc β := by
      nlinarith [(hMdn ω).2, mul_le_mul_of_nonneg_left (hMdn ω).2 hy0.le]
    have hpos : 0 ≤ fm ω := div_nonneg (mul_nonneg (hTB ω).1 hN0) (h1β.le.trans (hD ω))
    rw [abs_of_nonneg hpos]
    exact (div_le_div₀ (by positivity) (mul_le_mul (hTB ω).2 hN hN0 (by norm_num)) h1β
      (hD ω)).trans hC1
  have hgpC : ∀ ω, |gp ω| ≤ C := fun ω => by
    have hT := tgt_bounds hβ0 hβ1 t ω
    have hT0 := tgt_pos hβ0 hβ1 t ω
    have hden : kap β * (1 - β) ≤ kap β * (av β (t + 1) ω - β) :=
      mul_le_mul_of_nonneg_left (hD ω) hk0.le
    rw [abs_of_nonneg (div_nonneg hT0.le (hκ1β.le.trans hden))]
    exact (div_le_div₀ (by norm_num) hT.2 hκ1β hden).trans hC2
  have hgmC : ∀ ω, |gm ω| ≤ C := fun ω => by
    have hT := tgt_bounds hβ0 hβ1 t ω
    have hT0 := tgt_pos hβ0 hβ1 t ω
    rw [abs_of_nonneg (div_nonneg hT0.le (h1β.le.trans (hD ω)))]
    exact (div_le_div₀ (by norm_num) hT.2 h1β (hD ω)).trans hC3
  have hT := tgt_meas ν β t
  obtain ⟨-, -, hBm⟩ := MAB_meas ν β t
  have ha1 := av_pred ν β t
  have hMupm : Measurable[(iidSystem ν).𝓕 t] (Mup β t) :=
    Sw_fun_meas ν t (fun n => cc β * (1 - kq β ^ (if n = 0 then 0 else n + 1)))
  have hMdnm : Measurable[(iidSystem ν).𝓕 t] (Mdn β t) :=
    Sw_fun_meas ν t (fun n => cc β * (1 - kq β ^ (if n = 0 then 0 else n - 1)))
  have hfpm : StronglyMeasurable[(iidSystem ν).𝓕 t] fp :=
    (((hT.div hBm).mul (ha1.add (hMupm.const_mul y))).div
      ((ha1.sub_const β).const_mul (kap β))).stronglyMeasurable
  have hfmm : StronglyMeasurable[(iidSystem ν).𝓕 t] fm :=
    (((hT.div hBm).mul (ha1.add (hMdnm.const_mul y))).div (ha1.sub_const β)).stronglyMeasurable
  have hgpm : StronglyMeasurable[(iidSystem ν).𝓕 t] gp :=
    (hT.div ((ha1.sub_const β).const_mul (kap β))).stronglyMeasurable
  have hgmm : StronglyMeasurable[(iidSystem ν).𝓕 t] gm :=
    (hT.div (ha1.sub_const β)).stronglyMeasurable
  rw [eL, eR]
  filter_upwards [E_branch _ _ hfpm hfmm hfpC hfmC, E_branch _ _ hgpm hgmm hgpC hgmC]
    with ω e1 e2
  rw [e1, e2]
  -- the algebra: the risk-adjusted martingale property of `M`
  have hq := qmart hβ0 hβ1 t ω
  have hB := hBv ω
  have hDω := hD ω
  have hDp : 0 < av β (t + 1) ω - β := by linarith
  have eB : Bv β t ω = av β (t + 1) ω + y * Mv β t ω := rfl
  have hbr : pr β * (av β (t + 1) ω + y * Mup β t ω) +
      (1 - pr β) * kap β * (av β (t + 1) ω + y * Mdn β t ω) =
      Bv β t ω * (pr β + (1 - pr β) * kap β) := by
    rw [eB]
    linear_combination y * hq
  have hκ := hk0.ne'
  have hBne : Bv β t ω ≠ 0 := by linarith
  have hDne := hDp.ne'
  calc pr β * fp ω + (1 - pr β) * fm ω
      = tgt β t ω / (Bv β t ω * kap β * (av β (t + 1) ω - β)) *
        (pr β * (av β (t + 1) ω + y * Mup β t ω) +
          (1 - pr β) * kap β * (av β (t + 1) ω + y * Mdn β t ω)) := by
        simp only [hfp, hfm]
        field_simp
    _ = tgt β t ω / (Bv β t ω * kap β * (av β (t + 1) ω - β)) *
        (Bv β t ω * (pr β + (1 - pr β) * kap β)) := by rw [hbr]
    _ = pr β * gp ω + (1 - pr β) * gm ω := by
        simp only [hgp, hgm]
        field_simp

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): a biased coin with `0 < p < 1` has atoms of
mass at most `max(p, 1 − p) < 1`. -/
theorem biasCoin_singleton_le {p : ℝ} (h0 : 0 < p) (h1 : p < 1) (x : ℝ) :
    (biasCoin p h0.le h1.le : Measure ℝ) {x} ≤ max (ENNReal.ofReal p) (ENNReal.ofReal (1 - p)) := by
  change biasMeasure p {x} ≤ _
  simp only [biasMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurableSet_singleton x), Set.indicator, Set.mem_singleton_iff]
  rcases eq_or_ne x 1 with rfl | h1'
  · have : ¬ ((-1 : ℝ) = 1) := by norm_num
    simp [this]
  · rcases eq_or_ne x (-1) with rfl | h2'
    · have : ¬ ((1 : ℝ) = -1) := by norm_num
      simp [this]
    · simp [h1'.symm, h2'.symm]

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): **the probability space is genuine** — every
single history has probability zero (so no finite tree carries the probability). -/
theorem sys_singleton {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ω : ℕ → ℝ) :
    (Sys hβ0 hβ1).μ {ω} = 0 := by
  obtain ⟨-, -, -, -, hp0, hp1, -⟩ := params hβ0 hβ1
  set q := max (ENNReal.ofReal (pr β)) (ENNReal.ofReal (1 - pr β)) with hqdef
  have hq : q < 1 := max_lt (ENNReal.ofReal_lt_one.2 hp1) (ENNReal.ofReal_lt_one.2 (by linarith))
  have hle : ∀ x, ((biasCoin (pr β) (params hβ0 hβ1).2.2.2.2.1.le
      (params hβ0 hβ1).2.2.2.2.2.1.le : ProbabilityMeasure ℝ) : Measure ℝ) {x} ≤ q :=
    biasCoin_singleton_le hp0 hp1
  have hb : ∀ n, (Sys hβ0 hβ1).μ {ω} ≤ q ^ n := by
    intro n
    calc (Sys hβ0 hβ1).μ {ω}
        ≤ Measure.infinitePi (fun _ => ((biasCoin (pr β) (params hβ0 hβ1).2.2.2.2.1.le
            (params hβ0 hβ1).2.2.2.2.2.1.le : ProbabilityMeasure ℝ) : Measure ℝ))
            (Set.pi ↑(Finset.range n) fun i => {ω i}) :=
          measure_mono fun ω' h i _ => by rw [Set.mem_singleton_iff.mp h]; rfl
      _ = ∏ i ∈ Finset.range n, ((biasCoin (pr β) (params hβ0 hβ1).2.2.2.2.1.le
            (params hβ0 hβ1).2.2.2.2.2.1.le : ProbabilityMeasure ℝ) : Measure ℝ) {ω i} :=
          Measure.infinitePi_pi _ fun i _ => measurableSet_singleton _
      _ ≤ q ^ n := by
          simpa using Finset.prod_le_pow_card (Finset.range n) _ q fun i _ => hle (ω i)
  exact le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq) hb)
    bot_le

/-! ### Integrability -/

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): every process is integrable at every date
(bounded by a date-dependent constant). -/
theorem integrable_all {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (θ bbar : ℝ) (n : ℕ) :
    Integrable (Vv β n) (Sys hβ0 hβ1).μ ∧ Integrable (Pv β n) (Sys hβ0 hβ1).μ ∧
      Integrable (tgt β n) (Sys hβ0 hβ1).μ ∧ Integrable (av β n) (Sys hβ0 hβ1).μ ∧
      Integrable (Psi β n) (Sys hβ0 hβ1).μ ∧ Integrable (bv β θ bbar n) (Sys hβ0 hβ1).μ ∧
      Integrable (fun ω => 1 / Pv β n ω) (Sys hβ0 hβ1).μ := by
  set ν := biasCoin (pr β) (params hβ0 hβ1).2.2.2.2.1.le (params hβ0 hβ1).2.2.2.2.2.1.le
  have hle := (iidSystem ν).𝓕.le n
  have hβn : 0 < β ^ n := pow_pos hβ0 n
  have hVb : ∀ ω, |Vv β n ω| ≤ 2 * (β ^ n)⁻¹ := fun ω => by
    have h1 := (path_invariants hβ0 hβ1 ω n).1
    have h2 := (Psi_bounds hβ0 hβ1 n ω).2.2.2
    rw [abs_of_pos h1, le_mul_inv_iff₀ hβn]
    linarith
  have hVi : Integrable (Vv β n) (Sys hβ0 hβ1).μ :=
    Integrable.of_bound ((Vv_meas ν β n).mono hle le_rfl).aestronglyMeasurable (2 * (β ^ n)⁻¹)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hVb ω)
  have hai : Integrable (av β n) (Sys hβ0 hβ1).μ :=
    Integrable.of_bound ((av_meas ν β n).mono hle le_rfl).aestronglyMeasurable 2
      (Eventually.of_forall fun ω => by
        have := av_bounds hβ1 n ω
        rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith)
  refine ⟨hVi, ?_, ?_, hai, ?_, ?_, ?_⟩
  · exact Integrable.of_bound ((Pv_meas ν β n).mono hle le_rfl).aestronglyMeasurable
      (2 * (β ^ n)⁻¹) (Eventually.of_forall fun ω => by
        have h1 := Pv_bounds hβ0 hβ1 n ω
        have h2 := mP_pos hβ0 hβ1
        rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
        exact h1.2.trans ((le_abs_self _).trans (hVb ω)))
  · exact Integrable.of_bound ((tgt_meas ν β n).mono hle le_rfl).aestronglyMeasurable 2
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (tgt_pos hβ0 hβ1 n ω)]
        exact (tgt_bounds hβ0 hβ1 n ω).2)
  · exact Integrable.of_bound ((Psi_meas ν β n).mono hle le_rfl).aestronglyMeasurable
      (xL β ^ (n + 1) + 1) (Eventually.of_forall fun ω => by
        have := Psi_bounds hβ0 hβ1 n ω
        rw [Real.norm_eq_abs, abs_of_nonneg this.1]
        exact this.2.1)
  · exact (integrable_const bbar).add ((hVi.sub hai).const_mul θ)
  · exact Integrable.of_bound
      ((((Pv_meas ν β n).const_div 1).mono hle le_rfl).aestronglyMeasurable)
      (1 / mP β) (Eventually.of_forall fun ω => by
        have h1 := Pv_bounds hβ0 hβ1 n ω
        have h2 := mP_pos hβ0 hβ1
        rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (by linarith))]
        exact one_div_le_one_div_of_le h2 h1.1)

/-! ### The Lyapunov bound and the transversality condition -/

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): **`Ψ` contracts in expectation**,
`E_t Ψ_{t+1} ≤ λ Ψ_t` a.e. — under the true coin the sunspot state drifts down and is absorbed. -/
theorem psi_step {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (t : ℕ) :
    (Sys hβ0 hβ1).E t (Psi β (t + 1)) ≤ᵐ[(Sys hβ0 hβ1).μ] fun ω => lam β * Psi β t ω := by
  obtain ⟨-, -, -, -, hp0, hp1, -, hx, -, -, -, hβl, hxl, -, -⟩ := params hβ0 hβ1
  set ν := biasCoin (pr β) (params hβ0 hβ1).2.2.2.2.1.le (params hβ0 hβ1).2.2.2.2.2.1.le
  set qp : (ℕ → ℝ) → ℝ := fun ω => if Sw t ω = 0 then β * Phi β t ω else xL β ^ (Sw t ω + 1)
    with hqp
  set qm : (ℕ → ℝ) → ℝ := fun ω => if Sw t ω = 0 then β * Phi β t ω else xL β ^ (Sw t ω - 1)
    with hqm
  have e : Psi β (t + 1) = fun ω => if 0 < ω (t + 1) then qp ω else qm ω := by
    funext ω
    have hinv := path_invariants hβ0 hβ1 ω t
    by_cases hS : Sw t ω = 0
    · have hS' := Sw_succ_zero hS
      have hPhi : Phi β (t + 1) ω = β * Phi β t ω := by simp [Phi, hS]
      simp only [Psi, hS', hPhi, hqp, hqm, hS, ↓reduceIte, zero_add]
      split_ifs <;> rfl
    · by_cases hu : 0 < ω (t + 1)
      · have hS' : Sw (t + 1) ω = Sw t ω + 1 := by simp [Sw, hS, hu]
        have hPhi : Phi β (t + 1) ω = 0 := by simp [Phi, hS, hS']
        simp [Psi, hS', hPhi, hqp, hS, hu]
      · have hS' : Sw (t + 1) ω = Sw t ω - 1 := by simp [Sw, hS, hu]
        by_cases h1 : Sw t ω - 1 = 0
        · have hPhi : Phi β (t + 1) ω = 1 := by simp [Phi, hS, hS', h1]
          simp [Psi, hS', hPhi, hqm, hS, hu, h1]
        · have hPhi : Phi β (t + 1) ω = 0 := by simp [Phi, hS, hS', h1]
          simp [Psi, hS', hPhi, hqm, hS, hu, h1]
  have hxb : ∀ n, n ≤ t + 2 → 0 ≤ xL β ^ n ∧ xL β ^ n ≤ xL β ^ (t + 2) := fun n hn =>
    ⟨pow_nonneg (by linarith) n, pow_le_pow_right₀ hx hn⟩
  have hqpC : ∀ ω, |qp ω| ≤ xL β ^ (t + 2) + 1 := fun ω => by
    have hP := path_invariants hβ0 hβ1 ω t
    have hSl := Sw_le t ω
    have := hxb (Sw t ω + 1) (by omega)
    simp only [hqp]
    split_ifs
    · rw [abs_of_nonneg (mul_nonneg hβ0.le hP.2.1)]
      nlinarith [hP.2.2.1]
    · rw [abs_of_nonneg this.1]
      linarith
  have hqmC : ∀ ω, |qm ω| ≤ xL β ^ (t + 2) + 1 := fun ω => by
    have hP := path_invariants hβ0 hβ1 ω t
    have hSl := Sw_le t ω
    have := hxb (Sw t ω - 1) (by omega)
    simp only [hqm]
    split_ifs
    · rw [abs_of_nonneg (mul_nonneg hβ0.le hP.2.1)]
      nlinarith [hP.2.2.1]
    · rw [abs_of_nonneg this.1]
      linarith
  have hSm := Sw_meas ν t
  have hset : MeasurableSet[(iidSystem ν).𝓕 t] {ω | Sw t ω = 0} := hSm (measurableSet_singleton 0)
  have hPhm := Phi_meas ν β t
  have hqpm : StronglyMeasurable[(iidSystem ν).𝓕 t] qp :=
    (Measurable.ite hset (hPhm.const_mul β)
      (Sw_fun_meas ν t fun n => xL β ^ (n + 1))).stronglyMeasurable
  have hqmm : StronglyMeasurable[(iidSystem ν).𝓕 t] qm :=
    (Measurable.ite hset (hPhm.const_mul β)
      (Sw_fun_meas ν t fun n => xL β ^ (n - 1))).stronglyMeasurable
  rw [e]
  filter_upwards [E_branch _ _ hqpm hqmm hqpC hqmC] with ω h
  rw [h]
  have hinv := path_invariants hβ0 hβ1 ω t
  by_cases hS : Sw t ω = 0
  · have hPs : Psi β t ω = Phi β t ω := by simp [Psi, hS]
    simp only [hqp, hqm, hS, ↓reduceIte, hPs]
    nlinarith [hinv.2.1]
  · have hP0 := (hinv.2.2.2.1 hS).2.2
    have hPs : Psi β t ω = xL β ^ Sw t ω := by simp [Psi, hS, hP0]
    simp only [hqp, hqm, hS, ↓reduceIte, hPs]
    obtain ⟨k, hk⟩ : ∃ k, Sw t ω = k + 1 := ⟨Sw t ω - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel]
    have hx0 : 0 < xL β := by linarith
    have e2 : pr β * xL β ^ (k + 1 + 1) + (1 - pr β) * xL β ^ k =
        xL β ^ (k + 1) * (pr β * xL β + (1 - pr β) / xL β) := by
      field_simp
      ring
    rw [e2, mul_comm (lam β)]
    exact mul_le_mul_of_nonneg_left hxl (pow_nonneg hx0.le _)

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): iterating, `E_t Ψ_{t+k} ≤ λᵏ Ψ_t` a.e. -/
theorem psi_iter {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (t k : ℕ) :
    (Sys hβ0 hβ1).E t (Psi β (t + k)) ≤ᵐ[(Sys hβ0 hβ1).μ] fun ω => lam β ^ k * Psi β t ω := by
  set ν := biasCoin (pr β) (params hβ0 hβ1).2.2.2.2.1.le (params hβ0 hβ1).2.2.2.2.2.1.le
  have hl0 : 0 ≤ lam β := hβ0.le.trans (params hβ0 hβ1).2.2.2.2.2.2.2.2.2.2.2.1
  have hPi : ∀ n, Integrable (Psi β n) (Sys hβ0 hβ1).μ := fun n =>
    (integrable_all hβ0 hβ1 0 0 n).2.2.2.2.1
  induction k with
  | zero =>
    rw [add_zero, (Sys hβ0 hβ1).E_of_stronglyMeasurable (Psi_meas ν β t).stronglyMeasurable
      (hPi t)]
    exact Eventually.of_forall fun ω => by simp
  | succ k ih =>
    have h1 := (Sys hβ0 hβ1).E_tower (Nat.le_add_right t k) (Psi β (t + k + 1))
    have h2 := (Sys hβ0 hβ1).E_mono ((Sys hβ0 hβ1).integrable_E _ _)
      ((hPi (t + k)).const_mul (lam β)) (psi_step hβ0 hβ1 (t + k)) t
    have h3 := (Sys hβ0 hβ1).E_smul (lam β) (Psi β (t + k)) t
    filter_upwards [h1, h2, h3, ih] with ω e1 e2 e3 e4
    change (Sys hβ0 hβ1).E t (Psi β (t + k + 1)) ω ≤ _
    rw [← e1]
    refine e2.trans ?_
    change (Sys hβ0 hβ1).E t (lam β • Psi β (t + k)) ω ≤ _
    rw [e3, Pi.smul_apply, smul_eq_mul, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left e4 hl0]

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the forecast value of the price path decays,
`0 ≤ E_t P_{t+T} ≤ E_t V_{t+T}` and `β^T E_t V_{t+T} ≤ 2 β^{−t} Ψ_t λ^T` a.e. -/
theorem EV_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (t T : ℕ) :
    ∀ᵐ ω ∂(Sys hβ0 hβ1).μ, 0 ≤ (Sys hβ0 hβ1).E t (Pv β (t + T)) ω ∧
      (Sys hβ0 hβ1).E t (Pv β (t + T)) ω ≤ (Sys hβ0 hβ1).E t (Vv β (t + T)) ω ∧
      β ^ T * (Sys hβ0 hβ1).E t (Vv β (t + T)) ω ≤ 2 * (β ^ t)⁻¹ * Psi β t ω * lam β ^ T := by
  set S := Sys hβ0 hβ1
  obtain ⟨hVi, hPi, -, -, hPsi, -, -⟩ := integrable_all hβ0 hβ1 0 0 (t + T)
  have hβn : 0 < β ^ (t + T) := pow_pos hβ0 _
  have h0 : S.E t (fun _ => (0 : ℝ)) ≤ᵐ[S.μ] S.E t (Pv β (t + T)) :=
    S.E_mono (integrable_const 0) hPi (Eventually.of_forall fun ω => by
      have := Pv_bounds hβ0 hβ1 (t + T) ω
      have := mP_pos hβ0 hβ1
      change (0 : ℝ) ≤ Pv β (t + T) ω
      linarith) t
  rw [S.E_const] at h0
  have h1 : S.E t (Pv β (t + T)) ≤ᵐ[S.μ] S.E t (Vv β (t + T)) :=
    S.E_mono hPi hVi (Eventually.of_forall fun ω => (Pv_bounds hβ0 hβ1 (t + T) ω).2) t
  have h2 : S.E t (Vv β (t + T)) ≤ᵐ[S.μ] S.E t ((2 * (β ^ (t + T))⁻¹) • Psi β (t + T)) :=
    S.E_mono hVi (hPsi.smul _) (Eventually.of_forall fun ω => by
      have := (Psi_bounds hβ0 hβ1 (t + T) ω).2.2.1
      change Vv β (t + T) ω ≤ 2 * (β ^ (t + T))⁻¹ * Psi β (t + T) ω
      rw [mul_comm 2, mul_assoc, le_inv_mul_iff₀ hβn]
      linarith) t
  have h3 := S.E_smul (2 * (β ^ (t + T))⁻¹) (Psi β (t + T)) t
  filter_upwards [h0, h1, h2, h3, psi_iter hβ0 hβ1 t T] with ω e0 e1 e2 e3 e4
  refine ⟨e0, e1, ?_⟩
  rw [e3, Pi.smul_apply, smul_eq_mul] at e2
  have hβT : 0 < β ^ T := pow_pos hβ0 T
  have hc : 0 ≤ 2 * (β ^ (t + T))⁻¹ := by positivity
  calc β ^ T * S.E t (Vv β (t + T)) ω
      ≤ β ^ T * (2 * (β ^ (t + T))⁻¹ * (lam β ^ T * Psi β t ω)) :=
        mul_le_mul_of_nonneg_left (e2.trans (mul_le_mul_of_nonneg_left e4 hc)) hβT.le
    _ = 2 * (β ^ t)⁻¹ * Psi β t ω * lam β ^ T := by
        rw [pow_add]
        field_simp

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): **the transversality condition holds**,
`β^T E_t b_{t+T} → 0` a.e. -/
theorem tvc {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (θ bbar : ℝ) (t : ℕ) :
    ∀ᵐ ω ∂(Sys hβ0 hβ1).μ,
      Tendsto (fun T => β ^ T * (Sys hβ0 hβ1).E t (bv β θ bbar (t + T)) ω) atTop (𝓝 0) := by
  set S := Sys hβ0 hβ1
  have hl := params hβ0 hβ1
  have hl0 : 0 ≤ lam β := hβ0.le.trans hl.2.2.2.2.2.2.2.2.2.2.2.1
  have hl1 : lam β < 1 := hl.2.2.2.2.2.2.2.2.2.2.1
  have hlin : ∀ T, S.E t (bv β θ bbar (t + T)) =ᵐ[S.μ] fun ω =>
      bbar + θ * (S.E t (Vv β (t + T)) ω - S.E t (av β (t + T)) ω) := fun T => by
    obtain ⟨hVi, -, -, hai, -, -, -⟩ := integrable_all hβ0 hβ1 θ bbar (t + T)
    have e : bv β θ bbar (t + T) = (fun _ => bbar) + θ • (Vv β (t + T) - av β (t + T)) := by
      funext ω
      simp [bv]
    rw [e]
    filter_upwards [S.E_add (integrable_const bbar) ((hVi.sub hai).smul θ) t,
      S.E_smul θ (Vv β (t + T) - av β (t + T)) t, S.E_sub hVi hai t] with ω e1 e2 e3
    rw [e1, Pi.add_apply, e2, Pi.smul_apply, e3, S.E_const, Pi.sub_apply, smul_eq_mul]
  have ha : ∀ T, ∀ᵐ ω ∂S.μ, |S.E t (av β (t + T)) ω| ≤ 2 := fun T =>
    S.abs_E_le (Eventually.of_forall fun ω => by
      have := av_bounds hβ1 (t + T) ω
      rw [abs_of_pos (by linarith)]
      linarith) t
  filter_upwards [ae_all_iff.2 hlin, ae_all_iff.2 ha, ae_all_iff.2 (EV_bound hβ0 hβ1 t)]
    with ω e1 e2 e3
  have hg := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1
  have hV : Tendsto (fun T => β ^ T * S.E t (Vv β (t + T)) ω) atTop (𝓝 0) := by
    refine squeeze_zero (fun T => mul_nonneg (pow_pos hβ0 T).le ((e3 T).1.trans (e3 T).2.1))
      (fun T => (e3 T).2.2) ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hl0 hl1).const_mul
      (2 * (β ^ t)⁻¹ * Psi β t ω)
  have hA : Tendsto (fun T => β ^ T * S.E t (av β (t + T)) ω) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun T => ?_) (by simpa using hg.mul_const 2)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 T)]
    exact mul_le_mul_of_nonneg_left (e2 T) (pow_pos hβ0 T).le
  have := ((hg.mul_const bbar).add ((hV.sub hA).const_mul θ))
  simp only [zero_mul, sub_zero, mul_zero, zero_add] at this
  refine this.congr fun T => ?_
  rw [e1 T]
  ring

/-- Cochrane (2023), eq. (9.9), p. 266 (counterexample): **the valuation equation holds**,
`∑ⱼ βʲ E_t s_{t+j} = b_t` a.e. as a genuine `HasSum`, with `s_t = (1 − β) b̄ + θ (P_t − P*_t)`. -/
theorem valuation {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (θ bbar : ℝ) (t : ℕ) :
    ∀ᵐ ω ∂(Sys hβ0 hβ1).μ, HasSum (fun j => β ^ j * (Sys hβ0 hβ1).E t
      (fun ω' => (1 - β) * bbar + θ * (Pv β (t + j) ω' - tgt β (t + j) ω')) ω)
      (bv β θ bbar t ω) := by
  set S := Sys hβ0 hβ1
  set ν := biasCoin (pr β) (params hβ0 hβ1).2.2.2.2.1.le (params hβ0 hβ1).2.2.2.2.2.1.le
  have hl := params hβ0 hβ1
  have hl0 : 0 ≤ lam β := hβ0.le.trans hl.2.2.2.2.2.2.2.2.2.2.2.1
  have hl1 : lam β < 1 := hl.2.2.2.2.2.2.2.2.2.2.1
  set s : ℕ → (ℕ → ℝ) → ℝ := fun n ω => (1 - β) * bbar + θ * (Pv β n ω - tgt β n ω) with hs
  have hsi : ∀ n, Integrable (s n) S.μ := fun n => by
    obtain ⟨-, hPi, hTi, -⟩ := integrable_all hβ0 hβ1 θ bbar n
    exact (integrable_const _).add ((hPi.sub hTi).const_mul θ)
  have hbm : ∀ n, StronglyMeasurable[S.𝓕 n] (bv β θ bbar n) := fun n =>
    (measurable_const.add (((Vv_meas ν β n).sub (av_meas ν β n)).const_mul θ)).stronglyMeasurable
  have hbi : ∀ n, Integrable (bv β θ bbar n) S.μ := fun n =>
    (integrable_all hβ0 hβ1 θ bbar n).2.2.2.2.2.1
  have hpart := value_partial S (P := s) (V := bv β θ bbar) (bv_flow hβ0 hβ1 θ bbar) hbm hbi
    hsi t
  have hlin : ∀ j, S.E t (s (t + j)) =ᵐ[S.μ] fun ω => (1 - β) * bbar +
      θ * (S.E t (Pv β (t + j)) ω - S.E t (tgt β (t + j)) ω) := fun j => by
    obtain ⟨-, hPi, hTi, -⟩ := integrable_all hβ0 hβ1 θ bbar (t + j)
    have e : s (t + j) = (fun _ => (1 - β) * bbar) + θ • (Pv β (t + j) - tgt β (t + j)) := by
      funext ω
      simp [hs]
    rw [e]
    filter_upwards [S.E_add (integrable_const _) ((hPi.sub hTi).smul θ) t,
      S.E_smul θ (Pv β (t + j) - tgt β (t + j)) t, S.E_sub hPi hTi t] with ω e1 e2 e3
    rw [e1, Pi.add_apply, e2, Pi.smul_apply, e3, S.E_const, Pi.sub_apply, smul_eq_mul]
  have htg : ∀ j, ∀ᵐ ω ∂S.μ, |S.E t (tgt β (t + j)) ω| ≤ 2 := fun j =>
    S.abs_E_le (Eventually.of_forall fun ω => by
      rw [abs_of_pos (tgt_pos hβ0 hβ1 (t + j) ω)]
      exact (tgt_bounds hβ0 hβ1 (t + j) ω).2) t
  filter_upwards [ae_all_iff.2 hpart, tvc hβ0 hβ1 θ bbar t, ae_all_iff.2 hlin, ae_all_iff.2 htg,
    ae_all_iff.2 (EV_bound hβ0 hβ1 t)] with ω h1 h2 h3 h4 h5
  have hpartial : Tendsto (fun k => ∑ j ∈ Finset.range k, β ^ j * S.E t (s (t + j)) ω) atTop
      (𝓝 (bv β θ bbar t ω)) := by
    have := (tendsto_const_nhds (x := bv β θ bbar t ω)).sub h2
    rw [sub_zero] at this
    exact this.congr fun k => by linarith [h1 k]
  set c1 : ℝ := |(1 - β) * bbar| + 2 * |θ| with hc1
  set c2 : ℝ := |θ| * (2 * (β ^ t)⁻¹ * Psi β t ω) with hc2
  have hsum : Summable (fun j => β ^ j * S.E t (s (t + j)) ω) := by
    refine Summable.of_norm_bounded (((summable_geometric_of_lt_one hβ0.le hβ1).mul_right c1).add
      ((summable_geometric_of_lt_one hl0 hl1).mul_left c2)) fun j => ?_
    rw [Real.norm_eq_abs, h3 j, abs_mul, abs_of_pos (pow_pos hβ0 j)]
    obtain ⟨g0, g1, g2⟩ := h5 j
    have hP : |S.E t (Pv β (t + j)) ω - S.E t (tgt β (t + j)) ω| ≤
        S.E t (Pv β (t + j)) ω + 2 := by
      rw [abs_le]
      have := abs_le.1 (h4 j)
      constructor <;> linarith
    have hb : |(1 - β) * bbar + θ * (S.E t (Pv β (t + j)) ω - S.E t (tgt β (t + j)) ω)| ≤
        c1 + |θ| * S.E t (Pv β (t + j)) ω := by
      refine (abs_add_le _ _).trans ?_
      have hθm := abs_mul θ (S.E t (Pv β (t + j)) ω - S.E t (tgt β (t + j)) ω)
      rw [hθm, hc1]
      nlinarith [mul_le_mul_of_nonneg_left hP (abs_nonneg θ)]
    have hβj : 0 < β ^ j := pow_pos hβ0 j
    have hq : β ^ j * S.E t (Pv β (t + j)) ω ≤ 2 * (β ^ t)⁻¹ * Psi β t ω * lam β ^ j :=
      (mul_le_mul_of_nonneg_left g1 hβj.le).trans g2
    calc β ^ j * |(1 - β) * bbar + θ * (S.E t (Pv β (t + j)) ω - S.E t (tgt β (t + j)) ω)|
        ≤ β ^ j * (c1 + |θ| * S.E t (Pv β (t + j)) ω) := mul_le_mul_of_nonneg_left hb hβj.le
      _ = β ^ j * c1 + |θ| * (β ^ j * S.E t (Pv β (t + j)) ω) := by ring
      _ ≤ β ^ j * c1 + |θ| * (2 * (β ^ t)⁻¹ * Psi β t ω * lam β ^ j) := by
          nlinarith [mul_le_mul_of_nonneg_left hq (abs_nonneg θ)]
      _ = β ^ j * c1 + c2 * lam β ^ j := by rw [hc2]; ring
  have he := tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hpartial
  rw [← he]
  exact hsum.hasSum

/-- Cochrane (2023), §9.3.2, pp. 266–267 (counterexample): `P`, `b` form an equilibrium of the
fiscal rule with indexed debt and the interest-rate target (`RuleEqm`) on the genuine probability
space `Sys`. -/
theorem counter_ruleEqm {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (θ bbar : ℝ) :
    RuleEqm (Sys hβ0 hβ1) β θ bbar (tgt β) (Pv β) (bv β θ bbar) := by
  set ν := biasCoin (pr β) (params hβ0 hβ1).2.2.2.2.1.le (params hβ0 hβ1).2.2.2.2.2.1.le
  refine ⟨fun t ω => (mP_pos hβ0 hβ1).trans_le (Pv_bounds hβ0 hβ1 t ω).1,
    fun t => (Pv_meas ν β t).stronglyMeasurable,
    fun t => (integrable_all hβ0 hβ1 θ bbar t).2.1,
    fun t => (integrable_all hβ0 hβ1 θ bbar t).2.2.2.2.2.1, rate hβ0 hβ1,
    bv_flow hβ0 hβ1 θ bbar, fun t => ?_, valuation hβ0 hβ1 θ bbar, tvc hβ0 hβ1 θ bbar⟩
  exact (measurable_const.add
    (((Vv_pred ν β t).sub (av_pred ν β t)).const_mul θ)).stronglyMeasurable

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d), bounded-away-from-zero case: the
bounded real-rate hypothesis cannot be dropped**): for every `0 < β < 1`, `θ ≠ 0` and `b̄`, on a
genuine infinite-horizon probability space (i.i.d. biased coins; every history is null) there is a
bounded stochastic target `(2 − β)(1 − β)/2 ≤ P* ≤ 2` whose present value `a` is predetermined and
bounded (`1 ≤ a ≤ 2`, the target analogue of `a(β) = 0`), and an equilibrium of the rule
(`RuleEqm`) with initial debt `b₀ = b̄` and prices bounded away from zero (`P ≥ m_P > 0`), but
with `P₀ < P*₀` on every path. So the conclusion `P = (1 + (b₀ − b̄)/(θ a₀)) P* = P*` of
`fr_unique_stochastic_below` fails although all its other hypotheses hold: the bounded cumulative
real-rate factor `∏ E(P*/P*′)⁻¹ ≤ L` fails for every `L`. The prices are not bounded above (else
`fr_d_news` would give `P = P*`). -/
theorem fr_below_counterexample {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {θ : ℝ} (hθ : θ ≠ 0)
    (bbar : ℝ) :
    RuleEqm (Sys hβ0 hβ1) β θ bbar (tgt β) (Pv β) (bv β θ bbar) ∧
      (∀ ω, (Sys hβ0 hβ1).μ {ω} = 0) ∧ (∀ ω, bv β θ bbar 0 ω = bbar) ∧ 0 < mP β ∧
      (∀ t ω, mP β ≤ Pv β t ω) ∧
      StronglyAdapted (Sys hβ0 hβ1).𝓕 (tgt β) ∧
      (∀ t ω, (2 - β) * (1 - β) / 2 ≤ tgt β t ω ∧ tgt β t ω ≤ 2) ∧
      (∀ t ω, av β t ω = tgt β t ω + β * av β (t + 1) ω) ∧
      (∀ t, StronglyMeasurable[(Sys hβ0 hβ1).𝓕 t] (av β (t + 1))) ∧
      (∀ t ω, |av β t ω| ≤ 2) ∧ (∀ ω, Pv β 0 ω < tgt β 0 ω) ∧
      (¬ ∀ t, Pv β t =ᵐ[(Sys hβ0 hβ1).μ] tgt β t) ∧ (¬ ∃ M, ∀ t ω, Pv β t ω ≤ M) ∧
      ¬ ∃ L, ∀ t k, ∀ᵐ ω ∂(Sys hβ0 hβ1).μ, ∏ i ∈ Finset.range k,
        (tgt β (t + i) ω * (Sys hβ0 hβ1).E (t + i) (fun ω => 1 / tgt β (t + i + 1) ω) ω)⁻¹ ≤ L := by
  set ν := biasCoin (pr β) (params hβ0 hβ1).2.2.2.2.1.le (params hβ0 hβ1).2.2.2.2.2.1.le
  have hE := counter_ruleEqm hβ0 hβ1 θ bbar
  have hb0 : ∀ ω, bv β θ bbar 0 ω = bbar := fun ω => by simp [bv, Vv, av]
  have hm : 0 < (2 - β) * (1 - β) / 2 := by
    have : 0 < (2 - β) * (1 - β) := mul_pos (by linarith) (by linarith)
    linarith
  have hPsa : StronglyAdapted (Sys hβ0 hβ1).𝓕 (tgt β) := fun t =>
    (tgt_meas ν β t).stronglyMeasurable
  have hapre : ∀ t, StronglyMeasurable[(Sys hβ0 hβ1).𝓕 t] (av β (t + 1)) := fun t =>
    (av_pred ν β t).stronglyMeasurable
  have haK : ∀ t ω, |av β t ω| ≤ 2 := fun t ω => by
    have := av_bounds hβ1 t ω
    rw [abs_of_pos (by linarith)]
    linarith
  have hlow : ∀ ω, Pv β 0 ω < tgt β 0 ω := fun ω => by
    have hM := (Mv_bounds hβ0 hβ1 0 ω).2.1 (by simp [Sw])
    obtain ⟨-, -, -, hq1, -, -, -, -, -, -, -, -, -, -, hc⟩ := params hβ0 hβ1
    have hM0 : 0 < Mv β 0 ω := lt_of_lt_of_le (mul_pos hc (by linarith)) hM
    have hT := tgt_pos hβ0 hβ1 0 ω
    have e : Pv β 0 ω = tgt β 0 ω / (1 + Mv β 0 ω) := by
      simp [Pv, Vv, At, av]
    rw [e, div_lt_iff₀ (by linarith)]
    nlinarith
  have hnot : ¬ ∀ t, Pv β t =ᵐ[(Sys hβ0 hβ1).μ] tgt β t := fun h => by
    obtain ⟨ω, hω⟩ := (h 0).exists
    exact (hlow ω).ne hω
  refine ⟨hE, sys_singleton hβ0 hβ1, hb0, mP_pos hβ0 hβ1, fun t ω => (Pv_bounds hβ0 hβ1 t ω).1,
    hPsa,
    tgt_bounds hβ0 hβ1, fun t ω => by simp only [tgt]; ring, hapre, haK, hlow, hnot, ?_, ?_⟩
  · rintro ⟨M, hM⟩
    apply hnot
    intro t
    exact ((fr_d_news (Sys hβ0 hβ1) hβ0 hβ1 hθ hPsa hm (tgt_bounds hβ0 hβ1)).2 (Pv β)
      (bv β θ bbar) hE ⟨M, hM⟩ (fun n => (integrable_all hβ0 hβ1 θ bbar n).2.2.2.2.2.2)
      hb0 t).1
  · rintro ⟨L, hL⟩
    obtain ⟨-, -, hPi, hbi, hrate, hflow, hpre, -, htvc⟩ := hE
    apply hnot
    intro t
    filter_upwards [fr_unique_stochastic_below (Sys hβ0 hβ1) hβ0 hβ1 hθ (b0 := bbar)
      (Pv_meas ν β · |>.stronglyMeasurable) (mP_pos hβ0 hβ1)
      (fun t ω => (Pv_bounds hβ0 hβ1 t ω).1) hPi hPsa hm (tgt_bounds hβ0 hβ1)
      (fun t ω => by simp only [tgt]; ring) hapre haK hrate hflow hpre hb0 hbi htvc hL t]
      with ω h
    rw [h, sub_self, zero_div, add_zero, one_mul]

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d) with `b₀ = b̄`: the precise dividing
line**): (i) on every measure-theoretic system and for every adapted target `0 < m ≤ P* ≤ M*` —
whether or not its present value carries news — `P = P*` is the unique equilibrium among those with
prices bounded above (`fr_d_news`); (ii) bounded away from zero is not enough: for every `0 < β <
1` there is a genuine probability space, a target with predetermined present value, and an
equilibrium with `b₀ = b̄`, `P ≥ m_P > 0` and `P ≠ P*` (its cumulative target real-rate factor is
unbounded; with it bounded, `fr_unique_stochastic_below` restores uniqueness). -/
theorem fr_d_dividing_line {β θ bbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0) :
    (∀ {Ω : Type} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω) (m Ms : ℝ)
      (Pstar : ℕ → Ω → ℝ), StronglyAdapted S.𝓕 Pstar → 0 < m →
      (∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms) →
      ∀ P b : ℕ → Ω → ℝ, RuleEqm S β θ bbar Pstar P b → (∃ M, ∀ t ω, P t ω ≤ M) →
        (∀ t, Integrable (fun ω => 1 / P t ω) S.μ) → (∀ ω, b 0 ω = bbar) →
        ∀ t, P t =ᵐ[S.μ] Pstar t) ∧
      ∃ (S : MeasExpectationSystem (ℕ → ℝ)) (Pstar a P b : ℕ → (ℕ → ℝ) → ℝ) (m mP' : ℝ),
        RuleEqm S β θ bbar Pstar P b ∧ (∀ ω, b 0 ω = bbar) ∧ 0 < m ∧ 0 < mP' ∧
        StronglyAdapted S.𝓕 Pstar ∧ (∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ 2) ∧
        (∀ t ω, a t ω = Pstar t ω + β * a (t + 1) ω) ∧
        (∀ t, StronglyMeasurable[S.𝓕 t] (a (t + 1))) ∧ (∀ t ω, |a t ω| ≤ 2) ∧
        (∀ t ω, mP' ≤ P t ω) ∧ ¬ ∀ t, P t =ᵐ[S.μ] Pstar t := by
  refine ⟨fun S _ _ _ hPsa hm hPs P b hE hM hq hb0 t =>
    ((fr_d_news S hβ0 hβ1 hθ hPsa hm hPs).2 P b hE hM hq hb0 t).1, ?_⟩
  obtain ⟨hE, -, hb0, hmP, hlow, hPsa, hPs, ha, hapre, haK, -, hnot, -, -⟩ :=
    fr_below_counterexample hβ0 hβ1 hθ bbar
  have hm : 0 < (2 - β) * (1 - β) / 2 := by
    have : 0 < (2 - β) * (1 - β) := mul_pos (by linarith) (by linarith)
    linarith
  exact ⟨Sys hβ0 hβ1, tgt β, av β, Pv β, bv β θ bbar, _, _, hE, hb0, hm, hmP, hPsa, hPs, ha,
    hapre, haK, hlow, hnot⟩

/-- Cochrane (2023), §9.3.2, pp. 266–267 (Theorem FR (d), bounded away from zero, **link**): on a
finite fully supported system the core hypotheses of `FiscalRules.fr_unique_bounded` in its
bounded-away-from-zero form (`P* ≡ 1`, bridged core system) satisfy the bounded real-rate
hypothesis with `L = 1`, so `fr_unique_stochastic_below` gives the core conclusion `P ≡ 1`: the
hypothesis shown indispensable by `fr_below_counterexample` is automatic for the book's constant
target. -/
theorem fr_below_link [Finite Ω'] [MeasurableSpace Ω'] [DiscreteMeasurableSpace Ω']
    (S : MeasExpectationSystem Ω') (hfull : ∀ ω, S.μ {ω} ≠ 0) {β θ bbar m : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ : θ ≠ 0) {P b : ℕ → Ω' → ℝ} (hPa : (S.toExpectationSystem hfull).Adapted P)
    (h912 : ∀ t, β • (S.toExpectationSystem hfull).E t (P t / P (t + 1)) = fun _ => β)
    (hflow : ∀ t ω, b t ω = (1 - β) * bbar + θ * (P t ω - 1) + β * b (t + 1) ω)
    (hpre : ∀ t, (S.toExpectationSystem hfull).E t (b (t + 1)) = b (t + 1))
    (hb0 : ∀ ω, b 0 ω = bbar)
    (htvc : ∀ t ω, Tendsto (fun T => β ^ T * (S.toExpectationSystem hfull).E t (b (t + T)) ω)
      atTop (𝓝 0)) (hm : 0 < m) (hPm : ∀ t ω, m ≤ P t ω) :
    P = fun _ _ => 1 := by
  have h1β : 0 < 1 - β := by linarith
  have hsm : ∀ t (x : Ω' → ℝ), S.E t x = x → StronglyMeasurable[S.𝓕 t] x := fun t x h => by
    have := S.stronglyMeasurable_E t x
    rwa [h] at this
  have hrate : ∀ t, S.E t (P t / P (t + 1)) =ᵐ[S.μ]
      S.E t ((fun _ _ => (1 : ℝ)) t / (fun _ _ => (1 : ℝ)) (t + 1)) := fun t => by
    refine EventuallyEq.of_eq ?_
    have h := h912 t
    rw [S.toExpectationSystem_E] at h
    have e : ((fun _ _ => (1 : ℝ)) t / (fun _ _ => (1 : ℝ)) (t + 1) : Ω' → ℝ) = fun _ => 1 := by
      funext ω
      simp
    rw [e, S.E_const]
    funext ω
    have := congrFun h ω
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hβ0.ne' (this.trans (mul_one β).symm)
  funext t
  refine S.eq_of_ae_eq hfull ?_
  have h := fr_unique_stochastic_below S (m := 1) (Ms := 1) (K := 1 / (1 - β)) (L := 1)
    (a := fun _ _ => 1 / (1 - β)) (b0 := bbar) hβ0 hβ1 hθ (fun t => hsm t _ (hPa t)) hm hPm
    (fun _ => Integrable.of_finite) (fun _ => stronglyMeasurable_const) one_pos
    (fun _ _ => ⟨le_rfl, le_rfl⟩) (fun _ _ => by field_simp; ring)
    (fun _ => stronglyMeasurable_const)
    (fun _ _ => by rw [abs_of_pos (one_div_pos.2 h1β)]) hrate hflow
    (fun t => hsm t _ (hpre t)) hb0 (fun _ => Integrable.of_finite)
    (fun t => Eventually.of_forall (htvc t))
    (fun t k => Eventually.of_forall fun ω => by simp [S.E_const]) t
  filter_upwards [h] with ω e
  rw [e]
  simp

end Cochrane.AssetsRulesBalanceSheets.FiscalRulesBelowCounter
