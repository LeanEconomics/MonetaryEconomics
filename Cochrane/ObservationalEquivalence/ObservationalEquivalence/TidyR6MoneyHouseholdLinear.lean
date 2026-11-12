/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.TidyR6MoneyHouseholdTree
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The derived bond-pricing equation linearises to the Fisher equation of (22.2)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, eq. (22.2), p. 495 (the
Fisher equation `i_t = E_tπ_{t+1}` of the frictionless model), with the household's nonlinear
bond-pricing condition `Q_t = βP_tE_t[1/P_{t+1}]` derived in `TidyR6MoneyHouseholdEqm` and, on
finite trees, in `TidyR6MoneyHouseholdTree`.

Written in logs, the derived condition says that the bond yield is
`log(1/Q_t) = −log β − log E_t[exp(−π_{t+1})]` with `π_{t+1} = log P_{t+1} − log P_t`
(`fisher_log_form`). For an arbitrary core `ExpectationSystem`, at any steady state `π*` and along
every bounded direction `x` of log inflation, the map `ε ↦ −log β − log E_t[exp(−(π* + εx))]`
takes the value `−log β + π*` at `ε = 0` and has derivative `E_tx` there
(`gateaux_log_fisher`): the linear Fisher equation of (22.2), `i_t = E_tπ_{t+1}` with rates
measured from the steady state, is the exact derivative of the household's first-order condition.
The derivative lemmas are restated from the NewKeynesianSelection project (its module
LowerBound). `tree_fisher_log_form` applies this to every derived equilibrium on a finite tree.
-/

namespace Cochrane.ObservationalEquivalence.TidyR6MoneyHouseholdLinear

open Filter Topology
open Cochrane.ObservationalEquivalence.TidyR6MoneyHousehold

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), eq. (22.2), p. 495 (tool, restated from the NewKeynesianSelection project):
for `|z| ≤ 1`, `|e^z − 1 − z| ≤ z²`. -/
theorem abs_exp_sub_le {z : ℝ} (hz : |z| ≤ 1) : |Real.exp z - 1 - z| ≤ z ^ 2 :=
  Real.abs_exp_sub_one_sub_id_le hz

/-- Cochrane (2023), eq. (22.2), p. 495 (restated from the NewKeynesianSelection project): for an
arbitrary expectation system and bounded `x`, `ε ↦ E_t[exp(−εx)]` has derivative `−E_tx` at
`ε = 0`. -/
theorem hasDerivAt_E_exp {x : Ω → ℝ} {M : ℝ} (hM : 0 < M) (hx : ∀ ω, |x ω| ≤ M) (t : ℕ)
    (ω : Ω) :
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

/-- Cochrane (2023), eq. (22.2), p. 495 (restated from the NewKeynesianSelection project): for
bounded `x` (`|x| ≤ M`) and every `ε`, `E_t[exp(−εx)] ≥ exp(−|ε|M) > 0`. -/
theorem E_exp_pos {x : Ω → ℝ} {M : ℝ} (hx : ∀ ω, |x ω| ≤ M) (t : ℕ) (ω : Ω) (ε : ℝ) :
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

/-- Cochrane (2023), eq. (22.2), p. 495 (**the Fisher equation as the exact derivative of the
derived bond-pricing condition**): for any expectation system, steady-state log inflation `π*`
and bounded direction `x`, the log bond yield implied by the household's condition,
`ε ↦ −log β − log E_t[exp(−(π* + εx))]`, equals `−log β + π*` at `ε = 0` and has derivative
`E_tx` there: `i_t = E_tπ_{t+1}` in deviations from the steady state. -/
theorem gateaux_log_fisher (β pis : ℝ) {x : Ω → ℝ} {M : ℝ} (hM : 0 < M)
    (hx : ∀ ω, |x ω| ≤ M) (t : ℕ) (ω : Ω) :
    -Real.log β - Real.log (𝔼.E t (fun ω' => Real.exp (-(pis + 0 * x ω'))) ω) =
        -Real.log β + pis ∧
      HasDerivAt
        (fun ε => -Real.log β - Real.log (𝔼.E t (fun ω' => Real.exp (-(pis + ε * x ω'))) ω))
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
  have h1 : 𝔼.E t (fun ω' => Real.exp (-((0 : ℝ) * x ω'))) ω = 1 := by
    simp only [zero_mul, neg_zero, Real.exp_zero]
    exact congrFun (𝔼.const t 1) ω
  refine ⟨?_, ?_⟩
  · rw [hsplit, h1, mul_one, Real.log_exp]
    ring
  · have hfun : (fun ε => -Real.log β -
        Real.log (𝔼.E t (fun ω' => Real.exp (-(pis + ε * x ω'))) ω)) =
        fun ε => (-Real.log β + pis) -
          Real.log (𝔼.E t (fun ω' => Real.exp (-(ε * x ω'))) ω) := by
      funext ε
      rw [hsplit, Real.log_mul (Real.exp_pos _).ne' (E_exp_pos 𝔼 hx t ω ε).ne', Real.log_exp]
      ring
    rw [hfun]
    have hlog := (hasDerivAt_E_exp 𝔼 hM hx t ω).log (by rw [h1]; exact one_ne_zero)
    rw [h1, div_one] at hlog
    have := (hasDerivAt_const (0 : ℝ) (-Real.log β + pis)).sub hlog
    convert this using 1
    ring

/-- Cochrane (2023), eq. (16.25), p. 377, and (22.2), p. 495 (**the derived condition in logs**):
if `Q_t = βP_tE_t[1/P_{t+1}] > 0` with positive, adapted prices and the pull-out property, then
`log(1/Q_t) = −log β − log E_t[exp(−π_{t+1})]`, `π_{t+1} = log P_{t+1} − log P_t`. -/
theorem fisher_log_form (hpo : 𝔼.PullOut) {β : ℝ} (hβ : 0 < β) {P Q : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) (hPa : 𝔼.Adapted P)
    (hF : ∀ t ω, Q t ω = β * P t ω * 𝔼.E t (fun ω => (P (t + 1) ω)⁻¹) ω)
    (hQ : ∀ t ω, 0 < Q t ω) (t : ℕ) (ω : Ω) :
    Real.log (1 / Q t ω) = -Real.log β -
      Real.log (𝔼.E t (fun ω' => Real.exp (-(Real.log (P (t + 1) ω') - Real.log (P t ω')))) ω) := by
  have e1 : (fun ω' => Real.exp (-(Real.log (P (t + 1) ω') - Real.log (P t ω')))) =
      P t * fun ω' => (P (t + 1) ω')⁻¹ := by
    funext ω'
    rw [neg_sub, Real.exp_sub, Real.exp_log (hP t ω'), Real.exp_log (hP (t + 1) ω')]
    simp only [Pi.mul_apply, div_eq_mul_inv]
  rw [e1, hpo t _ _ (hPa t)]
  simp only [Pi.mul_apply]
  have hq := hQ t ω
  rw [hF t ω] at hq ⊢
  have hE : 0 < 𝔼.E t (fun ω => (P (t + 1) ω)⁻¹) ω := by
    have := hP t ω
    by_contra h
    push Not at h
    nlinarith [mul_pos hβ this]
  rw [one_div, Real.log_inv, mul_assoc, Real.log_mul hβ.ne' (mul_pos (hP t ω) hE).ne']
  ring

/-- Cochrane (2023), eq. (22.2), p. 495, on finite trees: in every derived equilibrium with
positive debt and a positive bond price, the bond yield is, at every node,
`log(1/Q_t) = −log β − log E_t[exp(−π_{t+1})]` in the tree's expectation system, the map whose
derivative at a steady state is the Fisher equation `i_t = E_tπ_{t+1}` (`gateaux_log_fisher`). -/
theorem tree_fisher_log_form {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [DiscreteMeasurableSpace Ω] (T : ExpectationsFiniteTree.FiniteTree Ω) {e : Econ Ω}
    {B M : ℕ → Ω → ℝ} (hreg : EconReg (ExpectationsMeasure.TreeBridge.treeSystem T) e)
    (hBa : T.toExpectationSystem.Adapted B) (hMa : T.toExpectationSystem.Adapted M)
    (hBpos : ∀ t ω, 0 < B t ω) (hP : ∀ t ω, 0 < e.P t ω) (hQ : ∀ t ω, 0 < e.Q t ω)
    (h : TidyR6MoneyHouseholdEqm.DerivedEqm (ExpectationsMeasure.TreeBridge.treeSystem T) e B M)
    (t : ℕ) (ω : Ω) :
    Real.log (1 / e.Q t ω) = -Real.log e.β - Real.log (T.toExpectationSystem.E t
      (fun ω' => Real.exp (-(Real.log (e.P (t + 1) ω') - Real.log (e.P t ω')))) ω) := by
  have hF := ((TidyR6MoneyHouseholdTree.tree_derived_iff T hreg hBa hMa hBpos).1 h).1
  have hPa : T.toExpectationSystem.Adapted e.P :=
    (TidyR6MoneyHouseholdTree.adapted_iff T).1 hreg.2.1.1
  exact fisher_log_form T.toExpectationSystem (ExpectationsFiniteTree.finiteTree_pullOut T)
    hreg.1.1 hP hPa (fun t ω => hF t ω) hQ t ω

end Cochrane.ObservationalEquivalence.TidyR6MoneyHouseholdLinear
