/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PolicyResponseDynamics.ForwardSystems
import PolicyResponseDynamics.ExpectationCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Habit persistence in aggregate expenditure

Woodford (2003), *Interest and Prices*, Chapter 5, §1.2, pp. 332–336, and Appendix D, §D.1,
pp. 687–688. All model equations hold for an arbitrary `ExpectationSystem` (perfect foresight or
genuine uncertainty); derivatives of expectations use a finite state space; infinite horizons
are genuine `tsum`s or limits.

## Main results

* (1.23) `habit_marginal_value`: `λ_T = u_c(C_T − ηC_{T−1}) − βη E_T u_c(C_{T+1} − ηC_T)` is the
  derivative of the infinite-horizon objective with respect to extra income at `T` (the two
  overlapping terms), `βᵀ E_0[a λ_T]`.
* App. D.1: `invest_marginal_value` (the investment interpretation gives (1.23) with `u_c`
  replaced by `γ − ψ_s`, `γ = νβ/[(1 − βη)(1 − β(1 − δ))]`, a derivative involving the genuine
  sum `hasSum_capResp`), `hasSum_project_value` (the value of a project is `γ`),
  `investment_perturb`, `capital_project`, `projK_eq`, `gamma_sub_strictAnti`.
* (1.24)–(1.25) as exact derivatives: `euler_loglinear`, `lamOf_hasDerivAt`, `uhC_eq`
  (`φ⁻¹ = (1 − βη)σ`), `euler_iff_IS`, `IS125_of_nonlinear`.
* The forward solution (p. 334): `quasiDiff_eq_forwardSeries`
  (`x_t − ηx_{t−1} = ∑ (βη)ʲ E_t x̃_{t+j}`), `xTilde_longRun` (`x̃_∞ = (1 − η)(1 − βη)x_∞`),
  `sum_q_tendsto`, `forward_solution` (with `ξ_k = xiK`, `xiK_pos`; stated as a limit of partial
  sums, since the series need not converge absolutely), `transitory_ar1` and `ar1_solves_IS`
  (transitory real-rate gaps ⇔ AR(1) output gap with coefficient `η`), `ar1_gap_response`,
  `hasSum_xiK_geom`, `ar2_output_gap`.
* (1.26): `AS126_iff_ASch3` (conditional on the Ch. 3 AS relation), `AS126_eta_zero`.
* (1.27)–(1.29): `as_identity`, `AS126_iff_AS127`, `as_identity_coeffs`, `coeffs_iff_root`,
  `identity_iff_root`, `habDelta`, `habKappa` (division-free), `habDelta_root`,
  `AS126_iff_AS127_habit` (valid for all `η ≥ 0`), `habKappa_eq` (`κ = ξ_p ηφ/δ`, `η > 0`),
  `habDelta_nonneg`, `habDelta_le`, `habDelta_pos_iff`, `habDelta_lt_iff`,
  `habDelta_eq_of_omega_zero`, `habDelta_smaller_root`, `habDelta2_gt_one`; survey error 12:
  `eta_zero_kappa`; the limits `delta_div_eta_tendsto`, `kappa_tendsto`; Ch. 6 p. 404:
  `habDelta_strictMonoOn`.
* (1.30)–(1.33): one-predetermined-variable Blanchard–Kahn theory for `n` jump variables
  (`PredSysN`, `DecompN`, `BKCondition`, `predSysN_existsUnique`, `predSysN_formula`,
  `predSysN_solution_form`, `predSysN_summable`), the habit model as such a system
  (`habit_iff_predSys`), `habit_existsUnique`, `habit_solution_form`, `habit_decomp_eta_zero`;
  survey error 7: `taylor130_iff_quarter`. Non-vacuity for `η > 0` at the Table 5.1
  calibration with `η = 1/2`: `vphiOf_calibration`, `calPhiPi`, `calPhiX`, `calOmega`, `calG`,
  `bkCondition_calibration`, `habit_existsUnique_calibration`. Necessity of `BKCondition` is
  proved in the module `HabitNecessity` (`habit_determinate_iff_bk`).
-/

namespace Woodford.PolicyResponseDynamics.Habit

open Filter Topology ForwardSystems ExpectationCalculus

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Lags and the quasi-difference `x̃` -/

/-- Woodford (2003), §1.2, p. 333: the lagged process `x_{t−1}`, with the initial value
`x_{−1}` given (known at date 0). -/
def lag (xm1 : Ω → ℝ) (x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => xm1
  | t + 1 => x t

/-- Woodford (2003), p. 333: the lag at date `t + 1` is the date-`t` value. -/
theorem lag_succ (xm1 : Ω → ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) : lag xm1 x (t + 1) = x t := rfl

/-- Woodford (2003), p. 333: the lag at date 0 is the given initial value. -/
theorem lag_zero (xm1 : Ω → ℝ) (x : ℕ → Ω → ℝ) : lag xm1 x 0 = xm1 := rfl

/-- Woodford (2003), p. 333: the lag of an adapted process with `x_{−1}` known at date 0 is
known at date `t`. -/
theorem lag_known {xm1 : Ω → ℝ} (hm : 𝔼.E 0 xm1 = xm1) {x : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x)
    (t : ℕ) : 𝔼.E t (lag xm1 x t) = lag xm1 x t := by
  cases t with
  | zero => exact hm
  | succ t => exact ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hx t)

/-- Woodford (2003), p. 333 (an infinite-horizon objective perturbed at two dates): if `g`
differs from a summable `f` only at dates `T` and `T + 1`, then
`∑ g = ∑ f + (g_T − f_T) + (g_{T+1} − f_{T+1})`. -/
theorem tsum_two_point {f g : ℕ → ℝ} (hf : Summable f) (T : ℕ)
    (hfg : ∀ t, t ≠ T → t ≠ T + 1 → g t = f t) :
    ∑' t, g t = ∑' t, f t + (g T - f T) + (g (T + 1) - f (T + 1)) := by
  have hd : ∀ t ∉ ({T, T + 1} : Finset ℕ), g t - f t = 0 := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    rw [hfg t ht.1 ht.2, sub_self]
  have hds : Summable (fun t => g t - f t) := summable_of_ne_finset_zero hd
  have hsplit : g = fun t => f t + (g t - f t) := by
    funext t
    ring
  rw [hsplit, hf.tsum_add hds, tsum_eq_sum hd, Finset.sum_pair (by omega)]
  simp only [add_sub_cancel_left]
  ring

/-! ### (1.23): the marginal value of income in the habit problem -/

/-- Woodford (2003), §1.2, p. 333: habit-adjusted expenditure `C_t − η C_{t−1}`, the argument
of the period utility `u(C_t − η C_{t−1}; ξ_t)`. -/
def habitArg (η : ℝ) (Cm1 : Ω → ℝ) (C : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  C t - η • lag Cm1 C t

/-- Woodford (2003), §1.2, p. 333: the household's objective
`E_0 ∑_{t ≥ 0} βᵗ u(C_t − η C_{t−1}; ξ_t)` (evaluated in the date-0 state `ω`); the dependence of
`u` on the date and state through the taste shock `ξ_t` is the dependence of `u t ω` on
`(t, ω)`. -/
noncomputable def habitObjective (β η : ℝ) (u : ℕ → Ω → ℝ → ℝ) (Cm1 : Ω → ℝ)
    (C : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑' t, β ^ t * 𝔼.E 0 (fun ω' => u t ω' (habitArg η Cm1 C t ω')) ω

/-- Woodford (2003), p. 333: an additional amount of real income `ε a` at date `T` (`a` known
at `T`), all of it spent at date `T`. -/
def perturb (C : ℕ → Ω → ℝ) (T : ℕ) (a : Ω → ℝ) (ε : ℝ) : ℕ → Ω → ℝ :=
  Function.update C T (C T + ε • a)

/-- Woodford (2003), eq. (1.23), p. 333: the marginal utility of real income in the habit model,
`λ_t = u_c(C_t − η C_{t−1}; ξ_t) − βη E_t[u_c(C_{t+1} − η C_t; ξ_{t+1})]`. -/
noncomputable def habitLambda (β η : ℝ) (uc : ℕ → Ω → ℝ → ℝ) (Cm1 : Ω → ℝ) (C : ℕ → Ω → ℝ)
    (t : ℕ) : Ω → ℝ :=
  (fun ω => uc t ω (habitArg η Cm1 C t ω)) -
    (β * η) • 𝔼.E t (fun ω => uc (t + 1) ω (habitArg η Cm1 C (t + 1) ω))

omit 𝔼 in
/-- Woodford (2003), p. 333: the unperturbed path. -/
theorem perturb_zero (C : ℕ → Ω → ℝ) (T : ℕ) (a : Ω → ℝ) : perturb C T a 0 = C := by
  simp [perturb]

omit 𝔼 in
/-- Woodford (2003), p. 333: extra spending at `T` changes `C_T − η C_{T−1}` by `ε a`. -/
theorem habitArg_perturb_self (η : ℝ) (Cm1 : Ω → ℝ) (C : ℕ → Ω → ℝ) (T : ℕ) (a : Ω → ℝ)
    (ε : ℝ) : habitArg η Cm1 (perturb C T a ε) T = habitArg η Cm1 C T + ε • a := by
  cases T with
  | zero => simp [habitArg, perturb, lag]; abel
  | succ T =>
    simp only [habitArg, perturb, lag, Function.update_self]
    rw [Function.update_of_ne (by omega)]
    abel

omit 𝔼 in
/-- Woodford (2003), p. 333: extra spending at `T` changes `C_{T+1} − η C_T` by `−η ε a`. -/
theorem habitArg_perturb_succ (η : ℝ) (Cm1 : Ω → ℝ) (C : ℕ → Ω → ℝ) (T : ℕ) (a : Ω → ℝ)
    (ε : ℝ) :
    habitArg η Cm1 (perturb C T a ε) (T + 1) = habitArg η Cm1 C (T + 1) - (η * ε) • a := by
  simp only [habitArg, perturb, lag, Function.update_self]
  rw [Function.update_of_ne (by omega), smul_add, smul_smul]
  abel

omit 𝔼 in
/-- Woodford (2003), p. 333: extra spending at `T` leaves `C_t − η C_{t−1}` unchanged at every
other date than `T` and `T + 1`. -/
theorem habitArg_perturb_other (η : ℝ) (Cm1 : Ω → ℝ) (C : ℕ → Ω → ℝ) (T : ℕ) (a : Ω → ℝ)
    (ε : ℝ) {t : ℕ} (h1 : t ≠ T) (h2 : t ≠ T + 1) :
    habitArg η Cm1 (perturb C T a ε) t = habitArg η Cm1 C t := by
  cases t with
  | zero => simp only [habitArg, perturb, lag]; rw [Function.update_of_ne h1]
  | succ t =>
    simp only [habitArg, perturb, lag]
    rw [Function.update_of_ne h1, Function.update_of_ne (by omega)]

/-- **Woodford (2003), eq. (1.23), p. 333.** `λ_T` is the marginal value of real income at date
`T`: spending an additional `ε a` at date `T` (`a` known at `T`) raises the infinite-horizon
objective `E_0 ∑ βᵗ u(C_t − η C_{t−1}; ξ_t)` at rate `βᵀ E_0[a λ_T]`, where
`λ_T = u_c(C_T − η C_{T−1}) − βη E_T u_c(C_{T+1} − η C_T)` collects the two overlapping terms
in which `C_T` appears. Finite state space (so `E_0` commutes with `d/dε`), any `ExpectationSystem`
with the pull-out property, any summable objective. -/
theorem habit_marginal_value [Finite Ω] (hPO : 𝔼.PullOut) {β η : ℝ}
    {u uc : ℕ → Ω → ℝ → ℝ} (hu : ∀ t ω h, HasDerivAt (u t ω) (uc t ω h) h)
    (Cm1 : Ω → ℝ) (C : ℕ → Ω → ℝ) {T : ℕ} {a : Ω → ℝ} (ha : 𝔼.E T a = a) (ω : Ω)
    (hsum : Summable fun t => β ^ t * 𝔼.E 0 (fun ω' => u t ω' (habitArg η Cm1 C t ω')) ω) :
    HasDerivAt (fun ε => habitObjective 𝔼 β η u Cm1 (perturb C T a ε) ω)
      (β ^ T * 𝔼.E 0 (a * habitLambda 𝔼 β η uc Cm1 C T) ω) 0 := by
  set F : ℝ → ℕ → ℝ := fun ε t =>
    β ^ t * 𝔼.E 0 (fun ω' => u t ω' (habitArg η Cm1 (perturb C T a ε) t ω')) ω with hF
  have hF0 : F 0 = fun t => β ^ t * 𝔼.E 0 (fun ω' => u t ω' (habitArg η Cm1 C t ω')) ω := by
    simp only [hF, perturb_zero]
  have hobj : ∀ ε, habitObjective 𝔼 β η u Cm1 (perturb C T a ε) ω =
      ∑' t, F 0 t + (F ε T - F 0 T) + (F ε (T + 1) - F 0 (T + 1)) := by
    intro ε
    refine tsum_two_point (hF0 ▸ hsum) T (fun t h1 h2 => ?_)
    simp only [hF, habitArg_perturb_other η Cm1 C T a ε h1 h2, perturb_zero]
  have hT : HasDerivAt (fun ε => F ε T)
      (β ^ T * 𝔼.E 0 (fun ω' => uc T ω' (habitArg η Cm1 C T ω') * a ω') ω) 0 := by
    simp only [hF, habitArg_perturb_self]
    refine HasDerivAt.const_mul _ (hasDerivAt_E 𝔼 (fun ω' => ?_) 0 ω)
    have hl : HasDerivAt (fun ε : ℝ => habitArg η Cm1 C T ω' + ε * a ω') (a ω') 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (a ω')).const_add
        (habitArg η Cm1 C T ω')
    have := (hu T ω' (habitArg η Cm1 C T ω')).comp_of_eq (0 : ℝ) hl (by simp)
    simpa [Function.comp_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
  have hT1 : HasDerivAt (fun ε => F ε (T + 1))
      (β ^ (T + 1) * 𝔼.E 0 (fun ω' => uc (T + 1) ω' (habitArg η Cm1 C (T + 1) ω') *
        (-η * a ω')) ω) 0 := by
    simp only [hF, habitArg_perturb_succ]
    refine HasDerivAt.const_mul _ (hasDerivAt_E 𝔼 (fun ω' => ?_) 0 ω)
    have hl : HasDerivAt (fun ε : ℝ => habitArg η Cm1 C (T + 1) ω' - η * ε * a ω')
        (-η * a ω') 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).const_mul η).mul_const (a ω')).const_sub
        (habitArg η Cm1 C (T + 1) ω')
      simpa [neg_mul] using this
    have := (hu (T + 1) ω' (habitArg η Cm1 C (T + 1) ω')).comp_of_eq (0 : ℝ) hl (by simp)
    simpa [Function.comp_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_assoc] using this
  have hsumD := ((hT.sub_const (F 0 T)).const_add (∑' t, F 0 t)).add
    (hT1.sub_const (F 0 (T + 1)))
  have hfun : (fun ε => habitObjective 𝔼 β η u Cm1 (perturb C T a ε) ω) =
      fun ε => ∑' t, F 0 t + (F ε T - F 0 T) + (F ε (T + 1) - F 0 (T + 1)) := by
    funext ε
    exact hobj ε
  rw [hfun]
  convert hsumD using 1
  -- identify the derivative with `βᵀ E_0[a λ_T]`
  have hpull : 𝔼.E 0 (a * 𝔼.E T (fun ω' => uc (T + 1) ω' (habitArg η Cm1 C (T + 1) ω'))) =
      𝔼.E 0 (fun ω' => uc (T + 1) ω' (habitArg η Cm1 C (T + 1) ω') * a ω') := by
    rw [← hPO T a _ ha, 𝔼.tower (Nat.zero_le T)]
    congr 1
    funext ω'
    simp only [Pi.mul_apply]
    ring
  have hlam : a * habitLambda 𝔼 β η uc Cm1 C T =
      (fun ω' => uc T ω' (habitArg η Cm1 C T ω') * a ω') -
        (β * η) • (a * 𝔼.E T (fun ω' => uc (T + 1) ω' (habitArg η Cm1 C (T + 1) ω'))) := by
    funext ω'
    simp only [habitLambda, Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hneg : (fun ω' => uc (T + 1) ω' (habitArg η Cm1 C (T + 1) ω') * (-η * a ω')) =
      (-η) • (fun ω' => uc (T + 1) ω' (habitArg η Cm1 C (T + 1) ω') * a ω') := by
    funext ω'
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hlam, map_sub, map_smul, hpull, hneg, map_smul]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### Appendix D.1: the investment-adjustment-cost interpretation -/

/-- Woodford (2003), App. D.1, p. 688: the capital stock, `K_{t+1} = I_t + (1 − δ) K_t`, from
a given `K_0`. -/
def capital (δ : ℝ) (K0 : Ω → ℝ) (I : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => K0
  | t + 1 => I t + (1 - δ) • capital δ K0 I t

/-- Woodford (2003), App. D.1, p. 688: investment spending from project starts,
`I_t = S_t + η I_{t−1}` (`I_{−1}` given). -/
def investment (η : ℝ) (Im1 : Ω → ℝ) (S : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => S 0 + η • Im1
  | t + 1 => S (t + 1) + η • investment η Im1 S t

omit 𝔼 in
/-- Woodford (2003), App. D.1, p. 688: project starts are recovered as
`S_t = I_t − η I_{t−1}`, the argument of the effort cost `ψ(S_t; ξ_t)`. -/
theorem habitArg_investment (η : ℝ) (Im1 : Ω → ℝ) (S : ℕ → Ω → ℝ) (t : ℕ) :
    habitArg η Im1 (investment η Im1 S) t = S t := by
  cases t with
  | zero => simp [habitArg, investment, lag]
  | succ t => simp [habitArg, investment, lag]

/-- Woodford (2003), App. D.1, p. 688: the response of capital `t` periods after a unit of
extra investment spending at date `T`: `(1 − δ)^{t−T−1}` for `t > T`, zero otherwise. -/
noncomputable def capResp (δ : ℝ) (T t : ℕ) : ℝ := if T < t then (1 - δ) ^ (t - (T + 1)) else 0

omit 𝔼 in
/-- Woodford (2003), App. D.1, p. 688: extra spending `ε a` at date `T` raises `K_t` by
`ε (1 − δ)^{t−T−1} a` for `t > T`. -/
theorem capital_perturb (δ : ℝ) (K0 : Ω → ℝ) (I : ℕ → Ω → ℝ) (T : ℕ) (a : Ω → ℝ) (ε : ℝ)
    (t : ℕ) :
    capital δ K0 (perturb I T a ε) t = capital δ K0 I t + (ε * capResp δ T t) • a := by
  induction t with
  | zero => simp [capital, capResp]
  | succ t ih =>
    change perturb I T a ε t + (1 - δ) • capital δ K0 (perturb I T a ε) t =
      (I t + (1 - δ) • capital δ K0 I t) + (ε * capResp δ T (t + 1)) • a
    rw [ih]
    by_cases htT : t = T
    · subst htT
      have h1 : capResp δ t t = 0 := by simp [capResp]
      have h2 : capResp δ t (t + 1) = 1 := by simp [capResp]
      have hp : perturb I t a ε t = I t + ε • a := by simp [perturb]
      rw [h1, h2, hp]
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · have hp : perturb I T a ε t = I t := Function.update_of_ne htT _ _
      have hc : capResp δ T (t + 1) = (1 - δ) * capResp δ T t := by
        unfold capResp
        rcases lt_or_gt_of_ne htT with h | h
        · have h1 : ¬ T < t := by omega
          have h2 : ¬ T < t + 1 := by omega
          simp only [h1, h2, ite_false, mul_zero]
        · have h2 : T < t + 1 := by omega
          simp only [h, h2, ite_true]
          rw [show t + 1 - (T + 1) = (t - (T + 1)) + 1 by omega, pow_succ]
          ring
      rw [hp, hc]
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring

omit 𝔼 in
/-- Woodford (2003), App. D.1, p. 688: the discounted capital response to one unit of
investment spending at `T`, `∑_t βᵗ (1 − δ)^{t−T−1} = β^{T+1}/(1 − β(1 − δ))`. -/
theorem hasSum_capResp {β δ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (T : ℕ) :
    HasSum (fun t => β ^ t * capResp δ T t) (β ^ (T + 1) / (1 - β * (1 - δ))) := by
  have hq0 : 0 ≤ β * (1 - δ) := mul_nonneg hβ0 (by linarith)
  have hq1 : β * (1 - δ) < 1 := by nlinarith
  have hg := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (β ^ (T + 1))
  have hshift : HasSum (fun n => β ^ (n + (T + 1)) * capResp δ T (n + (T + 1)))
      (β ^ (T + 1) / (1 - β * (1 - δ))) := by
    rw [div_eq_mul_inv]
    refine hg.congr_fun fun n => ?_
    simp only [capResp, show T < n + (T + 1) by omega, ite_true, Nat.add_sub_cancel, pow_add,
      mul_pow]
    ring
  have h0 : ∑ i ∈ Finset.range (T + 1), β ^ i * capResp δ T i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have : ¬ T < i := by simp only [Finset.mem_range] at hi; omega
    simp [capResp, this]
  have := (hasSum_nat_add_iff (f := fun t => β ^ t * capResp δ T t) (T + 1)).mp hshift
  rwa [h0, add_zero] at this

/-- Woodford (2003), App. D.1, p. 688: `γ ≡ νβ/[(1 − βη)(1 − β(1 − δ))]`. -/
noncomputable def gammaD1 (β η δ ν : ℝ) : ℝ := ν * β / ((1 - β * η) * (1 - β * (1 - δ)))

/-- Woodford (2003), App. D.1, p. 688: the household objective in the investment
interpretation, `E_0 ∑ βᵗ [ν K_t − ψ(I_t − η I_{t−1}; ξ_t)]`. -/
noncomputable def investObjective (β η δ ν : ℝ) (ψ : ℕ → Ω → ℝ → ℝ) (K0 Im1 : Ω → ℝ)
    (I : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑' t, β ^ t * 𝔼.E 0 (fun ω' => ν * capital δ K0 I t ω' - ψ t ω' (habitArg η Im1 I t ω')) ω

/-- Woodford (2003), App. D.1, p. 688: the marginal value of real income in the investment
interpretation, (1.23) with `u_c(·; ξ_t)` replaced by `γ − ψ_s(I_t − η I_{t−1}; ξ_t)`. -/
noncomputable def investLambda (β η γ : ℝ) (ψs : ℕ → Ω → ℝ → ℝ) (Im1 : Ω → ℝ)
    (I : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (fun ω => γ - ψs t ω (habitArg η Im1 I t ω)) -
    (β * η) • 𝔼.E t (fun ω => γ - ψs (t + 1) ω (habitArg η Im1 I (t + 1) ω))

/-- **Woodford (2003), App. D.1, p. 688.** In the investment interpretation (utility flow
`ν K_t − ψ(S_t; ξ_t)`, `K_{t+1} = I_t + (1 − δ) K_t`, `I_t = S_t + η I_{t−1}`), spending an
additional `ε a` at date `T` raises the infinite-horizon objective at rate `βᵀ E_0[a λ_T]`, with
`λ_T = [γ − ψ_s(S_T)] − βη E_T[γ − ψ_s(S_{T+1})]`, `γ = νβ/[(1 − βη)(1 − β(1 − δ))]`: the form
(1.23) with `u_c` replaced by `γ − ψ_s`. The capital term changes at every later date, so the
derivative involves the genuine infinite sum `∑ βᵗ (1 − δ)^{t−T−1}`. -/
theorem invest_marginal_value [Finite Ω] (hPO : 𝔼.PullOut) {β η δ ν : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hη1 : β * η ≠ 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {ψ ψs : ℕ → Ω → ℝ → ℝ} (hψ : ∀ t ω s, HasDerivAt (ψ t ω) (ψs t ω s) s)
    (K0 Im1 : Ω → ℝ) (I : ℕ → Ω → ℝ) {T : ℕ} {a : Ω → ℝ} (ha : 𝔼.E T a = a) (ω : Ω)
    (hsum : Summable fun t => β ^ t *
      𝔼.E 0 (fun ω' => ν * capital δ K0 I t ω' - ψ t ω' (habitArg η Im1 I t ω')) ω) :
    HasDerivAt (fun ε => investObjective 𝔼 β η δ ν ψ K0 Im1 (perturb I T a ε) ω)
      (β ^ T * 𝔼.E 0 (a * investLambda 𝔼 β η (gammaD1 β η δ ν) ψs Im1 I T) ω) 0 := by
  set H : ℝ → ℕ → ℝ := fun ε t => β ^ t * 𝔼.E 0 (fun ω' => ν * capital δ K0 I t ω' -
    ψ t ω' (habitArg η Im1 (perturb I T a ε) t ω')) ω with hH
  set W : ℝ := ν * 𝔼.E 0 a ω with hW
  have hR := hasSum_capResp hβ0 hβ1 hδ0 hδ1 T
  have hG : ∀ ε t, β ^ t * 𝔼.E 0 (fun ω' => ν * capital δ K0 (perturb I T a ε) t ω' -
      ψ t ω' (habitArg η Im1 (perturb I T a ε) t ω')) ω =
      H ε t + ε * W * (β ^ t * capResp δ T t) := by
    intro ε t
    have hfun : (fun ω' => ν * capital δ K0 (perturb I T a ε) t ω' -
        ψ t ω' (habitArg η Im1 (perturb I T a ε) t ω')) =
        (fun ω' => ν * capital δ K0 I t ω' - ψ t ω' (habitArg η Im1 (perturb I T a ε) t ω')) +
          (ν * (ε * capResp δ T t)) • a := by
      funext ω'
      simp only [capital_perturb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfun, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hH, hW]
    ring
  have hH0 : H 0 = fun t => β ^ t *
      𝔼.E 0 (fun ω' => ν * capital δ K0 I t ω' - ψ t ω' (habitArg η Im1 I t ω')) ω := by
    simp only [hH, perturb_zero]
  have hobj : ∀ ε, investObjective 𝔼 β η δ ν ψ K0 Im1 (perturb I T a ε) ω =
      (∑' t, H 0 t + (H ε T - H 0 T) + (H ε (T + 1) - H 0 (T + 1))) +
        ε * W * (β ^ (T + 1) / (1 - β * (1 - δ))) := by
    intro ε
    have hHs : Summable (H ε) := by
      have := (hH0 ▸ hsum).add (summable_of_ne_finset_zero (s := ({T, T + 1} : Finset ℕ))
        (f := fun t => H ε t - H 0 t) (fun t ht => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
          simp only [hH, habitArg_perturb_other η Im1 I T a ε ht.1 ht.2, perturb_zero,
            sub_self]))
      refine this.congr fun t => ?_
      ring
    unfold investObjective
    simp only [hG]
    rw [hHs.tsum_add (hR.summable.mul_left (ε * W)), tsum_mul_left, hR.tsum_eq]
    congr 1
    refine tsum_two_point (hH0 ▸ hsum) T (fun t h1 h2 => ?_)
    simp only [hH, habitArg_perturb_other η Im1 I T a ε h1 h2, perturb_zero]
  have hT : HasDerivAt (fun ε => H ε T)
      (β ^ T * 𝔼.E 0 (fun ω' => -(ψs T ω' (habitArg η Im1 I T ω') * a ω')) ω) 0 := by
    simp only [hH, habitArg_perturb_self]
    refine HasDerivAt.const_mul _ (hasDerivAt_E 𝔼 (fun ω' => ?_) 0 ω)
    have hl : HasDerivAt (fun ε : ℝ => habitArg η Im1 I T ω' + ε * a ω') (a ω') 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (a ω')).const_add
        (habitArg η Im1 I T ω')
    have := ((hψ T ω' (habitArg η Im1 I T ω')).comp_of_eq (0 : ℝ) hl (by simp)).const_sub
      (ν * capital δ K0 I T ω')
    simpa [Function.comp_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
  have hT1 : HasDerivAt (fun ε => H ε (T + 1))
      (β ^ (T + 1) * 𝔼.E 0 (fun ω' => -(ψs (T + 1) ω' (habitArg η Im1 I (T + 1) ω') *
        (-η * a ω'))) ω) 0 := by
    simp only [hH, habitArg_perturb_succ]
    refine HasDerivAt.const_mul _ (hasDerivAt_E 𝔼 (fun ω' => ?_) 0 ω)
    have hl : HasDerivAt (fun ε : ℝ => habitArg η Im1 I (T + 1) ω' - η * ε * a ω')
        (-η * a ω') 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).const_mul η).mul_const (a ω')).const_sub
        (habitArg η Im1 I (T + 1) ω')
      simpa [neg_mul] using this
    have := ((hψ (T + 1) ω' (habitArg η Im1 I (T + 1) ω')).comp_of_eq (0 : ℝ) hl
      (by simp)).const_sub (ν * capital δ K0 I (T + 1) ω')
    simpa [Function.comp_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_assoc] using this
  have hlin : HasDerivAt (fun ε : ℝ => ε * W * (β ^ (T + 1) / (1 - β * (1 - δ))))
      (W * (β ^ (T + 1) / (1 - β * (1 - δ)))) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const W).mul_const
      (β ^ (T + 1) / (1 - β * (1 - δ)))
  have hsumD := (((hT.sub_const (H 0 T)).const_add (∑' t, H 0 t)).add
    (hT1.sub_const (H 0 (T + 1)))).add hlin
  have hfun : (fun ε => investObjective 𝔼 β η δ ν ψ K0 Im1 (perturb I T a ε) ω) =
      fun ε => (∑' t, H 0 t + (H ε T - H 0 T) + (H ε (T + 1) - H 0 (T + 1))) +
        ε * W * (β ^ (T + 1) / (1 - β * (1 - δ))) := by
    funext ε
    exact hobj ε
  rw [hfun]
  convert hsumD using 1
  set P1 : Ω → ℝ := fun ω' => ψs (T + 1) ω' (habitArg η Im1 I (T + 1) ω') with hP1
  have hpull : 𝔼.E 0 (a * 𝔼.E T P1) = 𝔼.E 0 (fun ω' => P1 ω' * a ω') := by
    rw [← hPO T a _ ha, 𝔼.tower (Nat.zero_le T)]
    congr 1
    funext ω'
    simp only [Pi.mul_apply]
    ring
  have hET : 𝔼.E T (fun ω' => gammaD1 β η δ ν - P1 ω') =
      (fun _ => gammaD1 β η δ ν) - 𝔼.E T P1 := by
    rw [show (fun ω' => gammaD1 β η δ ν - P1 ω') = (fun _ => gammaD1 β η δ ν) - P1 from rfl,
      map_sub, 𝔼.const]
  have hlam : a * investLambda 𝔼 β η (gammaD1 β η δ ν) ψs Im1 I T =
      (gammaD1 β η δ ν * (1 - β * η)) • a -
        (fun ω' => ψs T ω' (habitArg η Im1 I T ω') * a ω') +
          (β * η) • (a * 𝔼.E T P1) := by
    unfold investLambda
    rw [show (fun ω => gammaD1 β η δ ν - ψs (T + 1) ω (habitArg η Im1 I (T + 1) ω)) =
      fun ω' => gammaD1 β η δ ν - P1 ω' from rfl, hET]
    funext ω'
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hneg1 : (fun ω' => -(ψs T ω' (habitArg η Im1 I T ω') * a ω')) =
      -(fun ω' => ψs T ω' (habitArg η Im1 I T ω') * a ω') := rfl
  have hneg2 : (fun ω' => -(P1 ω' * (-η * a ω'))) = η • (fun ω' => P1 ω' * a ω') := by
    funext ω'
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hlam, map_add, map_sub, map_smul, map_smul, hpull, hneg1, hneg2, map_neg, map_smul]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hW]
  have hden : (1 - β * (1 - δ)) ≠ 0 := by nlinarith
  have hden2 : (1 - β * η) ≠ 0 := sub_ne_zero.mpr (Ne.symm hη1)
  unfold gammaD1
  field_simp
  ring

/-- Woodford (2003), App. D.1, p. 688: the capital generated by one project started at date 0,
`ΔK_0 = 0`, `ΔK_{m+1} = ηᵐ + (1 − δ) ΔK_m` (the project's expenditure stream is `ηʲ`). -/
noncomputable def projK (η δ : ℝ) : ℕ → ℝ
  | 0 => 0
  | m + 1 => η ^ m + (1 - δ) * projK η δ m

/-- Woodford (2003), App. D.1, p. 688: `ΔK_m = ∑_{j<m} ηʲ (1 − δ)^{m−1−j}`. -/
theorem projK_eq (η δ : ℝ) (m : ℕ) :
    projK η δ m = ∑ j ∈ Finset.range m, η ^ j * (1 - δ) ^ (m - 1 - j) := by
  induction m with
  | zero => simp [projK]
  | succ m ih =>
    rw [projK, ih, Finset.sum_range_succ, Finset.mul_sum]
    rw [show m + 1 - 1 - m = 0 by omega, pow_zero, mul_one, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_range] at hj
    rw [show m + 1 - 1 - j = (m - 1 - j) + 1 by omega, pow_succ]
    ring

/-- **Woodford (2003), App. D.1, p. 688: the value of a project.** Starting one project (an
expenditure stream `ηʲ`) yields capital services worth
`∑_{m ≥ 0} βᵐ ν ΔK_m = γ = νβ/[(1 − βη)(1 − β(1 − δ))]`, a genuine infinite sum. -/
theorem hasSum_project_value {β η δ ν : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    HasSum (fun m => β ^ m * (ν * projK η δ m)) (gammaD1 β η δ ν) := by
  have hle : ∀ m, 0 ≤ projK η δ m ∧ projK η δ m ≤ m := by
    intro m
    induction m with
    | zero => simp [projK]
    | succ m ih =>
      have h1 : 0 ≤ η ^ m := pow_nonneg hη0 m
      have h2 : η ^ m ≤ 1 := pow_le_one₀ hη0 hη1
      simp only [projK]
      push_cast
      constructor <;> nlinarith [ih.1, ih.2]
  have hβn : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hβ0]; exact hβ1
  have hsV : Summable (fun m => β ^ m * projK η δ m) := by
    refine Summable.of_norm_bounded (summable_pow_mul_geometric_of_norm_lt_one 1 hβn)
      (fun m => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0, abs_of_nonneg (hle m).1,
      pow_one, mul_comm]
    exact mul_le_mul_of_nonneg_right (hle m).2 (pow_nonneg hβ0 m)
  set V := ∑' m, β ^ m * projK η δ m with hV
  have hq0 : 0 ≤ β * η := mul_nonneg hβ0 hη0
  have hq1 : β * η < 1 := by nlinarith
  have hgeo := (hasSum_geometric_of_lt_one hq0 hq1)
  have hrec : V = β * (1 - β * η)⁻¹ + β * (1 - δ) * V := by
    conv_lhs => rw [hV, hsV.tsum_eq_zero_add]
    simp only [projK, mul_zero, zero_add]
    have hsplit : (fun m => β ^ (m + 1) * (η ^ m + (1 - δ) * projK η δ m)) =
        fun m => β * (β * η) ^ m + β * (1 - δ) * (β ^ m * projK η δ m) := by
      funext m
      rw [mul_pow, pow_succ]
      ring
    rw [hsplit, (hgeo.summable.mul_left β).tsum_add (hsV.mul_left (β * (1 - δ))),
      tsum_mul_left, tsum_mul_left, hgeo.tsum_eq]
  have hden : 0 < 1 - β * (1 - δ) := by nlinarith
  have hVval : V = β / ((1 - β * η) * (1 - β * (1 - δ))) := by
    have hq : 1 - β * η ≠ 0 := by linarith
    rw [eq_div_iff (mul_ne_zero hq hden.ne')]
    have h2 : V * (1 - β * (1 - δ)) = β * (1 - β * η)⁻¹ := by linear_combination hrec
    calc V * ((1 - β * η) * (1 - β * (1 - δ))) = (V * (1 - β * (1 - δ))) * (1 - β * η) := by
          ring
      _ = β := by rw [h2, mul_assoc, inv_mul_cancel₀ hq, mul_one]
  have := (hsV.hasSum.mul_left ν)
  rw [← hV, hVval] at this
  convert this using 1
  · funext m
    ring
  · unfold gammaD1
    ring

/-- Woodford (2003), App. D.1, p. 688: the expenditure weight of a project started at `T`,
`η^{t−T}` for `t ≥ T`. -/
noncomputable def projI (η : ℝ) (T t : ℕ) : ℝ := if T ≤ t then η ^ (t - T) else 0

/-- Woodford (2003), App. D.1, p. 688: the capital weight of a project started at `T`,
`ΔK_{t−T}` for `t ≥ T`. -/
noncomputable def projKat (η δ : ℝ) (T t : ℕ) : ℝ := if T ≤ t then projK η δ (t - T) else 0

omit 𝔼 in
/-- Woodford (2003), App. D.1, p. 688: "starting a new project in period `t` implies a stream
of investment expenditures of size `ηʲ` in each period `t + j`": raising `S_T` by `ε a` raises
`I_t` by `ε η^{t−T} a` for `t ≥ T`. -/
theorem investment_perturb (η : ℝ) (Im1 : Ω → ℝ) (S : ℕ → Ω → ℝ) (T : ℕ) (a : Ω → ℝ)
    (ε : ℝ) (t : ℕ) :
    investment η Im1 (perturb S T a ε) t = investment η Im1 S t + (ε * projI η T t) • a := by
  induction t with
  | zero =>
    change perturb S T a ε 0 + η • Im1 = (S 0 + η • Im1) + (ε * projI η T 0) • a
    by_cases hT : T = 0
    · subst hT
      have hp : perturb S 0 a ε 0 = S 0 + ε • a := by simp [perturb]
      rw [hp]
      simp only [projI, le_refl, ite_true, Nat.sub_self, pow_zero, mul_one]
      abel
    · have hp : perturb S T a ε 0 = S 0 := Function.update_of_ne (Ne.symm hT) _ _
      have hw : projI η T 0 = 0 := by simp [projI]; omega
      rw [hp, hw, mul_zero, zero_smul, add_zero]
  | succ t ih =>
    change perturb S T a ε (t + 1) + η • investment η Im1 (perturb S T a ε) t =
      (S (t + 1) + η • investment η Im1 S t) + (ε * projI η T (t + 1)) • a
    rw [ih]
    by_cases hT : t + 1 = T
    · subst hT
      have hp : perturb S (t + 1) a ε (t + 1) = S (t + 1) + ε • a := by simp [perturb]
      have h1 : projI η (t + 1) t = 0 := by simp [projI]
      have h2 : projI η (t + 1) (t + 1) = 1 := by simp [projI]
      rw [hp, h1, h2]
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · have hp : perturb S T a ε (t + 1) = S (t + 1) := Function.update_of_ne hT _ _
      have hw : projI η T (t + 1) = η * projI η T t := by
        unfold projI
        by_cases h : T ≤ t
        · simp only [h, show T ≤ t + 1 by omega, ite_true]
          rw [show t + 1 - T = (t - T) + 1 by omega, pow_succ]
          ring
        · simp only [h, show ¬ T ≤ t + 1 by omega, ite_false, mul_zero]
      rw [hp, hw]
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring

omit 𝔼 in
/-- Woodford (2003), App. D.1, p. 688: a project started at `T` raises the capital stock at
`t ≥ T` by `ΔK_{t−T}`. -/
theorem capital_project (δ η : ℝ) (K0 Im1 : Ω → ℝ) (S : ℕ → Ω → ℝ) (T : ℕ) (a : Ω → ℝ)
    (ε : ℝ) (t : ℕ) :
    capital δ K0 (investment η Im1 (perturb S T a ε)) t =
      capital δ K0 (investment η Im1 S) t + (ε * projKat η δ T t) • a := by
  induction t with
  | zero => simp [capital, projKat, projK]
  | succ t ih =>
    change investment η Im1 (perturb S T a ε) t +
        (1 - δ) • capital δ K0 (investment η Im1 (perturb S T a ε)) t =
      (investment η Im1 S t + (1 - δ) • capital δ K0 (investment η Im1 S) t) +
        (ε * projKat η δ T (t + 1)) • a
    rw [ih, investment_perturb]
    have hw : projKat η δ T (t + 1) = projI η T t + (1 - δ) * projKat η δ T t := by
      unfold projKat projI
      by_cases h : T ≤ t
      · simp only [h, show T ≤ t + 1 by omega, ite_true]
        rw [show t + 1 - T = (t - T) + 1 by omega, projK]
      · by_cases h' : T = t + 1
        · subst h'
          simp [projK]
        · simp only [h, show ¬ T ≤ t + 1 by omega, ite_false, mul_zero, add_zero]
    rw [hw]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

omit 𝔼 in
/-- Woodford (2003), App. D.1, p. 688: "a monotonically decreasing function of `I_t − η I_{t−1}`"
— since `ψ(·; ξ)` is strictly convex, `ψ_s` is strictly increasing and `γ − ψ_s` strictly
decreasing, as `u_c` is in (1.23). -/
theorem gamma_sub_strictAnti {ψs : ℝ → ℝ} (hψ : StrictMono ψs) (γ : ℝ) :
    StrictAnti fun s => γ - ψs s :=
  fun _ _ h => by simp only; linarith [hψ h]

/-! ### (1.24)–(1.25): the Euler equation and the IS relation as exact derivatives -/

/-- Woodford (2003), §1.2, p. 333: the quasi-difference
`x̃_t ≡ (x_t − η x_{t−1}) − βη E_t(x_{t+1} − η x_t)`. -/
noncomputable def xTilde (β η : ℝ) (xm1 : Ω → ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (x t - η • lag xm1 x t) - (β * η) • 𝔼.E t (x (t + 1) - η • x t)

omit 𝔼 in
/-- Woodford (2003), p. 333: the lag of a difference is the difference of the lags. -/
theorem lag_sub (am1 bm1 : Ω → ℝ) (a b : ℕ → Ω → ℝ) (t : ℕ) :
    lag (am1 - bm1) (fun s => a s - b s) t = lag am1 a t - lag bm1 b t := by
  cases t <;> rfl

/-- Woodford (2003), p. 333: `x̃` is linear in the path. -/
theorem xTilde_sub (β η : ℝ) (am1 bm1 : Ω → ℝ) (a b : ℕ → Ω → ℝ) (t : ℕ) :
    xTilde 𝔼 β η (am1 - bm1) (fun s => a s - b s) t =
      xTilde 𝔼 β η am1 a t - xTilde 𝔼 β η bm1 b t := by
  unfold xTilde
  rw [lag_sub]
  have h : (a (t + 1) - b (t + 1)) - η • (a t - b t) =
      (a (t + 1) - η • a t) - (b (t + 1) - η • b t) := by
    rw [smul_sub]; abel
  rw [h, map_sub]
  funext ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), eq. (1.24), p. 333: the Euler equation
`λ_t = β E_t[λ_{t+1} (1 + i_t) P_t/P_{t+1}]` at date `t` (`Pr (t+1) = P_t/P_{t+1}`). -/
def EulerNL (β : ℝ) (lam onePlusI Pr : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  lam t = β • 𝔼.E t (lam (t + 1) * onePlusI t * Pr (t + 1))

/-- **Woodford (2003), eq. (1.24), p. 333, log-linearised (exact derivative).** Let a
one-parameter family of allocations satisfy (1.24) exactly for every `ε`, with
`1 + i_t = (1 + ī) e^{ε î_t}`, `P_t/P_{t+1} = e^{−ε π_{t+1}}`, `β(1 + ī) = 1`, and `λ_s(ε)` equal
to `λ̄ ≠ 0` at `ε = 0` with derivative `λ̄ λ̂_s` (`s = t, t + 1`). Then
`λ̂_t = E_t λ̂_{t+1} + î_t − E_t π_{t+1}`. Finite state space. -/
theorem euler_loglinear [Finite Ω] {β ibar lbar : ℝ} (hβi : β * (1 + ibar) = 1)
    (hl : lbar ≠ 0) {lamF : ℝ → ℕ → Ω → ℝ} {lamhat ihat π : ℕ → Ω → ℝ} {t : ℕ}
    (hE : ∀ ε, EulerNL 𝔼 β (lamF ε) (fun s ω => (1 + ibar) * Real.exp (ε * ihat s ω))
      (fun s ω => Real.exp (-(ε * π s ω))) t)
    (h0 : lamF 0 (t + 1) = fun _ => lbar)
    (hd : ∀ s ω, HasDerivAt (fun ε => lamF ε s ω) (lbar * lamhat s ω) 0)
    (hia : 𝔼.E t (ihat t) = ihat t) :
    lamhat t = 𝔼.E t (lamhat (t + 1)) + ihat t - 𝔼.E t (π (t + 1)) := by
  funext ω
  -- derivative of the right-hand side of (1.24)
  have hR : HasDerivAt (fun ε => (β • 𝔼.E t (fun ω' => lamF ε (t + 1) ω' *
      ((1 + ibar) * Real.exp (ε * ihat t ω')) * Real.exp (-(ε * π (t + 1) ω')))) ω)
      (β * 𝔼.E t (fun ω' => (1 + ibar) * (lbar * lamhat (t + 1) ω' + lbar * ihat t ω' -
        lbar * π (t + 1) ω')) ω) 0 := by
    simp only [Pi.smul_apply, smul_eq_mul]
    refine HasDerivAt.const_mul β (hasDerivAt_E 𝔼 (fun ω' => ?_) t ω)
    have h1 := hd (t + 1) ω'
    have h2 : HasDerivAt (fun ε : ℝ => (1 + ibar) * Real.exp (ε * ihat t ω'))
        ((1 + ibar) * (Real.exp (0 * ihat t ω') * ihat t ω')) 0 :=
      (((hasDerivAt_id (0 : ℝ)).mul_const (ihat t ω')).exp).const_mul (1 + ibar) |>.congr_deriv
        (by simp)
    have h3 : HasDerivAt (fun ε : ℝ => Real.exp (-(ε * π (t + 1) ω')))
        (Real.exp (-(0 * π (t + 1) ω')) * -π (t + 1) ω') 0 :=
      (((hasDerivAt_id (0 : ℝ)).mul_const (π (t + 1) ω')).neg.exp).congr_deriv (by simp)
    have h := (h1.mul h2).mul h3
    have hl0 : lamF 0 (t + 1) ω' = lbar := by rw [h0]
    convert h using 1
    simp only [Pi.mul_apply, hl0, zero_mul, neg_zero, Real.exp_zero]
    ring
  have hL := hd t ω
  have heq : (fun ε => lamF ε t ω) = fun ε => (β • 𝔼.E t (fun ω' => lamF ε (t + 1) ω' *
      ((1 + ibar) * Real.exp (ε * ihat t ω')) * Real.exp (-(ε * π (t + 1) ω')))) ω := by
    funext ε
    exact congrFun (hE ε) ω
  rw [heq] at hL
  have hu := hL.unique hR
  have hfun : (fun ω' => (1 + ibar) * (lbar * lamhat (t + 1) ω' + lbar * ihat t ω' -
      lbar * π (t + 1) ω')) = ((1 + ibar) * lbar) • (lamhat (t + 1) + ihat t - π (t + 1)) := by
    funext ω'
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [hfun, map_smul, map_sub, map_add, hia] at hu
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul] at hu
  simp only [Pi.add_apply, Pi.sub_apply]
  have hu' : lbar * lamhat t ω = (β * (1 + ibar)) * lbar * (𝔼.E t (lamhat (t + 1)) ω +
      ihat t ω - 𝔼.E t (π (t + 1)) ω) := by linear_combination hu
  rw [hβi, one_mul] at hu'
  exact mul_left_cancel₀ hl hu'

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Woodford (2003), eq. (1.23), p. 333: `λ_t` with the marginal utility `u_c(c; ξ)` written as
a function of habit-adjusted expenditure and a vector `ξ ∈ X` of taste shocks. -/
noncomputable def lamOf (β η : ℝ) (uc : ℝ → X → ℝ) (Cm1 : Ω → ℝ) (C : ℕ → Ω → ℝ)
    (ξ : ℕ → Ω → X) (t : ℕ) : Ω → ℝ :=
  (fun ω => uc (habitArg η Cm1 C t ω) (ξ t ω)) -
    (β * η) • 𝔼.E t (fun ω => uc (habitArg η Cm1 C (t + 1) ω) (ξ (t + 1) ω))

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- Woodford (2003), eq. (1.23), p. 333: `lamOf` is `habitLambda` with `u_c(·; ξ_t)`. -/
theorem lamOf_eq_habitLambda (β η : ℝ) (uc : ℝ → X → ℝ) (Cm1 : Ω → ℝ) (C : ℕ → Ω → ℝ)
    (ξ : ℕ → Ω → X) (t : ℕ) :
    lamOf 𝔼 β η uc Cm1 C ξ t = habitLambda 𝔼 β η (fun s ω c => uc c (ξ s ω)) Cm1 C t := rfl

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- Woodford (2003), p. 333: at the steady state (`C_t = C̄`, `ξ_t = ξ̄`) the marginal utility of
income is `λ̄ = (1 − βη) u_c((1 − η) C̄; ξ̄)`. -/
theorem lamOf_steady (β η Cbar : ℝ) (uc : ℝ → X → ℝ) (ξbar : X) (t : ℕ) :
    lamOf 𝔼 β η uc (fun _ => Cbar) (fun _ _ => Cbar) (fun _ _ => ξbar) t =
      fun _ => (1 - β * η) * uc ((1 - η) * Cbar) ξbar := by
  have hh : ∀ s, habitArg η (fun _ : Ω => Cbar) (fun _ _ => Cbar) s =
      fun _ => (1 - η) * Cbar := by
    intro s
    funext ω
    cases s <;> simp [habitArg, lag] <;> ring
  unfold lamOf
  simp only [hh, 𝔼.const]
  funext ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Woodford (2003), eq. (1.23), p. 333, linearised (exact derivative).** Along the family
`C_t = C̄(1 + ε ĉ_t)`, `ξ_t = ξ̄ + ε ξ̂_t`, with `u_c` differentiable at `((1 − η)C̄, ξ̄)` with
derivative `L`, `λ_t` has derivative
`U_h C̄ x̃_t(ĉ) + [z_t − βη E_t z_{t+1}]`, `U_h = L(1, 0)`, `z_t = L(0, ξ̂_t)`, where `x̃(ĉ)` is
the quasi-difference of `ĉ`. Finite state space. -/
theorem lamOf_hasDerivAt [Finite Ω] {β η Cbar : ℝ} {uc : ℝ → X → ℝ} {ξbar : X}
    {L : ℝ × X →L[ℝ] ℝ} (hU : HasFDerivAt (fun p : ℝ × X => uc p.1 p.2) L ((1 - η) * Cbar, ξbar))
    (chm1 : Ω → ℝ) (ch : ℕ → Ω → ℝ) (ξh : ℕ → Ω → X) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => lamOf 𝔼 β η uc (fun ω' => Cbar + ε * Cbar * chm1 ω')
      (fun s ω' => Cbar + ε * Cbar * ch s ω') (fun s ω' => ξbar + ε • ξh s ω') t ω)
      (L (1, 0) * Cbar * xTilde 𝔼 β η chm1 ch t ω +
        ((fun ω' => L (0, ξh t ω')) - (β * η) • 𝔼.E t (fun ω' => L (0, ξh (t + 1) ω'))) ω) 0 := by
  -- the habit argument along the family
  have hh : ∀ (ε : ℝ) s, habitArg η (fun ω' => Cbar + ε * Cbar * chm1 ω')
      (fun s ω' => Cbar + ε * Cbar * ch s ω') s =
      fun ω' => (1 - η) * Cbar + ε * (Cbar * (ch s ω' - η * lag chm1 ch s ω')) := by
    intro ε s
    funext ω'
    cases s <;> simp [habitArg, lag] <;> ring
  -- derivative of `ε ↦ u_c(h̄ + ε A, ξ̄ + ε v)`
  have hcurve : ∀ (A : ℝ) (v : X), HasDerivAt (fun ε : ℝ => uc ((1 - η) * Cbar + ε * A)
      (ξbar + ε • v)) (A * L (1, 0) + L (0, v)) 0 := by
    intro A v
    have h1 : HasDerivAt (fun ε : ℝ => (1 - η) * Cbar + ε * A) A 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const A).const_add ((1 - η) * Cbar)
    have h2 : HasDerivAt (fun ε : ℝ => ξbar + ε • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add ξbar
    have h := hU.comp_hasDerivAt_of_eq (0 : ℝ) (h1.prodMk h2) (by simp)
    have hL : L (A, v) = A * L (1, 0) + L (0, v) := by
      have : ((A, v) : ℝ × X) = A • ((1 : ℝ), (0 : X)) + ((0 : ℝ), v) := by
        ext <;> simp
      rw [this, map_add, map_smul, smul_eq_mul]
    rw [← hL]
    exact h
  have hfun : (fun ε => lamOf 𝔼 β η uc (fun ω' => Cbar + ε * Cbar * chm1 ω')
      (fun s ω' => Cbar + ε * Cbar * ch s ω') (fun s ω' => ξbar + ε • ξh s ω') t ω) =
      fun ε => uc ((1 - η) * Cbar + ε * (Cbar * (ch t ω - η * lag chm1 ch t ω)))
        (ξbar + ε • ξh t ω) - (β * η) * 𝔼.E t (fun ω' =>
          uc ((1 - η) * Cbar + ε * (Cbar * (ch (t + 1) ω' - η * lag chm1 ch (t + 1) ω')))
            (ξbar + ε • ξh (t + 1) ω')) ω := by
    funext ε
    unfold lamOf
    rw [hh, hh]
    rfl
  rw [hfun]
  have hA := hcurve (Cbar * (ch t ω - η * lag chm1 ch t ω)) (ξh t ω)
  have hB := (hasDerivAt_E 𝔼 (fun ω' => hcurve (Cbar * (ch (t + 1) ω' -
    η * lag chm1 ch (t + 1) ω')) (ξh (t + 1) ω')) t ω).const_mul (β * η)
  convert hA.sub hB using 1
  have hE1 : (fun ω' => Cbar * (ch (t + 1) ω' - η * lag chm1 ch (t + 1) ω') * L (1, 0) +
      L (0, ξh (t + 1) ω')) = (Cbar * L (1, 0)) • (ch (t + 1) - η • ch t) +
        fun ω' => L (0, ξh (t + 1) ω') := by
    funext ω'
    simp only [lag_succ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [hE1, map_add, map_smul]
  unfold xTilde
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), p. 333: with `σ ≡ −u_c/(C̄ u_cc)` (`u_cc = U_h`) and
`φ⁻¹ ≡ (1 − βη)σ`, the coefficient `U_h C̄` equals `−λ̄ φ`, `λ̄ = (1 − βη) u_c`: so
`λ̂_t = −φ x̃_t(ĉ) + (shock terms)`, and `φ > 0` when `σ > 0`, `βη < 1`. -/
theorem uhC_eq {β η Cbar ucbar Uh σ : ℝ} (hC : Cbar ≠ 0) (hU : Uh ≠ 0) (hu : ucbar ≠ 0)
    (hσ : σ = -ucbar / (Cbar * Uh)) (hβη : 1 - β * η ≠ 0) :
    Uh * Cbar = -((1 - β * η) * ucbar) * ((1 - β * η) * σ)⁻¹ := by
  rw [hσ]
  field_simp

/-- Woodford (2003), eq. (1.25), p. 333: the IS relation in `x̃`,
`x̃_t = E_t x̃_{t+1} − φ⁻¹(î_t − E_t π_{t+1} − r̂ⁿ_t)`, at every date. -/
def IS125 (vphi β η : ℝ) (xm1 : Ω → ℝ) (x i π rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, xTilde 𝔼 β η xm1 x t =
    𝔼.E t (xTilde 𝔼 β η xm1 x (t + 1)) - vphi⁻¹ • (i t - 𝔼.E t (π (t + 1)) - rn t)

/-- **Woodford (2003), eq. (1.25), pp. 333–334.** Suppose the log marginal utility of income is
`λ̂_t = −φ x̃_t(ĉ) + z_t` along the actual allocation and `λ̂ⁿ_t = −φ x̃_t(ĉⁿ) + z_t` along the
flexible-price allocation (the same taste-shock term `z`), and the natural rate is defined by
`λ̂ⁿ_t = E_t λ̂ⁿ_{t+1} + r̂ⁿ_t`. Then the log-linear Euler equation
`λ̂_t = E_t λ̂_{t+1} + î_t − E_t π_{t+1}` holds iff the output gap `x = ĉ − ĉⁿ` satisfies (1.25). -/
theorem euler_iff_IS {vphi β η : ℝ} (hφ : vphi ≠ 0) {lamhat lamhatN c cN z i π rn : ℕ → Ω → ℝ}
    {cm1 cNm1 : Ω → ℝ} (hl : ∀ t, lamhat t = -vphi • xTilde 𝔼 β η cm1 c t + z t)
    (hn : ∀ t, lamhatN t = -vphi • xTilde 𝔼 β η cNm1 cN t + z t)
    (hNat : ∀ t, lamhatN t = 𝔼.E t (lamhatN (t + 1)) + rn t) :
    (∀ t, lamhat t = 𝔼.E t (lamhat (t + 1)) + i t - 𝔼.E t (π (t + 1))) ↔
      IS125 𝔼 vphi β η (cm1 - cNm1) (fun s => c s - cN s) i π rn := by
  unfold IS125
  simp only [xTilde_sub, map_sub]
  refine forall_congr' fun t => ?_
  have hN := hNat t
  rw [hn t, hn (t + 1), map_add, map_smul] at hN
  rw [hl t, hl (t + 1), map_add, map_smul]
  constructor
  · intro H
    funext ω
    have a := congrFun H ω
    have b := congrFun hN ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b ⊢
    field_simp
    linear_combination b - a
  · intro H
    funext ω
    have a := congrFun H ω
    have b := congrFun hN ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b ⊢
    field_simp at a
    linear_combination b - a

/-- **Woodford (2003), eqs. (1.23)–(1.25), pp. 333–334: the IS relation (1.25) as an exact
derivative of the nonlinear model.** Let the actual allocation `C_t = C̄(1 + ε ĉ_t)` satisfy
the Euler equation (1.24) exactly for every `ε`, with `1 + i_t = (1 + ī)e^{ε î_t}`,
`P_t/P_{t+1} = e^{−ε π_{t+1}}`, and the flexible-price allocation `C̄(1 + ε ĉⁿ_t)` satisfy it with
the natural real rate `1 + rⁿ_t = (1 + ī)e^{ε r̂ⁿ_t}` and zero inflation, both with taste shocks
`ξ̄ + ε ξ̂_t` and `λ_t` given by (1.23). With `β(1 + ī) = 1`, `σ ≡ −u_c/(C̄ u_cc)` and
`φ⁻¹ ≡ (1 − βη)σ`, the output gap `x = ĉ − ĉⁿ` satisfies (1.25). Finite state space. -/
theorem IS125_of_nonlinear [Finite Ω] {β η ibar Cbar σ : ℝ} {uc : ℝ → X → ℝ} {ξbar : X}
    {L : ℝ × X →L[ℝ] ℝ} (hU : HasFDerivAt (fun p : ℝ × X => uc p.1 p.2) L ((1 - η) * Cbar, ξbar))
    (hβi : β * (1 + ibar) = 1) (hβη : 1 - β * η ≠ 0) (hC : Cbar ≠ 0) (hUh : L (1, 0) ≠ 0)
    (huc : uc ((1 - η) * Cbar) ξbar ≠ 0) (hσ : σ = -uc ((1 - η) * Cbar) ξbar / (Cbar * L (1, 0)))
    (chm1 cnm1 : Ω → ℝ) (ch cn : ℕ → Ω → ℝ) (ξh : ℕ → Ω → X) (ihat π rn : ℕ → Ω → ℝ)
    (hia : 𝔼.Adapted ihat) (hra : 𝔼.Adapted rn)
    (hE : ∀ ε t, EulerNL 𝔼 β (lamOf 𝔼 β η uc (fun ω' => Cbar + ε * Cbar * chm1 ω')
      (fun s ω' => Cbar + ε * Cbar * ch s ω') (fun s ω' => ξbar + ε • ξh s ω'))
      (fun s ω => (1 + ibar) * Real.exp (ε * ihat s ω)) (fun s ω => Real.exp (-(ε * π s ω))) t)
    (hEn : ∀ ε t, EulerNL 𝔼 β (lamOf 𝔼 β η uc (fun ω' => Cbar + ε * Cbar * cnm1 ω')
      (fun s ω' => Cbar + ε * Cbar * cn s ω') (fun s ω' => ξbar + ε • ξh s ω'))
      (fun s ω => (1 + ibar) * Real.exp (ε * rn s ω)) (fun _ _ => Real.exp (-(ε * 0))) t) :
    IS125 𝔼 ((1 - β * η) * σ)⁻¹ β η (chm1 - cnm1) (fun s => ch s - cn s) ihat π rn := by
  set lbar := (1 - β * η) * uc ((1 - η) * Cbar) ξbar with hlbar
  have hl0 : lbar ≠ 0 := mul_ne_zero hβη huc
  set z : ℕ → Ω → ℝ := fun t => (lbar⁻¹) • ((fun ω' => L (0, ξh t ω')) -
    (β * η) • 𝔼.E t (fun ω' => L (0, ξh (t + 1) ω'))) with hz
  set lh : (Ω → ℝ) → (ℕ → Ω → ℝ) → ℕ → Ω → ℝ := fun am1 a t =>
    -((1 - β * η) * σ)⁻¹ • xTilde 𝔼 β η am1 a t + z t with hlh
  have hkey := uhC_eq hC hUh huc hσ hβη
  have hder : ∀ (am1 : Ω → ℝ) (a : ℕ → Ω → ℝ) t ω, HasDerivAt (fun ε => lamOf 𝔼 β η uc
      (fun ω' => Cbar + ε * Cbar * am1 ω') (fun s ω' => Cbar + ε * Cbar * a s ω')
      (fun s ω' => ξbar + ε • ξh s ω') t ω) (lbar * lh am1 a t ω) 0 := by
    intro am1 a t ω
    convert lamOf_hasDerivAt 𝔼 hU am1 a ξh t ω using 1
    simp only [hlh, hz, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hkey]
    field_simp
    ring
  have hst : ∀ (am1 : Ω → ℝ) (a : ℕ → Ω → ℝ) t, lamOf 𝔼 β η uc
      (fun ω' => Cbar + 0 * Cbar * am1 ω') (fun s ω' => Cbar + 0 * Cbar * a s ω')
      (fun s ω' => ξbar + (0 : ℝ) • ξh s ω') t = fun _ => lbar := by
    intro am1 a t
    simp only [zero_mul, add_zero, zero_smul]
    exact lamOf_steady 𝔼 β η Cbar uc ξbar t
  have hEul : ∀ t, lh chm1 ch t = 𝔼.E t (lh chm1 ch (t + 1)) + ihat t - 𝔼.E t (π (t + 1)) :=
    fun t => euler_loglinear 𝔼 hβi hl0 (fun ε => hE ε t) (hst chm1 ch (t + 1))
      (hder chm1 ch) (hia t)
  have hNat : ∀ t, lh cnm1 cn t = 𝔼.E t (lh cnm1 cn (t + 1)) + rn t := by
    intro t
    have h := euler_loglinear 𝔼 (π := fun _ _ => 0) hβi hl0 (fun ε => hEn ε t)
      (hst cnm1 cn (t + 1)) (hder cnm1 cn) (hra t)
    rw [h, show (fun _ : Ω => (0 : ℝ)) = 0 from rfl, map_zero, sub_zero]
  exact (euler_iff_IS 𝔼 (inv_ne_zero (mul_ne_zero hβη (by
    rw [hσ]; exact div_ne_zero (neg_ne_zero.mpr huc) (mul_ne_zero hC hUh))))
    (fun t => rfl) (fun t => rfl) hNat).mp hEul

/-! ### The forward solution of (1.25), p. 334 -/

/-- Woodford (2003), p. 334: the weights `ξ_k = φ⁻¹ (1 − (βη)^{k+1})/(1 − βη)` of the forward
solution (the survey notes that this `ξ_k` clashes with `ξ_p` and the shocks `ξ_t`). -/
noncomputable def xiK (vphi β η : ℝ) (k : ℕ) : ℝ :=
  vphi⁻¹ * (1 - (β * η) ^ (k + 1)) / (1 - β * η)

omit 𝔼 in
/-- Woodford (2003), p. 334: `ξ_k > 0` for each `k ≥ 0` (`φ > 0`, `0 ≤ βη < 1`). -/
theorem xiK_pos {vphi β η : ℝ} (hφ : 0 < vphi) (h0 : 0 ≤ β * η) (h1 : β * η < 1) (k : ℕ) :
    0 < xiK vphi β η k := by
  unfold xiK
  have : (β * η) ^ (k + 1) < 1 := pow_lt_one₀ h0 h1 (Nat.succ_ne_zero k)
  have := inv_pos.mpr hφ
  apply div_pos _ (by linarith)
  nlinarith

/-- Woodford (2003), p. 333: `x̃` of a process bounded by `M` (with `|x_{−1}| ≤ M`) is
bounded. -/
theorem xTilde_bounded {β η M : ℝ} {xm1 : Ω → ℝ} {x : ℕ → Ω → ℝ} (hm : ∀ ω, |xm1 ω| ≤ M)
    (hx : ∀ t ω, |x t ω| ≤ M) (t : ℕ) (ω : Ω) :
    |xTilde 𝔼 β η xm1 x t ω| ≤ (1 + |η|) * M + |β * η| * ((1 + |η|) * M) := by
  have hl : ∀ s ω, |lag xm1 x s ω| ≤ M := by
    intro s ω
    cases s
    · exact hm ω
    · exact hx _ ω
  have hb : ∀ ω, |(x (t + 1) - η • x t) ω| ≤ (1 + |η|) * M := by
    intro ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    calc |x (t + 1) ω - η * x t ω| ≤ |x (t + 1) ω| + |η| * |x t ω| := by
          rw [← abs_mul]; exact abs_sub _ _
      _ ≤ M + |η| * M := by
          gcongr
          · exact hx _ ω
          · exact hx t ω
      _ = (1 + |η|) * M := by ring
  have hE := 𝔼.abs_E_le hb t ω
  unfold xTilde
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  calc |x t ω - η * lag xm1 x t ω - β * η * 𝔼.E t (x (t + 1) - η • x t) ω|
      ≤ |x t ω| + |η| * |lag xm1 x t ω| + |β * η| * |𝔼.E t (x (t + 1) - η • x t) ω| := by
        rw [← abs_mul, ← abs_mul]
        exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ M + |η| * M + |β * η| * ((1 + |η|) * M) := by
        gcongr
        · exact hx t ω
        · exact hl t ω
    _ = (1 + |η|) * M + |β * η| * ((1 + |η|) * M) := by ring

/-- Woodford (2003), p. 333: `x̃` of an adapted process (with `x_{−1}` known at 0) is adapted. -/
theorem xTilde_adapted {β η : ℝ} {xm1 : Ω → ℝ} {x : ℕ → Ω → ℝ} (hm : 𝔼.E 0 xm1 = xm1)
    (hx : 𝔼.Adapted x) : 𝔼.Adapted (xTilde 𝔼 β η xm1 x) := by
  intro t
  unfold xTilde
  rw [map_sub, map_sub, map_smul, map_smul, hx t, lag_known 𝔼 hm hx t, 𝔼.E_E_self]

/-- **Woodford (2003), p. 334, first equality.** For a bounded adapted `x` (and `x_{−1}` known
at 0), `x_t − η x_{t−1} = ∑_{j ≥ 0} (βη)ʲ E_t x̃_{t+j}` (a genuine, absolutely convergent
infinite sum), for `0 ≤ βη < 1`. -/
theorem quasiDiff_eq_forwardSeries {β η M : ℝ} (h0 : 0 ≤ β * η) (h1 : β * η < 1)
    {xm1 : Ω → ℝ} {x : ℕ → Ω → ℝ} (hm0 : 𝔼.E 0 xm1 = xm1) (hx : 𝔼.Adapted x)
    (hm : ∀ ω, |xm1 ω| ≤ M) (hxb : ∀ t ω, |x t ω| ≤ M) :
    (fun t => x t - η • lag xm1 x t) = 𝔼.forwardSeries (β * η) (xTilde 𝔼 β η xm1 x) := by
  refine 𝔼.eq_forwardSeries h0 h1 (xTilde_bounded 𝔼 hm hxb) (xTilde_adapted 𝔼 hm0 hx)
    (fun t => ?_) ⟨M + |η| * M, fun t ω => ?_⟩
  · unfold xTilde
    rw [lag_succ]
    abel
  · have hl : |lag xm1 x t ω| ≤ M := by
      cases t
      · exact hm ω
      · exact hxb _ ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    calc |x t ω - η * lag xm1 x t ω| ≤ |x t ω| + |η| * |lag xm1 x t ω| := by
          rw [← abs_mul]; exact abs_sub _ _
      _ ≤ M + |η| * M := by gcongr; exact hxb t ω

/-- Woodford (2003), p. 334: the long-run forecast of `x̃`: if `E_t x_{t+T} → x_∞` then
`E_t x̃_{t+T} → x̃_∞ = (1 − η)(1 − βη) x_∞`. -/
theorem xTilde_longRun {β η xinf : ℝ} {xm1 : Ω → ℝ} {x : ℕ → Ω → ℝ}
    (hlim : ∀ t ω, Tendsto (fun T => 𝔼.E t (x (t + T)) ω) atTop (𝓝 xinf)) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => 𝔼.E t (xTilde 𝔼 β η xm1 x (t + T)) ω) atTop
      (𝓝 ((1 - η) * (1 - β * η) * xinf)) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have hk : ∀ k, Tendsto (fun T => 𝔼.E t (x (t + (T + k))) ω) atTop (𝓝 xinf) := fun k =>
    (hlim t ω).comp (tendsto_add_atTop_nat k)
  have heq : ∀ T, 𝔼.E t (xTilde 𝔼 β η xm1 x (t + (T + 1))) ω =
      (1 + β * η * η) * 𝔼.E t (x (t + (T + 1))) ω - η * 𝔼.E t (x (t + (T + 0))) ω -
        β * η * 𝔼.E t (x (t + (T + 2))) ω := by
    intro T
    unfold xTilde
    rw [show t + (T + 1) = (t + T) + 1 by omega, lag_succ]
    simp only [map_sub, map_smul]
    rw [𝔼.tower (show t ≤ t + T + 1 by omega), 𝔼.tower (show t ≤ t + T + 1 by omega)]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [show t + T + 1 + 1 = t + (T + 2) by omega, show t + T + 1 = t + (T + 1) by omega,
      show t + T = t + (T + 0) by omega]
    ring
  simp only [heq]
  have := (((hk 1).const_mul (1 + β * η * η)).sub ((hk 0).const_mul η)).sub
    ((hk 2).const_mul (β * η))
  convert this using 2
  ring

/-- Woodford (2003), p. 334: iterating (1.25) (in the general form
`x̃_t = E_t x̃_{t+1} − φ⁻¹ q_t`): `x̃_t = E_t x̃_{t+N} − φ⁻¹ ∑_{k<N} E_t q_{t+k}`. -/
theorem xTilde_iterate {vphi β η : ℝ} {xm1 : Ω → ℝ} {x q : ℕ → Ω → ℝ}
    (hxa : 𝔼.Adapted (xTilde 𝔼 β η xm1 x))
    (hIS : ∀ t, xTilde 𝔼 β η xm1 x t = 𝔼.E t (xTilde 𝔼 β η xm1 x (t + 1)) - vphi⁻¹ • q t)
    (t N : ℕ) :
    xTilde 𝔼 β η xm1 x t = 𝔼.E t (xTilde 𝔼 β η xm1 x (t + N)) -
      vphi⁻¹ • ∑ k ∈ Finset.range N, 𝔼.E t (q (t + k)) := by
  induction N with
  | zero => simp [hxa t]
  | succ N ih =>
    rw [ih, Finset.sum_range_succ, hIS (t + N), map_sub, map_smul,
      𝔼.tower (Nat.le_add_right t N), ← add_assoc, smul_add]
    abel

/-- **Woodford (2003), p. 334: `x̃_t = x̃_∞ − φ⁻¹ ∑_{k ≥ 0} E_t q_{t+k}`.** The series of expected
real-rate gaps converges (as a limit of partial sums: in general only conditionally, so it is
stated with `Tendsto`, not `tsum`) to `φ (x̃_∞ − x̃_t)`. -/
theorem sum_q_tendsto {vphi β η xinf : ℝ} (hφ : vphi ≠ 0) {xm1 : Ω → ℝ} {x q : ℕ → Ω → ℝ}
    (hxa : 𝔼.Adapted (xTilde 𝔼 β η xm1 x))
    (hIS : ∀ t, xTilde 𝔼 β η xm1 x t = 𝔼.E t (xTilde 𝔼 β η xm1 x (t + 1)) - vphi⁻¹ • q t)
    (hlim : ∀ t ω, Tendsto (fun T => 𝔼.E t (x (t + T)) ω) atTop (𝓝 xinf)) (t : ℕ) (ω : Ω) :
    Tendsto (fun N => ∑ k ∈ Finset.range N, 𝔼.E t (q (t + k)) ω) atTop
      (𝓝 (vphi * ((1 - η) * (1 - β * η) * xinf - xTilde 𝔼 β η xm1 x t ω))) := by
  have h := ((xTilde_longRun 𝔼 (β := β) (η := η) (xm1 := xm1) hlim t ω).sub_const
    (xTilde 𝔼 β η xm1 x t ω)).const_mul vphi
  refine h.congr fun N => ?_
  have e := congrFun (xTilde_iterate 𝔼 hxa hIS t N) ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at e
  rw [e, sub_sub_cancel, ← mul_assoc, mul_inv_cancel₀ hφ, one_mul]

/-- **Woodford (2003), p. 334: the forward solution of (1.25).** For a bounded adapted output
gap with `E_t x_{t+T} → x_∞` solving `x̃_t = E_t x̃_{t+1} − φ⁻¹ q_t` (`q_t = î_t − E_t π_{t+1} −
r̂ⁿ_t`, any bounded `q`), `x_t − η x_{t−1} = (1 − η) x_∞ − ∑_{k ≥ 0} ξ_k E_t q_{t+k}` with
`ξ_k = φ⁻¹(1 − (βη)^{k+1})/(1 − βη)`. The double sum `∑_j (βη)ʲ ∑_k E_t q_{t+j+k}` is
rearranged by summation by parts; the resulting series converges as a limit of partial sums
(`Tendsto`), in general not absolutely. Any `ExpectationSystem`. -/
theorem forward_solution {vphi β η xinf M Mq : ℝ} (hφ : vphi ≠ 0) (h0 : 0 ≤ β * η)
    (h1 : β * η < 1) {xm1 : Ω → ℝ} {x q : ℕ → Ω → ℝ} (hm0 : 𝔼.E 0 xm1 = xm1)
    (hx : 𝔼.Adapted x) (hm : ∀ ω, |xm1 ω| ≤ M) (hxb : ∀ t ω, |x t ω| ≤ M)
    (hq : ∀ t ω, |q t ω| ≤ Mq)
    (hIS : ∀ t, xTilde 𝔼 β η xm1 x t = 𝔼.E t (xTilde 𝔼 β η xm1 x (t + 1)) - vphi⁻¹ • q t)
    (hlim : ∀ t ω, Tendsto (fun T => 𝔼.E t (x (t + T)) ω) atTop (𝓝 xinf)) (t : ℕ) (ω : Ω) :
    Tendsto (fun N => ∑ k ∈ Finset.range N, xiK vphi β η k * 𝔼.E t (q (t + k)) ω) atTop
      (𝓝 ((1 - η) * xinf - (x t ω - η * lag xm1 x t ω))) := by
  set a := β * η with ha
  have hxa := xTilde_adapted 𝔼 (β := β) (η := η) hm0 hx
  set X : ℕ → ℝ := fun j => 𝔼.E t (xTilde 𝔼 β η xm1 x (t + j)) ω with hX
  set b : ℕ → ℝ := fun k => 𝔼.E t (q (t + k)) ω with hb
  set K := (1 + |η|) * M + |a| * ((1 + |η|) * M) with hK
  have hXb : ∀ j, |X j| ≤ K := fun j =>
    𝔼.abs_E_le (fun ω' => xTilde_bounded 𝔼 hm hxb (t + j) ω') t ω
  -- `E_t q_{t+k} = φ (X_{k+1} − X_k)`
  have hbX : ∀ k, b k = vphi * (X (k + 1) - X k) := by
    intro k
    have e := congrArg (𝔼.E t) (hIS (t + k))
    rw [map_sub, map_smul, 𝔼.tower (Nat.le_add_right t k)] at e
    have e' := congrFun e ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e'
    simp only [hb, hX, show t + (k + 1) = t + k + 1 by omega]
    rw [e', sub_sub_cancel, ← mul_assoc, mul_inv_cancel₀ hφ, one_mul]
  have hinc : ∀ j, |X (j + 1) - X j| ≤ K + K := fun j =>
    (abs_sub _ _).trans (add_le_add (hXb _) (hXb _))
  have haa : |a| < 1 := by rw [abs_of_nonneg h0]; exact h1
  -- the geometric part
  have hsA : Summable fun k => a ^ k * b k := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h0 h1).mul_right Mq)
      (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hq (t + k)) t ω) (pow_nonneg h0 k)
  have hS := sum_q_tendsto 𝔼 hφ hxa hIS hlim t ω
  have hpart : ∀ N, ∑ k ∈ Finset.range N, xiK vphi β η k * b k =
      vphi⁻¹ / (1 - a) * (∑ k ∈ Finset.range N, b k - a * ∑ k ∈ Finset.range N, a ^ k * b k) := by
    intro N
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [xiK, ← ha, pow_succ]
    ring
  have hlim2 := (hS.sub (hsA.hasSum.tendsto_sum_nat.const_mul a)).const_mul (vphi⁻¹ / (1 - a))
  -- identify the limit with summation by parts
  have hy := congrFun (congrFun (quasiDiff_eq_forwardSeries 𝔼 h0 h1 hm0 hx hm hxb) t) ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hy
  change _ = ∑' k, a ^ k * X k at hy
  have habel := ForwardSolution.abel_tsum haa hinc
  have hA : ∑' k, a ^ k * b k = vphi * ∑' j, a ^ j * (X (j + 1) - X j) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by rw [hbX]; ring
  have hA2 : ∑' j, a ^ (j + 1) * (X (j + 1) - X j) = a * ∑' j, a ^ j * (X (j + 1) - X j) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by ring
  have hX0 : X 0 = xTilde 𝔼 β η xm1 x t ω := by
    simp only [hX, add_zero]
    exact congrFun (hxa t) ω
  have h1a : 1 - a ≠ 0 := by linarith
  have hval : vphi⁻¹ / (1 - a) * (vphi * ((1 - η) * (1 - a) * xinf - xTilde 𝔼 β η xm1 x t ω) -
      a * ∑' k, a ^ k * b k) = (1 - η) * xinf - (x t ω - η * lag xm1 x t ω) := by
    rw [hA, hy]
    rw [hA2, hX0] at habel
    field_simp
    linear_combination habel
  rw [hval] at hlim2
  exact hlim2.congr fun N => (hpart N).symm

/-- **Woodford (2003), p. 334: transitory real-rate gaps give an AR(1) output gap with
coefficient `η`.** If the real-rate gap is purely transitory (`E_t q_{t+k} = 0` for `k ≥ 1`),
every bounded solution of (1.25) with long-run expectation `x_∞` satisfies
`x_t = η x_{t−1} + (1 − η) x_∞ − φ⁻¹ q_t`. -/
theorem transitory_ar1 {vphi β η xinf M Mq : ℝ} (hφ : vphi ≠ 0) (h0 : 0 ≤ β * η)
    (h1 : β * η < 1) {xm1 : Ω → ℝ} {x q : ℕ → Ω → ℝ} (hm0 : 𝔼.E 0 xm1 = xm1)
    (hx : 𝔼.Adapted x) (hm : ∀ ω, |xm1 ω| ≤ M) (hxb : ∀ t ω, |x t ω| ≤ M)
    (hq : ∀ t ω, |q t ω| ≤ Mq) (hqa : 𝔼.Adapted q)
    (htr : ∀ t k, 1 ≤ k → 𝔼.E t (q (t + k)) = 0)
    (hIS : ∀ t, xTilde 𝔼 β η xm1 x t = 𝔼.E t (xTilde 𝔼 β η xm1 x (t + 1)) - vphi⁻¹ • q t)
    (hlim : ∀ t ω, Tendsto (fun T => 𝔼.E t (x (t + T)) ω) atTop (𝓝 xinf)) (t : ℕ) :
    x t = η • lag xm1 x t + (fun _ => (1 - η) * xinf) - vphi⁻¹ • q t := by
  funext ω
  have hF := forward_solution 𝔼 hφ h0 h1 hm0 hx hm hxb hq hIS hlim t ω
  have hc : ∀ N, 1 ≤ N → ∑ k ∈ Finset.range N, xiK vphi β η k * 𝔼.E t (q (t + k)) ω =
      vphi⁻¹ * q t ω := by
    intro N hN
    induction N with
    | zero => omega
    | succ N ih =>
      rw [Finset.sum_range_succ]
      rcases Nat.eq_zero_or_pos N with h | h
      · subst h
        have h1' : 1 - β * η ≠ 0 := by linarith
        simp only [Finset.range_zero, Finset.sum_empty, zero_add, xiK, add_zero, hqa t]
        field_simp
      · rw [ih h, htr t N h]
        simp
  have hlim' : Tendsto (fun N => ∑ k ∈ Finset.range N, xiK vphi β η k * 𝔼.E t (q (t + k)) ω)
      atTop (𝓝 (vphi⁻¹ * q t ω)) :=
    tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨1, fun N hN => (hc N hN).symm⟩)
  have := tendsto_nhds_unique hF hlim'
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linarith

/-- Woodford (2003), p. 334 (the converse of `transitory_ar1`): with purely transitory
real-rate gaps (`E_t q_{t+1} = 0`), the AR(1) process
`x_t = η x_{t−1} + (1 − η) x_∞ − φ⁻¹ q_t` solves (1.25). -/
theorem ar1_solves_IS {vphi β η xinf : ℝ} {xm1 : Ω → ℝ} {x q : ℕ → Ω → ℝ}
    (htr : ∀ t, 𝔼.E t (q (t + 1)) = 0)
    (hx : ∀ t, x t = η • lag xm1 x t + (fun _ => (1 - η) * xinf) - vphi⁻¹ • q t) (t : ℕ) :
    xTilde 𝔼 β η xm1 x t = 𝔼.E t (xTilde 𝔼 β η xm1 x (t + 1)) - vphi⁻¹ • q t := by
  have hy : ∀ s, x (s + 1) - η • x s = (fun _ => (1 - η) * xinf) - vphi⁻¹ • q (s + 1) := by
    intro s
    rw [hx (s + 1), lag_succ]
    abel
  have hy0 : ∀ s, x s - η • lag xm1 x s = (fun _ => (1 - η) * xinf) - vphi⁻¹ • q s := by
    intro s
    rw [hx s]
    abel
  have hE1 : ∀ s, 𝔼.E s (x (s + 1) - η • x s) = fun _ => (1 - η) * xinf := by
    intro s
    rw [hy s, map_sub, map_smul, 𝔼.const, htr s, smul_zero, sub_zero]
  have hxt : ∀ s, xTilde 𝔼 β η xm1 x s =
      (fun _ => (1 - η) * (1 - β * η) * xinf) - vphi⁻¹ • q s := by
    intro s
    unfold xTilde
    rw [hy0 s, hE1 s]
    funext ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hxt t, hxt (t + 1), map_sub, map_smul, 𝔼.const, htr t, smul_zero, sub_zero]

omit 𝔼 in
/-- Woodford (2003), p. 334: `∑_k ξ_k ρᵏ = φ⁻¹/[(1 − ρ)(1 − βηρ)]` for `|ρ| < 1`. -/
theorem hasSum_xiK_geom {vphi β η ρ : ℝ} (h0 : 0 ≤ β * η) (h1 : β * η < 1) (hρ : |ρ| < 1) :
    HasSum (fun k => xiK vphi β η k * ρ ^ k) (vphi⁻¹ / ((1 - ρ) * (1 - β * η * ρ))) := by
  have hab : |β * η * ρ| < 1 := by
    rw [abs_mul, abs_of_nonneg h0]
    calc β * η * |ρ| ≤ 1 * |ρ| := by gcongr
      _ < 1 := by linarith
  have hA := hasSum_geometric_of_abs_lt_one hρ
  have hB := hasSum_geometric_of_abs_lt_one hab
  have h := (hA.sub (hB.mul_left (β * η))).mul_left (vphi⁻¹ / (1 - β * η))
  have h1a : 1 - β * η ≠ 0 := by linarith
  have h1r : 1 - ρ ≠ 0 := by
    intro h; have : ρ = 1 := by linarith
    rw [this, abs_one] at hρ; exact lt_irrefl _ hρ
  have h1b : 1 - β * η * ρ ≠ 0 := by
    intro h; have : β * η * ρ = 1 := by linarith
    rw [this, abs_one] at hab; exact lt_irrefl _ hab
  have hkey : (1 - ρ)⁻¹ - β * η * (1 - β * η * ρ)⁻¹ =
      (1 - β * η) / ((1 - ρ) * (1 - β * η * ρ)) := by
    rw [eq_div_iff (mul_ne_zero h1r h1b)]
    have e1 : (1 - ρ)⁻¹ * (1 - ρ) = 1 := inv_mul_cancel₀ h1r
    have e2 : (1 - β * η * ρ)⁻¹ * (1 - β * η * ρ) = 1 := inv_mul_cancel₀ h1b
    linear_combination (1 - β * η * ρ) * e1 - β * η * (1 - ρ) * e2
  convert h using 1
  · funext k
    simp only [xiK, mul_pow, pow_succ]
    field_simp
  · rw [hkey]
    field_simp

/-- **Woodford (2003), p. 334: AR(1) real-rate gaps.** If `q` is an AR(1) process with
`|ρ| < 1` (`E_t q_{t+k} = ρᵏ q_t`), every bounded solution of (1.25) with long-run expectation
`x_∞` satisfies `x_t − η x_{t−1} = (1 − η) x_∞ − φ⁻¹/[(1 − ρ)(1 − βηρ)] q_t`. -/
theorem ar1_gap_response {vphi β η xinf ρ M Mq : ℝ} (hφ : vphi ≠ 0) (h0 : 0 ≤ β * η)
    (h1 : β * η < 1) (hρ : |ρ| < 1) {xm1 : Ω → ℝ} {x q : ℕ → Ω → ℝ}
    (hm0 : 𝔼.E 0 xm1 = xm1) (hx : 𝔼.Adapted x) (hm : ∀ ω, |xm1 ω| ≤ M)
    (hxb : ∀ t ω, |x t ω| ≤ M) (hq : ∀ t ω, |q t ω| ≤ Mq) (hqa : 𝔼.IsAR1 ρ q)
    (hIS : ∀ t, xTilde 𝔼 β η xm1 x t = 𝔼.E t (xTilde 𝔼 β η xm1 x (t + 1)) - vphi⁻¹ • q t)
    (hlim : ∀ t ω, Tendsto (fun T => 𝔼.E t (x (t + T)) ω) atTop (𝓝 xinf)) (t : ℕ) :
    x t - η • lag xm1 x t =
      (fun _ => (1 - η) * xinf) - (vphi⁻¹ / ((1 - ρ) * (1 - β * η * ρ))) • q t := by
  funext ω
  have hF := forward_solution 𝔼 hφ h0 h1 hm0 hx hm hxb hq hIS hlim t ω
  have hG := ((hasSum_xiK_geom (vphi := vphi) h0 h1 hρ).mul_right (q t ω)).tendsto_sum_nat
  have hfun : (fun N => ∑ k ∈ Finset.range N, xiK vphi β η k * ρ ^ k * q t ω) =
      fun N => ∑ k ∈ Finset.range N, xiK vphi β η k * 𝔼.E t (q (t + k)) ω := by
    funext N
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [𝔼.ar1_iterate hqa t k, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun] at hG
  have := tendsto_nhds_unique hF hG
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linarith

/-- Woodford (2003), p. 334: with AR(1) real-rate gaps the output gap is AR(2):
`x_{t+2} = (η + ρ) x_{t+1} − ηρ x_t + (1 − η)(1 − ρ) x_∞ − c (q_{t+2} − ρ q_{t+1})`,
`c = φ⁻¹/[(1 − ρ)(1 − βηρ)]` (`q_{t+2} − ρ q_{t+1}` is the innovation of the AR(1) process). -/
theorem ar2_output_gap {η ρ xinf c : ℝ} {xm1 : Ω → ℝ} {x q : ℕ → Ω → ℝ}
    (h : ∀ t, x t - η • lag xm1 x t = (fun _ => (1 - η) * xinf) - c • q t) (t : ℕ) :
    x (t + 2) = (η + ρ) • x (t + 1) - (η * ρ) • x t + (fun _ => (1 - η) * (1 - ρ) * xinf) -
      c • (q (t + 2) - ρ • q (t + 1)) := by
  have h2 := h (t + 2)
  have h1 := h (t + 1)
  rw [lag_succ] at h1 h2
  funext ω
  have a := congrFun h2 ω
  have b := congrFun h1 ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b ⊢
  linear_combination a - ρ * b

/-! ### The aggregate-supply relation (1.26) and its alternative form (1.27)–(1.29) -/

/-- Woodford (2003), Ch. 3 (eq. (4.9) there) as used on p. 334: the Calvo AS relation before the
marginal utility of income is substituted out, `π_t = ξ_p[ω x_t − (λ̂_t − λ̂ⁿ_t)] + β E_t π_{t+1}`,
where `λ̂ − λ̂ⁿ` (`lamgap`) is the gap in the log marginal utility of real income, which raises
real wage demands and hence real marginal cost. Taken here as the Ch. 3 relation (not
re-derived). -/
def ASch3 (ξp ω β : ℝ) (lamgap x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π t = ξp • (ω • x t - lamgap t) + β • 𝔼.E t (π (t + 1))

/-- Woodford (2003), eq. (1.26), p. 334: `π_t = ξ_p[ω x_t + φ x̃_t] + β E_t π_{t+1}`. -/
def AS126 (ξp ω vphi β η : ℝ) (xm1 : Ω → ℝ) (x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π t = ξp • (ω • x t + vphi • xTilde 𝔼 β η xm1 x t) + β • 𝔼.E t (π (t + 1))

/-- Woodford (2003), eq. (1.27), p. 335:
`π_t = κ[(x_t − δ x_{t−1}) − βδ E_t(x_{t+1} − δ x_t)] + β E_t π_{t+1}`. -/
def AS127 (κ δ β : ℝ) (xm1 : Ω → ℝ) (x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π t = κ • xTilde 𝔼 β δ xm1 x t + β • 𝔼.E t (π (t + 1))

/-- **Woodford (2003), eq. (1.26), p. 334 (conditional on the Ch. 3 AS relation).** With
habits the gap in the log marginal utility of income is `λ̂_t − λ̂ⁿ_t = −φ x̃_t` (see
`euler_iff_IS`), so the Ch. 3 relation becomes (1.26). -/
theorem AS126_iff_ASch3 {ξp ω vphi β η : ℝ} {xm1 : Ω → ℝ} {lamgap x π : ℕ → Ω → ℝ}
    (hl : ∀ t, lamgap t = -vphi • xTilde 𝔼 β η xm1 x t) :
    ASch3 𝔼 ξp ω β lamgap x π ↔ AS126 𝔼 ξp ω vphi β η xm1 x π := by
  unfold ASch3 AS126
  refine forall_congr' fun t => ?_
  rw [hl t, neg_smul, sub_neg_eq_add]

/-- Woodford (2003), p. 335: for `η = 0` and `φ = σ⁻¹`, (1.26) is the basic AS relation of
Ch. 4 with `κ ≡ ξ_p(ω + σ⁻¹)`. -/
theorem AS126_eta_zero {ξp ω σ β : ℝ} {xm1 : Ω → ℝ} {x π : ℕ → Ω → ℝ} :
    AS126 𝔼 ξp ω σ⁻¹ β 0 xm1 x π ↔
      ∀ t, π t = (ξp * (ω + σ⁻¹)) • x t + β • 𝔼.E t (π (t + 1)) := by
  unfold AS126 xTilde
  refine forall_congr' fun t => ?_
  simp only [zero_smul, sub_zero, mul_zero, smul_add, smul_smul, mul_add, add_smul]

/-- **Woodford (2003), (1.26) ⟺ (1.27), p. 335 (coefficient matching).** For adapted `x`, if
`κδ = ξ_p ηφ` and `κ(1 + βδ²) = ξ_p(ω + φ(1 + βη²))`, then
`ξ_p[ω x_t + φ x̃_t] = κ[(x_t − δ x_{t−1}) − βδ E_t(x_{t+1} − δ x_t)]` at every date. -/
theorem as_identity {ξp ω vphi β η κ δ : ℝ} (h1 : κ * δ = ξp * η * vphi)
    (h2 : κ * (1 + β * δ ^ 2) = ξp * (ω + vphi * (1 + β * η ^ 2))) {xm1 : Ω → ℝ}
    {x : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) (t : ℕ) :
    ξp • (ω • x t + vphi • xTilde 𝔼 β η xm1 x t) = κ • xTilde 𝔼 β δ xm1 x t := by
  unfold xTilde
  simp only [map_sub, map_smul, hx t]
  funext ω'
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (lag xm1 x t ω' + β * 𝔼.E t (x (t + 1)) ω') * h1 - x t ω' * h2

/-- **Woodford (2003), p. 335: (1.26) ⟺ (1.27)** for adapted `x`, whenever `κδ = ξ_p ηφ` and
`κ(1 + βδ²) = ξ_p(ω + φ(1 + βη²))`. -/
theorem AS126_iff_AS127 {ξp ω vphi β η κ δ : ℝ} (h1 : κ * δ = ξp * η * vphi)
    (h2 : κ * (1 + β * δ ^ 2) = ξp * (ω + vphi * (1 + β * η ^ 2))) {xm1 : Ω → ℝ}
    {x π : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) :
    AS126 𝔼 ξp ω vphi β η xm1 x π ↔ AS127 𝔼 κ δ β xm1 x π := by
  unfold AS126 AS127
  refine forall_congr' fun t => ?_
  rw [as_identity 𝔼 h1 h2 hx t]

/-- **Woodford (2003), p. 335 (necessity of the coefficient conditions).** If the identity
`ξ_p[ω x_t + φ x̃_t] = κ[(x_t − δ x_{t−1}) − βδ E_t(x_{t+1} − δ x_t)]` holds for every path (it
suffices: every perfect-foresight path at date 0), then `κδ = ξ_p ηφ` and
`κ(1 + βδ²) = ξ_p(ω + φ(1 + βη²))`. -/
theorem as_identity_coeffs {ξp ω vphi β η κ δ : ℝ}
    (h : ∀ (xm1 : Unit → ℝ) (x : ℕ → Unit → ℝ), ξp • (ω • x 0 + vphi •
      xTilde perfectForesight β η xm1 x 0) = κ • xTilde perfectForesight β δ xm1 x 0) :
    κ * δ = ξp * η * vphi ∧ κ * (1 + β * δ ^ 2) = ξp * (ω + vphi * (1 + β * η ^ 2)) := by
  have hA := congrFun (h (fun _ => 1) (fun _ _ => 0)) ()
  have hB := congrFun (h (fun _ => 0) (fun t _ => if t = 0 then 1 else 0)) ()
  simp [xTilde, lag, perfectForesight] at hA hB
  constructor
  · linarith
  · linear_combination -hB

/-- Woodford (2003), (1.28), p. 335: `B ≡ ω + φ(1 + βη²)`, the coefficient of `δ`. -/
noncomputable def habB (β ω vphi η : ℝ) : ℝ := ω + vphi * (1 + β * η ^ 2)

/-- Woodford (2003), (1.28), p. 335: the discriminant `B² − 4β(ηφ)²` of
`βηφ δ² − B δ + ηφ = 0`. -/
noncomputable def habDisc (β ω vphi η : ℝ) : ℝ := habB β ω vphi η ^ 2 - 4 * β * (η * vphi) ^ 2

/-- Woodford (2003), (1.28), p. 335: the smaller root of (1.28), written without division by
`η`: `δ = 2ηφ/(B + √(B² − 4β(ηφ)²))` (so `δ = 0` at `η = 0`). -/
noncomputable def habDelta (β ω vphi η : ℝ) : ℝ :=
  2 * η * vphi / (habB β ω vphi η + Real.sqrt (habDisc β ω vphi η))

/-- Woodford (2003), (1.29), p. 335: `κ`, written without division by `δ`:
`κ = ξ_p (B + √(B² − 4β(ηφ)²))/2` (equal to `ξ_p ηφ/δ` for `η > 0`, `habKappa_eq`). -/
noncomputable def habKappa (ξp β ω vphi η : ℝ) : ℝ :=
  ξp * (habB β ω vphi η + Real.sqrt (habDisc β ω vphi η)) / 2

/-- Woodford (2003), p. 335: the discriminant of (1.28) is nonnegative (`β ≥ 0`, `ω ≥ 0`,
`φ > 0`), since `(1 + βη²)² − 4βη² = (1 − βη²)²`. -/
theorem habDisc_nonneg {β ω vphi η : ℝ} (hβ : 0 ≤ β) (hω : 0 ≤ ω) (hφ : 0 < vphi) :
    0 ≤ habDisc β ω vphi η := by
  unfold habDisc habB
  have h1 : vphi * (1 + β * η ^ 2) ≤ ω + vphi * (1 + β * η ^ 2) := by linarith
  have h0 : 0 ≤ vphi * (1 + β * η ^ 2) := by positivity
  have h2 : (vphi * (1 + β * η ^ 2)) ^ 2 ≤ (ω + vphi * (1 + β * η ^ 2)) ^ 2 :=
    pow_le_pow_left₀ h0 h1 2
  nlinarith [sq_nonneg (vphi * (1 - β * η ^ 2))]

/-- Woodford (2003), p. 335: `B + √D > 0`. -/
theorem habB_add_sqrt_pos {β ω vphi η : ℝ} (hβ : 0 ≤ β) (hω : 0 ≤ ω) (hφ : 0 < vphi) :
    0 < habB β ω vphi η + Real.sqrt (habDisc β ω vphi η) := by
  have : 0 < habB β ω vphi η := by unfold habB; positivity
  linarith [Real.sqrt_nonneg (habDisc β ω vphi η)]

/-- **Woodford (2003), (1.28), p. 335: `δ` is a root**, `ηφ(1 + βδ²) = [ω + φ(1 + βη²)] δ`. -/
theorem habDelta_root {β ω vphi η : ℝ} (hβ : 0 ≤ β) (hω : 0 ≤ ω) (hφ : 0 < vphi) :
    η * vphi * (1 + β * habDelta β ω vphi η ^ 2) =
      habB β ω vphi η * habDelta β ω vphi η := by
  have hpos := habB_add_sqrt_pos (η := η) hβ hω hφ
  have hs : Real.sqrt (habDisc β ω vphi η) ^ 2 = habB β ω vphi η ^ 2 - 4 * β * (η * vphi) ^ 2 :=
    Real.sq_sqrt (habDisc_nonneg (η := η) hβ hω hφ)
  unfold habDelta
  set S := Real.sqrt (habDisc β ω vphi η)
  set B := habB β ω vphi η
  field_simp
  linear_combination η * hs

/-- Woodford (2003), (1.29), p. 335: `κδ = ξ_p ηφ` (for every `η ≥ 0`, no division). -/
theorem habKappa_mul_delta {ξp β ω vphi η : ℝ} (hβ : 0 ≤ β) (hω : 0 ≤ ω) (hφ : 0 < vphi) :
    habKappa ξp β ω vphi η * habDelta β ω vphi η = ξp * η * vphi := by
  have hpos := habB_add_sqrt_pos (η := η) hβ hω hφ
  unfold habKappa habDelta
  field_simp

/-- Woodford (2003), (1.27)–(1.29), p. 335: `κ(1 + βδ²) = ξ_p(ω + φ(1 + βη²))`. -/
theorem habKappa_mul {ξp β ω vphi η : ℝ} (hβ : 0 ≤ β) (hω : 0 ≤ ω) (hφ : 0 < vphi) :
    habKappa ξp β ω vphi η * (1 + β * habDelta β ω vphi η ^ 2) =
      ξp * (ω + vphi * (1 + β * η ^ 2)) := by
  have hpos := habB_add_sqrt_pos (η := η) hβ hω hφ
  have hs : Real.sqrt (habDisc β ω vphi η) ^ 2 = habB β ω vphi η ^ 2 - 4 * β * (η * vphi) ^ 2 :=
    Real.sq_sqrt (habDisc_nonneg (η := η) hβ hω hφ)
  unfold habKappa habDelta
  rw [show ω + vphi * (1 + β * η ^ 2) = habB β ω vphi η from rfl]
  set S := Real.sqrt (habDisc β ω vphi η)
  set B := habB β ω vphi η
  field_simp
  linear_combination ξp * hs

/-- **Woodford (2003), (1.26) ⟺ (1.27), p. 335**, with `δ` the smaller root of (1.28) and `κ`
from (1.29), for every `η ≥ 0` (including the limiting case `η = 0`, where `δ = 0` and
`κ = ξ_p(ω + φ)`), for adapted `x`. -/
theorem AS126_iff_AS127_habit {ξp β ω vphi η : ℝ} (hβ : 0 ≤ β) (hω : 0 ≤ ω) (hφ : 0 < vphi)
    {xm1 : Ω → ℝ} {x π : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) :
    AS126 𝔼 ξp ω vphi β η xm1 x π ↔
      AS127 𝔼 (habKappa ξp β ω vphi η) (habDelta β ω vphi η) β xm1 x π :=
  AS126_iff_AS127 𝔼 (habKappa_mul_delta hβ hω hφ) (habKappa_mul hβ hω hφ) hx

/-- **Woodford (2003), (1.29), p. 335:** for `η > 0`, `κ = ξ_p ηφ/δ`. -/
theorem habKappa_eq {ξp β ω vphi η : ℝ} (hβ : 0 ≤ β) (hω : 0 ≤ ω) (hφ : 0 < vphi)
    (hη : 0 < η) : habKappa ξp β ω vphi η = ξp * η * vphi / habDelta β ω vphi η := by
  have hd : 0 < habDelta β ω vphi η := by
    unfold habDelta
    exact div_pos (by positivity) (habB_add_sqrt_pos hβ hω hφ)
  rw [eq_div_iff hd.ne', habKappa_mul_delta hβ hω hφ]

/-- Woodford (2003), (1.29), p. 335: `κ > 0` (`ξ_p > 0`). -/
theorem habKappa_pos {ξp β ω vphi η : ℝ} (hξ : 0 < ξp) (hβ : 0 ≤ β) (hω : 0 ≤ ω)
    (hφ : 0 < vphi) : 0 < habKappa ξp β ω vphi η := by
  unfold habKappa
  exact div_pos (mul_pos hξ (habB_add_sqrt_pos hβ hω hφ)) two_pos

/-- **Woodford (2003), (1.27)–(1.29), p. 335: the coefficient conditions are (1.28)–(1.29).**
For `η > 0`, `ξ_p > 0`, `φ > 0`: `κδ = ξ_p ηφ` and `κ(1 + βδ²) = ξ_p(ω + φ(1 + βη²))` hold iff
`δ` solves (1.28) and `κ = ξ_p ηφ/δ`. -/
theorem coeffs_iff_root {ξp β ω vphi η κ δ : ℝ} (hξ : 0 < ξp) (hφ : 0 < vphi) (hη : 0 < η) :
    (κ * δ = ξp * η * vphi ∧ κ * (1 + β * δ ^ 2) = ξp * (ω + vphi * (1 + β * η ^ 2))) ↔
      (η * vphi * (1 + β * δ ^ 2) = (ω + vphi * (1 + β * η ^ 2)) * δ ∧
        κ = ξp * η * vphi / δ) := by
  have hp : 0 < ξp * η * vphi := by positivity
  constructor
  · rintro ⟨h1, h2⟩
    have hδ : δ ≠ 0 := by rintro rfl; rw [mul_zero] at h1; linarith
    refine ⟨?_, by rw [eq_div_iff hδ, h1]⟩
    have : ξp * (η * vphi * (1 + β * δ ^ 2)) = ξp * ((ω + vphi * (1 + β * η ^ 2)) * δ) := by
      linear_combination δ * h2 - (1 + β * δ ^ 2) * h1
    exact mul_left_cancel₀ hξ.ne' this
  · rintro ⟨hr, hk⟩
    have hδ : δ ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hr
      have : 0 < η * vphi * (1 + β * 0 ^ 2) := by
        rw [zero_pow two_ne_zero, mul_zero, add_zero, mul_one]; positivity
      linarith
    have h1 : κ * δ = ξp * η * vphi := by rw [hk, div_mul_cancel₀ _ hδ]
    refine ⟨h1, ?_⟩
    rw [hk, div_mul_eq_mul_div, div_eq_iff hδ]
    linear_combination ξp * hr

/-- **Woodford (2003), p. 335, characterisation of (1.27).** For `η > 0`: the identity between
the right-hand sides of (1.26) and (1.27) holds for every path iff `δ` is a root of (1.28) and
`κ = ξ_p ηφ/δ` (either root of (1.28) works; the book takes the smaller one). -/
theorem identity_iff_root {ξp β ω vphi η κ δ : ℝ} (hξ : 0 < ξp) (hφ : 0 < vphi) (hη : 0 < η) :
    (∀ (xm1 : Unit → ℝ) (x : ℕ → Unit → ℝ), ξp • (ω • x 0 + vphi •
      xTilde perfectForesight β η xm1 x 0) = κ • xTilde perfectForesight β δ xm1 x 0) ↔
      (η * vphi * (1 + β * δ ^ 2) = (ω + vphi * (1 + β * η ^ 2)) * δ ∧
        κ = ξp * η * vphi / δ) := by
  constructor
  · intro h
    exact (coeffs_iff_root hξ hφ hη).mp (as_identity_coeffs h)
  · intro h xm1 x
    obtain ⟨h1, h2⟩ := (coeffs_iff_root hξ hφ hη).mpr h
    exact as_identity perfectForesight h1 h2 (fun _ => rfl) 0

/-- Woodford (2003), p. 335: `δ ≥ 0` for `η ≥ 0`. -/
theorem habDelta_nonneg {β ω vphi η : ℝ} (hβ : 0 ≤ β) (hω : 0 ≤ ω) (hφ : 0 < vphi)
    (hη : 0 ≤ η) : 0 ≤ habDelta β ω vphi η :=
  div_nonneg (by positivity) (habB_add_sqrt_pos hβ hω hφ).le

/-- Woodford (2003), p. 335 (strictness at the lower end): `δ > 0 ↔ η > 0`. -/
theorem habDelta_pos_iff {β ω vphi η : ℝ} (hβ : 0 ≤ β) (hω : 0 ≤ ω) (hφ : 0 < vphi) :
    0 < habDelta β ω vphi η ↔ 0 < η := by
  unfold habDelta
  rw [div_pos_iff_of_pos_right (habB_add_sqrt_pos hβ hω hφ)]
  constructor
  · intro h; nlinarith
  · intro h; positivity

/-- Woodford (2003), p. 335: `2φ − B ≤ √D`, with `D − (2φ − B)² = 4φω`. -/
theorem two_vphi_sub_le_sqrt {β ω vphi η : ℝ} (hω : 0 ≤ ω) (hφ : 0 < vphi) :
    2 * vphi - habB β ω vphi η ≤ Real.sqrt (habDisc β ω vphi η) := by
  have hD : (2 * vphi - habB β ω vphi η) ^ 2 + 4 * vphi * ω = habDisc β ω vphi η := by
    unfold habDisc habB; ring
  refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
  nlinarith

/-- **Woodford (2003), p. 335: `0 ≤ δ ≤ η`.** -/
theorem habDelta_le {β ω vphi η : ℝ} (hβ : 0 ≤ β) (hω : 0 ≤ ω) (hφ : 0 < vphi) (hη : 0 ≤ η) :
    habDelta β ω vphi η ≤ η := by
  have hpos := habB_add_sqrt_pos (η := η) hβ hω hφ
  have h2 := two_vphi_sub_le_sqrt (β := β) (η := η) hω hφ
  unfold habDelta
  rw [div_le_iff₀ hpos]
  nlinarith

/-- Woodford (2003), p. 335 (strictness at the upper end): for `η > 0` and `ω > 0`, `δ < η`. -/
theorem habDelta_lt {β ω vphi η : ℝ} (hβ : 0 ≤ β) (hω : 0 < ω) (hφ : 0 < vphi) (hη : 0 < η) :
    habDelta β ω vphi η < η := by
  have hpos := habB_add_sqrt_pos (η := η) hβ hω.le hφ
  have hlt : 2 * vphi - habB β ω vphi η < Real.sqrt (habDisc β ω vphi η) := by
    rcases lt_or_ge (2 * vphi - habB β ω vphi η) 0 with h | h
    · exact lt_of_lt_of_le h (Real.sqrt_nonneg _)
    · have hD : (2 * vphi - habB β ω vphi η) ^ 2 + 4 * vphi * ω = habDisc β ω vphi η := by
        unfold habDisc habB; ring
      rw [Real.lt_sqrt h, ← hD]
      nlinarith [mul_pos hφ hω]
  unfold habDelta
  rw [div_lt_iff₀ hpos]
  nlinarith

/-- Woodford (2003), p. 335 (strictness at the upper end): with `ω = 0` (and `βη² ≤ 1`),
`δ = η`. -/
theorem habDelta_eq_of_omega_zero {β vphi η : ℝ} (hφ : 0 < vphi)
    (hb : β * η ^ 2 ≤ 1) : habDelta β 0 vphi η = η := by
  have hD : habDisc β 0 vphi η = (vphi * (1 - β * η ^ 2)) ^ 2 := by
    unfold habDisc habB; ring
  have hS : Real.sqrt (habDisc β 0 vphi η) = vphi * (1 - β * η ^ 2) := by
    rw [hD, Real.sqrt_sq (by nlinarith)]
  unfold habDelta
  rw [hS]
  unfold habB
  have : (0 : ℝ) + vphi * (1 + β * η ^ 2) + vphi * (1 - β * η ^ 2) = 2 * vphi := by ring
  rw [this]
  field_simp

/-- **Woodford (2003), p. 335: exact strictness of `0 ≤ δ ≤ η`.** For `0 < η` with
`βη² ≤ 1`: `δ < η ↔ ω > 0` (and `δ > 0 ↔ η > 0`, `habDelta_pos_iff`). -/
theorem habDelta_lt_iff {β ω vphi η : ℝ} (hβ : 0 ≤ β) (hω : 0 ≤ ω) (hφ : 0 < vphi)
    (hη : 0 < η) (hb : β * η ^ 2 ≤ 1) : habDelta β ω vphi η < η ↔ 0 < ω := by
  constructor
  · intro h
    rcases hω.lt_or_eq with h' | h'
    · exact h'
    · subst h'
      rw [habDelta_eq_of_omega_zero hφ hb] at h
      exact absurd h (lt_irrefl _)
  · intro h
    exact habDelta_lt hβ h hφ hη

/-- Woodford (2003), (1.28), p. 335: the larger root `δ' = (B + √D)/(2βηφ)`. -/
noncomputable def habDelta2 (β ω vphi η : ℝ) : ℝ :=
  (habB β ω vphi η + Real.sqrt (habDisc β ω vphi η)) / (2 * β * η * vphi)

/-- **Woodford (2003), (1.28), p. 335: `δ` is the smaller root.** For `β, η > 0`, every root
`d` of (1.28) is `δ` or `δ'`, `δ δ' = β⁻¹`, and `δ ≤ δ'`; when moreover `η ≤ 1` and `β < 1`,
`δ' > 1`. -/
theorem habDelta_smaller_root {β ω vphi η : ℝ} (hβ : 0 < β) (hω : 0 ≤ ω) (hφ : 0 < vphi)
    (hη : 0 < η) :
    (∀ d, η * vphi * (1 + β * d ^ 2) = habB β ω vphi η * d →
      d = habDelta β ω vphi η ∨ d = habDelta2 β ω vphi η) ∧
    habDelta β ω vphi η * habDelta2 β ω vphi η = β⁻¹ ∧
    habDelta β ω vphi η ≤ habDelta2 β ω vphi η := by
  have hpos := habB_add_sqrt_pos (η := η) hβ.le hω hφ
  have hs : Real.sqrt (habDisc β ω vphi η) ^ 2 = habB β ω vphi η ^ 2 - 4 * β * (η * vphi) ^ 2 :=
    Real.sq_sqrt (habDisc_nonneg (η := η) hβ.le hω hφ)
  have hprod : habDelta β ω vphi η * habDelta2 β ω vphi η = β⁻¹ := by
    unfold habDelta habDelta2
    field_simp
  have hsum : habDelta β ω vphi η + habDelta2 β ω vphi η =
      habB β ω vphi η / (β * η * vphi) := by
    unfold habDelta habDelta2
    field_simp
    linear_combination hs
  refine ⟨fun d hd => ?_, hprod, ?_⟩
  · have hfac : β * η * vphi * ((d - habDelta β ω vphi η) * (d - habDelta2 β ω vphi η)) = 0 := by
      have e : (d - habDelta β ω vphi η) * (d - habDelta2 β ω vphi η) =
          d ^ 2 - (habDelta β ω vphi η + habDelta2 β ω vphi η) * d +
            habDelta β ω vphi η * habDelta2 β ω vphi η := by ring
      rw [e, hsum, hprod]
      field_simp
      linear_combination hd
    rcases mul_eq_zero.mp hfac with h | h
    · exfalso; have : 0 < β * η * vphi := by positivity
      linarith
    · rcases mul_eq_zero.mp h with h | h
      · left; linarith
      · right; linarith
  · unfold habDelta habDelta2
    rw [div_le_div_iff₀ hpos (by positivity)]
    nlinarith [Real.sqrt_nonneg (habDisc β ω vphi η), hs]

/-- Woodford (2003), p. 335: for `0 < η ≤ 1` and `0 < β < 1` the larger root exceeds 1, so it
lies outside `[0, η]` and `δ` is the only root there. -/
theorem habDelta2_gt_one {β ω vphi η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hω : 0 ≤ ω)
    (hφ : 0 < vphi) (hη : 0 < η) (hη1 : η ≤ 1) : 1 < habDelta2 β ω vphi η := by
  obtain ⟨-, hprod, -⟩ := habDelta_smaller_root hβ hω hφ hη
  have hd0 : 0 < habDelta β ω vphi η := (habDelta_pos_iff hβ.le hω hφ).mpr hη
  have hd1 : habDelta β ω vphi η ≤ 1 := (habDelta_le hβ.le hω hφ hη.le).trans hη1
  have h1 : 1 < β⁻¹ := one_lt_inv₀ hβ |>.mpr hβ1
  by_contra hc
  push Not at hc
  have : habDelta β ω vphi η * habDelta2 β ω vphi η ≤ 1 := by
    have h2 : 0 ≤ habDelta2 β ω vphi η := by
      unfold habDelta2
      exact div_nonneg (habB_add_sqrt_pos hβ.le hω hφ).le (by positivity)
    nlinarith
  linarith

/-- **Woodford (2003), (1.29), p. 335 at `η = 0` (survey error 12).** At `η = 0` the printed
formula `κ = ξ_p ηφ/δ` is `0/0`: `δ = 0` and `ξ_p ηφ = 0`, so the relation `κδ = ξ_p ηφ`
holds for every `κ` and does not determine `κ`. The value the book intends is the continuous
extension `κ = ξ_p(ω + φ)` (`habKappa`), which is also what the second coefficient condition
`κ(1 + βδ²) = ξ_p(ω + φ(1 + βη²))` forces at `η = 0`. -/
theorem eta_zero_kappa {ξp β ω vphi : ℝ} (hω : 0 ≤ ω) (hφ : 0 < vphi) :
    habDelta β ω vphi 0 = 0 ∧ ξp * 0 * vphi = 0 ∧
      (∀ κ, κ * habDelta β ω vphi 0 = ξp * 0 * vphi) ∧
      habKappa ξp β ω vphi 0 = ξp * (ω + vphi) ∧
      (∀ κ, κ * (1 + β * habDelta β ω vphi 0 ^ 2) = ξp * (ω + vphi * (1 + β * 0 ^ 2)) ↔
        κ = ξp * (ω + vphi)) := by
  have hd : habDelta β ω vphi 0 = 0 := by simp [habDelta]
  have hD : habDisc β ω vphi 0 = (ω + vphi) ^ 2 := by unfold habDisc habB; ring
  have hlast : ∀ κ, κ * (1 + β * habDelta β ω vphi 0 ^ 2) =
      ξp * (ω + vphi * (1 + β * 0 ^ 2)) ↔ κ = ξp * (ω + vphi) := by
    intro κ
    rw [hd]
    constructor
    · intro h
      linear_combination h
    · intro h
      linear_combination h
  refine ⟨hd, by ring, fun κ => by rw [hd]; ring, ?_, hlast⟩
  unfold habKappa
  rw [hD, Real.sqrt_sq (by linarith)]
  unfold habB
  ring

/-- Woodford (2003), p. 333: `φ(η) = [(1 − βη)σ]⁻¹`, the habit-adjusted intertemporal
elasticity coefficient as a function of `η` (`σ` fixed). -/
noncomputable def vphiOf (β σ η : ℝ) : ℝ := ((1 - β * η) * σ)⁻¹

/-- Woodford (2003), p. 333: `φ(η) > 0` when `βη < 1`, `σ > 0`. -/
theorem vphiOf_pos {β σ η : ℝ} (hσ : 0 < σ) (h : β * η < 1) : 0 < vphiOf β σ η := by
  unfold vphiOf
  exact inv_pos.mpr (mul_pos (by linarith) hσ)

/-- Woodford (2003), p. 335: as `η → 0`, `B + √D → 2(ω + σ⁻¹)` (with `φ = φ(η)`). -/
theorem habBS_tendsto {β σ ω : ℝ} (hσ : 0 < σ) (hω : 0 ≤ ω) :
    Tendsto (fun η => habB β ω (vphiOf β σ η) η + Real.sqrt (habDisc β ω (vphiOf β σ η) η))
      (𝓝 0) (𝓝 (2 * (ω + σ⁻¹))) := by
  have hv : Tendsto (vphiOf β σ) (𝓝 0) (𝓝 σ⁻¹) := by
    have h1 : Tendsto (fun η : ℝ => (1 - β * η) * σ) (𝓝 0) (𝓝 ((1 - β * 0) * σ)) :=
      ((tendsto_const_nhds.sub (tendsto_id.const_mul β)).mul_const σ)
    have h2 := h1.inv₀ (by rw [mul_zero, sub_zero, one_mul]; exact hσ.ne')
    rw [mul_zero, sub_zero, one_mul] at h2
    exact h2
  have hB : Tendsto (fun η => habB β ω (vphiOf β σ η) η) (𝓝 0)
      (𝓝 (ω + σ⁻¹ * (1 + β * 0 ^ 2))) :=
    tendsto_const_nhds.add (hv.mul (tendsto_const_nhds.add
      (tendsto_const_nhds.mul (tendsto_id.pow 2))))
  have hD : Tendsto (fun η => habDisc β ω (vphiOf β σ η) η) (𝓝 0)
      (𝓝 ((ω + σ⁻¹ * (1 + β * 0 ^ 2)) ^ 2 - 4 * β * (0 * σ⁻¹) ^ 2)) :=
    (hB.pow 2).sub (tendsto_const_nhds.mul ((tendsto_id.mul hv).pow 2))
  have hS := (Real.continuous_sqrt.tendsto _).comp hD
  have hpos : 0 ≤ ω + σ⁻¹ := by have := inv_pos.mpr hσ; linarith
  have e1 : ω + σ⁻¹ * (1 + β * 0 ^ 2) = ω + σ⁻¹ := by ring
  have e2 : (ω + σ⁻¹ * (1 + β * 0 ^ 2)) ^ 2 - 4 * β * (0 * σ⁻¹) ^ 2 = (ω + σ⁻¹) ^ 2 := by ring
  have hval : ω + σ⁻¹ * (1 + β * 0 ^ 2) +
      Real.sqrt ((ω + σ⁻¹ * (1 + β * 0 ^ 2)) ^ 2 - 4 * β * (0 * σ⁻¹) ^ 2) = 2 * (ω + σ⁻¹) := by
    rw [e2, e1, Real.sqrt_sq hpos]
    ring
  have hlim := hB.add hS
  rw [hval] at hlim
  exact hlim

/-- **Woodford (2003), p. 335: `δ/η → φ/(ω + φ)` as `η → 0⁺`** (with `φ = φ(η)`, so the limit
is `σ⁻¹/(ω + σ⁻¹)`), a genuine limit. -/
theorem delta_div_eta_tendsto {β σ ω : ℝ} (hσ : 0 < σ) (hω : 0 ≤ ω) :
    Tendsto (fun η => habDelta β ω (vphiOf β σ η) η / η) (𝓝[>] 0)
      (𝓝 (σ⁻¹ / (ω + σ⁻¹))) := by
  have hv : Tendsto (vphiOf β σ) (𝓝 0) (𝓝 σ⁻¹) := by
    have h1 : Tendsto (fun η : ℝ => (1 - β * η) * σ) (𝓝 0) (𝓝 ((1 - β * 0) * σ)) :=
      ((tendsto_const_nhds.sub (tendsto_id.const_mul β)).mul_const σ)
    have h2 := h1.inv₀ (by rw [mul_zero, sub_zero, one_mul]; exact hσ.ne')
    rw [mul_zero, sub_zero, one_mul] at h2
    exact h2
  have hpos : 0 < ω + σ⁻¹ := by have := inv_pos.mpr hσ; linarith
  have hg := (hv.const_mul 2).div (habBS_tendsto (β := β) hσ hω) (by positivity)
  have hval : 2 * σ⁻¹ / (2 * (ω + σ⁻¹)) = σ⁻¹ / (ω + σ⁻¹) := by
    rw [mul_div_mul_left _ _ two_ne_zero]
  rw [hval] at hg
  refine (hg.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hη0 : η ≠ 0 := ne_of_gt hη
  rw [Pi.div_apply]
  symm
  unfold habDelta
  rw [div_div, show 2 * η * vphiOf β σ η = η * (2 * vphiOf β σ η) by ring,
    show (habB β ω (vphiOf β σ η) η + Real.sqrt (habDisc β ω (vphiOf β σ η) η)) * η =
      η * (habB β ω (vphiOf β σ η) η + Real.sqrt (habDisc β ω (vphiOf β σ η) η)) by ring,
    mul_div_mul_left _ _ hη0]

/-- **Woodford (2003), p. 335: `κ = ξ_p ηφ/δ → ξ_p(ω + σ⁻¹)` as `η → 0⁺`**, so in the limit
(1.29) coincides with the Ch. 3 definition `κ ≡ ξ_p(ω + σ⁻¹)`. -/
theorem kappa_tendsto {ξp β σ ω : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hσ : 0 < σ) (hω : 0 ≤ ω) :
    Tendsto (fun η => ξp * η * vphiOf β σ η / habDelta β ω (vphiOf β σ η) η) (𝓝[>] 0)
      (𝓝 (ξp * (ω + σ⁻¹))) := by
  have hk := ((habBS_tendsto (β := β) hσ hω).const_mul ξp).div_const 2
  have hval : ξp * (2 * (ω + σ⁻¹)) / 2 = ξp * (ω + σ⁻¹) := by ring
  rw [hval] at hk
  refine (hk.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with η hη
  have hβη : β * η < 1 := by nlinarith [hη.1, hη.2]
  have := habKappa_eq (ξp := ξp) hβ0 hω (vphiOf_pos hσ hβη) hη.1
  unfold habKappa at this
  rw [← this, mul_div_assoc]

/-- **Woodford (2003), Ch. 6, p. 404 (used there; property of (1.28)): `δ` is strictly
increasing in `η` on `[0, 1]`** (with `φ = φ(η) = [(1 − βη)σ]⁻¹`, `0 < β < 1`, `σ > 0`,
`ω ≥ 0`). -/
theorem habDelta_strictMonoOn {β σ ω : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hω : 0 ≤ ω) :
    StrictMonoOn (fun η => habDelta β ω (vphiOf β σ η) η) (Set.Icc 0 1) := by
  intro η1 h1 η2 h2 hlt
  obtain ⟨h10, h11⟩ := h1
  obtain ⟨h20, h21⟩ := h2
  simp only
  have hb1 : β * η1 < 1 := by nlinarith
  have hb2 : β * η2 < 1 := by nlinarith
  set φ1 := vphiOf β σ η1 with hφ1
  set φ2 := vphiOf β σ η2 with hφ2
  have hp1 : 0 < φ1 := vphiOf_pos hσ hb1
  have hp2 : 0 < φ2 := vphiOf_pos hσ hb2
  have hi1 : φ1 * ((1 - β * η1) * σ) = 1 := inv_mul_cancel₀ (by
    have : 0 < (1 - β * η1) * σ := mul_pos (by linarith) hσ
    exact this.ne')
  have hi2 : φ2 * ((1 - β * η2) * σ) = 1 := inv_mul_cancel₀ (by
    have : 0 < (1 - β * η2) * σ := mul_pos (by linarith) hσ
    exact this.ne')
  have r1 := habDelta_root (η := η1) hβ0.le hω hp1
  have r2 := habDelta_root (η := η2) hβ0.le hω hp2
  unfold habB at r1 r2
  set d1 := habDelta β ω φ1 η1
  set d2 := habDelta β ω φ2 η2
  set c1 := ω * σ * (1 - β * η1) + 1 + β * η1 ^ 2
  set c2 := ω * σ * (1 - β * η2) + 1 + β * η2 ^ 2
  have r1' : η1 * (1 + β * d1 ^ 2) = c1 * d1 := by
    linear_combination ((1 - β * η1) * σ) * r1 - (η1 * (1 + β * d1 ^ 2) -
      (1 + β * η1 ^ 2) * d1) * hi1
  have r2' : η2 * (1 + β * d2 ^ 2) = c2 * d2 := by
    linear_combination ((1 - β * η2) * σ) * r2 - (η2 * (1 + β * d2 ^ 2) -
      (1 + β * η2 ^ 2) * d2) * hi2
  have d10 : 0 ≤ d1 := habDelta_nonneg hβ0.le hω hp1 h10
  have d1le : d1 ≤ η1 := habDelta_le hβ0.le hω hp1 h10
  have d20 : 0 ≤ d2 := habDelta_nonneg hβ0.le hω hp2 h20
  have d2le : d2 ≤ η2 := habDelta_le hβ0.le hω hp2 h20
  have hprod : 0 ≤ (η1 - d1) * (η2 - d1) := mul_nonneg (by linarith) (by linarith)
  have hωσ : 0 ≤ ω * σ * β * d1 := by positivity
  have hη12 : η1 * η2 ≤ 1 := by nlinarith
  have hbr : 0 < 1 + β * d1 ^ 2 - β * d1 * (η1 + η2) + ω * σ * β * d1 := by nlinarith
  have hG1 : 0 < η2 * (1 + β * d1 ^ 2) - c2 * d1 := by
    have e : η2 * (1 + β * d1 ^ 2) - c2 * d1 =
        (η2 - η1) * (1 + β * d1 ^ 2 - β * d1 * (η1 + η2) + ω * σ * β * d1) +
          (η1 * (1 + β * d1 ^ 2) - c1 * d1) := by ring
    rw [e, r1', sub_self, add_zero]
    exact mul_pos (by linarith) hbr
  have hneg : β * η2 * (d1 + d2) - c2 < 0 := by
    have hωs : 0 ≤ ω * σ * (1 - β * η2) := mul_nonneg (by positivity) (by linarith)
    have : β * η2 * (d1 + d2) ≤ β * η2 * (η1 + η2) := by
      have : 0 ≤ β * η2 := by positivity
      nlinarith
    nlinarith
  have hfac : η2 * (1 + β * d1 ^ 2) - c2 * d1 =
      (d1 - d2) * (β * η2 * (d1 + d2) - c2) + (η2 * (1 + β * d2 ^ 2) - c2 * d2) := by ring
  rw [r2', sub_self, add_zero] at hfac
  rw [hfac] at hG1
  nlinarith

/-! ### (1.30)–(1.33): determinacy with one predetermined variable

The Blanchard–Kahn tools (`pow_entry_bound`, `rvMul`, `FSolves`, `fsolves_unique`, `fwdVec`,
`abs_rec_le`) are in `ForwardSystems` (restated from the Woodford Chapter 4 project,
`BlanchardKahn`, itself from the Galí Chapter 6 project). -/

/-- Woodford (2003), p. 335 (coefficients `ψ_j`): with scalar forcing `w_t = v g_t`, the forward
series is `∑_k (Kᵏ v)_i E_t g_{t+k}`. -/
theorem fwdS_scalar {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (g : ℕ → Ω → ℝ)
    (t : ℕ) (i : Fin n) (ω : Ω) :
    fwdVec 𝔼 K (fun t j => v j • g t) t i ω =
      ∑' k, ((K ^ k).mulVec v) i * 𝔼.E t (g (t + k)) ω := by
  unfold fwdVec
  refine tsum_congr fun k => ?_
  simp only [map_smul]
  rw [rvMul_smul_const]
  rfl

/-- Woodford (2003), (1.30)–(1.33), p. 335: `n` non-predetermined variables `z_t` and one
predetermined variable `s_t`: `P z_t = N E_t z_{t+1} + h s_t + b g_t`,
`s_{t+1} = ρ s_t + φ · z_t`. -/
def PredSysN {n : ℕ} (P N : Matrix (Fin n) (Fin n) ℝ) (h b φ : Fin n → ℝ) (ρ : ℝ)
    (g : ℕ → Ω → ℝ) (z : ℕ → Fin n → Ω → ℝ) (s : ℕ → Ω → ℝ) : Prop :=
  (∀ t, rvMul P (z t) = rvMul N (fun j => 𝔼.E t (z (t + 1) j)) + fun i => h i • s t + b i • g t)
    ∧ ∀ t, s (t + 1) = ρ • s t + ∑ j, φ j • z t j

/-- Woodford (2003), p. 335 (the Blanchard–Kahn decomposition): `(λ, ω)` with
`P ω = λ N ω + h` and `λ = ρ + φ · ω` (`λ` the eigenvalue attached to the
predetermined variable, `ω` the coefficients `ω_y` of (1.31)–(1.33)). -/
def DecompN {n : ℕ} (P N : Matrix (Fin n) (Fin n) ℝ) (h φ : Fin n → ℝ) (ρ lam : ℝ)
    (ω : Fin n → ℝ) : Prop :=
  (∀ i, ∑ j, P i j * ω j = lam * ∑ j, N i j * ω j + h i) ∧ lam = ρ + ∑ j, φ j * ω j

/-- Woodford (2003), p. 335: the matrix `M = P − (N ω) φᵀ` of the forward block satisfied by
`ẑ_t = z_t − ω s_t`. -/
def resMN {n : ℕ} (P N : Matrix (Fin n) (Fin n) ℝ) (φ ω : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => P i j - (∑ l, N i l * ω l) * φ j

omit 𝔼 in
/-- Woodford (2003), p. 335: the row identity behind the decomposition — given
`s_{t+1} = ρ s_t + φ · z_t`, `P z_t = N E_t z_{t+1} + h s_t + b g_t` in row `i` iff
`M ẑ_t = N E_t ẑ_{t+1} + b g_t` in row `i` (`ẑ = z − ω s`). -/
theorem rowN_iff {n : ℕ} {P N : Matrix (Fin n) (Fin n) ℝ} {h b φ ω : Fin n → ℝ} {ρ lam : ℝ}
    (hD : DecompN P N h φ ρ lam ω) (i : Fin n) {z E : Fin n → ℝ} {st st1 gt : ℝ}
    (hrec : st1 = ρ * st + ∑ j, φ j * z j) :
    ∑ j, P i j * z j = ∑ j, N i j * E j + h i * st + b i * gt ↔
      ∑ j, resMN P N φ ω i j * (z j - ω j * st) =
        ∑ j, N i j * (E j - ω j * st1) + b i * gt := by
  obtain ⟨hW, hL⟩ := hD
  have hWi := hW i
  simp only [resMN, Matrix.of_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
  have e1 : ∑ j, P i j * (ω j * st) = st * ∑ j, P i j * ω j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ j, (∑ l, N i l * ω l) * φ j * z j = (∑ l, N i l * ω l) * ∑ j, φ j * z j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have e3 : ∑ j, (∑ l, N i l * ω l) * φ j * (ω j * st) =
      (∑ l, N i l * ω l) * st * ∑ j, φ j * ω j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have e4 : ∑ j, N i j * (ω j * st1) = st1 * ∑ j, N i j * ω j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2, e3, e4]
  constructor
  · intro H
    linear_combination H + (∑ l, N i l * ω l) * hrec - st * hWi -
      (∑ l, N i l * ω l) * st * hL
  · intro H
    linear_combination H - (∑ l, N i l * ω l) * hrec + st * hWi +
      (∑ l, N i l * ω l) * st * hL

/-- Woodford (2003), p. 335: `G = M⁻¹ N`, the matrix of the forward block. -/
noncomputable def predG {n : ℕ} (P N : Matrix (Fin n) (Fin n) ℝ) (φ ω : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (resMN P N φ ω)⁻¹ * N

/-- Woodford (2003), p. 335: `w = M⁻¹ b`, the loading of the forcing in the forward block. -/
noncomputable def predW {n : ℕ} (P N : Matrix (Fin n) (Fin n) ℝ) (b φ ω : Fin n → ℝ) :
    Fin n → ℝ :=
  (resMN P N φ ω)⁻¹.mulVec b

/-- **Woodford (2003), p. 335: the Blanchard–Kahn determinacy condition with one
predetermined variable**, stated exactly: a decomposition `(λ, ω)` (`DecompN`) with the
eigenvalue `λ` attached to the predetermined variable inside the unit circle, `M = P − (Nω)φᵀ`
invertible, and every (complex) eigenvalue of the forward-block matrix `G = M⁻¹N` inside the
unit circle (equivalently, all remaining roots of the system outside it). This module proves
that the condition is sufficient for existence and uniqueness (`predSysN_existsUnique`) and that it
is non-vacuous for `η > 0` (`bkCondition_calibration`); its necessity is proved in the module
`HabitNecessity` (`habit_determinate_iff_bk`). -/
def BKCondition {n : ℕ} (P N : Matrix (Fin n) (Fin n) ℝ) (h φ : Fin n → ℝ) (ρ lam : ℝ)
    (ω : Fin n → ℝ) : Prop :=
  DecompN P N h φ ρ lam ω ∧ |lam| < 1 ∧ IsUnit (resMN P N φ ω).det ∧
    ∀ w : ℂ, (Matrix.scalar (Fin n) w - (predG P N φ ω).map Complex.ofReal).det = 0 → ‖w‖ < 1

/-- Woodford (2003), p. 335: with `M` invertible, `M ẑ_t = N E_t ẑ_{t+1} + b g_t` iff
`ẑ_t = G E_t ẑ_{t+1} + w g_t`. -/
theorem res_iff_fsolves {n : ℕ} {P N : Matrix (Fin n) (Fin n) ℝ} {b φ ω : Fin n → ℝ}
    (hM : IsUnit (resMN P N φ ω).det) (g : ℕ → Ω → ℝ) (zh : ℕ → Fin n → Ω → ℝ) :
    (∀ t, rvMul (resMN P N φ ω) (zh t) =
      rvMul N (fun j => 𝔼.E t (zh (t + 1) j)) + fun i => b i • g t) ↔
      FSolves 𝔼 (predG P N φ ω) (fun t i => predW P N b φ ω i • g t) zh := by
  set M := resMN P N φ ω
  have h1 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hM
  have h2 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  constructor
  · intro H t
    have e := congrArg (rvMul M⁻¹) (H t)
    rw [rvMul_rvMul, h1, rvMul_one, rvMul_add, rvMul_rvMul, rvMul_smul_const] at e
    rw [e]
    rfl
  · intro H t
    rw [H t]
    change rvMul M (rvMul (M⁻¹ * N) (fun j => 𝔼.E t (zh (t + 1) j)) +
      fun i => (M⁻¹.mulVec b) i • g t) = _
    rw [rvMul_add, rvMul_rvMul, ← mul_assoc, h2, one_mul, rvMul_smul_const,
      Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]

/-- Woodford (2003), p. 335: the path of the predetermined variable, `s_0` given and
`s_{t+1} = λ s_t + φ · F_t`. -/
noncomputable def sPathN {n : ℕ} (lam : ℝ) (φ : Fin n → ℝ) (F : ℕ → Fin n → Ω → ℝ)
    (s0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => s0
  | t + 1 => lam • sPathN lam φ F s0 t + ∑ j, φ j • F t j

/-- Woodford (2003), p. 335 (reduction): along any adapted solution, `ẑ_t = z_t − ω s_t` solves
`M ẑ_t = N E_t ẑ_{t+1} + b g_t` and `s_{t+1} = λ s_t + φ · ẑ_t`. -/
theorem predSysN_reduce {n : ℕ} {P N : Matrix (Fin n) (Fin n) ℝ} {h b φ ω : Fin n → ℝ}
    {ρ lam : ℝ} (hD : DecompN P N h φ ρ lam ω) {g : ℕ → Ω → ℝ} {z : ℕ → Fin n → Ω → ℝ}
    {s : ℕ → Ω → ℝ} (hsys : PredSysN 𝔼 P N h b φ ρ g z s) (hza : VAdapted 𝔼 z)
    (hsa : 𝔼.Adapted s) :
    (∀ t, rvMul (resMN P N φ ω) (fun i => z t i - ω i • s t) =
      rvMul N (fun j => 𝔼.E t (z (t + 1) j - ω j • s (t + 1))) + fun i => b i • g t) ∧
    ∀ t, s (t + 1) = lam • s t + ∑ j, φ j • (z t j - ω j • s t) := by
  obtain ⟨hrow, hrec⟩ := hsys
  have hE1 : ∀ t, 𝔼.E t (s (t + 1)) = s (t + 1) := by
    intro t
    rw [hrec t, map_add, map_smul, hsa t, map_sum]
    simp only [map_smul, hza t]
  refine ⟨fun t => ?_, fun t => ?_⟩
  · funext i x
    have H := congrFun (congrFun (hrow t) i) x
    have R := congrFun (hrec t) x
    simp only [rvMul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at H R
    simp only [rvMul_apply, Pi.add_apply, map_sub, map_smul, hE1 t, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    exact (rowN_iff hD i (z := fun j => z t j x) (E := fun j => 𝔼.E t (z (t + 1) j) x) R).mp
      (by linear_combination H)
  · rw [hrec t, hD.2]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.sum_apply,
      mul_sub, Finset.sum_sub_distrib, add_mul, Finset.sum_mul]
    have : ∑ j, φ j * (ω j * s t x) = ∑ j, φ j * ω j * s t x :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    ring

/-- **Woodford (2003), (1.31)–(1.33), p. 335 (uniqueness and solution form).** Under the
Blanchard–Kahn condition, every bounded adapted solution of the one-predetermined-variable
system has `z_t = ω s_t + ∑_{j ≥ 0} ψ_j E_t g_{t+j}` with `ψ_j = Gʲ w`. -/
theorem predSysN_formula {n : ℕ} {P N : Matrix (Fin n) (Fin n) ℝ} {h b φ ω : Fin n → ℝ}
    {ρ lam : ℝ} (hBK : BKCondition P N h φ ρ lam ω) {g : ℕ → Ω → ℝ} {Mg : ℝ}
    (hg : ∀ t ω, |g t ω| ≤ Mg) (hga : 𝔼.Adapted g) {z : ℕ → Fin n → Ω → ℝ}
    {s : ℕ → Ω → ℝ} (hsys : PredSysN 𝔼 P N h b φ ρ g z s) (hza : VAdapted 𝔼 z)
    (hsa : 𝔼.Adapted s) (hzb : VBounded z) (hsb : BoundedProc s) :
    (fun t i => z t i - ω i • s t) =
      fwdVec 𝔼 (predG P N φ ω) (fun t i => predW P N b φ ω i • g t) ∧
    ∀ t, s (t + 1) = lam • s t + ∑ j, φ j • (z t j - ω j • s t) := by
  obtain ⟨hD, -, hM, hG⟩ := hBK
  obtain ⟨Cb, r, -, hr0, hr1, hpow⟩ := pow_entry_bound _ hG
  obtain ⟨hres, hrec⟩ := predSysN_reduce 𝔼 hD hsys hza hsa
  set zh : ℕ → Fin n → Ω → ℝ := fun t i => z t i - ω i • s t with hzh
  have hFz : FSolves 𝔼 (predG P N φ ω) (fun t i => predW P N b φ ω i • g t) zh :=
    (res_iff_fsolves 𝔼 hM g zh).mp hres
  have hwb : ∀ t i x, |predW P N b φ ω i • g t x| ≤
      (∑ i, |predW P N b φ ω i|) * Mg := by
    intro t i x
    simp only [smul_eq_mul, abs_mul]
    exact mul_le_mul (Finset.single_le_sum (f := fun i => |predW P N b φ ω i|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)) (hg t x) (abs_nonneg _)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hwa : VAdapted 𝔼 (fun t i => predW P N b φ ω i • g t) := by
    intro t i
    simp only [map_smul, hga t]
  obtain ⟨hFs, hFa, hFb⟩ := fwdVec_spec 𝔼 hr0.le hr1 hpow hwb hwa
  have hzha : VAdapted 𝔼 zh := by
    intro t i
    simp only [hzh, map_sub, map_smul, hza t i, hsa t]
  have hzhb : VBounded zh := by
    obtain ⟨Mz, hMz⟩ := hzb
    obtain ⟨Ms, hMs⟩ := hsb
    refine ⟨Mz + (∑ i, |ω i|) * Ms, fun t i x => ?_⟩
    simp only [hzh, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have hMs0 : 0 ≤ Ms := (abs_nonneg _).trans (hMs t x)
    have hωi : |ω i| ≤ ∑ i, |ω i| :=
      Finset.single_le_sum (f := fun i => |ω i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    refine (abs_sub _ _).trans (add_le_add (hMz t i x) ?_)
    rw [abs_mul]
    exact mul_le_mul hωi (hMs t x) (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  exact ⟨fsolves_unique 𝔼 hr0.le hr1 hpow hFz hFs hzha hFa hzhb hFb, hrec⟩

/-- **Woodford (2003), (1.31)–(1.33), p. 335 (coefficient form).** Under the Blanchard–Kahn
condition every bounded adapted solution has
`z_{t,i} = ω_i s_t + ∑_{k ≥ 0} ψ_{k,i} E_t g_{t+k}` with `ψ_k = Gᵏ w`. -/
theorem predSysN_solution_form {n : ℕ} {P N : Matrix (Fin n) (Fin n) ℝ} {h b φ ω : Fin n → ℝ}
    {ρ lam : ℝ} (hBK : BKCondition P N h φ ρ lam ω) {g : ℕ → Ω → ℝ} {Mg : ℝ}
    (hg : ∀ t ω, |g t ω| ≤ Mg) (hga : 𝔼.Adapted g) {z : ℕ → Fin n → Ω → ℝ}
    {s : ℕ → Ω → ℝ} (hsys : PredSysN 𝔼 P N h b φ ρ g z s) (hza : VAdapted 𝔼 z)
    (hsa : 𝔼.Adapted s) (hzb : VBounded z) (hsb : BoundedProc s) (t : ℕ) (i : Fin n) (x : Ω) :
    z t i x = ω i * s t x + ∑' k, ((predG P N φ ω ^ k).mulVec (predW P N b φ ω)) i *
      𝔼.E t (g (t + k)) x := by
  have h1 := congrFun (congrFun (congrFun
    (predSysN_formula 𝔼 hBK hg hga hsys hza hsa hzb hsb).1 t) i) x
  rw [fwdS_scalar, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1
  linarith

/-- **Woodford (2003), (1.30)–(1.33), p. 335 (existence and uniqueness).** Under the
Blanchard–Kahn condition, for every bounded adapted forcing `g` and every initial value `s_0`
known at date 0, the one-predetermined-variable system has exactly one bounded adapted
solution `(z, s)` with `s_0` given. -/
theorem predSysN_existsUnique {n : ℕ} {P N : Matrix (Fin n) (Fin n) ℝ} {h b φ ω : Fin n → ℝ}
    {ρ lam : ℝ} (hBK : BKCondition P N h φ ρ lam ω) {g : ℕ → Ω → ℝ} {Mg : ℝ}
    (hg : ∀ t ω, |g t ω| ≤ Mg) (hga : 𝔼.Adapted g) {s0 : Ω → ℝ} {B : ℝ}
    (hs0 : 𝔼.E 0 s0 = s0) (hs0b : ∀ x, |s0 x| ≤ B) :
    ∃! p : (ℕ → Fin n → Ω → ℝ) × (ℕ → Ω → ℝ), PredSysN 𝔼 P N h b φ ρ g p.1 p.2 ∧
      p.2 0 = s0 ∧ VAdapted 𝔼 p.1 ∧ 𝔼.Adapted p.2 ∧ VBounded p.1 ∧ BoundedProc p.2 := by
  have hBK' := hBK
  obtain ⟨hD, hl, hM, hG⟩ := hBK
  obtain ⟨Cb, r, -, hr0, hr1, hpow⟩ := pow_entry_bound _ hG
  set G := predG P N φ ω
  set wv := predW P N b φ ω
  have hwb : ∀ t i x, |(fun t i => wv i • g t) t i x| ≤ (∑ i, |wv i|) * Mg := by
    intro t i x
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul (Finset.single_le_sum (f := fun i => |wv i|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)) (hg t x) (abs_nonneg _)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hwa : VAdapted 𝔼 (fun t i => wv i • g t) := by
    intro t i
    simp only [map_smul, hga t]
  obtain ⟨hFs, hFa, ⟨MF, hMF⟩⟩ := fwdVec_spec 𝔼 hr0.le hr1 hpow hwb hwa
  set F := fwdVec 𝔼 G (fun t i => wv i • g t) with hFdef
  set sp := sPathN lam φ F s0 with hspdef
  have hsp1 : ∀ t, sp (t + 1) = lam • sp t + ∑ j, φ j • F t j := fun t => rfl
  have hspa : 𝔼.Adapted sp := by
    intro t
    induction t with
    | zero => exact hs0
    | succ t ih =>
      rw [hsp1 t, map_add, map_smul, map_sum,
        ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hFa t j)]
  have hE1 : ∀ t, 𝔼.E t (sp (t + 1)) = sp (t + 1) := by
    intro t
    rw [hsp1 t, map_add, map_smul, hspa t, map_sum]
    simp only [map_smul, hFa t]
  have hspb : BoundedProc sp := by
    refine ⟨max B ((∑ j, |φ j|) * MF / (1 - |lam|)), fun t x => ?_⟩
    refine abs_rec_le hl (u := fun t => ∑ j, φ j * F t j x) (x := fun t => sp t x)
      (fun t => ?_) (hs0b x) (fun t => ?_) t
    · calc |∑ j, φ j * F t j x| ≤ ∑ j, |φ j * F t j x| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, |φ j| * MF := Finset.sum_le_sum fun j _ => by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hMF t j x) (abs_nonneg _)
        _ = (∑ j, |φ j|) * MF := by rw [Finset.sum_mul]
    · simp only [hsp1 t, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  set zp : ℕ → Fin n → Ω → ℝ := fun t i => ω i • sp t + F t i with hzpdef
  have hzpa : VAdapted 𝔼 zp := by
    intro t i
    simp only [hzpdef, map_add, map_smul, hspa t, hFa t i]
  have hzpb : VBounded zp := by
    obtain ⟨Ms, hMs⟩ := hspb
    refine ⟨(∑ i, |ω i|) * Ms + MF, fun t i x => ?_⟩
    simp only [hzpdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hωi : |ω i| ≤ ∑ i, |ω i| :=
      Finset.single_le_sum (f := fun i => |ω i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    refine (abs_add_le _ _).trans (add_le_add ?_ (hMF t i x))
    rw [abs_mul]
    exact mul_le_mul hωi (hMs t x) (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hrec : ∀ t, sp (t + 1) = ρ • sp t + ∑ j, φ j • zp t j := by
    intro t
    rw [hsp1 t, hD.2]
    funext x
    simp only [hzpdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, mul_add,
      Finset.sum_add_distrib, add_mul, Finset.sum_mul]
    have : ∑ j, φ j * (ω j * sp t x) = ∑ j, φ j * ω j * sp t x :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    ring
  have hres := (res_iff_fsolves 𝔼 hM g F).mpr hFs
  have hsys : PredSysN 𝔼 P N h b φ ρ g zp sp := by
    refine ⟨fun t => ?_, hrec⟩
    funext i x
    have R := congrFun (hrec t) x
    have H := congrFun (congrFun (hres t) i) x
    simp only [rvMul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply] at R H ⊢
    have e0 : ∀ j, zp t j x - ω j * sp t x = F t j x := fun j => by simp [hzpdef]
    have f0 : ∀ j, 𝔼.E t (zp (t + 1) j) x - ω j * sp (t + 1) x = 𝔼.E t (F (t + 1) j) x := by
      intro j
      simp only [hzpdef, map_add, map_smul, hE1 t, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have key := (rowN_iff hD i (b := b) (z := fun j => zp t j x)
      (E := fun j => 𝔼.E t (zp (t + 1) j) x) (gt := g t x) R).mpr (by
        simp only [e0, f0]
        exact H)
    linear_combination key
  refine ⟨(zp, sp), ⟨hsys, rfl, hzpa, hspa, hzpb, hspb⟩, ?_⟩
  rintro ⟨z', s'⟩ ⟨hsys', hs0', hza', hsa', hzb', hsb'⟩
  dsimp only at hsys' hs0' hza' hsa' hzb' hsb'
  obtain ⟨hF', hrec'⟩ := predSysN_formula 𝔼 hBK' hg hga hsys' hza' hsa' hzb' hsb'
  have hzh : ∀ t i, z' t i - ω i • s' t = F t i := fun t i =>
    congrFun (congrFun hF' t) i
  have hs : s' = sp := by
    funext t
    induction t with
    | zero => exact hs0'
    | succ t ih =>
      rw [hrec' t, hsp1 t, ih]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [← ih, hzh t j]
  have hz : z' = zp := by
    funext t i
    have := hzh t i
    rw [hs] at this
    simp only [hzpdef]
    rw [← this]
    abel
  rw [hs, hz]

/-! #### The habit model (1.25), (1.26), (1.30) as a system with one predetermined variable -/

/-- Woodford (2003), eq. (1.30), p. 335, as printed:
`î_t = ī_t + φ_π(π_t − π̄) + φ_x(x_t − x̄)` (no `/4` on `φ_x`, unlike Ch. 4 (1.14) and Ch. 5
(3.33); see `taylor130_iff_quarter`). -/
def Taylor130 (φπ φx πbar xbar : ℝ) (π x i ibar : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = ibar t + φπ • (π t - fun _ => πbar) + φx • (x t - fun _ => xbar)

omit 𝔼 in
/-- **Woodford (2003), (1.30), p. 335 (survey error 7, confirmed).** The printed rule (1.30)
omits the `/4` on `φ_x` that Ch. 4 (1.14) and Ch. 5 (3.33) carry (output gap at annual rates
vs. quarterly interest): (1.30) with coefficient `φ_x` is the `/4` rule with coefficient `4φ_x`.
So the Ch. 4 Taylor-principle threshold `φ_π + (1 − β)φ_x/(4κ) > 1` must be read with `4φ_x`
for the rule as printed. -/
theorem taylor130_iff_quarter (φπ φx πbar xbar : ℝ) (π x i ibar : ℕ → Ω → ℝ) :
    Taylor130 φπ φx πbar xbar π x i ibar ↔
      ∀ t, i t = ibar t + φπ • (π t - fun _ => πbar) + ((4 * φx) / 4) • (x t - fun _ => xbar) := by
  unfold Taylor130
  rw [show 4 * φx / 4 = φx by ring]

/-- Woodford (2003), p. 335: the output gap `x̄` consistent with `π̄` under (1.26),
`(1 − β)π̄ = ξ_p(ω + φ(1 − η)(1 − βη)) x̄`. -/
def XbarConsistent (ξp ω vphi β η πbar xbar : ℝ) : Prop :=
  (1 - β) * πbar = ξp * (ω + vphi * (1 - η) * (1 - β * η)) * xbar

/-- Woodford (2003), (1.25)–(1.26), p. 335: `P` of the system in `z_t = (π̂_t, x̂_t, E_t x̂_{t+1})`
(rows: AS (1.26), IS (1.25) with (1.30) substituted, definition of the third variable). -/
noncomputable def habP (ξp ω vphi β η φπ φx : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, -(ξp * (ω + vphi * (1 + β * η ^ 2))), ξp * vphi * β * η;
    vphi⁻¹ * φπ, 1 + β * η ^ 2 + η + vphi⁻¹ * φx, -(β * η);
    0, 0, 1]

/-- Woodford (2003), (1.25)–(1.26), p. 335: `N`, the coefficients of `E_t z_{t+1}`. -/
noncomputable def habN (vphi β η : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![β, 0, 0; vphi⁻¹, 1 + β * η ^ 2, -(β * η); 0, 1, 0]

/-- Woodford (2003), p. 335: the loading of the predetermined `s_t = x_{t−1} − x̄`. -/
noncomputable def habH (ξp vphi η : ℝ) : Fin 3 → ℝ := ![-(ξp * vphi * η), η, 0]

/-- Woodford (2003), p. 335: the loading of the composite disturbance `r̂ⁿ_t − ī_t + π̄`. -/
noncomputable def habBv (vphi : ℝ) : Fin 3 → ℝ := ![0, vphi⁻¹, 0]

/-- Woodford (2003), p. 335: `s_{t+1} = x_t − x̄` selects the second variable. -/
def habSel : Fin 3 → ℝ := ![0, 1, 0]

/-- Woodford (2003), p. 335: the vector `z_t = (π_t − π̄, x_t − x̄, E_t x_{t+1} − x̄)`. -/
def habVec (πbar xbar : ℝ) (π x : ℕ → Ω → ℝ) : ℕ → Fin 3 → Ω → ℝ :=
  fun t => ![π t - fun _ => πbar, x t - fun _ => xbar, 𝔼.E t (x (t + 1)) - fun _ => xbar]

/-- Woodford (2003), p. 335: the predetermined variable `s_t = x_{t−1} − x̄`. -/
def habS (xbar : ℝ) (xm1 : Ω → ℝ) (x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => lag xm1 x t - fun _ => xbar

/-- Woodford (2003), p. 335: the composite disturbance `r̂ⁿ_t − ī_t + π̄`. -/
def habG (πbar : ℝ) (rn ibar : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => rn t - ibar t + fun _ => πbar

omit 𝔼 in
/-- Woodford (2003), p. 335: row 0 of `P z`. -/
theorem habP_row0 (ξp ω vphi β η φπ φx : ℝ) (v : Fin 3 → Ω → ℝ) (x : Ω) :
    rvMul (habP ξp ω vphi β η φπ φx) v 0 x = v 0 x -
      ξp * (ω + vphi * (1 + β * η ^ 2)) * v 1 x + ξp * vphi * β * η * v 2 x := by
  simp [rvMul_apply, habP, Fin.sum_univ_three]
  ring

omit 𝔼 in
/-- Woodford (2003), p. 335: row 1 of `P z`. -/
theorem habP_row1 (ξp ω vphi β η φπ φx : ℝ) (v : Fin 3 → Ω → ℝ) (x : Ω) :
    rvMul (habP ξp ω vphi β η φπ φx) v 1 x = vphi⁻¹ * φπ * v 0 x +
      (1 + β * η ^ 2 + η + vphi⁻¹ * φx) * v 1 x - β * η * v 2 x := by
  simp [rvMul_apply, habP, Fin.sum_univ_three]
  ring

omit 𝔼 in
/-- Woodford (2003), p. 335: row 2 of `P z`. -/
theorem habP_row2 (ξp ω vphi β η φπ φx : ℝ) (v : Fin 3 → Ω → ℝ) (x : Ω) :
    rvMul (habP ξp ω vphi β η φπ φx) v 2 x = v 2 x := by
  simp [rvMul_apply, habP, Fin.sum_univ_three]

omit 𝔼 in
/-- Woodford (2003), p. 335: row 0 of `N E z`. -/
theorem habN_row0 (vphi β η : ℝ) (v : Fin 3 → Ω → ℝ) (x : Ω) :
    rvMul (habN vphi β η) v 0 x = β * v 0 x := by
  simp [rvMul_apply, habN, Fin.sum_univ_three]

omit 𝔼 in
/-- Woodford (2003), p. 335: row 1 of `N E z`. -/
theorem habN_row1 (vphi β η : ℝ) (v : Fin 3 → Ω → ℝ) (x : Ω) :
    rvMul (habN vphi β η) v 1 x =
      vphi⁻¹ * v 0 x + (1 + β * η ^ 2) * v 1 x - β * η * v 2 x := by
  simp [rvMul_apply, habN, Fin.sum_univ_three]
  ring

omit 𝔼 in
/-- Woodford (2003), p. 335: row 2 of `N E z`. -/
theorem habN_row2 (vphi β η : ℝ) (v : Fin 3 → Ω → ℝ) (x : Ω) :
    rvMul (habN vphi β η) v 2 x = v 1 x := by
  simp [rvMul_apply, habN, Fin.sum_univ_three]

/-- Woodford (2003), (1.25), (1.26), (1.30), p. 335: the habit model — the IS relation (1.25),
the AS relation (1.26) and the Taylor rule (1.30). -/
def HabitModel (ξp ω vphi β η φπ φx πbar xbar : ℝ) (xm1 : Ω → ℝ)
    (π x i ibar rn : ℕ → Ω → ℝ) : Prop :=
  IS125 𝔼 vphi β η xm1 x i π rn ∧ AS126 𝔼 ξp ω vphi β η xm1 x π ∧
    Taylor130 φπ φx πbar xbar π x i ibar

/-- **Woodford (2003), p. 335: the habit model is a system with one predetermined variable.**
For adapted `π`, `x` (and `x_{−1}` known at 0), given the Taylor rule (1.30) and `x̄`
consistent with `π̄`, (1.25) and (1.26) hold iff `z_t = (π_t − π̄, x_t − x̄, E_t x_{t+1} − x̄)`
and `s_t = x_{t−1} − x̄` solve `P z_t = N E_t z_{t+1} + h s_t + b g_t`, `s_{t+1} = (0, 1, 0)·z_t`
with `g_t = r̂ⁿ_t − ī_t + π̄`. -/
theorem habit_iff_predSys {ξp ω vphi β η φπ φx πbar xbar : ℝ} (hφ : vphi ≠ 0)
    (hxbar : XbarConsistent ξp ω vphi β η πbar xbar) {xm1 : Ω → ℝ} {π x i ibar rn : ℕ → Ω → ℝ}
    (hx : 𝔼.Adapted x) (hT : Taylor130 φπ φx πbar xbar π x i ibar) :
    (IS125 𝔼 vphi β η xm1 x i π rn ∧ AS126 𝔼 ξp ω vphi β η xm1 x π) ↔
      PredSysN 𝔼 (habP ξp ω vphi β η φπ φx) (habN vphi β η) (habH ξp vphi η) (habBv vphi)
        habSel 0 (habG πbar rn ibar) (habVec 𝔼 πbar xbar π x) (habS xbar xm1 x) := by
  unfold XbarConsistent at hxbar
  have hrec : ∀ t, habS xbar xm1 x (t + 1) = (0 : ℝ) • habS xbar xm1 x t +
      ∑ j, habSel j • habVec 𝔼 πbar xbar π x t j := by
    intro t
    funext y
    simp [habS, habSel, habVec, lag, Fin.sum_univ_three]
  -- pointwise values
  have hz0 : ∀ t y, habVec 𝔼 πbar xbar π x t 0 y = π t y - πbar := fun t y => rfl
  have hz1 : ∀ t y, habVec 𝔼 πbar xbar π x t 1 y = x t y - xbar := fun t y => rfl
  have hz2 : ∀ t y, habVec 𝔼 πbar xbar π x t 2 y = 𝔼.E t (x (t + 1)) y - xbar :=
    fun t y => rfl
  have hE0 : ∀ t y, 𝔼.E t (habVec 𝔼 πbar xbar π x (t + 1) 0) y = 𝔼.E t (π (t + 1)) y - πbar := by
    intro t y
    simp [habVec, map_sub, 𝔼.const]
  have hE1 : ∀ t y, 𝔼.E t (habVec 𝔼 πbar xbar π x (t + 1) 1) y = 𝔼.E t (x (t + 1)) y - xbar := by
    intro t y
    simp [habVec, map_sub, 𝔼.const]
  have hE2 : ∀ t y, 𝔼.E t (habVec 𝔼 πbar xbar π x (t + 1) 2) y =
      𝔼.E t (x (t + 2)) y - xbar := by
    intro t y
    simp [habVec, map_sub, 𝔼.const, 𝔼.tower (Nat.le_succ t)]
  have hs : ∀ t y, habS xbar xm1 x t y = lag xm1 x t y - xbar := fun t y => rfl
  have hg : ∀ t y, habG πbar rn ibar t y = rn t y - ibar t y + πbar := fun t y => rfl
  have hxt : ∀ t y, xTilde 𝔼 β η xm1 x t y = x t y - η * lag xm1 x t y -
      β * η * (𝔼.E t (x (t + 1)) y - η * x t y) := by
    intro t y
    simp [xTilde, map_sub, map_smul, hx t]
  have hExt : ∀ t y, 𝔼.E t (xTilde 𝔼 β η xm1 x (t + 1)) y = 𝔼.E t (x (t + 1)) y - η * x t y -
      β * η * (𝔼.E t (x (t + 2)) y - η * 𝔼.E t (x (t + 1)) y) := by
    intro t y
    simp [xTilde, map_sub, map_smul, hx t, lag, 𝔼.tower (Nat.le_succ t)]
  have hTy : ∀ t y, i t y = ibar t y + φπ * (π t y - πbar) + φx * (x t y - xbar) := by
    intro t y
    have := congrFun (hT t) y
    simpa using this
  have hφi : vphi * vphi⁻¹ = 1 := mul_inv_cancel₀ hφ
  constructor
  · rintro ⟨hIS, hAS⟩
    refine ⟨fun t => ?_, hrec⟩
    funext j y
    have A := congrFun (hAS t) y
    have I := congrFun (hIS t) y
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at A I ⊢
    rw [hxt] at A I
    rw [hExt] at I
    fin_cases j
    · simp only [Fin.zero_eta, habP_row0, habN_row0, hz0, hz1, hz2, hE0, hs, hg, habH, habBv,
        Matrix.cons_val_zero]
      linear_combination A - hxbar
    · simp only [Fin.mk_one, habP_row1, habN_row1, hz0, hz1, hz2, hE0, hE1, hE2, hs, hg, habH,
        habBv, Matrix.cons_val_one, Matrix.cons_val_zero]
      linear_combination I - vphi⁻¹ * hTy t y
    · simp only [Fin.reduceFinMk, habP_row2, habN_row2, hz2, hE1, habH, habBv,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      ring
  · rintro ⟨hrow, -⟩
    have R : ∀ t (j : Fin 3) y, rvMul (habP ξp ω vphi β η φπ φx) (habVec 𝔼 πbar xbar π x t) j y =
        rvMul (habN vphi β η) (fun k => 𝔼.E t (habVec 𝔼 πbar xbar π x (t + 1) k)) j y +
          (habH ξp vphi η j * habS xbar xm1 x t y + habBv vphi j * habG πbar rn ibar t y) := by
      intro t j y
      have := congrFun (congrFun (hrow t) j) y
      simpa using this
    refine ⟨fun t => ?_, fun t => ?_⟩
    · funext y
      have R1 := R t 1 y
      simp only [habP_row1, habN_row1, hz0, hz1, hz2, hE0, hE1, hE2, hs, hg, habH,
        habBv, Matrix.cons_val_one, Matrix.cons_val_zero] at R1
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hxt, hExt]
      linear_combination R1 + vphi⁻¹ * hTy t y
    · funext y
      have R0 := R t 0 y
      simp only [habP_row0, habN_row0, hz0, hz1, hz2, hE0, hs, hg, habH, habBv,
        Matrix.cons_val_zero] at R0
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hxt]
      linear_combination R0 + hxbar

/-- Woodford (2003), (1.31)–(1.33), p. 335: the response coefficients `ψ_k = Gᵏ w` are
geometrically dominated, so the series `∑_k ψ_{k,i} E_t g_{t+k}` converge absolutely. -/
theorem predSysN_summable {n : ℕ} {P N : Matrix (Fin n) (Fin n) ℝ} {h b φ ω : Fin n → ℝ}
    {ρ lam : ℝ} (hBK : BKCondition P N h φ ρ lam ω) {g : ℕ → Ω → ℝ} {Mg : ℝ}
    (hg : ∀ t ω, |g t ω| ≤ Mg) (t : ℕ) (i : Fin n) (x : Ω) :
    Summable fun k => ((predG P N φ ω ^ k).mulVec (predW P N b φ ω)) i *
      𝔼.E t (g (t + k)) x := by
  obtain ⟨-, -, -, hG⟩ := hBK
  obtain ⟨Cb, r, -, hr0, hr1, hpow⟩ := pow_entry_bound _ hG
  set W := ∑ j, |predW P N b φ ω j|
  refine Summable.of_norm_bounded
    (((summable_geometric_of_lt_one hr0.le hr1).mul_left (Cb * W)).mul_right Mg) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have hM0 : 0 ≤ Mg := (abs_nonneg _).trans (hg t x)
  have hv : |((predG P N φ ω ^ k).mulVec (predW P N b φ ω)) i| ≤ Cb * W * r ^ k := by
    simp only [Matrix.mulVec, dotProduct]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |(predG P N φ ω ^ k) i j * predW P N b φ ω j|
        ≤ ∑ j, Cb * r ^ k * |predW P N b φ ω j| := Finset.sum_le_sum fun j _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hpow k i j) (abs_nonneg _)
      _ = Cb * W * r ^ k := by rw [← Finset.mul_sum]; ring
  exact mul_le_mul hv (𝔼.abs_E_le (hg (t + k)) t x) (abs_nonneg _)
    ((abs_nonneg _).trans hv)

/-- **Woodford (2003), (1.30)–(1.33), p. 335: existence and uniqueness in the habit model.**
Under the Blanchard–Kahn condition for the system of `habit_iff_predSys` (the determinacy
condition, stated exactly as `BKCondition`), for bounded adapted `r̂ⁿ`, `ī` and a bounded
`x_{−1}` known at date 0, there is exactly one bounded adapted `(π, x, î)` satisfying (1.25),
(1.26) and (1.30). Any `ExpectationSystem`. -/
theorem habit_existsUnique {ξp ω vphi β η φπ φx πbar xbar lam : ℝ} {ωv : Fin 3 → ℝ}
    (hφ : vphi ≠ 0) (hxbar : XbarConsistent ξp ω vphi β η πbar xbar)
    (hBK : BKCondition (habP ξp ω vphi β η φπ φx) (habN vphi β η) (habH ξp vphi η) habSel 0
      lam ωv)
    {rn ibar : ℕ → Ω → ℝ} (hrn : BoundedProc rn) (hib : BoundedProc ibar)
    (hrna : 𝔼.Adapted rn) (hiba : 𝔼.Adapted ibar) {xm1 : Ω → ℝ} {B : ℝ}
    (hm0 : 𝔼.E 0 xm1 = xm1) (hmb : ∀ y, |xm1 y| ≤ B) :
    ∃! p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      HabitModel 𝔼 ξp ω vphi β η φπ φx πbar xbar xm1 p.1 p.2.1 p.2.2 ibar rn ∧
      𝔼.Adapted p.1 ∧ 𝔼.Adapted p.2.1 ∧ 𝔼.Adapted p.2.2 ∧
      BoundedProc p.1 ∧ BoundedProc p.2.1 ∧ BoundedProc p.2.2 := by
  obtain ⟨Mr, hMr⟩ := hrn
  obtain ⟨Mi, hMi⟩ := hib
  set g := habG πbar rn ibar with hgdef
  have hgb : ∀ t y, |g t y| ≤ Mr + Mi + |πbar| := by
    intro t y
    simp only [hgdef, habG, Pi.add_apply, Pi.sub_apply]
    calc |rn t y - ibar t y + πbar| ≤ |rn t y| + |ibar t y| + |πbar| := by
          refine (abs_add_le _ _).trans ?_
          exact add_le_add (abs_sub _ _) le_rfl
      _ ≤ Mr + Mi + |πbar| := by
          gcongr
          · exact hMr t y
          · exact hMi t y
  have hga : 𝔼.Adapted g := by
    intro t
    simp only [hgdef, habG, map_add, map_sub, 𝔼.const, hrna t, hiba t]
  set s0 : Ω → ℝ := xm1 - fun _ => xbar with hs0def
  have hs0 : 𝔼.E 0 s0 = s0 := by rw [hs0def, map_sub, hm0, 𝔼.const]
  have hs0b : ∀ y, |s0 y| ≤ B + |xbar| := fun y => by
    simp only [hs0def, Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hmb y) le_rfl)
  obtain ⟨⟨z, s⟩, ⟨hsys, hsz, hza, hsa, hzb, hsb⟩, huniq⟩ :=
    predSysN_existsUnique 𝔼 (b := habBv vphi) hBK hgb hga hs0 hs0b
  dsimp only at hsys hsz hza hsa hzb hsb
  -- the candidate equilibrium
  set π : ℕ → Ω → ℝ := fun t => z t 0 + fun _ => πbar with hπdef
  set x : ℕ → Ω → ℝ := fun t => z t 1 + fun _ => xbar with hxdef
  set i : ℕ → Ω → ℝ := fun t => ibar t + φπ • (π t - fun _ => πbar) +
    φx • (x t - fun _ => xbar) with hidef
  have hxa : 𝔼.Adapted x := by
    intro t; simp only [hxdef, map_add, hza t 1, 𝔼.const]
  have hπa : 𝔼.Adapted π := by
    intro t; simp only [hπdef, map_add, hza t 0, 𝔼.const]
  have hT : Taylor130 φπ φx πbar xbar π x i ibar := fun t => rfl
  have hrow2 : ∀ t, z t 2 = 𝔼.E t (z (t + 1) 1) := by
    intro t
    funext y
    have := congrFun (congrFun (hsys.1 t) 2) y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, habP_row2, habN_row2] at this
    simpa [habH, habBv] using this
  have hS : habS xbar xm1 x = s := by
    funext t
    induction t with
    | zero => simp only [habS, lag]; exact hsz.symm
    | succ t _ =>
      rw [hsys.2 t]
      funext y
      simp [habS, lag, hxdef, habSel, Fin.sum_univ_three]
  have hV : habVec 𝔼 πbar xbar π x = z := by
    funext t j
    fin_cases j
    · simp [habVec, hπdef]
    · simp [habVec, hxdef]
    · simp only [habVec, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, hxdef, map_add, 𝔼.const, hrow2 t]
      abel
  have hmodel : HabitModel 𝔼 ξp ω vphi β η φπ φx πbar xbar xm1 π x i ibar rn := by
    have := (habit_iff_predSys 𝔼 hφ hxbar (rn := rn) hxa hT).mpr (by rw [hV, hS]; exact hsys)
    exact ⟨this.1, this.2, hT⟩
  obtain ⟨Mz, hMz⟩ := hzb
  refine ⟨(π, x, i), ⟨hmodel, hπa, hxa, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro t
    simp only [hidef, map_add, map_smul, map_sub, hiba t, hπa t, hxa t, 𝔼.const]
  · exact ⟨Mz + |πbar|, fun t y => (abs_add_le _ _).trans (add_le_add (hMz t 0 y) le_rfl)⟩
  · exact ⟨Mz + |xbar|, fun t y => (abs_add_le _ _).trans (add_le_add (hMz t 1 y) le_rfl)⟩
  · refine ⟨Mi + |φπ| * Mz + |φx| * Mz, fun t y => ?_⟩
    simp only [hidef, hπdef, hxdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      add_sub_cancel_right]
    calc |ibar t y + φπ * z t 0 y + φx * z t 1 y|
        ≤ |ibar t y| + |φπ| * |z t 0 y| + |φx| * |z t 1 y| := by
          rw [← abs_mul, ← abs_mul]
          exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ Mi + |φπ| * Mz + |φx| * Mz := by
          gcongr
          · exact hMi t y
          · exact hMz t 0 y
          · exact hMz t 1 y
  · rintro ⟨π', x', i'⟩ ⟨⟨hIS', hAS', hT'⟩, hπa', hxa', -, ⟨Mπ, hMπ⟩, ⟨Mx, hMx⟩, -⟩
    dsimp only at hIS' hAS' hT' hπa' hxa' hMπ hMx
    have hsys' := (habit_iff_predSys 𝔼 hφ hxbar hxa' hT').mp ⟨hIS', hAS'⟩
    have hva : VAdapted 𝔼 (habVec 𝔼 πbar xbar π' x') := by
      intro t j
      fin_cases j
      · simp [habVec, map_sub, hπa' t, 𝔼.const]
      · simp [habVec, map_sub, hxa' t, 𝔼.const]
      · simp [habVec, map_sub, 𝔼.E_E_self, 𝔼.const]
    have hsa' : 𝔼.Adapted (habS xbar xm1 x') := by
      intro t
      simp only [habS, map_sub, lag_known 𝔼 hm0 hxa' t, 𝔼.const]
    have hvb : VBounded (habVec 𝔼 πbar xbar π' x') := by
      refine ⟨Mπ + |πbar| + (Mx + |xbar|), fun t j y => ?_⟩
      have hx0 : 0 ≤ Mx := (abs_nonneg _).trans (hMx 0 y)
      have hπ0 : 0 ≤ Mπ := (abs_nonneg _).trans (hMπ 0 y)
      fin_cases j
      · simp only [habVec, Fin.zero_eta, Matrix.cons_val_zero, Pi.sub_apply]
        have := (abs_sub _ _).trans (add_le_add (hMπ t y) (le_refl |πbar|))
        linarith [abs_nonneg xbar]
      · simp only [habVec, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.sub_apply]
        have := (abs_sub _ _).trans (add_le_add (hMx t y) (le_refl |xbar|))
        linarith [abs_nonneg πbar]
      · simp only [habVec, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons,
          Matrix.head_cons, Pi.sub_apply]
        have := (abs_sub _ _).trans (add_le_add (𝔼.abs_E_le (hMx (t + 1)) t y)
          (le_refl |xbar|))
        linarith [abs_nonneg πbar]
    have hsb' : BoundedProc (habS xbar xm1 x') := by
      refine ⟨max B Mx + |xbar|, fun t y => ?_⟩
      simp only [habS, Pi.sub_apply]
      refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
      cases t with
      | zero => exact (hmb y).trans (le_max_left _ _)
      | succ t => exact (hMx t y).trans (le_max_right _ _)
    have hs0' : habS xbar xm1 x' 0 = s0 := rfl
    have heq := huniq (habVec 𝔼 πbar xbar π' x', habS xbar xm1 x')
      ⟨hsys', hs0', hva, hsa', hvb, hsb'⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hv', -⟩ := heq
    have hπ' : π' = π := by
      funext t y
      have := congrFun (congrFun (congrFun hv' t) 0) y
      simp only [habVec, Matrix.cons_val_zero, Pi.sub_apply] at this
      simp only [hπdef, Pi.add_apply]
      linarith
    have hx' : x' = x := by
      funext t y
      have := congrFun (congrFun (congrFun hv' t) 1) y
      simp only [habVec, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.sub_apply] at this
      simp only [hxdef, Pi.add_apply]
      linarith
    have hi' : i' = i := by
      funext t
      rw [hT' t, hπ', hx']
    rw [hπ', hx', hi']

/-- Woodford (2003), p. 335: for bounded adapted `π`, `x` (and bounded `x_{−1}` known at 0) the
vector `z_t` and the predetermined `s_t` are bounded and adapted. -/
theorem habVec_props {πbar xbar B Mπ Mx : ℝ} {xm1 : Ω → ℝ} {π x : ℕ → Ω → ℝ}
    (hm0 : 𝔼.E 0 xm1 = xm1) (hmb : ∀ y, |xm1 y| ≤ B) (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x)
    (hMπ : ∀ t y, |π t y| ≤ Mπ) (hMx : ∀ t y, |x t y| ≤ Mx) :
    VAdapted 𝔼 (habVec 𝔼 πbar xbar π x) ∧ 𝔼.Adapted (habS xbar xm1 x) ∧
      VBounded (habVec 𝔼 πbar xbar π x) ∧ BoundedProc (habS xbar xm1 x) := by
  refine ⟨fun t j => ?_, fun t => ?_, ⟨Mπ + |πbar| + (Mx + |xbar|), fun t j y => ?_⟩,
    ⟨max B Mx + |xbar|, fun t y => ?_⟩⟩
  · fin_cases j
    · simp [habVec, map_sub, hπa t, 𝔼.const]
    · simp [habVec, map_sub, hxa t, 𝔼.const]
    · simp [habVec, map_sub, 𝔼.E_E_self, 𝔼.const]
  · simp only [habS, map_sub, lag_known 𝔼 hm0 hxa t, 𝔼.const]
  · fin_cases j
    · simp only [habVec, Fin.zero_eta, Matrix.cons_val_zero, Pi.sub_apply]
      have := (abs_sub _ _).trans (add_le_add (hMπ t y) (le_refl |πbar|))
      linarith [abs_nonneg xbar, (abs_nonneg _).trans (hMx 0 y)]
    · simp only [habVec, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.sub_apply]
      have := (abs_sub _ _).trans (add_le_add (hMx t y) (le_refl |xbar|))
      linarith [abs_nonneg πbar, (abs_nonneg _).trans (hMπ 0 y)]
    · simp only [habVec, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, Pi.sub_apply]
      have := (abs_sub _ _).trans (add_le_add (𝔼.abs_E_le (hMx (t + 1)) t y)
        (le_refl |xbar|))
      linarith [abs_nonneg πbar, (abs_nonneg _).trans (hMπ 0 y)]
  · simp only [habS, Pi.sub_apply]
    refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
    cases t with
    | zero => exact (hmb y).trans (le_max_left _ _)
    | succ t => exact (hMx t y).trans (le_max_right _ _)

/-- **Woodford (2003), (1.31)–(1.33), p. 335: the form of the determinate equilibrium.** Under
the Blanchard–Kahn condition, every bounded adapted equilibrium of the habit model satisfies
`π_t = π̄ + ω_π(x_{t−1} − x̄) + ∑_j ψ^π_j E_t(r̂ⁿ_{t+j} − ī_{t+j} + π̄)`,
`x_t = x̄ + ω_x(x_{t−1} − x̄) + ∑_j ψ^x_j E_t(⋯)`,
`î_t = ī_t + ω_i(x_{t−1} − x̄) + ∑_j ψ^i_j E_t(⋯)`, with `ω_π, ω_x` the decomposition
coefficients, `ψ_j = Gʲ w`, `ω_i = φ_π ω_π + φ_x ω_x`, `ψ^i_j = φ_π ψ^π_j + φ_x ψ^x_j` (all
series absolutely convergent). -/
theorem habit_solution_form {ξp ω vphi β η φπ φx πbar xbar lam : ℝ} {ωv : Fin 3 → ℝ}
    (hφ : vphi ≠ 0) (hxbar : XbarConsistent ξp ω vphi β η πbar xbar)
    (hBK : BKCondition (habP ξp ω vphi β η φπ φx) (habN vphi β η) (habH ξp vphi η) habSel 0
      lam ωv)
    {rn ibar : ℕ → Ω → ℝ} {Mg : ℝ} (hgb : ∀ t y, |habG πbar rn ibar t y| ≤ Mg)
    (hrna : 𝔼.Adapted rn) (hiba : 𝔼.Adapted ibar) {xm1 : Ω → ℝ} {B : ℝ}
    (hm0 : 𝔼.E 0 xm1 = xm1) (hmb : ∀ y, |xm1 y| ≤ B) {π x i : ℕ → Ω → ℝ}
    (hmod : HabitModel 𝔼 ξp ω vphi β η φπ φx πbar xbar xm1 π x i ibar rn)
    (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x) (hπb : BoundedProc π) (hxb : BoundedProc x)
    (t : ℕ) (y : Ω) :
    let ψ : ℕ → Fin 3 → ℝ := fun k => (predG (habP ξp ω vphi β η φπ φx) (habN vphi β η)
      habSel ωv ^ k).mulVec (predW (habP ξp ω vphi β η φπ φx) (habN vphi β η) (habBv vphi)
        habSel ωv)
    π t y = πbar + ωv 0 * (lag xm1 x t y - xbar) +
        ∑' k, ψ k 0 * 𝔼.E t (habG πbar rn ibar (t + k)) y ∧
      x t y = xbar + ωv 1 * (lag xm1 x t y - xbar) +
        ∑' k, ψ k 1 * 𝔼.E t (habG πbar rn ibar (t + k)) y ∧
      i t y = ibar t y + (φπ * ωv 0 + φx * ωv 1) * (lag xm1 x t y - xbar) +
        ∑' k, (φπ * ψ k 0 + φx * ψ k 1) * 𝔼.E t (habG πbar rn ibar (t + k)) y := by
  intro ψ
  obtain ⟨hIS, hAS, hT⟩ := hmod
  obtain ⟨Mπ, hMπ⟩ := hπb
  obtain ⟨Mx, hMx⟩ := hxb
  have hga : 𝔼.Adapted (habG πbar rn ibar) := by
    intro t
    simp only [habG, map_add, map_sub, 𝔼.const, hrna t, hiba t]
  have hsys := (habit_iff_predSys 𝔼 hφ hxbar hxa hT).mp ⟨hIS, hAS⟩
  obtain ⟨hva, hsa, hvb, hsb⟩ := habVec_props 𝔼 (πbar := πbar) (xbar := xbar) hm0 hmb hπa hxa
    hMπ hMx
  have f0 := predSysN_solution_form 𝔼 hBK hgb hga hsys hva hsa hvb hsb t 0 y
  have f1 := predSysN_solution_form 𝔼 hBK hgb hga hsys hva hsa hvb hsb t 1 y
  simp only [habVec, habS, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply] at f0 f1
  have s0 := predSysN_summable 𝔼 (b := habBv vphi) hBK hgb t 0 y
  have s1 := predSysN_summable 𝔼 (b := habBv vphi) hBK hgb t 1 y
  refine ⟨by linarith, by linarith, ?_⟩
  have hTy : i t y = ibar t y + φπ * (π t y - πbar) + φx * (x t y - xbar) := by
    have := congrFun (hT t) y
    simpa using this
  have hsplit : ∑' k, (φπ * ψ k 0 + φx * ψ k 1) * 𝔼.E t (habG πbar rn ibar (t + k)) y =
      φπ * ∑' k, ψ k 0 * 𝔼.E t (habG πbar rn ibar (t + k)) y +
        φx * ∑' k, ψ k 1 * 𝔼.E t (habG πbar rn ibar (t + k)) y := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (s0.mul_left φπ).tsum_add (s1.mul_left φx)]
    exact tsum_congr fun k => by ring
  rw [hsplit, hTy]
  change π t y - πbar = ωv 0 * (lag xm1 x t y - xbar) +
    ∑' k, ψ k 0 * 𝔼.E t (habG πbar rn ibar (t + k)) y at f0
  change x t y - xbar = ωv 1 * (lag xm1 x t y - xbar) +
    ∑' k, ψ k 1 * 𝔼.E t (habG πbar rn ibar (t + k)) y at f1
  linear_combination φπ * f0 + φx * f1

/-- Woodford (2003), p. 335 ("the model of Chapter 4 corresponds to the limiting case `η = 0`"):
for `η = 0` the predetermined variable drops out (`h = 0`), and `(λ, ω) = (0, 0)` is a
decomposition, so the Blanchard–Kahn condition reduces to all eigenvalues of `P⁻¹N` lying inside
the unit circle (the forward-looking Ch. 4 condition). -/
theorem habit_decomp_eta_zero (ξp ω vphi β φπ φx : ℝ) :
    DecompN (habP ξp ω vphi β 0 φπ φx) (habN vphi β 0) (habH ξp vphi 0) habSel 0 0 0 := by
  refine ⟨fun i => ?_, by simp⟩
  fin_cases i <;> simp [habH]

/-! #### Non-vacuity of the determinacy condition for `η > 0` -/

/-- Woodford (2003), Table 5.1, p. 341, with habit `η = 1/2`: `φ(η) = [(1 − βη)σ]⁻¹ = 32/101`
at `β = 0.99`, `σ = 1/0.16`. -/
theorem vphiOf_calibration : vphiOf (99 / 100) (25 / 4) (1 / 2) = 32 / 101 := by
  norm_num [vphiOf]

/-- Woodford (2003), p. 335: the inflation response of the calibrated Taylor rule,
`φ_π ≈ 1.4897` (chosen near 1.5 so that the stable root is exactly `1/6`). -/
noncomputable def calPhiPi : ℝ := 2734303130463 / 1835506100000

/-- Woodford (2003), p. 335: the output-gap response of the calibrated Taylor rule,
`φ_x ≈ 0.4912` (chosen near 0.5 so that one unstable root is exactly `1.03`). -/
noncomputable def calPhiX : ℝ := 9561701413801 / 19465542190500

/-- Woodford (2003), (1.31)–(1.33), p. 335: the decomposition coefficients at the calibration:
`ω_π = −100/118069`, `ω_x = λ = 1/6`, and `λ² = 1/36` for `E_t x_{t+1}`. -/
noncomputable def calOmega : Fin 3 → ℝ := ![-100 / 118069, 1 / 6, 1 / 36]

/-- Woodford (2003), p. 335: the forward-block matrix `G = M⁻¹N` at the calibration, exactly. -/
noncomputable def calG : Matrix (Fin 3) (Fin 3) ℝ :=
  !![3178113567050165 / 3258645648349632, 68594473454549663 / 6011641141484260947,
      -1391331978861000 / 286268625784964807;
    -61611797740496759 / 130345825933985280, 5687378416992779 / 10183267651092600,
      -2650011931875 / 16972112751821;
    -61611797740496759 / 782074955603911680, 66786984323548379 / 61099605906555600,
      -883337310625 / 33944225503642]

/-- **Woodford (2003), (1.30)–(1.33), p. 335: the determinacy condition is non-vacuous for
`η > 0`.** At the Table 5.1 calibration (`β = 0.99`, `σ⁻¹ = 0.16`, `ω = 0.47`,
`ξ_p = κ/(ω + σ⁻¹) = 0.024/0.63 = 4/105`) with habit `η = 1/2` and the Taylor rule
`φ_π ≈ 1.49`, `φ_x ≈ 0.49` (`calPhiPi`, `calPhiX`), `BKCondition` holds: the decomposition is
`λ = 1/6`, `ω = calOmega`; `det M ≠ 0`; and the characteristic polynomial of `G = M⁻¹N` factors
as `(w − 100/103)(w² − T w + D)` with `(T, D)` Schur–Cohn stable, so all eigenvalues of `G` lie
inside the unit circle (the system's roots are `1/6`, `1.03` and a complex pair of modulus
`≈ 2.5`). Only sufficiency of `BKCondition` is proved in this module; its necessity is proved
in the module `HabitNecessity` (`habit_determinate_iff_bk`). -/
theorem bkCondition_calibration :
    BKCondition (habP (4 / 105) (47 / 100) (32 / 101) (99 / 100) (1 / 2) calPhiPi calPhiX)
      (habN (32 / 101) (99 / 100) (1 / 2)) (habH (4 / 105) (32 / 101) (1 / 2)) habSel 0
      (1 / 6) calOmega := by
  set M := resMN (habP (4 / 105) (47 / 100) (32 / 101) (99 / 100) (1 / 2) calPhiPi calPhiX)
    (habN (32 / 101) (99 / 100) (1 / 2)) habSel calOmega with hMdef
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_fin_three]
    simp [hMdef, resMN, habP, habN, habSel, calOmega, calPhiPi, calPhiX, Fin.sum_univ_three]
    norm_num
  have hMG : M * calG = habN (32 / 101) (99 / 100) (1 / 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hMdef, Matrix.mul_apply, Fin.sum_univ_three, resMN, habP, habN, habSel, calOmega,
        calPhiPi, calPhiX, calG] <;> norm_num
  have hG : predG (habP (4 / 105) (47 / 100) (32 / 101) (99 / 100) (1 / 2) calPhiPi calPhiX)
      (habN (32 / 101) (99 / 100) (1 / 2)) habSel calOmega = calG := by
    change M⁻¹ * habN (32 / 101) (99 / 100) (1 / 2) = calG
    rw [← hMG, ← mul_assoc, Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hdet), one_mul]
  refine ⟨⟨fun i => ?_, ?_⟩, by norm_num [abs_of_pos], isUnit_iff_ne_zero.mpr hdet, ?_⟩
  · fin_cases i <;> simp [habP, habN, habH, calOmega, calPhiPi, calPhiX, Fin.sum_univ_three] <;>
      norm_num
  · simp [habSel, calOmega, Fin.sum_univ_three]
  · intro w hw
    rw [hG, Matrix.det_fin_three] at hw
    simp only [Matrix.scalar_apply, calG, Fin.isValue, Matrix.sub_apply,
      Matrix.diagonal_apply_eq, Matrix.map_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Complex.ofReal_div, Complex.ofReal_ofNat,
      Matrix.cons_val_one, Matrix.cons_val, Complex.ofReal_neg, ne_eq, Fin.reduceEq,
      not_false_eq_true, Matrix.diagonal_apply_ne, zero_sub, mul_neg, neg_mul, neg_neg,
      zero_ne_one, one_ne_zero] at hw
    have hf : (w - 100 / 103) * (w ^ 2 - ((141548595428273 / 263644469931200 : ℝ) : ℂ) * w +
        ((419761890009 / 2636444699312 : ℝ) : ℂ)) = 0 := by
      push_cast at hw ⊢
      linear_combination hw
    rcases mul_eq_zero.mp hf with h1 | h2
    · rw [sub_eq_zero.mp h1]
      norm_num [Complex.norm_div]
    · have hS : SchurStable (141548595428273 / 263644469931200) (419761890009 / 2636444699312) := by
        unfold SchurStable
        rw [abs_of_pos (by norm_num), abs_of_pos (by norm_num)]
        norm_num
      rcases eq_root_of_eq h2 with h | h
      · rw [h]; exact ((schurStable_iff_roots _ _).mp hS).1
      · rw [h]; exact ((schurStable_iff_roots _ _).mp hS).2

/-- **Woodford (2003), (1.30)–(1.33), p. 335, at a calibration with `η = 1/2`:** with the
Table 5.1 parameters and the Taylor rule of `bkCondition_calibration` (`π̄ = x̄ = 0`), for
bounded adapted `r̂ⁿ`, `ī` and bounded `x_{−1}` known at 0 there is exactly one bounded adapted
equilibrium `(π, x, î)` of (1.25), (1.26), (1.30). -/
theorem habit_existsUnique_calibration {rn ibar : ℕ → Ω → ℝ} (hrn : BoundedProc rn)
    (hib : BoundedProc ibar) (hrna : 𝔼.Adapted rn) (hiba : 𝔼.Adapted ibar) {xm1 : Ω → ℝ}
    {B : ℝ} (hm0 : 𝔼.E 0 xm1 = xm1) (hmb : ∀ y, |xm1 y| ≤ B) :
    ∃! p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      HabitModel 𝔼 (4 / 105) (47 / 100) (32 / 101) (99 / 100) (1 / 2) calPhiPi calPhiX 0 0
        xm1 p.1 p.2.1 p.2.2 ibar rn ∧
      𝔼.Adapted p.1 ∧ 𝔼.Adapted p.2.1 ∧ 𝔼.Adapted p.2.2 ∧
      BoundedProc p.1 ∧ BoundedProc p.2.1 ∧ BoundedProc p.2.2 :=
  habit_existsUnique 𝔼 (by norm_num) (by simp [XbarConsistent]) bkCondition_calibration
    hrn hib hrna hiba hm0 hmb

end Woodford.PolicyResponseDynamics.Habit
