/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Money in the utility function: the separable example

Galí (2015), Chapter 2, §2.5 and §2.5.1 (pp. 31–34).

Real balances `M_t/P_t` enter period utility (eq. (30)) and the flow budget constraint
becomes (31).

* `budget_rewrite`: eq. (32), the budget constraint in terms of total financial wealth
  `A_t = B_t + M_t`; the services of money cost `1 − Q_t = 1 − e^{−i_t}`
  (`price_of_money_services`, `one_sub_exp_neg_le`, `mul_exp_neg_le_one_sub_exp_neg`:
  `i e^{−i} ≤ 1 − e^{−i} ≤ i`, the book's `1 − e^{−i} ≃ i`).
* `miu_foc_necessary`: eq. (33) for a **general** differentiable utility of
  `(C, M/P)`: if the perturbation `P dC + (1 − Q) dM = 0` (p. 33) cannot raise utility,
  then `U_m = (1 − Q) U_c`.
* For the separable utility of p. 33 (`sepUtil`), `miu_static_optimum_iff`: the plan is
  optimal against every feasible perturbation **iff** `U_m / U_c = 1 − Q`
  (necessity by the first-order condition, sufficiency by concavity);
  `miu_static_optimum_iff_exp` is the same with `Q = e^{−i}`. Separability
  (`hasDerivAt_sepUtil_C`, `hasDerivAt_sepUtil_N`): `U_c` and `U_n` do not depend on real
  balances, so (7)–(10) are unchanged (p. 33).
* `money_demand_iff`: eq. (34), `M/P = C^{σ/ν} (1 − e^{−i})^{−1/ν}`, valid for `i > 0`;
  `no_money_demand_of_nonpos`: for `i ≤ 0` the optimality condition has no solution.
* `hasFDerivAt_logMoneyDemand`: eq. (35) as an **exact derivative**: the log money demand
  `(c, i) ↦ (σ/ν) c − ν⁻¹ log(1 − e^{−i})` has total derivative `(σ/ν, −η)` with
  `η = 1/(ν(e^i − 1))`; `eta_le`, `exp_neg_div_le_eta`: `e^{−i}/(νi) ≤ η ≤ 1/(νi)`, the
  book's `η ≃ 1/(νi)`.
* `hasFDerivAt_logMoneyDemand_unit`, `money_demand_unit_elastic`: eq. (36), the case
  `ν = σ`.

The utility functions and their concavity lemmas are restated from the Chapter 3 project
(`Household.lean`).
-/

namespace Gali.ClassicalMonetaryModel.MIUSeparable

open Filter Topology

/-! ### The budget constraint -/

/-- Galí (2015), eq. (32), p. 32 (**exact**): with total financial wealth `A_t = B_t + M_t`
and `A_{t−1} = B_{t−1} + M_{t−1}`, the flow budget constraint (31)
`P C + Q B + M ≤ B_{−1} + M_{−1} + W N + D` is equivalent to
`P C + Q A + (1 − Q) M ≤ A_{−1} + W N + D`. -/
theorem budget_rewrite (P C Q B M Bm Mm W N D : ℝ) :
    P * C + Q * B + M ≤ Bm + Mm + W * N + D ↔
      P * C + Q * (B + M) + (1 - Q) * M ≤ (Bm + Mm) + W * N + D := by
  have h : P * C + Q * (B + M) + (1 - Q) * M = P * C + Q * B + M := by ring
  rw [h]

/-- Galí (2015), p. 32: with `i = −log Q` the bond price is `Q = e^{−i}`, so the price of the
services of money is `1 − Q = 1 − e^{−i}`. -/
theorem price_of_money_services {Q : ℝ} (hQ : 0 < Q) : 1 - Q = 1 - Real.exp (-(-Real.log Q)) := by
  rw [neg_neg, Real.exp_log hQ]

/-- Galí (2015), p. 32 (`1 − e^{−i} ≃ i`, upper bound): `1 − e^{−i} ≤ i` for every `i`. -/
theorem one_sub_exp_neg_le (i : ℝ) : 1 - Real.exp (-i) ≤ i := by
  linarith [Real.add_one_le_exp (-i)]

/-- Galí (2015), p. 32 (`1 − e^{−i} ≃ i`, lower bound): `i e^{−i} ≤ 1 − e^{−i}`. -/
theorem mul_exp_neg_le_one_sub_exp_neg (i : ℝ) : i * Real.exp (-i) ≤ 1 - Real.exp (-i) := by
  have h1 := Real.add_one_le_exp i
  have h2 : Real.exp i * Real.exp (-i) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  nlinarith [Real.exp_pos (-i)]

/-! ### Eq. (33) for a general utility function -/

/-- Galí (2015), eq. (33), pp. 32–33 (**necessity, general utility**): let `U(C, M/P)` be
differentiable at the plan with derivative `L` (so `U_c = L (1, 0)`, `U_m = L (0, 1)`). If no
small perturbation `(dC, dM) = (−(1 − Q) δ / P, δ)`, which satisfies
`P dC + (1 − Q) dM = 0` and leaves all other variables unchanged, raises utility, then
`U_m = (1 − Q) U_c`. -/
theorem miu_foc_necessary {U : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {P Q C M : ℝ} (hP : P ≠ 0)
    (hU : HasFDerivAt U L (C, M / P))
    (hloc : IsLocalMax (fun δ : ℝ => U (C - (1 - Q) * δ / P, (M + δ) / P)) 0) :
    L (0, 1) = (1 - Q) * L (1, 0) := by
  have hc1 : HasDerivAt (fun δ : ℝ => C - (1 - Q) * δ / P) (-((1 - Q) / P)) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).const_mul (1 - Q)).div_const P).const_sub C
    simpa using this
  have hc2 : HasDerivAt (fun δ : ℝ => (M + δ) / P) (1 / P) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_add M).div_const P
    simpa using this
  have hcomp := hU.comp_hasDerivAt_of_eq 0 (hc1.prodMk hc2) (by simp)
  have h0 := hloc.hasDerivAt_eq_zero hcomp
  have hv : ((-((1 - Q) / P), 1 / P) : ℝ × ℝ)
      = (-((1 - Q) / P)) • ((1 : ℝ), (0 : ℝ)) + (1 / P) • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hv, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h0
  field_simp at h0
  linarith

/-! ### The separable utility of §2.5.1 -/

/-- Galí (2015), p. 33: the isoelastic utility `(x^{1−σ} − 1)/(1 − σ)`, with the log case
`σ = 1` (restated from the Chapter 3 project). -/
noncomputable def utilPow (σ x : ℝ) : ℝ :=
  if σ = 1 then Real.log x else (x ^ (1 - σ) - 1) / (1 - σ)

/-- Galí (2015), p. 33: marginal utility `x^{−σ}` of `utilPow` (restated from the Chapter 3
project). -/
theorem hasDerivAt_utilPow (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (utilPow σ) (x ^ (-σ)) x := by
  by_cases hσ : σ = 1
  · have hfun : utilPow σ = Real.log := funext fun y => by simp [utilPow, hσ]
    rw [hfun, hσ, Real.rpow_neg_one]
    exact Real.hasDerivAt_log hx.ne'
  · have hfun : utilPow σ = fun y => (y ^ (1 - σ) - 1) / (1 - σ) :=
      funext fun y => by simp [utilPow, hσ]
    have hs : (1 : ℝ) - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
    rw [hfun]
    refine (((Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hx.ne')).sub_const 1).div_const
      (1 - σ)).congr_deriv ?_
    rw [show (1 : ℝ) - σ - 1 = -σ by ring]
    field_simp

/-- A differentiable function on `(0, ∞)` with nonincreasing derivative lies below its
tangent lines (restated from the Chapter 3 project; Galí (2015), p. 32, concavity). -/
theorem le_tangent {f f' : ℝ → ℝ} {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hcont : ContinuousOn f (Set.uIcc x y)) (hd : ∀ z, 0 < z → HasDerivAt f (f' z) z)
    (hanti : AntitoneOn f' (Set.Ioi 0)) : f y ≤ f x + f' x * (y - x) := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f f' hxy
      (by rwa [Set.uIcc_of_le hxy.le] at hcont) (fun z hz => hd z (hx.trans hz.1))
    have hle : f' c ≤ f' x := hanti hx (hx.trans hc.1) hc.1.le
    have hpos : 0 < y - x := sub_pos.2 hxy
    rw [eq_div_iff hpos.ne'] at hcs
    nlinarith
  · simp
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f f' hxy
      (by rwa [Set.uIcc_of_ge hxy.le] at hcont) (fun z hz => hd z (lt_of_le_of_lt hy hz.1))
    have hle : f' x ≤ f' c := hanti (lt_of_le_of_lt hy hc.1) hx hc.2.le
    have hpos : 0 < x - y := sub_pos.2 hxy
    rw [eq_div_iff hpos.ne'] at hcs
    nlinarith

/-- Galí (2015), p. 32 (utility concave in each argument): `utilPow σ` lies below its tangent
lines on `(0, ∞)` for `σ > 0` (restated from the Chapter 3 project). -/
theorem utilPow_le_tangent {σ : ℝ} (hσ : 0 < σ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    utilPow σ y ≤ utilPow σ x + x ^ (-σ) * (y - x) := by
  refine le_tangent (f' := fun z => z ^ (-σ)) hx hy.le ?_ (fun z hz => hasDerivAt_utilPow σ hz)
    (fun _ ha _ _ hab => Real.rpow_le_rpow_of_nonpos ha hab (by linarith))
  intro z hz
  have hz0 : 0 < z := by
    rcases Set.mem_uIcc.1 hz with h | h
    · exact lt_of_lt_of_le hx h.1
    · exact lt_of_lt_of_le hy h.1
  exact (hasDerivAt_utilPow σ hz0).continuousAt.continuousWithinAt

/-- Galí (2015), p. 33: the separable period utility
`U(C, M/P, N; Z) = ((C^{1−σ} − 1)/(1 − σ) + ((M/P)^{1−ν} − 1)/(1 − ν) − N^{1+φ}/(1+φ)) Z`
(log branches for `σ = 1`, `ν = 1`), with `m = M/P` real balances. -/
noncomputable def sepUtil (σ ν φ Z C m N : ℝ) : ℝ :=
  (utilPow σ C + utilPow ν m - N ^ (1 + φ) / (1 + φ)) * Z

/-- Galí (2015), p. 33 (separability): `U_c = C^{−σ} Z` does not depend on real balances `m`
or on hours, so eqs. (7), (8) and their log forms (9), (10) are unchanged. -/
theorem hasDerivAt_sepUtil_C (σ ν φ Z m N : ℝ) {C : ℝ} (hC : 0 < C) :
    HasDerivAt (fun C' => sepUtil σ ν φ Z C' m N) (C ^ (-σ) * Z) C := by
  have := (((hasDerivAt_utilPow σ hC).add_const (utilPow ν m)).sub_const
    (N ^ (1 + φ) / (1 + φ))).mul_const Z
  exact this

/-- Galí (2015), p. 33 (separability): `U_n = −N^φ Z` does not depend on real balances. -/
theorem hasDerivAt_sepUtil_N (σ ν Z C m : ℝ) {φ : ℝ} (hφ : 0 ≤ φ) (N : ℝ) :
    HasDerivAt (fun N' => sepUtil σ ν φ Z C m N') (-(N ^ φ) * Z) N := by
  have h1 : (0 : ℝ) < 1 + φ := by linarith
  have hd : HasDerivAt (fun N' : ℝ => N' ^ (1 + φ) / (1 + φ)) (N ^ φ) N := by
    refine ((Real.hasDerivAt_rpow_const (x := N) (p := 1 + φ) (Or.inr (by linarith))).div_const
      (1 + φ)).congr_deriv ?_
    rw [show (1 : ℝ) + φ - 1 = φ by ring]
    field_simp
  have := (hd.const_sub (utilPow σ C + utilPow ν m)).mul_const Z
  simpa [sepUtil, sub_eq_add_neg] using this

/-- Galí (2015), p. 33: derivative at `δ = 0` of utility along the money perturbation
`(dC, dM) = (−(1 − Q) δ / P, δ)`: `(−C^{−σ}(1 − Q)/P + (M/P)^{−ν}/P) Z`. -/
theorem hasDerivAt_perturbation (σ ν φ Z N : ℝ) {P Q C M : ℝ} (hP : 0 < P) (hC : 0 < C)
    (hM : 0 < M) :
    HasDerivAt (fun δ => sepUtil σ ν φ Z (C - (1 - Q) * δ / P) ((M + δ) / P) N)
      ((C ^ (-σ) * (-((1 - Q) / P)) + (M / P) ^ (-ν) * (1 / P)) * Z) 0 := by
  have hc1 : HasDerivAt (fun δ : ℝ => C - (1 - Q) * δ / P) (-((1 - Q) / P)) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).const_mul (1 - Q)).div_const P).const_sub C
    simpa using this
  have hc2 : HasDerivAt (fun δ : ℝ => (M + δ) / P) (1 / P) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_add M).div_const P
    simpa using this
  have hu1 : HasDerivAt (utilPow σ) (C ^ (-σ)) (C - (1 - Q) * 0 / P) := by
    simpa using hasDerivAt_utilPow σ hC
  have hu2 : HasDerivAt (utilPow ν) ((M / P) ^ (-ν)) ((M + 0) / P) := by
    simpa using hasDerivAt_utilPow ν (div_pos hM hP)
  have := (((hu1.comp 0 hc1).add (hu2.comp 0 hc2)).sub_const
    (N ^ (1 + φ) / (1 + φ))).mul_const Z
  exact this

/-- Galí (2015), eq. (33), pp. 32–33, separable utility (**necessary and sufficient**): for
`σ, ν > 0`, `Z, P > 0`, `C, M > 0`, the plan `(C, M)` cannot be improved by any feasible
perturbation `(dC, dM) = (−(1 − Q) δ / P, δ)` (positive consumption and money) **iff**
`U_m = (1 − Q) U_c`, i.e. `(M/P)^{−ν} = (1 − Q) C^{−σ}`. -/
theorem miu_static_optimum_iff {σ ν φ Z P Q C M N : ℝ} (hσ : 0 < σ) (hν : 0 < ν) (hZ : 0 < Z)
    (hP : 0 < P) (hC : 0 < C) (hM : 0 < M) :
    (∀ δ, 0 < C - (1 - Q) * δ / P → 0 < (M + δ) / P →
      sepUtil σ ν φ Z (C - (1 - Q) * δ / P) ((M + δ) / P) N ≤ sepUtil σ ν φ Z C (M / P) N) ↔
      (M / P) ^ (-ν) = (1 - Q) * C ^ (-σ) := by
  constructor
  · intro hopt
    have hloc : IsLocalMax (fun δ => sepUtil σ ν φ Z (C - (1 - Q) * δ / P) ((M + δ) / P) N) 0 := by
      have hc1 : Continuous fun δ : ℝ => C - (1 - Q) * δ / P := by fun_prop
      have hc2 : Continuous fun δ : ℝ => (M + δ) / P := by fun_prop
      have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < C - (1 - Q) * δ / P :=
        (hc1.tendsto 0).eventually_const_lt (by simpa using hC)
      have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < (M + δ) / P :=
        (hc2.tendsto 0).eventually_const_lt (by simpa using div_pos hM hP)
      filter_upwards [e1, e2] with δ h1 h2
      simpa using hopt δ h1 h2
    have h0 := hloc.hasDerivAt_eq_zero (hasDerivAt_perturbation σ ν φ Z N hP hC hM)
    have h1 := (mul_eq_zero.1 h0).resolve_right hZ.ne'
    field_simp at h1
    linarith
  · intro hfoc δ h1 h2
    have t1 := utilPow_le_tangent hσ hC h1
    have t2 := utilPow_le_tangent hν (div_pos hM hP) h2
    unfold sepUtil
    apply mul_le_mul_of_nonneg_right _ hZ.le
    have e : C ^ (-σ) * (C - (1 - Q) * δ / P - C) + (M / P) ^ (-ν) * ((M + δ) / P - M / P)
        = 0 := by rw [hfoc]; ring
    linarith

/-- Galí (2015), eq. (33), p. 32, ratio form: `U_m = (1 − Q) U_c` iff `U_m / U_c = 1 − Q`
(`U_c = C^{−σ} > 0`). -/
theorem foc_iff_ratio {σ ν Q C m : ℝ} (hC : 0 < C) :
    m ^ (-ν) = (1 - Q) * C ^ (-σ) ↔ m ^ (-ν) / C ^ (-σ) = 1 - Q := by
  rw [div_eq_iff (Real.rpow_pos_of_pos hC _).ne']

/-- Galí (2015), eq. (33), pp. 32–33, with `Q = e^{−i}` (**necessary and sufficient**):
the plan is optimal against all feasible money perturbations iff
`U_m / U_c = 1 − e^{−i}`. -/
theorem miu_static_optimum_iff_exp {σ ν φ Z P i C M N : ℝ} (hσ : 0 < σ) (hν : 0 < ν)
    (hZ : 0 < Z) (hP : 0 < P) (hC : 0 < C) (hM : 0 < M) :
    (∀ δ, 0 < C - (1 - Real.exp (-i)) * δ / P → 0 < (M + δ) / P →
      sepUtil σ ν φ Z (C - (1 - Real.exp (-i)) * δ / P) ((M + δ) / P) N
        ≤ sepUtil σ ν φ Z C (M / P) N) ↔
      (M / P) ^ (-ν) / C ^ (-σ) = 1 - Real.exp (-i) := by
  rw [miu_static_optimum_iff hσ hν hZ hP hC hM, foc_iff_ratio hC]

/-! ### Eq. (34): money demand -/

/-- Galí (2015), eq. (34), p. 34 (**exact**): for `i > 0`, `ν > 0` and positive `C`, `m`, the
optimality condition `m^{−ν} = (1 − e^{−i}) C^{−σ}` is equivalent to the money demand
`m = C^{σ/ν} (1 − e^{−i})^{−1/ν}`. -/
theorem money_demand_iff {σ ν i C m : ℝ} (hν : 0 < ν) (hi : 0 < i) (hC : 0 < C) (hm : 0 < m) :
    m ^ (-ν) = (1 - Real.exp (-i)) * C ^ (-σ) ↔
      m = C ^ (σ / ν) * (1 - Real.exp (-i)) ^ (-1 / ν) := by
  have hk : 0 < 1 - Real.exp (-i) := by
    have : Real.exp (-i) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have hp1 : 0 < m ^ (-ν) := Real.rpow_pos_of_pos hm _
  have hp2 : 0 < (1 - Real.exp (-i)) * C ^ (-σ) := mul_pos hk (Real.rpow_pos_of_pos hC _)
  have hp3 : 0 < C ^ (σ / ν) * (1 - Real.exp (-i)) ^ (-1 / ν) :=
    mul_pos (Real.rpow_pos_of_pos hC _) (Real.rpow_pos_of_pos hk _)
  rw [← Real.log_injOn_pos.eq_iff hp1 hp2, ← Real.log_injOn_pos.eq_iff hm hp3,
    Real.log_rpow hm, Real.log_mul hk.ne' (Real.rpow_pos_of_pos hC _).ne', Real.log_rpow hC,
    Real.log_mul (Real.rpow_pos_of_pos hC _).ne' (Real.rpow_pos_of_pos hk _).ne',
    Real.log_rpow hC, Real.log_rpow hk]
  have key : σ / ν * Real.log C + -1 / ν * Real.log (1 - Real.exp (-i))
      = (σ * Real.log C - Real.log (1 - Real.exp (-i))) / ν := by ring
  rw [key, eq_div_iff hν.ne']
  constructor <;> intro h <;> linarith

/-- Galí (2015), p. 34: money is held only at a positive nominal rate. For `i ≤ 0` the
optimality condition (33) `m^{−ν} = (1 − e^{−i}) C^{−σ}` has no solution with `m, C > 0`. -/
theorem no_money_demand_of_nonpos {σ ν i C m : ℝ} (hi : i ≤ 0) (hC : 0 < C) (hm : 0 < m) :
    m ^ (-ν) ≠ (1 - Real.exp (-i)) * C ^ (-σ) := by
  have hk : 1 - Real.exp (-i) ≤ 0 := by
    have : 1 ≤ Real.exp (-i) := Real.one_le_exp (by linarith)
    linarith
  have h1 : 0 < m ^ (-ν) := Real.rpow_pos_of_pos hm _
  have h2 : (1 - Real.exp (-i)) * C ^ (-σ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hk (Real.rpow_pos_of_pos hC _).le
  intro h
  linarith

/-! ### Eq. (35): the log-linear money demand -/

/-- Galí (2015), eq. (35), p. 34: the log money demand implied by (34),
`log(M/P) = (σ/ν) c − ν⁻¹ log(1 − e^{−i})` with `c = log C`. -/
noncomputable def logMoneyDemand (σ ν c i : ℝ) : ℝ :=
  σ / ν * c - 1 / ν * Real.log (1 - Real.exp (-i))

/-- Galí (2015), p. 34: the interest semi-elasticity of money demand `η = 1/(ν(e^i − 1))`. -/
noncomputable def eta (ν i : ℝ) : ℝ := 1 / (ν * (Real.exp i - 1))

/-- Galí (2015), eqs. (34)–(35), p. 34 (**exact**): the log of the money demand (34) is
`logMoneyDemand σ ν (log C) i`. -/
theorem log_money_demand {σ ν i C : ℝ} (hi : 0 < i) (hC : 0 < C) :
    Real.log (C ^ (σ / ν) * (1 - Real.exp (-i)) ^ (-1 / ν))
      = logMoneyDemand σ ν (Real.log C) i := by
  have hk : 0 < 1 - Real.exp (-i) := by
    have : Real.exp (-i) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  rw [Real.log_mul (Real.rpow_pos_of_pos hC _).ne' (Real.rpow_pos_of_pos hk _).ne',
    Real.log_rpow hC, Real.log_rpow hk, logMoneyDemand]
  ring

/-- Galí (2015), p. 34 (the Taylor step behind (35)): for `i > 0`,
`d/di log(1 − e^{−i}) = 1/(e^i − 1)`. -/
theorem hasDerivAt_log_one_sub_exp_neg {i : ℝ} (hi : 0 < i) :
    HasDerivAt (fun j => Real.log (1 - Real.exp (-j))) (1 / (Real.exp i - 1)) i := by
  have hk : 0 < 1 - Real.exp (-i) := by
    have : Real.exp (-i) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have h1 : HasDerivAt (fun j => 1 - Real.exp (-j)) (-(Real.exp (-i) * (-1))) i :=
    ((hasDerivAt_neg i).exp).const_sub 1
  refine (h1.log hk.ne').congr_deriv ?_
  have he : 1 < Real.exp i := Real.one_lt_exp_iff.2 hi
  have hx : Real.exp (-i) = (Real.exp i)⁻¹ := Real.exp_neg i
  rw [hx]
  have : Real.exp i - 1 ≠ 0 := by linarith
  have : Real.exp i ≠ 0 := (Real.exp_pos i).ne'
  field_simp

/-- Galí (2015), eq. (35), p. 34, as an **exact derivative**: for `i > 0`, `ν ≠ 0`, the log
money demand `(c, i) ↦ (σ/ν) c − ν⁻¹ log(1 − e^{−i})` has total derivative
`(dc, di) ↦ (σ/ν) dc − η di`, `η = 1/(ν(e^i − 1))`; to first order
`m − p = (σ/ν) c − η i` up to a constant. -/
theorem hasFDerivAt_logMoneyDemand (σ ν c : ℝ) {i : ℝ} (hi : 0 < i) :
    HasFDerivAt (fun x : ℝ × ℝ => logMoneyDemand σ ν x.1 x.2)
      ((σ / ν) • ContinuousLinearMap.fst ℝ ℝ ℝ - eta ν i • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (c, i) := by
  have h1 := (hasFDerivAt_fst (𝕜 := ℝ) (p := ((c, i) : ℝ × ℝ))).const_mul (σ / ν)
  have h2 := ((hasDerivAt_log_one_sub_exp_neg hi).comp_hasFDerivAt ((c, i) : ℝ × ℝ)
    (hasFDerivAt_snd (𝕜 := ℝ) (p := ((c, i) : ℝ × ℝ)))).const_mul (1 / ν)
  refine (h1.sub h2).congr_fderiv ?_
  ext
  · simp [eta]
  · simp [eta]
    ring

/-- Galí (2015), p. 34: `η > 0` for `ν > 0`, `i > 0`. -/
theorem eta_pos {ν i : ℝ} (hν : 0 < ν) (hi : 0 < i) : 0 < eta ν i := by
  have : 0 < Real.exp i - 1 := by linarith [Real.one_lt_exp_iff.2 hi]
  unfold eta
  positivity

/-- Galí (2015), p. 34 (`η ≃ 1/(νi)`, upper bound): `η ≤ 1/(ν i)`. -/
theorem eta_le {ν i : ℝ} (hν : 0 < ν) (hi : 0 < i) : eta ν i ≤ 1 / (ν * i) := by
  unfold eta
  apply one_div_le_one_div_of_le (mul_pos hν hi)
  have := Real.add_one_le_exp i
  nlinarith

/-- Galí (2015), p. 34 (`η ≃ 1/(νi)`, lower bound): `e^{−i}/(ν i) ≤ η`. -/
theorem exp_neg_div_le_eta {ν i : ℝ} (hν : 0 < ν) (hi : 0 < i) :
    Real.exp (-i) / (ν * i) ≤ eta ν i := by
  have hpos : 0 < Real.exp i - 1 := by linarith [Real.one_lt_exp_iff.2 hi]
  have h : Real.exp (-i) * Real.exp i = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h2 := one_sub_exp_neg_le i
  unfold eta
  rw [div_le_div_iff₀ (mul_pos hν hi) (mul_pos hν hpos)]
  have e : Real.exp (-i) * (ν * (Real.exp i - 1)) = ν * (1 - Real.exp (-i)) := by
    linear_combination ν * h
  rw [e]
  nlinarith

/-! ### Eq. (36): the case `ν = σ` -/

/-- Galí (2015), eq. (36), p. 34 (**exact derivative**): for `ν = σ ≠ 0` the log money demand
has unit consumption elasticity: its derivative is `(dc, di) ↦ dc − η di`. -/
theorem hasFDerivAt_logMoneyDemand_unit (c : ℝ) {σ i : ℝ} (hσ : σ ≠ 0) (hi : 0 < i) :
    HasFDerivAt (fun x : ℝ × ℝ => logMoneyDemand σ σ x.1 x.2)
      (ContinuousLinearMap.fst ℝ ℝ ℝ - eta σ i • ContinuousLinearMap.snd ℝ ℝ ℝ) (c, i) := by
  have := hasFDerivAt_logMoneyDemand σ σ c hi
  rwa [div_self hσ, one_smul] at this

/-- Galí (2015), eq. (36), p. 34 (the log-linear model): with `ν = σ` the linearised money
demand reads `m − p = c − η i`, and with all output consumed (`y = c`) it is
`m − p = y − η i`. -/
theorem money_demand_unit_elastic {σ η mp c y i : ℝ} (hσ : σ ≠ 0)
    (h35 : mp = σ / σ * c - η * i) (hyc : y = c) : mp = c - η * i ∧ mp = y - η * i := by
  rw [div_self hσ, one_mul] at h35
  exact ⟨h35, hyc ▸ h35⟩

end Gali.ClassicalMonetaryModel.MIUSeparable
