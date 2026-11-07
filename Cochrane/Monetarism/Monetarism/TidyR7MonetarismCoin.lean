/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR7MonetarismValuation
import Monetarism.TidyR7ProductStepCoin

/-!
# Non-vacuity of (1.31)–(1.33) under uncertainty, and the meaning of `E_t∫_t^∞`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Two concrete models on the fair coin of
`TidyR7ProductStepCoin` (`Ω = Bool`, `ξ = ±1` revealed at time `1`), with `H = 1{u ≥ 1}`
(`TidyR7StieltjesSums.heaviside`) and `G = 1{u > 1}` (`stepG`).

## A model with news in `Λ/P` (`coinModel`)

`P = 1`, `Λ_u = 1 + (ξ/2)H(u)` (so `Λ/P = A + N` with `A = 1`, `i = 0`, and the nonzero càdlàg
martingale `N_u = (ξ/2)H(u)`), bonds `B_u = 1 + ξ(u − 1)⁺` (`TidyR7ProductStepCoin.coinB`), money
`M_u = ξ(u − 1)⁺` (`coinMon`), `i^m = 0`, surplus `s_u = −2ξG(u)` (`coinSur`), so that the flow
(1.31) `d(B + M) = −Ps dt = 2ξG dt` holds. On `[0, 2]`:
* `coin_lhs_1_32`: `E_0[n_2B_2 − n_0B_0] = 1/2`; `coin_flow133`:
  `∫_0^2 Λs dr + ∫_0^2 n dM = −ξ − 1/2` path by path, so `−E_0[…] = 1/2` (`coin_rhs_1_32`);
  `coin_1_32`: both sides of (1.32) and the theorem
  `TidyR7MonetarismModel.MonetaryModel.incr_1_32` there.
* `coin_pathwise_fails`: without the expectation the identity fails (`2 ≠ 3/2` at `ξ = 1`): the
  martingale part of `Λ/P` matters.
* `coin_1_33_finite`: the finite-horizon (1.33), `n_0B_0 = 1 = 3/2 + (−1/2) =
  E_0[n_2B_2] + E_0[∫_0^2 Λs + ∫_0^2 n dM]`.

## `E_t∫_t^∞` need not exist when the valuation equation holds (`impModel`)

`Λ = P = 1`, `i = i^m = 0`, `M = 0`, surplus `s_u = ξG(u)`, bonds `B_u = −ξ(u − 1)⁺` (debt paid
down or run up after the coin, matching the surplus). At `t = 0`, `B_0 = 0`, and:
* `imp_tvc`: `E_0[n_TB_T] = 0` for every `T`: the transversality condition holds;
* `imp_limit`: `E_0∫_0^T Λs = 0 → 0 = n_0B_0`: the valuation equation holds in the limit form of
  `TidyR7MonetarismValuation.MonetaryModel.valuation_1_33_seq`;
* `imp_no_L1_limit`, `imp_no_pathwise_limit`: but `∫_0^T Λs = ξ(T − 1)⁺` has no `L¹` limit and no
  pathwise limit at `ξ = 1`, so the printed `E_0∫_0^∞ Λ_τs_τ dτ` is undefined.
So (1.33)–(1.34) as printed presuppose that `∫_t^∞` converges (e.g. in `L¹` or dominatedly); the
limit form `lim_T E_t∫_t^T` is the statement that holds without that presupposition.
-/

namespace Cochrane.Monetarism.TidyR7MonetarismCoin

open MeasureTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesIntegral Cochrane.Monetarism.TidyR7StieltjesSums
  Cochrane.Monetarism.TidyR7ProductStep Cochrane.Monetarism.TidyR7ProductStepCoin
  Cochrane.Monetarism.TidyR7MonetarismAC Cochrane.Monetarism.TidyR7MonetarismModel
  Cochrane.Monetarism.TidyR7MonetarismValuation

/-! ## Tools -/

/-- Cochrane (2023), A1 §1.6, p. 567 (non-vacuity): the step `G(u) = 1{u > 1}`. -/
noncomputable def stepG (r : ℝ) : ℝ := if 1 < r then 1 else 0

/-- Cochrane (2023), A1 §1.6, p. 567: `G` is monotone. -/
theorem monotone_stepG : Monotone stepG := by
  intro x y hxy
  simp only [stepG]
  split_ifs with h1 h2 <;> (try simp only [not_lt] at *) <;> linarith

/-- Cochrane (2023), A1 §1.6, p. 567: `G` is interval integrable.
From Mathlib `Monotone.intervalIntegrable`. -/
theorem intervalIntegrable_stepG (u v : ℝ) :
    IntervalIntegrable stepG MeasureSpace.volume u v :=
  monotone_stepG.intervalIntegrable

/-- Cochrane (2023), A1 §1.6, p. 567: `∫_u^v G = (v − 1)⁺ − (u − 1)⁺` for `u ≤ v`. -/
theorem integral_stepG {u v : ℝ} (huv : u ≤ v) :
    ∫ r in u..v, stepG r = max (v - 1) 0 - max (u - 1) 0 := by
  have h0 : ∀ a b : ℝ, a ≤ b → b ≤ 1 → ∫ r in a..b, stepG r = 0 := by
    intro a b hab hb
    have e : ∫ r in a..b, stepG r = ∫ _ in a..b, (0 : ℝ) :=
      intervalIntegral.integral_congr_ae (Eventually.of_forall fun r hr => by
        rw [Set.uIoc_of_le hab] at hr
        simp only [stepG, not_lt.2 (hr.2.trans hb), ↓reduceIte])
    rw [e, intervalIntegral.integral_zero]
  have h1 : ∀ a b : ℝ, a ≤ b → 1 ≤ a → ∫ r in a..b, stepG r = b - a := by
    intro a b hab ha
    have e : ∫ r in a..b, stepG r = ∫ _ in a..b, (1 : ℝ) :=
      intervalIntegral.integral_congr_ae (Eventually.of_forall fun r hr => by
        rw [Set.uIoc_of_le hab] at hr
        simp only [stepG, show 1 < r from lt_of_le_of_lt ha hr.1, ↓reduceIte])
    rw [e, intervalIntegral.integral_const, smul_eq_mul, mul_one]
  rcases le_total v 1 with hv | hv
  · rw [h0 u v huv hv, max_eq_right (by linarith), max_eq_right (by linarith)]
    ring
  · rcases le_total 1 u with hu | hu
    · rw [h1 u v huv hu, max_eq_left (by linarith), max_eq_left (by linarith)]
      ring
    · rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1)
        (intervalIntegrable_stepG u 1) (intervalIntegrable_stepG 1 v), h0 u 1 hu le_rfl,
        h1 1 v hv le_rfl, max_eq_left (by linarith), max_eq_right (by linarith)]
      ring

/-- Cochrane (2023), A1 §1.6, p. 567: `H·G = G` (`H = 1{u ≥ 1}`, `G = 1{u > 1}`). -/
theorem heaviside_mul_stepG (r : ℝ) : heaviside r * stepG r = stepG r := by
  simp only [heaviside, stepG]
  split_ifs with h1 h2 <;> (try simp only [not_lt, not_le] at *) <;> linarith

/-- Cochrane (2023), A1 §1.6, p. 567: a process that is non-random before time `1` is adapted to
the coin filtration. -/
theorem coin_adapted {f : ℝ → Bool → ℝ} (hf : ∀ u < 1, ∀ ω, f u ω = f u true) (u : ℝ) :
    StronglyMeasurable[coinFiltration u] (f u) := by
  by_cases hu : u < 1
  · have e : f u = fun _ => f u true := funext fun ω => hf u hu ω
    rw [e]
    exact stronglyMeasurable_const
  · rw [coinFiltration_ge (not_lt.1 hu)]
    exact (measurable_of_finite _).stronglyMeasurable

/-- Cochrane (2023), A1 §1.6, p. 567: the ramp `u ↦ c(u − 1)⁺` is `|c|`-Lipschitz, hence of
bounded variation on every `[a, b]`. -/
theorem bv_ramp (c a b : ℝ) :
    BoundedVariationOn (fun u => c * max (u - 1) 0) (Set.Icc a b) := by
  have hL : LipschitzWith ‖c‖₊ fun u : ℝ => c * max (u - 1) 0 := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, Real.dist_eq, coe_nnnorm, Real.norm_eq_abs, ← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
    calc |max (x - 1) 0 - max (y - 1) 0| ≤ |x - 1 - (y - 1)| := abs_max_sub_max_le_abs _ _ _
      _ = |x - y| := by ring_nf
  exact hL.comp_boundedVariationOn (BoundedVariationOn.id_Icc a b)

/-- Cochrane (2023), A1 §1.6, p. 567: the ramp is continuous. -/
theorem continuous_ramp (c : ℝ) : Continuous fun u : ℝ => c * max (u - 1) 0 :=
  continuous_const.mul ((continuous_id.sub continuous_const).max continuous_const)

/-! ## A model with news in `Λ/P` -/

/-- Cochrane (2023), A1 §1.6, p. 567: the SDF `Λ_u = 1 + (ξ/2)H(u)`. -/
noncomputable def coinLam (u : ℝ) (ω : Bool) : ℝ := 1 + coinXi ω / 2 * heaviside u

/-- Cochrane (2023), A1 §1.6, p. 567: the price level `P = 1`. -/
def coinP (_ : ℝ) (_ : Bool) : ℝ := 1

/-- Cochrane (2023), A1 §1.6, p. 567: the finite-variation part `A = 1` of `Λ/P` (`i = 0`). -/
def coinA1 (_ : ℝ) (_ : Bool) : ℝ := 1

/-- Cochrane (2023), A1 §1.6, p. 567: the martingale part `N_u = (ξ/2)H(u)` of `Λ/P`. -/
noncomputable def coinN (u : ℝ) (ω : Bool) : ℝ := coinXi ω / 2 * heaviside u

/-- Cochrane (2023), A1 §1.6, p. 567: money `M_u = ξ(u − 1)⁺`. -/
noncomputable def coinMon (u : ℝ) (ω : Bool) : ℝ := coinXi ω * max (u - 1) 0

/-- Cochrane (2023), A1 §1.6, p. 567: the surplus `s_u = −2ξG(u)`. -/
noncomputable def coinSur (u : ℝ) (ω : Bool) : ℝ := -(2 * coinXi ω * stepG u)

/-- Cochrane (2023), A1 §1.6, p. 567: a zero rate (`i = i^m = 0`). -/
def zeroRate (_ : ℝ) (_ : Bool) : ℝ := 0

/-- Cochrane (2023), A1 §1.6, p. 567: here `Λ/P = Λ`. -/
theorem disc_coin (u : ℝ) (ω : Bool) : disc coinLam coinP u ω = coinLam u ω := by
  simp [disc, coinP]

/-- Cochrane (2023), A1 §1.6, p. 567: the flow density is `2ξG`. -/
theorem flowRate_coin (ω : Bool) :
    (fun r => flowRate coinB coinMon coinP zeroRate zeroRate coinSur r ω) =
      fun r => 2 * coinXi ω * stepG r :=
  funext fun r => by simp only [flowRate, zeroRate, coinP, coinSur]; ring

/-- **Cochrane (2023), A1 §1.6, (1.31)–(1.32), p. 567: the coin model satisfies the hypotheses of
`TidyR7MonetarismModel.MonetaryModel`**, with a nonzero martingale part in `Λ/P`. -/
theorem coinModel : MonetaryModel coinMeasure coinFiltration coinLam coinP coinB coinMon coinA1
    coinN zeroRate zeroRate coinSur where
  P_pos _ _ := one_pos
  Λ_pos u ω := by
    have h1 : |coinXi ω / 2 * heaviside u| ≤ 1 / 2 := by
      rw [abs_mul, abs_div, abs_coinXi]
      simp only [heaviside]
      split_ifs <;> norm_num
    simp only [coinLam]
    linarith [neg_abs_le (coinXi ω / 2 * heaviside u)]
  Λ_adapted := coin_adapted fun u hu ω => by simp [coinLam, heaviside, not_le.2 hu]
  P_adapted _ := stronglyMeasurable_const
  dec u ω := by simp [disc, coinLam, coinP, coinA1, coinN]
  A_incr ω u v _ := by simp [coinA1, zeroRate]
  A_int ω u v := by
    have e : (fun r => -(zeroRate r ω * disc coinLam coinP r ω)) = fun _ => (0 : ℝ) :=
      funext fun r => by simp [zeroRate]
    rw [e]
    exact intervalIntegrable_const
  N_mart := by
    have e : coinN = (1 / 2 : ℝ) • coinM := funext fun u => funext fun ω => by
      simp only [coinN, coinM, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact martingale_coinM.smul _
  N_cadlag ω := isCadlag_heaviside.continuous_comp (continuous_const.mul continuous_id
    (f := fun _ : ℝ => coinXi ω / 2))
  B_adapted := coin_adapted fun u hu ω => by rw [coinB_le hu.le, coinB_le hu.le]
  M_adapted := coin_adapted fun u hu ω => by
    simp [coinMon, max_eq_right (by linarith : u - 1 ≤ 0)]
  M_cont ω := continuous_ramp (coinXi ω)
  M_bv ω a b := bv_ramp (coinXi ω) a b
  flow ω u v huv := by
    rw [flowRate_coin ω, intervalIntegral.integral_const_mul, integral_stepG huv]
    simp only [addProc, coinB, coinMon]
    ring
  flow_int ω u v := by
    rw [flowRate_coin ω]
    exact (intervalIntegrable_stepG u v).const_mul _

/-- Cochrane (2023), A1 §1.6, p. 567: the martingale part of `Λ/P` is not zero
(`N_1 = 1/2` at `ξ = 1`). -/
theorem coinN_ne_zero : coinN 1 true ≠ 0 := by
  simp [coinN, coinXi, heaviside]

/-- Cochrane (2023), A1 §1.6, p. 567: the domination conditions hold on `[0, 2]` (finite `Ω`). -/
theorem coinDom : Dominated coinMeasure coinA1 coinN 0 2 coinB (disc coinLam coinP) :=
  ⟨Integrable.of_finite, Integrable.of_finite, fun _ _ _ _ _ => Integrable.of_finite⟩

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the discounted flow on the coin,
`∫_0^2 Λs dr + ∫_0^2 (Λ/P) dM = −ξ − 1/2`** path by path. -/
theorem coin_flow133 (ω : Bool) :
    flow133 coinLam coinP coinMon coinSur 0 2 ω = -coinXi ω - 1 / 2 := by
  have hMi : ∀ u v, IntervalIntegrable (fun r => coinXi ω * stepG r) MeasureSpace.volume u v :=
    fun u v => (intervalIntegrable_stepG u v).const_mul _
  have hMinc : ∀ u v, u ≤ v → coinMon v ω - coinMon u ω = ∫ r in u..v, coinXi ω * stepG r := by
    intro u v huv
    rw [intervalIntegral.integral_const_mul, integral_stepG huv]
    simp only [coinMon]
    ring
  have hrs := rsInt_eq_integral_of_incr (coinModel.disc_cadlag ω) hMi hMinc
    (by norm_num : (0 : ℝ) ≤ 2)
  have e1 : ∫ r in (0 : ℝ)..2, coinLam r ω * coinSur r ω =
      ∫ r in (0 : ℝ)..2, (-2 * coinXi ω - coinXi ω ^ 2) * stepG r :=
    intervalIntegral.integral_congr fun r _ => by
      simp only [coinLam, coinSur]
      linear_combination (-(coinXi ω ^ 2)) * heaviside_mul_stepG r
  have e2 : ∫ r in (0 : ℝ)..2, disc coinLam coinP r ω * (coinXi ω * stepG r) =
      ∫ r in (0 : ℝ)..2, (coinXi ω + coinXi ω ^ 2 / 2) * stepG r :=
    intervalIntegral.integral_congr fun r _ => by
      simp only [disc_coin, coinLam]
      linear_combination (coinXi ω ^ 2 / 2) * heaviside_mul_stepG r
  have hI : ∫ r in (0 : ℝ)..2, stepG r = 1 := by
    rw [integral_stepG (by norm_num)]
    norm_num
  have hsq : coinXi ω ^ 2 = 1 := by rw [sq, coinXi_mul_self]
  rw [flow133, hrs, e1, e2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hI, hsq]
  ring

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567, left side on the coin:
`E_0[n_2B_2 − n_0B_0] = 1/2`** (`n_2B_2 = (1 + ξ/2)(1 + ξ)`, `n_0B_0 = 1`). -/
theorem coin_lhs_1_32 :
    coinMeasure[fun ω => disc coinLam coinP 2 ω * coinB 2 ω -
      disc coinLam coinP 0 ω * coinB 0 ω | coinFiltration 0] = fun _ => 1 / 2 := by
  rw [condExp_coin_lt (by norm_num)]
  funext _
  simp [disc_coin, coinLam, coinB, coinXi, heaviside]
  norm_num

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567, right side on the coin:
`−E_0[∫_0^2 Λs dr + ∫_0^2 n dM] = 1/2`.** -/
theorem coin_rhs_1_32 :
    coinMeasure[fun ω => -((∫ r in (0 : ℝ)..2, coinLam r ω * coinSur r ω) +
      rsInt 0 2 (fun u => disc coinLam coinP u ω) (fun u => coinMon u ω)) | coinFiltration 0] =
      fun _ => 1 / 2 := by
  have e : (fun ω => -((∫ r in (0 : ℝ)..2, coinLam r ω * coinSur r ω) +
      rsInt 0 2 (fun u => disc coinLam coinP u ω) (fun u => coinMon u ω))) =
      fun ω => coinXi ω + 1 / 2 := funext fun ω => by
    have := coin_flow133 ω
    simp only [flow133] at this
    rw [this]
    ring
  rw [e, condExp_coin_lt (by norm_num)]
  funext _
  simp [coinXi]
  norm_num

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: both sides computed on a model with news in
`Λ/P`**: `E_0[n_2B_2 − n_0B_0] = 1/2 = −E_0[∫_0^2 Λs dr + ∫_0^2 n dM]`, and the conclusion of
`TidyR7MonetarismModel.MonetaryModel.incr_1_32` holds there. -/
theorem coin_1_32 :
    coinMeasure[fun ω => disc coinLam coinP 2 ω * coinB 2 ω -
        disc coinLam coinP 0 ω * coinB 0 ω | coinFiltration 0] = (fun _ => 1 / 2) ∧
      coinMeasure[fun ω => -((∫ r in (0 : ℝ)..2, coinLam r ω * coinSur r ω) +
        rsInt 0 2 (fun u => disc coinLam coinP u ω) (fun u => coinMon u ω)) |
          coinFiltration 0] = (fun _ => 1 / 2) ∧
      coinMeasure[fun ω => disc coinLam coinP 2 ω * coinB 2 ω -
          disc coinLam coinP 0 ω * coinB 0 ω | coinFiltration 0] =ᵐ[coinMeasure]
        coinMeasure[fun ω => -((∫ r in (0 : ℝ)..2, coinLam r ω * coinSur r ω) +
          rsInt 0 2 (fun u => disc coinLam coinP u ω) (fun u => coinMon u ω)) |
            coinFiltration 0] :=
  ⟨coin_lhs_1_32, coin_rhs_1_32, coinModel.incr_1_32 (by norm_num) coinDom fun _ _ => rfl⟩

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the expectation cannot be dropped.** Path by path
`n_2B_2 − n_0B_0 ≠ −(∫_0^2 Λs dr + ∫_0^2 n dM)` at `ξ = 1` (`2` against `3/2`): the difference is
the martingale term `B_1ΔN_1 = ξ/2`, which vanishes only under `E_0`. -/
theorem coin_pathwise_fails :
    disc coinLam coinP 2 true * coinB 2 true - disc coinLam coinP 0 true * coinB 0 true ≠
      -flow133 coinLam coinP coinMon coinSur 0 2 true := by
  rw [coin_flow133]
  simp [disc_coin, coinLam, coinB, coinXi, heaviside]
  norm_num

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567, on a finite horizon on the coin:**
`n_0B_0 = 1`, `E_0[n_2B_2] = 3/2`, `E_0[∫_0^2 Λs dr + ∫_0^2 n dM] = −1/2`, and the finite-horizon
budget `TidyR7MonetarismValuation.MonetaryModel.rec_1_33` holds: `1 = 3/2 − 1/2`. -/
theorem coin_1_33_finite :
    (∀ ω, disc coinLam coinP 0 ω * coinB 0 ω = 1) ∧
      coinMeasure[fun ω => disc coinLam coinP 2 ω * coinB 2 ω | coinFiltration 0] =
        (fun _ => 3 / 2) ∧
      coinMeasure[flow133 coinLam coinP coinMon coinSur 0 2 | coinFiltration 0] =
        (fun _ => -1 / 2) ∧
      (fun ω => disc coinLam coinP 0 ω * coinB 0 ω) =ᵐ[coinMeasure]
        coinMeasure[fun ω => disc coinLam coinP 2 ω * coinB 2 ω | coinFiltration 0] +
          coinMeasure[flow133 coinLam coinP coinMon coinSur 0 2 | coinFiltration 0] := by
  refine ⟨fun ω => ?_, ?_, ?_, (MonetaryModel.rec_1_33 coinModel (fun _ _ => rfl)
    (by norm_num) coinDom Integrable.of_finite Integrable.of_finite).2⟩
  · simp [disc_coin, coinLam, coinB, heaviside]
  · rw [condExp_coin_lt (by norm_num)]
    funext _
    simp [disc_coin, coinLam, coinB, coinXi, heaviside]
    norm_num
  · rw [condExp_coin_lt (by norm_num), coin_flow133, coin_flow133]
    funext _
    simp [coinXi]
    norm_num

/-! ## `E_t∫_t^∞` need not exist -/

/-- Cochrane (2023), A1 §1.6, p. 567: the unit process (`Λ = P = 1`, `A = 1`). -/
def oneProc (_ : ℝ) (_ : Bool) : ℝ := 1

/-- Cochrane (2023), A1 §1.6, p. 567: bonds `B_u = −ξ(u − 1)⁺`. -/
noncomputable def impB (u : ℝ) (ω : Bool) : ℝ := -coinXi ω * max (u - 1) 0

/-- Cochrane (2023), A1 §1.6, p. 567: the surplus `s_u = ξG(u)`. -/
noncomputable def impSur (u : ℝ) (ω : Bool) : ℝ := coinXi ω * stepG u

/-- Cochrane (2023), A1 §1.6, p. 567: here `Λ/P = 1`. -/
theorem disc_one (u : ℝ) (ω : Bool) : disc oneProc oneProc u ω = 1 := by
  simp [disc, oneProc]

/-- Cochrane (2023), A1 §1.6, p. 567: the flow density is `−ξG`. -/
theorem flowRate_imp (ω : Bool) :
    (fun r => flowRate impB zeroRate oneProc zeroRate zeroRate impSur r ω) =
      fun r => -coinXi ω * stepG r :=
  funext fun r => by simp only [flowRate, zeroRate, oneProc, impSur]; ring

/-- **Cochrane (2023), A1 §1.6, (1.31), p. 567: a second coin model** (`Λ = P = 1`, `M = 0`,
`B_u = −ξ(u − 1)⁺`, `s_u = ξG(u)`) satisfying `TidyR7MonetarismModel.MonetaryModel`. -/
theorem impModel : MonetaryModel coinMeasure coinFiltration oneProc oneProc impB zeroRate oneProc
    zeroRate zeroRate zeroRate impSur where
  P_pos _ _ := one_pos
  Λ_pos _ _ := one_pos
  Λ_adapted _ := stronglyMeasurable_const
  P_adapted _ := stronglyMeasurable_const
  dec u ω := by simp [disc, oneProc, zeroRate]
  A_incr ω u v _ := by simp [oneProc, zeroRate]
  A_int ω u v := by
    have e : (fun r => -(zeroRate r ω * disc oneProc oneProc r ω)) = fun _ => (0 : ℝ) :=
      funext fun r => by simp [zeroRate]
    rw [e]
    exact intervalIntegrable_const
  N_mart := martingale_const _ _ _
  N_cadlag _ := IsCadlag.const
  B_adapted := coin_adapted fun u hu ω => by
    simp [impB, max_eq_right (by linarith : u - 1 ≤ 0)]
  M_adapted _ := stronglyMeasurable_const
  M_cont _ := continuous_const
  M_bv _ a b := by
    rw [BoundedVariationOn, eVariationOn.constant_on
      (Set.subsingleton_of_forall_eq (0 : ℝ) fun _ ⟨_, _, hy⟩ => hy.symm)]
    exact ENNReal.zero_ne_top
  flow ω u v huv := by
    rw [flowRate_imp ω, intervalIntegral.integral_const_mul, integral_stepG huv]
    simp only [addProc, impB, zeroRate]
    ring
  flow_int ω u v := by
    rw [flowRate_imp ω]
    exact (intervalIntegrable_stepG u v).const_mul _

/-- Cochrane (2023), A1 §1.6, p. 567: the domination conditions hold on every `[0, T]`. -/
theorem impDom (T : ℝ) : Dominated coinMeasure oneProc zeroRate 0 T impB (disc oneProc oneProc) :=
  ⟨Integrable.of_finite, Integrable.of_finite, fun _ _ _ _ _ => Integrable.of_finite⟩

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: `∫_0^T Λs dr + ∫_0^T n dM = ξ(T − 1)⁺` for
`T ≥ 0`. -/
theorem imp_flow133 {T : ℝ} (hT : 0 ≤ T) (ω : Bool) :
    flow133 oneProc oneProc zeroRate impSur 0 T ω = coinXi ω * max (T - 1) 0 := by
  have hrs := rsInt_eq_integral_of_incr (f := fun u => disc oneProc oneProc u ω)
    (g := fun u => zeroRate u ω) (h := fun _ => (0 : ℝ))
    (impModel.disc_cadlag ω) (fun _ _ => intervalIntegrable_const)
    (fun u v _ => by simp [zeroRate]) hT
  have e : ∫ r in (0 : ℝ)..T, oneProc r ω * impSur r ω = coinXi ω * ∫ r in (0 : ℝ)..T, stepG r :=
    by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun r _ => by simp only [oneProc, impSur]; ring
  rw [flow133, hrs, e, integral_stepG hT]
  simp

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the transversality condition holds at `0`:**
`E_0[n_TB_T] = 0` for every `T`, so `∫|E_0[n_TB_T]| → 0`. -/
theorem imp_tvc :
    Tendsto (fun T => ∫ ω, |coinMeasure[fun ω => disc oneProc oneProc T ω * impB T ω |
      coinFiltration 0] ω| ∂coinMeasure) atTop (𝓝 0) := by
  have e : ∀ T : ℝ, coinMeasure[fun ω => disc oneProc oneProc T ω * impB T ω |
      coinFiltration 0] = fun _ => 0 := fun T => by
    rw [condExp_coin_lt (by norm_num)]
    funext _
    simp [disc_one, impB, coinXi]
  simp only [e, abs_zero, integral_zero]
  exact tendsto_const_nhds

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the valuation equation holds at `0` in the limit
form:** `E_0[∫_0^T Λs dr + ∫_0^T n dM] = 0 = n_0B_0` for every `T ≥ 0`. -/
theorem imp_limit (ω : Bool) :
    Tendsto (fun T =>
      coinMeasure[flow133 oneProc oneProc zeroRate impSur 0 T | coinFiltration 0] ω) atTop
      (𝓝 (disc oneProc oneProc 0 ω * impB 0 ω)) := by
  have hB0 : disc oneProc oneProc 0 ω * impB 0 ω = 0 := by simp [impB]
  rw [hB0]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with T hT
  rw [condExp_coin_lt (by norm_num), imp_flow133 hT, imp_flow133 hT]
  simp [coinXi]

/-- Cochrane (2023), A1 §1.6, p. 567: `∫|F_T − G| ≥ |F_T(true) − G(true)|/2` under the fair coin. -/
theorem integral_abs_ge (F G : Bool → ℝ) :
    |F true - G true| / 2 ≤ ∫ ω, |F ω - G ω| ∂coinMeasure := by
  rw [integral_coin]
  have := abs_nonneg (F false - G false)
  linarith

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: no `L¹` limit.** There is no `G` with
`∫_0^T Λs dr + ∫_0^T n dM → G` in `L¹`: `E_0∫_0^∞` is undefined in the `L¹` sense. -/
theorem imp_no_L1_limit : ¬ ∃ G : Bool → ℝ,
    Tendsto (fun T => ∫ ω, |flow133 oneProc oneProc zeroRate impSur 0 T ω - G ω| ∂coinMeasure)
      atTop (𝓝 0) := by
  rintro ⟨G, hG⟩
  obtain ⟨T0, hT0⟩ := eventually_atTop.1 ((tendsto_order.1 hG).2 (1 / 2) (by norm_num))
  set T := max T0 (|G true| + 3) with hTdef
  have hT : |G true| + 3 ≤ T := le_max_right _ _
  have h1 := hT0 T (le_max_left _ _)
  have h2 := integral_abs_ge (flow133 oneProc oneProc zeroRate impSur 0 T) G
  have hT0' : 0 ≤ T := by linarith [abs_nonneg (G true)]
  rw [imp_flow133 hT0' true] at h2
  simp only [coinXi, ↓reduceIte, one_mul] at h2
  rw [max_eq_left (by linarith [abs_nonneg (G true)])] at h2
  have h3 : 2 ≤ |T - 1 - G true| := by
    rw [abs_of_nonneg (by linarith [le_abs_self (G true)])]
    linarith [le_abs_self (G true)]
  linarith

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: no pathwise limit.** At `ξ = 1`,
`∫_0^T Λs dr + ∫_0^T n dM = (T − 1)⁺ → ∞`. -/
theorem imp_no_pathwise_limit : ¬ ∃ g : ℝ,
    Tendsto (fun T => flow133 oneProc oneProc zeroRate impSur 0 T true) atTop (𝓝 g) := by
  rintro ⟨g, hg⟩
  have htop : Tendsto (fun T => flow133 oneProc oneProc zeroRate impSur 0 T true) atTop atTop := by
    have h : Tendsto (fun T : ℝ => T - 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_id
    refine (h.congr' ?_)
    filter_upwards [eventually_ge_atTop 1] with T hT
    rw [imp_flow133 (by linarith) true, max_eq_left (by linarith)]
    simp [coinXi]
  exact not_tendsto_nhds_of_tendsto_atTop htop g hg

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the printed `E_t∫_t^∞` presupposes convergence.**
In `impModel` at `t = 0`: the transversality condition holds (`imp_tvc`), the valuation equation
holds in the limit form `lim_T E_0[∫_0^T Λs + ∫_0^T n dM] = n_0B_0` (`imp_limit`, as
`TidyR7MonetarismValuation.MonetaryModel.valuation_1_33_seq` asserts), yet the flows have no
`L¹` limit (`imp_no_L1_limit`) and no pathwise limit at `ξ = 1` (`imp_no_pathwise_limit`). -/
theorem imp_headline :
    Tendsto (fun T => ∫ ω, |coinMeasure[fun ω => disc oneProc oneProc T ω * impB T ω |
        coinFiltration 0] ω| ∂coinMeasure) atTop (𝓝 0) ∧
      (∀ ω, Tendsto (fun T =>
        coinMeasure[flow133 oneProc oneProc zeroRate impSur 0 T | coinFiltration 0] ω)
          atTop (𝓝 (disc oneProc oneProc 0 ω * impB 0 ω))) ∧
      (¬ ∃ G : Bool → ℝ, Tendsto (fun T =>
        ∫ ω, |flow133 oneProc oneProc zeroRate impSur 0 T ω - G ω| ∂coinMeasure) atTop (𝓝 0)) ∧
      ¬ ∃ g : ℝ, Tendsto (fun T => flow133 oneProc oneProc zeroRate impSur 0 T true) atTop (𝓝 g) :=
  ⟨imp_tvc, imp_limit, imp_no_L1_limit, imp_no_pathwise_limit⟩

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: `impModel` meets the hypotheses of the limit form
`TidyR7MonetarismValuation.MonetaryModel.valuation_1_33_seq` (with `T_k = k`), whose two sides
both hold there. -/
theorem imp_seq :
    (∀ᵐ ω ∂coinMeasure, Tendsto (fun k : ℕ =>
        coinMeasure[flow133 oneProc oneProc zeroRate impSur 0 k | coinFiltration 0] ω) atTop
        (𝓝 (disc oneProc oneProc 0 ω * impB 0 ω))) ∧
      ∀ᵐ ω ∂coinMeasure, Tendsto (fun k : ℕ => coinMeasure[fun ω =>
        disc oneProc oneProc k ω * impB k ω | coinFiltration 0] ω) atTop (𝓝 0) := by
  have h := MonetaryModel.valuation_1_33_seq impModel (fun _ _ => rfl) (s := 0)
    (fun T _ => impDom T) (fun _ _ => Integrable.of_finite) (T := fun k : ℕ => (k : ℝ))
    (fun k => Nat.cast_nonneg k)
  have h1 : ∀ᵐ ω ∂coinMeasure, Tendsto (fun k : ℕ =>
      coinMeasure[flow133 oneProc oneProc zeroRate impSur 0 k | coinFiltration 0] ω) atTop
      (𝓝 (disc oneProc oneProc 0 ω * impB 0 ω)) :=
    Eventually.of_forall fun ω => (imp_limit ω).comp tendsto_natCast_atTop_atTop
  exact ⟨h1, h.1 h1⟩

end Cochrane.Monetarism.TidyR7MonetarismCoin
