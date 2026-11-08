/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.TidyR7ProductStepJump
import Generality.TidyR7ProductStepCoin

/-!
# Bonds that jump with the news: the book's (1.32) step fails; the corrected step holds

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eq. (1.32). The fair coin `ξ = ±1` of `TidyR7ProductStepCoin`
(`coinMeasure`, `coinFiltration`) is revealed at time `1`; `M_u = ξ·1{u ≥ 1}` (`coinM`) is a
càdlàg martingale. On `[0, 2]`:

## Scenario 1: bonds jump together with `X` (`jumpB`, `jumpData`)

`B_u = b + ξ·1{u ≥ 1}` (adapted, càdlàg, of bounded variation, NOT continuous), `A = 0`, `X = M`.
`E_0[B_2X_2 − B_0X_0] = E[(b + ξ)ξ] = 1` (`jump_lhs`). Path by path `∫ X_− dB = X(1−)ξ = 0`,
`∫ B_− dA = 0`, `Σ ΔXΔB = ξ² = 1` (`jump_intLeftXB`, `jump_intBA`, `jump_jumpCov`).
* `jump_corrected`: the corrected step `TidyR7ProductStepJump.JumpStepData.jump_step`,
  `1 = 0 + 0 + 1`, both sides computed.
* `jump_book_fails`: **the book's step fails**: for EVERY partition `Σ X_iΔB_i = 0` and
  `Σ ΔX_iΔB_i = 1` path by path; `B·E_0 dX = 0` (`TidyR7ProductStep.ExpIncrLimit`); so
  `E_0[B_2X_2 − B_0X_0] = 1 ≠ 0 = lim E_0[Σ X_iΔB_i] + B·E_0 dX`.
* `jump_ls_holds`: with the Lebesgue–Stieltjes integral of the CURRENT `X`, `∫ X dB = X(1)ξ = 1`,
  so I2's two-term form `E_0∫X dB + E_0∫B dA = 1` happens to hold here (`A` has no jump).

## Scenario 2: bonds jump together with the drift part `A` (`jumpDataA`)

Same `B`, `A_u = ξ·1{u ≥ 1}`, `M = 0`. `jumpA_ls_fails`: **I2's statement
`E_s[Δ(BX)] = E_s∫X dB + E_s∫B dA` (`TidyR7ProductStep.ProductStepData.product_step`) fails for
càdlàg `B`**: `1 ≠ 1 + 1`. `jumpA_corrected`: the corrected step `1 = 0 + 0 + 1` and its
two-term form `TidyR7ProductStepJump.JumpStepData.jump_step_ls`, `1 = 1 + 0`.
So no reading of the book's two-term step is right for jumping bonds: the left-point reading fails
in scenario 1 and the Lebesgue–Stieltjes reading in scenario 2.

## Scenario 3: bonds jump, but not when `X` jumps (`lateB`, `lateData`)

`B_u = 1 + ξ·1{u ≥ 3/2}`. `late_corrected`: `1 = 1 + 0 + 0`: `∫ X_− dB = X(3/2−)ξ = 1` and the
jump covariation is `0` path by path although `B` jumps (`late_jump_B`).
-/

namespace Cochrane.Generality.TidyR7ProductStepJumpCoin

open MeasureTheory Filter Topology
open Cochrane.Generality.TidyR7StieltjesIntegral Cochrane.Generality.TidyR7StieltjesSums
  Cochrane.Generality.TidyR7ProductStep Cochrane.Generality.TidyR7ProductStepCoin
  Cochrane.Generality.TidyR7ProductStepJump Cochrane.Generality.TidyR7JumpSums

/-! ## Step functions -/

/-- Cochrane (2023), A1 §1.6, p. 567 (tool for (1.32)): the step `1{x ≥ c}`.
Not the same function as TidyR7MonetarismUI.stepAt of the Monetarism project (which is `1{r > c}`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.stepAt). -/
noncomputable def stepAt (c x : ℝ) : ℝ := if c ≤ x then 1 else 0

/-- Cochrane (2023), A1 §1.6, p. 567: `1{x ≥ 1}` is `TidyR7StieltjesSums.heaviside`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.stepAt_one). -/
theorem stepAt_one : stepAt 1 = heaviside := rfl

/-- Cochrane (2023), A1 §1.6, p. 567: the step `1{x ≥ c}` is càdlàg.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.isCadlag_stepAt). -/
theorem isCadlag_stepAt (c : ℝ) : IsCadlag (stepAt c) := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rcases le_or_gt c x with hx | hx
    · refine (continuousWithinAt_const (b := (1 : ℝ))).congr (fun y hy => ?_) ?_
      · simp only [stepAt, hx.trans (le_of_lt hy), ↓reduceIte]
      · simp only [stepAt, hx, ↓reduceIte]
    · refine (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [Ioo_mem_nhdsGT hx] with y hy
        simp only [stepAt, not_le.2 hy.2, ↓reduceIte]
      · simp only [stepAt, not_le.2 hx, ↓reduceIte]
  · rcases le_or_gt x c with hx | hx
    · refine ⟨0, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with y hy
      simp only [stepAt, not_le.2 (lt_of_lt_of_le hy hx), ↓reduceIte]
    · refine ⟨1, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [Ioo_mem_nhdsLT hx] with y hy
      simp only [stepAt, hy.1.le, ↓reduceIte]

/-- Cochrane (2023), A1 §1.6, p. 567: the step `1{x ≥ c}` has bounded variation on `[a, b]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.bv_stepAt). -/
theorem bv_stepAt (c a b : ℝ) : BoundedVariationOn (stepAt c) (Set.Icc a b) := by
  have hm : Monotone (stepAt c) := by
    intro x y hxy
    simp only [stepAt]
    split_ifs <;> first | (exfalso; linarith) | norm_num
  refine (hm.monotoneOn _).boundedVariationOn (C := 1) fun x _ => ?_
  simp only [stepAt]
  split_ifs <;> norm_num

/-- Cochrane (2023), A1 §1.6, p. 567: the path `k + m·1{u ≥ c}` is càdlàg.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.isCadlag_affine). -/
theorem isCadlag_affine (k m c : ℝ) : IsCadlag fun u => k + m * stepAt c u :=
  (isCadlag_stepAt c).continuous_comp (g := fun y => k + m * y)
    (continuous_const.add (continuous_const.mul continuous_id))

/-- Cochrane (2023), A1 §1.6, p. 567: the path `k + m·1{u ≥ c}` has bounded variation on
`[a, b]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.bv_affine). -/
theorem bv_affine (k m c a b : ℝ) :
    BoundedVariationOn (fun u => k + m * stepAt c u) (Set.Icc a b) := by
  have hk : ∀ r : ℝ, BoundedVariationOn (fun _ : ℝ => r) (Set.Icc a b) := fun r => by
    rw [BoundedVariationOn, eVariationOn.constant_on
      (Set.subsingleton_of_forall_eq r fun _ ⟨_, _, hy⟩ => hy.symm)]
    exact ENNReal.zero_ne_top
  have hm : BoundedVariationOn (fun u => m * stepAt c u) (Set.Icc a b) :=
    (hk m).fun_mul (bv_stepAt c a b)
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hk k, hm⟩) (eVariationOn_add_le _ _ _)

/-- Cochrane (2023), A1 §1.6, p. 567: **the integral against `k + m·1{u ≥ c}`**, `a < c ≤ b`:
`∫_a^b f d(k + m·1{· ≥ c}) = f(c)·m` for every `f` (`TidyR7JumpSums.rsInt_single_jump`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.rsInt_affine). -/
theorem rsInt_affine {a b c : ℝ} (f : ℝ → ℝ) (k m : ℝ) (hac : a < c) (hcb : c ≤ b) :
    rsInt a b f (fun u => k + m * stepAt c u) = f c * m := by
  rw [rsInt_single_jump (k₀ := k) (k₁ := k + m) hac hcb (bv_affine k m c a b)
    (fun x hx => by simp [stepAt, not_le.2 hx]) (fun x hx => by simp [stepAt, hx])]
  ring

/-- Cochrane (2023), A1 §1.6, p. 567: **the left limit of `k + m·1{u ≥ c}`** at `y`: `k` for
`y ≤ c`, `k + m` for `y > c`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.leftLim_affine). -/
theorem leftLim_affine (k m c y : ℝ) :
    Function.leftLim (fun u => k + m * stepAt c u) y = if c < y then k + m else k := by
  split_ifs with h
  · refine leftLim_eq_of_tendsto (tendsto_const_nhds.congr' ?_)
    filter_upwards [Ioo_mem_nhdsLT h] with z hz
    simp [stepAt, hz.1.le]
  · refine leftLim_eq_of_tendsto (tendsto_const_nhds.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp [stepAt, not_le.2 (lt_of_lt_of_le hz (not_lt.1 h))]

/-- Cochrane (2023), A1 §1.6, p. 567: the paths of `M = ξ·1{u ≥ 1}` in the form
`0 + ξ·1{u ≥ 1}`.
Restates `TidyR7ProductStepCoin.coinM` path by path.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.coinM_path). -/
theorem coinM_path (ω : Bool) : (fun u => coinM u ω) = fun u => 0 + coinXi ω * stepAt 1 u :=
  funext fun u => by simp [coinM, stepAt_one]

/-- Cochrane (2023), A1 §1.6, p. 567: `X = A + M = 0 + ξ·1{u ≥ 1}` path by path.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.coinX_path). -/
theorem coinX_path (ω : Bool) :
    (fun u => addProc coinA coinM u ω) = fun u => 0 + coinXi ω * stepAt 1 u :=
  funext fun u => by simp [addProc, coinA, coinM, stepAt_one]

/-! ## Scenario 1: bonds jumping with `X` -/

/-- Cochrane (2023), A1 §1.6, p. 567: **bonds jumping at the news date**, `B_u = b + ξ·1{u ≥ 1}`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.jumpB). -/
noncomputable def jumpB (b : ℝ) (u : ℝ) (ω : Bool) : ℝ := b + coinXi ω * stepAt 1 u

/-- Cochrane (2023), A1 §1.6, p. 567: the bond path jumps by `ξ ≠ 0` at time `1`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.jump_jumpB). -/
theorem jump_jumpB (b : ℝ) (ω : Bool) : jump (fun u => jumpB b u ω) 1 = coinXi ω := by
  simp only [jump, jumpB]
  rw [leftLim_affine]
  simp [stepAt]

/-- Cochrane (2023), A1 §1.6, p. 567: before time `1`, `B = b` is deterministic, so `B` is
adapted to the coin filtration.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.jumpB_adapted). -/
theorem jumpB_adapted (b u : ℝ) : StronglyMeasurable[coinFiltration u] (jumpB b u) := by
  by_cases hu : u < 1
  · have e : jumpB b u = fun _ => b := funext fun ω => by simp [jumpB, stepAt, not_le.2 hu]
    rw [e]
    exact stronglyMeasurable_const
  · rw [coinFiltration_ge (not_lt.1 hu)]
    exact (measurable_of_finite _).stronglyMeasurable

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: scenario 1 satisfies the hypotheses of the
corrected product step** (`TidyR7ProductStepJump.JumpStepData`) on `[0, 2]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.jumpData). -/
theorem jumpData (b : ℝ) : JumpStepData coinMeasure coinFiltration 0 2 (jumpB b) coinA coinM where
  le := by norm_num
  B_adapted u _ := jumpB_adapted b u
  B_cadlag ω := isCadlag_affine b (coinXi ω) 1
  B_bv ω := bv_affine b (coinXi ω) 1 0 2
  A_meas := coinData.A_meas
  A_cadlag := coinData.A_cadlag
  A_bv := coinData.A_bv
  M_mart := martingale_coinM
  M_cadlag := coinData.M_cadlag
  int_XB := Integrable.of_finite
  int_BA := Integrable.of_finite
  int_BM _ _ _ _ _ := Integrable.of_finite

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: **the left side, `E_0[B_2X_2 − B_0X_0] = 1`**
(`B_2X_2 = (b + ξ)ξ = bξ + 1`, `B_0X_0 = 0`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.jump_lhs). -/
theorem jump_lhs (b : ℝ) :
    coinMeasure[fun ω => jumpB b 2 ω * addProc coinA coinM 2 ω -
      jumpB b 0 ω * addProc coinA coinM 0 ω | coinFiltration 0] = fun _ => 1 := by
  rw [condExp_coin_lt (by norm_num)]
  funext _
  norm_num [jumpB, stepAt, coinA, coinM, addProc, coinXi, heaviside]
  ring

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: path by path `∫_{(0,2]} X_− dB = X(1−)·ξ = 0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.jump_intLeftXB). -/
theorem jump_intLeftXB (b : ℝ) (ω : Bool) : intLeft 0 2 (addProc coinA coinM) (jumpB b) ω = 0 := by
  simp only [intLeft, jumpB]
  rw [rsInt_affine _ b (coinXi ω) (by norm_num) (by norm_num), coinX_path, leftLim_affine]
  simp

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: path by path `∫_0^2 X dB = X(1)·ξ = ξ² = 1`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.jump_intXB). -/
theorem jump_intXB (b : ℝ) (ω : Bool) : intRS 0 2 (addProc coinA coinM) (jumpB b) ω = 1 := by
  simp only [intRS, jumpB]
  rw [rsInt_affine _ b (coinXi ω) (by norm_num) (by norm_num)]
  simp only [addProc, coinA, coinM, heaviside, le_refl, ↓reduceIte, mul_one, zero_add]
  exact coinXi_mul_self ω

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: path by path the jump covariation is
`ΔX_1ΔB_1 = ξ² = 1`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.jump_jumpCov). -/
theorem jump_jumpCov (b : ℝ) (ω : Bool) : jumpCov 0 2 (addProc coinA coinM) (jumpB b) ω = 1 := by
  have h := (jumpData b).intRS_eq ω
  rw [jump_intXB, jump_intLeftXB] at h
  linarith

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: path by path `∫ B_− dA = ∫ B dA = 0` (`A = 0`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.jump_intBA). -/
theorem jump_intBA (b : ℝ) (ω : Bool) :
    intLeft 0 2 (jumpB b) coinA ω = 0 ∧ intRS 0 2 (jumpB b) coinA ω = 0 :=
  ⟨rsInt_const_right (by norm_num) _ 0, rsInt_const_right (by norm_num) _ 0⟩

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: non-vacuity of the corrected step on the
coin.** Both sides of `TidyR7ProductStepJump.JumpStepData.jump_step` computed:
`E_0[B_2X_2 − B_0X_0] = 1`, `E_0[∫X_− dB] = 0`, `E_0[∫B_− dA] = 0`, `E_0[ΣΔXΔB] = 1`, and the
corrected identity holds, `1 = 0 + 0 + 1`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.jump_corrected). -/
theorem jump_corrected (b : ℝ) :
    coinMeasure[fun ω => jumpB b 2 ω * addProc coinA coinM 2 ω -
        jumpB b 0 ω * addProc coinA coinM 0 ω | coinFiltration 0] = (fun _ => 1) ∧
      coinMeasure[intLeft 0 2 (addProc coinA coinM) (jumpB b) | coinFiltration 0] = 0 ∧
      coinMeasure[intLeft 0 2 (jumpB b) coinA | coinFiltration 0] = 0 ∧
      coinMeasure[jumpCov 0 2 (addProc coinA coinM) (jumpB b) | coinFiltration 0] =
        (fun _ => 1) ∧
      coinMeasure[fun ω => jumpB b 2 ω * addProc coinA coinM 2 ω -
          jumpB b 0 ω * addProc coinA coinM 0 ω | coinFiltration 0] =ᵐ[coinMeasure]
        coinMeasure[intLeft 0 2 (addProc coinA coinM) (jumpB b) | coinFiltration 0] +
          coinMeasure[intLeft 0 2 (jumpB b) coinA | coinFiltration 0] +
          coinMeasure[jumpCov 0 2 (addProc coinA coinM) (jumpB b) | coinFiltration 0] := by
  have e1 : intLeft 0 2 (addProc coinA coinM) (jumpB b) = fun _ => 0 :=
    funext (jump_intLeftXB b)
  have e2 : intLeft 0 2 (jumpB b) coinA = fun _ => 0 := funext fun ω => (jump_intBA b ω).1
  have e3 : jumpCov 0 2 (addProc coinA coinM) (jumpB b) = fun _ => 1 := funext (jump_jumpCov b)
  refine ⟨jump_lhs b, ?_, ?_, ?_, (jumpData b).jump_step⟩
  · rw [e1, condExp_coin_lt (by norm_num)]
    funext _
    norm_num
  · rw [e2, condExp_coin_lt (by norm_num)]
    funext _
    norm_num
  · rw [e3, condExp_coin_lt (by norm_num)]
    funext _
    norm_num

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: for EVERY partition of `[0, 2]`, path by path,
`Σ X_iΔB_i = 0` (the only nonzero `ΔB_i` multiplies `X_{t_i}` with `t_i < 1`) and
`Σ ΔX_iΔB_i = ξ² = 1` (`TidyR7StieltjesSums.crossSum_heaviside`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.jump_sums). -/
theorem jump_sums (b : ℝ) (P : Partition 0 2) (ω : Bool) :
    sumRS P (addProc coinA coinM) (jumpB b) ω = 0 ∧
      sumCross P (addProc coinA coinM) (jumpB b) ω = 1 := by
  constructor
  · simp only [sumRS, rsSum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hlt := P.strictMono (show i < i + 1 by omega)
    simp only [addProc, coinA, coinM, jumpB, stepAt, heaviside]
    split_ifs <;> first | (exfalso; linarith) | ring
  · have e : sumCross P (addProc coinA coinM) (jumpB b) ω =
        coinXi ω * coinXi ω * crossSum P heaviside heaviside := by
      simp only [sumCross, crossSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [addProc, coinA, coinM, jumpB, stepAt_one]
      ring
    rw [e, crossSum_heaviside, coinXi_mul_self, one_mul]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the book's step FAILS for bonds that jump with
the news.** Read as the limit of the discrete step (left-point sums), the book's
`Λ/P·dB + E_t d(Λ/P)·B` is `lim E_0[Σ X_iΔB_i] + B·E_0 dX`. Here `Σ X_iΔB_i = 0` and
`Σ ΔX_iΔB_i = 1` at EVERY partition, the expected-increment integral is `B·E_0 dX = 0`, and
`E_0[B_2X_2 − B_0X_0] = 1 ≠ 0`: the missing term is the expected jump covariation `E_0[ΔXΔB] = 1`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.jump_book_fails). -/
theorem jump_book_fails (b : ℝ) :
    (∀ (P : Partition 0 2) (ω : Bool), sumRS P (addProc coinA coinM) (jumpB b) ω = 0 ∧
        sumCross P (addProc coinA coinM) (jumpB b) ω = 1) ∧
      ExpIncrLimit coinMeasure coinFiltration 0 2 (jumpB b) (addProc coinA coinM) 0 ∧
      coinMeasure[fun ω => jumpB b 2 ω * addProc coinA coinM 2 ω -
          jumpB b 0 ω * addProc coinA coinM 0 ω | coinFiltration 0] ≠
        coinMeasure[intLeft 0 2 (addProc coinA coinM) (jumpB b) | coinFiltration 0] + 0 := by
  obtain ⟨hL, hX, hA, -, -⟩ := jump_corrected b
  refine ⟨jump_sums b, ?_, ?_⟩
  · have h := (jumpData b).expIncrLimit_intLeft
    rwa [hA] at h
  · rw [hL, hX, add_zero]
    intro h
    have := congrFun h true
    norm_num at this

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: **in scenario 1 the Lebesgue–Stieltjes reading
happens to hold**: `∫_0^2 X dB = X(1)ξ = 1` (the current `X`, not `X(1−)`), so I2's two-term form
`E_0[∫X dB] + E_0[∫B dA] = 1 + 0 = E_0[B_2X_2 − B_0X_0]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.jump_ls_holds). -/
theorem jump_ls_holds (b : ℝ) :
    coinMeasure[intRS 0 2 (addProc coinA coinM) (jumpB b) | coinFiltration 0] = (fun _ => 1) ∧
      coinMeasure[intRS 0 2 (jumpB b) coinA | coinFiltration 0] = 0 := by
  have e1 : intRS 0 2 (addProc coinA coinM) (jumpB b) = fun _ => 1 := funext (jump_intXB b)
  have e2 : intRS 0 2 (jumpB b) coinA = fun _ => 0 := funext fun ω => (jump_intBA b ω).2
  constructor
  · rw [e1, condExp_coin_lt (by norm_num)]
    funext _
    norm_num
  · rw [e2, condExp_coin_lt (by norm_num)]
    funext _
    norm_num

/-! ## Scenario 2: bonds jumping with the drift part `A` -/

/-- Cochrane (2023), A1 §1.6, p. 567: the zero martingale.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.zeroM). -/
def zeroM (_ : ℝ) (_ : Bool) : ℝ := 0

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: scenario 2 satisfies the hypotheses of the
corrected product step**: `B = b + ξ·1{u ≥ 1}`, `A = ξ·1{u ≥ 1}`, `M = 0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.jumpDataA). -/
theorem jumpDataA (b : ℝ) :
    JumpStepData coinMeasure coinFiltration 0 2 (jumpB b) coinM zeroM where
  le := by norm_num
  B_adapted u _ := jumpB_adapted b u
  B_cadlag ω := isCadlag_affine b (coinXi ω) 1
  B_bv ω := bv_affine b (coinXi ω) 1 0 2
  A_meas _ _ := measurable_of_finite _
  A_cadlag := coinData.M_cadlag
  A_bv ω := by rw [coinM_path]; exact bv_affine 0 (coinXi ω) 1 0 2
  M_mart := martingale_zero ℝ coinFiltration coinMeasure
  M_cadlag _ := IsCadlag.const
  int_XB := Integrable.of_finite
  int_BA := Integrable.of_finite
  int_BM _ _ _ _ _ := Integrable.of_finite

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: I2's two-term form FAILS for càdlàg bonds.**
In scenario 2, `E_0[B_2X_2 − B_0X_0] = 1`, but `E_0[∫_0^2 X dB] = 1` and
`E_0[∫_0^2 B dA] = E[(b + ξ)ξ] = 1`: `1 ≠ 1 + 1`. The conclusion of
`TidyR7ProductStep.ProductStepData.product_step` does not extend to bonds that jump.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.jumpA_ls_fails). -/
theorem jumpA_ls_fails (b : ℝ) :
    coinMeasure[fun ω => jumpB b 2 ω * addProc coinM zeroM 2 ω -
        jumpB b 0 ω * addProc coinM zeroM 0 ω | coinFiltration 0] = (fun _ => 1) ∧
      coinMeasure[intRS 0 2 (addProc coinM zeroM) (jumpB b) | coinFiltration 0] = (fun _ => 1) ∧
      coinMeasure[intRS 0 2 (jumpB b) coinM | coinFiltration 0] = (fun _ => 1) ∧
      coinMeasure[fun ω => jumpB b 2 ω * addProc coinM zeroM 2 ω -
          jumpB b 0 ω * addProc coinM zeroM 0 ω | coinFiltration 0] ≠
        coinMeasure[intRS 0 2 (addProc coinM zeroM) (jumpB b) | coinFiltration 0] +
          coinMeasure[intRS 0 2 (jumpB b) coinM | coinFiltration 0] := by
  have hX : ∀ ω, (fun u => addProc coinM zeroM u ω) = fun u => 0 + coinXi ω * stepAt 1 u :=
    fun ω => funext fun u => by simp [addProc, zeroM, coinM, stepAt_one]
  have e1 : intRS 0 2 (addProc coinM zeroM) (jumpB b) = fun _ => 1 := funext fun ω => by
    simp only [intRS, jumpB]
    rw [rsInt_affine _ b (coinXi ω) (by norm_num) (by norm_num)]
    simp [addProc, zeroM, coinM, heaviside, coinXi_mul_self]
  have e2 : intRS 0 2 (jumpB b) coinM = fun ω => (b + coinXi ω) * coinXi ω := funext fun ω => by
    simp only [intRS]
    rw [coinM_path, rsInt_affine _ 0 (coinXi ω) (by norm_num) (by norm_num)]
    simp [jumpB, stepAt]
  have hl : coinMeasure[fun ω => jumpB b 2 ω * addProc coinM zeroM 2 ω -
      jumpB b 0 ω * addProc coinM zeroM 0 ω | coinFiltration 0] = fun _ => 1 := by
    rw [condExp_coin_lt (by norm_num)]
    funext _
    norm_num [jumpB, stepAt, zeroM, coinM, addProc, coinXi, heaviside]
    ring
  have h2 : coinMeasure[intRS 0 2 (jumpB b) coinM | coinFiltration 0] = fun _ => 1 := by
    rw [e2, condExp_coin_lt (by norm_num)]
    funext _
    simp [coinXi]
    ring
  have h1 : coinMeasure[intRS 0 2 (addProc coinM zeroM) (jumpB b) | coinFiltration 0] =
      fun _ => 1 := by
    rw [e1, condExp_coin_lt (by norm_num)]
    funext _
    norm_num
  refine ⟨hl, h1, h2, ?_⟩
  rw [hl, h1, h2]
  intro h
  have := congrFun h true
  norm_num at this

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the corrected step holds in scenario 2**:
`E_0[∫X_− dB] = 0`, `E_0[∫B_− dA] = E[bξ] = 0`, `E_0[ΣΔXΔB] = 1`: `1 = 0 + 0 + 1`
(`TidyR7ProductStepJump.JumpStepData.jump_step`); and the two-term form
`TidyR7ProductStepJump.JumpStepData.jump_step_ls`, `1 = E_0∫X dB + E_0∫B_− dA = 1 + 0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.jumpA_corrected). -/
theorem jumpA_corrected (b : ℝ) :
    coinMeasure[intLeft 0 2 (addProc coinM zeroM) (jumpB b) | coinFiltration 0] = 0 ∧
      coinMeasure[intLeft 0 2 (jumpB b) coinM | coinFiltration 0] = 0 ∧
      coinMeasure[jumpCov 0 2 (addProc coinM zeroM) (jumpB b) | coinFiltration 0] =
        (fun _ => 1) ∧
      coinMeasure[fun ω => jumpB b 2 ω * addProc coinM zeroM 2 ω -
          jumpB b 0 ω * addProc coinM zeroM 0 ω | coinFiltration 0] =ᵐ[coinMeasure]
        coinMeasure[intLeft 0 2 (addProc coinM zeroM) (jumpB b) | coinFiltration 0] +
          coinMeasure[intLeft 0 2 (jumpB b) coinM | coinFiltration 0] +
          coinMeasure[jumpCov 0 2 (addProc coinM zeroM) (jumpB b) | coinFiltration 0] ∧
      coinMeasure[fun ω => jumpB b 2 ω * addProc coinM zeroM 2 ω -
          jumpB b 0 ω * addProc coinM zeroM 0 ω | coinFiltration 0] =ᵐ[coinMeasure]
        coinMeasure[intRS 0 2 (addProc coinM zeroM) (jumpB b) | coinFiltration 0] +
          coinMeasure[intLeft 0 2 (jumpB b) coinM | coinFiltration 0] := by
  have hX : ∀ ω, (fun u => addProc coinM zeroM u ω) = fun u => 0 + coinXi ω * stepAt 1 u :=
    fun ω => funext fun u => by simp [addProc, zeroM, coinM, stepAt_one]
  have e1 : intLeft 0 2 (addProc coinM zeroM) (jumpB b) = fun _ => 0 := funext fun ω => by
    simp only [intLeft, jumpB]
    rw [rsInt_affine _ b (coinXi ω) (by norm_num) (by norm_num), hX, leftLim_affine]
    simp
  have e2 : intLeft 0 2 (jumpB b) coinM = fun ω => b * coinXi ω := funext fun ω => by
    simp only [intLeft]
    rw [coinM_path, rsInt_affine _ 0 (coinXi ω) (by norm_num) (by norm_num)]
    simp only [jumpB]
    rw [leftLim_affine]
    simp
  have e3 : intRS 0 2 (addProc coinM zeroM) (jumpB b) = fun _ => 1 := funext fun ω => by
    simp only [intRS, jumpB]
    rw [rsInt_affine _ b (coinXi ω) (by norm_num) (by norm_num)]
    simp [addProc, zeroM, coinM, heaviside, coinXi_mul_self]
  have e4 : jumpCov 0 2 (addProc coinM zeroM) (jumpB b) = fun _ => 1 := funext fun ω => by
    have h := (jumpDataA b).intRS_eq ω
    rw [congrFun e3 ω, congrFun e1 ω] at h
    linarith
  refine ⟨?_, ?_, ?_, (jumpDataA b).jump_step, (jumpDataA b).jump_step_ls⟩
  · rw [e1, condExp_coin_lt (by norm_num)]
    funext _
    norm_num
  · rw [e2, condExp_coin_lt (by norm_num)]
    funext _
    simp [coinXi]
  · rw [e4, condExp_coin_lt (by norm_num)]
    funext _
    norm_num

/-! ## Scenario 3: bonds jumping when `X` does not -/

/-- Cochrane (2023), A1 §1.6, p. 567: bonds jumping at `3/2`, after the news,
`B_u = 1 + ξ·1{u ≥ 3/2}`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.lateB). -/
noncomputable def lateB (u : ℝ) (ω : Bool) : ℝ := 1 + coinXi ω * stepAt (3 / 2) u

/-- Cochrane (2023), A1 §1.6, p. 567: the bond path jumps by `ξ ≠ 0` at `3/2`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.late_jump_B). -/
theorem late_jump_B (ω : Bool) : jump (fun u => lateB u ω) (3 / 2) = coinXi ω := by
  simp only [jump, lateB]
  rw [leftLim_affine]
  simp [stepAt]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: scenario 3 satisfies the hypotheses of the
corrected product step.**
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.lateData). -/
theorem lateData : JumpStepData coinMeasure coinFiltration 0 2 lateB coinA coinM where
  le := by norm_num
  B_adapted u _ := by
    by_cases hu : u < 1
    · have e : lateB u = fun _ => 1 := funext fun ω => by
        simp [lateB, stepAt, not_le.2 (hu.trans (by norm_num : (1 : ℝ) < 3 / 2))]
      rw [e]
      exact stronglyMeasurable_const
    · rw [coinFiltration_ge (not_lt.1 hu)]
      exact (measurable_of_finite _).stronglyMeasurable
  B_cadlag ω := isCadlag_affine 1 (coinXi ω) (3 / 2)
  B_bv ω := bv_affine 1 (coinXi ω) (3 / 2) 0 2
  A_meas := coinData.A_meas
  A_cadlag := coinData.A_cadlag
  A_bv := coinData.A_bv
  M_mart := martingale_coinM
  M_cadlag := coinData.M_cadlag
  int_XB := Integrable.of_finite
  int_BA := Integrable.of_finite
  int_BM _ _ _ _ _ := Integrable.of_finite

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: non-vacuity with a jump of `B` but no common
jump.** `E_0[B_2X_2 − B_0X_0] = 1`; path by path `∫X_− dB = X(3/2−)ξ = ξ² = 1`, `∫B_− dA = 0`, and
the jump covariation is `0` although `B` jumps (`late_jump_B`): `1 = 1 + 0 + 0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStepJumpCoin.late_corrected). -/
theorem late_corrected :
    coinMeasure[fun ω => lateB 2 ω * addProc coinA coinM 2 ω -
        lateB 0 ω * addProc coinA coinM 0 ω | coinFiltration 0] = (fun _ => 1) ∧
      intLeft 0 2 (addProc coinA coinM) lateB = (fun _ => 1) ∧
      intLeft 0 2 lateB coinA = (fun _ => 0) ∧
      jumpCov 0 2 (addProc coinA coinM) lateB = (fun _ => 0) ∧
      coinMeasure[fun ω => lateB 2 ω * addProc coinA coinM 2 ω -
          lateB 0 ω * addProc coinA coinM 0 ω | coinFiltration 0] =ᵐ[coinMeasure]
        coinMeasure[intLeft 0 2 (addProc coinA coinM) lateB | coinFiltration 0] +
          coinMeasure[intLeft 0 2 lateB coinA | coinFiltration 0] +
          coinMeasure[jumpCov 0 2 (addProc coinA coinM) lateB | coinFiltration 0] := by
  have e1 : intLeft 0 2 (addProc coinA coinM) lateB = fun _ => 1 := funext fun ω => by
    simp only [intLeft, lateB]
    rw [rsInt_affine _ 1 (coinXi ω) (by norm_num) (by norm_num), coinX_path, leftLim_affine]
    simp only [show (1 : ℝ) < 3 / 2 by norm_num, ↓reduceIte, zero_add]
    exact coinXi_mul_self ω
  have e3 : intRS 0 2 (addProc coinA coinM) lateB = fun _ => 1 := funext fun ω => by
    simp only [intRS, lateB]
    rw [rsInt_affine _ 1 (coinXi ω) (by norm_num) (by norm_num)]
    simp [addProc, coinA, coinM, heaviside, coinXi_mul_self, show (1 : ℝ) ≤ 3 / 2 by norm_num]
  have e4 : jumpCov 0 2 (addProc coinA coinM) lateB = fun _ => 0 := funext fun ω => by
    have h := lateData.intRS_eq ω
    rw [congrFun e3 ω, congrFun e1 ω] at h
    linarith
  refine ⟨?_, e1, funext fun _ => rsInt_const_right (by norm_num) _ 0, e4, lateData.jump_step⟩
  rw [condExp_coin_lt (by norm_num)]
  funext _
  simp [lateB, stepAt, coinA, coinM, addProc, coinXi, heaviside]
  norm_num

end Cochrane.Generality.TidyR7ProductStepJumpCoin
