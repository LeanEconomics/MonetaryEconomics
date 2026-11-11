/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR11JumpDiffCoinBM

/-!
# The jump-diffusion product step of (1.32) on a Brownian motion with a coin

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eq. (1.32). A realisation of
`TidyR11JumpDiffStep.JumpDiffData` in which BOTH parts of the covariation of bonds and `Λ/P` are
present, on the space of `TidyR11JumpDiffCoinBM` (Brownian motion `W`, independent coin `ξ = ±1`
revealed at time `1`), on `[0, 2]`.

## The realisation (parameters `c d e : ℝ`)

* `Λ/P = X = A + M_d + M_c` with `A = 0`, `M_d = e·ξ·1{u ≥ 1}` (`TidyR11JumpDiffCoinBM.cbJ`),
  `M_c = d·W` (`K = d`);
* bonds `B = B_bv + B_c` with `B_bv = e·ξ·1{u ≥ 1}` (a lump bond issue at the news date, moving
  with `Λ/P`) and `B_c = c·W` (`σ_B = c`).

## Results

* `jdcbData`: the hypotheses of the jump-diffusion step hold for all `c d e`.
* `jdcb_contCov`, `jdcb_jumpCov`, `jdcb_fullCov`: path by path the continuous covariation is
  `∫_0^2 σ_BK du = 2cd`, the jump covariation `ΔB_1ΔX_1 = e²ξ² = e²`, the full covariation
  `2cd + e²`.
* `jdcb_step`: the unified step, `E_0[B_2X_2 − B_0X_0] = E_0[∫X_− dB_bv] + 2cd + e²` a.s.
* `jdcb_book_iff`: the book's two-term step holds iff `2cd + e² = 0`.
* `jdcb_book_fails`: for `c = d = e = 1` both parts are nonzero and the book's step fails.
* `jdcb_cancel`: for `c = −1/2`, `d = e = 1` the continuous part (`−1`) and the jump part (`1`)
  are both nonzero and CANCEL: the book's step holds although bonds covary with `Λ/P` both
  continuously and at the jump.
* `jdcb_recovers_jump_step` (`c = d = 0`) and `jdcb_recovers_bond_step` (`e = 0`): the reductions
  `TidyR11JumpDiffStep.JumpDiffData.jd_recovers_jump_step` and
  `TidyR11JumpDiffStep.JumpDiffData.jd_recovers_bond_step` are not vacuous.
-/

namespace Cochrane.Monetarism.TidyR11JumpDiffCoinBMStep

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesIntegral Cochrane.Monetarism.TidyR7StieltjesSums
  Cochrane.Monetarism.TidyR7CondDominated Cochrane.Monetarism.TidyR7ProductStep
  Cochrane.Monetarism.TidyR7JumpSums Cochrane.Monetarism.TidyR7ProductStepJump
  Cochrane.Monetarism.TidyR7BrownianTools Cochrane.Monetarism.TidyR7BrownianQV
  Cochrane.Monetarism.TidyR7ProductStepCoin Cochrane.Monetarism.TidyR7ProductStepJumpCoin
  Cochrane.Monetarism.TidyR10DoobProductStep Cochrane.Monetarism.TidyR11JumpDiffStep
  Cochrane.Monetarism.TidyR11JumpDiffCoinBM
open scoped NNReal

/-- Cochrane (2023), A1 §1.6, p. 567: the diffusive bond component `B_c = c·W`. -/
noncomputable def jdBc (c : ℝ) (u : ℝ) (ω : (ℕ → ℝ) × Bool) : ℝ := c * bmReal cbW u ω

/-- Cochrane (2023), A1 §1.6, p. 567: the diffusive part of `Λ/P`, `M_c = d·W`. -/
noncomputable def jdMc (d : ℝ) (u : ℝ) (ω : (ℕ → ℝ) × Bool) : ℝ := d * bmReal cbW u ω

/-- Cochrane (2023), A1 §1.6, p. 567: the paths of `c·W` are continuous. -/
theorem continuous_jdBc (c : ℝ) (ω : (ℕ → ℝ) × Bool) : Continuous fun u => jdBc c u ω :=
  continuous_const.mul (continuous_bmReal (continuous_cbW ω))

/-- Cochrane (2023), A1 §1.6, p. 567: the values of `c·W` are measurable. -/
theorem measurable_jdBc (c u : ℝ) : Measurable (jdBc c u) :=
  measurable_const.mul (measurable_cbW _)

/-- Cochrane (2023), A1 §1.6, p. 567: the paths of `e·ξ·1{u ≥ 1}` are càdlàg.
An instance of `TidyR7ProductStepJumpCoin.isCadlag_affine`. -/
theorem cadlag_cbJ (e : ℝ) (ω : (ℕ → ℝ) × Bool) : IsCadlag fun u => cbJ e u ω := by
  rw [cbJ_path]
  exact isCadlag_affine 0 _ 1

/-- Cochrane (2023), A1 §1.6, p. 567: the paths of `e·ξ·1{u ≥ 1}` have bounded variation.
An instance of `TidyR7ProductStepJumpCoin.bv_affine`. -/
theorem bv_cbJ (e : ℝ) (ω : (ℕ → ℝ) × Bool) :
    BoundedVariationOn (fun u => cbJ e u ω) (Set.Icc 0 2) := by
  rw [cbJ_path]
  exact bv_affine 0 _ 1 0 2

/-- Cochrane (2023), A1 §1.6, p. 567: the values of `e·ξ·1{u ≥ 1}` are measurable. -/
theorem measurable_cbJ (e u : ℝ) : Measurable (cbJ e u) :=
  ((measurable_of_finite fun b : Bool => e * coinXi b).comp measurable_snd).mul measurable_const

/-- Cochrane (2023), A1 §1.6, p. 567: the variation of `e·ξ·1{u ≥ 1}` on `[0, 2]` as a function
of the coin. -/
noncomputable def varJ (e : ℝ) (b : Bool) : ℝ :=
  (eVariationOn (fun u => e * coinXi b * stepAt 1 u) (Set.Icc 0 2)).toReal

/-- Cochrane (2023), A1 §1.6, p. 567: `Var_{[0,2]}(e·ξ·1{u ≥ 1})` depends on the coin only. -/
theorem pathVar_cbJ (e : ℝ) : pathVar 0 2 (cbJ e) = fun ω => varJ e ω.2 := rfl

/-- Cochrane (2023), A1 §1.6, p. 567: `Var_{[0,2]}(e·ξ·1{u ≥ 1})` is measurable. -/
theorem measurable_pathVar_cbJ (e : ℝ) : Measurable (pathVar 0 2 (cbJ e)) := by
  rw [pathVar_cbJ]
  exact (measurable_of_finite (varJ e)).comp measurable_snd

/-- Cochrane (2023), A1 §1.6, p. 567: `Var_{[0,2]}(e·ξ·1{u ≥ 1})` is bounded (two values). -/
theorem pathVar_cbJ_le (e : ℝ) (ω : (ℕ → ℝ) × Bool) :
    pathVar 0 2 (cbJ e) ω ≤ varJ e true + varJ e false := by
  rw [pathVar_cbJ]
  have h1 : 0 ≤ varJ e true := ENNReal.toReal_nonneg
  have h2 : 0 ≤ varJ e false := ENNReal.toReal_nonneg
  obtain ⟨x, b⟩ := ω
  cases b
  · change varJ e false ≤ _
    linarith
  · change varJ e true ≤ _
    linarith

/-- Cochrane (2023), A1 §1.6, p. 567: the zero path has bounded variation.
Mathlib `eVariationOn.constant_on`. -/
theorem jdcb_bv_const_path (a b : ℝ) : BoundedVariationOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc a b) := by
  rw [BoundedVariationOn, eVariationOn.constant_on
    (Set.subsingleton_of_forall_eq (0 : ℝ) fun _ ⟨_, _, hy⟩ => hy.symm)]
  exact ENNReal.zero_ne_top

/-- Cochrane (2023), A1 §1.6, p. 567: `sup|Y| · Var(0) = 0` is integrable.
Uses `TidyR10DoobProductStep.pathVar_zero`. -/
theorem jdcb_integrable_pathSup_mul_zero (Y : ℝ → (ℕ → ℝ) × Bool → ℝ) :
    Integrable (fun ω => pathSup 0 2 Y ω * pathVar 0 2 (fun _ _ => (0 : ℝ)) ω) cbMeasure := by
  simp only [pathVar_zero, mul_zero]
  exact integrable_zero _ _ _

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the realisation satisfies the hypotheses of the
jump-diffusion product step** on `[0, 2]`, for all `c d e`. -/
theorem jdcbData (c d e : ℝ) :
    JumpDiffData cbMeasure cbF cbW 0 2 (cbJ e) (jdBc c) (fun _ _ => 0) (cbJ e) (jdMc d)
      (fun _ _ => c) (fun _ _ => d) |c| |d| := by
  have := isProbabilityMeasure_cbMeasure
  have hB := isPreBrownianReal_cbW
  have hW := measurable_cbW
  have h𝓕 := cbF_isBM
  have mBc := martingale_const_mul_bm hB hW h𝓕 c
  have mMc := martingale_const_mul_bm hB hW h𝓕 d
  have mJ := martingale_cbJ e
  have h02 : (0 : ℝ) < 2 := by norm_num
  have hV := pathVar_cbJ_le e
  have hX : Martingale (addProc (cbJ e) (jdMc d)) cbF cbMeasure := mJ.add mMc
  exact {
    bv := {
      le := h02.le
      B_adapted := fun u _ => mJ.1 u
      B_cadlag := cadlag_cbJ e
      B_bv := bv_cbJ e
      A_meas := fun _ _ => measurable_const
      A_cadlag := fun _ => IsCadlag.const
      A_bv := fun _ => jdcb_bv_const_path 0 2
      M_mart := hX
      M_cadlag := fun ω => (cadlag_cbJ e ω).fun_add (continuous_jdBc d ω).isCadlag
      int_XB := cb_integrable_pathSup_mul_pathVar hB hW h𝓕 continuous_cbW h02 (abs_nonneg e)
        (abs_nonneg d) (fun u _ => measurable_const.add ((measurable_cbJ e u).add
          (measurable_jdBc d u)))
        (fun u _ ω => by
          simp only [addProc, zero_add]
          refine (abs_add_le _ _).trans (add_le_add (abs_cbJ_le e u ω) ?_)
          change |d * bmReal cbW u ω| ≤ |d| * |bmReal cbW u ω|
          rw [abs_mul])
        (measurable_pathVar_cbJ e) hV
      int_BA := jdcb_integrable_pathSup_mul_zero _
      int_BM := integrable_mul_incr_of_bound (fun u _ ω => abs_cbJ_le e u ω)
        (fun u _ => measurable_cbJ e u) hX.integrable }
    cA := {
      le := h02.le
      B_adapted := fun _ _ => stronglyMeasurable_const
      B_cadlag := fun _ => IsCadlag.const
      B_bv := fun _ => jdcb_bv_const_path 0 2
      A_meas := fun _ _ => measurable_const
      A_cadlag := fun _ => IsCadlag.const
      A_bv := fun _ => jdcb_bv_const_path 0 2
      M_mart := mBc
      M_cadlag := fun ω => (continuous_jdBc c ω).isCadlag
      int_XB := jdcb_integrable_pathSup_mul_zero _
      int_BA := jdcb_integrable_pathSup_mul_zero _
      int_BM := fun _ _ _ _ _ => by
        simp only [zero_mul]
        exact integrable_zero _ _ _ }
    cM := {
      le := h02.le
      B_adapted := fun u _ => mJ.1 u
      B_cadlag := cadlag_cbJ e
      B_bv := bv_cbJ e
      A_meas := fun _ _ => measurable_const
      A_cadlag := fun _ => IsCadlag.const
      A_bv := fun _ => jdcb_bv_const_path 0 2
      M_mart := mBc
      M_cadlag := fun ω => (continuous_jdBc c ω).isCadlag
      int_XB := cb_integrable_pathSup_mul_pathVar hB hW h𝓕 continuous_cbW h02 le_rfl
        (abs_nonneg c) (fun u _ => measurable_const.add (measurable_jdBc c u))
        (fun u _ ω => by
          simp only [addProc, zero_add]
          change |c * bmReal cbW u ω| ≤ |c| * |bmReal cbW u ω|
          rw [abs_mul])
        (measurable_pathVar_cbJ e) hV
      int_BA := jdcb_integrable_pathSup_mul_zero _
      int_BM := integrable_mul_incr_of_bound (fun u _ ω => abs_cbJ_le e u ω)
        (fun u _ => measurable_cbJ e u) mBc.integrable }
    Md_mart := mJ
    int_cM := fun u v _ _ _ => by
      refine ((mBc.integrable u).norm.mul_const (2 * |e|)).mono'
        ((measurable_jdBc c u).mul ((measurable_cbJ e v).sub
          (measurable_cbJ e u))).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc |cbJ e v ω - cbJ e u ω| ≤ |cbJ e v ω| + |cbJ e u ω| := abs_sub _ _
        _ ≤ |e| + |e| := add_le_add (abs_cbJ_le e v ω) (abs_cbJ_le e u ω)
        _ = 2 * |e| := by ring
    Bc_cont := continuous_jdBc c
    Mc_cont := continuous_jdBc d
    Bc_ito := itoProcess_const_mul_bm hB hW h𝓕 le_rfl c
    Mc_ito := itoProcess_const_mul_bm hB hW h𝓕 le_rfl d }

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the continuous covariation** of the
realisation: `∫_0^2 σ_BK du = 2cd` path by path. -/
theorem jdcb_contCov (c d : ℝ) :
    (fun ω : (ℕ → ℝ) × Bool => ∫ u in (0 : ℝ)..2, (fun _ _ => c) u ω * (fun _ _ => d) u ω) =
      fun _ => 2 * (c * d) := by
  funext ω
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the jump covariation** of the realisation:
`Σ_{0<u≤2} ΔB_uΔX_u = (eξ)² = e²` path by path. -/
theorem jdcb_jumpCov (c d e : ℝ) (ω : (ℕ → ℝ) × Bool) :
    jumpCov 0 2 (addProc (fun _ _ => 0) (addProc (cbJ e) (jdMc d)))
      (addProc (cbJ e) (jdBc c)) ω = e ^ 2 := by
  rw [(jdcbData c d e).jumpCov_eq_bv ω]
  set m := e * coinXi ω.2 with hm
  have hf : (fun u => addProc (fun _ _ => (0 : ℝ)) (cbJ e) u ω) =
      fun u => 0 + m * stepAt 1 u := funext fun u => by simp [addProc, cbJ, hm]
  have hg : (fun u => cbJ e u ω) = fun u => 0 + m * stepAt 1 u := cbJ_path e ω
  simp only [jumpCov]
  rw [hf, hg, jumpSum_eq (by norm_num) (isCadlag_affine 0 m 1) (bv_affine 0 m 1 0 2)
    (isCadlag_affine 0 m 1), rsInt_affine _ 0 m (by norm_num) (by norm_num),
    rsInt_affine _ 0 m (by norm_num) (by norm_num), leftLim_affine]
  have h2 : m * m = e ^ 2 := by
    rw [hm]
    have := coinXi_mul_self ω.2
    calc e * coinXi ω.2 * (e * coinXi ω.2) = e ^ 2 * (coinXi ω.2 * coinXi ω.2) := by ring
      _ = e ^ 2 := by rw [this, mul_one]
  simp only [stepAt, le_refl, ↓reduceIte, lt_irrefl, mul_one, zero_add, zero_mul, sub_zero]
  exact h2

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the full covariation** of the realisation:
`[B, X]_2 − [B, X]_0 = 2cd + e²` path by path. -/
theorem jdcb_fullCov (c d e : ℝ) :
    fullCov 0 2 (fun _ _ => c) (fun _ _ => d)
      (addProc (fun _ _ => 0) (addProc (cbJ e) (jdMc d))) (addProc (cbJ e) (jdBc c)) =
      fun _ => 2 * (c * d) + e ^ 2 := by
  funext ω
  have h := congrFun (jdcb_contCov c d) ω
  simp only [fullCov] at h ⊢
  rw [h, jdcb_jumpCov]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the unified step on the realisation.** Almost
surely `E_0[B_2X_2 − B_0X_0] = E_0[∫_{(0,2]} X_− dB_bv] + 2cd + e²`: continuous covariation `2cd`,
jump covariation `e²`. -/
theorem jdcb_step (c d e : ℝ) :
    cbMeasure[fun ω => addProc (cbJ e) (jdBc c) 2 ω *
        addProc (fun _ _ => 0) (addProc (cbJ e) (jdMc d)) 2 ω -
        addProc (cbJ e) (jdBc c) 0 ω * addProc (fun _ _ => 0) (addProc (cbJ e) (jdMc d)) 0 ω
        | cbF 0] =ᵐ[cbMeasure]
      cbMeasure[intLeft 0 2 (addProc (fun _ _ => 0) (addProc (cbJ e) (jdMc d))) (cbJ e)
        | cbF 0] + fun _ => 2 * (c * d) + e ^ 2 := by
  have := isProbabilityMeasure_cbMeasure
  have h := (jdcbData c d e).jump_diff_step_fullCov isPreBrownianReal_cbW measurable_cbW cbF_isBM
    le_rfl (by norm_num)
  have e0 : intLeft 0 2 (addProc (cbJ e) (jdBc c)) (fun _ _ => (0 : ℝ)) = 0 :=
    funext fun ω => rsInt_const_right (by norm_num) _ 0
  rw [jdcb_fullCov, e0, condExp_zero, condExp_const (cbF.le 0), add_zero] at h
  exact h

/-- Cochrane (2023), A1 §1.6, p. 567: on the probability space a constant function is a.e. `0`
iff the constant is `0`. -/
theorem jdcb_const_ae_zero_iff (k : ℝ) :
    (fun _ : (ℕ → ℝ) × Bool => k) =ᵐ[cbMeasure] 0 ↔ k = 0 := by
  have := isProbabilityMeasure_cbMeasure
  constructor
  · intro h
    obtain ⟨ω, hω⟩ := h.exists
    exact hω
  · intro h
    exact Eventually.of_forall fun _ => h

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: on the realisation the book's two-term step
holds iff `2cd + e² = 0`**, i.e. iff the continuous and jump covariations cancel. -/
theorem jdcb_book_iff (c d e : ℝ) :
    (cbMeasure[fun ω => addProc (cbJ e) (jdBc c) 2 ω *
        addProc (fun _ _ => 0) (addProc (cbJ e) (jdMc d)) 2 ω -
        addProc (cbJ e) (jdBc c) 0 ω * addProc (fun _ _ => 0) (addProc (cbJ e) (jdMc d)) 0 ω
        | cbF 0] =ᵐ[cbMeasure]
      cbMeasure[intLeft 0 2 (addProc (fun _ _ => 0) (addProc (cbJ e) (jdMc d))) (cbJ e) | cbF 0]
        + cbMeasure[intLeft 0 2 (addProc (cbJ e) (jdBc c)) (fun _ _ => 0) | cbF 0]) ↔
      2 * (c * d) + e ^ 2 = 0 := by
  have := isProbabilityMeasure_cbMeasure
  rw [(jdcbData c d e).jd_book_iff isPreBrownianReal_cbW measurable_cbW cbF_isBM le_rfl
    (by norm_num), jdcb_fullCov, condExp_const (cbF.le 0)]
  exact jdcb_const_ae_zero_iff _

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the book's step fails when bonds covary with
`Λ/P` both continuously and at the jump** (`c = d = e = 1`: continuous part `2`, jump part `1`,
both nonzero; `2 + 1 ≠ 0`). -/
theorem jdcb_book_fails :
    (fun ω : (ℕ → ℝ) × Bool => ∫ u in (0 : ℝ)..2, (fun _ _ => (1 : ℝ)) u ω *
        (fun _ _ => (1 : ℝ)) u ω) = (fun _ => 2) ∧
      (∀ ω, jumpCov 0 2 (addProc (fun _ _ => 0) (addProc (cbJ 1) (jdMc 1)))
        (addProc (cbJ 1) (jdBc 1)) ω = 1) ∧
      ¬ (cbMeasure[fun ω => addProc (cbJ 1) (jdBc 1) 2 ω *
          addProc (fun _ _ => 0) (addProc (cbJ 1) (jdMc 1)) 2 ω -
          addProc (cbJ 1) (jdBc 1) 0 ω * addProc (fun _ _ => 0) (addProc (cbJ 1) (jdMc 1)) 0 ω
          | cbF 0] =ᵐ[cbMeasure]
        cbMeasure[intLeft 0 2 (addProc (fun _ _ => 0) (addProc (cbJ 1) (jdMc 1))) (cbJ 1) | cbF 0]
          + cbMeasure[intLeft 0 2 (addProc (cbJ 1) (jdBc 1)) (fun _ _ => 0) | cbF 0]) := by
  refine ⟨by rw [jdcb_contCov]; norm_num, fun ω => by rw [jdcb_jumpCov]; norm_num, ?_⟩
  rw [jdcb_book_iff]
  norm_num

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the continuous and jump covariations can cancel**
(`c = −1/2`, `d = e = 1`): the continuous covariation is `−1 ≠ 0`, the jump covariation is
`1 ≠ 0`, and the book's two-term step HOLDS. So the book's step is not "no diffusive bonds and
no common jumps": the exact condition is `E_s[[B, Λ/P]_t − [B, Λ/P]_s] = 0`. -/
theorem jdcb_cancel :
    (fun ω : (ℕ → ℝ) × Bool => ∫ u in (0 : ℝ)..2, (fun _ _ => (-1 / 2 : ℝ)) u ω *
        (fun _ _ => (1 : ℝ)) u ω) = (fun _ => -1) ∧
      (∀ ω, jumpCov 0 2 (addProc (fun _ _ => 0) (addProc (cbJ 1) (jdMc 1)))
        (addProc (cbJ 1) (jdBc (-1 / 2))) ω = 1) ∧
      (cbMeasure[fun ω => addProc (cbJ 1) (jdBc (-1 / 2)) 2 ω *
          addProc (fun _ _ => 0) (addProc (cbJ 1) (jdMc 1)) 2 ω -
          addProc (cbJ 1) (jdBc (-1 / 2)) 0 ω *
            addProc (fun _ _ => 0) (addProc (cbJ 1) (jdMc 1)) 0 ω
          | cbF 0] =ᵐ[cbMeasure]
        cbMeasure[intLeft 0 2 (addProc (fun _ _ => 0) (addProc (cbJ 1) (jdMc 1))) (cbJ 1) | cbF 0]
          + cbMeasure[intLeft 0 2 (addProc (cbJ 1) (jdBc (-1 / 2))) (fun _ _ => 0) | cbF 0]) := by
  refine ⟨by rw [jdcb_contCov]; norm_num, fun ω => by rw [jdcb_jumpCov]; norm_num, ?_⟩
  rw [jdcb_book_iff]
  norm_num

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: non-vacuity of the jump-only reduction**
(`c = d = 0`): `TidyR11JumpDiffStep.JumpDiffData.jd_recovers_jump_step` applies to the realisation
and gives I4's three-term step for `B = X = e·ξ·1{u ≥ 1}`. -/
theorem jdcb_recovers_jump_step (e : ℝ) :
    cbMeasure[fun ω => cbJ e 2 ω * addProc (fun _ _ => 0) (cbJ e) 2 ω -
        cbJ e 0 ω * addProc (fun _ _ => 0) (cbJ e) 0 ω | cbF 0] =ᵐ[cbMeasure]
      cbMeasure[intLeft 0 2 (addProc (fun _ _ => 0) (cbJ e)) (cbJ e) | cbF 0]
        + cbMeasure[intLeft 0 2 (cbJ e) (fun _ _ => 0) | cbF 0]
        + cbMeasure[jumpCov 0 2 (addProc (fun _ _ => 0) (cbJ e)) (cbJ e) | cbF 0] := by
  have := isProbabilityMeasure_cbMeasure
  exact (jdcbData 0 0 e).jd_recovers_jump_step isPreBrownianReal_cbW measurable_cbW cbF_isBM le_rfl
    (by norm_num) (fun _ _ => rfl) (fun _ _ => zero_mul _) (fun _ _ => zero_mul _)

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: non-vacuity of the no-jump reduction**
(`e = 0`): `TidyR11JumpDiffStep.JumpDiffData.jd_recovers_bond_step` applies (`β = ν = 0`) and gives
I5e's form `E_0[B_2X_2 − B_0X_0] = E_0[∫Xβ] + E_0[∫Bν] + E_0[∫σ_BK du]`, here with
`E_0[∫σ_BK du] = 2cd`. -/
theorem jdcb_recovers_bond_step (c d : ℝ) :
    cbMeasure[fun ω => addProc (cbJ 0) (jdBc c) 2 ω *
        addProc (fun _ _ => 0) (addProc (cbJ 0) (jdMc d)) 2 ω -
        addProc (cbJ 0) (jdBc c) 0 ω * addProc (fun _ _ => 0) (addProc (cbJ 0) (jdMc d)) 0 ω
        | cbF 0] =ᵐ[cbMeasure]
      cbMeasure[fun ω => ∫ u in (0 : ℝ)..2,
          addProc (fun _ _ => 0) (addProc (cbJ 0) (jdMc d)) u ω * (fun _ _ => (0 : ℝ)) u ω
          | cbF 0]
        + cbMeasure[fun ω => ∫ u in (0 : ℝ)..2,
          addProc (cbJ 0) (jdBc c) u ω * (fun _ _ => (0 : ℝ)) u ω | cbF 0]
        + fun _ => 2 * (c * d) := by
  have := isProbabilityMeasure_cbMeasure
  have hJ : ∀ ω, (fun u => cbJ 0 u ω) = fun _ => 0 := fun ω => funext fun u => by simp [cbJ]
  have h := (jdcbData c d 0).jd_recovers_bond_step isPreBrownianReal_cbW measurable_cbW cbF_isBM
    le_rfl (by norm_num) (β := fun _ _ => 0) (ν := fun _ _ => 0)
    (fun ω x => by rw [hJ ω]; exact hasDerivAt_const x 0) (fun _ => continuous_const)
    (fun _ x => hasDerivAt_const x 0) (fun _ => continuous_const)
    (fun ω => by rw [hJ ω]; exact continuousOn_const)
  rw [jdcb_contCov, condExp_const (cbF.le 0)] at h
  exact h

end Cochrane.Monetarism.TidyR11JumpDiffCoinBMStep
