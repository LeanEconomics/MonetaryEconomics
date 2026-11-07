/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR7MonetarismJump
import Monetarism.TidyR7MonetarismCoin
import Monetarism.TidyR7ProductStepJumpCoin

/-!
# An open-market operation at a news date: (1.32) and (1.33) as printed fail

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34), in the model
`TidyR7MonetarismJump.JumpMonetaryModel`.

## The economy (`jcoinModel`)

The coin `ξ = ±1` of `TidyR7ProductStepCoin` is revealed at time `1`. As in
`TidyR7MonetarismCoin`: `P = 1`, `Λ = Λ/P = 1 + (ξ/2)·1{u ≥ 1}` (`coinLam`), `A = 1`,
`N = (ξ/2)·1{u ≥ 1}`, `i = i^m = 0`; here the surplus is `s = 0` and at the news date the
government swaps bonds for money: money `M_u = 2 + ξ·1{u ≥ 1}` (`jM`), bonds
`B_u = 2 − ξ·1{u ≥ 1}` (`jBd`), so `B + M = 4` and (1.31) holds; `ΔM_1 = ξ`, `ΔB_1 = −ξ`,
`Δ(Λ/P)_1 = ξ/2` (`jcoin_jumps`).

## What fails, exactly (on `[0, 2]`, at `s = 0`)

* `jcoin_lhs`: `E_0[n_2B_2 − n_0B_0] = 3/2 − 2 = −1/2`.
* `jcoin_1_32_ls`: line 3 of (1.32), `−E_0[∫Λs dr + ∫ n dM]`, with `∫ n dM` the
  Lebesgue–Stieltjes integral of the CURRENT `n` (`n(1)ξ = ξ + 1/2`), is `−1/2`: it HOLDS
  (`TidyR7MonetarismJump.JumpMonetaryModel.incr_1_32_jump`).
* `jcoin_1_32_left_fails`: with the pre-jump reading `∫ n_− dM = n(1−)ξ = ξ` it is `0 ≠ −1/2`;
  the missing term is `−E_0[ΔnΔM] = −1/2`
  (`TidyR7MonetarismJump.JumpMonetaryModel.incr_1_32_jump_left`).
* `jcoin_middle_fails`: the middle line `Λ/P·dB + E_t[d(Λ/P)]B`, read as the limit of
  left-point sums (`E_0∫n_− dB + B·E_0 dn = 0 + 0`), is `0 ≠ −1/2`;
  `E_0[Σ Δn ΔM] = 1/2 ≠ 0` (`TidyR7MonetarismJump.JumpMonetaryModel.middle_1_32_book_iff`).
* `jcoin_1_33_finite`: the finite-horizon (1.33), `n_0B_0 = E_0[n_2B_2] + E_0[F_2]`, holds with
  the current-`n` flow (`2 = 3/2 + 1/2`) and fails with the pre-jump flow (`2 ≠ 3/2 + 0`); the
  corrected pre-jump form adds `E_0[ΣΔnΔM] = 1/2`.
* `jcoin_1_34`: (1.34) needs no correction: `B + M` does not jump, `0 = 0`.
-/

namespace Cochrane.Monetarism.TidyR7MonetarismJumpCoin

open MeasureTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesIntegral Cochrane.Monetarism.TidyR7StieltjesSums
  Cochrane.Monetarism.TidyR7ProductStep Cochrane.Monetarism.TidyR7ProductStepCoin
  Cochrane.Monetarism.TidyR7MonetarismModel Cochrane.Monetarism.TidyR7MonetarismValuation
  Cochrane.Monetarism.TidyR7MonetarismCoin Cochrane.Monetarism.TidyR7JumpSums
  Cochrane.Monetarism.TidyR7ProductStepJump Cochrane.Monetarism.TidyR7ProductStepJumpCoin
  Cochrane.Monetarism.TidyR7MonetarismJump

/-- Cochrane (2023), A1 §1.6, p. 567: money with an open-market purchase at the news date,
`M_u = 2 + ξ·1{u ≥ 1}`. -/
noncomputable def jM (u : ℝ) (ω : Bool) : ℝ := 2 + coinXi ω * stepAt 1 u

/-- Cochrane (2023), A1 §1.6, p. 567: bonds swapped for that money, `B_u = 2 − ξ·1{u ≥ 1}`. -/
noncomputable def jBd (u : ℝ) (ω : Bool) : ℝ := 2 + -coinXi ω * stepAt 1 u

/-- Cochrane (2023), A1 §1.6, p. 567: `Λ/P = 1 + (ξ/2)·1{u ≥ 1}` path by path.
Restates `TidyR7MonetarismCoin.disc_coin`. -/
theorem jdisc_path (ω : Bool) :
    (fun u => disc coinLam coinP u ω) = fun u => 1 + coinXi ω / 2 * stepAt 1 u :=
  funext fun u => by rw [disc_coin]; rfl

/-- **Cochrane (2023), A1 §1.6, (1.31)–(1.34), pp. 567–568: the open-market-operation economy
satisfies `TidyR7MonetarismJump.JumpMonetaryModel`**, with money and bonds jumping at the news
date. -/
theorem jcoinModel : JumpMonetaryModel coinMeasure coinFiltration coinLam coinP jBd jM coinA1
    coinN zeroRate zeroRate zeroRate where
  P_pos := coinModel.P_pos
  Λ_pos := coinModel.Λ_pos
  Λ_adapted := coinModel.Λ_adapted
  P_adapted := coinModel.P_adapted
  dec := coinModel.dec
  A_incr := coinModel.A_incr
  A_int := coinModel.A_int
  N_mart := coinModel.N_mart
  N_cadlag := coinModel.N_cadlag
  B_adapted := coin_adapted fun u hu ω => by simp [jBd, stepAt, not_le.2 hu]
  M_adapted := coin_adapted fun u hu ω => by simp [jM, stepAt, not_le.2 hu]
  M_cadlag ω := isCadlag_affine 2 (coinXi ω) 1
  M_bv ω a b := bv_affine 2 (coinXi ω) 1 a b
  flow ω u v _ := by
    have h0 : ∀ r, flowRate jBd jM coinP zeroRate zeroRate zeroRate r ω = 0 := fun r => by
      simp [flowRate, zeroRate]
    simp only [h0, intervalIntegral.integral_zero, addProc, jBd, jM]
    ring
  flow_int ω u v := by
    have e : (fun r => flowRate jBd jM coinP zeroRate zeroRate zeroRate r ω) = fun _ => (0 : ℝ) :=
      funext fun r => by simp [flowRate, zeroRate]
    rw [e]
    exact intervalIntegrable_const

/-- Cochrane (2023), A1 §1.6, p. 567: the domination conditions hold on `[0, 2]` (finite `Ω`).
The analogue of `TidyR7MonetarismCoin.coinDom`. -/
theorem jcoinDom : Dominated coinMeasure coinA1 coinN 0 2 jBd (disc coinLam coinP) :=
  ⟨Integrable.of_finite, Integrable.of_finite, fun _ _ _ _ _ => Integrable.of_finite⟩

/-- Cochrane (2023), A1 §1.6, p. 567: **the jumps at the news date**: `ΔM_1 = ξ`, `ΔB_1 = −ξ`,
`Δ(Λ/P)_1 = ξ/2`, `Δ(B + M)_1 = 0`. -/
theorem jcoin_jumps (ω : Bool) :
    jump (fun u => jM u ω) 1 = coinXi ω ∧ jump (fun u => jBd u ω) 1 = -coinXi ω ∧
      jump (fun u => disc coinLam coinP u ω) 1 = coinXi ω / 2 ∧
      jump (fun u => addProc jBd jM u ω) 1 = 0 := by
  have hW : (fun u => addProc jBd jM u ω) = fun u => 4 + 0 * stepAt 1 u :=
    funext fun u => by simp only [addProc, jBd, jM]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [jump, jM]
    rw [leftLim_affine]
    simp [stepAt]
  · simp only [jump, jBd]
    rw [leftLim_affine]
    simp [stepAt]
  · rw [jump, jdisc_path, leftLim_affine]
    simp [disc_coin, coinLam, heaviside]
  · rw [jump, hW, leftLim_affine]
    simp only [addProc, jBd, jM, lt_irrefl, ↓reduceIte]
    ring

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: **the left side, `E_0[n_2B_2 − n_0B_0] = −1/2`**
(`n_2B_2 = (1 + ξ/2)(2 − ξ) = 3/2`, `n_0B_0 = 2`). -/
theorem jcoin_lhs :
    coinMeasure[fun ω => disc coinLam coinP 2 ω * jBd 2 ω - disc coinLam coinP 0 ω * jBd 0 ω
      | coinFiltration 0] = fun _ => -1 / 2 := by
  rw [condExp_coin_lt (by norm_num)]
  funext _
  norm_num [disc_coin, coinLam, jBd, stepAt, heaviside, coinXi]

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: path by path `∫_0^2 n dM = n(1)ξ = ξ + 1/2`,
`∫_{(0,2]} n_− dM = n(1−)ξ = ξ`, and `Σ Δn ΔM = 1/2`. -/
theorem jcoin_integrals (ω : Bool) :
    rsInt 0 2 (fun u => disc coinLam coinP u ω) (fun u => jM u ω) = coinXi ω + 1 / 2 ∧
      intLeft 0 2 (disc coinLam coinP) jM ω = coinXi ω ∧
      jumpCov 0 2 (disc coinLam coinP) jM ω = 1 / 2 := by
  have h1 : rsInt 0 2 (fun u => disc coinLam coinP u ω) (fun u => jM u ω) = coinXi ω + 1 / 2 := by
    simp only [jM]
    rw [rsInt_affine _ 2 (coinXi ω) (by norm_num) (by norm_num), disc_coin]
    simp only [coinLam, heaviside, le_refl, ↓reduceIte, mul_one]
    linear_combination (1 / 2 : ℝ) * coinXi_mul_self ω
  have h2 : intLeft 0 2 (disc coinLam coinP) jM ω = coinXi ω := by
    simp only [intLeft, jM]
    rw [rsInt_affine _ 2 (coinXi ω) (by norm_num) (by norm_num), jdisc_path, leftLim_affine]
    simp
  refine ⟨h1, h2, ?_⟩
  have h := jcoinModel.rsInt_n_M ω (by norm_num : (0 : ℝ) ≤ 2)
  rw [h1, h2] at h
  linarith

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: the surplus and interest terms vanish
(`s = i = i^m = 0`). -/
theorem jcoin_flow_zero (ω : Bool) :
    (∫ r in (0 : ℝ)..2, (coinLam r ω * zeroRate r ω -
      zeroRate r ω * disc coinLam coinP r ω * jM r ω)) = 0 := by
  simp [zeroRate]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: line 3 of (1.32) HOLDS with the current-`n`
Lebesgue–Stieltjes integral**: `−E_0[∫Λs dr + ∫ n dM] = −E[ξ + 1/2] = −1/2 = E_0[n_2B_2 − n_0B_0]`,
as `TidyR7MonetarismJump.JumpMonetaryModel.incr_1_32_jump` says. -/
theorem jcoin_1_32_ls :
    coinMeasure[fun ω => -((∫ r in (0 : ℝ)..2, (coinLam r ω * zeroRate r ω -
        zeroRate r ω * disc coinLam coinP r ω * jM r ω)) +
        rsInt 0 2 (fun u => disc coinLam coinP u ω) (fun u => jM u ω)) | coinFiltration 0] =
      fun _ => -1 / 2 := by
  have e : (fun ω => -((∫ r in (0 : ℝ)..2, (coinLam r ω * zeroRate r ω -
        zeroRate r ω * disc coinLam coinP r ω * jM r ω)) +
        rsInt 0 2 (fun u => disc coinLam coinP u ω) (fun u => jM u ω))) =
      fun ω => -(coinXi ω + 1 / 2) :=
    funext fun ω => by rw [jcoin_flow_zero, (jcoin_integrals ω).1, zero_add]
  rw [e, condExp_coin_lt (by norm_num)]
  funext _
  norm_num [coinXi]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: line 3 of (1.32) FAILS with the pre-jump
reading of `dM/P`.** `−E_0[∫Λs dr + ∫ n_− dM] = −E[ξ] = 0 ≠ −1/2 = E_0[n_2B_2 − n_0B_0]`; the
missing term is `−E_0[Σ Δn ΔM] = −1/2`, and the corrected identity
`−1/2 = 0 − 1/2` holds (`TidyR7MonetarismJump.JumpMonetaryModel.incr_1_32_jump_left`). -/
theorem jcoin_1_32_left_fails :
    coinMeasure[fun ω => -((∫ r in (0 : ℝ)..2, (coinLam r ω * zeroRate r ω -
        zeroRate r ω * disc coinLam coinP r ω * jM r ω)) +
        intLeft 0 2 (disc coinLam coinP) jM ω) | coinFiltration 0] = 0 ∧
      coinMeasure[jumpCov 0 2 (disc coinLam coinP) jM | coinFiltration 0] = (fun _ => 1 / 2) ∧
      coinMeasure[fun ω => disc coinLam coinP 2 ω * jBd 2 ω - disc coinLam coinP 0 ω * jBd 0 ω
          | coinFiltration 0] ≠
        coinMeasure[fun ω => -((∫ r in (0 : ℝ)..2, (coinLam r ω * zeroRate r ω -
          zeroRate r ω * disc coinLam coinP r ω * jM r ω)) +
          intLeft 0 2 (disc coinLam coinP) jM ω) | coinFiltration 0] ∧
      coinMeasure[fun ω => disc coinLam coinP 2 ω * jBd 2 ω - disc coinLam coinP 0 ω * jBd 0 ω
          | coinFiltration 0] =ᵐ[coinMeasure]
        coinMeasure[fun ω => -((∫ r in (0 : ℝ)..2, (coinLam r ω * zeroRate r ω -
          zeroRate r ω * disc coinLam coinP r ω * jM r ω)) +
          intLeft 0 2 (disc coinLam coinP) jM ω) | coinFiltration 0] -
        coinMeasure[jumpCov 0 2 (disc coinLam coinP) jM | coinFiltration 0] := by
  have e1 : (fun ω => -((∫ r in (0 : ℝ)..2, (coinLam r ω * zeroRate r ω -
        zeroRate r ω * disc coinLam coinP r ω * jM r ω)) +
        intLeft 0 2 (disc coinLam coinP) jM ω)) = fun ω => -coinXi ω :=
    funext fun ω => by rw [jcoin_flow_zero, (jcoin_integrals ω).2.1, zero_add]
  have e2 : jumpCov 0 2 (disc coinLam coinP) jM = fun _ => 1 / 2 :=
    funext fun ω => (jcoin_integrals ω).2.2
  have h1 : coinMeasure[fun ω => -((∫ r in (0 : ℝ)..2, (coinLam r ω * zeroRate r ω -
        zeroRate r ω * disc coinLam coinP r ω * jM r ω)) +
        intLeft 0 2 (disc coinLam coinP) jM ω) | coinFiltration 0] = 0 := by
    rw [e1, condExp_coin_lt (by norm_num)]
    funext _
    norm_num [coinXi]
  have h2 : coinMeasure[jumpCov 0 2 (disc coinLam coinP) jM | coinFiltration 0] =
      fun _ => 1 / 2 := by
    rw [e2, condExp_coin_lt (by norm_num)]
    funext _
    norm_num
  refine ⟨h1, h2, ?_, jcoinModel.incr_1_32_jump_left (by norm_num) jcoinDom⟩
  rw [jcoin_lhs, h1]
  intro h
  have := congrFun h true
  norm_num at this

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the printed middle line FAILS.** Read as limits
of left-point sums, `E_0[∫ n_− dB] + B·E_0 d(Λ/P) = E[−ξ] + 0 = 0`, while
`E_0[n_2B_2 − n_0B_0] = −1/2`; correspondingly `E_0[Σ Δn ΔM] = 1/2 ≠ 0`
(`TidyR7MonetarismJump.JumpMonetaryModel.middle_1_32_book_iff`). -/
theorem jcoin_middle_fails :
    coinMeasure[intLeft 0 2 (disc coinLam coinP) jBd | coinFiltration 0] = 0 ∧
      coinMeasure[fun ω => -∫ r in (0 : ℝ)..2, zeroRate r ω * disc coinLam coinP r ω * jBd r ω
        | coinFiltration 0] = 0 ∧
      ExpIncrLimit coinMeasure coinFiltration 0 2 jBd (disc coinLam coinP)
        (coinMeasure[fun ω => -∫ r in (0 : ℝ)..2, zeroRate r ω * disc coinLam coinP r ω * jBd r ω
          | coinFiltration 0]) ∧
      coinMeasure[fun ω => disc coinLam coinP 2 ω * jBd 2 ω - disc coinLam coinP 0 ω * jBd 0 ω
          | coinFiltration 0] ≠
        coinMeasure[intLeft 0 2 (disc coinLam coinP) jBd | coinFiltration 0] +
          coinMeasure[fun ω => -∫ r in (0 : ℝ)..2,
            zeroRate r ω * disc coinLam coinP r ω * jBd r ω | coinFiltration 0] := by
  have e1 : intLeft 0 2 (disc coinLam coinP) jBd = fun ω => -coinXi ω := funext fun ω => by
    simp only [intLeft, jBd]
    rw [rsInt_affine _ 2 (-coinXi ω) (by norm_num) (by norm_num), jdisc_path, leftLim_affine]
    simp
  have h1 : coinMeasure[intLeft 0 2 (disc coinLam coinP) jBd | coinFiltration 0] = 0 := by
    rw [e1, condExp_coin_lt (by norm_num)]
    funext _
    norm_num [coinXi]
  have e2 : (fun ω => -∫ r in (0 : ℝ)..2, zeroRate r ω * disc coinLam coinP r ω * jBd r ω) =
      fun _ => 0 := funext fun ω => by simp [zeroRate]
  have h2 : coinMeasure[fun ω => -∫ r in (0 : ℝ)..2,
      zeroRate r ω * disc coinLam coinP r ω * jBd r ω | coinFiltration 0] = 0 := by
    rw [e2, condExp_coin_lt (by norm_num)]
    funext _
    norm_num
  refine ⟨h1, h2, jcoinModel.expIncr_disc_jump (by norm_num) jcoinDom, ?_⟩
  rw [jcoin_lhs, h1, h2]
  intro h
  have := congrFun h true
  norm_num at this

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567, finite horizon: which reading of `dM/P`
works.** `n_0B_0 = 2`, `E_0[n_2B_2] = 3/2`; the current-`n` flow `F_2 = ∫Λs + ∫ n dM` has
`E_0[F_2] = 1/2` (so `2 = 3/2 + 1/2`, `TidyR7MonetarismJump.JumpMonetaryModel.rec_1_33_jump`);
the pre-jump flow `F⁻_2 = ∫Λs + ∫ n_− dM` has `E_0[F⁻_2] = 0` (so `2 ≠ 3/2 + 0`), and the jump
term `E_0[Σ Δn ΔM] = 1/2` restores it (`TidyR7MonetarismJump.JumpMonetaryModel.rec_1_33_jump_left`).
-/
theorem jcoin_1_33_finite :
    (∀ ω, disc coinLam coinP 0 ω * jBd 0 ω = 2) ∧
      coinMeasure[fun ω => disc coinLam coinP 2 ω * jBd 2 ω | coinFiltration 0] =
        (fun _ => 3 / 2) ∧
      coinMeasure[flow133 coinLam coinP jM zeroRate 0 2 | coinFiltration 0] = (fun _ => 1 / 2) ∧
      coinMeasure[flow133Left coinLam coinP jM zeroRate 0 2 | coinFiltration 0] = 0 ∧
      (fun ω => disc coinLam coinP 0 ω * jBd 0 ω) ≠
        coinMeasure[fun ω => disc coinLam coinP 2 ω * jBd 2 ω | coinFiltration 0] +
          coinMeasure[flow133Left coinLam coinP jM zeroRate 0 2 | coinFiltration 0] := by
  have h0 : ∀ ω, disc coinLam coinP 0 ω * jBd 0 ω = 2 := fun ω => by
    norm_num [disc_coin, coinLam, jBd, stepAt, heaviside]
  have h2 : coinMeasure[fun ω => disc coinLam coinP 2 ω * jBd 2 ω | coinFiltration 0] =
      fun _ => 3 / 2 := by
    rw [condExp_coin_lt (by norm_num)]
    funext _
    norm_num [disc_coin, coinLam, jBd, stepAt, heaviside, coinXi]
  have eF : flow133 coinLam coinP jM zeroRate 0 2 = fun ω => coinXi ω + 1 / 2 :=
    funext fun ω => by simp only [flow133, (jcoin_integrals ω).1]; simp [zeroRate]
  have eL : flow133Left coinLam coinP jM zeroRate 0 2 = fun ω => coinXi ω :=
    funext fun ω => by simp only [flow133Left, (jcoin_integrals ω).2.1]; simp [zeroRate]
  have hF : coinMeasure[flow133 coinLam coinP jM zeroRate 0 2 | coinFiltration 0] =
      fun _ => 1 / 2 := by
    rw [eF, condExp_coin_lt (by norm_num)]
    funext _
    norm_num [coinXi]
  have hL : coinMeasure[flow133Left coinLam coinP jM zeroRate 0 2 | coinFiltration 0] = 0 := by
    rw [eL, condExp_coin_lt (by norm_num)]
    funext _
    norm_num [coinXi]
  refine ⟨h0, h2, hF, hL, ?_⟩
  rw [h2, hL]
  intro h
  have := congrFun h true
  rw [h0] at this
  norm_num at this

/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567: no correction for money plus bonds.** `B + M = 4`
does not jump although money does, and
`E_0[n_2(B + M)_2 − n_0(B + M)_0] = E[4(1 + ξ/2) − 4] = 0 = −E_0∫(Λs + (i − i^m)nM) dr`. -/
theorem jcoin_1_34 :
    coinMeasure[fun ω => disc coinLam coinP 2 ω * addProc jBd jM 2 ω -
        disc coinLam coinP 0 ω * addProc jBd jM 0 ω | coinFiltration 0] = 0 ∧
      coinMeasure[fun ω => -∫ r in (0 : ℝ)..2, (coinLam r ω * zeroRate r ω +
        (zeroRate r ω - zeroRate r ω) * disc coinLam coinP r ω * jM r ω) | coinFiltration 0] =
        0 := by
  constructor
  · rw [condExp_coin_lt (by norm_num)]
    funext _
    norm_num [disc_coin, coinLam, jBd, jM, addProc, stepAt, heaviside, coinXi]
  · have e : (fun ω => -∫ r in (0 : ℝ)..2, (coinLam r ω * zeroRate r ω +
        (zeroRate r ω - zeroRate r ω) * disc coinLam coinP r ω * jM r ω)) = fun _ => 0 :=
      funext fun ω => by simp [zeroRate]
    rw [e, condExp_coin_lt (by norm_num)]
    funext _
    norm_num

end Cochrane.Monetarism.TidyR7MonetarismJumpCoin
