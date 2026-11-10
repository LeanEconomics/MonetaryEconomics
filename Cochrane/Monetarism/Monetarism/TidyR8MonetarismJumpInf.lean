/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR8MonetarismMoneyInf
import Monetarism.TidyR7MonetarismJumpCoin

/-!
# The pre-jump reading of (1.33) fails on `[0, ∞)`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34), in the model
`TidyR7MonetarismJump.JumpMonetaryModel`. `TidyR7MonetarismJumpCoin.jcoin_1_33_finite` shows the
failure of the pre-jump (left-point) reading of `dM/P` in (1.33) on `[0, 2]`; here it is shown
in an infinite-horizon economy where the transversality condition holds.

## The economy (`jumpInfModel`)

The coin `ξ = ±1` is revealed at time `1`. `P = 1`, `Λ = Λ/P = e^{−u}(1 + (ξ/2)H(u))`
(`TidyR8MonetarismMoneyInf.decLam`), nominal rate `i = 1`, `i^m = 0`. At the news date the
government swaps bonds for money: `M_u = 2 + ξH(u)` (`TidyR7MonetarismJumpCoin.jM`),
`B_u = 2 − ξH(u)` (`TidyR7MonetarismJumpCoin.jBd`), so bonds and `Λ/P` jump together
(`ΔB_1 = −ξ`, `Δ(Λ/P)_1 = (ξ/2)e^{−1}`), and the surplus is `s = B` (so (1.31),
`d(B + M) = (iB − Ps) dt = 0`, holds).

## Results (at `s = 0`, along `T_k = k + 1`)

* `jumpInf_tvc_eq`: `E_0[n_TB_T] = (3/2)e^{−T} → 0`: the transversality condition holds.
* `jumpInf_flow133`: the current-`n` flow `F_T = ∫_0^T Λs + ∫_0^T n dM = 2 − (3/2)e^{−T} + ξe^{−1}`
  (`∫ n dM = n(1)ξ = e^{−1}(ξ + 1/2)`) tends to `G = 2 + ξe^{−1}`, `E_0[G] = 2 = n_0B_0`;
* `jumpInf_flow133Left`: the pre-jump flow `F⁻_T = ∫Λs + ∫ n_− dM` (`∫ n_− dM = n(1−)ξ = e^{−1}ξ`)
  tends to `G⁻ = G − e^{−1}/2`, `E_0[G⁻] = 2 − e^{−1}/2 ≠ 2`;
* `jumpInf_jumpCov`: the jump covariation `Σ Δn ΔM = e^{−1}/2`.
* `jumpInf_headline`: the post-jump (Lebesgue–Stieltjes, current-`n`) (1.33) holds in the
  dominated form (`TidyR7MonetarismJump.JumpMonetaryModel.valuation_1_33_jump_dom`); the printed
  pre-jump (1.33) `n_0B_0 = E_0[G⁻]` fails, and so does its limit form, exactly as
  `TidyR7MonetarismJump.JumpMonetaryModel.valuation_1_33_jump_left_iff` predicts with
  `c = lim E_0[Σ Δn ΔM] = e^{−1}/2 ≠ 0`.
* `jumpInf_1_34`: (1.34) holds verbatim in this economy with nonzero jumping money
  (`TidyR7MonetarismJump.JumpMonetaryModel.valuation_1_34_jump_dom`), both sides `4`.
-/

namespace Cochrane.Monetarism.TidyR8MonetarismJumpInf

open MeasureTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesIntegral Cochrane.Monetarism.TidyR7StieltjesSums
  Cochrane.Monetarism.TidyR7ProductStep Cochrane.Monetarism.TidyR7ProductStepCoin
  Cochrane.Monetarism.TidyR7MonetarismAC Cochrane.Monetarism.TidyR7MonetarismModel
  Cochrane.Monetarism.TidyR7MonetarismValuation Cochrane.Monetarism.TidyR7MonetarismCoin
  Cochrane.Monetarism.TidyR7MonetarismCoinInf Cochrane.Monetarism.TidyR7JumpSums
  Cochrane.Monetarism.TidyR7ProductStepJump Cochrane.Monetarism.TidyR7ProductStepJumpCoin
  Cochrane.Monetarism.TidyR7MonetarismJump Cochrane.Monetarism.TidyR7MonetarismJumpCoin
  Cochrane.Monetarism.TidyR8MonetarismMoneyInf

/-- Cochrane (2023), A1 §1.6, p. 567: `H(u)² = H(u)`. -/
theorem heaviside_mul_self (u : ℝ) : heaviside u * heaviside u = heaviside u := by
  simp only [heaviside]
  split_ifs <;> norm_num

/-- Cochrane (2023), A1 §1.6, (1.31), p. 567: the flow density `iB + i^mM − Ps = B − B = 0`. -/
theorem flowRate_jumpInf (ω : Bool) :
    (fun r => flowRate jBd jM coinP decOne zeroRate jBd r ω) = fun _ => 0 :=
  funext fun r => by simp only [flowRate, decOne, zeroRate, coinP]; ring

/-- **Cochrane (2023), A1 §1.6, (1.31)–(1.34), pp. 567–568: an infinite-horizon economy where
bonds and `Λ/P` jump together** satisfying `TidyR7MonetarismJump.JumpMonetaryModel`: `P = 1`,
`Λ = e^{−u}(1 + (ξ/2)H)`, `i = 1`, `i^m = 0`, `M = 2 + ξH`, `B = 2 − ξH`, `s = B`. -/
theorem jumpInfModel : JumpMonetaryModel coinMeasure coinFiltration decLam coinP jBd jM decA decN
    decOne zeroRate jBd where
  P_pos := moneyInfModel.P_pos
  Λ_pos := moneyInfModel.Λ_pos
  Λ_adapted := moneyInfModel.Λ_adapted
  P_adapted := moneyInfModel.P_adapted
  dec := moneyInfModel.dec
  A_incr := moneyInfModel.A_incr
  A_int := moneyInfModel.A_int
  N_mart := moneyInfModel.N_mart
  N_cadlag := moneyInfModel.N_cadlag
  B_adapted := jcoinModel.B_adapted
  M_adapted := jcoinModel.M_adapted
  M_cadlag := jcoinModel.M_cadlag
  M_bv := jcoinModel.M_bv
  flow ω u v _ := by
    rw [flowRate_jumpInf ω, intervalIntegral.integral_zero]
    simp only [addProc, jBd, jM]
    ring
  flow_int ω u v := by
    rw [flowRate_jumpInf ω]
    exact intervalIntegrable_const

/-- Cochrane (2023), A1 §1.6, p. 567: the domination conditions hold on every interval (finite
`Ω`). -/
theorem jumpInfDom (s t : ℝ) : Dominated coinMeasure decA decN s t jBd (disc decLam coinP) :=
  ⟨Integrable.of_finite, Integrable.of_finite, fun _ _ _ _ _ => Integrable.of_finite⟩

/-- Cochrane (2023), A1 §1.6, p. 567: the domination conditions for `B + M` hold on every
interval. -/
theorem jumpInfDomW (s t : ℝ) :
    Dominated coinMeasure decA decN s t (addProc jBd jM) (disc decLam coinP) :=
  ⟨Integrable.of_finite, Integrable.of_finite, fun _ _ _ _ _ => Integrable.of_finite⟩

/-! ## The flows -/

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: `Λ_rs_r = Λ_rB_r = 2e^{−r} − (1/2)H(r)e^{−r}`
(`(1 + ξH/2)(2 − ξH) = 2 − H/2` as `ξ² = 1`, `H² = H`). -/
theorem jumpInf_Ls (r : ℝ) (ω : Bool) :
    decLam r ω * jBd r ω = 2 * Real.exp (-r) - 1 / 2 * (heaviside r * Real.exp (-r)) := by
  have hξ := coinXi_mul_self ω
  have hH := heaviside_mul_self r
  simp only [decLam, jBd, stepAt_one]
  linear_combination (-(Real.exp (-r)) / 2 * heaviside r * heaviside r) * hξ +
    (-(Real.exp (-r)) / 2) * hH

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: `∫_0^T Λs dr = 2(1 − e^{−T}) − (e^{−1} − e^{−T})/2`
for `T ≥ 1`. -/
theorem jumpInf_integral {T : ℝ} (hT : 1 ≤ T) (ω : Bool) :
    ∫ r in (0 : ℝ)..T, decLam r ω * jBd r ω =
      2 * (1 - Real.exp (-T)) - 1 / 2 * (Real.exp (-1) - Real.exp (-T)) := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have e : (fun r => decLam r ω * jBd r ω) =
      fun r => 2 * Real.exp (-r) - 1 / 2 * (heaviside r * Real.exp (-r)) :=
    funext fun r => jumpInf_Ls r ω
  rw [e, intervalIntegral.integral_sub ((continuous_expNeg.intervalIntegrable 0 T).const_mul _)
    ((intervalIntegrable_mul_of_isCadlag isCadlag_heaviside hT0
      (continuous_expNeg.intervalIntegrable 0 T)).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_expNeg,
    integral_heaviside_expNeg hT]
  simp

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: the current-`n` integral
`∫_0^T n dM = n(1)ξ = e^{−1}(ξ + 1/2)` for `T ≥ 1`. -/
theorem jumpInf_rsInt {T : ℝ} (hT : 1 ≤ T) (ω : Bool) :
    rsInt 0 T (fun u => disc decLam coinP u ω) (fun u => jM u ω) =
      Real.exp (-1) * (coinXi ω + 1 / 2) := by
  have hξ := coinXi_mul_self ω
  simp only [jM]
  rw [rsInt_affine _ 2 (coinXi ω) (by norm_num) hT, disc_dec]
  simp only [decLam, heaviside, le_refl, ↓reduceIte, mul_one]
  linear_combination (Real.exp (-1) / 2) * hξ

/-- Cochrane (2023), A1 §1.6, p. 567: `n(1−) = e^{−1}`. -/
theorem jumpInf_leftLim (ω : Bool) :
    Function.leftLim (fun u => disc decLam coinP u ω) 1 = Real.exp (-1) := by
  have h : Tendsto (fun u : ℝ => Real.exp (-u)) (𝓝[<] 1) (𝓝 (Real.exp (-1))) :=
    (continuous_expNeg.tendsto 1).mono_left nhdsWithin_le_nhds
  refine leftLim_eq_of_tendsto (h.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [disc_dec]
  simp [decLam, heaviside, not_le.2 (show y < 1 from hy)]

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: the pre-jump integral
`∫_{(0,T]} n_− dM = n(1−)ξ = e^{−1}ξ` for `T ≥ 1`. -/
theorem jumpInf_intLeft {T : ℝ} (hT : 1 ≤ T) (ω : Bool) :
    intLeft 0 T (disc decLam coinP) jM ω = Real.exp (-1) * coinXi ω := by
  simp only [intLeft, jM]
  rw [rsInt_affine _ 2 (coinXi ω) (by norm_num) hT, jumpInf_leftLim]

/-- **Cochrane (2023), A1 §1.6, (1.32)–(1.33), p. 567: the jump covariation**
`Σ_{0<u≤T} Δn_uΔM_u = Δn_1ΔM_1 = (ξ/2)e^{−1}·ξ = e^{−1}/2` for `T ≥ 1`. -/
theorem jumpInf_jumpCov {T : ℝ} (hT : 1 ≤ T) (ω : Bool) :
    jumpCov 0 T (disc decLam coinP) jM ω = Real.exp (-1) / 2 := by
  have h := jumpInfModel.rsInt_n_M ω (by linarith : (0 : ℝ) ≤ T)
  rw [jumpInf_rsInt hT, jumpInf_intLeft hT] at h
  linarith

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the current-`n` flow.** For `T ≥ 1`,
`F_T = ∫_0^T Λs dr + ∫_0^T n dM = 2 − (3/2)e^{−T} + ξe^{−1}`. -/
theorem jumpInf_flow133 {T : ℝ} (hT : 1 ≤ T) (ω : Bool) :
    flow133 decLam coinP jM jBd 0 T ω = 2 - 3 / 2 * Real.exp (-T) + coinXi ω * Real.exp (-1) := by
  rw [flow133, jumpInf_integral hT, jumpInf_rsInt hT]
  ring

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the pre-jump flow.** For `T ≥ 1`,
`F⁻_T = ∫_0^T Λs dr + ∫_{(0,T]} n_− dM = 2 − (3/2)e^{−T} + ξe^{−1} − e^{−1}/2`. -/
theorem jumpInf_flow133Left {T : ℝ} (hT : 1 ≤ T) (ω : Bool) :
    flow133Left decLam coinP jM jBd 0 T ω =
      2 - 3 / 2 * Real.exp (-T) + coinXi ω * Real.exp (-1) - Real.exp (-1) / 2 := by
  rw [flow133Left, jumpInf_integral hT, jumpInf_intLeft hT]
  ring

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: the limit `G = 2 + ξe^{−1}` of the current-`n`
flows. -/
noncomputable def jumpInfG (ω : Bool) : ℝ := 2 + coinXi ω * Real.exp (-1)

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: the limit `G⁻ = G − e^{−1}/2` of the pre-jump
flows. -/
noncomputable def jumpInfGL (ω : Bool) : ℝ := 2 + coinXi ω * Real.exp (-1) - Real.exp (-1) / 2

/-- Cochrane (2023), A1 §1.6, p. 567: `T_k = k + 1 ≥ 1`.
The same as `TidyR8MonetarismUISharp.one_le_succ_cast`. -/
theorem one_le_succ (k : ℕ) : (1 : ℝ) ≤ (k : ℝ) + 1 := by
  have := Nat.cast_nonneg (α := ℝ) k
  linarith

/-- Cochrane (2023), A1 §1.6, p. 567: `e^{−(k+1)} → 0`. -/
theorem tendsto_expNeg_succ :
    Tendsto (fun k : ℕ => Real.exp (-((k : ℝ) + 1))) atTop (𝓝 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: path by path `F_{T_k} → G` and `F⁻_{T_k} → G⁻`**
along `T_k = k + 1`. -/
theorem jumpInf_tendsto (ω : Bool) :
    Tendsto (fun k : ℕ => flow133 decLam coinP jM jBd 0 ((k : ℝ) + 1) ω) atTop
        (𝓝 (jumpInfG ω)) ∧
      Tendsto (fun k : ℕ => flow133Left decLam coinP jM jBd 0 ((k : ℝ) + 1) ω) atTop
        (𝓝 (jumpInfGL ω)) := by
  have he := tendsto_expNeg_succ
  constructor
  · have h := (tendsto_const_nhds (x := (2 : ℝ))).sub (he.const_mul (3 / 2))
      |>.add_const (coinXi ω * Real.exp (-1))
    rw [mul_zero, sub_zero] at h
    refine h.congr fun k => ?_
    rw [jumpInf_flow133 (one_le_succ k)]
  · have h := ((tendsto_const_nhds (x := (2 : ℝ))).sub (he.const_mul (3 / 2))
      |>.add_const (coinXi ω * Real.exp (-1))).sub_const (Real.exp (-1) / 2)
    rw [mul_zero, sub_zero] at h
    refine h.congr fun k => ?_
    rw [jumpInf_flow133Left (one_le_succ k)]

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: `|F_T| ≤ 5` and `|F⁻_T| ≤ 5` for `T ≥ 1`. -/
theorem abs_jumpInf_le {T : ℝ} (hT : 1 ≤ T) (ω : Bool) :
    |flow133 decLam coinP jM jBd 0 T ω| ≤ 5 ∧ |flow133Left decLam coinP jM jBd 0 T ω| ≤ 5 := by
  rw [jumpInf_flow133 hT, jumpInf_flow133Left hT]
  have h1 := expNeg_le_one (by linarith : (0 : ℝ) ≤ T)
  have h2 := Real.exp_pos (-T)
  have h3 := expNeg_le_one (by norm_num : (0 : ℝ) ≤ 1)
  have h4 := Real.exp_pos (-1)
  have hx : |coinXi ω * Real.exp (-1)| ≤ 1 := by
    rw [abs_mul, abs_coinXi, one_mul, abs_of_pos h4]
    exact h3
  rw [abs_le] at hx
  constructor <;> rw [abs_le] <;> constructor <;> linarith [hx.1, hx.2]

/-! ## Both readings of (1.33) -/

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the transversality condition holds:**
`E_0[n_TB_T] = (3/2)e^{−T}` for `T ≥ 1`. -/
theorem jumpInf_tvc_eq {T : ℝ} (hT : 1 ≤ T) :
    coinMeasure[fun ω => disc decLam coinP T ω * jBd T ω | coinFiltration 0] =
      fun _ => 3 / 2 * Real.exp (-T) := by
  rw [condExp_coin_lt (by norm_num)]
  funext _
  simp only [disc_dec, jumpInf_Ls, heaviside, hT, ↓reduceIte]
  ring

/-- Cochrane (2023), A1 §1.6, p. 567: `n_0B_0 = 2` (`Λ_0 = 1`, `B_0 = 2`). -/
theorem jumpInf_Y0 (ω : Bool) : disc decLam coinP 0 ω * jBd 0 ω = 2 := by
  rw [disc_dec, jumpInf_Ls]
  simp [heaviside]

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: `E_0[G] = 2` and `E_0[G⁻] = 2 − e^{−1}/2`. -/
theorem jumpInf_EG :
    coinMeasure[jumpInfG | coinFiltration 0] = (fun _ => 2) ∧
      coinMeasure[jumpInfGL | coinFiltration 0] = (fun _ => 2 - Real.exp (-1) / 2) := by
  constructor
  · rw [condExp_coin_lt (by norm_num)]
    funext _
    simp only [jumpInfG, coinXi, Bool.false_eq_true, ↓reduceIte]
    ring
  · rw [condExp_coin_lt (by norm_num)]
    funext _
    simp only [jumpInfGL, coinXi, Bool.false_eq_true, ↓reduceIte]
    ring

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: headline — the pre-jump (1.33) fails on
`[0, ∞)`.** In `jumpInfModel` at `s = 0`, along `T_k = k + 1`:
(i) the transversality condition holds, `E_0[n_{T_k}B_{T_k}] → 0`;
(ii) the post-jump (current-`n`) (1.33) holds in the dominated form: the conclusion of
`TidyR7MonetarismJump.JumpMonetaryModel.valuation_1_33_jump_dom` with `F_{T_k} → G`,
`|F_{T_k}| ≤ 5`, and `n_0B_0 = E_0[G]` (both `2`);
(iii) the pre-jump flows converge path by path to `G⁻` with `|F⁻_{T_k}| ≤ 5`, but the printed
pre-jump (1.33) fails: `n_0B_0 = 2 ≠ 2 − e^{−1}/2 = E_0[G⁻]`;
(iv) `E_0[Σ Δn ΔM] = e^{−1}/2` for every `T_k`, and the pre-jump limit form fails, as
`TidyR7MonetarismJump.JumpMonetaryModel.valuation_1_33_jump_left_iff` predicts. -/
theorem jumpInf_headline :
    (∀ ω, Tendsto (fun k : ℕ => coinMeasure[fun ω => disc decLam coinP ((k : ℝ) + 1) ω *
        jBd ((k : ℝ) + 1) ω | coinFiltration 0] ω) atTop (𝓝 0)) ∧
      ((fun ω => disc decLam coinP 0 ω * jBd 0 ω) =ᵐ[coinMeasure]
          coinMeasure[jumpInfG | coinFiltration 0] ↔
        ∀ᵐ ω ∂coinMeasure, Tendsto (fun k : ℕ => coinMeasure[fun ω =>
          disc decLam coinP ((k : ℝ) + 1) ω * jBd ((k : ℝ) + 1) ω | coinFiltration 0] ω)
            atTop (𝓝 0)) ∧
      (fun ω => disc decLam coinP 0 ω * jBd 0 ω) =ᵐ[coinMeasure]
          coinMeasure[jumpInfG | coinFiltration 0] ∧
      (∀ ω, Tendsto (fun k : ℕ => flow133Left decLam coinP jM jBd 0 ((k : ℝ) + 1) ω) atTop
        (𝓝 (jumpInfGL ω))) ∧
      (∀ (k : ℕ) ω, |flow133Left decLam coinP jM jBd 0 ((k : ℝ) + 1) ω| ≤ 5) ∧
      coinMeasure[jumpInfGL | coinFiltration 0] = (fun _ => 2 - Real.exp (-1) / 2) ∧
      ¬ (fun ω => disc decLam coinP 0 ω * jBd 0 ω) =ᵐ[coinMeasure]
          coinMeasure[jumpInfGL | coinFiltration 0] ∧
      (∀ k : ℕ, coinMeasure[jumpCov 0 ((k : ℝ) + 1) (disc decLam coinP) jM | coinFiltration 0] =
        fun _ => Real.exp (-1) / 2) ∧
      ¬ ∀ᵐ ω ∂coinMeasure, Tendsto (fun k : ℕ =>
          coinMeasure[flow133Left decLam coinP jM jBd 0 ((k : ℝ) + 1) | coinFiltration 0] ω)
        atTop (𝓝 (disc decLam coinP 0 ω * jBd 0 ω)) := by
  have hT0 : ∀ k : ℕ, (0 : ℝ) ≤ (k : ℝ) + 1 := fun k => by linarith [one_le_succ k]
  have htvc : ∀ ω, Tendsto (fun k : ℕ => coinMeasure[fun ω => disc decLam coinP ((k : ℝ) + 1) ω
      * jBd ((k : ℝ) + 1) ω | coinFiltration 0] ω) atTop (𝓝 0) := fun ω => by
    have h := tendsto_expNeg_succ.const_mul (3 / 2)
    rw [mul_zero] at h
    refine h.congr fun k => ?_
    rw [jumpInf_tvc_eq (one_le_succ k)]
  have hdom := jumpInfModel.valuation_1_33_jump_dom (fun _ _ => rfl) (s := 0)
    (fun T _ => jumpInfDom 0 T) (fun _ _ => Integrable.of_finite)
    (T := fun k : ℕ => (k : ℝ) + 1) hT0 (G := jumpInfG) (H := fun _ => 5) (integrable_const _)
    (fun k ω => (abs_jumpInf_le (one_le_succ k) ω).1) (fun ω => (jumpInf_tendsto ω).1)
  have hval := hdom.2 (Eventually.of_forall htvc)
  have hJ : ∀ k : ℕ, coinMeasure[jumpCov 0 ((k : ℝ) + 1) (disc decLam coinP) jM |
      coinFiltration 0] = fun _ => Real.exp (-1) / 2 := fun k => by
    have e : jumpCov 0 ((k : ℝ) + 1) (disc decLam coinP) jM = fun _ => Real.exp (-1) / 2 :=
      funext fun ω => jumpInf_jumpCov (one_le_succ k) ω
    rw [e, condExp_coin_lt (by norm_num)]
    funext _
    ring
  have hleft := jumpInfModel.valuation_1_33_jump_left_iff (fun _ _ => rfl) (s := 0)
    (fun T _ => jumpInfDom 0 T) (fun _ _ => Integrable.of_finite)
    (T := fun k : ℕ => (k : ℝ) + 1) hT0 (c := fun _ => Real.exp (-1) / 2)
    (Eventually.of_forall fun ω => by simp_rw [hJ]; exact tendsto_const_nhds)
    (Eventually.of_forall htvc) (sp := jBd)
  refine ⟨htvc, hdom, hval, fun ω => (jumpInf_tendsto ω).2,
    fun k ω => (abs_jumpInf_le (one_le_succ k) ω).2, jumpInf_EG.2, ?_, hJ, ?_⟩
  · rw [jumpInf_EG.2]
    intro h
    obtain ⟨ω, hω⟩ := h.exists
    have hω' : disc decLam coinP 0 ω * jBd 0 ω = 2 - Real.exp (-1) / 2 := hω
    rw [jumpInf_Y0] at hω'
    have := Real.exp_pos (-1)
    linarith
  · intro h
    have hc := hleft.1 h
    obtain ⟨ω, hω⟩ := hc.exists
    simp only [Pi.zero_apply] at hω
    have := Real.exp_pos (-1)
    linarith

/-! ## (1.34) with jumping money -/

/-- Cochrane (2023), A1 §1.6, (1.34), p. 567: the flow of (1.34) on `jumpInfModel` is that of
`TidyR8MonetarismMoneyInf.moneyInfModel`, `∫_0^T Λ(B + M) dr = ∫_0^T 4Λ` (`s = B`, `i = 1`,
`i^m = 0`). -/
theorem jumpInf_flow134 (T : ℝ) (ω : Bool) :
    flow134 decLam coinP jM decOne zeroRate jBd 0 T ω =
      flow134 decLam coinP decTwo decOne decHalf decThree 0 T ω := by
  simp only [flow134]
  refine intervalIntegral.integral_congr fun r _ => ?_
  simp only [disc_dec, jBd, jM, decOne, zeroRate, decTwo, decHalf, decThree]
  ring

/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567: (1.34) holds verbatim with jumping money on
`[0, ∞)`.** On `jumpInfModel` along `T_k = k + 1`: the conclusion of
`TidyR7MonetarismJump.JumpMonetaryModel.valuation_1_34_jump_dom` holds, the transversality
condition `E_0[n_{T_k}(B + M)_{T_k}] = 4e^{−T_k} → 0` holds, and
`n_0(B_0 + M_0) = 4 = E_0[G]`, `G = 4 + 2ξe^{−1}`. -/
theorem jumpInf_1_34 :
    ((fun ω => disc decLam coinP 0 ω * addProc jBd jM 0 ω) =ᵐ[coinMeasure]
        coinMeasure[moneyInfG | coinFiltration 0] ↔
      ∀ᵐ ω ∂coinMeasure, Tendsto (fun k : ℕ => coinMeasure[fun ω =>
        disc decLam coinP ((k : ℝ) + 1) ω * addProc jBd jM ((k : ℝ) + 1) ω | coinFiltration 0] ω)
          atTop (𝓝 0)) ∧
      (∀ ω, Tendsto (fun k : ℕ => coinMeasure[fun ω =>
        disc decLam coinP ((k : ℝ) + 1) ω * addProc jBd jM ((k : ℝ) + 1) ω | coinFiltration 0] ω)
          atTop (𝓝 0)) ∧
      (∀ ω, disc decLam coinP 0 ω * addProc jBd jM 0 ω = 4) ∧
      (fun ω => disc decLam coinP 0 ω * addProc jBd jM 0 ω) =ᵐ[coinMeasure]
        coinMeasure[moneyInfG | coinFiltration 0] := by
  have hT0 : ∀ k : ℕ, (0 : ℝ) ≤ (k : ℝ) + 1 := fun k => by linarith [one_le_succ k]
  have eW : addProc jBd jM = addProc decTwo decTwo := funext fun u => funext fun ω => by
    simp only [addProc, jBd, jM, decTwo]
    ring
  have hseq : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hdom := jumpInfModel.valuation_1_34_jump_dom (s := 0) (fun T _ => jumpInfDomW 0 T)
    (fun _ _ => Integrable.of_finite) (T := fun k : ℕ => (k : ℝ) + 1) hT0 (G := moneyInfG)
    (H := fun _ => 6) (integrable_const _)
    (fun k ω => by rw [jumpInf_flow134]; exact abs_moneyInf_flow134_le (one_le_succ k) ω)
    (fun ω => ((moneyInf_tendsto ω).comp hseq).congr fun k => by
      simp only [Function.comp_apply]
      rw [jumpInf_flow134])
  have htvc : ∀ ω, Tendsto (fun k : ℕ => coinMeasure[fun ω =>
      disc decLam coinP ((k : ℝ) + 1) ω * addProc jBd jM ((k : ℝ) + 1) ω | coinFiltration 0] ω)
        atTop (𝓝 0) := fun ω => by
    rw [eW]
    refine (tendsto_moneyInf_tvc.comp hseq).congr fun k => ?_
    rw [moneyInf_tvc_eq (one_le_succ k)]
    rfl
  have h0 : ∀ ω, disc decLam coinP 0 ω * addProc jBd jM 0 ω = 4 := fun ω => by
    rw [eW]
    exact moneyInf_Y0 ω
  exact ⟨hdom, htvc, h0, hdom.2 (Eventually.of_forall htvc)⟩

end Cochrane.Monetarism.TidyR8MonetarismJumpInf
