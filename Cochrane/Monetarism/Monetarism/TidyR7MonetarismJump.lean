/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR7ProductStepJump
import Monetarism.TidyR7MonetarismValuation

/-!
# (1.31)–(1.34) when money and bonds jump at news dates

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34), in a model with JUMPING money.

## The model (`JumpMonetaryModel`)

As `TidyR7MonetarismModel.MonetaryModel`, except that money `M` has càdlàg paths of bounded
variation (`JumpMonetaryModel.M_cadlag`) instead of continuous ones: the government may swap
money for bonds in a lump at a news date (an open-market operation `ΔM = −ΔB`). The nominal
flow (1.31) `d(B + M) = (iB + i^mM − Ps) dt` still holds path by path, so `B + M` is continuous and
`ΔB_u = −ΔM_u` (`JumpMonetaryModel.jump_B`); `Λ/P = A + N` with `dA = −i(Λ/P) dt` (so
`Δ(Λ/P) = ΔN`, `JumpMonetaryModel.jump_disc`). Every `TidyR7MonetarismModel.MonetaryModel` is one
(`JumpMonetaryModel.ofMonetaryModel`).

## Results: what changes in (1.32)–(1.34)

* `JumpMonetaryModel.pathwise_1_32_jump`, `JumpMonetaryModel.incr_1_32_jump`: the corrected
  product step (`TidyR7ProductStepJump.JumpStepData.jump_step`) gives
  `E_s[n_tB_t − n_sB_s] = −E_s[∫_s^t (Λs − i^m nM) dr + ∫_s^t n dM]` with `∫ n dM` the
  Lebesgue–Stieltjes integral of the CURRENT `n = Λ/P` (I3's `flow133` reading).
* `JumpMonetaryModel.incr_1_32_jump_left`: with the left-point (pre-jump) reading `∫ n_− dM`,
  `E_s[n_tB_t − n_sB_s] = −E_s[∫ (Λs − i^m nM) dr + ∫ n_− dM] − E_s[Σ_{s<u≤t} Δn_uΔM_u]`:
  the extra term `−E_s[ΔM Δ(Λ/P)]` (`= +E_s[ΔB Δ(Λ/P)]`, `JumpMonetaryModel.jumpCov_B`).
* `JumpMonetaryModel.middle_1_32_jump`, `JumpMonetaryModel.middle_1_32_book_iff`: the middle
  line `Λ/P·dB + E_t[d(Λ/P)]B = −Λ(s dt + dM/P)`: the corrected version has the third term
  `E_s[Σ Δn ΔB]`; the printed two-term version, read as limits of left-point sums, holds at `ω`
  iff `E_s[Σ_{s<u≤t} Δn_uΔM_u](ω) = 0`.
* `JumpMonetaryModel.rec_1_33_jump`, `JumpMonetaryModel.rec_1_33_jump_left`,
  `JumpMonetaryModel.valuation_1_33_jump_seq`, `JumpMonetaryModel.valuation_1_33_jump`,
  `JumpMonetaryModel.valuation_1_33_jump_dom`: (1.33) holds unchanged with `∫ n dM` the
  Lebesgue–Stieltjes integral of the current `n` (limit, `L¹` and dominated forms, iff the
  transversality condition); with the pre-jump reading the flow needs `+ Σ Δn ΔM`:
  `JumpMonetaryModel.tendsto_flow133Left`, `JumpMonetaryModel.valuation_1_33_jump_left_iff` (under
  transversality the pre-jump valuation is off by exactly `lim E_s[Σ Δn ΔM]`, and holds iff that
  limit is `0`).
* `JumpMonetaryModel.incr_1_34_jump`, `JumpMonetaryModel.rec_1_34_jump`,
  `JumpMonetaryModel.valuation_1_34_jump_seq`, `JumpMonetaryModel.valuation_1_34_jump`,
  `JumpMonetaryModel.valuation_1_34_jump_dom`: (1.34) holds VERBATIM: `B + M` is continuous, so
  `Δ(B + M) = 0` and no jump term appears.
-/

namespace Cochrane.Monetarism.TidyR7MonetarismJump

open MeasureTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesIntegral Cochrane.Monetarism.TidyR7StieltjesSums
  Cochrane.Monetarism.TidyR7CondDominated Cochrane.Monetarism.TidyR7ProductStep
  Cochrane.Monetarism.TidyR7MonetarismAC Cochrane.Monetarism.TidyR7MonetarismModel
  Cochrane.Monetarism.TidyR7MonetarismValuation Cochrane.Monetarism.TidyR7JumpSums
  Cochrane.Monetarism.TidyR7ProductStepJump

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

variable (μ : Measure Ω) (𝓕 : Filtration ℝ mΩ) (Λ P B M A N i im sp : ℝ → Ω → ℝ)

/-- **Cochrane (2023), A1 §1.6, (1.31)–(1.34), pp. 567–568: the model with jumping money.**
As `TidyR7MonetarismModel.MonetaryModel`, but money has càdlàg (not necessarily continuous)
paths of bounded variation; the flow (1.31) `d(B + M) = (iB + i^mM − Ps) dt` holds path by path. -/
structure JumpMonetaryModel where
  P_pos : ∀ u ω, 0 < P u ω
  Λ_pos : ∀ u ω, 0 < Λ u ω
  Λ_adapted : ∀ u, StronglyMeasurable[𝓕 u] (Λ u)
  P_adapted : ∀ u, StronglyMeasurable[𝓕 u] (P u)
  dec : ∀ u ω, disc Λ P u ω = A u ω + N u ω
  A_incr : IncrOf A fun r ω => -(i r ω * disc Λ P r ω)
  A_int : LocInt fun r ω => -(i r ω * disc Λ P r ω)
  N_mart : Martingale N 𝓕 μ
  N_cadlag : ∀ ω, IsCadlag fun u => N u ω
  B_adapted : ∀ u, StronglyMeasurable[𝓕 u] (B u)
  M_adapted : ∀ u, StronglyMeasurable[𝓕 u] (M u)
  M_cadlag : ∀ ω, IsCadlag fun u => M u ω
  M_bv : ∀ ω a b, BoundedVariationOn (fun u => M u ω) (Set.Icc a b)
  flow : IncrOf (addProc B M) (flowRate B M P i im sp)
  flow_int : LocInt (flowRate B M P i im sp)

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: the flow of (1.33) with the PRE-jump (left-point)
reading of `dM`: `F⁻_T = ∫_s^T Λs dr + ∫_{(s,T]} n_− dM`, `n = Λ/P`. -/
noncomputable def flow133Left (s T : ℝ) (ω : Ω) : ℝ :=
  (∫ r in s..T, Λ r ω * sp r ω) + intLeft s T (disc Λ P) M ω

variable {μ 𝓕 Λ P B M A N i im sp}

namespace JumpMonetaryModel

/-- Cochrane (2023), A1 §1.6, p. 567: **every model with continuous money is a model with
jumping money** (`TidyR7MonetarismModel.MonetaryModel`). -/
theorem ofMonetaryModel (hm : MonetaryModel μ 𝓕 Λ P B M A N i im sp) :
    JumpMonetaryModel μ 𝓕 Λ P B M A N i im sp where
  P_pos := hm.P_pos
  Λ_pos := hm.Λ_pos
  Λ_adapted := hm.Λ_adapted
  P_adapted := hm.P_adapted
  dec := hm.dec
  A_incr := hm.A_incr
  A_int := hm.A_int
  N_mart := hm.N_mart
  N_cadlag := hm.N_cadlag
  B_adapted := hm.B_adapted
  M_adapted := hm.M_adapted
  M_cadlag ω := (hm.M_cont ω).isCadlag
  M_bv := hm.M_bv
  flow := hm.flow
  flow_int := hm.flow_int

variable (hm : JumpMonetaryModel μ 𝓕 Λ P B M A N i im sp)
include hm

/-- Cochrane (2023), A1 §1.6, p. 567: `Λ/P = A + N` as processes.
Restates `TidyR7MonetarismModel.MonetaryModel.disc_eq` for jumping money. -/
theorem disc_eq : disc Λ P = addProc A N :=
  funext fun u => funext fun ω => hm.dec u ω

/-- Cochrane (2023), A1 §1.6, p. 567: `(Λ/P)·P = Λ`.
Restates `TidyR7MonetarismModel.MonetaryModel.disc_mul_P` for jumping money. -/
theorem disc_mul_P (u : ℝ) (ω : Ω) : disc Λ P u ω * P u ω = Λ u ω :=
  div_mul_cancel₀ (Λ u ω) (hm.P_pos u ω).ne'

/-- Cochrane (2023), A1 §1.6, p. 567: `A` has continuous paths.
Restates `TidyR7MonetarismModel.MonetaryModel.A_cont` for jumping money. -/
theorem A_cont (ω : Ω) : Continuous fun u => A u ω :=
  continuous_of_incr (hm.A_int ω) (hm.A_incr ω)

/-- Cochrane (2023), A1 §1.6, p. 567: `A` has bounded variation on every `[a, b]`.
Restates `TidyR7MonetarismModel.MonetaryModel.A_bv` for jumping money. -/
theorem A_bv (ω : Ω) (a b : ℝ) : BoundedVariationOn (fun u => A u ω) (Set.Icc a b) :=
  bv_of_incr (hm.A_int ω) (hm.A_incr ω) a b

/-- Cochrane (2023), A1 §1.6, (1.31), p. 567: `B + M` has continuous paths, even when money
jumps.
Restates `TidyR7MonetarismModel.MonetaryModel.W_cont` for jumping money. -/
theorem W_cont (ω : Ω) : Continuous fun u => addProc B M u ω :=
  continuous_of_incr (hm.flow_int ω) (hm.flow ω)

/-- Cochrane (2023), A1 §1.6, (1.31), p. 567: `B + M` has bounded variation on every `[a, b]`.
Restates `TidyR7MonetarismModel.MonetaryModel.W_bv` for jumping money. -/
theorem W_bv (ω : Ω) (a b : ℝ) : BoundedVariationOn (fun u => addProc B M u ω) (Set.Icc a b) :=
  bv_of_incr (hm.flow_int ω) (hm.flow ω) a b

/-- Cochrane (2023), A1 §1.6, (1.31), p. 567: bonds have càdlàg paths. -/
theorem B_cadlag (ω : Ω) : IsCadlag fun u => B u ω := by
  rw [MonetaryModel.B_eq (B := B) (M := M) ω]
  exact (hm.W_cont ω).isCadlag.fun_add
    ((hm.M_cadlag ω).continuous_comp (g := fun y => -1 * y) (continuous_const.mul continuous_id))

/-- Cochrane (2023), A1 §1.6, (1.31), p. 567: bonds have bounded variation on every `[a, b]`.
Restates `TidyR7MonetarismModel.MonetaryModel.B_bv` for jumping money. -/
theorem B_bv (ω : Ω) (a b : ℝ) : BoundedVariationOn (fun u => B u ω) (Set.Icc a b) := by
  rw [MonetaryModel.B_eq (B := B) (M := M) ω]
  exact bv_add_neg (hm.W_bv ω a b) (hm.M_bv ω a b)

/-- Cochrane (2023), A1 §1.6, p. 567: `Λ/P` has càdlàg paths.
Restates `TidyR7MonetarismModel.MonetaryModel.disc_cadlag` for jumping money. -/
theorem disc_cadlag (ω : Ω) : IsCadlag fun u => disc Λ P u ω := by
  rw [hm.disc_eq]
  exact (hm.A_cont ω).isCadlag.fun_add (hm.N_cadlag ω)

/-- Cochrane (2023), A1 §1.6, p. 567: `Λ_u/P_u` is `𝓕_u`-measurable.
Restates `TidyR7MonetarismModel.MonetaryModel.disc_adapted` for jumping money. -/
theorem disc_adapted (u : ℝ) : StronglyMeasurable[𝓕 u] (disc Λ P u) :=
  ((hm.Λ_adapted u).measurable.div (hm.P_adapted u).measurable).stronglyMeasurable

/-- Cochrane (2023), A1 §1.6, p. 567: `A_u = Λ_u/P_u − N_u` is measurable.
Restates `TidyR7MonetarismModel.MonetaryModel.measurable_A` for jumping money. -/
theorem measurable_A (u : ℝ) : Measurable (A u) := by
  have e : A u = fun ω => disc Λ P u ω - N u ω := funext fun ω => by rw [hm.dec u ω]; ring
  rw [e]
  exact (((hm.disc_adapted u).mono (𝓕.le u)).measurable).sub
    (((hm.N_mart.1 u).mono (𝓕.le u)).measurable)

/-- Cochrane (2023), A1 §1.6, p. 567: `B + M` is adapted.
Restates `TidyR7MonetarismModel.MonetaryModel.W_adapted` for jumping money. -/
theorem W_adapted (u : ℝ) : StronglyMeasurable[𝓕 u] (addProc B M u) :=
  (hm.B_adapted u).add (hm.M_adapted u)

/-- **Cochrane (2023), A1 §1.6, (1.31), p. 567: bonds jump exactly opposite to money**,
`ΔB_u = −ΔM_u` (the flow (1.31) makes `B + M` continuous). -/
theorem jump_B (ω : Ω) (u : ℝ) : jump (fun v => B v ω) u = -jump (fun v => M v ω) u := by
  have hl : Function.leftLim (fun v => B v ω) u =
      addProc B M u ω - Function.leftLim (fun v => M v ω) u := by
    refine leftLim_eq_of_tendsto ?_
    have h := (((hm.W_cont ω).tendsto u).mono_left nhdsWithin_le_nhds).sub
      ((hm.M_cadlag ω).tendsto_nhdsLT_leftLim u)
    refine h.congr fun v => ?_
    simp only [addProc]
    ring
  simp only [jump, hl, addProc]
  ring

/-- **Cochrane (2023), A1 §1.6, p. 567: `Λ/P` jumps exactly with its martingale part**,
`Δ(Λ/P)_u = ΔN_u` (`A` is continuous). -/
theorem jump_disc (ω : Ω) (u : ℝ) : jump (fun v => disc Λ P v ω) u = jump (fun v => N v ω) u := by
  have hl : Function.leftLim (fun v => disc Λ P v ω) u =
      A u ω + Function.leftLim (fun v => N v ω) u := by
    refine leftLim_eq_of_tendsto ?_
    have h := (((hm.A_cont ω).tendsto u).mono_left nhdsWithin_le_nhds).add
      ((hm.N_cadlag ω).tendsto_nhdsLT_leftLim u)
    exact h.congr fun v => (hm.dec v ω).symm
  simp only [jump, hl, hm.dec u ω]
  ring

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: **the data of the corrected product step for
jumping bonds** `B` against `Λ/P = A + N` on `[s, t]`, under the domination conditions.
The analogue of `TidyR7MonetarismModel.MonetaryModel.productStepData_B`. -/
theorem jumpStepData_B {s t : ℝ} (hst : s ≤ t) (hd : Dominated μ A N s t B (disc Λ P)) :
    JumpStepData μ 𝓕 s t B A N where
  le := hst
  B_adapted u _ := hm.B_adapted u
  B_cadlag := hm.B_cadlag
  B_bv ω := hm.B_bv ω s t
  A_meas u _ := hm.measurable_A u
  A_cadlag ω := (hm.A_cont ω).isCadlag
  A_bv ω := hm.A_bv ω s t
  M_mart := hm.N_mart
  M_cadlag := hm.N_cadlag
  int_XB := by rw [← hm.disc_eq]; exact hd.sup_var
  int_BA := hd.sup_varA
  int_BM := hd.mart_incr

/-- Cochrane (2023), A1 §1.6, (1.34), p. 567: **the data of I2's product step for `B + M`**,
which is continuous even when money jumps.
Restates `TidyR7MonetarismModel.MonetaryModel.productStepData_W` for jumping money. -/
theorem productStepData_W {s t : ℝ} (hst : s ≤ t)
    (hd : Dominated μ A N s t (addProc B M) (disc Λ P)) : ProductStepData μ 𝓕 s t (addProc B M) A N
    where
  le := hst
  B_adapted u _ := hm.W_adapted u
  B_cont ω := (hm.W_cont ω).continuousOn
  B_bv ω := hm.W_bv ω s t
  A_meas u _ := hm.measurable_A u
  A_cadlag ω := (hm.A_cont ω).isCadlag
  A_bv ω := hm.A_bv ω s t
  M_mart := hm.N_mart
  M_cadlag := hm.N_cadlag
  int_XB := by rw [← hm.disc_eq]; exact hd.sup_var
  int_BA := hd.sup_varA
  int_BM := hd.mart_incr

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: `Σ Δn ΔB = −Σ Δn ΔM`** path by path
(`ΔB = −ΔM`): the extra term of the bond step is minus the jump covariation of money and `Λ/P`. -/
theorem jumpCov_B (ω : Ω) {s t : ℝ} (hst : s ≤ t) :
    jumpCov s t (disc Λ P) B ω = -jumpCov s t (disc Λ P) M ω := by
  have hn := hm.disc_cadlag ω
  have hMn : BoundedVariationOn (fun u => -1 * M u ω) (Set.Icc s t) := by
    have e : (fun u => -1 * M u ω) = fun u => -M u ω := funext fun u => by ring
    rw [BoundedVariationOn, e, eVariationOn_neg]
    exact hm.M_bv ω s t
  have hMc : IsCadlag fun u => -1 * M u ω :=
    (hm.M_cadlag ω).continuous_comp (g := fun y => -1 * y) (continuous_const.mul continuous_id)
  simp only [jumpCov]
  rw [MonetaryModel.B_eq (B := B) (M := M) ω,
    jumpSum_add_right hst hn (hm.W_bv ω s t) (hm.W_cont ω).isCadlag hMn hMc,
    jumpSum_eq_zero_of_continuousOn hst hn (hm.W_bv ω s t) (hm.W_cont ω).isCadlag
      (hm.W_cont ω).continuousOn,
    jumpSum_smul_right (-1) hst hn (hm.M_bv ω s t) (hm.M_cadlag ω)]
  ring

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: `∫_{(s,t]} B_− dA = −∫_s^t i n B` path by path
(`A` is continuous, so `B_−` may be replaced by `B`).
The analogue of `TidyR7MonetarismModel.MonetaryModel.rsInt_B_A`. -/
theorem intLeft_B_A (ω : Ω) {s t : ℝ} (hst : s ≤ t) :
    intLeft s t B A ω = -∫ r in s..t, i r ω * disc Λ P r ω * B r ω := by
  simp only [intLeft]
  rw [← rsInt_eq_rsInt_leftLim hst (hm.B_cadlag ω) (hm.A_bv ω s t) (hm.A_cont ω).continuousOn,
    rsInt_eq_integral_of_incr (hm.B_cadlag ω) (hm.A_int ω) (hm.A_incr ω) hst,
    ← intervalIntegral.integral_neg]
  exact intervalIntegral.integral_congr fun r _ => by ring

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567, path by path, jumping money.** For `s ≤ t`,
`∫ n_− dB + ∫ B_− dA + Σ Δn ΔB = −(∫_s^t (Λs − i^m nM) dr + ∫_s^t n dM)`, with `∫ n dM` the
Lebesgue–Stieltjes integral of the current `n = Λ/P`.
Generalises `TidyR7MonetarismModel.MonetaryModel.pathwise_1_32`. -/
theorem pathwise_1_32_jump (ω : Ω) {s t : ℝ} (hst : s ≤ t) :
    intLeft s t (disc Λ P) B ω + intLeft s t B A ω + jumpCov s t (disc Λ P) B ω =
      -((∫ r in s..t, (Λ r ω * sp r ω - im r ω * disc Λ P r ω * M r ω)) +
        rsInt s t (fun u => disc Λ P u ω) (fun u => M u ω)) := by
  have hn := hm.disc_cadlag ω
  have hMbv : BoundedVariationOn (fun u => -1 * M u ω) (Set.Icc s t) := by
    have e : (fun u => -1 * M u ω) = fun u => -M u ω := funext fun u => by ring
    rw [BoundedVariationOn, e, eVariationOn_neg]
    exact hm.M_bv ω s t
  have e0 : intLeft s t (disc Λ P) B ω + jumpCov s t (disc Λ P) B ω =
      rsInt s t (fun u => disc Λ P u ω) (fun u => B u ω) :=
    (rsInt_eq_leftLim_add_jumpSum hst hn (hm.B_bv ω s t) (hm.B_cadlag ω)).symm
  have e1 : rsInt s t (fun u => disc Λ P u ω) (fun u => B u ω) =
      rsInt s t (fun u => disc Λ P u ω) (fun u => addProc B M u ω) -
        rsInt s t (fun u => disc Λ P u ω) (fun u => M u ω) := by
    rw [MonetaryModel.B_eq (B := B) (M := M) ω,
      rsInt_add_right hst (hm.W_bv ω s t) hMbv (rsIntegrable_of_isCadlag hn),
      rsInt_smul_right (-1) hst (hm.M_bv ω s t)]
    ring
  have e2 : rsInt s t (fun u => disc Λ P u ω) (fun u => addProc B M u ω) =
      ∫ r in s..t, disc Λ P r ω * flowRate B M P i im sp r ω :=
    rsInt_eq_integral_of_incr hn (hm.flow_int ω) (hm.flow ω) hst
  have e3 : intLeft s t B A ω = ∫ r in s..t, B r ω * -(i r ω * disc Λ P r ω) := by
    simp only [intLeft]
    rw [← rsInt_eq_rsInt_leftLim hst (hm.B_cadlag ω) (hm.A_bv ω s t) (hm.A_cont ω).continuousOn]
    exact rsInt_eq_integral_of_incr (hm.B_cadlag ω) (hm.A_int ω) (hm.A_incr ω) hst
  have i1 : IntervalIntegrable (fun r => disc Λ P r ω * flowRate B M P i im sp r ω)
      MeasureSpace.volume s t := intervalIntegrable_mul_of_isCadlag hn hst (hm.flow_int ω s t)
  have i2 : IntervalIntegrable (fun r => B r ω * -(i r ω * disc Λ P r ω))
      MeasureSpace.volume s t :=
    intervalIntegrable_mul_of_isCadlag (hm.B_cadlag ω) hst (hm.A_int ω s t)
  have e4 : (∫ r in s..t, disc Λ P r ω * flowRate B M P i im sp r ω) +
      (∫ r in s..t, B r ω * -(i r ω * disc Λ P r ω)) =
        -∫ r in s..t, (Λ r ω * sp r ω - im r ω * disc Λ P r ω * M r ω) := by
    rw [← intervalIntegral.integral_add i1 i2, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun r _ => ?_
    simp only [flowRate]
    rw [← hm.disc_mul_P r ω]
    ring
  rw [e3]
  linarith

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: path by path,
`∫_s^t n dM = ∫_{(s,t]} n_− dM + Σ_{s<u≤t} Δn_uΔM_u`. -/
theorem rsInt_n_M (ω : Ω) {s t : ℝ} (hst : s ≤ t) :
    rsInt s t (fun u => disc Λ P u ω) (fun u => M u ω) =
      intLeft s t (disc Λ P) M ω + jumpCov s t (disc Λ P) M ω :=
  rsInt_eq_leftLim_add_jumpSum hst (hm.disc_cadlag ω) (hm.M_bv ω s t) (hm.M_cadlag ω)

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: the integrabilities of the bond step:
`∫ n_− dB`, `∫ B_− dA`, `Σ Δn ΔB`, `Σ Δn ΔM` and the flow `∫(Λs − i^m nM) + ∫ n dM`. -/
theorem integrable_1_32_jump {s t : ℝ} (hst : s ≤ t) (hd : Dominated μ A N s t B (disc Λ P)) :
    Integrable (intLeft s t (disc Λ P) B) μ ∧ Integrable (intLeft s t B A) μ ∧
      Integrable (jumpCov s t (disc Λ P) B) μ ∧ Integrable (jumpCov s t (disc Λ P) M) μ ∧
      Integrable (fun ω => -((∫ r in s..t, (Λ r ω * sp r ω - im r ω * disc Λ P r ω * M r ω)) +
        rsInt s t (fun u => disc Λ P u ω) (fun u => M u ω))) μ := by
  have hj := hm.jumpStepData_B hst hd
  have i1 := hj.integrable_intLeftXB
  have i2 := hj.integrable_intLeftBA
  have i3 := hj.integrable_jumpCov
  rw [← hm.disc_eq] at i1 i3
  have eM : jumpCov s t (disc Λ P) M = -jumpCov s t (disc Λ P) B :=
    funext fun ω => by rw [Pi.neg_apply, hm.jumpCov_B ω hst, neg_neg]
  have eF : (fun ω => -((∫ r in s..t, (Λ r ω * sp r ω - im r ω * disc Λ P r ω * M r ω)) +
      rsInt s t (fun u => disc Λ P u ω) (fun u => M u ω))) =
      intLeft s t (disc Λ P) B + intLeft s t B A + jumpCov s t (disc Λ P) B :=
    funext fun ω => (hm.pathwise_1_32_jump ω hst).symm
  refine ⟨i1, i2, i3, ?_, ?_⟩
  · rw [eM]
    exact i3.neg
  · rw [eF]
    exact (i1.add i2).add i3

variable [IsFiniteMeasure μ]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567, with jumping money and bonds.** Under the
domination conditions on `[s, t]`, almost surely
`E_s[n_tB_t − n_sB_s] = −E_s[∫_s^t (Λs − i^m nM) dr + ∫_s^t n dM]`, `n = Λ/P`, with `∫ n dM` the
Lebesgue–Stieltjes integral of the CURRENT `n` (which charges `n(u)ΔM_u` at a jump).
Generalises `TidyR7MonetarismModel.MonetaryModel.incr_1_32_general`. -/
theorem incr_1_32_jump {s t : ℝ} (hst : s ≤ t) (hd : Dominated μ A N s t B (disc Λ P)) :
    μ[fun ω => disc Λ P t ω * B t ω - disc Λ P s ω * B s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => -((∫ r in s..t, (Λ r ω * sp r ω - im r ω * disc Λ P r ω * M r ω)) +
        rsInt s t (fun u => disc Λ P u ω) (fun u => M u ω)) | 𝓕 s] := by
  have hj := hm.jumpStepData_B hst hd
  have h := hj.jump_step
  have i1 := hj.integrable_intLeftXB
  have i2 := hj.integrable_intLeftBA
  have i3 := hj.integrable_jumpCov
  rw [← hm.disc_eq] at h i1 i3
  have eL : (fun ω => B t ω * disc Λ P t ω - B s ω * disc Λ P s ω) =
      fun ω => disc Λ P t ω * B t ω - disc Λ P s ω * B s ω := funext fun ω => by ring
  have eR : (fun ω => -((∫ r in s..t, (Λ r ω * sp r ω - im r ω * disc Λ P r ω * M r ω)) +
        rsInt s t (fun u => disc Λ P u ω) (fun u => M u ω))) =
      intLeft s t (disc Λ P) B + intLeft s t B A + jumpCov s t (disc Λ P) B :=
    funext fun ω => (hm.pathwise_1_32_jump ω hst).symm
  rw [eL] at h
  rw [eR]
  filter_upwards [h, condExp_add (i1.add i2) i3 (𝓕 s), condExp_add i1 i2 (𝓕 s)] with ω h1 h2 h3
  rw [h1, h2]
  simp only [Pi.add_apply] at h3 ⊢
  rw [h3]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the extra term `E_t[ΔM Δ(Λ/P)]`.** With the
PRE-jump reading `∫ n_− dM` of `dM/P`, almost surely
`E_s[n_tB_t − n_sB_s] = −E_s[∫_s^t (Λs − i^m nM) dr + ∫_{(s,t]} n_− dM] − E_s[Σ_{s<u≤t} Δn_uΔM_u]`.
The book's line `E_t d(ΛB/P) = −Λ(s dt + dM/P)` read this way misses `−E_s[Σ ΔnΔM]`.
The pre-jump variant of `TidyR7MonetarismModel.MonetaryModel.incr_1_32_general`. -/
theorem incr_1_32_jump_left {s t : ℝ} (hst : s ≤ t) (hd : Dominated μ A N s t B (disc Λ P)) :
    μ[fun ω => disc Λ P t ω * B t ω - disc Λ P s ω * B s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => -((∫ r in s..t, (Λ r ω * sp r ω - im r ω * disc Λ P r ω * M r ω)) +
        intLeft s t (disc Λ P) M ω) | 𝓕 s] - μ[jumpCov s t (disc Λ P) M | 𝓕 s] := by
  obtain ⟨-, -, -, iJ, iF⟩ := hm.integrable_1_32_jump hst hd
  have eG : (fun ω => -((∫ r in s..t, (Λ r ω * sp r ω - im r ω * disc Λ P r ω * M r ω)) +
      intLeft s t (disc Λ P) M ω)) =
      (fun ω => -((∫ r in s..t, (Λ r ω * sp r ω - im r ω * disc Λ P r ω * M r ω)) +
        rsInt s t (fun u => disc Λ P u ω) (fun u => M u ω))) + jumpCov s t (disc Λ P) M :=
    funext fun ω => by
      simp only [Pi.add_apply]
      rw [hm.rsInt_n_M ω hst]
      ring
  rw [eG]
  filter_upwards [hm.incr_1_32_jump hst hd, condExp_add iF iJ (𝓕 s)] with ω h1 h2
  rw [h1, Pi.sub_apply, h2, Pi.add_apply]
  ring

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: `E_t d(Λ/P) = −i(Λ/P) dt` for jumping bonds,
in the expected-increment sense**: `B·E_s d(Λ/P)` (`TidyR7ProductStep.ExpIncrLimit`) exists and
equals `−E_s∫_s^t i n B`.
Generalises `TidyR7MonetarismModel.MonetaryModel.expIncr_disc`. -/
theorem expIncr_disc_jump {s t : ℝ} (hst : s ≤ t) (hd : Dominated μ A N s t B (disc Λ P)) :
    ExpIncrLimit μ 𝓕 s t B (disc Λ P)
      (μ[fun ω => -∫ r in s..t, i r ω * disc Λ P r ω * B r ω | 𝓕 s]) := by
  have h := (hm.jumpStepData_B hst hd).expIncrLimit_intLeft
  have e : intLeft s t B A = fun ω => -∫ r in s..t, i r ω * disc Λ P r ω * B r ω :=
    funext fun ω => hm.intLeft_B_A ω hst
  rw [e, ← hm.disc_eq] at h
  exact h

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567, the corrected middle line**
`Λ/P_− dB + E_t[d(Λ/P)]B_− + E_t[Δ(Λ/P)ΔB] = −Λ(s dt + dM/P)`, integrated: almost surely
`E_s[∫ n_− dB] + B·E_s d(Λ/P) + E_s[Σ Δn ΔB] = −E_s[∫(Λs − i^m nM) dr + ∫ n dM]`, with
`B·E_s d(Λ/P) = −E_s∫ i n B` (`JumpMonetaryModel.expIncr_disc_jump`).
Generalises `TidyR7MonetarismModel.MonetaryModel.middle_1_32`. -/
theorem middle_1_32_jump {s t : ℝ} (hst : s ≤ t) (hd : Dominated μ A N s t B (disc Λ P)) :
    μ[intLeft s t (disc Λ P) B | 𝓕 s] +
        μ[fun ω => -∫ r in s..t, i r ω * disc Λ P r ω * B r ω | 𝓕 s] +
        μ[jumpCov s t (disc Λ P) B | 𝓕 s] =ᵐ[μ]
      μ[fun ω => -((∫ r in s..t, (Λ r ω * sp r ω - im r ω * disc Λ P r ω * M r ω)) +
        rsInt s t (fun u => disc Λ P u ω) (fun u => M u ω)) | 𝓕 s] := by
  have h := (hm.jumpStepData_B hst hd).jump_step
  rw [← hm.disc_eq] at h
  have e : intLeft s t B A = fun ω => -∫ r in s..t, i r ω * disc Λ P r ω * B r ω :=
    funext fun ω => hm.intLeft_B_A ω hst
  have eL : (fun ω => B t ω * disc Λ P t ω - B s ω * disc Λ P s ω) =
      fun ω => disc Λ P t ω * B t ω - disc Λ P s ω * B s ω := funext fun ω => by ring
  rw [e, eL] at h
  filter_upwards [h, hm.incr_1_32_jump hst hd] with ω h1 h2
  rw [← h1, h2]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: exactly when the printed middle line holds.**
Read as limits of left-point sums, the printed two-term step
`E_s[n_tB_t − n_sB_s] = E_s[∫ n_− dB] + B·E_s d(Λ/P)` holds at almost every `ω` iff
`E_s[Σ_{s<u≤t} Δ(Λ/P)_uΔM_u](ω) = 0`: it fails exactly when money (equivalently bonds) is
expected to jump together with `Λ/P`. -/
theorem middle_1_32_book_iff {s t : ℝ} (hst : s ≤ t) (hd : Dominated μ A N s t B (disc Λ P)) :
    ∀ᵐ ω ∂μ, (μ[fun ω => disc Λ P t ω * B t ω - disc Λ P s ω * B s ω | 𝓕 s] ω =
        μ[intLeft s t (disc Λ P) B | 𝓕 s] ω +
          μ[fun ω => -∫ r in s..t, i r ω * disc Λ P r ω * B r ω | 𝓕 s] ω ↔
      μ[jumpCov s t (disc Λ P) M | 𝓕 s] ω = 0) := by
  have hj := hm.jumpStepData_B hst hd
  have hL := hm.expIncr_disc_jump hst hd
  rw [hm.disc_eq] at hL
  have h := hj.book_step_iff hL
  rw [← hm.disc_eq] at h
  have eL : (fun ω => B t ω * disc Λ P t ω - B s ω * disc Λ P s ω) =
      fun ω => disc Λ P t ω * B t ω - disc Λ P s ω * B s ω := funext fun ω => by ring
  have eB : jumpCov s t (disc Λ P) B = -jumpCov s t (disc Λ P) M :=
    funext fun ω => hm.jumpCov_B ω hst
  rw [eL, eB] at h
  filter_upwards [h, condExp_neg (μ := μ) (jumpCov s t (disc Λ P) M) (𝓕 s)] with ω h1 h2
  rw [h1, h2, Pi.neg_apply, neg_eq_zero]

/-! ## (1.33): the bond valuation equation -/

omit [IsFiniteMeasure μ] in
/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: with `i^m = 0`, path by path
`F_T = ∫_s^T Λs dr + ∫_s^T n dM = −(∫ n_− dB + ∫ B_− dA + Σ Δn ΔB)` (`flow133` of I3, with the
Lebesgue–Stieltjes integral of the current `n`).
Restates `TidyR7MonetarismValuation.MonetaryModel.flow133_eq`. -/
theorem flow133_eq_jump (him : ∀ r ω, im r ω = 0) {s T : ℝ} (hsT : s ≤ T) :
    flow133 Λ P M sp s T =
      -(intLeft s T (disc Λ P) B + intLeft s T B A + jumpCov s T (disc Λ P) B) := by
  funext ω
  have h := hm.pathwise_1_32_jump ω hsT
  simp only [him, zero_mul, sub_zero] at h
  simp only [flow133, Pi.neg_apply, Pi.add_apply]
  rw [h, neg_neg]

omit [IsFiniteMeasure μ] in
/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: the flow `F_T` is measurable.
Restates `TidyR7MonetarismValuation.MonetaryModel.measurable_flow133`. -/
theorem measurable_flow133_jump (him : ∀ r ω, im r ω = 0) {s T : ℝ} (hsT : s ≤ T)
    (hd : Dominated μ A N s T B (disc Λ P)) : Measurable (flow133 Λ P M sp s T) := by
  have hj := hm.jumpStepData_B hsT hd
  have m1 := hj.measurable_intLeftXB
  have m3 := hj.measurable_jumpCov
  rw [← hm.disc_eq] at m1 m3
  rw [hm.flow133_eq_jump him hsT]
  exact ((m1.add hj.measurable_intLeftBA).add m3).neg

/-- **Cochrane (2023), A1 §1.6, (1.32) ⇒ (1.33), p. 567: the finite-horizon budget with jumping
money.** With `i^m = 0`, the domination conditions on `[s, T]` and `n_sB_s`, `n_TB_T` integrable:
`n_sB_s = E_s[n_TB_T] + E_s[∫_s^T Λs dr + ∫_s^T n dM]` a.s. (current-`n` reading of `dM/P`).
Restates `TidyR7MonetarismValuation.MonetaryModel.rec_1_33`. -/
theorem rec_1_33_jump (him : ∀ r ω, im r ω = 0) {s T : ℝ} (hsT : s ≤ T)
    (hd : Dominated μ A N s T B (disc Λ P))
    (hYs : Integrable (fun ω => disc Λ P s ω * B s ω) μ)
    (hYT : Integrable (fun ω => disc Λ P T ω * B T ω) μ) :
    Integrable (flow133 Λ P M sp s T) μ ∧
      (fun ω => disc Λ P s ω * B s ω) =ᵐ[μ]
        μ[fun ω => disc Λ P T ω * B T ω | 𝓕 s] + μ[flow133 Λ P M sp s T | 𝓕 s] := by
  obtain ⟨i1, i2, i3, -, -⟩ := hm.integrable_1_32_jump hsT hd
  have hF : Integrable (flow133 Λ P M sp s T) μ := by
    rw [hm.flow133_eq_jump him hsT]
    exact ((i1.add i2).add i3).neg
  refine ⟨hF, ?_⟩
  have hinc := hm.incr_1_32_jump hsT hd
  have e : (fun ω => -((∫ r in s..T, (Λ r ω * sp r ω - im r ω * disc Λ P r ω * M r ω)) +
      rsInt s T (fun u => disc Λ P u ω) (fun u => M u ω))) =
      fun ω => -flow133 Λ P M sp s T ω :=
    funext fun ω => by simp only [him, zero_mul, sub_zero, flow133]
  rw [e] at hinc
  exact rec_of_incr (Y := fun t ω => disc Λ P t ω * B t ω) (F := flow133 Λ P M sp s T) hinc
    ((hm.disc_adapted s).mul (hm.B_adapted s)) hYs hYT

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the finite-horizon budget with the pre-jump
reading.** Under the hypotheses of `JumpMonetaryModel.rec_1_33_jump`, a.s.
`n_sB_s = E_s[n_TB_T] + E_s[∫_s^T Λs dr + ∫_{(s,T]} n_− dM] + E_s[Σ_{s<u≤T} Δn_uΔM_u]`. -/
theorem rec_1_33_jump_left (him : ∀ r ω, im r ω = 0) {s T : ℝ} (hsT : s ≤ T)
    (hd : Dominated μ A N s T B (disc Λ P))
    (hYs : Integrable (fun ω => disc Λ P s ω * B s ω) μ)
    (hYT : Integrable (fun ω => disc Λ P T ω * B T ω) μ) :
    (fun ω => disc Λ P s ω * B s ω) =ᵐ[μ]
      μ[fun ω => disc Λ P T ω * B T ω | 𝓕 s] + μ[flow133Left Λ P M sp s T | 𝓕 s] +
        μ[jumpCov s T (disc Λ P) M | 𝓕 s] := by
  obtain ⟨hF, hrec⟩ := hm.rec_1_33_jump him hsT hd hYs hYT
  obtain ⟨-, -, -, iJ, -⟩ := hm.integrable_1_32_jump hsT hd
  have e : flow133 Λ P M sp s T = flow133Left Λ P M sp s T + jumpCov s T (disc Λ P) M :=
    funext fun ω => by
      simp only [flow133, flow133Left, Pi.add_apply]
      rw [hm.rsInt_n_M ω hsT]
      ring
  have iL : Integrable (flow133Left Λ P M sp s T) μ := by
    have e' : flow133Left Λ P M sp s T = flow133 Λ P M sp s T - jumpCov s T (disc Λ P) M := by
      rw [e]
      ring
    rw [e']
    exact hF.sub iJ
  rw [e] at hrec
  filter_upwards [hrec, condExp_add iL iJ (𝓕 s)] with ω h1 h2
  rw [h1]
  simp only [Pi.add_apply] at h2 ⊢
  rw [h2]
  ring

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567, limit form, jumping money.** With `i^m = 0`, the
domination conditions on every `[s, T]` and `n_TB_T` integrable: along any `T_k ≥ s`, a.s.
`E_s[∫_s^{T_k} Λs dr + ∫_s^{T_k} n dM] → n_sB_s` iff a.s. `E_s[n_{T_k}B_{T_k}] → 0`.
Generalises `TidyR7MonetarismValuation.MonetaryModel.valuation_1_33_seq`. -/
theorem valuation_1_33_jump_seq (him : ∀ r ω, im r ω = 0) {s : ℝ}
    (hd : ∀ T, s ≤ T → Dominated μ A N s T B (disc Λ P))
    (hYi : ∀ T, s ≤ T → Integrable (fun ω => disc Λ P T ω * B T ω) μ) {T : ℕ → ℝ}
    (hT : ∀ k, s ≤ T k) :
    (∀ᵐ ω ∂μ, Tendsto (fun k => μ[flow133 Λ P M sp s (T k) | 𝓕 s] ω) atTop
        (𝓝 (disc Λ P s ω * B s ω))) ↔
      ∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => disc Λ P (T k) ω * B (T k) ω | 𝓕 s] ω) atTop
        (𝓝 0) :=
  valuation_iff_tvc_seq (Y := fun t ω => disc Λ P t ω * B t ω)
    (fun T' hT' => (hm.rec_1_33_jump him hT' (hd T' hT') (hYi s le_rfl) (hYi T' hT')).2) hT

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567, `L¹` form, jumping money: valuation iff
transversality.** With `F_T → G` in `L¹`: `n_sB_s = E_s[G]` a.s. iff `E_s[n_TB_T] → 0` in `L¹`.
Generalises `TidyR7MonetarismValuation.MonetaryModel.valuation_1_33`. -/
theorem valuation_1_33_jump (him : ∀ r ω, im r ω = 0) {s : ℝ}
    (hd : ∀ T, s ≤ T → Dominated μ A N s T B (disc Λ P))
    (hYi : ∀ T, s ≤ T → Integrable (fun ω => disc Λ P T ω * B T ω) μ) {G : Ω → ℝ}
    (hG : Integrable G μ)
    (hconv : Tendsto (fun T => ∫ ω, |flow133 Λ P M sp s T ω - G ω| ∂μ) atTop (𝓝 0)) :
    (fun ω => disc Λ P s ω * B s ω) =ᵐ[μ] μ[G | 𝓕 s] ↔
      Tendsto (fun T => ∫ ω, |μ[fun ω => disc Λ P T ω * B T ω | 𝓕 s] ω| ∂μ) atTop (𝓝 0) :=
  valuation_iff_tvc_flow (Y := fun t ω => disc Λ P t ω * B t ω) (F := flow133 Λ P M sp s)
    (fun T hT => (hm.rec_1_33_jump him hT (hd T hT) (hYi s le_rfl) (hYi T hT)).2) hYi
    (fun T hT => (hm.rec_1_33_jump him hT (hd T hT) (hYi s le_rfl) (hYi T hT)).1) hG hconv

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567, dominated form, jumping money.** If along
`T_k ≥ s` the flows `F_{T_k}` converge path by path to `G` with `|F_{T_k}| ≤ H` integrable:
`n_sB_s = E_s[G]` a.s. iff `E_s[n_{T_k}B_{T_k}] → 0` a.s.
Generalises `TidyR7MonetarismValuation.MonetaryModel.valuation_1_33_dom`. -/
theorem valuation_1_33_jump_dom (him : ∀ r ω, im r ω = 0) {s : ℝ}
    (hd : ∀ T, s ≤ T → Dominated μ A N s T B (disc Λ P))
    (hYi : ∀ T, s ≤ T → Integrable (fun ω => disc Λ P T ω * B T ω) μ) {T : ℕ → ℝ}
    (hT : ∀ k, s ≤ T k) {G H : Ω → ℝ} (hH : Integrable H μ)
    (hbd : ∀ k ω, |flow133 Λ P M sp s (T k) ω| ≤ H ω)
    (hlim : ∀ ω, Tendsto (fun k => flow133 Λ P M sp s (T k) ω) atTop (𝓝 (G ω))) :
    (fun ω => disc Λ P s ω * B s ω) =ᵐ[μ] μ[G | 𝓕 s] ↔
      ∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => disc Λ P (T k) ω * B (T k) ω | 𝓕 s] ω) atTop
        (𝓝 0) :=
  valuation_iff_tvc_dom (Y := fun t ω => disc Λ P t ω * B t ω) (F := flow133 Λ P M sp s)
    (fun T' hT' => (hm.rec_1_33_jump him hT' (hd T' hT') (hYi s le_rfl) (hYi T' hT')).2) hT
    (fun k => hm.measurable_flow133_jump him (hT k) (hd (T k) (hT k))) hH hbd hlim

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the pre-jump reading of (1.33) is off by the
expected jump covariation.** Under the hypotheses of `JumpMonetaryModel.valuation_1_33_jump_seq`,
if the transversality condition `E_s[n_{T_k}B_{T_k}] → 0` holds a.s. and
`E_s[Σ_{s<u≤T_k} Δn_uΔM_u] → c` a.s., then a.s.
`E_s[∫_s^{T_k} Λs dr + ∫_{(s,T_k]} n_− dM] → n_sB_s − c`. -/
theorem tendsto_flow133Left (him : ∀ r ω, im r ω = 0) {s : ℝ}
    (hd : ∀ T, s ≤ T → Dominated μ A N s T B (disc Λ P))
    (hYi : ∀ T, s ≤ T → Integrable (fun ω => disc Λ P T ω * B T ω) μ) {T : ℕ → ℝ}
    (hT : ∀ k, s ≤ T k) {c : Ω → ℝ}
    (hJ : ∀ᵐ ω ∂μ, Tendsto (fun k => μ[jumpCov s (T k) (disc Λ P) M | 𝓕 s] ω) atTop (𝓝 (c ω)))
    (htvc : ∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => disc Λ P (T k) ω * B (T k) ω | 𝓕 s] ω)
      atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => μ[flow133Left Λ P M sp s (T k) | 𝓕 s] ω) atTop
      (𝓝 (disc Λ P s ω * B s ω - c ω)) := by
  have hall := ae_all_iff.2 fun k =>
    hm.rec_1_33_jump_left him (hT k) (hd (T k) (hT k)) (hYi s le_rfl) (hYi (T k) (hT k))
  filter_upwards [hall, hJ, htvc] with ω h1 h2 h3
  have e : ∀ k, μ[flow133Left Λ P M sp s (T k) | 𝓕 s] ω = disc Λ P s ω * B s ω -
      μ[fun ω => disc Λ P (T k) ω * B (T k) ω | 𝓕 s] ω -
        μ[jumpCov s (T k) (disc Λ P) M | 𝓕 s] ω := fun k => by
    have := h1 k
    simp only [Pi.add_apply] at this
    linarith
  have hlim := (tendsto_const_nhds (x := disc Λ P s ω * B s ω)).sub h3 |>.sub h2
  rw [sub_zero] at hlim
  exact (tendsto_congr e).2 hlim

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: exactly when the pre-jump reading of (1.33)
holds.** Under transversality and `E_s[Σ_{s<u≤T_k} Δn_uΔM_u] → c` a.s.:
`E_s[∫_s^{T_k} Λs dr + ∫_{(s,T_k]} n_− dM] → n_sB_s` a.s. iff `c = 0` a.s. -/
theorem valuation_1_33_jump_left_iff (him : ∀ r ω, im r ω = 0) {s : ℝ}
    (hd : ∀ T, s ≤ T → Dominated μ A N s T B (disc Λ P))
    (hYi : ∀ T, s ≤ T → Integrable (fun ω => disc Λ P T ω * B T ω) μ) {T : ℕ → ℝ}
    (hT : ∀ k, s ≤ T k) {c : Ω → ℝ}
    (hJ : ∀ᵐ ω ∂μ, Tendsto (fun k => μ[jumpCov s (T k) (disc Λ P) M | 𝓕 s] ω) atTop (𝓝 (c ω)))
    (htvc : ∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => disc Λ P (T k) ω * B (T k) ω | 𝓕 s] ω)
      atTop (𝓝 0)) :
    (∀ᵐ ω ∂μ, Tendsto (fun k => μ[flow133Left Λ P M sp s (T k) | 𝓕 s] ω) atTop
        (𝓝 (disc Λ P s ω * B s ω))) ↔ c =ᵐ[μ] 0 := by
  have h := hm.tendsto_flow133Left him hd hYi hT hJ htvc
  constructor
  · intro h'
    filter_upwards [h, h'] with ω h1 h2
    have := tendsto_nhds_unique h1 h2
    simp only [Pi.zero_apply]
    linarith
  · intro hc
    filter_upwards [h, hc] with ω h1 h2
    simp only [Pi.zero_apply] at h2
    rwa [h2, sub_zero] at h1

/-! ## (1.34): money plus bonds, unchanged -/

omit [IsFiniteMeasure μ] in
/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567, path by path, jumping money.** For `s ≤ t`,
`∫_s^t n d(B + M) + ∫_s^t (B + M) dA = −∫_s^t (Λs + (i − i^m)nM) dr` (`B + M` is continuous).
Generalises `TidyR7MonetarismModel.MonetaryModel.pathwise_1_34`. -/
theorem pathwise_1_34_jump (ω : Ω) {s t : ℝ} (hst : s ≤ t) :
    rsInt s t (fun u => disc Λ P u ω) (fun u => addProc B M u ω) +
        rsInt s t (fun u => addProc B M u ω) (fun u => A u ω) =
      -∫ r in s..t, (Λ r ω * sp r ω + (i r ω - im r ω) * disc Λ P r ω * M r ω) := by
  have hn := hm.disc_cadlag ω
  have hW := (hm.W_cont ω).isCadlag
  rw [rsInt_eq_integral_of_incr hn (hm.flow_int ω) (hm.flow ω) hst,
    rsInt_eq_integral_of_incr hW (hm.A_int ω) (hm.A_incr ω) hst,
    ← intervalIntegral.integral_add (intervalIntegrable_mul_of_isCadlag hn hst (hm.flow_int ω s t))
      (intervalIntegrable_mul_of_isCadlag hW hst (hm.A_int ω s t)),
    ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun r _ => ?_
  simp only [flowRate, addProc]
  rw [← hm.disc_mul_P r ω]
  ring

/-- **Cochrane (2023), A1 §1.6, p. 567, the line before (1.34), with jumping money:
`E_t d(Λ(M + B)/P) = −Λ(s + (i − i^m)M/P) dt`, integrated, with NO jump term.** Under the
domination conditions for `B + M` on `[s, t]`, a.s.
`E_s[n_t(B + M)_t − n_s(B + M)_s] = −E_s∫_s^t (Λs + (i − i^m)nM) dr`.
Generalises `TidyR7MonetarismModel.MonetaryModel.incr_1_34`. -/
theorem incr_1_34_jump {s t : ℝ} (hst : s ≤ t)
    (hd : Dominated μ A N s t (addProc B M) (disc Λ P)) :
    μ[fun ω => disc Λ P t ω * addProc B M t ω - disc Λ P s ω * addProc B M s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => -∫ r in s..t, (Λ r ω * sp r ω + (i r ω - im r ω) * disc Λ P r ω * M r ω)
        | 𝓕 s] := by
  have hpd := hm.productStepData_W hst hd
  have h := hpd.product_step
  have i1 := hpd.integrable_intXB
  have i2 := hpd.integrable_intBA
  rw [← hm.disc_eq] at h i1
  have eL : (fun ω => addProc B M t ω * disc Λ P t ω - addProc B M s ω * disc Λ P s ω) =
      fun ω => disc Λ P t ω * addProc B M t ω - disc Λ P s ω * addProc B M s ω :=
    funext fun ω => by ring
  have eR : (fun ω => -∫ r in s..t,
        (Λ r ω * sp r ω + (i r ω - im r ω) * disc Λ P r ω * M r ω)) =
      intRS s t (disc Λ P) (addProc B M) + intRS s t (addProc B M) A :=
    funext fun ω => (hm.pathwise_1_34_jump ω hst).symm
  rw [eL] at h
  rw [eR]
  filter_upwards [h, condExp_add i1 i2 (𝓕 s)] with ω h1 h2
  rw [h1, h2]

omit [IsFiniteMeasure μ] in
/-- Cochrane (2023), A1 §1.6, (1.34), p. 567: the flow `F_T` of (1.34) is measurable.
Restates `TidyR7MonetarismValuation.MonetaryModel.measurable_flow134`. -/
theorem measurable_flow134_jump {s T : ℝ} (hsT : s ≤ T) :
    Measurable (flow134 Λ P M i im sp s T) := by
  have eF : flow134 Λ P M i im sp s T =
      -(intRS s T (disc Λ P) (addProc B M) + intRS s T (addProc B M) A) := funext fun ω => by
    simp only [flow134, Pi.neg_apply, Pi.add_apply, intRS]
    rw [hm.pathwise_1_34_jump ω hsT, neg_neg]
  rw [eF]
  rcases hsT.lt_or_eq with hlt | rfl
  · have hWm : ∀ u, Measurable (addProc B M u) := fun u =>
      ((hm.W_adapted u).mono (𝓕.le u)).measurable
    have hnm : ∀ u, Measurable (disc Λ P u) := fun u =>
      ((hm.disc_adapted u).mono (𝓕.le u)).measurable
    have m1 : Measurable (intRS s T (disc Λ P) (addProc B M)) :=
      TidyR7StieltjesCalculus.measurable_rsInt (f := fun ω u => disc Λ P u ω)
        (g := fun ω u => addProc B M u ω) hlt hnm hWm fun ω =>
          Or.inr ⟨hm.disc_cadlag ω, hm.W_bv ω s T, (hm.W_cont ω).continuousOn⟩
    have m2 : Measurable (intRS s T (addProc B M) A) :=
      TidyR7StieltjesCalculus.measurable_rsInt (f := fun ω u => addProc B M u ω)
        (g := fun ω u => A u ω) hlt hWm hm.measurable_A fun ω =>
          Or.inl ⟨(hm.W_cont ω).continuousOn, hm.A_bv ω s T⟩
    exact (m1.add m2).neg
  · have e : intRS s s (disc Λ P) (addProc B M) + intRS s s (addProc B M) A = 0 :=
      funext fun ω => by
        simp only [Pi.add_apply, intRS, TidyR7StieltjesVariation.rsInt_self, add_zero,
          Pi.zero_apply]
    rw [e, neg_zero]
    exact measurable_const

/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567: the finite-horizon budget for `B + M`, jumping
money.** Under the domination conditions for `B + M` on `[s, T]` and integrability:
`n_s(B + M)_s = E_s[n_T(B + M)_T] + E_s∫_s^T (Λs + (i − i^m)nM) dr` a.s.; the flow is integrable.
An instance of `TidyR7MonetarismValuation.rec_of_incr`. -/
theorem rec_1_34_jump {s T : ℝ} (hsT : s ≤ T)
    (hd : Dominated μ A N s T (addProc B M) (disc Λ P))
    (hYs : Integrable (fun ω => disc Λ P s ω * addProc B M s ω) μ)
    (hYT : Integrable (fun ω => disc Λ P T ω * addProc B M T ω) μ) :
    Integrable (flow134 Λ P M i im sp s T) μ ∧
      (fun ω => disc Λ P s ω * addProc B M s ω) =ᵐ[μ]
        μ[fun ω => disc Λ P T ω * addProc B M T ω | 𝓕 s] +
          μ[flow134 Λ P M i im sp s T | 𝓕 s] := by
  have hpd := hm.productStepData_W hsT hd
  have i1 := hpd.integrable_intXB
  rw [← hm.disc_eq] at i1
  have eF : flow134 Λ P M i im sp s T =
      -(intRS s T (disc Λ P) (addProc B M) + intRS s T (addProc B M) A) := funext fun ω => by
    simp only [flow134, Pi.neg_apply, Pi.add_apply, intRS]
    rw [hm.pathwise_1_34_jump ω hsT, neg_neg]
  have hF : Integrable (flow134 Λ P M i im sp s T) μ := by
    rw [eF]
    exact (i1.add hpd.integrable_intBA).neg
  refine ⟨hF, ?_⟩
  exact rec_of_incr (Y := fun t ω => disc Λ P t ω * addProc B M t ω)
    (F := flow134 Λ P M i im sp s T) (hm.incr_1_34_jump hsT hd)
    ((hm.disc_adapted s).mul (hm.W_adapted s)) hYs hYT

/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567, limit form, jumping money.** Along any
`T_k ≥ s`, a.s. `E_s∫_s^{T_k} (Λs + (i − i^m)nM) dr → n_s(B + M)_s` iff a.s.
`E_s[n_{T_k}(B + M)_{T_k}] → 0`.
An instance of `TidyR7MonetarismValuation.valuation_iff_tvc_seq`. -/
theorem valuation_1_34_jump_seq {s : ℝ}
    (hd : ∀ T, s ≤ T → Dominated μ A N s T (addProc B M) (disc Λ P))
    (hYi : ∀ T, s ≤ T → Integrable (fun ω => disc Λ P T ω * addProc B M T ω) μ) {T : ℕ → ℝ}
    (hT : ∀ k, s ≤ T k) :
    (∀ᵐ ω ∂μ, Tendsto (fun k => μ[flow134 Λ P M i im sp s (T k) | 𝓕 s] ω) atTop
        (𝓝 (disc Λ P s ω * addProc B M s ω))) ↔
      ∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => disc Λ P (T k) ω * addProc B M (T k) ω | 𝓕 s] ω)
        atTop (𝓝 0) :=
  valuation_iff_tvc_seq (Y := fun t ω => disc Λ P t ω * addProc B M t ω)
    (fun T' hT' => (hm.rec_1_34_jump hT' (hd T' hT') (hYi s le_rfl) (hYi T' hT')).2) hT

/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567, `L¹` form, jumping money: valuation iff
transversality.** With `F_T → G` in `L¹`: `n_s(B + M)_s = E_s[G]` a.s. iff
`E_s[n_T(B + M)_T] → 0` in `L¹`.
Generalises `TidyR7MonetarismValuation.MonetaryModel.valuation_1_34`. -/
theorem valuation_1_34_jump {s : ℝ}
    (hd : ∀ T, s ≤ T → Dominated μ A N s T (addProc B M) (disc Λ P))
    (hYi : ∀ T, s ≤ T → Integrable (fun ω => disc Λ P T ω * addProc B M T ω) μ) {G : Ω → ℝ}
    (hG : Integrable G μ)
    (hconv : Tendsto (fun T => ∫ ω, |flow134 Λ P M i im sp s T ω - G ω| ∂μ) atTop (𝓝 0)) :
    (fun ω => disc Λ P s ω * addProc B M s ω) =ᵐ[μ] μ[G | 𝓕 s] ↔
      Tendsto (fun T => ∫ ω, |μ[fun ω => disc Λ P T ω * addProc B M T ω | 𝓕 s] ω| ∂μ) atTop
        (𝓝 0) :=
  valuation_iff_tvc_flow (Y := fun t ω => disc Λ P t ω * addProc B M t ω)
    (F := flow134 Λ P M i im sp s)
    (fun T hT => (hm.rec_1_34_jump hT (hd T hT) (hYi s le_rfl) (hYi T hT)).2) hYi
    (fun T hT => (hm.rec_1_34_jump hT (hd T hT) (hYi s le_rfl) (hYi T hT)).1) hG hconv

/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567, dominated form, jumping money.** If along
`T_k ≥ s` the flows converge path by path to `G` with `|F_{T_k}| ≤ H` integrable:
`n_s(B + M)_s = E_s[G]` a.s. iff `E_s[n_{T_k}(B + M)_{T_k}] → 0` a.s.
An instance of `TidyR7MonetarismValuation.valuation_iff_tvc_dom`. -/
theorem valuation_1_34_jump_dom {s : ℝ}
    (hd : ∀ T, s ≤ T → Dominated μ A N s T (addProc B M) (disc Λ P))
    (hYi : ∀ T, s ≤ T → Integrable (fun ω => disc Λ P T ω * addProc B M T ω) μ) {T : ℕ → ℝ}
    (hT : ∀ k, s ≤ T k) {G H : Ω → ℝ} (hH : Integrable H μ)
    (hbd : ∀ k ω, |flow134 Λ P M i im sp s (T k) ω| ≤ H ω)
    (hlim : ∀ ω, Tendsto (fun k => flow134 Λ P M i im sp s (T k) ω) atTop (𝓝 (G ω))) :
    (fun ω => disc Λ P s ω * addProc B M s ω) =ᵐ[μ] μ[G | 𝓕 s] ↔
      ∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => disc Λ P (T k) ω * addProc B M (T k) ω | 𝓕 s] ω)
        atTop (𝓝 0) :=
  valuation_iff_tvc_dom (Y := fun t ω => disc Λ P t ω * addProc B M t ω)
    (F := flow134 Λ P M i im sp s)
    (fun T' hT' => (hm.rec_1_34_jump hT' (hd T' hT') (hYi s le_rfl) (hYi T' hT')).2) hT
    (fun k => hm.measurable_flow134_jump (hT k)) hH hbd hlim

end JumpMonetaryModel

end Cochrane.Monetarism.TidyR7MonetarismJump
