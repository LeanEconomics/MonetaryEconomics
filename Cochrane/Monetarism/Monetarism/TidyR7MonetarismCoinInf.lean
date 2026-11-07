/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR7MonetarismCoin
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Non-vacuity of (1.33)–(1.34) on `[0, ∞)` with news in `Λ/P`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). An infinite-horizon instance of
`TidyR7MonetarismValuation.MonetaryModel.valuation_1_33`,
`TidyR7MonetarismValuation.MonetaryModel.valuation_1_33_book` and
`TidyR7MonetarismValuation.MonetaryModel.valuation_1_34_book` on the fair coin of
`TidyR7ProductStepCoin` (`ξ = ±1` revealed at time `1`, `H = 1{u ≥ 1}`).

## The model (`infModel`)

`P = 1`, `Λ_u = n_u = 1 + e^{−u} + (ξ/4)H(u)`: the finite-variation part is `A_u = 1 + e^{−u}`,
the martingale part `N_u = (ξ/4)H(u)` is not zero (`infN_ne_zero`), and the nominal rate
`i_u = e^{−u}/n_u > 0` (`infI_pos`) makes `dA = −i n dt` hold exactly. Bonds `B_u = e^{−u}` are
paid down by the bounded surplus `s_u = i_uB_u + e^{−u}` (so `dB = (iB − Ps) dt`, (1.31)), money
`M = 0`, `i^m = 0`.

## Results

* `inf_flow133`: for `T ≥ 1`, path by path
  `∫_0^T Λs dr + ∫_0^T n dM = 2 − (1 + e^{−T})e^{−T} + (ξ/4)(e^{−1} − e^{−T})`, which tends to
  `G = 2 + (ξ/4)e^{−1}` (`inf_tendsto`), with `|F_T| ≤ 5`.
* `inf_tvc_eq`: `E_0[n_TB_T] = (1 + e^{−T})e^{−T} → 0`: the transversality condition holds.
* `inf_1_33`: `MonetaryModel.valuation_1_33` (`L¹` form) applies, and both of its sides hold:
  `n_0B_0 = 2 = E_0[G]`.
* `inf_1_33_book`: `MonetaryModel.valuation_1_33_book` applies along `T_k = k + 1`; both sides
computed:
  `B_0/P_0 = 1 = E_0[G/Λ_0]`, and the transversality condition holds.
* `inf_1_34_book`: the same for `MonetaryModel.valuation_1_34_book` (here `M = 0`).
-/

namespace Cochrane.Monetarism.TidyR7MonetarismCoinInf

open MeasureTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesIntegral Cochrane.Monetarism.TidyR7StieltjesSums
  Cochrane.Monetarism.TidyR7ProductStep Cochrane.Monetarism.TidyR7ProductStepCoin
  Cochrane.Monetarism.TidyR7MonetarismAC Cochrane.Monetarism.TidyR7MonetarismModel
  Cochrane.Monetarism.TidyR7MonetarismValuation Cochrane.Monetarism.TidyR7MonetarismCoin

/-! ## Exponential tools -/

/-- Cochrane (2023), A1 §1.6, p. 567 (non-vacuity): `d/du e^{−u} = −e^{−u}`. -/
theorem hasDerivAt_expNeg (r : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-r)) r := by
  have := (hasDerivAt_neg r).exp
  simpa using this

/-- Cochrane (2023), A1 §1.6, p. 567: `e^{−u}` is continuous. -/
theorem continuous_expNeg : Continuous fun u : ℝ => Real.exp (-u) :=
  Real.continuous_exp.comp continuous_neg

/-- Cochrane (2023), A1 §1.6, p. 567: `∫_u^v e^{−r} dr = e^{−u} − e^{−v}`. -/
theorem integral_expNeg (u v : ℝ) : ∫ r in u..v, Real.exp (-r) = Real.exp (-u) - Real.exp (-v) := by
  have h : ∀ r, HasDerivAt (-(fun x : ℝ => Real.exp (-x))) (Real.exp (-r)) r := fun r => by
    simpa using (hasDerivAt_expNeg r).neg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => h r)
    (continuous_expNeg.intervalIntegrable u v)]
  simp only [Pi.neg_apply]
  ring

/-- Cochrane (2023), A1 §1.6, p. 567: `e^{−u} ≤ 1` for `u ≥ 0`. -/
theorem expNeg_le_one {u : ℝ} (hu : 0 ≤ u) : Real.exp (-u) ≤ 1 :=
  Real.exp_le_one_iff.2 (by linarith)

/-! ## The model -/

/-- Cochrane (2023), A1 §1.6, p. 567: `Λ_u = 1 + e^{−u} + (ξ/4)H(u)` (`= Λ/P`, `P = 1`). -/
noncomputable def infLam (u : ℝ) (ω : Bool) : ℝ := 1 + Real.exp (-u) + coinXi ω / 4 * heaviside u

/-- Cochrane (2023), A1 §1.6, p. 567: the finite-variation part `A_u = 1 + e^{−u}`. -/
noncomputable def infA (u : ℝ) (_ : Bool) : ℝ := 1 + Real.exp (-u)

/-- Cochrane (2023), A1 §1.6, p. 567: the martingale part `N_u = (ξ/4)H(u)`. -/
noncomputable def infN (u : ℝ) (ω : Bool) : ℝ := coinXi ω / 4 * heaviside u

/-- Cochrane (2023), A1 §1.6, p. 567: the nominal rate `i_u = e^{−u}/n_u`. -/
noncomputable def infI (u : ℝ) (ω : Bool) : ℝ := Real.exp (-u) / infLam u ω

/-- Cochrane (2023), A1 §1.6, p. 567: bonds `B_u = e^{−u}`. -/
noncomputable def infB (u : ℝ) (_ : Bool) : ℝ := Real.exp (-u)

/-- Cochrane (2023), A1 §1.6, p. 567: the surplus `s_u = i_uB_u + e^{−u}`. -/
noncomputable def infSur (u : ℝ) (ω : Bool) : ℝ := infI u ω * infB u ω + Real.exp (-u)

/-- Cochrane (2023), A1 §1.6, p. 567: `|(ξ/4)H| ≤ 1/4`. -/
theorem abs_infN_le (u : ℝ) (ω : Bool) : |coinXi ω / 4 * heaviside u| ≤ 1 / 4 := by
  rw [abs_mul, abs_div, abs_coinXi]
  simp only [heaviside]
  split_ifs <;> norm_num

/-- Cochrane (2023), A1 §1.6, p. 567: `Λ = n > 0` (indeed `≥ 3/4`). -/
theorem infLam_pos (u : ℝ) (ω : Bool) : 0 < infLam u ω := by
  have h1 := abs_infN_le u ω
  have h2 := Real.exp_pos (-u)
  simp only [infLam]
  linarith [neg_abs_le (coinXi ω / 4 * heaviside u)]

/-- Cochrane (2023), A1 §1.6, p. 567: the nominal rate is positive. -/
theorem infI_pos (u : ℝ) (ω : Bool) : 0 < infI u ω :=
  div_pos (Real.exp_pos _) (infLam_pos u ω)

/-- Cochrane (2023), A1 §1.6, p. 567: `Λ/P = Λ` here. -/
theorem disc_inf (u : ℝ) (ω : Bool) : disc infLam coinP u ω = infLam u ω := by
  simp [disc, coinP]

/-- Cochrane (2023), A1 §1.6, p. 567: `i n = e^{−u}`. -/
theorem infI_mul (u : ℝ) (ω : Bool) : infI u ω * infLam u ω = Real.exp (-u) :=
  div_mul_cancel₀ _ (infLam_pos u ω).ne'

/-- Cochrane (2023), A1 §1.6, p. 567: the bond-pricing density `−i n = −e^{−u}`. -/
theorem rate_inf (ω : Bool) :
    (fun r => -(infI r ω * disc infLam coinP r ω)) = fun r => -Real.exp (-r) :=
  funext fun r => by rw [disc_inf, infI_mul]

/-- Cochrane (2023), A1 §1.6, (1.31), p. 567: the flow density is `−e^{−u}`. -/
theorem flowRate_inf (ω : Bool) :
    (fun r => flowRate infB zeroRate coinP infI zeroRate infSur r ω) =
      fun r => -Real.exp (-r) :=
  funext fun r => by simp only [flowRate, zeroRate, coinP, infSur]; ring

/-- **Cochrane (2023), A1 §1.6, (1.31)–(1.34), pp. 567–568: an infinite-horizon model with news in
`Λ/P` and a positive nominal rate** satisfying `TidyR7MonetarismModel.MonetaryModel`. -/
theorem infModel : MonetaryModel coinMeasure coinFiltration infLam coinP infB zeroRate infA infN
    infI zeroRate infSur where
  P_pos _ _ := one_pos
  Λ_pos := infLam_pos
  Λ_adapted := coin_adapted fun u hu ω => by simp [infLam, heaviside, not_le.2 hu]
  P_adapted _ := stronglyMeasurable_const
  dec u ω := by rw [disc_inf]; simp only [infLam, infA, infN]
  A_incr ω u v _ := by
    rw [rate_inf ω, intervalIntegral.integral_neg, integral_expNeg]
    simp only [infA]
    ring
  A_int ω u v := by
    rw [rate_inf ω]
    exact continuous_expNeg.neg.intervalIntegrable u v
  N_mart := by
    have e : infN = (1 / 4 : ℝ) • coinM := funext fun u => funext fun ω => by
      simp only [infN, coinM, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact martingale_coinM.smul _
  N_cadlag ω := isCadlag_heaviside.continuous_comp (continuous_const.mul continuous_id
    (f := fun _ : ℝ => coinXi ω / 4))
  B_adapted _ := stronglyMeasurable_const
  M_adapted _ := stronglyMeasurable_const
  M_cont _ := continuous_const
  M_bv _ a b := by
    rw [BoundedVariationOn, eVariationOn.constant_on
      (Set.subsingleton_of_forall_eq (0 : ℝ) fun _ ⟨_, _, hy⟩ => hy.symm)]
    exact ENNReal.zero_ne_top
  flow ω u v _ := by
    rw [flowRate_inf ω, intervalIntegral.integral_neg, integral_expNeg]
    simp only [addProc, infB, zeroRate]
    ring
  flow_int ω u v := by
    rw [flowRate_inf ω]
    exact continuous_expNeg.neg.intervalIntegrable u v

/-- Cochrane (2023), A1 §1.6, p. 567: the martingale part of `Λ/P` is not zero. -/
theorem infN_ne_zero : infN 1 true ≠ 0 := by
  simp [infN, coinXi, heaviside]

/-- Cochrane (2023), A1 §1.6, p. 567: the domination conditions hold on every interval. -/
theorem infDom (s t : ℝ) : Dominated coinMeasure infA infN s t infB (disc infLam coinP) :=
  ⟨Integrable.of_finite, Integrable.of_finite, fun _ _ _ _ _ => Integrable.of_finite⟩

/-- Cochrane (2023), A1 §1.6, p. 567: the domination conditions for `B + M` hold on every
interval. -/
theorem infDomW (s t : ℝ) :
    Dominated coinMeasure infA infN s t (addProc infB zeroRate) (disc infLam coinP) :=
  ⟨Integrable.of_finite, Integrable.of_finite, fun _ _ _ _ _ => Integrable.of_finite⟩

/-! ## The flows -/

/-- Cochrane (2023), A1 §1.6, p. 567: `∫_0^T H(r)e^{−r} dr = e^{−1} − e^{−T}` for `T ≥ 1`. -/
theorem integral_heaviside_expNeg {T : ℝ} (hT : 1 ≤ T) :
    ∫ r in (0 : ℝ)..T, heaviside r * Real.exp (-r) = Real.exp (-1) - Real.exp (-T) := by
  have hint : ∀ a b : ℝ, a ≤ b → IntervalIntegrable (fun r => heaviside r * Real.exp (-r))
      MeasureSpace.volume a b := fun a b hab =>
    intervalIntegrable_mul_of_isCadlag isCadlag_heaviside hab
      (continuous_expNeg.intervalIntegrable a b)
  have hne : ∀ᵐ x : ℝ ∂MeasureSpace.volume, x ∉ ({1} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 (measure_singleton 1)
  have h0 : ∫ r in (0 : ℝ)..1, heaviside r * Real.exp (-r) = ∫ _ in (0 : ℝ)..1, (0 : ℝ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hne] with r hr hr'
    rw [Set.uIoc_of_le (by norm_num)] at hr'
    have hr1 : r < 1 := lt_of_le_of_ne hr'.2 (by simpa using hr)
    simp [heaviside, not_le.2 hr1]
  have h1 : ∫ r in (1 : ℝ)..T, heaviside r * Real.exp (-r) = ∫ r in (1 : ℝ)..T, Real.exp (-r) := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun r hr => ?_)
    rw [Set.uIoc_of_le hT] at hr
    simp [heaviside, hr.1.le]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 1 (by norm_num)) (hint 1 T hT),
    h0, h1, intervalIntegral.integral_zero, integral_expNeg]
  simp

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the flows on `infModel`.** For `T ≥ 1`, path by
path, `∫_0^T Λs dr + ∫_0^T n dM = 2 − (1 + e^{−T})e^{−T} + (ξ/4)(e^{−1} − e^{−T})`. -/
theorem inf_flow133 {T : ℝ} (hT : 1 ≤ T) (ω : Bool) :
    flow133 infLam coinP zeroRate infSur 0 T ω =
      2 - (1 + Real.exp (-T)) * Real.exp (-T) +
        coinXi ω / 4 * (Real.exp (-1) - Real.exp (-T)) := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hrs := rsInt_eq_integral_of_incr (f := fun u => disc infLam coinP u ω)
    (g := fun u => zeroRate u ω) (h := fun _ => (0 : ℝ))
    (infModel.disc_cadlag ω) (fun _ _ => intervalIntegrable_const)
    (fun u v _ => by simp [zeroRate]) hT0
  set e : ℝ → ℝ := fun r => Real.exp (-r) with he
  have hq : ∀ r, HasDerivAt (fun x => -((1 + e x) * e x)) (e r * e r + (1 + e r) * e r) r :=
    fun r => by
      have := ((((hasDerivAt_const r (1 : ℝ)).add (hasDerivAt_expNeg r)).mul
        (hasDerivAt_expNeg r))).neg
      simp only [he]
      convert this using 1
      simp only [Pi.add_apply]
      ring
  have hc1 : Continuous fun r => e r * e r + (1 + e r) * e r := by
    simp only [he]; fun_prop
  have hI1 : ∫ r in (0 : ℝ)..T, (e r * e r + (1 + e r) * e r) =
      2 - (1 + Real.exp (-T)) * Real.exp (-T) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hq r)
      (hc1.intervalIntegrable 0 T)]
    simp only [he, neg_zero, Real.exp_zero]
    ring
  have hint2 : IntervalIntegrable (fun r => heaviside r * Real.exp (-r)) MeasureSpace.volume 0 T :=
    intervalIntegrable_mul_of_isCadlag isCadlag_heaviside hT0
      (continuous_expNeg.intervalIntegrable 0 T)
  have hpt : ∀ r, infLam r ω * infSur r ω =
      (e r * e r + (1 + e r) * e r) + coinXi ω / 4 * (heaviside r * Real.exp (-r)) := by
    intro r
    have h := infI_mul r ω
    simp only [infSur, infB, he]
    have e1 : infLam r ω * (infI r ω * Real.exp (-r) + Real.exp (-r)) =
        (infI r ω * infLam r ω) * Real.exp (-r) + infLam r ω * Real.exp (-r) := by ring
    rw [e1, h]
    simp only [infLam]
    ring
  rw [flow133, hrs, intervalIntegral.integral_congr (fun r _ => hpt r),
    intervalIntegral.integral_add (hc1.intervalIntegrable 0 T) (hint2.const_mul _),
    intervalIntegral.integral_const_mul, hI1, integral_heaviside_expNeg hT]
  simp

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: the limit `G = 2 + (ξ/4)e^{−1}` of the flows. -/
noncomputable def infG (ω : Bool) : ℝ := 2 + coinXi ω / 4 * Real.exp (-1)

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the flows converge path by path to `G`.** -/
theorem inf_tendsto (ω : Bool) :
    Tendsto (fun T => flow133 infLam coinP zeroRate infSur 0 T ω) atTop (𝓝 (infG ω)) := by
  have he := Real.tendsto_exp_neg_atTop_nhds_zero
  have h : Tendsto (fun T : ℝ => 2 - (1 + Real.exp (-T)) * Real.exp (-T) +
      coinXi ω / 4 * (Real.exp (-1) - Real.exp (-T))) atTop
      (𝓝 (2 - (1 + 0) * 0 + coinXi ω / 4 * (Real.exp (-1) - 0))) :=
    ((tendsto_const_nhds.sub ((tendsto_const_nhds.add he).mul he)).add
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub he)))
  have e : 2 - (1 + 0) * 0 + coinXi ω / 4 * (Real.exp (-1) - 0) = infG ω := by
    simp only [infG]; ring
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  rw [inf_flow133 hT]

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: `|F_T| ≤ 5` for `T ≥ 1`. -/
theorem abs_inf_flow133_le {T : ℝ} (hT : 1 ≤ T) (ω : Bool) :
    |flow133 infLam coinP zeroRate infSur 0 T ω| ≤ 5 := by
  rw [inf_flow133 hT]
  have h1 := expNeg_le_one (by linarith : (0 : ℝ) ≤ T)
  have h2 := Real.exp_pos (-T)
  have h3 := expNeg_le_one (by norm_num : (0 : ℝ) ≤ 1)
  have h4 := Real.exp_pos (-1)
  have hx := abs_coinXi ω
  have habs : |Real.exp (-1) - Real.exp (-T)| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hb : |coinXi ω / 4 * (Real.exp (-1) - Real.exp (-T))| ≤ 1 := by
    rw [abs_mul, abs_div, hx, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    linarith [abs_nonneg (Real.exp (-1) - Real.exp (-T))]
  have hq0 : 0 ≤ (1 + Real.exp (-T)) * Real.exp (-T) := by positivity
  have hq2 : (1 + Real.exp (-T)) * Real.exp (-T) ≤ 2 := by nlinarith
  rw [abs_le] at hb ⊢
  constructor <;> linarith [hb.1, hb.2]

/-! ## Both sides of (1.33) and (1.34) -/

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the transversality condition holds:**
`E_0[n_TB_T] = (1 + e^{−T})e^{−T}` (with `H(T) = 1` for `T ≥ 1`), which tends to `0`. -/
theorem inf_tvc_eq {T : ℝ} (hT : 1 ≤ T) :
    coinMeasure[fun ω => disc infLam coinP T ω * infB T ω | coinFiltration 0] =
      fun _ => (1 + Real.exp (-T)) * Real.exp (-T) := by
  rw [condExp_coin_lt (by norm_num)]
  funext _
  simp only [disc_inf, infLam, infB, coinXi, heaviside, hT, ↓reduceIte, Bool.false_eq_true]
  ring

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: `(1 + e^{−T})e^{−T} → 0`. -/
theorem tendsto_tvc_inf :
    Tendsto (fun T : ℝ => (1 + Real.exp (-T)) * Real.exp (-T)) atTop (𝓝 0) := by
  have he := Real.tendsto_exp_neg_atTop_nhds_zero
  have := ((tendsto_const_nhds (x := (1 : ℝ))).add he).mul he
  simpa using this

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: `E_0[G] = 2 = n_0B_0`. -/
theorem inf_EG : coinMeasure[infG | coinFiltration 0] = fun _ => 2 := by
  rw [condExp_coin_lt (by norm_num)]
  funext _
  simp only [infG, coinXi]
  norm_num
  ring

/-- Cochrane (2023), A1 §1.6, p. 567: `n_0B_0 = 2` (`Λ_0 = 2`, `B_0 = 1`). -/
theorem inf_Y0 (ω : Bool) : disc infLam coinP 0 ω * infB 0 ω = 2 := by
  simp [disc_inf, infLam, infB, heaviside]
  norm_num

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567, `L¹` form on `[0, ∞)` with news in `Λ/P`.**
On `infModel` the flows converge in `L¹` to `G`, `MonetaryModel.valuation_1_33` applies, and both
of its sides
hold: `n_0B_0 = E_0[G]` (both `2`) and `∫|E_0[n_TB_T]| → 0`. -/
theorem inf_1_33 :
    Tendsto (fun T => ∫ ω, |flow133 infLam coinP zeroRate infSur 0 T ω - infG ω| ∂coinMeasure)
        atTop (𝓝 0) ∧
      ((fun ω => disc infLam coinP 0 ω * infB 0 ω) =ᵐ[coinMeasure]
          coinMeasure[infG | coinFiltration 0] ↔
        Tendsto (fun T => ∫ ω, |coinMeasure[fun ω => disc infLam coinP T ω * infB T ω |
          coinFiltration 0] ω| ∂coinMeasure) atTop (𝓝 0)) ∧
      (fun ω => disc infLam coinP 0 ω * infB 0 ω) =ᵐ[coinMeasure]
          coinMeasure[infG | coinFiltration 0] ∧
      Tendsto (fun T => ∫ ω, |coinMeasure[fun ω => disc infLam coinP T ω * infB T ω |
          coinFiltration 0] ω| ∂coinMeasure) atTop (𝓝 0) := by
  have hconv : Tendsto (fun T => ∫ ω, |flow133 infLam coinP zeroRate infSur 0 T ω - infG ω|
      ∂coinMeasure) atTop (𝓝 0) := by
    simp only [integral_coin]
    have h1 := ((inf_tendsto true).sub_const (infG true)).abs
    have h2 := ((inf_tendsto false).sub_const (infG false)).abs
    have := (h1.add h2).div_const 2
    simpa using this
  have hval := MonetaryModel.valuation_1_33 infModel (fun _ _ => rfl) (s := 0)
    (fun T _ => infDom 0 T) (fun _ _ => Integrable.of_finite) (G := infG) Integrable.of_finite
    hconv
  have hlhs : (fun ω => disc infLam coinP 0 ω * infB 0 ω) =ᵐ[coinMeasure]
      coinMeasure[infG | coinFiltration 0] := by
    rw [inf_EG]
    exact Eventually.of_forall fun ω => inf_Y0 ω
  refine ⟨hconv, hval, hlhs, hval.1 hlhs⟩

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567, as printed, on `[0, ∞)` with news in `Λ/P`.**
On `infModel`, along `T_k = k + 1`, the conclusion of `MonetaryModel.valuation_1_33_book` holds,
both sides are
computed (`B_0/P_0 = 1` and `E_0[G/Λ_0] = 1`), and the transversality condition holds:
`E_0[n_{T_k}B_{T_k}] → 0`. -/
theorem inf_1_33_book :
    ((∀ ω, Tendsto (fun k : ℕ => (∫ r in (0 : ℝ)..((k : ℝ) + 1),
          infLam r ω / infLam 0 ω * infSur r ω) +
        rsInt 0 ((k : ℝ) + 1) (fun u => infLam u ω / infLam 0 ω / coinP u ω)
          (fun u => zeroRate u ω)) atTop (𝓝 (infG ω / infLam 0 ω))) ∧
      ((fun ω => infB 0 ω / coinP 0 ω) =ᵐ[coinMeasure]
          coinMeasure[fun ω => infG ω / infLam 0 ω | coinFiltration 0] ↔
        ∀ᵐ ω ∂coinMeasure, Tendsto (fun k : ℕ => coinMeasure[fun ω =>
          disc infLam coinP ((k : ℝ) + 1) ω * infB ((k : ℝ) + 1) ω | coinFiltration 0] ω)
            atTop (𝓝 0))) ∧
      (fun ω => infB 0 ω / coinP 0 ω) = (fun _ => 1) ∧
      coinMeasure[fun ω => infG ω / infLam 0 ω | coinFiltration 0] = (fun _ => 1) ∧
      ∀ ω, Tendsto (fun k : ℕ => coinMeasure[fun ω =>
          disc infLam coinP ((k : ℝ) + 1) ω * infB ((k : ℝ) + 1) ω | coinFiltration 0] ω)
            atTop (𝓝 0) := by
  have hT : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k => by
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hseq : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  refine ⟨MonetaryModel.valuation_1_33_book infModel (fun _ _ => rfl) (s := 0)
    (fun T _ => infDom 0 T) (fun _ _ => Integrable.of_finite) (T := fun k : ℕ => (k : ℝ) + 1)
    (fun k => by linarith [hT k]) (H := fun _ => 5) (integrable_const _)
    (fun k ω => abs_inf_flow133_le (hT k) ω) (fun ω => (inf_tendsto ω).comp hseq)
    Integrable.of_finite, ?_, ?_, fun ω => ?_⟩
  · funext _
    simp [infB, coinP]
  · rw [condExp_coin_lt (by norm_num)]
    funext _
    simp only [infG, infLam, coinXi, heaviside, neg_zero, Real.exp_zero]
    norm_num
    ring
  · have h := tendsto_tvc_inf.comp hseq
    refine h.congr fun k => ?_
    rw [inf_tvc_eq (hT k)]
    rfl

/-- Cochrane (2023), A1 §1.6, (1.34), p. 567: with `M = 0` the flow of (1.34) is that of (1.33). -/
theorem inf_flow134 (T : ℝ) (ω : Bool) (hT : 0 ≤ T) :
    flow134 infLam coinP zeroRate infI zeroRate infSur 0 T ω =
      flow133 infLam coinP zeroRate infSur 0 T ω := by
  have hrs := rsInt_eq_integral_of_incr (f := fun u => disc infLam coinP u ω)
    (g := fun u => zeroRate u ω) (h := fun _ => (0 : ℝ))
    (infModel.disc_cadlag ω) (fun _ _ => intervalIntegrable_const)
    (fun u v _ => by simp [zeroRate]) hT
  rw [flow134, flow133, hrs]
  simp [zeroRate]

/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567, as printed, on `[0, ∞)` with news in `Λ/P`.** On
`infModel` (`M = 0`, `i^m = 0`), along `T_k = k + 1`, the conclusion of
`MonetaryModel.valuation_1_34_book`
holds; `(M_0 + B_0)/P_0 = 1 = E_0[G/Λ_0]` and the transversality condition holds. -/
theorem inf_1_34_book :
    ((∀ ω, Tendsto (fun k : ℕ => ∫ r in (0 : ℝ)..((k : ℝ) + 1),
        infLam r ω / infLam 0 ω * (infSur r ω + (infI r ω - zeroRate r ω) * zeroRate r ω /
          coinP r ω)) atTop (𝓝 (infG ω / infLam 0 ω))) ∧
      ((fun ω => addProc infB zeroRate 0 ω / coinP 0 ω) =ᵐ[coinMeasure]
          coinMeasure[fun ω => infG ω / infLam 0 ω | coinFiltration 0] ↔
        ∀ᵐ ω ∂coinMeasure, Tendsto (fun k : ℕ => coinMeasure[fun ω =>
          disc infLam coinP ((k : ℝ) + 1) ω * addProc infB zeroRate ((k : ℝ) + 1) ω |
            coinFiltration 0] ω) atTop (𝓝 0))) ∧
      (fun ω => addProc infB zeroRate 0 ω / coinP 0 ω) = (fun _ => 1) ∧
      ∀ ω, Tendsto (fun k : ℕ => coinMeasure[fun ω =>
          disc infLam coinP ((k : ℝ) + 1) ω * addProc infB zeroRate ((k : ℝ) + 1) ω |
            coinFiltration 0] ω) atTop (𝓝 0) := by
  have hT : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k => by
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hseq : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have eW : addProc infB zeroRate = infB := funext fun u => funext fun ω => by
    simp [addProc, zeroRate]
  refine ⟨MonetaryModel.valuation_1_34_book infModel (s := 0) (fun s t _ => infDomW s t)
    (fun _ => Integrable.of_finite) (T := fun k : ℕ => (k : ℝ) + 1)
    (fun k => by linarith [hT k]) (H := fun _ => 5) (integrable_const _)
    (fun k ω => by rw [inf_flow134 _ ω (by linarith [hT k])]; exact abs_inf_flow133_le (hT k) ω)
    (fun ω => ((inf_tendsto ω).comp hseq).congr fun k => by
      simp only [Function.comp]
      rw [inf_flow134 _ ω (by linarith [hT k])])
    Integrable.of_finite, ?_, fun ω => ?_⟩
  · funext _
    simp [addProc, infB, coinP, zeroRate]
  · rw [eW]
    have h := tendsto_tvc_inf.comp hseq
    refine h.congr fun k => ?_
    rw [inf_tvc_eq (hT k)]
    rfl

end Cochrane.Monetarism.TidyR7MonetarismCoinInf
