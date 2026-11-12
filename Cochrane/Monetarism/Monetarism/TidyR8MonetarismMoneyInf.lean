/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR7MonetarismCoinInf

/-!
# (1.34) on `[0, ∞)` with nonzero money and interest on money

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). An infinite-horizon instance of
`TidyR7MonetarismValuation.MonetaryModel.valuation_1_34_book` and
`TidyR7MonetarismValuation.MonetaryModel.valuation_1_34` with `M ≠ 0` and `i^m ≠ 0`, on the
fair coin of `TidyR7ProductStepCoin` (`ξ = ±1` revealed at time `1`, `H = 1{u ≥ 1}`).

`TidyR7MonetarismCoinInf` has zero money: there `Λ/P → 1 + ξ/4`, so with constant nonzero money
the money transversality condition fails. Here the nominal discount factor decays.

## The discount factor (`decLam`)

`P = 1`, `Λ_u = n_u = e^{−u}(1 + (ξ/2)H(u)) > 0`, the nominal rate is `i = 1`:
`n = A + N` with the martingale `N_u = (ξ/2)e^{−1}H(u)` (`decN`, not zero) and
`A_u = e^{−u} − (ξ/2)φ(u)`, `φ(u) = (e^{−1} − e^{−u})⁺` (`decPhi`), so that `dA = −n du = −i n du`
(`integral_heaviside_expNeg_gen`: `∫_u^v H e^{−r} dr = φ(v) − φ(u)`). This discount factor is
shared with `TidyR8MonetarismJumpInf`.

## The economy (`moneyInfModel`)

Bonds `B = 2`, money `M = 2`, interest on money `i^m = 1/2`, surplus `s = 3`: (1.31) holds,
`iB + i^mM − Ps = 2 + 1 − 3 = 0 = d(B + M)/dt`. The seigniorage term `(i − i^m)M/P = 1` is not
zero.

## Results

* `moneyInf_flow134`: for `T ≥ 1`, `∫_0^T (Λs + (i − i^m)nM) dr = ∫_0^T 4Λ
  = 4(1 − e^{−T}) + 2ξ(e^{−1} − e^{−T})`, tending to `G = 4 + 2ξe^{−1}` (`moneyInf_tendsto`),
  `|F_T| ≤ 6`.
* `moneyInf_tvc_eq`: `E_0[n_T(B_T + M_T)] = 4e^{−T} → 0`: the transversality condition holds.
* `moneyInf_1_34_book` (headline): the conclusion of `MonetaryModel.valuation_1_34_book` holds,
  and both sides are computed: `(M_0 + B_0)/P_0 = 4 = E_0[G/Λ_0]`.
* `moneyInf_1_34_L1`: the `L¹` form `MonetaryModel.valuation_1_34`, both sides holding.
-/

namespace Cochrane.Monetarism.TidyR8MonetarismMoneyInf

open MeasureTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesIntegral Cochrane.Monetarism.TidyR7StieltjesSums
  Cochrane.Monetarism.TidyR7ProductStep Cochrane.Monetarism.TidyR7ProductStepCoin
  Cochrane.Monetarism.TidyR7MonetarismAC Cochrane.Monetarism.TidyR7MonetarismModel
  Cochrane.Monetarism.TidyR7MonetarismValuation Cochrane.Monetarism.TidyR7MonetarismCoin
  Cochrane.Monetarism.TidyR7MonetarismCoinInf

/-! ## The decaying discount factor -/

/-- Cochrane (2023), A1 §1.6, p. 567: `φ(u) = (e^{−1} − e^{−u})⁺`, zero before `1`. -/
noncomputable def decPhi (u : ℝ) : ℝ := max (Real.exp (-1) - Real.exp (-u)) 0

/-- Cochrane (2023), A1 §1.6, p. 567: `Λ_u = n_u = e^{−u}(1 + (ξ/2)H(u))` (`P = 1`). -/
noncomputable def decLam (u : ℝ) (ω : Bool) : ℝ := Real.exp (-u) * (1 + coinXi ω / 2 * heaviside u)

/-- Cochrane (2023), A1 §1.6, p. 567: the finite-variation part `A_u = e^{−u} − (ξ/2)φ(u)`. -/
noncomputable def decA (u : ℝ) (ω : Bool) : ℝ := Real.exp (-u) - coinXi ω / 2 * decPhi u

/-- Cochrane (2023), A1 §1.6, p. 567: the martingale part `N_u = (ξ/2)e^{−1}H(u)`. -/
noncomputable def decN (u : ℝ) (ω : Bool) : ℝ := coinXi ω / 2 * Real.exp (-1) * heaviside u

/-- Cochrane (2023), A1 §1.6, p. 567: the nominal rate `i = 1`. -/
def decOne (_ : ℝ) (_ : Bool) : ℝ := 1

/-- Cochrane (2023), A1 §1.6, p. 567: the interest on money `i^m = 1/2`. -/
noncomputable def decHalf (_ : ℝ) (_ : Bool) : ℝ := 1 / 2

/-- Cochrane (2023), A1 §1.6, p. 567: bonds and money, both `= 2`. -/
def decTwo (_ : ℝ) (_ : Bool) : ℝ := 2

/-- Cochrane (2023), A1 §1.6, p. 567: the surplus `s = 3`. -/
def decThree (_ : ℝ) (_ : Bool) : ℝ := 3

/-- Cochrane (2023), A1 §1.6, p. 567: `φ` is continuous. -/
theorem continuous_decPhi : Continuous decPhi :=
  (continuous_const.sub continuous_expNeg).max continuous_const

/-- Cochrane (2023), A1 §1.6, p. 567: `φ(u) = 0` for `u < 1`. -/
theorem decPhi_of_lt {u : ℝ} (hu : u < 1) : decPhi u = 0 :=
  max_eq_right (by linarith [Real.exp_lt_exp.2 (by linarith : -1 < -u)])

/-- Cochrane (2023), A1 §1.6, p. 567: `φ(u) = e^{−1} − e^{−u}` for `u ≥ 1`. -/
theorem decPhi_of_ge {u : ℝ} (hu : 1 ≤ u) : decPhi u = Real.exp (-1) - Real.exp (-u) :=
  max_eq_left (by linarith [Real.exp_le_exp.2 (by linarith : -u ≤ -1)])

/-- **Cochrane (2023), A1 §1.6, p. 567 (tool): `∫_u^v H(r)e^{−r} dr = φ(v) − φ(u)`** for `u ≤ v`
(the right derivative of `φ` is `H e^{−·}`).
Generalises `TidyR7MonetarismCoinInf.integral_heaviside_expNeg`. -/
theorem integral_heaviside_expNeg_gen {u v : ℝ} (huv : u ≤ v) :
    ∫ r in u..v, heaviside r * Real.exp (-r) = decPhi v - decPhi u := by
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le huv
    continuous_decPhi.continuousOn (fun x _ => ?_)
    (intervalIntegrable_mul_of_isCadlag isCadlag_heaviside huv
      (continuous_expNeg.intervalIntegrable u v))
  rcases lt_or_ge x 1 with hx | hx
  · have hH : heaviside x * Real.exp (-x) = 0 := by simp [heaviside, not_le.2 hx]
    rw [hH]
    refine ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_).hasDerivWithinAt
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact decPhi_of_lt hy
  · have hH : heaviside x * Real.exp (-x) = Real.exp (-x) := by simp [heaviside, hx]
    rw [hH]
    have hd : HasDerivAt (fun y => Real.exp (-1) - Real.exp (-y)) (Real.exp (-x)) x := by
      have := (hasDerivAt_expNeg x).const_sub (Real.exp (-1))
      simpa using this
    exact hd.hasDerivWithinAt.congr (fun y hy => decPhi_of_ge (hx.trans (le_of_lt hy)))
      (decPhi_of_ge hx)

/-- Cochrane (2023), A1 §1.6, p. 567: `|(ξ/2)H| ≤ 1/2`. -/
theorem abs_half_xi_le (u : ℝ) (ω : Bool) : |coinXi ω / 2 * heaviside u| ≤ 1 / 2 := by
  rw [abs_mul, abs_div, abs_coinXi]
  simp only [heaviside]
  split_ifs <;> norm_num

/-- Cochrane (2023), A1 §1.6, p. 567: `Λ = n > 0`. -/
theorem decLam_pos (u : ℝ) (ω : Bool) : 0 < decLam u ω := by
  have h1 := abs_half_xi_le u ω
  have h2 : 0 < 1 + coinXi ω / 2 * heaviside u := by
    linarith [neg_abs_le (coinXi ω / 2 * heaviside u)]
  exact mul_pos (Real.exp_pos _) h2

/-- Cochrane (2023), A1 §1.6, p. 567: `Λ/P = Λ` (`P = 1`). -/
theorem disc_dec (u : ℝ) (ω : Bool) : disc decLam coinP u ω = decLam u ω := by
  simp [disc, coinP]

/-- Cochrane (2023), A1 §1.6, p. 567: `n_u = e^{−u} + (ξ/2)(H(u)e^{−u})`. -/
theorem decLam_eq (u : ℝ) (ω : Bool) :
    decLam u ω = Real.exp (-u) + coinXi ω / 2 * (heaviside u * Real.exp (-u)) := by
  simp only [decLam]
  ring

/-- Cochrane (2023), A1 §1.6, p. 567: `n = A + N`. -/
theorem decLam_split (u : ℝ) (ω : Bool) : decLam u ω = decA u ω + decN u ω := by
  rcases lt_or_ge u 1 with hu | hu
  · simp only [decLam, decA, decN, decPhi_of_lt hu, heaviside, not_le.2 hu, ↓reduceIte]
    ring
  · simp only [decLam, decA, decN, decPhi_of_ge hu, heaviside, hu, ↓reduceIte]
    ring

/-- Cochrane (2023), A1 §1.6, p. 567: the paths of `n` are interval integrable. -/
theorem intervalIntegrable_decLam (ω : Bool) (u v : ℝ) :
    IntervalIntegrable (fun r => decLam r ω) MeasureSpace.volume u v := by
  have key : ∀ a b : ℝ, a ≤ b →
      IntervalIntegrable (fun r => decLam r ω) MeasureSpace.volume a b := by
    intro a b hab
    have e : (fun r => decLam r ω) =
        fun r => Real.exp (-r) + coinXi ω / 2 * (heaviside r * Real.exp (-r)) :=
      funext fun r => decLam_eq r ω
    rw [e]
    exact (continuous_expNeg.intervalIntegrable a b).add
      ((intervalIntegrable_mul_of_isCadlag isCadlag_heaviside hab
        (continuous_expNeg.intervalIntegrable a b)).const_mul _)
  rcases le_total u v with h | h
  · exact key u v h
  · exact (key v u h).symm

/-- **Cochrane (2023), A1 §1.6, p. 567: `∫_u^v n_r dr = (e^{−u} − e^{−v}) + (ξ/2)(φ(v) − φ(u))`**
for `u ≤ v`. -/
theorem integral_decLam (ω : Bool) {u v : ℝ} (huv : u ≤ v) :
    ∫ r in u..v, decLam r ω =
      (Real.exp (-u) - Real.exp (-v)) + coinXi ω / 2 * (decPhi v - decPhi u) := by
  have e : (fun r => decLam r ω) =
      fun r => Real.exp (-r) + coinXi ω / 2 * (heaviside r * Real.exp (-r)) :=
    funext fun r => decLam_eq r ω
  rw [e, intervalIntegral.integral_add (continuous_expNeg.intervalIntegrable u v)
    ((intervalIntegrable_mul_of_isCadlag isCadlag_heaviside huv
      (continuous_expNeg.intervalIntegrable u v)).const_mul _),
    intervalIntegral.integral_const_mul, integral_expNeg, integral_heaviside_expNeg_gen huv]

/-- Cochrane (2023), A1 §1.6, p. 567: with `i = 1`, the bond-pricing density is `−i n = −n`. -/
theorem rate_dec (ω : Bool) :
    (fun r => -(decOne r ω * disc decLam coinP r ω)) = fun r => -decLam r ω :=
  funext fun r => by rw [disc_dec, decOne, one_mul]

/-- Cochrane (2023), A1 §1.6, p. 567: `A` has increments `−∫ i n`, the bond-pricing condition
`E_t d(Λ/P) = −i(Λ/P) dt` with `i = 1`. -/
theorem decA_incr : IncrOf decA fun r ω => -(decOne r ω * disc decLam coinP r ω) := by
  intro ω u v huv
  rw [rate_dec ω, intervalIntegral.integral_neg, integral_decLam ω huv]
  simp only [decA]
  ring

/-- Cochrane (2023), A1 §1.6, p. 567: `−i n` is locally integrable. -/
theorem decA_int : LocInt fun r ω => -(decOne r ω * disc decLam coinP r ω) := by
  intro ω u v
  rw [rate_dec ω]
  exact (intervalIntegrable_decLam ω u v).neg

/-- Cochrane (2023), A1 §1.6, p. 567: `N = (e^{−1}/2)·ξH` is a martingale
(`TidyR7ProductStepCoin.martingale_coinM`). -/
theorem martingale_decN : Martingale decN coinFiltration coinMeasure := by
  have e : decN = (Real.exp (-1) / 2) • coinM := funext fun u => funext fun ω => by
    simp only [decN, coinM, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e]
  exact martingale_coinM.smul _

/-- Cochrane (2023), A1 §1.6, p. 567: `N` has càdlàg paths. -/
theorem decN_cadlag (ω : Bool) : IsCadlag fun u => decN u ω :=
  isCadlag_heaviside.continuous_comp (continuous_const.mul continuous_id
    (f := fun _ : ℝ => coinXi ω / 2 * Real.exp (-1)))

/-- Cochrane (2023), A1 §1.6, p. 567: `n` is non-random before time `1`, hence adapted. -/
theorem decLam_adapted (u : ℝ) : StronglyMeasurable[coinFiltration u] (decLam u) :=
  coin_adapted (fun u hu ω => by simp [decLam, heaviside, not_le.2 hu]) u

/-- Cochrane (2023), A1 §1.6, p. 567: the martingale part of `n` is not zero. -/
theorem decN_ne_zero : decN 1 true ≠ 0 := by
  simp [decN, coinXi, heaviside, Real.exp_ne_zero]

/-! ## The economy with money -/

/-- Cochrane (2023), A1 §1.6, (1.31), p. 567: the flow density `iB + i^mM − Ps = 2 + 1 − 3 = 0`.
-/
theorem flowRate_money (ω : Bool) :
    (fun r => flowRate decTwo decTwo coinP decOne decHalf decThree r ω) = fun _ => 0 :=
  funext fun r => by simp only [flowRate, decTwo, decOne, decHalf, coinP, decThree]; norm_num

/-- **Cochrane (2023), A1 §1.6, (1.31)–(1.34), pp. 567–568: an infinite-horizon model with
nonzero money, interest on money and news in `Λ/P`** satisfying
`TidyR7MonetarismModel.MonetaryModel`: `P = 1`, `Λ = e^{−u}(1 + (ξ/2)H)`, `i = 1`,
`i^m = 1/2`, `B = M = 2`, `s = 3`. -/
theorem moneyInfModel : MonetaryModel coinMeasure coinFiltration decLam coinP decTwo decTwo decA
    decN decOne decHalf decThree where
  P_pos _ _ := one_pos
  Λ_pos := decLam_pos
  Λ_adapted := decLam_adapted
  P_adapted _ := stronglyMeasurable_const
  dec u ω := by rw [disc_dec]; exact decLam_split u ω
  A_incr := decA_incr
  A_int := decA_int
  N_mart := martingale_decN
  N_cadlag := decN_cadlag
  B_adapted _ := stronglyMeasurable_const
  M_adapted _ := stronglyMeasurable_const
  M_cont _ := continuous_const
  M_bv _ a b := by
    rw [BoundedVariationOn, eVariationOn.constant_on
      (Set.subsingleton_of_forall_eq (2 : ℝ) fun _ ⟨_, _, hy⟩ => hy.symm)]
    exact ENNReal.zero_ne_top
  flow ω u v _ := by
    rw [flowRate_money ω, intervalIntegral.integral_zero]
    simp only [addProc, decTwo]
    ring
  flow_int ω u v := by
    rw [flowRate_money ω]
    exact intervalIntegrable_const

/-- Cochrane (2023), A1 §1.6, p. 567: money, interest on money and the seigniorage term
`(i − i^m)M/P = 1` are all nonzero, and `i^m < i`. -/
theorem moneyInf_nonzero (u : ℝ) (ω : Bool) :
    decTwo u ω ≠ 0 ∧ decHalf u ω ≠ 0 ∧ decHalf u ω < decOne u ω ∧
      (decOne u ω - decHalf u ω) * decTwo u ω / coinP u ω = 1 := by
  simp only [decTwo, decHalf, decOne, coinP]
  norm_num

/-- Cochrane (2023), A1 §1.6, p. 567: the domination conditions for `B + M` hold on every
interval (finite `Ω`). -/
theorem moneyInfDom (s t : ℝ) :
    Dominated coinMeasure decA decN s t (addProc decTwo decTwo) (disc decLam coinP) :=
  ⟨Integrable.of_finite, Integrable.of_finite, fun _ _ _ _ _ => Integrable.of_finite⟩

/-! ## Both sides of (1.34) -/

/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567: the flow on `moneyInfModel`.** For `T ≥ 1`,
`∫_0^T (Λs + (i − i^m)nM) dr = ∫_0^T 4Λ = 4(1 − e^{−T}) + 2ξ(e^{−1} − e^{−T})`. -/
theorem moneyInf_flow134 {T : ℝ} (hT : 1 ≤ T) (ω : Bool) :
    flow134 decLam coinP decTwo decOne decHalf decThree 0 T ω =
      4 * (1 - Real.exp (-T)) + 2 * coinXi ω * (Real.exp (-1) - Real.exp (-T)) := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have e : (fun r => decLam r ω * decThree r ω + (decOne r ω - decHalf r ω) *
      disc decLam coinP r ω * decTwo r ω) = fun r => 4 * decLam r ω :=
    funext fun r => by
      rw [disc_dec]
      simp only [decThree, decOne, decHalf, decTwo]
      ring
  rw [flow134, e, intervalIntegral.integral_const_mul, integral_decLam ω hT0,
    decPhi_of_ge hT, decPhi_of_lt (by norm_num : (0 : ℝ) < 1)]
  simp only [neg_zero, Real.exp_zero]
  ring

/-- Cochrane (2023), A1 §1.6, (1.34), p. 567: the limit `G = 4 + 2ξe^{−1}` of the flows. -/
noncomputable def moneyInfG (ω : Bool) : ℝ := 4 + 2 * coinXi ω * Real.exp (-1)

/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567: the flows converge path by path to `G`.** -/
theorem moneyInf_tendsto (ω : Bool) :
    Tendsto (fun T => flow134 decLam coinP decTwo decOne decHalf decThree 0 T ω) atTop
      (𝓝 (moneyInfG ω)) := by
  have he := Real.tendsto_exp_neg_atTop_nhds_zero
  have h : Tendsto (fun T : ℝ => 4 * (1 - Real.exp (-T)) +
      2 * coinXi ω * (Real.exp (-1) - Real.exp (-T))) atTop
      (𝓝 (4 * (1 - 0) + 2 * coinXi ω * (Real.exp (-1) - 0))) :=
    (tendsto_const_nhds.mul (tendsto_const_nhds.sub he)).add
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub he))
  have e : 4 * (1 - 0) + 2 * coinXi ω * (Real.exp (-1) - 0) = moneyInfG ω := by
    simp only [moneyInfG]; ring
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  rw [moneyInf_flow134 hT]

/-- Cochrane (2023), A1 §1.6, (1.34), p. 567: `|F_T| ≤ 6` for `T ≥ 1`. -/
theorem abs_moneyInf_flow134_le {T : ℝ} (hT : 1 ≤ T) (ω : Bool) :
    |flow134 decLam coinP decTwo decOne decHalf decThree 0 T ω| ≤ 6 := by
  rw [moneyInf_flow134 hT]
  have h1 := expNeg_le_one (by linarith : (0 : ℝ) ≤ T)
  have h2 := Real.exp_pos (-T)
  have h3 := Real.exp_le_exp.2 (by linarith : -T ≤ -1)
  have h4 := expNeg_le_one (by norm_num : (0 : ℝ) ≤ 1)
  have hb : |2 * coinXi ω * (Real.exp (-1) - Real.exp (-T))| ≤ 2 := by
    rw [abs_mul, abs_mul, abs_coinXi, abs_of_nonneg (by linarith : 0 ≤ Real.exp (-1) -
      Real.exp (-T))]
    norm_num
    linarith
  rw [abs_le] at hb ⊢
  constructor <;> nlinarith [hb.1, hb.2]

/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567: the transversality condition holds:**
`E_0[n_T(B_T + M_T)] = 4e^{−T}` for `T ≥ 1`. -/
theorem moneyInf_tvc_eq {T : ℝ} (hT : 1 ≤ T) :
    coinMeasure[fun ω => disc decLam coinP T ω * addProc decTwo decTwo T ω | coinFiltration 0] =
      fun _ => 4 * Real.exp (-T) := by
  rw [condExp_coin_lt (by norm_num)]
  funext _
  simp only [disc_dec, decLam, addProc, decTwo, coinXi, heaviside, hT, ↓reduceIte,
    Bool.false_eq_true]
  ring

/-- Cochrane (2023), A1 §1.6, (1.34), p. 567: `4e^{−T} → 0`. -/
theorem tendsto_moneyInf_tvc : Tendsto (fun T : ℝ => 4 * Real.exp (-T)) atTop (𝓝 0) := by
  simpa using (Real.tendsto_exp_neg_atTop_nhds_zero).const_mul 4

/-- Cochrane (2023), A1 §1.6, (1.34), p. 567: `n_0(B_0 + M_0) = 4` (`Λ_0 = 1`). -/
theorem moneyInf_Y0 (ω : Bool) : disc decLam coinP 0 ω * addProc decTwo decTwo 0 ω = 4 := by
  simp [disc_dec, decLam, addProc, decTwo, heaviside]
  norm_num

/-- Cochrane (2023), A1 §1.6, (1.34), p. 567: `E_0[G] = 4`. -/
theorem moneyInf_EG : coinMeasure[moneyInfG | coinFiltration 0] = fun _ => 4 := by
  rw [condExp_coin_lt (by norm_num)]
  funext _
  simp only [moneyInfG, coinXi]
  norm_num
  ring

/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567, as printed, on `[0, ∞)` with nonzero money and
interest on money.** On `moneyInfModel` (`M = 2`, `i^m = 1/2`, `i = 1`), along `T_k = k + 1`:
the conclusion of `TidyR7MonetarismValuation.MonetaryModel.valuation_1_34_book` holds, both sides
are computed (`(M_0 + B_0)/P_0 = 4` and `E_0[G/Λ_0] = 4`), the transversality condition holds,
so the printed (1.34)
`(M_0 + B_0)/P_0 = E_0∫_0^∞ (Λ_τ/Λ_0)(s_τ + (i_τ − i^m_τ)M_τ/P_τ) dτ` holds. -/
theorem moneyInf_1_34_book :
    ((∀ ω, Tendsto (fun k : ℕ => ∫ r in (0 : ℝ)..((k : ℝ) + 1),
        decLam r ω / decLam 0 ω * (decThree r ω + (decOne r ω - decHalf r ω) * decTwo r ω /
          coinP r ω)) atTop (𝓝 (moneyInfG ω / decLam 0 ω))) ∧
      ((fun ω => addProc decTwo decTwo 0 ω / coinP 0 ω) =ᵐ[coinMeasure]
          coinMeasure[fun ω => moneyInfG ω / decLam 0 ω | coinFiltration 0] ↔
        ∀ᵐ ω ∂coinMeasure, Tendsto (fun k : ℕ => coinMeasure[fun ω =>
          disc decLam coinP ((k : ℝ) + 1) ω * addProc decTwo decTwo ((k : ℝ) + 1) ω |
            coinFiltration 0] ω) atTop (𝓝 0))) ∧
      (fun ω => addProc decTwo decTwo 0 ω / coinP 0 ω) = (fun _ => 4) ∧
      coinMeasure[fun ω => moneyInfG ω / decLam 0 ω | coinFiltration 0] = (fun _ => 4) ∧
      (∀ ω, Tendsto (fun k : ℕ => coinMeasure[fun ω =>
          disc decLam coinP ((k : ℝ) + 1) ω * addProc decTwo decTwo ((k : ℝ) + 1) ω |
            coinFiltration 0] ω) atTop (𝓝 0)) ∧
      (fun ω => addProc decTwo decTwo 0 ω / coinP 0 ω) =ᵐ[coinMeasure]
          coinMeasure[fun ω => moneyInfG ω / decLam 0 ω | coinFiltration 0] := by
  have hT : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k => by
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hseq : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hbook := MonetaryModel.valuation_1_34_book moneyInfModel (s := 0)
    (fun s t _ => moneyInfDom s t) (fun _ => Integrable.of_finite)
    (T := fun k : ℕ => (k : ℝ) + 1) (fun k => by linarith [hT k]) (H := fun _ => 6)
    (integrable_const _) (fun k ω => abs_moneyInf_flow134_le (hT k) ω)
    (fun ω => (moneyInf_tendsto ω).comp hseq) (G := moneyInfG) Integrable.of_finite
  have hL0 : ∀ ω, decLam 0 ω = 1 := fun ω => by simp [decLam, heaviside]
  have htvc : ∀ ω, Tendsto (fun k : ℕ => coinMeasure[fun ω =>
      disc decLam coinP ((k : ℝ) + 1) ω * addProc decTwo decTwo ((k : ℝ) + 1) ω |
        coinFiltration 0] ω) atTop (𝓝 0) := fun ω => by
    refine (tendsto_moneyInf_tvc.comp hseq).congr fun k => ?_
    rw [moneyInf_tvc_eq (hT k)]
    rfl
  have hl : (fun ω => addProc decTwo decTwo 0 ω / coinP 0 ω) = (fun _ => 4) := by
    funext _
    simp only [addProc, decTwo, coinP]
    norm_num
  have hr : coinMeasure[fun ω => moneyInfG ω / decLam 0 ω | coinFiltration 0] = (fun _ => 4) := by
    simp_rw [hL0, div_one]
    exact moneyInf_EG
  exact ⟨hbook, hl, hr, htvc, hbook.2.2 (Eventually.of_forall htvc)⟩

/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567, `L¹` form, on `[0, ∞)` with nonzero money.** On
`moneyInfModel` the flows converge in `L¹` to `G`, `MonetaryModel.valuation_1_34` applies, and
both of its sides hold: `n_0(B_0 + M_0) = E_0[G]` (both `4`) and
`∫|E_0[n_T(B_T + M_T)]| → 0`. -/
theorem moneyInf_1_34_L1 :
    Tendsto (fun T => ∫ ω, |flow134 decLam coinP decTwo decOne decHalf decThree 0 T ω -
        moneyInfG ω| ∂coinMeasure) atTop (𝓝 0) ∧
      (fun ω => disc decLam coinP 0 ω * addProc decTwo decTwo 0 ω) =ᵐ[coinMeasure]
          coinMeasure[moneyInfG | coinFiltration 0] ∧
      Tendsto (fun T => ∫ ω, |coinMeasure[fun ω => disc decLam coinP T ω *
          addProc decTwo decTwo T ω | coinFiltration 0] ω| ∂coinMeasure) atTop (𝓝 0) := by
  have hconv : Tendsto (fun T => ∫ ω, |flow134 decLam coinP decTwo decOne decHalf decThree 0 T ω
      - moneyInfG ω| ∂coinMeasure) atTop (𝓝 0) := by
    simp only [integral_coin]
    have h1 := ((moneyInf_tendsto true).sub_const (moneyInfG true)).abs
    have h2 := ((moneyInf_tendsto false).sub_const (moneyInfG false)).abs
    have := (h1.add h2).div_const 2
    simpa using this
  have hval := MonetaryModel.valuation_1_34 moneyInfModel (s := 0)
    (fun s t _ => moneyInfDom s t) (fun _ => Integrable.of_finite) (G := moneyInfG)
    Integrable.of_finite hconv
  have hlhs : (fun ω => disc decLam coinP 0 ω * addProc decTwo decTwo 0 ω) =ᵐ[coinMeasure]
      coinMeasure[moneyInfG | coinFiltration 0] := by
    rw [moneyInf_EG]
    exact Eventually.of_forall fun ω => moneyInf_Y0 ω
  exact ⟨hconv, hlhs, hval.1 hlhs⟩

end Cochrane.Monetarism.TidyR8MonetarismMoneyInf
