/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.BridgeCore
import StabilizationWelfare.BridgeExtensions
import StabilizationWelfare.ExpectationsFiniteTree
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Linking the Layer-B bridges to the primitives

Woodford (2003), *Interest and Prices*, Chapter 6, §2.2 (pp. 399–405), §4.1 (pp. 420–426),
§4.3–4.4 (pp. 435–448) and Appendix E.2–E.4, E.6–E.8 (pp. 695–708).

The Layer-B modules `BridgeCore` and `BridgeExtensions` left some ingredients as hypotheses.
This module discharges those that are mechanical consequences of results proved elsewhere.

## Main results

* The finite weighted cross-section as a goods population: `wMeasure` (the probability measure
  `∑ wᵢ δᵢ`), `crossMean_wMeasure`, `crossVar_wMeasure`, `goods_rec_fin` (the Calvo dispersion
  law (2.20)/(2.24) for a finite cross-section following the Calvo rule `Links.GoodsPop.Calvo`),
  `disp_hasSum_fin` (its discounted form).
* Proposition 6.3 as a UNIFORM family bound: `logP` (log of the Dixit–Stiglitz price index),
  `logP_const_add`, `logP_sub_mean_o`, `disc_o` (`π̄ − π = O(s²)` along ANY filter, in particular
  uniformly in the date and the state), `cen`, `cen_o`, `cen_demand` (relative prices from
  relative outputs by (2.12)), `disc_prod`, `cen_all_prod`, `cen_all_state`.
* Propositions 6.4–6.5 from the Calvo goods population: `prop64_goods`, `prop65_goods` (the
  hypotheses `var_i ŷ = θ²Δ`, the dispersion recursion and its `O(ε³)` remainder of
  `BridgeCore.Econ.prop64_bridge`/`prop65_bridge` discharged).
* The money-demand residual of Proposition 6.7 from the first-order condition `u_m = Δu_c`:
  `taylor1_family`, `exp_sub_one_sub_o`, `money_residual_o`.
* The discounted Propositions 6.8, 6.11, 6.13 from the primitives: `prop68_primitive`,
  `prop611_primitive`, `prop613_primitive` (the per-period expansion `hP` of
  `BridgeExtensions.prop68_layerB`/`prop611_layerB`/`prop613_layerB` is the corresponding
  `_actual` theorem on the filter `l ×ˢ ⊤`; `V_p`, `V_w` are identified with the Calvo price and
  wage dispersions by (2.12)); bounded t.i.p.: `bdd_quad_terms`, `bdd_tipT`, `bdd_tip2`,
  `bdd_tip12`; `logY2_o`.
* Propositions 6.14–6.15: `goods_state_package`, `prop614_goods_layerB`, `prop615_goods_layerB`
  (dispersion hypotheses `hV`, `hD`, `hDO`, `hpO` discharged from the goods population).
* Proposition 6.6 under genuine uncertainty: `Habit.prop66_bridge_rx` (pathwise, the realised
  residual `r_tx_t` kept), `Habit.prop66_expected` (any `ExpectationSystem` with pull-out on a
  finite state space, `E_t r_t = 0`), `Habit.prop66_finiteTree`.
-/

namespace Woodford.StabilizationWelfare.BridgeLinks

open Filter Topology Asymptotics MeasureTheory
open ExpLogCES (crossMean crossVar)

variable {ι : Type*} [Fintype ι]

/-! ## The finite cross-section as a goods population -/

/-- Woodford (2003), App. E.2, p. 695: the finite weighted cross-section of goods as the
probability measure `∑ wᵢ δᵢ` on the goods, so that `Links.GoodsPop.Calvo` (the Calvo reset
rule on a population of goods) applies to it. -/
noncomputable def wMeasure [MeasurableSpace ι] (w : ι → ℝ) : Measure ι :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac i

/-- Woodford (2003), App. E.2, p. 695: integrals against `wMeasure` are weighted sums. -/
theorem integral_wMeasure [MeasurableSpace ι] [MeasurableSingletonClass ι] {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (f : ι → ℝ) : ∫ i, f i ∂(wMeasure w) = ∑ i, w i * f i := by
  unfold wMeasure
  rw [integral_finsetSum_measure fun i _ =>
    (Integrable.of_finite (μ := Measure.dirac i)).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw i), smul_eq_mul]

/-- Woodford (2003), App. E.2, p. 695: `wMeasure` is a probability measure for probability
weights. -/
theorem isProbabilityMeasure_wMeasure [MeasurableSpace ι] {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) : IsProbabilityMeasure (wMeasure w) := by
  constructor
  unfold wMeasure
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hw i, hw1, ENNReal.ofReal_one]

/-- Woodford (2003), p. 694: the population mean over `wMeasure` is the weighted mean. -/
theorem crossMean_wMeasure [MeasurableSpace ι] [MeasurableSingletonClass ι] {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (x : ι → ℝ) : CrossSection.crossMean (wMeasure w) x = crossMean w x := by
  unfold CrossSection.crossMean
  rw [integral_wMeasure hw]
  rfl

/-- Woodford (2003), p. 694: the population variance over `wMeasure` is the weighted variance. -/
theorem crossVar_wMeasure [MeasurableSpace ι] [MeasurableSingletonClass ι] {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (x : ι → ℝ) : CrossSection.crossVar (wMeasure w) x = crossVar w x := by
  unfold CrossSection.crossVar
  rw [integral_wMeasure hw, crossMean_wMeasure hw]
  rfl

/-- Woodford (2003), (2.20)/(2.24) and (E.8), pp. 399–402, 695 (**the Calvo dispersion law for a
finite cross-section**): if the goods of the finite weighted cross-section follow the Calvo
reset rule with indexation increment `d` (`Links.GoodsPop.Calvo` on `wMeasure w`), then
`Δ_t = αΔ_{t−1} + α/(1 − α)(P̄_t − P̄_{t−1} − d_t)²` exactly, with `Δ = var_i log p`,
`P̄ = E_i log p` (from `Links.goods_disp_rec`). -/
theorem goods_rec_fin [MeasurableSpace ι] [MeasurableSingletonClass ι] {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {α : ℝ} (hα : α ≠ 1) {X : ℕ → ι → ℝ}
    {R : ℕ → Set ι} {ps d : ℕ → ℝ} (hG : Links.GoodsPop.Calvo (wMeasure w) α X R ps d)
    (t : ℕ) :
    crossVar w (X (t + 1)) = α * crossVar w (X t) +
      α / (1 - α) * (crossMean w (X (t + 1)) - crossMean w (X t) - d t) ^ 2 := by
  have := isProbabilityMeasure_wMeasure hw hw1
  have h := Links.goods_disp_rec (wMeasure w) hG hα t
  simpa only [crossVar_wMeasure hw, crossMean_wMeasure hw] using h

/-! ## Proposition 6.3 as a uniform family bound -/

/-- Woodford (2003), eq. (2.2), p. 392: the log of the Dixit–Stiglitz price index
`log P = (1 − θ)⁻¹ log E_i p(i)^{1−θ}` of the log prices `q`. -/
noncomputable def logP (w : ι → ℝ) (θ : ℝ) (q : ι → ℝ) : ℝ :=
  Real.log (ExpLogCES.cesIndex w (1 - θ) (fun i => Real.exp (q i)))

/-- Woodford (2003), App. E.2, p. 695: raising every log price by `c` raises `log P` by `c`. -/
theorem logP_const_add {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {θ : ℝ}
    (hθ : θ ≠ 1) (c : ℝ) (q : ι → ℝ) : logP w θ (fun i => c + q i) = c + logP w θ q := by
  have hr : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  unfold logP
  rw [ExpLogCES.log_cesIndex_exp hw hw1 _ q, ← ExpLogCES.cumulant_const_add hw hw1 hr c q,
    ← ExpLogCES.log_cesIndex_exp hw hw1 _ (fun i => c + q i)]

/-- Woodford (2003), App. E.2, p. 695: the relative log prices `q(i) − E_i q`. -/
noncomputable def cen (w : ι → ℝ) (q : ι → ℝ) : ι → ℝ := fun i => q i - crossMean w q

/-- Woodford (2003), App. E.2, p. 695: relative prices have mean zero. -/
theorem crossMean_cen {w : ι → ℝ} (hw1 : ∑ i, w i = 1) (q : ι → ℝ) : crossMean w (cen w q) = 0 := by
  unfold cen crossMean
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
  exact sub_self _

variable {B : Type*} {L : Filter B} {s : B → ℝ}

/-- Woodford (2003), Prop. 6.3 and App. E.2, p. 695 (**`log P − P̄ = O(Δ)` along any family**):
if the relative log prices are `O(s)` along a filter `L` with `s → 0`, then
`log P − E_i log p = O(s²)` along `L` (from `ExpLogCES.log_priceIndex_sub_mean_isBigO` and the
invariance of `log P − P̄` to a common shift). Taking `L = l ×ˢ ⊤` makes the bound uniform in the
date. -/
theorem logP_sub_mean_o (hs : Tendsto s L (𝓝 0)) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {θ : ℝ} (hθ : θ ≠ 1) {q : B → ι → ℝ}
    (hq : (fun b => cen w (q b)) =O[L] fun b => s b ^ 1) :
    (fun b => logP w θ (q b) - crossMean w (q b)) =O[L] fun b => s b ^ 2 := by
  have h := ExpLogCES.log_priceIndex_sub_mean_isBigO hw hw1 hθ 0
  have ht : Tendsto (fun b => cen w (q b)) L (𝓝 fun _ => (0 : ℝ)) :=
    hq.trans_tendsto (by simpa using hs)
  have h2 := h.comp_tendsto ht
  have h3 : (fun b => ‖cen w (q b) - fun _ => (0 : ℝ)‖ ^ 2) =O[L] fun b => s b ^ 2 := by
    have h4 : (fun b => ‖cen w (q b)‖ ^ 2) =O[L] fun b => s b ^ 2 :=
      (hq.norm_left.pow 2).congr_right fun b => by ring
    refine h4.congr_left fun b => ?_
    congr 2
    funext i
    simp
  refine (h2.trans h3).congr_left fun b => ?_
  simp only [Function.comp_apply]
  have e : q b = fun i => crossMean w (q b) + cen w (q b) i := by
    funext i; unfold cen; ring
  have e2 : logP w θ (q b) = crossMean w (q b) + logP w θ (cen w (q b)) := by
    conv_lhs => rw [e]
    exact logP_const_add hw hw1 hθ _ _
  rw [e2, crossMean_cen hw1]
  unfold logP
  ring

/-- Woodford (2003), **Proposition 6.3**, App. E.2 and (5.2)–(5.3), pp. 399, 456, 695 (**the
inflation discrepancy as a UNIFORM family bound**): with relative prices `O(s)` at both dates,
`e = (P̄_t − P̄_{t−1}) − (log P_t − log P_{t−1}) = O(s²)` along `L`. -/
theorem disc_o (hs : Tendsto s L (𝓝 0)) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {θ : ℝ} (hθ : θ ≠ 1) {qn qo : B → ι → ℝ}
    (hn : (fun b => cen w (qn b)) =O[L] fun b => s b ^ 1)
    (ho : (fun b => cen w (qo b)) =O[L] fun b => s b ^ 1) :
    (fun b => (crossMean w (qn b) - crossMean w (qo b)) - (logP w θ (qn b) - logP w θ (qo b)))
      =O[L] fun b => s b ^ 2 :=
  ((logP_sub_mean_o hs hw hw1 hθ ho).sub (logP_sub_mean_o hs hw hw1 hθ hn)).congr_left
    fun b => by ring

/-- Woodford (2003), App. E.2, p. 695: relative outputs of order `s` have relative values of
order `s`. -/
theorem cen_o {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {y : B → ι → ℝ}
    (hy : y =O[L] fun b => s b ^ 1) : (fun b => cen w (y b)) =O[L] fun b => s b ^ 1 := by
  have hm := BridgeExtensions.crossMean_o hw hw1 hy
  have hc : (fun b => fun _ : ι => crossMean w (y b)) =O[L] fun b => s b ^ 1 := by
    refine (IsBigO.of_bound 1 (Eventually.of_forall fun b => ?_)).trans hm
    rw [one_mul]
    exact pi_norm_const_le _
  exact (hy.sub hc).congr_left fun b => by funext i; rfl

/-- Woodford (2003), eq. (2.12), p. 396 (relative demand): with
`ŷ(i) = Ŷ − θ(log p(i) − log P)`, relative prices are `−θ⁻¹` times relative outputs. -/
theorem cen_demand {w : ι → ℝ} (hw1 : ∑ i, w i = 1) {θ : ℝ} (hθ : θ ≠ 0) {y p : ι → ℝ}
    {Y P : ℝ} (hd : ∀ i, y i = Y - θ * (p i - P)) : cen w p = (-θ⁻¹) • cen w y := by
  have hm : crossMean w y = Y - θ * (crossMean w p - P) := by
    have e : y = fun i => (Y + θ * P) + (-θ) * p i := by
      funext i; rw [hd i]; ring
    rw [e, Moments.crossMean_affine hw1]
    ring
  funext i
  simp only [cen, Pi.smul_apply, smul_eq_mul, hd i, hm]
  field_simp
  ring

/-! ## Propositions 6.4–6.5 from the Calvo goods population -/

open BridgeCore (unif tendsto_unif)

/-- Woodford (2003), App. E.2, p. 695 (survey error 25): relative prices of order `ε` uniformly
at every date `t ≥ 0` and at the initial date `−1` are of order `ε` uniformly at every index
(index `0` is date `−1`). -/
theorem cen_unif_all {w : ι → ℝ} {X : ℝ → ℕ → ι → ℝ}
    (hn : (fun p : ℕ × ℝ => cen w (X p.2 (p.1 + 1))) =O[unif] fun p => p.2 ^ 1)
    (h0 : (fun ε => cen w (X ε 0)) =O[𝓝 0] fun ε => ε ^ 1) :
    (fun p : ℕ × ℝ => cen w (X p.2 p.1)) =O[unif] fun p => p.2 ^ 1 := by
  obtain ⟨C1, h1⟩ := (BridgeCore.isBigO_unif_iff (f := fun t ε => cen w (X ε (t + 1)))
    (g := fun ε => ε ^ 1)).1 hn
  obtain ⟨C2, h2⟩ := h0.bound
  refine (BridgeCore.isBigO_unif_iff (f := fun t ε => cen w (X ε t))
    (g := fun ε => ε ^ 1)).2 ⟨max C1 C2, ?_⟩
  filter_upwards [h1, h2] with ε e1 e2 t
  cases t with
  | zero => exact e2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  | succ t => exact (e1 t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

/-- Woodford (2003), (E.7), p. 695 (the remainder of the dispersion recursion): if `a = O(s)` and
`e = O(s²)` then `(a + e)² − a² = O(s³)`. -/
theorem sq_add_sub_o (hs : Tendsto s L (𝓝 0)) {a e : B → ℝ} (ha : a =O[L] fun b => s b ^ 1)
    (he : e =O[L] fun b => s b ^ 2) :
    (fun b => (a b + e b) ^ 2 - a b ^ 2) =O[L] fun b => s b ^ 3 :=
  (BridgeExtensions.o_mul he ((BridgeExtensions.o_weaken hs (by norm_num : 1 ≤ 2) he).add
    (ha.const_mul_left 2)) (by norm_num : 2 + 1 = 3)).congr_left fun b => by ring

variable {Ξ : Type*} [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]

/-- Woodford (2003), App. E.2, p. 695: along a family with first-order solution
`ŷ = εy₁ + O(ε²)` uniformly in `t` and Dixit–Stiglitz demand (2.12), relative prices at every date
are `O(ε)` uniformly (given the initial cross-section `log p_{−1}`). -/
theorem cen_of_family {M : BridgeCore.Econ Ξ ι} (hM : M.Std) (hθ : M.θ ≠ 0)
    {yh : ℕ → ℝ → ι → ℝ} {y1 : ℕ → ι → ℝ}
    (h : (fun p : ℕ × ℝ => yh p.1 p.2 - p.2 • y1 p.1) =O[unif] fun p => p.2 ^ 2)
    (hy1 : ∃ C, ∀ t, ‖y1 t‖ ≤ C) {X : ℝ → ℕ → ι → ℝ} {LY LP : ℕ → ℝ → ℝ}
    (hdem : ∀ t ε i, yh t ε i = LY t ε - M.θ * (X ε (t + 1) i - LP t ε))
    (hX0 : (fun ε => cen M.w (X ε 0)) =O[𝓝 0] fun ε => ε ^ 1) :
    (fun p : ℕ × ℝ => cen M.w (X p.2 (p.1 + 1))) =O[unif] (fun p => p.2 ^ 1) ∧
      (fun p : ℕ × ℝ => cen M.w (X p.2 p.1)) =O[unif] fun p => p.2 ^ 1 := by
  have hyu : (fun p : ℕ × ℝ => yh p.1 p.2) =O[unif] fun p => p.2 ^ 1 :=
    (BridgeCore.family_isBigO tendsto_unif h (BridgeCore.unif_of_bounded hy1)).congr_right
      fun p => (pow_one _).symm
  have hcn : (fun p : ℕ × ℝ => cen M.w (X p.2 (p.1 + 1))) =O[unif] fun p => p.2 ^ 1 :=
    ((cen_o hM.w_nonneg hM.w_sum hyu).const_smul_left (-M.θ⁻¹)).congr_left fun p =>
      (cen_demand hM.w_sum hθ (hdem p.1 p.2)).symm
  exact ⟨hcn, cen_unif_all hcn hX0⟩

/-- Woodford (2003), **Proposition 6.4, eqs. (2.21)–(2.22), p. 400, Layer B FROM THE CALVO GOODS
POPULATION**. `BridgeCore.Econ.prop64_bridge` with its hypotheses
* `var_i ŷ_t = θ²Δ_t` discharged by Dixit–Stiglitz demand (2.12) (`Moments.crossVar_demand`),
* the exact dispersion recursion discharged by the Calvo rule on the goods of the cross-section
  (`Links.GoodsPop.Calvo` on `wMeasure`, `goods_rec_fin`),
* its remainder `R_t = α/(1 − α)(π̄_t² − π_t²) = O(ε³)` uniformly in `t` discharged by the uniform
  Prop. 6.3 bound `π̄ − π = O(ε²)` (`disc_o`),
where `Δ_t = var_i log p_t(i)`, `π_t = log P_t − log P_{t−1}` is index inflation (`hinfl`) and the
initial relative prices are `O(ε)` (`hX0`). -/
theorem prop64_goods [MeasurableSpace ι] [MeasurableSingletonClass ι] {M : BridgeCore.Econ Ξ ι}
    (hM : M.Std) (heff : M.vy = M.uc) (hden : M.sig + M.omg ≠ 0) (hθ : M.θ ≠ 0)
    (hd : 1 + M.omg * M.θ ≠ 0) {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {yh : ℕ → ℝ → ι → ℝ} {y1 : ℕ → ι → ℝ} {ξ1 : ℕ → Ξ}
    (h : (fun p : ℕ × ℝ => yh p.1 p.2 - p.2 • y1 p.1) =O[unif] fun p => p.2 ^ 2)
    (hy1 : ∃ C, ∀ t, ‖y1 t‖ ≤ C) (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C) {X : ℝ → ℕ → ι → ℝ}
    {Rs : ℝ → ℕ → Set ι} {ps : ℝ → ℕ → ℝ} {LY LP : ℕ → ℝ → ℝ}
    (hG : ∀ ε, Links.GoodsPop.Calvo (wMeasure M.w) α (X ε) (Rs ε) (ps ε) fun _ => 0)
    (hdem : ∀ t ε i, yh t ε i = LY t ε - M.θ * (X ε (t + 1) i - LP t ε))
    (hX0 : (fun ε => cen M.w (X ε 0)) =O[𝓝 0] fun ε => ε ^ 1) {infl : ℝ → ℕ → ℝ}
    (hinfl : ∀ ε t, infl ε (t + 1) = logP M.w M.θ (X ε (t + 1)) - logP M.w M.θ (X ε t))
    {π1 : ℕ → ℝ} (hπ : (fun p : ℕ × ℝ => infl p.2 p.1 - p.2 * π1 p.1) =O[unif] fun p => p.2 ^ 2)
    (hπ1 : ∃ C, ∀ t, |π1 t| ≤ C) :
    (fun ε => ∑' t, β ^ t * M.Ustate (yh t ε) (ε • ξ1 t) -
      ((∑' t, β ^ t * M.tipState (ε • ξ1 t) - M.Yb * M.uc *
          (M.θ * (1 + M.omg * M.θ) / 2 * (α * crossVar M.w (X ε 0) / (1 - α * β)))) +
        ε ^ 2 / 2 * (-(M.Yb * M.uc * (2 * PriceDispersion.ThetaCalvo α β M.θ M.omg) *
          ∑' t, β ^ t * (π1 (t + 1) ^ 2 + Moments.calvoKappa α β M.omg M.θ M.sig / M.θ *
            M.gap (y1 t) (ξ1 t) ^ 2))))) =O[𝓝 0] fun ε => ε ^ 3 := by
  have hw := hM.w_nonneg
  have hw1 := hM.w_sum
  obtain ⟨hcn, hco⟩ := cen_of_family hM hθ h hy1 hdem hX0
  have hdisc := disc_o tendsto_unif hw hw1 hM.θ_ne_one hcn hco
  obtain ⟨C, hC⟩ := hπ1
  have hπs := BridgeCore.unif_shift (f := fun t ε => infl ε t - ε * π1 t) (g := fun ε => ε ^ 2) hπ
  have hiu : (fun p : ℕ × ℝ => infl p.2 (p.1 + 1)) =O[unif] fun p => p.2 ^ 1 :=
    ((BridgeExtensions.o_weaken tendsto_unif (by norm_num : 1 ≤ 2) hπs).add
      (((isBigO_refl (fun p : ℕ × ℝ => p.2) unif).mul (BridgeCore.unif_of_bounded
        (f := fun t => π1 (t + 1)) ⟨C, fun t => by simpa using hC (t + 1)⟩)).congr_right
          fun p => by ring)).congr_left fun p => by ring
  have he : (fun p : ℕ × ℝ => (crossMean M.w (X p.2 (p.1 + 1)) - crossMean M.w (X p.2 p.1)) -
      infl p.2 (p.1 + 1)) =O[unif] fun p => p.2 ^ 2 :=
    hdisc.congr_left fun p => by rw [hinfl]
  have hRo := (sq_add_sub_o tendsto_unif hiu he).const_mul_left (α / (1 - α))
  refine BridgeCore.Econ.prop64_bridge hM heff hden hθ hd hα0 hα1 hβ0 hβ1 h hy1 hξ1
    (D := fun ε t => crossVar M.w (X ε t))
    (R := fun ε t => α / (1 - α) * ((infl ε (t + 1) +
      ((crossMean M.w (X ε (t + 1)) - crossMean M.w (X ε t)) - infl ε (t + 1))) ^ 2 -
        infl ε (t + 1) ^ 2)) (fun ε t => ?_) (fun ε t => ?_) hπ ⟨C, hC⟩ hRo
  · rw [show yh t ε = fun i => LY t ε - M.θ * (X ε (t + 1) i - LP t ε) from funext (hdem t ε)]
    exact Moments.crossVar_demand hw1 _ _ _ _
  · have hr := goods_rec_fin hw hw1 hα1.ne (hG ε) t
    simp only [sub_zero] at hr
    rw [hr]
    ring

/-- Woodford (2003), **Proposition 6.5, eq. (2.25), p. 402, Layer B FROM THE GOODS POPULATION
WITH INDEXATION**. `BridgeCore.Econ.prop65_bridge` with `var_i ŷ = θ²Δ` (2.12), the indexation
dispersion law (2.24) (non-resetting prices raised by `γπ_{t−1}`, `Links.GoodsPop.Calvo` with
`d_t = γπ_{t−1}`) and the `O(ε³)` remainder of the recursion in index inflation (uniform Prop. 6.3
bound `disc_o`) all discharged. -/
theorem prop65_goods [MeasurableSpace ι] [MeasurableSingletonClass ι] {M : BridgeCore.Econ Ξ ι}
    (hM : M.Std) (heff : M.vy = M.uc) (hden : M.sig + M.omg ≠ 0) (hθ : M.θ ≠ 0)
    (hd : 1 + M.omg * M.θ ≠ 0) {α β γ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {yh : ℕ → ℝ → ι → ℝ} {y1 : ℕ → ι → ℝ} {ξ1 : ℕ → Ξ}
    (h : (fun p : ℕ × ℝ => yh p.1 p.2 - p.2 • y1 p.1) =O[unif] fun p => p.2 ^ 2)
    (hy1 : ∃ C, ∀ t, ‖y1 t‖ ≤ C) (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C) {X : ℝ → ℕ → ι → ℝ}
    {Rs : ℝ → ℕ → Set ι} {ps : ℝ → ℕ → ℝ} {LY LP : ℕ → ℝ → ℝ} {infl : ℝ → ℕ → ℝ}
    (hG : ∀ ε, Links.GoodsPop.Calvo (wMeasure M.w) α (X ε) (Rs ε) (ps ε) fun t => γ * infl ε t)
    (hdem : ∀ t ε i, yh t ε i = LY t ε - M.θ * (X ε (t + 1) i - LP t ε))
    (hX0 : (fun ε => cen M.w (X ε 0)) =O[𝓝 0] fun ε => ε ^ 1)
    (hinfl : ∀ ε t, infl ε (t + 1) = logP M.w M.θ (X ε (t + 1)) - logP M.w M.θ (X ε t))
    {π1 : ℕ → ℝ} (hπ : (fun p : ℕ × ℝ => infl p.2 p.1 - p.2 * π1 p.1) =O[unif] fun p => p.2 ^ 2)
    (hπ1 : ∃ C, ∀ t, |π1 t| ≤ C) :
    (fun ε => ∑' t, β ^ t * M.Ustate (yh t ε) (ε • ξ1 t) -
      ((∑' t, β ^ t * M.tipState (ε • ξ1 t) - M.Yb * M.uc *
          (M.θ * (1 + M.omg * M.θ) / 2 * (α * crossVar M.w (X ε 0) / (1 - α * β)))) +
        ε ^ 2 / 2 * (-(M.Yb * M.uc * (2 * PriceDispersion.ThetaCalvo α β M.θ M.omg) *
          ∑' t, β ^ t * ((π1 (t + 1) - γ * π1 t) ^ 2 +
            Moments.calvoKappa α β M.omg M.θ M.sig / M.θ * M.gap (y1 t) (ξ1 t) ^ 2))))) =O[𝓝 0]
      fun ε => ε ^ 3 := by
  have hw := hM.w_nonneg
  have hw1 := hM.w_sum
  obtain ⟨hcn, hco⟩ := cen_of_family hM hθ h hy1 hdem hX0
  have hdisc := disc_o tendsto_unif hw hw1 hM.θ_ne_one hcn hco
  obtain ⟨C, hC⟩ := hπ1
  have hb : ∀ k : ℕ, (fun p : ℕ × ℝ => π1 (p.1 + k)) =O[unif] fun _ => (1 : ℝ) := fun k =>
    BridgeCore.unif_of_bounded (f := fun t => π1 (t + k)) ⟨C, fun t => by simpa using hC (t + k)⟩
  have hπs := BridgeCore.unif_shift (f := fun t ε => infl ε t - ε * π1 t) (g := fun ε => ε ^ 2) hπ
  have hO : ∀ k : ℕ, (fun p : ℕ × ℝ => infl p.2 (p.1 + k) - p.2 * π1 (p.1 + k)) =O[unif]
      (fun p => p.2 ^ 2) → (fun p : ℕ × ℝ => infl p.2 (p.1 + k)) =O[unif] fun p => p.2 ^ 1 :=
    fun k hk => ((BridgeExtensions.o_weaken tendsto_unif (by norm_num : 1 ≤ 2) hk).add
      (((isBigO_refl (fun p : ℕ × ℝ => p.2) unif).mul (hb k)).congr_right
        fun p => by ring)).congr_left fun p => by ring
  have hi1 := hO 1 hπs
  have hi0 := hO 0 hπ
  have ha : (fun p : ℕ × ℝ => infl p.2 (p.1 + 1) - γ * infl p.2 p.1) =O[unif]
      fun p => p.2 ^ 1 := hi1.sub (hi0.const_mul_left γ)
  have he : (fun p : ℕ × ℝ => (crossMean M.w (X p.2 (p.1 + 1)) - crossMean M.w (X p.2 p.1)) -
      infl p.2 (p.1 + 1)) =O[unif] fun p => p.2 ^ 2 :=
    hdisc.congr_left fun p => by rw [hinfl]
  have hRo := (sq_add_sub_o tendsto_unif ha he).const_mul_left (α / (1 - α))
  refine BridgeCore.Econ.prop65_bridge hM heff hden hθ hd hα0 hα1 hβ0 hβ1 h hy1 hξ1
    (D := fun ε t => crossVar M.w (X ε t))
    (R := fun ε t => α / (1 - α) * (((infl ε (t + 1) - γ * infl ε t) +
      ((crossMean M.w (X ε (t + 1)) - crossMean M.w (X ε t)) - infl ε (t + 1))) ^ 2 -
        (infl ε (t + 1) - γ * infl ε t) ^ 2)) (fun ε t => ?_) (fun ε t => ?_) hπ ⟨C, hC⟩ hRo
  · rw [show yh t ε = fun i => LY t ε - M.θ * (X ε (t + 1) i - LP t ε) from funext (hdem t ε)]
    exact Moments.crossVar_demand hw1 _ _ _ _
  · rw [goods_rec_fin hw hw1 hα1.ne (hG ε) t]
    ring

/-! ## The money-demand residual of Proposition 6.7 from the first-order condition -/

/-- Woodford (2003), eq. (1.2), p. 385, at FIRST order along a family (a `C²` map into any normed
space): if `z_b = O(s)` then `F(z̄ + z_b) − F(z̄) − DF(z̄) z_b = O(s²)`. -/
theorem taylor1_family {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {F : E → G} (hF : ContDiff ℝ 2 F) (z0 : E)
    (hs : Tendsto s L (𝓝 0)) {z : B → E} (hz : z =O[L] fun b => s b ^ 1) :
    (fun b => F (z0 + z b) - F z0 - fderiv ℝ F z0 (z b)) =O[L] fun b => s b ^ 2 := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := h1.contDiffAt.exists_lipschitzOnWith (x := z0)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 ht
  have hz0 : Tendsto z L (𝓝 0) := BridgeExtensions.tendsto_of_o_one hs hz
  have hzn : (fun b => ‖z b‖ ^ 2) =O[L] fun b => s b ^ 2 :=
    (hz.norm_left.pow 2).congr_right fun b => by ring
  refine (IsBigO.of_bound K ?_).trans hzn
  filter_upwards [hz0.eventually_mem (Metric.ball_mem_nhds 0 hδ)] with b hb
  have hzb : ‖z b‖ < δ := by simpa using hb
  have hS : Metric.closedBall z0 ‖z b‖ ⊆ Metric.ball z0 δ := Metric.closedBall_subset_ball hzb
  have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun x => F x - fderiv ℝ F z0 x) (f' := fun x => fderiv ℝ F x - fderiv ℝ F z0)
    (s := Metric.closedBall z0 ‖z b‖) (C := K * ‖z b‖) (x := z0) (y := z0 + z b)
    (fun x _ => (((hF.differentiable (by norm_num) x).hasFDerivAt).sub
      (fderiv ℝ F z0).hasFDerivAt).hasFDerivWithinAt) (fun x hx => ?_)
    (convex_closedBall _ _) (Metric.mem_closedBall_self (norm_nonneg _)) (by simp)
  · simp only [map_add, add_sub_cancel_left] at key
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖F (z0 + z b) - F z0 - fderiv ℝ F z0 (z b)‖ =
          ‖F (z0 + z b) - (fderiv ℝ F z0 z0 + fderiv ℝ F z0 (z b)) -
            (F z0 - fderiv ℝ F z0 z0)‖ := by congr 1; abel
      _ ≤ K * ‖z b‖ * ‖z b‖ := key
      _ = K * ‖z b‖ ^ 2 := by ring
  · have h2 := hK.dist_le_mul x (hball (hS hx)) z0 (hball (Metric.mem_ball_self hδ))
    rw [dist_eq_norm, dist_eq_norm] at h2
    have h3 : ‖x - z0‖ ≤ ‖z b‖ := by simpa [dist_eq_norm] using hx
    calc ‖fderiv ℝ F x - fderiv ℝ F z0‖ ≤ K * ‖x - z0‖ := h2
      _ ≤ K * ‖z b‖ := mul_le_mul_of_nonneg_left h3 K.coe_nonneg

/-- Woodford (2003), App. E.1, p. 693: `e^x − 1 − x = O(s²)` along a family with `x = O(s)`. -/
theorem exp_sub_one_sub_o (hs : Tendsto s L (𝓝 0)) {x : B → ℝ} (hx : x =O[L] fun b => s b ^ 1) :
    (fun b => Real.exp (x b) - 1 - x b) =O[L] fun b => s b ^ 2 :=
  (((BridgeExtensions.o_pow hx 2).const_mul_left (1 / 2)).add (BridgeExtensions.o_weaken hs
    (by norm_num : 2 ≤ 3) (BridgeExtensions.expRem_o hs hx))).congr_left fun b => by
      rw [ExpLogCES.exp_sub_one_eq]; ring

variable {Ξ' : Type*} [NormedAddCommGroup Ξ'] [NormedSpace ℝ Ξ']

/-- Woodford (2003), eq. (4.1), p. 420, Assumption 6.1, p. 422 and footnote 4 of App. E.4,
p. 700 (**the money-demand residual is of second order**). Real balances solve the first-order
condition `u_m(Y, m; ξ) = Δ·u_c(Y, m; ξ)` with `Δ = (i − iᵐ)/(1 + i) = 1 − e^{−(î − îᵐ)}` (the
interest differential at the satiated steady state `Δ̄ = 0`), BELOW satiation (`m < m̄`) where the
utility `U` coincides with its `C³` extension `Ũ`. With the coefficient definitions of
`BridgeExtensions.prop67_actual` (`u_m(m̄) = 0`, `χ`, `s_mσ_m⁻¹ = (η_iv̄)⁻¹`, `εᵐ`, `η_y = χη_iv̄`)
and `v̄ = Ȳ/m̄` (velocity), along any family with `Ŷ, m̂, î − îᵐ, ξ, εᵐ = O(s)`:
`m̂ = η_yŶ − η_i(î − îᵐ) + εᵐ + O(s²)`, i.e. the residual `r` of (4.1) is `O(s²)`. -/
theorem money_residual_o (hs : Tendsto s L (𝓝 0)) {U Ut : ℝ × ℝ × Ξ' → ℝ}
    (hUt : ContDiff ℝ 3 Ut) {mbar Ybar : ℝ} (hmbar : 0 < mbar)
    (hEq : Set.EqOn U Ut {z | z.2.1 ≤ mbar}) (P : Transactions.TxParams)
    (hvel : P.vbar * mbar = Ybar) (hey : P.etaY = P.chi * P.etaI * P.vbar) (hi : P.etaI ≠ 0)
    (hvb : P.vbar ≠ 0) (huc : fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) ≠ 0)
    (hsat : fderiv ℝ Ut (Ybar, mbar, 0) (0, 1, 0) = 0)
    (h12 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (0, 1, 0) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (1, 0, 0) =
        2 * (P.chi * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / mbar))
    (h22 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (0, 1, 0) =
      -(Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / (P.etaI * P.vbar) / mbar ^ 2))
    {Yh mh d eps : B → ℝ} {xu : B → Ξ'}
    (heps : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (0, 0, xu b) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 0, xu b) (0, 1, 0) =
        2 * (Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / (P.etaI * P.vbar) / mbar * eps b))
    (hY : Yh =O[L] fun b => s b ^ 1) (hmh : mh =O[L] fun b => s b ^ 1)
    (hd : d =O[L] fun b => s b ^ 1) (hxu : xu =O[L] fun b => s b ^ 1)
    (hbelow : ∀ᶠ b in L, mh b < 0)
    (hfoc : ∀ᶠ b in L, fderiv ℝ U (Ybar * Real.exp (Yh b), mbar * Real.exp (mh b), xu b)
      (0, 1, 0) = (1 - Real.exp (-d b)) *
        fderiv ℝ U (Ybar * Real.exp (Yh b), mbar * Real.exp (mh b), xu b) (1, 0, 0)) :
    (fun b => mh b - (P.etaY * Yh b - P.etaI * d b + eps b)) =O[L] fun b => s b ^ 2 := by
  subst hvel
  set z0 : ℝ × ℝ × Ξ' := (P.vbar * mbar, mbar, 0) with hz0
  set uc := fderiv ℝ Ut z0 (1, 0, 0) with huc_def
  set D2 := fderiv ℝ (fderiv ℝ Ut) z0 with hD2
  have hsym : IsSymmSndFDerivAt ℝ Ut z0 :=
    (hUt.contDiffAt (x := z0)).isSymmSndFDerivAt (by simp; norm_num)
  have lev : ∀ (c : ℝ) (x : B → ℝ), x =O[L] (fun b => s b ^ 1) →
      (fun b => c * (Real.exp (x b) - 1)) =O[L] fun b => s b ^ 1 := fun c x hx =>
    (((BridgeExtensions.o_weaken hs (by norm_num : 1 ≤ 2) (exp_sub_one_sub_o hs hx)).add
      hx).const_mul_left c).congr_left fun b => by ring
  set h : B → ℝ × ℝ × Ξ' := fun b =>
    (P.vbar * mbar * (Real.exp (Yh b) - 1), mbar * (Real.exp (mh b) - 1), xu b) with hh_def
  have hh : h =O[L] fun b => s b ^ 1 :=
    (lev (P.vbar * mbar) Yh hY).prod_left ((lev mbar mh hmh).prod_left hxu)
  have hF : ContDiff ℝ 2 (fderiv ℝ Ut) := hUt.fderiv_right (by norm_num)
  have T := taylor1_family hF z0 hs hh
  have ev : ∀ v : ℝ × ℝ × Ξ', (fun b => fderiv ℝ Ut (z0 + h b) v - fderiv ℝ Ut z0 v -
      D2 (h b) v) =O[L] fun b => s b ^ 2 := fun v =>
    (((ContinuousLinearMap.apply ℝ ℝ v).isBigO_comp _ _).trans T).congr_left fun b => by
      simp [hD2]
  have T1 := ev (1, 0, 0)
  have T2 := ev (0, 1, 0)
  have hD1 : (fun b => D2 (h b) (1, 0, 0)) =O[L] fun b => s b ^ 1 :=
    (((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ), (0 : Ξ'))).comp D2).isBigO_comp _
      _).trans hh
  have hP1 : (fun b => fderiv ℝ Ut (z0 + h b) (1, 0, 0) - uc) =O[L] fun b => s b ^ 1 :=
    ((BridgeExtensions.o_weaken hs (by norm_num : 1 ≤ 2) T1).add hD1).congr_left
      fun b => by ring
  have hΔd : (fun b => Real.exp (-d b) - 1 - -d b) =O[L] fun b => s b ^ 2 :=
    exp_sub_one_sub_o hs hd.neg_left
  have hΔ : (fun b => 1 - Real.exp (-d b)) =O[L] fun b => s b ^ 1 :=
    ((BridgeExtensions.o_weaken hs (by norm_num : 1 ≤ 2) hΔd).neg_left.add hd).congr_left
      fun b => by ring
  have hprod := BridgeExtensions.o_mul hΔ hP1 (by norm_num : 1 + 1 = 2)
  have hcomb := ((((exp_sub_one_sub_o hs hY).const_mul_left P.etaY).sub
    (exp_sub_one_sub_o hs hmh)).sub ((hprod.sub T2).const_mul_left (P.etaI / uc))).add
      (hΔd.const_mul_left P.etaI)
  refine hcomb.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [hfoc, hbelow] with b hb hlt
  have hpt : z0 + h b = (P.vbar * mbar * Real.exp (Yh b), mbar * Real.exp (mh b), xu b) := by
    simp only [hz0, hh_def, Prod.mk_add_mk, zero_add]
    congr 1 <;> [ring; (congr 1; ring)]
  have hlt' : mbar * Real.exp (mh b) < mbar := by
    have := Real.exp_lt_one_iff.2 hlt
    nlinarith
  have hUe : U =ᶠ[𝓝 (P.vbar * mbar * Real.exp (Yh b), mbar * Real.exp (mh b), xu b)] Ut :=
    Filter.eventuallyEq_of_mem ((isOpen_lt (continuous_fst.comp continuous_snd)
      continuous_const).mem_nhds hlt') fun w hw =>
      hEq (show w.2.1 ≤ mbar from le_of_lt hw)
  rw [hUe.fderiv_eq] at hb
  have hsplit : h b = (P.vbar * mbar * (Real.exp (Yh b) - 1)) • ((1 : ℝ), (0 : ℝ), (0 : Ξ')) +
      (mbar * (Real.exp (mh b) - 1)) • ((0 : ℝ), (1 : ℝ), (0 : Ξ')) +
        ((0 : ℝ), (0 : ℝ), xu b) := by
    simp only [hh_def]
    ext <;> simp
  have h12' : D2 (1, 0, 0) (0, 1, 0) = P.chi * uc / mbar := by
    have := hsym (1, 0, 0) (0, 1, 0)
    linarith [h12]
  have heps' : D2 (0, 0, xu b) (0, 1, 0) =
      P.vbar * mbar * uc / (P.etaI * P.vbar) / mbar * eps b := by
    have := hsym (0, 1, 0) (0, 0, xu b)
    linarith [heps b]
  have hD2e2 : D2 (h b) (0, 1, 0) = P.vbar * mbar * (Real.exp (Yh b) - 1) *
      (P.chi * uc / mbar) + mbar * (Real.exp (mh b) - 1) *
        (-(P.vbar * mbar * uc / (P.etaI * P.vbar) / mbar ^ 2)) +
      P.vbar * mbar * uc / (P.etaI * P.vbar) / mbar * eps b := by
    rw [hsplit, map_add, map_add, map_smul, map_smul]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [h12', heps', h22]
  rw [hpt] at *
  rw [hsat, hD2e2, hb, hey]
  have hm0 : mbar ≠ 0 := hmbar.ne'
  field_simp
  ring

/-! ## Discounted Propositions 6.8, 6.11, 6.13 from the primitives: tools -/

variable {A : Type*} {l : Filter A} {e : A → ℝ}

/-- Woodford (2003), App. E.2, p. 695 (uniformly in the date): relative prices of order `ε` at
every date `t ≥ 0` (uniformly) and at the initial date `−1` give relative prices of order `ε` at
every index, uniformly (index `0` is date `−1`). -/
theorem cen_all_prod {J : Type*} [Norm J] {X : A → ℕ → J}
    (hn : (fun p : A × ℕ => X p.1 (p.2 + 1)) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (h0 : (fun a => X a 0) =O[l] fun a => e a ^ 1) :
    (fun p : A × ℕ => X p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 := by
  obtain ⟨C1, h1⟩ := hn.bound
  obtain ⟨C2, h2⟩ := h0.bound
  refine IsBigO.of_bound (max C1 C2) ?_
  rw [Filter.prod_top, Filter.eventually_comap] at h1 ⊢
  filter_upwards [h1, h2] with a ha ha0 p hp
  obtain ⟨a', t⟩ := p
  simp only at hp
  subst hp
  cases t with
  | zero => exact ha0.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  | succ t =>
    exact (ha (a', t) rfl).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

/-- Woodford (2003), (E.2)–(E.3), p. 692: the terms `c + Dξ + ½D²(ξ, ξ)` of an expansion are a
bounded sequence when the disturbances are bounded. -/
theorem bdd_quad_terms {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ)
    (D1 : E →L[ℝ] ℝ) (D2 : E →L[ℝ] E →L[ℝ] ℝ) {u : ℕ → E} {M : ℝ} (hu : ∀ t, ‖u t‖ ≤ M) :
    Sequences.Bdd (fun t => c + D1 (u t) + D2 (u t) (u t) / 2) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hu 0)
  have b1 : Sequences.Bdd (fun t => D1 (u t)) := ⟨‖D1‖ * M, fun t => by
    rw [← Real.norm_eq_abs]
    exact (D1.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hu t) (norm_nonneg _))⟩
  have b2 : Sequences.Bdd (fun t => D2 (u t) (u t)) := ⟨‖D2‖ * M * M, fun t => by
    rw [← Real.norm_eq_abs]
    refine (D2.le_opNorm₂ _ _).trans ?_
    gcongr <;> exact hu t⟩
  exact ((Sequences.Bdd.const c).add b1).add (b2.div_const 2)

omit [NormedSpace ℝ Ξ'] in
/-- Woodford (2003), App. E.4, E.8: a disturbance in the last coordinate has the norm of the
disturbance. -/
theorem norm_triple (x : Ξ') : ‖((0 : ℝ), (0 : ℝ), x)‖ = ‖x‖ := by
  simp [Prod.norm_def]

omit [NormedSpace ℝ Ξ'] in
/-- Woodford (2003), App. E.1: a disturbance in the second coordinate has the norm of the
disturbance. -/
theorem norm_pair (x : Ξ') : ‖((0 : ℝ), x)‖ = ‖x‖ := by
  simp [Prod.norm_def]

/-- Woodford (2003), (2.20)–(2.21), pp. 399–400 (**the discounted Calvo dispersion law of a
finite cross-section**): if the goods of the weighted cross-section follow the Calvo rule
(`Links.GoodsPop.Calvo` on `wMeasure`), demand is Dixit–Stiglitz (2.12) and mean-price inflation
is bounded, then `∑βᵗ var_i ŷ_t = θ²(α/((1 − α)(1 − αβ))∑βᵗπ̄_t² + αΔ_{−1}/(1 − αβ))`. -/
theorem disp_hasSum_fin [MeasurableSpace ι] [MeasurableSingletonClass ι] {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {α β θ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {X : ℕ → ι → ℝ} {R : ℕ → Set ι} {ps : ℕ → ℝ}
    (hG : Links.GoodsPop.Calvo (wMeasure w) α X R ps fun _ => 0) {y : ℕ → ι → ℝ}
    {LY LP : ℕ → ℝ} (hdem : ∀ t i, y t i = LY t - θ * (X (t + 1) i - LP t))
    (hπ : Sequences.Bdd fun t => crossMean w (X (t + 1)) - crossMean w (X t)) :
    HasSum (fun t => β ^ t * crossVar w (y t))
      (θ ^ 2 * (Moments.calvoK α β *
        ∑' t, β ^ t * (crossMean w (X (t + 1)) - crossMean w (X t)) ^ 2 +
          α * crossVar w (X 0) / (1 - α * β))) := by
  have hrec : ∀ t, crossVar w (X (t + 1)) =
      α * Sequences.lagS (crossVar w (X 0)) (fun s => crossVar w (X (s + 1))) t +
        α / (1 - α) * (crossMean w (X (t + 1)) - crossMean w (X t)) ^ 2 := fun t => by
    have h := goods_rec_fin hw hw1 hα1.ne hG t
    simp only [sub_zero] at h
    rw [h]
    cases t <;> rfl
  have hΔb := Sequences.disp_bdd hα0.le hα1 hπ hrec
  have hD := Sequences.disp_discounted hβ0 hβ1 hα0.le hα1 hπ hrec
  have h := ((hΔb.summable hβ0 hβ1).hasSum).mul_left (θ ^ 2)
  rw [hD] at h
  convert h using 1
  · funext t
    rw [show y t = fun i => LY t - θ * (X (t + 1) i - LP t) from funext (hdem t),
      Moments.crossVar_demand hw1]
    ring
  · have h1 : (1 : ℝ) - α ≠ 0 := by linarith
    have h2 : (1 : ℝ) - α * β ≠ 0 := by nlinarith
    unfold Moments.calvoK
    field_simp
    ring

/-- Woodford (2003), App. E.2, p. 695, uniformly in the date: Dixit–Stiglitz demand with relative
outputs `O(ε)` uniformly and initial relative prices `O(ε)` gives relative prices `O(ε)` at
both dates of every inflation rate, hence `π̄_t − π_t = O(ε²)` uniformly (`disc_o`). -/
theorem disc_prod {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {θ : ℝ} (hθ0 : θ ≠ 0)
    (hθ : θ ≠ 1) (he : Tendsto e l (𝓝 0)) {yh : A → ℕ → ι → ℝ} {lp : A → ℕ → ι → ℝ}
    {LY LP : A → ℕ → ℝ} (hdem : ∀ a t i, yh a t i = LY a t - θ * (lp a (t + 1) i - LP a t))
    (hyh : (fun p : A × ℕ => yh p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hlp0 : (fun a => cen w (lp a 0)) =O[l] fun a => e a ^ 1) :
    (fun p : A × ℕ => (crossMean w (lp p.1 (p.2 + 1)) - crossMean w (lp p.1 p.2)) -
      (logP w θ (lp p.1 (p.2 + 1)) - logP w θ (lp p.1 p.2))) =O[l ×ˢ ⊤]
        fun p => e p.1 ^ 2 := by
  have hs := BridgeExtensions.tendsto_amp (J := ℕ) he
  have hcn : (fun p : A × ℕ => cen w (lp p.1 (p.2 + 1))) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 :=
    ((cen_o hw hw1 hyh).const_smul_left (-θ⁻¹)).congr_left fun p =>
      (cen_demand hw1 hθ0 (hdem p.1 p.2)).symm
  exact disc_o hs hw hw1 hθ hcn (cen_all_prod (X := fun a t => cen w (lp a t)) hcn hlp0)

/-- Woodford (2003), (4.9) and (E.15), p. 699: the t.i.p. of the transactions model is a bounded
sequence when the disturbances are bounded. -/
theorem bdd_tipT (Ut : ℝ × ℝ × Ξ' → ℝ) (v : ℝ × Ξ' → ℝ) (Ybar mbar K : ℝ)
    (P : Transactions.TxParams) {xu xv : ℕ → Ξ'} {g q eps : ℕ → ℝ}
    (hxu : ∃ M, ∀ t, ‖xu t‖ ≤ M) (hxv : ∃ M, ∀ t, ‖xv t‖ ≤ M) (hg : Sequences.Bdd g)
    (hq : Sequences.Bdd q) (heps : Sequences.Bdd eps) :
    Sequences.Bdd (fun t => BridgeExtensions.tipT Ut v Ybar mbar (xu t) (xv t) +
      K * Transactions.tip P (g t) (q t) (eps t) 0 0) := by
  obtain ⟨M1, h1⟩ := hxu
  obtain ⟨M2, h2⟩ := hxv
  have b1 := bdd_quad_terms (Ut (Ybar, mbar, 0)) (fderiv ℝ Ut (Ybar, mbar, 0))
    (fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0)) (u := fun t => ((0 : ℝ), (0 : ℝ), xu t))
    (M := M1) fun t => by rw [norm_triple]; exact h1 t
  have b2 := bdd_quad_terms (v (Ybar, 0)) (fderiv ℝ v (Ybar, 0))
    (fderiv ℝ (fderiv ℝ v) (Ybar, 0)) (u := fun t => ((0 : ℝ), xv t))
    (M := M2) fun t => by rw [norm_pair]; exact h2 t
  have b3 : Sequences.Bdd (fun t => Transactions.tip P (g t) (q t) (eps t) 0 0) := by
    unfold Transactions.tip Transactions.natRate Transactions.xStar Transactions.sM
    aesop (add safe apply [Sequences.Bdd.add, Sequences.Bdd.sub, Sequences.Bdd.mul,
      Sequences.Bdd.neg, Sequences.Bdd.div_const, Sequences.Bdd.pow, Sequences.Bdd.const])
  exact (b1.sub b2).add ((Sequences.Bdd.const K).mul b3)

/-- Woodford (2003), **Proposition 6.8**, (4.10)–(4.11), p. 423, LAYER B FROM THE PRIMITIVES
(discounted, uniformly in the date). `BridgeExtensions.prop68_layerB` with every hypothesis
discharged:
* the per-period expansion `hP` is `BridgeExtensions.prop67_actual` on the filter `l ×ˢ ⊤`
  (one constant for all dates), from the actual utility `U` (one-sided at satiation) and `v`;
* the money-demand residual is `O(ε²)` from the first-order condition `u_m = Δu_c`
  (`money_residual_o`);
* `var_i ŷ = θ²Δ` and the discounted Calvo law from the goods following the Calvo rule
  (`disp_hasSum_fin`), with t.i.p. `T₀ = αΔ_{−1}/(1 − αβ)`;
* `π̄ − π = O(ε²)` uniformly (`disc_prod`), with `π` index inflation;
* the t.i.p. is bounded for bounded disturbances (`bdd_tipT`).
Conclusion: `∑βᵗU_t = ∑βᵗτ_t − (K/2)[Λ∑βᵗL_t + (θ⁻¹ + ω)θ²T₀] + O(ε³)` with `L_t` the loss
(4.10) on the actual path, `Λ = θ(1 + ωθ)α/((1 − α)(1 − αβ))`, `K = Ȳu_c`. -/
theorem prop68_primitive [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (he : Tendsto e l (𝓝 0)) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ : θ ≠ 1) {U Ut : ℝ × ℝ × Ξ' → ℝ} (hUt : ContDiff ℝ 3 Ut) {mbar : ℝ}
    (hmbar : 0 < mbar) (hEq : Set.EqOn U Ut {z | z.2.1 ≤ mbar}) {v : ℝ × Ξ' → ℝ}
    (hv : ContDiff ℝ 3 v) {Ybar : ℝ} (P : Transactions.TxParams) (hθi : P.thetaInv = θ⁻¹)
    (hvel : P.vbar * mbar = Ybar) (hey : P.etaY = P.chi * P.etaI * P.vbar)
    (hΩ : 0 < Transactions.omegaMC P) (hω : 0 ≤ P.omega) (hi : P.etaI ≠ 0) (hvb : P.vbar ≠ 0)
    (huc : fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) ≠ 0)
    (hsat : fderiv ℝ Ut (Ybar, mbar, 0) (0, 1, 0) = 0)
    (h11 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (1, 0, 0) =
      -(P.sigInv * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / Ybar))
    (h12 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (0, 1, 0) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (1, 0, 0) =
        2 * (P.chi * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / mbar))
    (h22 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (0, 1, 0) =
      -(Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / (P.etaI * P.vbar) / mbar ^ 2))
    (hvy : BridgeExtensions.dY v (Ybar, 0) = fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0))
    (hvyy : BridgeExtensions.dYY v (Ybar, 0) = P.omega * BridgeExtensions.dY v (Ybar, 0) / Ybar)
    {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {yh : A → ℕ → ι → ℝ} {mh d g q eps : A → ℕ → ℝ} {xu xv : A → ℕ → Ξ'}
    (hg : ∀ a t, fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (0, 0, xu a t) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 0, xu a t) (1, 0, 0) =
        2 * (P.sigInv * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) * g a t))
    (heps : ∀ a t, fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (0, 0, xu a t) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 0, xu a t) (0, 1, 0) =
        2 * (Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / (P.etaI * P.vbar) / mbar *
          eps a t))
    (hq : ∀ a t, BridgeExtensions.dYXi v (Ybar, 0) (xv a t) =
      -(P.omega * BridgeExtensions.dY v (Ybar, 0) * q a t))
    (hyh : (fun p : A × ℕ => yh p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hmh : (fun p : A × ℕ => mh p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hd : (fun p : A × ℕ => d p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hgO : (fun p : A × ℕ => g p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hqO : (fun p : A × ℕ => q p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hepsO : (fun p : A × ℕ => eps p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hxu : (fun p : A × ℕ => xu p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hxv : (fun p : A × ℕ => xv p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hbelow : ∀ᶠ p in l ×ˢ ⊤, mh p.1 p.2 < 0)
    (hfoc : ∀ᶠ p in l ×ˢ ⊤, fderiv ℝ U (Ybar * Real.exp (BridgeExtensions.logYidx w θ
        (yh p.1 p.2)), mbar * Real.exp (mh p.1 p.2), xu p.1 p.2) (0, 1, 0) =
      (1 - Real.exp (-d p.1 p.2)) * fderiv ℝ U (Ybar * Real.exp (BridgeExtensions.logYidx w θ
        (yh p.1 p.2)), mbar * Real.exp (mh p.1 p.2), xu p.1 p.2) (1, 0, 0))
    {lp : A → ℕ → ι → ℝ} {Rs : A → ℕ → Set ι} {ps : A → ℕ → ℝ} {LY LP : A → ℕ → ℝ}
    (hG : ∀ a, Links.GoodsPop.Calvo (wMeasure w) α (lp a) (Rs a) (ps a) fun _ => 0)
    (hdem : ∀ a t i, yh a t i = LY a t - θ * (lp a (t + 1) i - LP a t))
    (hlp0 : (fun a => cen w (lp a 0)) =O[l] fun a => e a ^ 1)
    (hπ : (fun p : A × ℕ => logP w θ (lp p.1 (p.2 + 1)) - logP w θ (lp p.1 p.2)) =O[l ×ˢ ⊤]
      fun p => e p.1 ^ 1)
    (hpibB : ∀ a, Sequences.Bdd fun t => crossMean w (lp a (t + 1)) - crossMean w (lp a t))
    (hxuB : ∀ a, ∃ M, ∀ t, ‖xu a t‖ ≤ M) (hxvB : ∀ a, ∃ M, ∀ t, ‖xv a t‖ ≤ M)
    (hgB : ∀ a, Sequences.Bdd (g a)) (hqB : ∀ a, Sequences.Bdd (q a))
    (hepsB : ∀ a, Sequences.Bdd (eps a)) :
    (fun a => ∑' t, β ^ t * BridgeExtensions.periodUT U v w θ Ybar mbar (yh a t) (mh a t)
        (xu a t) (xv a t) -
      (∑' t, β ^ t * (BridgeExtensions.tipT Ut v Ybar mbar (xu a t) (xv a t) +
          Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) *
            Transactions.tip P (g a t) (q a t) (eps a t) 0 0) -
        Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / 2 *
          (θ * (1 + P.omega * θ) * Moments.calvoK α β * ∑' t, β ^ t *
            Transactions.loss410 P α β θ (logP w θ (lp a (t + 1)) - logP w θ (lp a t))
              (BridgeExtensions.logYidx w θ (yh a t) -
                Transactions.natRate P (g a t) (q a t) (eps a t)) (d a t) +
            (P.thetaInv + P.omega) * θ ^ 2 * (α * crossVar w (lp a 0) / (1 - α * β)))))
      =O[l] fun a => e a ^ 3 := by
  have hs := BridgeExtensions.tendsto_amp (J := ℕ) he
  have hYO := BridgeExtensions.logYidx_o hs hw0 hw1 hθ hyh
  have hr := money_residual_o hs hUt hmbar hEq P hvel hey hi hvb huc hsat h12 h22
    (heps := fun p => heps p.1 p.2) hYO hmh hd hxu hbelow hfoc
  have hW := BridgeExtensions.prop67_actual hs hw0 hw1 hθ hUt hmbar hEq hv P hθi hey hΩ.ne' hi
    hvb hsat h11 h12 h22 hvy hvyy (fun p => hg p.1 p.2) (fun p => heps p.1 p.2)
    (fun p => hq p.1 p.2) hyh hmh hd hgO hqO hepsO hxu hxv hr (hbelow.mono fun p hp => hp.le)
  exact BridgeExtensions.prop68_layerB P hα0 hα1 hβ0 hβ1 hθ0 (by rw [hθi, one_div]) hω hΩ hvb he
    (W := fun a t => BridgeExtensions.periodUT U v w θ Ybar mbar (yh a t) (mh a t) (xu a t)
      (xv a t))
    (τ := fun a t => BridgeExtensions.tipT Ut v Ybar mbar (xu a t) (xv a t) +
      Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) *
        Transactions.tip P (g a t) (q a t) (eps a t) 0 0)
    (Y := fun a t => BridgeExtensions.logYidx w θ (yh a t)) (V := fun a t => crossVar w (yh a t))
    (pib := fun a t => crossMean w (lp a (t + 1)) - crossMean w (lp a t))
    (infl := fun a t => logP w θ (lp a (t + 1)) - logP w θ (lp a t))
    (T0 := fun a => α * crossVar w (lp a 0) / (1 - α * β))
    (fun a => bdd_tipT Ut v Ybar mbar _ P (hxuB a) (hxvB a) (hgB a) (hqB a) (hepsB a))
    (hW.congr_left fun p => by simp only [Transactions.loss49, BridgeExtensions.txSat]; ring)
    hYO hd hgO hqO hepsO hπ (disc_prod hw0 hw1 hθ0.ne' hθ he hdem hyh hlp0)
    (fun a => disp_hasSum_fin hw0 hw1 hα0 hα1 hβ0 hβ1 (hG a) (hdem a) (hpibB a))

/-- Woodford (2003), App. E.2, p. 695: relative values are invariant to a common shift. -/
theorem cen_const_add {w : ι → ℝ} (hw1 : ∑ i, w i = 1) (c : ℝ) (y : ι → ℝ) :
    cen w (fun i => c + y i) = cen w y := by
  funext i
  unfold cen
  rw [ExpLogCES.crossMean_const_add hw1]
  ring

/-- Woodford (2003), (4.28)/(E.33): the t.i.p. of the sticky-wage model is a bounded sequence
when the disturbances are bounded. -/
theorem bdd_tip12 (u v : ℝ × Ξ' → ℝ) (Ybar Hbar K σi ω ν : ℝ) {xu xv : ℕ → Ξ'}
    {g a hb : ℕ → ℝ} (hxu : ∃ M, ∀ t, ‖xu t‖ ≤ M) (hxv : ∃ M, ∀ t, ‖xv t‖ ≤ M)
    (hg : Sequences.Bdd g) (ha : Sequences.Bdd a) (hhb : Sequences.Bdd hb) :
    Sequences.Bdd (fun t => BridgeExtensions.tip12 u v Ybar Hbar (xu t) (xv t) +
      K * StickyWageWelfare.tip612 σi ω ν 0 (g t) (a t) (hb t)) := by
  obtain ⟨M1, h1⟩ := hxu
  obtain ⟨M2, h2⟩ := hxv
  have b1 := bdd_quad_terms (u (Ybar, 0)) (fderiv ℝ u (Ybar, 0))
    (fderiv ℝ (fderiv ℝ u) (Ybar, 0)) (u := fun t => ((0 : ℝ), xu t))
    (M := M1) fun t => by rw [norm_pair]; exact h1 t
  have b2 := bdd_quad_terms (v (Hbar, 0)) (fderiv ℝ v (Hbar, 0))
    (fderiv ℝ (fderiv ℝ v) (Hbar, 0)) (u := fun t => ((0 : ℝ), xv t))
    (M := M2) fun t => by rw [norm_pair]; exact h2 t
  have b3 : Sequences.Bdd (fun t => StickyWageWelfare.tip612 σi ω ν 0 (g t) (a t) (hb t)) := by
    unfold StickyWageWelfare.tip612
    aesop (add safe apply [Sequences.Bdd.add, Sequences.Bdd.sub, Sequences.Bdd.mul,
      Sequences.Bdd.neg, Sequences.Bdd.div_const, Sequences.Bdd.pow, Sequences.Bdd.const])
  exact (b1.sub b2).add ((Sequences.Bdd.const K).mul b3)

variable {J : Type*} [Fintype J]

/-- Woodford (2003), **Proposition 6.13**, (4.29), p. 445, LAYER B FROM THE PRIMITIVES
(discounted, uniformly in the date). `BridgeExtensions.prop613_layerB` with every hypothesis
discharged:
* the per-period expansion `hP` is `BridgeExtensions.prop612_actual` on `l ×ˢ ⊤`;
* `V_p = var_i ŷ/θ_p² = Δ_p` (price dispersion `var_i log p`) by Dixit–Stiglitz demand (2.12)
  (`Moments.crossVar_demand`), and `V_w = var_j lw = Δ_w` (wage dispersion `var_j log w`) since
  relative wages are log wages less a common term;
* the Calvo laws for `Δ_p`, `Δ_w` from goods and labour types following the Calvo rule
  (`goods_rec_fin`; `ξ_p`, `ξ_w` the Calvo slopes);
* `π̄ − π = O(ε²)` and `π̄_w − π_w = O(ε²)` uniformly (`disc_o`), `π`, `π_w` index inflations;
* the t.i.p. is bounded for bounded disturbances (`bdd_tip12`).
Conclusion: `∑βᵗU_t = −(K/2)D∑βᵗL_t + ∑βᵗτ_t − (K/2)(t.i.p. of the initial dispersions)
+ O(ε³)`, `L_t` the loss (4.29) on the actual path, `x − x* = Ŷ − Ŷⁿ` at the efficient
steady state. -/
theorem prop613_primitive [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace J]
    [MeasurableSingletonClass J] (he : Tendsto e l (𝓝 0)) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {ωt : J → ℝ} (hωt0 : ∀ j, 0 ≤ ωt j) (hωt1 : ∑ j, ωt j = 1)
    {θp θw : ℝ} (hθp : 0 < θp) (hθp1 : θp ≠ 1) (hθw : 0 < θw) (hθw1 : θw ≠ 1)
    {u v : ℝ × Ξ' → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 3 G) (hG0 : G 0 = 1) {σi ω ν ωp φh Ybar Hbar : ℝ}
    (hG1 : fderiv ℝ G 0 1 = φh) (hG2 : fderiv ℝ (fderiv ℝ G) 0 1 1 = φh * (1 + ωp))
    (hω : ω = ωp + ν * φh) (hφ : 0 < φh) (hσω : 0 < σi + ω) (hωθ : 0 < 1 + ωp * θp)
    (hνθ : 0 < 1 + ν * θw)
    (hucc : BridgeExtensions.dYY u (Ybar, 0) = -(σi * BridgeExtensions.dY u (Ybar, 0) / Ybar))
    (hvhh : BridgeExtensions.dYY v (Hbar, 0) = ν * BridgeExtensions.dY v (Hbar, 0) / Hbar)
    (hss : Hbar * BridgeExtensions.dY v (Hbar, 0) * φh = Ybar * BridgeExtensions.dY u (Ybar, 0))
    {αp αw β : ℝ} (hap0 : 0 < αp) (hap1 : αp < 1) (haw0 : 0 < αw) (haw1 : αw < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {yh : A → ℕ → ι → ℝ} {lw : A → ℕ → J → ℝ} {av g hb : A → ℕ → ℝ} {xu xv : A → ℕ → Ξ'}
    (hg : ∀ a t, BridgeExtensions.dYXi u (Ybar, 0) (xu a t) =
      σi * BridgeExtensions.dY u (Ybar, 0) * g a t)
    (hhb : ∀ a t, BridgeExtensions.dYXi v (Hbar, 0) (xv a t) =
      -(ν * BridgeExtensions.dY v (Hbar, 0) * hb a t))
    (hyh : (fun p : A × ℕ => yh p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hlw : (fun p : A × ℕ => lw p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (ha : (fun p : A × ℕ => av p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hgO : (fun p : A × ℕ => g p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hhbO : (fun p : A × ℕ => hb p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hxu : (fun p : A × ℕ => xu p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hxv : (fun p : A × ℕ => xv p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    {lp : A → ℕ → ι → ℝ} {Rs : A → ℕ → Set ι} {ps : A → ℕ → ℝ} {LY LP : A → ℕ → ℝ}
    (hCp : ∀ a, Links.GoodsPop.Calvo (wMeasure w) αp (lp a) (Rs a) (ps a) fun _ => 0)
    (hdem : ∀ a t i, yh a t i = LY a t - θp * (lp a (t + 1) i - LP a t))
    (hlp0 : (fun a => cen w (lp a 0)) =O[l] fun a => e a ^ 1)
    {lwage : A → ℕ → J → ℝ} {Rw : A → ℕ → Set J} {pw : A → ℕ → ℝ} {LW : A → ℕ → ℝ}
    (hCw : ∀ a, Links.GoodsPop.Calvo (wMeasure ωt) αw (lwage a) (Rw a) (pw a) fun _ => 0)
    (hrel : ∀ a t j, lw a t j = lwage a (t + 1) j - LW a t)
    (hlw0 : (fun a => cen ωt (lwage a 0)) =O[l] fun a => e a ^ 1)
    (hπ : (fun p : A × ℕ => logP w θp (lp p.1 (p.2 + 1)) - logP w θp (lp p.1 p.2)) =O[l ×ˢ ⊤]
      fun p => e p.1 ^ 1)
    (hπw : (fun p : A × ℕ => logP ωt θw (lwage p.1 (p.2 + 1)) - logP ωt θw (lwage p.1 p.2))
      =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hxuB : ∀ a, ∃ M, ∀ t, ‖xu a t‖ ≤ M) (hxvB : ∀ a, ∃ M, ∀ t, ‖xv a t‖ ≤ M)
    (hgB : ∀ a, Sequences.Bdd (g a)) (haB : ∀ a, Sequences.Bdd (av a))
    (hhbB : ∀ a, Sequences.Bdd (hb a)) :
    (fun a => ∑' t, β ^ t * BridgeExtensions.periodU12 u v w ωt θp θw Ybar Hbar G (av a t)
        (yh a t) (lw a t) (xu a t) (xv a t) -
      (-(Ybar * BridgeExtensions.dY u (Ybar, 0) / 2 *
          StickyWageWelfare.Dsum θp (Moments.calvoXi αp β ωp θp) θw φh
            (Moments.calvoXi αw β ν θw)) *
        ∑' t, β ^ t * StickyWageWelfare.loss429
          (StickyWageWelfare.lamP θp (Moments.calvoXi αp β ωp θp) θw φh
            (Moments.calvoXi αw β ν θw))
          (StickyWageWelfare.lamW θp (Moments.calvoXi αp β ωp θp) θw φh
            (Moments.calvoXi αw β ν θw))
          (StickyWageWelfare.lamX613 σi ω θp (Moments.calvoXi αp β ωp θp) θw φh
            (Moments.calvoXi αw β ν θw))
          (logP w θp (lp a (t + 1)) - logP w θp (lp a t))
          (logP ωt θw (lwage a (t + 1)) - logP ωt θw (lwage a t))
          (BridgeExtensions.logYidx w θp (yh a t) -
            StickyWageWelfare.natY612 σi ω ν (g a t) (av a t) (hb a t)) 0 +
        (∑' t, β ^ t * (BridgeExtensions.tip12 u v Ybar Hbar (xu a t) (xv a t) +
            Ybar * BridgeExtensions.dY u (Ybar, 0) *
              StickyWageWelfare.tip612 σi ω ν 0 (g a t) (av a t) (hb a t)) -
          Ybar * BridgeExtensions.dY u (Ybar, 0) / 2 *
            (θp * (1 + ωp * θp) * (αp * crossVar w (lp a 0) / (1 - αp * β)) +
              θw / φh * (1 + ν * θw) * (αw * crossVar ωt (lwage a 0) / (1 - αw * β))))))
      =O[l] fun a => e a ^ 3 := by
  have hs := BridgeExtensions.tendsto_amp (J := ℕ) he
  have hYO := BridgeExtensions.logYidx_o hs hw0 hw1 hθp1 hyh
  have hW := BridgeExtensions.prop612_actual hs hw0 hw1 hωt0 hωt1 hθp.ne' hθp1 hθw1 hu hv hG hG0
    hG1 hG2 hω hφ.ne' hσω.ne' hucc hvhh hss (fun p => hg p.1 p.2) (fun p => hhb p.1 p.2) hyh hlw
    ha hgO hhbO hxu hxv
  have hVp : ∀ a t, crossVar w (yh a t) / θp ^ 2 = crossVar w (lp a (t + 1)) := fun a t => by
    rw [show yh a t = fun i => LY a t - θp * (lp a (t + 1) i - LP a t) from funext (hdem a t),
      Moments.crossVar_demand hw1]
    field_simp
  have hlwe : ∀ a t, lw a t = fun j => -LW a t + lwage a (t + 1) j := fun a t => by
    funext j; rw [hrel]; ring
  have hVw : ∀ a t, crossVar ωt (lw a t) = crossVar ωt (lwage a (t + 1)) := fun a t => by
    rw [hlwe, ExpLogCES.crossVar_const_add hωt1]
  have hx : (fun p : A × ℕ => (BridgeExtensions.logYidx w θp (yh p.1 p.2) -
      StickyWageWelfare.natY612 σi ω ν (g p.1 p.2) (av p.1 p.2) (hb p.1 p.2)) - 0) =O[l ×ˢ ⊤]
        fun p => e p.1 ^ 1 :=
    (hYO.sub ((((hgO.const_mul_left σi).add (ha.const_mul_left (1 + ω))).add
      (hhbO.const_mul_left ν)).const_mul_left (σi + ω)⁻¹)).congr_left fun p => by
        simp only [StickyWageWelfare.natY612]; ring
  have hΔp : (fun p : A × ℕ => crossVar w (lp p.1 (p.2 + 1))) =O[l ×ˢ ⊤] fun p => e p.1 ^ 2 :=
    ((BridgeExtensions.crossVar_o hw0 hw1 hyh).const_mul_left (θp ^ 2)⁻¹).congr_left
      fun p => by rw [← hVp]; ring
  have hΔw : (fun p : A × ℕ => crossVar ωt (lwage p.1 (p.2 + 1))) =O[l ×ˢ ⊤]
      fun p => e p.1 ^ 2 :=
    (BridgeExtensions.crossVar_o hωt0 hωt1 hlw).congr_left fun p => hVw _ _
  have hcw : (fun p : A × ℕ => cen ωt (lwage p.1 (p.2 + 1))) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 :=
    (cen_o hωt0 hωt1 hlw).congr_left fun p => by rw [hlwe, cen_const_add hωt1]
  have hwd := disc_o hs hωt0 hωt1 hθw1 hcw
    (cen_all_prod (X := fun a t => cen ωt (lwage a t)) hcw hlw0)
  exact BridgeExtensions.prop613_layerB hap0 hap1 haw0 haw1 hβ0 hβ1 hθp hθw hφ hωθ hνθ hσω he
    (K := Ybar * BridgeExtensions.dY u (Ybar, 0)) (xs := 0)
    (W := fun a t => BridgeExtensions.periodU12 u v w ωt θp θw Ybar Hbar G (av a t) (yh a t)
      (lw a t) (xu a t) (xv a t))
    (τ := fun a t => BridgeExtensions.tip12 u v Ybar Hbar (xu a t) (xv a t) +
      Ybar * BridgeExtensions.dY u (Ybar, 0) *
        StickyWageWelfare.tip612 σi ω ν 0 (g a t) (av a t) (hb a t))
    (x := fun a t => BridgeExtensions.logYidx w θp (yh a t) -
      StickyWageWelfare.natY612 σi ω ν (g a t) (av a t) (hb a t))
    (π := fun a t => logP w θp (lp a (t + 1)) - logP w θp (lp a t))
    (πw := fun a t => logP ωt θw (lwage a (t + 1)) - logP ωt θw (lwage a t))
    (pb := fun a t => crossMean w (lp a (t + 1)) - crossMean w (lp a t))
    (wb := fun a t => crossMean ωt (lwage a (t + 1)) - crossMean ωt (lwage a t))
    (Δp := fun a t => crossVar w (lp a (t + 1))) (Δw := fun a t => crossVar ωt (lwage a (t + 1)))
    (Δpm := fun a => crossVar w (lp a 0)) (Δwm := fun a => crossVar ωt (lwage a 0))
    (fun a => bdd_tip12 u v Ybar Hbar _ σi ω ν (hxuB a) (hxvB a) (hgB a) (haB a) (hhbB a))
    (hW.congr_left fun p => by
      simp only [BridgeExtensions.loss612, hVp, hVw]; ring)
    hx hπ hπw hΔp hΔw (disc_prod hw0 hw1 hθp.ne' hθp1 he hdem hyh hlp0) hwd
    (fun a => by simpa using goods_rec_fin hw0 hw1 hap1.ne (hCp a) 0)
    (fun a t => by simpa using goods_rec_fin hw0 hw1 hap1.ne (hCp a) (t + 1))
    (fun a => by simpa using goods_rec_fin hωt0 hωt1 haw1.ne (hCw a) 0)
    (fun a t => by simpa using goods_rec_fin hωt0 hωt1 haw1.ne (hCw a) (t + 1))

/-- Woodford (2003), (E.29)–(E.31), p. 705: the t.i.p. of the two-sector model is a bounded
sequence when the disturbances are bounded. -/
theorem bdd_tip2 (u v : ℝ × Ξ' → ℝ) (n1 η Ybar K σi ω : ℝ) {xu xv1 xv2 : ℕ → Ξ'}
    {f1 f2 g q1 q2 : ℕ → ℝ} (hxu : ∃ M, ∀ t, ‖xu t‖ ≤ M) (hxv1 : ∃ M, ∀ t, ‖xv1 t‖ ≤ M)
    (hxv2 : ∃ M, ∀ t, ‖xv2 t‖ ≤ M) (hf1 : Sequences.Bdd f1) (hf2 : Sequences.Bdd f2)
    (hg : Sequences.Bdd g) (hq1 : Sequences.Bdd q1) (hq2 : Sequences.Bdd q2) :
    Sequences.Bdd (fun t => BridgeExtensions.tip2 u v n1 Ybar (xu t) (xv1 t) (xv2 t) +
      K * TwoSectorWelfare.tip610 σi ω η⁻¹ n1 0 (g t) (q1 t) (q2 t) (f2 t - f1 t)
        (BridgeExtensions.tauAgg η⁻¹ n1 (f1 t) (f2 t))) := by
  obtain ⟨M1, h1⟩ := hxu
  obtain ⟨M2, h2⟩ := hxv1
  obtain ⟨M3, h3⟩ := hxv2
  have b1 := bdd_quad_terms (u (Ybar, 0)) (fderiv ℝ u (Ybar, 0))
    (fderiv ℝ (fderiv ℝ u) (Ybar, 0)) (u := fun t => ((0 : ℝ), xu t))
    (M := M1) fun t => by rw [norm_pair]; exact h1 t
  have b2 := bdd_quad_terms (v (Ybar, 0)) (fderiv ℝ v (Ybar, 0))
    (fderiv ℝ (fderiv ℝ v) (Ybar, 0)) (u := fun t => ((0 : ℝ), xv1 t))
    (M := M2) fun t => by rw [norm_pair]; exact h2 t
  have b3 := bdd_quad_terms (v (Ybar, 0)) (fderiv ℝ v (Ybar, 0))
    (fderiv ℝ (fderiv ℝ v) (Ybar, 0)) (u := fun t => ((0 : ℝ), xv2 t))
    (M := M3) fun t => by rw [norm_pair]; exact h3 t
  have b4 : Sequences.Bdd (fun t => TwoSectorWelfare.tip610 σi ω η⁻¹ n1 0 (g t) (q1 t) (q2 t)
      (f2 t - f1 t) (BridgeExtensions.tauAgg η⁻¹ n1 (f1 t) (f2 t))) := by
    unfold TwoSectorWelfare.tip610 BridgeExtensions.tauAgg
    aesop (add safe apply [Sequences.Bdd.add, Sequences.Bdd.sub, Sequences.Bdd.mul,
      Sequences.Bdd.neg, Sequences.Bdd.div_const, Sequences.Bdd.pow, Sequences.Bdd.const])
  exact (b1.sub (((Sequences.Bdd.const n1).mul b2).add
    ((Sequences.Bdd.const (1 - n1)).mul b3))).add ((Sequences.Bdd.const K).mul b4)

/-- Woodford (2003), App. E.6, p. 703: the log two-sector aggregate is of first order when the
sectoral indices and preference shocks are (from (E.27), `aggAtom_o`). -/
theorem logY2_o (hs : Tendsto s L (𝓝 0)) {n1 η Ybar : ℝ} (hn0 : 0 < n1) (hn1 : n1 < 1)
    (hη : 0 < η) (hη1 : η ≠ 1) (hY : 0 < Ybar) {f1 f2 Y1 Y2 : B → ℝ}
    (hf1 : f1 =O[L] fun b => s b ^ 1) (hf2 : f2 =O[L] fun b => s b ^ 1)
    (hY1 : Y1 =O[L] fun b => s b ^ 1) (hY2 : Y2 =O[L] fun b => s b ^ 1) :
    (fun b => BridgeExtensions.logY2 n1 η Ybar (f1 b) (f2 b) (Y1 b) (Y2 b)) =O[L]
      fun b => s b ^ 1 := by
  have hA := BridgeExtensions.o_weaken hs (by norm_num : 1 ≤ 3)
    (BridgeExtensions.aggAtom_o hs hn0 hn1 hη hη1 hY hf1 hf2 hY1 hY2)
  have hd := hf2.sub hf1
  have hD := hY2.sub hY1
  have w2 : ∀ {x y : B → ℝ}, x =O[L] (fun b => s b ^ 1) → y =O[L] (fun b => s b ^ 1) →
      (fun b => x b * y b) =O[L] fun b => s b ^ 1 := fun hx hy =>
    BridgeExtensions.o_weaken hs (by norm_num : 1 ≤ 2)
      (BridgeExtensions.o_mul hx hy (by norm_num : 1 + 1 = 2))
  have hS := (hf1.const_mul_left n1).add (hf2.const_mul_left (1 - n1))
  refine ((((((hA.add (hY1.const_mul_left n1)).add (hY2.const_mul_left (1 - n1))).add
    ((w2 hd hD).const_mul_left (η⁻¹ * n1 * (1 - n1)))).add
    ((w2 hD hD).const_mul_left (n1 * (1 - n1) * (1 - η⁻¹) / 2))).add
    (hS.const_mul_left ((1 - η⁻¹)⁻¹ * η⁻¹))).add
    ((w2 hd hd).const_mul_left (n1 * (1 - n1) * (1 - η⁻¹)⁻¹ * η⁻¹ ^ 2 / 2))).congr_left
      fun b => ?_
  unfold BridgeExtensions.aggAtom TwoSectorWelfare.ET BridgeExtensions.tauAgg
  ring

/-- Woodford (2003), **Proposition 6.11**, (4.25)/(E.32), p. 437, LAYER B FROM THE PRIMITIVES
(discounted, uniformly in the date). `BridgeExtensions.prop611_layerB` with every hypothesis
discharged:
* the per-period expansion `hP` is `BridgeExtensions.prop610_actual` on `l ×ˢ ⊤`, rewritten
  with `V_j = θ²Δ_j` ((2.12) in each sector, `Moments.crossVar_demand`) and, from the exact
  sectoral demand `Ŷ₂ − Ŷ₁ = (φ̂₂ − φ̂₁) − ηp̂_R` (`hsec`, cf. `TwoSectorWelfare.prop_6_10`),
  `(Ŷ₂ − Ŷ₁) − (Ŷ₂ⁿ − Ŷ₁ⁿ) = −η(p̂_R − p̂_Rⁿ)` with `p̂_Rⁿ = ((φ̂₂ − φ̂₁) − (Ŷ₂ⁿ − Ŷ₁ⁿ))/η`;
* the sectoral Calvo laws from the goods of each sector following the Calvo rule;
* `π̄_j − π_j = O(ε²)` uniformly (`disc_prod`), `π_j` sectoral index inflation;
* the t.i.p. is bounded for bounded disturbances (`bdd_tip2`).
`x − x* = Ŷ − Ŷⁿ` at the efficient steady state. -/
theorem prop611_primitive [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (he : Tendsto e l (𝓝 0)) {n1 η θ : ℝ} (hn0 : 0 < n1) (hn1 : n1 < 1) (hη : 0 < η)
    (hη1 : η ≠ 1) (hθ : 0 < θ) (hθ1 : θ ≠ 1) {w1 w2 : ι → ℝ} (hw10 : ∀ i, 0 ≤ w1 i)
    (hw11 : ∑ i, w1 i = 1) (hw20 : ∀ i, 0 ≤ w2 i) (hw21 : ∑ i, w2 i = 1)
    {u v : ℝ × Ξ' → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v) {Ybar σi ω : ℝ}
    (hY : 0 < Ybar) (hω : 0 ≤ ω) (hσω : 0 < σi + ω)
    (hucc : BridgeExtensions.dYY u (Ybar, 0) = -(σi * BridgeExtensions.dY u (Ybar, 0) / Ybar))
    (hvy : BridgeExtensions.dY v (Ybar, 0) = BridgeExtensions.dY u (Ybar, 0))
    (hvyy : BridgeExtensions.dYY v (Ybar, 0) = ω * BridgeExtensions.dY v (Ybar, 0) / Ybar)
    {α1 α2 β : ℝ} (ha10 : 0 < α1) (ha11 : α1 < 1) (ha20 : 0 < α2) (ha21 : α2 < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {yh1 yh2 : A → ℕ → ι → ℝ} {f1 f2 g q1 q2 pR : A → ℕ → ℝ} {xu xv1 xv2 : A → ℕ → Ξ'}
    (hnorm : ∀ a t, n1 * Real.exp (f1 a t) + (1 - n1) * Real.exp (f2 a t) = 1)
    (hg : ∀ a t, BridgeExtensions.dYXi u (Ybar, 0) (xu a t) =
      σi * BridgeExtensions.dY u (Ybar, 0) * g a t)
    (hq1 : ∀ a t, BridgeExtensions.dYXi v (Ybar, 0) (xv1 a t) =
      -(ω * BridgeExtensions.dY v (Ybar, 0) * q1 a t))
    (hq2 : ∀ a t, BridgeExtensions.dYXi v (Ybar, 0) (xv2 a t) =
      -(ω * BridgeExtensions.dY v (Ybar, 0) * q2 a t))
    (hyh1 : (fun p : A × ℕ => yh1 p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hyh2 : (fun p : A × ℕ => yh2 p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hf1 : (fun p : A × ℕ => f1 p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hf2 : (fun p : A × ℕ => f2 p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hgO : (fun p : A × ℕ => g p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hq1O : (fun p : A × ℕ => q1 p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hq2O : (fun p : A × ℕ => q2 p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hxu : (fun p : A × ℕ => xu p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hxv1 : (fun p : A × ℕ => xv1 p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hxv2 : (fun p : A × ℕ => xv2 p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hsec : ∀ a t, BridgeExtensions.logYidx w2 θ (yh2 a t) -
      BridgeExtensions.logYidx w1 θ (yh1 a t) = (f2 a t - f1 a t) - η * pR a t)
    {lp1 lp2 : A → ℕ → ι → ℝ} {R1 R2 : A → ℕ → Set ι} {ps1 ps2 : A → ℕ → ℝ}
    {LY1 LP1 LY2 LP2 : A → ℕ → ℝ}
    (hC1 : ∀ a, Links.GoodsPop.Calvo (wMeasure w1) α1 (lp1 a) (R1 a) (ps1 a) fun _ => 0)
    (hC2 : ∀ a, Links.GoodsPop.Calvo (wMeasure w2) α2 (lp2 a) (R2 a) (ps2 a) fun _ => 0)
    (hdem1 : ∀ a t i, yh1 a t i = LY1 a t - θ * (lp1 a (t + 1) i - LP1 a t))
    (hdem2 : ∀ a t i, yh2 a t i = LY2 a t - θ * (lp2 a (t + 1) i - LP2 a t))
    (hlp10 : (fun a => cen w1 (lp1 a 0)) =O[l] fun a => e a ^ 1)
    (hlp20 : (fun a => cen w2 (lp2 a 0)) =O[l] fun a => e a ^ 1)
    (hπ1 : (fun p : A × ℕ => logP w1 θ (lp1 p.1 (p.2 + 1)) - logP w1 θ (lp1 p.1 p.2))
      =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hπ2 : (fun p : A × ℕ => logP w2 θ (lp2 p.1 (p.2 + 1)) - logP w2 θ (lp2 p.1 p.2))
      =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hxuB : ∀ a, ∃ M, ∀ t, ‖xu a t‖ ≤ M) (hxv1B : ∀ a, ∃ M, ∀ t, ‖xv1 a t‖ ≤ M)
    (hxv2B : ∀ a, ∃ M, ∀ t, ‖xv2 a t‖ ≤ M) (hf1B : ∀ a, Sequences.Bdd (f1 a))
    (hf2B : ∀ a, Sequences.Bdd (f2 a)) (hgB : ∀ a, Sequences.Bdd (g a))
    (hq1B : ∀ a, Sequences.Bdd (q1 a)) (hq2B : ∀ a, Sequences.Bdd (q2 a)) :
    (fun a => ∑' t, β ^ t * BridgeExtensions.periodU2 u v n1 η θ Ybar w1 w2 (f1 a t) (f2 a t)
        (yh1 a t) (yh2 a t) (xu a t) (xv1 a t) (xv2 a t) -
      (-(Ybar * BridgeExtensions.dY u (Ybar, 0) / 2 *
          (θ * (σi + ω) / TwoSectorWelfare.kappaH n1 (Moments.calvoKappa α1 β ω θ σi)
            (Moments.calvoKappa α2 β ω θ σi))) *
        ∑' t, β ^ t * TwoSectorWelfare.loss425
          (TwoSectorWelfare.wJ n1 (Moments.calvoKappa α1 β ω θ σi)
            (TwoSectorWelfare.kappaH n1 (Moments.calvoKappa α1 β ω θ σi)
              (Moments.calvoKappa α2 β ω θ σi)))
          (TwoSectorWelfare.wJ (1 - n1) (Moments.calvoKappa α2 β ω θ σi)
            (TwoSectorWelfare.kappaH n1 (Moments.calvoKappa α1 β ω θ σi)
              (Moments.calvoKappa α2 β ω θ σi)))
          (TwoSectorWelfare.lamX (TwoSectorWelfare.kappaH n1 (Moments.calvoKappa α1 β ω θ σi)
            (Moments.calvoKappa α2 β ω θ σi)) θ)
          (TwoSectorWelfare.lamR n1 η ω σi (TwoSectorWelfare.kappaH n1
            (Moments.calvoKappa α1 β ω θ σi) (Moments.calvoKappa α2 β ω θ σi)) θ)
          (logP w1 θ (lp1 a (t + 1)) - logP w1 θ (lp1 a t))
          (logP w2 θ (lp2 a (t + 1)) - logP w2 θ (lp2 a t))
          (BridgeExtensions.logY2 n1 η Ybar (f1 a t) (f2 a t)
              (BridgeExtensions.logYidx w1 θ (yh1 a t)) (BridgeExtensions.logYidx w2 θ (yh2 a t)) -
            TwoSectorWelfare.natY σi ω n1 (g a t) (q1 a t) (q2 a t)) 0
          (pR a t - ((f2 a t - f1 a t) - TwoSectorWelfare.natD η⁻¹ ω (f2 a t - f1 a t) (q1 a t)
            (q2 a t)) / η) +
        (∑' t, β ^ t * (BridgeExtensions.tip2 u v n1 Ybar (xu a t) (xv1 a t) (xv2 a t) +
            Ybar * BridgeExtensions.dY u (Ybar, 0) * TwoSectorWelfare.tip610 σi ω η⁻¹ n1 0 (g a t)
              (q1 a t) (q2 a t) (f2 a t - f1 a t)
              (BridgeExtensions.tauAgg η⁻¹ n1 (f1 a t) (f2 a t))) -
          Ybar * BridgeExtensions.dY u (Ybar, 0) / 2 * (θ * (1 + ω * θ)) *
            (n1 * (α1 * crossVar w1 (lp1 a 0) / (1 - α1 * β)) +
              (1 - n1) * (α2 * crossVar w2 (lp2 a 0) / (1 - α2 * β))))))
      =O[l] fun a => e a ^ 3 := by
  have hs := BridgeExtensions.tendsto_amp (J := ℕ) he
  have hηω : η⁻¹ + ω ≠ 0 := by have := inv_pos.2 hη; linarith
  have hY1 := BridgeExtensions.logYidx_o hs hw10 hw11 hθ1 hyh1
  have hY2 := BridgeExtensions.logYidx_o hs hw20 hw21 hθ1 hyh2
  have hW := BridgeExtensions.prop610_actual hs hn0 hn1 hη hη1 hθ1 hw10 hw11 hw20 hw21 hu hv hY
    hσω.ne' hηω hucc hvy hvyy (fun p => hnorm p.1 p.2) (fun p => hg p.1 p.2)
    (fun p => hq1 p.1 p.2) (fun p => hq2 p.1 p.2) hyh1 hyh2 hf1 hf2 hgO hq1O hq2O hxu hxv1 hxv2
  have hV : ∀ {w : ι → ℝ} {yh lp : A → ℕ → ι → ℝ} {LY LP : A → ℕ → ℝ}, ∑ i, w i = 1 →
      (∀ a t i, yh a t i = LY a t - θ * (lp a (t + 1) i - LP a t)) →
      ∀ a t, crossVar w (yh a t) = θ ^ 2 * crossVar w (lp a (t + 1)) :=
    fun {w} {yh} {lp} {LY} {LP} hw1 hdem a t => by
      rw [show yh a t = fun i => LY a t - θ * (lp a (t + 1) i - LP a t) from funext (hdem a t),
        Moments.crossVar_demand hw1]
  have hΔ : ∀ {w : ι → ℝ} {yh lp : A → ℕ → ι → ℝ} {LY LP : A → ℕ → ℝ}, (∀ i, 0 ≤ w i) →
      ∑ i, w i = 1 → (∀ a t i, yh a t i = LY a t - θ * (lp a (t + 1) i - LP a t)) →
      (fun p : A × ℕ => yh p.1 p.2) =O[l ×ˢ ⊤] (fun p => e p.1 ^ 1) →
      (fun p : A × ℕ => crossVar w (lp p.1 (p.2 + 1))) =O[l ×ˢ ⊤] fun p => e p.1 ^ 2 :=
    fun {w} {yh} {lp} {LY} {LP} hw0 hw1 hdem hyh =>
      ((BridgeExtensions.crossVar_o hw0 hw1 hyh).const_mul_left (θ ^ 2)⁻¹).congr_left
        fun p => by rw [hV hw1 hdem]; field_simp
  have hx := (logY2_o hs hn0 hn1 hη hη1 hY hf1 hf2 hY1 hY2).sub
    ((((hgO.const_mul_left σi).add (((hq1O.const_mul_left n1).add
      (hq2O.const_mul_left (1 - n1))).const_mul_left ω))).const_mul_left (σi + ω)⁻¹)
  have hgR : (fun p : A × ℕ => pR p.1 p.2 - ((f2 p.1 p.2 - f1 p.1 p.2) -
      TwoSectorWelfare.natD η⁻¹ ω (f2 p.1 p.2 - f1 p.1 p.2) (q1 p.1 p.2) (q2 p.1 p.2)) / η)
      =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 := by
    have hd := hf2.sub hf1
    have hn : (fun p : A × ℕ => TwoSectorWelfare.natD η⁻¹ ω (f2 p.1 p.2 - f1 p.1 p.2)
        (q1 p.1 p.2) (q2 p.1 p.2)) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 :=
      (((hd.const_mul_left η⁻¹).add ((hq2O.sub hq1O).const_mul_left ω)).const_mul_left
        (η⁻¹ + ω)⁻¹).congr_left fun p => by unfold TwoSectorWelfare.natD; ring
    refine ((((hd.sub (hY2.sub hY1)).const_mul_left η⁻¹)).sub
      ((hd.sub hn).const_mul_left η⁻¹)).congr_left fun p => ?_
    rw [hsec p.1 p.2]
    field_simp
    ring
  exact BridgeExtensions.prop611_layerB ha10 ha11 ha20 ha21 hβ0 hβ1 hn0 hn1 hθ
    (by nlinarith) hσω he (K := Ybar * BridgeExtensions.dY u (Ybar, 0)) (xs := 0)
    (W := fun a t => BridgeExtensions.periodU2 u v n1 η θ Ybar w1 w2 (f1 a t) (f2 a t)
      (yh1 a t) (yh2 a t) (xu a t) (xv1 a t) (xv2 a t))
    (τ := fun a t => BridgeExtensions.tip2 u v n1 Ybar (xu a t) (xv1 a t) (xv2 a t) +
      Ybar * BridgeExtensions.dY u (Ybar, 0) * TwoSectorWelfare.tip610 σi ω η⁻¹ n1 0 (g a t)
        (q1 a t) (q2 a t) (f2 a t - f1 a t) (BridgeExtensions.tauAgg η⁻¹ n1 (f1 a t) (f2 a t)))
    (x := fun a t => BridgeExtensions.logY2 n1 η Ybar (f1 a t) (f2 a t)
      (BridgeExtensions.logYidx w1 θ (yh1 a t)) (BridgeExtensions.logYidx w2 θ (yh2 a t)) -
        TwoSectorWelfare.natY σi ω n1 (g a t) (q1 a t) (q2 a t))
    (gR := fun a t => pR a t - ((f2 a t - f1 a t) - TwoSectorWelfare.natD η⁻¹ ω (f2 a t - f1 a t)
      (q1 a t) (q2 a t)) / η)
    (π1 := fun a t => logP w1 θ (lp1 a (t + 1)) - logP w1 θ (lp1 a t))
    (π2 := fun a t => logP w2 θ (lp2 a (t + 1)) - logP w2 θ (lp2 a t))
    (pb1 := fun a t => crossMean w1 (lp1 a (t + 1)) - crossMean w1 (lp1 a t))
    (pb2 := fun a t => crossMean w2 (lp2 a (t + 1)) - crossMean w2 (lp2 a t))
    (Δ1 := fun a t => crossVar w1 (lp1 a (t + 1))) (Δ2 := fun a t => crossVar w2 (lp2 a (t + 1)))
    (Δ1m := fun a => crossVar w1 (lp1 a 0)) (Δ2m := fun a => crossVar w2 (lp2 a 0))
    (fun a => bdd_tip2 u v n1 η Ybar _ σi ω (hxuB a) (hxv1B a) (hxv2B a) (hf1B a) (hf2B a)
      (hgB a) (hq1B a) (hq2B a))
    (hW.congr_left fun p => by
      have h := hsec p.1 p.2
      simp only [BridgeExtensions.loss610, hV hw11 hdem1, hV hw21 hdem2]
      rw [h]
      field_simp
      ring)
    (hx.congr_left fun p => by simp only [TwoSectorWelfare.natY]; ring) hgR hπ1 hπ2
    (hΔ hw10 hw11 hdem1 hyh1) (hΔ hw20 hw21 hdem2 hyh2)
    (disc_prod hw10 hw11 hθ.ne' hθ1 he hdem1 hyh1 hlp10)
    (disc_prod hw20 hw21 hθ.ne' hθ1 he hdem2 hyh2 hlp20)
    (fun a => by simpa using goods_rec_fin hw10 hw11 ha11.ne (hC1 a) 0)
    (fun a t => by simpa using goods_rec_fin hw10 hw11 ha11.ne (hC1 a) (t + 1))
    (fun a => by simpa using goods_rec_fin hw20 hw21 ha21.ne (hC2 a) 0)
    (fun a t => by simpa using goods_rec_fin hw20 hw21 ha21.ne (hC2 a) (t + 1))

/-! ## Proposition 6.6 (Layer B) under genuine uncertainty -/

namespace Habit

open BridgeCore BridgeCore.Econ
open Prop61 (gShock)

/-- Woodford (2003), **Proposition 6.6 (corrected)**, (2.27)/(E.9), pp. 403–404, 696–698, Layer B
along ONE PATH WITHOUT the flexible-price relation (restated from `BridgeCore.Econ.prop66_bridge`,
whose proof is followed verbatim except at the last step): the realised flexible-price residual
term `−Ȳu_c(1 − βη)∑βᵗr_t(ε)x_t(ε)` is kept explicitly,
`∑βᵗU_t(ε) = TIP(ε) − Ȳu_c(1 − βη)∑βᵗr_tx_t − (ε²/2)Ȳu_c∑βᵗ[μ_x(x₁ − δx₁₋₁)² +
(1 − βη)(θ⁻¹ + ω)var_i y₁] + O(ε³)`. Under perfect foresight with `r = 0` it is
`prop66_bridge`; under uncertainty the residual term vanishes in `E₀` (`prop66_expected`). -/
theorem prop66_bridge_rx {M : Econ Ξ ι} (hM : M.Std) {P : HabitWelfare.Par} (hP : P.Std)
    {Gbar cbar : ℝ}
    (hPs : P.sinv = M.sigH cbar) (hPΦ : P.Φ = 0) (hPω : P.ω = M.omg) (hPθ : P.θ = M.θ)
    (hcbar : cbar = (1 - P.η) * (M.Yb - Gbar)) (huc : 0 < M.ucH cbar)
    (hucc : M.uccH cbar ≠ 0) (heff : M.vy = (1 - P.β * P.η) * M.ucH cbar)
    {e1 : HabitWelfare.Exo} {ξ1 : ℕ → Ξ} (hgp : ∀ t, e1.gp t = M.gpH cbar (ξ1 t))
    (hq : ∀ t, e1.q t = M.qS (ξ1 t)) (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C)
    (hG1 : Sequences.Bdd e1.G) (hn1 : Sequences.Bdd e1.n)
    {yh : ℕ → ℝ → ι → ℝ} {y1 : ℕ → ι → ℝ}
    (h : (fun p : ℕ × ℝ => yh p.1 p.2 - p.2 • y1 p.1) =O[unif] fun p => p.2 ^ 2)
    (hy1 : ∃ C, ∀ t, ‖y1 t‖ ≤ C) {Ym1 : ℝ → ℝ} {Y1m1 : ℝ}
    (hYm1 : (fun ε => Ym1 ε - ε * Y1m1) =O[𝓝 0] fun ε => ε ^ 2) :
    (fun ε => ∑' t, P.β ^ t * M.Uhab P.η Gbar (yh t ε)
        (Sequences.lagS (Ym1 ε) (fun s => M.Yagg (yh s ε)) t) (ε * e1.G t)
        (Sequences.lagS (ε * e1.Gm1) (fun s => ε * e1.G s) t) (ε • ξ1 t) -
      ((∑' t, P.β ^ t * (tip0 M.u cbar (ε • ξ1 t) - tip0 M.v M.Yb (ε • ξ1 t)) +
          M.Yb * M.ucH cbar * HabitWelfare.tipTotal P (exoSmul ε e1) (Ym1 ε) -
          M.Yb * M.ucH cbar * (1 - P.β * P.η) * ∑' t, P.β ^ t *
            (HabitWelfare.rS P (exoSmul ε e1) t *
              HabitWelfare.xS (exoSmul ε e1) (fun s => M.Yagg (yh s ε)) t)) +
        ε ^ 2 / 2 * (-(M.Yb * M.ucH cbar * ∑' t, P.β ^ t *
          (P.muX * HabitWelfare.gapSq P e1 Y1m1 (fun s => crossMean M.w (y1 s)) t +
            (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) * crossVar M.w (y1 t)))))) =O[𝓝 0]
      fun ε => ε ^ 3 := by
  have hβ0 : 0 ≤ P.β := hP.1
  have hβ1 : P.β < 1 := hP.2.1
  have hβη : 0 < 1 - P.β * P.η := by
    have := hP.2.2.1; have := hP.2.2.2.1; nlinarith
  have hw := hM.w_nonneg
  have hw1 := hM.w_sum
  -- uniform orders of the state variables
  have hy1u := unif_of_bounded hy1
  have hx1 := unif_of_bounded hξ1
  have hyu : (fun p : ℕ × ℝ => yh p.1 p.2) =O[unif] fun p => p.2 :=
    family_isBigO (s := fun p : ℕ × ℝ => p.2) tendsto_unif h hy1u
  obtain ⟨-, hVu, heu, hYu⟩ := ces_orders hw hw1 (r_ne hM) tendsto_unif hyu
  have hYm1' : Ym1 =O[𝓝 0] fun ε => ε := by
    have h2 : (fun ε : ℝ => Ym1 ε - ε * Y1m1) =O[𝓝 0] fun ε => ε :=
      (hYm1.trans (pow_isBigO_pow (s := fun ε : ℝ => ε) tendsto_id
        (by norm_num : 1 ≤ 2))).congr_right fun ε => pow_one ε
    exact (h2.add ((isBigO_refl (fun ε : ℝ => ε) (𝓝 0)).const_mul_left Y1m1)).congr_left
      fun ε => by ring
  have hYlag := lag_unif (F := fun t ε => M.Yagg (yh t ε)) (A := Ym1) (g := fun ε => ε) hYu
    hYm1'
  obtain ⟨CG, hCG⟩ := hG1
  have hG1u : (fun p : ℕ × ℝ => e1.G p.1) =O[unif] fun _ => (1 : ℝ) :=
    unif_of_bounded ⟨CG, fun t => by simpa using hCG t⟩
  have hGu : (fun p : ℕ × ℝ => p.2 * e1.G p.1) =O[unif] fun p => p.2 :=
    ((isBigO_refl (fun p : ℕ × ℝ => p.2) unif).mul hG1u).congr_right fun _ => mul_one _
  have hGlb : Sequences.Bdd (Sequences.lagS e1.Gm1 e1.G) := Sequences.Bdd.lagS ⟨CG, hCG⟩ _
  obtain ⟨CGl, hCGl⟩ := hGlb
  have hGlag : (fun p : ℕ × ℝ => Sequences.lagS (p.2 * e1.Gm1) (fun s => p.2 * e1.G s) p.1)
      =O[unif] fun p => p.2 :=
    (((isBigO_refl (fun p : ℕ × ℝ => p.2) unif).mul (unif_of_bounded (f := fun t =>
      Sequences.lagS e1.Gm1 e1.G t) ⟨CGl, fun t => by simpa using hCGl t⟩)).congr_right
        fun _ => mul_one _).congr_left fun p => (lagS_smul _ _ _ _).symm
  have hξu : (fun p : ℕ × ℝ => p.2 • ξ1 p.1) =O[unif] fun p => p.2 :=
    ((isBigO_refl (fun p : ℕ × ℝ => p.2) unif).smul hx1).congr_right fun _ => mul_one _
  -- the period bridge, uniformly in `t`
  have hρ0 := habit_state (l := unif) (s := fun p : ℕ × ℝ => p.2) hM hPs hPΦ hPω hPθ hcbar
    hβη.ne' huc hucc heff tendsto_unif hyu hYlag hGu hGlag hξu
  have hρ : (fun p : ℕ × ℝ => M.Uhab P.η Gbar (yh p.1 p.2)
      (Sequences.lagS (Ym1 p.2) (fun s => M.Yagg (yh s p.2)) p.1) (p.2 * e1.G p.1)
      (Sequences.lagS (p.2 * e1.Gm1) (fun s => p.2 * e1.G s) p.1) (p.2 • ξ1 p.1) -
      ((tip0 M.u cbar (p.2 • ξ1 p.1) - tip0 M.v M.Yb (p.2 • ξ1 p.1)) + M.Yb * M.ucH cbar *
        HabitWelfare.Useq P (exoSmul p.2 e1) (Ym1 p.2) (fun s => M.Yagg (yh s p.2))
          (fun s => crossVar M.w (yh s p.2)) p.1)) =O[unif] fun p => p.2 ^ 3 := by
    refine hρ0.congr_left fun p => ?_
    rw [Useq_eq_at]
    dsimp only [exoSmul]
    rw [hgp, hq, gpH_smul, M.qS_smul]
  -- the remainder of the Layer-A identity, uniformly in `t`
  have hgpb : (fun p : ℕ × ℝ => e1.gp p.1) =O[unif] fun _ => (1 : ℝ) :=
    ((cross_isBigO M.u cbar hx1).const_mul_left (-(M.Yb * M.uccH cbar)⁻¹)).congr_left
      fun p => by rw [hgp]; unfold gpH gShock; ring
  have hqb : (fun p : ℕ × ℝ => e1.q p.1) =O[unif] fun _ => (1 : ℝ) :=
    (M.qS_isBigO hx1).congr_left fun p => (hq p.1).symm
  have hgpu : (fun p : ℕ × ℝ => p.2 * e1.gp p.1) =O[unif] fun p => p.2 :=
    ((isBigO_refl (fun p : ℕ × ℝ => p.2) unif).mul hgpb).congr_right fun _ => mul_one _
  have hqu : (fun p : ℕ × ℝ => p.2 * e1.q p.1) =O[unif] fun p => p.2 :=
    ((isBigO_refl (fun p : ℕ × ℝ => p.2) unif).mul hqb).congr_right fun _ => mul_one _
  have hRU : (fun p : ℕ × ℝ => HabitWelfare.RUseq P (exoSmul p.2 e1) (Ym1 p.2)
      (fun s => M.Yagg (yh s p.2)) (fun s => crossVar M.w (yh s p.2)) p.1) =O[unif]
      fun p => p.2 ^ 3 := by
    refine ((E10rem_isBigO tendsto_unif P.sinv P.η hYu hYlag hGu hGlag hgpu).sub
      ((vRem_isBigO tendsto_unif P.θ P.ω hYu hqu hVu).const_mul_left
        (1 - P.β * P.η))).congr_left fun p => ?_
    unfold HabitWelfare.RUseq
    dsimp only [exoSmul]
    rw [hPΦ]
    rfl
  -- the gap, uniformly in `t`
  have hY1b : (fun p : ℕ × ℝ => crossMean M.w (y1 p.1)) =O[unif] fun _ => (1 : ℝ) :=
    crossMean_isBigO hw hw1 hy1u
  have hD0 : (fun p : ℕ × ℝ => M.Yagg (yh p.1 p.2) - p.2 * crossMean M.w (y1 p.1)) =O[unif]
      fun p => p.2 ^ 2 :=
    (((heu.trans (pow_isBigO_pow tendsto_unif (by norm_num : 2 ≤ 3))).add
      (hVu.const_mul_left ((1 - M.θ⁻¹) / 2))).add (crossMean_isBigO hw hw1 h)).congr_left
        fun p => by rw [crossMean_sub', crossMean_smul']; unfold Yagg; ring
  have hlagD := lag_unif (F := fun t ε => M.Yagg (yh t ε) - ε * crossMean M.w (y1 t))
    (A := fun ε => Ym1 ε - ε * Y1m1) (g := fun ε => ε ^ 2) hD0 hYm1
  have hxhat := HabitWelfare.xhat_of_Phi_zero hPΦ
  have ha : (fun p : ℕ × ℝ =>
      (HabitWelfare.xS (exoSmul p.2 e1) (fun s => M.Yagg (yh s p.2)) p.1 -
        P.δ * Sequences.lagS (Ym1 p.2 - (exoSmul p.2 e1).nm1)
          (HabitWelfare.xS (exoSmul p.2 e1) (fun s => M.Yagg (yh s p.2))) p.1 - P.xhat) -
      p.2 * (HabitWelfare.xS e1 (fun s => crossMean M.w (y1 s)) p.1 -
        P.δ * Sequences.lagS (Y1m1 - e1.nm1) (HabitWelfare.xS e1 (fun s => crossMean M.w (y1 s)))
          p.1 - P.xhat)) =O[unif] fun p => p.2 ^ 2 := by
    refine (hD0.sub (hlagD.const_mul_left P.δ)).congr_left fun p => ?_
    obtain ⟨t, ε⟩ := p
    rw [hxhat]
    cases t <;> simp only [Sequences.lagS, HabitWelfare.xS, exoSmul] <;> ring
  have hx1b : Sequences.Bdd (fun t => HabitWelfare.xS e1 (fun s => crossMean M.w (y1 s)) t -
      P.δ * Sequences.lagS (Y1m1 - e1.nm1) (HabitWelfare.xS e1 (fun s => crossMean M.w (y1 s)))
        t - P.xhat) := by
    have hm : Sequences.Bdd (fun s => crossMean M.w (y1 s)) :=
      bounded_of_unif (f := fun s => crossMean M.w (y1 s)) hY1b
    have hxs : Sequences.Bdd (HabitWelfare.xS e1 (fun s => crossMean M.w (y1 s))) := hm.sub hn1
    exact (hxs.sub ((Sequences.Bdd.const _).mul (hxs.lagS _))).sub (Sequences.Bdd.const _)
  have ha1 : (fun p : ℕ × ℝ => HabitWelfare.xS e1 (fun s => crossMean M.w (y1 s)) p.1 -
      P.δ * Sequences.lagS (Y1m1 - e1.nm1) (HabitWelfare.xS e1 (fun s => crossMean M.w (y1 s)))
        p.1 - P.xhat) =O[unif] fun _ => (1 : ℝ) :=
    unif_of_bdd (f := fun t => HabitWelfare.xS e1 (fun s => crossMean M.w (y1 s)) t -
      P.δ * Sequences.lagS (Y1m1 - e1.nm1) (HabitWelfare.xS e1 (fun s => crossMean M.w (y1 s)))
        t - P.xhat) hx1b
  have hgap := sq_sub_sq_isBigO tendsto_unif ha ha1
  have hVd := crossVar_family hw hw1 tendsto_unif h hy1u
  -- discounted sums of the three uniform remainders
  have S1 := tsum_isBigO_of_unif (f := fun t ε => M.Uhab P.η Gbar (yh t ε)
      (Sequences.lagS (Ym1 ε) (fun s => M.Yagg (yh s ε)) t) (ε * e1.G t)
      (Sequences.lagS (ε * e1.Gm1) (fun s => ε * e1.G s) t) (ε • ξ1 t) -
      ((tip0 M.u cbar (ε • ξ1 t) - tip0 M.v M.Yb (ε • ξ1 t)) + M.Yb * M.ucH cbar *
        HabitWelfare.Useq P (exoSmul ε e1) (Ym1 ε) (fun s => M.Yagg (yh s ε))
          (fun s => crossVar M.w (yh s ε)) t)) hβ0 hβ1 hρ
  have S2 := tsum_isBigO_of_unif (f := fun t ε => HabitWelfare.RUseq P (exoSmul ε e1) (Ym1 ε)
      (fun s => M.Yagg (yh s ε)) (fun s => crossVar M.w (yh s ε)) t) hβ0 hβ1 hRU
  have S3 := tsum_isBigO_of_unif (f := fun t ε =>
      P.muX * (HabitWelfare.gapSq P (exoSmul ε e1) (Ym1 ε) (fun s => M.Yagg (yh s ε)) t -
        ε ^ 2 * HabitWelfare.gapSq P e1 Y1m1 (fun s => crossMean M.w (y1 s)) t) +
      (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) * (crossVar M.w (yh t ε) - ε ^ 2 * crossVar M.w (y1 t)))
      hβ0 hβ1 ((hgap.const_mul_left P.muX).add (hVd.const_mul_left _))
  have hcomb := (S1.add (S2.const_mul_left (M.Yb * M.ucH cbar))).sub
    (S3.const_mul_left (M.Yb * M.ucH cbar / 2))
  -- boundedness for each small `ε`
  have one : (fun p : ℕ × ℝ => p.2) =O[unif] fun _ => (1 : ℝ) := tendsto_unif.isBigO_one ℝ
  have b2 : ∀ {n : ℕ}, (fun p : ℕ × ℝ => p.2 ^ n) =O[unif] fun _ => (1 : ℝ) := fun {n} =>
    (one.pow n).congr_right fun _ => one_pow n
  have hab : (fun p : ℕ × ℝ =>
      HabitWelfare.xS (exoSmul p.2 e1) (fun s => M.Yagg (yh s p.2)) p.1 -
        P.δ * Sequences.lagS (Ym1 p.2 - (exoSmul p.2 e1).nm1)
          (HabitWelfare.xS (exoSmul p.2 e1) (fun s => M.Yagg (yh s p.2))) p.1 - P.xhat)
      =O[unif] fun _ => (1 : ℝ) :=
    ((ha.trans b2).add ((one.mul ha1).congr_right fun _ => mul_one 1)).congr_left
      fun p => by ring
  obtain ⟨Cy, hCy⟩ := hy1
  have bV1 : Sequences.Bdd (fun t => crossVar M.w (y1 t)) := ⟨Cy ^ 2, fun t => by
    have h := ExpLogCES.crossVar_le hw hw1 (y1 t)
    rw [abs_of_nonneg h.1]
    exact h.2.trans (pow_le_pow_left₀ (norm_nonneg _) (hCy t) 2)⟩
  have bB : Sequences.Bdd (fun t => P.muX * HabitWelfare.gapSq P e1 Y1m1
      (fun s => crossMean M.w (y1 s)) t + (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) *
        crossVar M.w (y1 t)) :=
    ((Sequences.Bdd.const _).mul (hx1b.pow 2)).add ((Sequences.Bdd.const _).mul bV1)
  have bgp1 : Sequences.Bdd e1.gp := bounded_of_unif (f := e1.gp) hgpb
  have bq1 : Sequences.Bdd e1.q := bounded_of_unif (f := e1.q) hqb
  have bG1 : Sequences.Bdd e1.G := ⟨CG, hCG⟩
  refine hcomb.congr' ?_ EventuallyEq.rfl
  filter_upwards [bdd_of_unif (f := fun t ε => M.Yagg (yh t ε)) (g := fun ε => ε) hYu,
    bdd_of_unif (f := fun t ε => crossVar M.w (yh t ε)) (g := fun ε => ε ^ 2) hVu,
    bdd_of_unif (f := fun t ε => tip0 M.u cbar (ε • ξ1 t) - tip0 M.v M.Yb (ε • ξ1 t))
      (g := fun _ => (1 : ℝ)) ((tip0_unif M.u cbar hξ1).sub (tip0_unif M.v M.Yb hξ1)),
    bdd_of_unif (f := fun t ε => M.Uhab P.η Gbar (yh t ε)
      (Sequences.lagS (Ym1 ε) (fun s => M.Yagg (yh s ε)) t) (ε * e1.G t)
      (Sequences.lagS (ε * e1.Gm1) (fun s => ε * e1.G s) t) (ε • ξ1 t) -
      ((tip0 M.u cbar (ε • ξ1 t) - tip0 M.v M.Yb (ε • ξ1 t)) + M.Yb * M.ucH cbar *
        HabitWelfare.Useq P (exoSmul ε e1) (Ym1 ε) (fun s => M.Yagg (yh s ε))
          (fun s => crossVar M.w (yh s ε)) t)) (g := fun ε => ε ^ 3) hρ,
    bdd_of_unif (f := fun t ε =>
      HabitWelfare.xS (exoSmul ε e1) (fun s => M.Yagg (yh s ε)) t -
        P.δ * Sequences.lagS (Ym1 ε - (exoSmul ε e1).nm1)
          (HabitWelfare.xS (exoSmul ε e1) (fun s => M.Yagg (yh s ε))) t - P.xhat)
      (g := fun _ => (1 : ℝ)) hab] with ε bY bV bT bρ bX
  have hb : (exoSmul ε e1).Bounded :=
    ⟨(Sequences.Bdd.const ε).mul bG1, (Sequences.Bdd.const ε).mul bgp1,
      (Sequences.Bdd.const ε).mul bq1, (Sequences.Bdd.const ε).mul hn1⟩
  have bUs : Sequences.Bdd (fun t => HabitWelfare.Useq P (exoSmul ε e1) (Ym1 ε)
      (fun s => M.Yagg (yh s ε)) (fun s => crossVar M.w (yh s ε)) t) := by
    have := bdd_UseqAt P bY (bY.lagS (Ym1 ε)) ((Sequences.Bdd.const ε).mul bG1)
      (((Sequences.Bdd.const ε).mul bG1).lagS (ε * e1.Gm1)) ((Sequences.Bdd.const ε).mul bgp1)
      ((Sequences.Bdd.const ε).mul bq1) bV
    exact this
  have bA : Sequences.Bdd (fun t => P.muX * HabitWelfare.gapSq P (exoSmul ε e1) (Ym1 ε)
      (fun s => M.Yagg (yh s ε)) t + (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) *
        crossVar M.w (yh t ε)) :=
    ((Sequences.Bdd.const _).mul (bX.pow 2)).add ((Sequences.Bdd.const _).mul bV)
  have h66 := HabitWelfare.prop66_corrected hP (exoSmul ε e1) (Ym1 ε)
    (fun s => M.Yagg (yh s ε)) (fun s => crossVar M.w (yh s ε)) bY bV hb
  have sT := bT.summable hβ0 hβ1
  have sU := bUs.summable hβ0 hβ1
  have sρ := bρ.summable hβ0 hβ1
  have e_U : ∑' t, P.β ^ t * M.Uhab P.η Gbar (yh t ε)
        (Sequences.lagS (Ym1 ε) (fun s => M.Yagg (yh s ε)) t) (ε * e1.G t)
        (Sequences.lagS (ε * e1.Gm1) (fun s => ε * e1.G s) t) (ε • ξ1 t) =
      ∑' t, P.β ^ t * (tip0 M.u cbar (ε • ξ1 t) - tip0 M.v M.Yb (ε • ξ1 t)) +
        M.Yb * M.ucH cbar * ∑' t, P.β ^ t * HabitWelfare.Useq P (exoSmul ε e1) (Ym1 ε)
          (fun s => M.Yagg (yh s ε)) (fun s => crossVar M.w (yh s ε)) t +
        ∑' t, P.β ^ t * (M.Uhab P.η Gbar (yh t ε)
          (Sequences.lagS (Ym1 ε) (fun s => M.Yagg (yh s ε)) t) (ε * e1.G t)
          (Sequences.lagS (ε * e1.Gm1) (fun s => ε * e1.G s) t) (ε • ξ1 t) -
          ((tip0 M.u cbar (ε • ξ1 t) - tip0 M.v M.Yb (ε • ξ1 t)) + M.Yb * M.ucH cbar *
            HabitWelfare.Useq P (exoSmul ε e1) (Ym1 ε) (fun s => M.Yagg (yh s ε))
              (fun s => crossVar M.w (yh s ε)) t)) := by
    rw [← tsum_mul_left, ← sT.tsum_add (sU.mul_left _), ← (sT.add (sU.mul_left _)).tsum_add sρ]
    exact tsum_congr fun t => by ring
  have e_A : ∑' t, P.β ^ t *
      (P.muX * (HabitWelfare.gapSq P (exoSmul ε e1) (Ym1 ε) (fun s => M.Yagg (yh s ε)) t -
        ε ^ 2 * HabitWelfare.gapSq P e1 Y1m1 (fun s => crossMean M.w (y1 s)) t) +
      (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) *
        (crossVar M.w (yh t ε) - ε ^ 2 * crossVar M.w (y1 t))) =
      ∑' t, P.β ^ t * (P.muX * HabitWelfare.gapSq P (exoSmul ε e1) (Ym1 ε)
        (fun s => M.Yagg (yh s ε)) t + (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) *
          crossVar M.w (yh t ε)) -
      ε ^ 2 * ∑' t, P.β ^ t * (P.muX * HabitWelfare.gapSq P e1 Y1m1
        (fun s => crossMean M.w (y1 s)) t + (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) *
          crossVar M.w (y1 t)) := by
    rw [← tsum_mul_left, ← (bA.summable hβ0 hβ1).tsum_sub ((bB.summable hβ0 hβ1).mul_left _)]
    exact tsum_congr fun t => by ring
  rw [e_U, h66]
  linear_combination (-(M.Yb * M.ucH cbar / 2)) * e_A


/-- Woodford (2003), App. E.3, p. 697: on a finite state space, a process bounded along each
path is uniformly bounded. -/
theorem ubdd_of_finite {Ω : Type*} [Finite Ω] {x : ℕ → Ω → ℝ}
    (h : ∀ ω, Sequences.Bdd fun t => x t ω) : HabitWelfare.UBdd x := by
  have := Fintype.ofFinite Ω
  choose M hM using h
  refine ⟨∑ ω, |M ω|, fun p => (hM p.2 p.1).trans ((le_abs_self _).trans ?_)⟩
  exact Finset.single_le_sum (f := fun ω => |M ω|) (fun ω _ => abs_nonneg _)
    (Finset.mem_univ p.2)

/-- Woodford (2003), p. 697: the realised flexible-price residual of bounded exogenous data is a
bounded sequence. -/
theorem bdd_rS (P : HabitWelfare.Par) {e : HabitWelfare.Exo} (he : e.Bounded) :
    Sequences.Bdd (HabitWelfare.rS P e) := by
  obtain ⟨hG, hgp, hq, hn⟩ := he
  unfold HabitWelfare.rS HabitWelfare.gTil HabitWelfare.gS
  aesop (add safe apply [Sequences.Bdd.add, Sequences.Bdd.sub, Sequences.Bdd.mul,
    Sequences.Bdd.neg, Sequences.Bdd.div_const, Sequences.Bdd.pow, Sequences.Bdd.shift,
    Sequences.Bdd.lagS, Sequences.Bdd.const])

/-- Woodford (2003), **Proposition 6.6 (corrected), (2.27)/(E.9), pp. 403–404, 696–698, LAYER B
UNDER GENUINE UNCERTAINTY**. A finite state space `Ω` (each state a path) with an arbitrary
`ExpectationSystem` having the pull-out property (every finite tree has it,
`ExpectationsFiniteTree.finiteTree_pullOut`). In each state the hypotheses of
`prop66_bridge_rx` hold (first-order family uniform in `t`, bounded first-order data). Output is
adapted, the natural rate is adapted, and the first-order natural rate satisfies the book's
flexible-price relation IN EXPECTATION, `E_t r_t = 0` (`HabitWelfare.flexE_iff`), NOT pathwise.
Then
`E₀∑βᵗU_t(ε) = E₀TIP(ε) − (ε²/2)Ȳu_c E₀∑βᵗ[μ_x(x₁ − δx₁₋₁)² + (1 − βη)(θ⁻¹ + ω)var_i y₁]
+ O(ε³)`: the realised residual term `r_tx_t` vanishes in `E₀` (`HabitWelfare.E0_tsum_mul_zero`)
and the pathwise `O(ε³)` remainders, uniform in `t`, are uniform over the finitely many states. -/
theorem prop66_expected {Ω : Type*} [Finite Ω] (𝔼 : ExpectationSystem Ω) (hPO : 𝔼.PullOut)
    {M : Econ Ξ ι} (hM : M.Std) {P : HabitWelfare.Par} (hP : P.Std) {Gbar cbar : ℝ}
    (hPs : P.sinv = M.sigH cbar) (hPΦ : P.Φ = 0) (hPω : P.ω = M.omg) (hPθ : P.θ = M.θ)
    (hcbar : cbar = (1 - P.η) * (M.Yb - Gbar)) (huc : 0 < M.ucH cbar)
    (hucc : M.uccH cbar ≠ 0) (heff : M.vy = (1 - P.β * P.η) * M.ucH cbar)
    {e1 : Ω → HabitWelfare.Exo} {ξ1 : Ω → ℕ → Ξ}
    (hgp : ∀ ω t, (e1 ω).gp t = M.gpH cbar (ξ1 ω t)) (hq : ∀ ω t, (e1 ω).q t = M.qS (ξ1 ω t))
    (hξ1 : ∀ ω, ∃ C, ∀ t, ‖ξ1 ω t‖ ≤ C) (hG1 : ∀ ω, Sequences.Bdd (e1 ω).G)
    (hn1 : ∀ ω, Sequences.Bdd (e1 ω).n) {yh : Ω → ℕ → ℝ → ι → ℝ} {y1 : Ω → ℕ → ι → ℝ}
    (h : ∀ ω, (fun p : ℕ × ℝ => yh ω p.1 p.2 - p.2 • y1 ω p.1) =O[unif] fun p => p.2 ^ 2)
    (hy1 : ∀ ω, ∃ C, ∀ t, ‖y1 ω t‖ ≤ C) {Ym1 : Ω → ℝ → ℝ} {Y1m1 : Ω → ℝ}
    (hYm1 : ∀ ω, (fun ε => Ym1 ω ε - ε * Y1m1 ω) =O[𝓝 0] fun ε => ε ^ 2)
    (hYa : ∀ ε, 𝔼.Adapted fun t ω => M.Yagg (yh ω t ε))
    (hna : 𝔼.Adapted fun t ω => (e1 ω).n t)
    (hflexE : ∀ t, 𝔼.E t (fun ω => HabitWelfare.rS P (e1 ω) t) = 0) (w : Ω) :
    (fun ε => 𝔼.E 0 (fun ω => ∑' t, P.β ^ t * M.Uhab P.η Gbar (yh ω t ε)
        (Sequences.lagS (Ym1 ω ε) (fun s => M.Yagg (yh ω s ε)) t) (ε * (e1 ω).G t)
        (Sequences.lagS (ε * (e1 ω).Gm1) (fun s => ε * (e1 ω).G s) t) (ε • ξ1 ω t)) w -
      (𝔼.E 0 (fun ω => ∑' t, P.β ^ t * (tip0 M.u cbar (ε • ξ1 ω t) -
          tip0 M.v M.Yb (ε • ξ1 ω t)) +
          M.Yb * M.ucH cbar * HabitWelfare.tipTotal P (exoSmul ε (e1 ω)) (Ym1 ω ε)) w +
        ε ^ 2 / 2 * (-(M.Yb * M.ucH cbar * 𝔼.E 0 (fun ω => ∑' t, P.β ^ t *
          (P.muX * HabitWelfare.gapSq P (e1 ω) (Y1m1 ω) (fun s => crossMean M.w (y1 ω s)) t +
            (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) * crossVar M.w (y1 ω t))) w))))
      =O[𝓝 0] fun ε => ε ^ 3 := by
  have := Fintype.ofFinite Ω
  set K := M.Yb * M.ucH cbar with hK
  set Uf : Ω → ℝ → ℝ := fun ω ε => ∑' t, P.β ^ t * M.Uhab P.η Gbar (yh ω t ε)
    (Sequences.lagS (Ym1 ω ε) (fun s => M.Yagg (yh ω s ε)) t) (ε * (e1 ω).G t)
    (Sequences.lagS (ε * (e1 ω).Gm1) (fun s => ε * (e1 ω).G s) t) (ε • ξ1 ω t) with hUf
  set Tf : Ω → ℝ → ℝ := fun ω ε => ∑' t, P.β ^ t * (tip0 M.u cbar (ε • ξ1 ω t) -
    tip0 M.v M.Yb (ε • ξ1 ω t)) + K * HabitWelfare.tipTotal P (exoSmul ε (e1 ω)) (Ym1 ω ε)
    with hTf
  set Xf : Ω → ℝ → ℝ := fun ω ε => ∑' t, P.β ^ t * (HabitWelfare.rS P (exoSmul ε (e1 ω)) t *
    HabitWelfare.xS (exoSmul ε (e1 ω)) (fun s => M.Yagg (yh ω s ε)) t) with hXf
  set Lf : Ω → ℝ := fun ω => ∑' t, P.β ^ t *
    (P.muX * HabitWelfare.gapSq P (e1 ω) (Y1m1 ω) (fun s => crossMean M.w (y1 ω s)) t +
      (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) * crossVar M.w (y1 ω t)) with hLf
  set F : Ω → ℝ → ℝ := fun ω ε => Uf ω ε - ((Tf ω ε - K * (1 - P.β * P.η) * Xf ω ε) +
    ε ^ 2 / 2 * (-(K * Lf ω))) with hF
  have hFo : ∀ ω, (fun ε => F ω ε) =O[𝓝 0] fun ε => ε ^ 3 := fun ω =>
    prop66_bridge_rx hM hP hPs hPΦ hPω hPθ hcbar huc hucc heff (hgp ω) (hq ω) (hξ1 ω) (hG1 ω)
      (hn1 ω) (h ω) (hy1 ω) (hYm1 ω)
  -- the expectation of the pathwise remainders
  have hsum : (fun ε => ∑ ω, |F ω ε|) =O[𝓝 0] fun ε => ε ^ 3 :=
    IsBigO.fun_sum (s := Finset.univ) fun ω _ =>
      (hFo ω).norm_left.congr_left fun ε => Real.norm_eq_abs _
  have hEF : (fun ε => 𝔼.E 0 (fun ω => F ω ε) w) =O[𝓝 0] fun ε => ε ^ 3 :=
    (IsBigO.of_bound 1 (Eventually.of_forall fun ε => by
      rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun ω _ => abs_nonneg (F ω ε))]
      exact 𝔼.abs_E_le (fun ω => Finset.single_le_sum (f := fun ω => |F ω ε|)
        (fun ω _ => abs_nonneg _) (Finset.mem_univ ω)) 0 w)).trans hsum
  -- the residual term vanishes in expectation for every small `ε`
  have hYb : ∀ᶠ ε in 𝓝 0, ∀ ω, Sequences.Bdd fun t => M.Yagg (yh ω t ε) := by
    rw [Filter.eventually_all]
    intro ω
    have hyu : (fun p : ℕ × ℝ => yh ω p.1 p.2) =O[unif] fun p => p.2 :=
      family_isBigO (s := fun p : ℕ × ℝ => p.2) tendsto_unif (h ω) (unif_of_bounded (hy1 ω))
    obtain ⟨-, -, -, hYu⟩ := ces_orders hM.w_nonneg hM.w_sum (r_ne hM) tendsto_unif hyu
    exact bdd_of_unif (f := fun t ε => M.Yagg (yh ω t ε)) (g := fun ε => ε) hYu
  have hX0 : ∀ᶠ ε in 𝓝 0, 𝔼.E 0 (fun ω => Xf ω ε) w = 0 := by
    filter_upwards [hYb] with ε hε
    have hb : ∀ ω, (e1 ω).Bounded := fun ω => by
      obtain ⟨C, hC⟩ := hξ1 ω
      have hx1 : (fun p : ℕ × ℝ => ξ1 ω p.1) =O[unif] fun _ => (1 : ℝ) :=
        unif_of_bounded ⟨C, hC⟩
      have hgpb : (fun p : ℕ × ℝ => (e1 ω).gp p.1) =O[unif] fun _ => (1 : ℝ) :=
        ((cross_isBigO M.u cbar hx1).const_mul_left (-(M.Yb * M.uccH cbar)⁻¹)).congr_left
          fun p => by rw [hgp]; unfold gpH gShock; ring
      have hqb : (fun p : ℕ × ℝ => (e1 ω).q p.1) =O[unif] fun _ => (1 : ℝ) :=
        (M.qS_isBigO hx1).congr_left fun p => (hq ω p.1).symm
      exact ⟨hG1 ω, bounded_of_unif (f := (e1 ω).gp) hgpb, bounded_of_unif (f := (e1 ω).q) hqb,
        hn1 ω⟩
    have hc : HabitWelfare.UBdd fun t ω => HabitWelfare.rS P (exoSmul ε (e1 ω)) t :=
      ubdd_of_finite fun ω => by
        simp only [rS_exoSmul]
        exact (Sequences.Bdd.const ε).mul (bdd_rS P (hb ω))
    have hy : HabitWelfare.UBdd fun t ω =>
        HabitWelfare.xS (exoSmul ε (e1 ω)) (fun s => M.Yagg (yh ω s ε)) t :=
      ubdd_of_finite fun ω => (hε ω).sub ((Sequences.Bdd.const ε).mul (hn1 ω))
    have hya : 𝔼.Adapted fun t ω =>
        HabitWelfare.xS (exoSmul ε (e1 ω)) (fun s => M.Yagg (yh ω s ε)) t := by
      intro t
      dsimp only
      have e : (fun ω => HabitWelfare.xS (exoSmul ε (e1 ω)) (fun s => M.Yagg (yh ω s ε)) t) =
          (fun ω => M.Yagg (yh ω t ε)) - ε • (fun ω => (e1 ω).n t) := by
        funext ω
        simp [HabitWelfare.xS, exoSmul, smul_eq_mul]
      rw [e, map_sub, map_smul, hYa ε t, hna t]
    have hc0 : ∀ t, 𝔼.E t (fun ω => HabitWelfare.rS P (exoSmul ε (e1 ω)) t) = 0 := fun t => by
      have e : (fun ω => HabitWelfare.rS P (exoSmul ε (e1 ω)) t) =
          ε • (fun ω => HabitWelfare.rS P (e1 ω) t) := by
        funext ω
        simp [rS_exoSmul, smul_eq_mul]
      rw [e, map_smul, hflexE t, smul_zero]
    exact HabitWelfare.E0_tsum_mul_zero 𝔼 hPO hP.1 hP.2.1 hc hy hya hc0 w
  refine hEF.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [hX0] with ε hε
  have e : (fun ω => Uf ω ε) = (fun ω => F ω ε) + (fun ω => Tf ω ε) -
      (K * (1 - P.β * P.η)) • (fun ω => Xf ω ε) + (ε ^ 2 / 2 * -K) • (fun _ => (0 : ℝ)) +
        (ε ^ 2 / 2 * -K) • (fun ω => Lf ω) := by
    funext ω
    simp only [hF, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  change 𝔼.E 0 (fun ω => F ω ε) w = 𝔼.E 0 (fun ω => Uf ω ε) w -
    (𝔼.E 0 (fun ω => Tf ω ε) w + ε ^ 2 / 2 * -(K * 𝔼.E 0 (fun ω => Lf ω) w))
  rw [e, map_add, map_add, map_sub, map_add, map_smul, map_smul, map_smul]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hε, 𝔼.const]
  ring

/-- Woodford (2003), **Proposition 6.6 (corrected), Layer B on a finite event tree** (§1, p. 385;
genuine uncertainty): `prop66_expected` for the conditional expectations of a finite tree, whose
pull-out property is `ExpectationsFiniteTree.finiteTree_pullOut`. -/
theorem prop66_finiteTree {Ω : Type*} [Fintype Ω] (T : ExpectationsFiniteTree.FiniteTree Ω)
    {M : Econ Ξ ι} (hM : M.Std) {P : HabitWelfare.Par} (hP : P.Std) {Gbar cbar : ℝ}
    (hPs : P.sinv = M.sigH cbar) (hPΦ : P.Φ = 0) (hPω : P.ω = M.omg) (hPθ : P.θ = M.θ)
    (hcbar : cbar = (1 - P.η) * (M.Yb - Gbar)) (huc : 0 < M.ucH cbar)
    (hucc : M.uccH cbar ≠ 0) (heff : M.vy = (1 - P.β * P.η) * M.ucH cbar)
    {e1 : Ω → HabitWelfare.Exo} {ξ1 : Ω → ℕ → Ξ}
    (hgp : ∀ ω t, (e1 ω).gp t = M.gpH cbar (ξ1 ω t)) (hq : ∀ ω t, (e1 ω).q t = M.qS (ξ1 ω t))
    (hξ1 : ∀ ω, ∃ C, ∀ t, ‖ξ1 ω t‖ ≤ C) (hG1 : ∀ ω, Sequences.Bdd (e1 ω).G)
    (hn1 : ∀ ω, Sequences.Bdd (e1 ω).n) {yh : Ω → ℕ → ℝ → ι → ℝ} {y1 : Ω → ℕ → ι → ℝ}
    (h : ∀ ω, (fun p : ℕ × ℝ => yh ω p.1 p.2 - p.2 • y1 ω p.1) =O[unif] fun p => p.2 ^ 2)
    (hy1 : ∀ ω, ∃ C, ∀ t, ‖y1 ω t‖ ≤ C) {Ym1 : Ω → ℝ → ℝ} {Y1m1 : Ω → ℝ}
    (hYm1 : ∀ ω, (fun ε => Ym1 ω ε - ε * Y1m1 ω) =O[𝓝 0] fun ε => ε ^ 2)
    (hYa : ∀ ε, T.toExpectationSystem.Adapted fun t ω => M.Yagg (yh ω t ε))
    (hna : T.toExpectationSystem.Adapted fun t ω => (e1 ω).n t)
    (hflexE : ∀ t, T.toExpectationSystem.E t (fun ω => HabitWelfare.rS P (e1 ω) t) = 0) (w : Ω) :
    (fun ε => T.toExpectationSystem.E 0 (fun ω => ∑' t, P.β ^ t * M.Uhab P.η Gbar (yh ω t ε)
        (Sequences.lagS (Ym1 ω ε) (fun s => M.Yagg (yh ω s ε)) t) (ε * (e1 ω).G t)
        (Sequences.lagS (ε * (e1 ω).Gm1) (fun s => ε * (e1 ω).G s) t) (ε • ξ1 ω t)) w -
      (T.toExpectationSystem.E 0 (fun ω => ∑' t, P.β ^ t * (tip0 M.u cbar (ε • ξ1 ω t) -
          tip0 M.v M.Yb (ε • ξ1 ω t)) +
          M.Yb * M.ucH cbar * HabitWelfare.tipTotal P (exoSmul ε (e1 ω)) (Ym1 ω ε)) w +
        ε ^ 2 / 2 * (-(M.Yb * M.ucH cbar * T.toExpectationSystem.E 0 (fun ω => ∑' t, P.β ^ t *
          (P.muX * HabitWelfare.gapSq P (e1 ω) (Y1m1 ω) (fun s => crossMean M.w (y1 ω s)) t +
            (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) * crossVar M.w (y1 ω t))) w))))
      =O[𝓝 0] fun ε => ε ^ 3 :=
  prop66_expected T.toExpectationSystem (ExpectationsFiniteTree.finiteTree_pullOut T) hM hP hPs hPΦ
    hPω hPθ hcbar huc hucc heff hgp hq hξ1 hG1 hn1 h hy1 hYm1 hYa hna hflexE w

end Habit

/-! ## Propositions 6.14–6.15: the dispersion hypotheses from the goods population -/

/-- Woodford (2003), App. E.2, p. 695 (uniformly in the date and the state): relative prices of
order `ε` at every date `t ≥ 0` and at the initial date `−1` (every state) are of order `ε` at
every index (index `0` is date `−1`). -/
theorem cen_all_state {Ω J : Type*} [Norm J] {X : A → ℕ → Ω → J}
    (hn : BridgeExtensions.UProc l (fun a t z => X a (t + 1) z) fun a => e a ^ 1)
    (h0 : BridgeExtensions.UProc l (fun a (_ : ℕ) z => X a 0 z) fun a => e a ^ 1) :
    BridgeExtensions.UProc l X fun a => e a ^ 1 := by
  obtain ⟨C1, h1⟩ := IsBigO.bound hn
  obtain ⟨C2, h2⟩ := IsBigO.bound h0
  refine IsBigO.of_bound (max C1 C2) ?_
  rw [Filter.prod_top, Filter.eventually_comap] at h1 h2 ⊢
  filter_upwards [h1, h2] with a ha ha0 p hp
  obtain ⟨a', t, z⟩ := p
  simp only at hp
  subst hp
  cases t with
  | zero =>
    exact (ha0 (a', 0, z) rfl).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (norm_nonneg _))
  | succ t =>
    exact (ha (a', t, z) rfl).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (norm_nonneg _))

/-- Woodford (2003), (2.12), (2.20), Prop. 6.3 and (5.2)–(5.3), pp. 396–399, 456 (**the dispersion
package from the goods population, uniformly in the date and the state**). In every state the
goods of the weighted cross-section follow the Calvo rule and Dixit–Stiglitz demand; outputs are
uniformly `O(ε)` and the initial relative prices are `O(ε)`. Then, with `D_t = var_i log p_{t−1}`
(`D 0 = Δ_{−1}`), `π̄_t = P̄_t − P̄_{t−1}` and `π_t` index inflation:
`var_i ŷ_t = θ²D_{t+1}`, `D_{t+1} = αD_t + α/(1 − α)π̄_t²`, `D = O(ε²)` and `π̄ − π = O(ε²)`,
all uniformly — exactly the hypotheses `hV`, `hD`, `hDO`, `hpO` of
`BridgeExtensions.prop614_layerB`/`prop615_layerB`. -/
theorem goods_state_package [MeasurableSpace ι] [MeasurableSingletonClass ι] {Ω : Type*}
    (he : Tendsto e l (𝓝 0)) {wt : ι → ℝ} (hw0 : ∀ i, 0 ≤ wt i) (hw1 : ∑ i, wt i = 1)
    {θ α : ℝ} (hθ0 : θ ≠ 0) (hθ1 : θ ≠ 1) (hα1 : α ≠ 1) {yh : A → ℕ → Ω → ι → ℝ}
    (hyh : BridgeExtensions.UProc l yh fun a => e a ^ 1) {X : A → ℕ → Ω → ι → ℝ}
    {Rs : A → Ω → ℕ → Set ι} {ps : A → Ω → ℕ → ℝ} {LY LP : A → ℕ → Ω → ℝ}
    (hG : ∀ a z, Links.GoodsPop.Calvo (wMeasure wt) α (fun t => X a t z) (Rs a z) (ps a z)
      fun _ => 0)
    (hdem : ∀ a t z i, yh a t z i = LY a t z - θ * (X a (t + 1) z i - LP a t z))
    (hX0 : BridgeExtensions.UProc l (fun a (_ : ℕ) z => cen wt (X a 0 z)) fun a => e a ^ 1) :
    (∀ a t, (fun z => crossVar wt (yh a t z)) = θ ^ 2 • fun z => crossVar wt (X a (t + 1) z)) ∧
    (∀ a t, (fun z => crossVar wt (X a (t + 1) z)) = α • (fun z => crossVar wt (X a t z)) +
      (α / (1 - α)) • (fun z => crossMean wt (X a (t + 1) z) - crossMean wt (X a t z)) ^ 2) ∧
    BridgeExtensions.UProc l (fun a t z => crossVar wt (X a t z)) (fun a => e a ^ 2) ∧
    BridgeExtensions.UProc l (fun a t z => (crossMean wt (X a (t + 1) z) - crossMean wt (X a t z)) -
      (logP wt θ (X a (t + 1) z) - logP wt θ (X a t z))) fun a => e a ^ 2 := by
  have hs := BridgeExtensions.tendsto_amp (J := ℕ × Ω) he
  have hcn : BridgeExtensions.UProc l (fun a t z => cen wt (X a (t + 1) z))
      fun a => e a ^ 1 :=
    ((cen_o hw0 hw1 hyh).const_smul_left (-θ⁻¹)).congr_left fun p =>
      (cen_demand hw1 hθ0 (hdem p.1 p.2.1 p.2.2)).symm
  have hca := cen_all_state (X := fun a t z => cen wt (X a t z)) hcn hX0
  refine ⟨fun a t => ?_, fun a t => ?_, ?_, disc_o hs hw0 hw1 hθ1 hcn hca⟩
  · funext z
    rw [show yh a t z = fun i => LY a t z - θ * (X a (t + 1) z i - LP a t z) from
      funext (hdem a t z), Moments.crossVar_demand hw1]
    rfl
  · funext z
    have h := goods_rec_fin hw0 hw1 hα1 (hG a z) t
    simp only [sub_zero] at h
    simp only [Pi.add_apply, Pi.smul_apply, Pi.pow_apply, smul_eq_mul]
    exact h
  · refine (BridgeExtensions.crossVar_o hw0 hw1 hca).congr_left fun p => ?_
    have e : cen wt (X p.1 p.2.1 p.2.2) =
        fun i => -crossMean wt (X p.1 p.2.1 p.2.2) + X p.1 p.2.1 p.2.2 i := by
      funext i; unfold cen; ring
    simp only
    rw [e, ExpLogCES.crossVar_const_add hw1]

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), **Proposition 6.14**, (5.2)–(5.3), p. 456, LAYER B FROM THE GOODS
POPULATION: `BridgeExtensions.prop614_layerB` with its dispersion hypotheses `hV` ((2.12)),
`hD` (Calvo law), `hDO` (`D = O(ε²)`) and `hpO` (`π̄ − π = O(ε²)`, the uniform Prop. 6.3 bound)
discharged by `goods_state_package`; `π_t` is index inflation and `D_t` the dispersion of log
prices (`D 0 = Δ_{−1}`, part of the t.i.p.). -/
theorem prop614_goods_layerB [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {α β θ ω σ Φ Ybar : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : 0 < θ) (hθ1 : θ ≠ 1) (hω : 0 < ω) (hσ : 0 < σ) (hΦ : Φ < 1)
    (he : Tendsto e l (𝓝 0)) {wt : ι → ℝ} (hw0 : ∀ i, 0 ≤ wt i) (hw1 : ∑ i, wt i = 1)
    {u v : ℝ × Ξ' → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    (hucc : BridgeExtensions.dYY u (Ybar, 0) = -(σ * BridgeExtensions.dY u (Ybar, 0) / Ybar))
    (hvy : BridgeExtensions.dY v (Ybar, 0) = (1 - Φ) * BridgeExtensions.dY u (Ybar, 0))
    (hvyy : BridgeExtensions.dYY v (Ybar, 0) = ω * BridgeExtensions.dY v (Ybar, 0) / Ybar)
    {yh : A → ℕ → Ω → ι → ℝ} {xu xv : A → ℕ → Ω → Ξ'} {g q : A → ℕ → Ω → ℝ}
    (hyh : BridgeExtensions.UProc l yh fun a => e a ^ 1)
    (hxu : BridgeExtensions.UProc l xu fun a => e a ^ 1)
    (hxv : BridgeExtensions.UProc l xv fun a => e a ^ 1)
    (hgO : BridgeExtensions.UProc l g fun a => e a ^ 1)
    (hqO : BridgeExtensions.UProc l q fun a => e a ^ 1)
    (hg : ∀ a t z, BridgeExtensions.dYXi u (Ybar, 0) (xu a t z) =
      σ * BridgeExtensions.dY u (Ybar, 0) * g a t z)
    (hq : ∀ a t z, BridgeExtensions.dYXi v (Ybar, 0) (xv a t z) =
      -(ω * BridgeExtensions.dY v (Ybar, 0) * q a t z))
    {X : A → ℕ → Ω → ι → ℝ} {Rs : A → Ω → ℕ → Set ι} {ps : A → Ω → ℕ → ℝ}
    {LY LP : A → ℕ → Ω → ℝ}
    (hG : ∀ a z, Links.GoodsPop.Calvo (wMeasure wt) α (fun t => X a t z) (Rs a z) (ps a z)
      fun _ => 0)
    (hdem : ∀ a t z i, yh a t z i = LY a t z - θ * (X a (t + 1) z i - LP a t z))
    (hX0 : BridgeExtensions.UProc l (fun a (_ : ℕ) z => cen wt (X a 0 z)) fun a => e a ^ 1)
    (hiO : BridgeExtensions.UProc l (fun a t z => logP wt θ (X a (t + 1) z) -
      logP wt θ (X a t z)) fun a => e a ^ 1) (w0 : Ω) :
    (fun a => Sequences.dsum 𝔼 β
        (fun t z => BridgeExtensions.periodU u v wt θ Ybar (yh a t z) (xu a t z) (xv a t z)) w0 -
      (-LargeDistortions.OmegaW Ybar (BridgeExtensions.dY u (Ybar, 0))
          (Moments.calvoKappa α β ω θ σ) θ Φ ω σ *
          Sequences.dsum 𝔼 β (LargeDistortions.loss614 (Moments.calvoKappa α β ω θ σ) θ Φ ω σ
            (fun t z => logP wt θ (X a (t + 1) z) - logP wt θ (X a t z))
            (fun t z => BridgeExtensions.logYidx wt θ (yh a t z)) (g a) (q a)) w0 +
        (Sequences.dsum 𝔼 β (fun t z => BridgeExtensions.tip51 u v Ybar (xu a t z) (xv a t z))
            w0 -
          LargeDistortions.OmegaW Ybar (BridgeExtensions.dY u (Ybar, 0))
            (Moments.calvoKappa α β ω θ σ) θ Φ ω σ * (1 - α) *
            𝔼.E 0 (fun z => crossVar wt (X a 0 z)) w0)))
      =O[l] fun a => e a ^ 3 := by
  obtain ⟨hV, hD, hDO, hpO⟩ :=
    goods_state_package he hw0 hw1 hθ.ne' hθ1 hα1.ne hyh hG hdem hX0
  exact BridgeExtensions.prop614_layerB 𝔼 hα0 hα1 hβ0 hβ1 hθ hθ1 hω hσ hΦ he hw0 hw1 hu hv
    hucc hvy hvyy hyh hxu hxv hgO hqO hiO hpO hDO hg hq hV hD w0

/-- Woodford (2003), **Proposition 6.15**, (5.5)–(5.8), pp. 458–459, LAYER B FROM THE GOODS
POPULATION: `BridgeExtensions.prop615_layerB` with its dispersion hypotheses `hV`, `hD`, `hDO`
and `hpO` discharged by `goods_state_package` (inflation `π` is index inflation, which is also the
inflation of the exact Calvo model `hM`, itself available from the reset-price first-order
condition and the price index via `LargeDistortions.calvoAS_of_primitives`). -/
theorem prop615_goods_layerB [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {α β θ ω σ sC Φ Ybar : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : 1 < θ) (hω : 0 < ω) (hσ : 0 < σ) (hsC : 0 < sC) (hΦ0 : 0 ≤ Φ) (hΦ : Φ < 1)
    (hMd : LargeDistortions.Mden ω σ sC Φ ≠ 0) (he : Tendsto e l (𝓝 0)) {wt : ι → ℝ}
    (hw0 : ∀ i, 0 ≤ wt i) (hw1 : ∑ i, wt i = 1) {u v : ℝ × Ξ' → ℝ} (hu : ContDiff ℝ 3 u)
    (hv : ContDiff ℝ 3 v)
    (hucc : BridgeExtensions.dYY u (Ybar, 0) = -(σ * BridgeExtensions.dY u (Ybar, 0) / Ybar))
    (hvy : BridgeExtensions.dY v (Ybar, 0) = (1 - Φ) * BridgeExtensions.dY u (Ybar, 0))
    (hvyy : BridgeExtensions.dYY v (Ybar, 0) = ω * BridgeExtensions.dY v (Ybar, 0) / Ybar)
    {yh : A → ℕ → Ω → ι → ℝ} {xu xv : A → ℕ → Ω → Ξ'}
    {xr F K f k G cb q muw tau : A → ℕ → Ω → ℝ} {X : A → ℕ → Ω → ι → ℝ}
    {Rs : A → Ω → ℕ → Set ι} {ps : A → Ω → ℕ → ℝ} {LY LP : A → ℕ → Ω → ℝ}
    (hM : ∀ a, LargeDistortions.CalvoModel.CalvoAS 𝔼 α β θ ω σ sC
      (fun t z => logP wt θ (X a (t + 1) z) - logP wt θ (X a t z)) (xr a) (F a) (K a) (f a)
      (k a) (fun t z => BridgeExtensions.logYidx wt θ (yh a t z)) (G a) (cb a) (q a) (muw a)
      (tau a))
    (hyh : BridgeExtensions.UProc l yh fun a => e a ^ 1)
    (hxu : BridgeExtensions.UProc l xu fun a => e a ^ 1)
    (hxv : BridgeExtensions.UProc l xv fun a => e a ^ 1)
    (hiO : BridgeExtensions.UProc l (fun a t z => logP wt θ (X a (t + 1) z) -
      logP wt θ (X a t z)) fun a => e a ^ 1)
    (hxrO : BridgeExtensions.UProc l xr fun a => e a ^ 1)
    (hFO : BridgeExtensions.UProc l F fun a => e a ^ 1)
    (hKO : BridgeExtensions.UProc l K fun a => e a ^ 1)
    (hfO : BridgeExtensions.UProc l f fun a => e a ^ 1)
    (hkO : BridgeExtensions.UProc l k fun a => e a ^ 1)
    (hGO : BridgeExtensions.UProc l G fun a => e a ^ 1)
    (hcbO : BridgeExtensions.UProc l cb fun a => e a ^ 1)
    (hqO : BridgeExtensions.UProc l q fun a => e a ^ 1)
    (hmO : BridgeExtensions.UProc l muw fun a => e a ^ 1)
    (htO : BridgeExtensions.UProc l tau fun a => e a ^ 1)
    (hg : ∀ a t z, BridgeExtensions.dYXi u (Ybar, 0) (xu a t z) =
      σ * BridgeExtensions.dY u (Ybar, 0) * (G a t z + sC * cb a t z))
    (hq : ∀ a t z, BridgeExtensions.dYXi v (Ybar, 0) (xv a t z) =
      -(ω * BridgeExtensions.dY v (Ybar, 0) * q a t z))
    (hG : ∀ a z, Links.GoodsPop.Calvo (wMeasure wt) α (fun t => X a t z) (Rs a z) (ps a z)
      fun _ => 0)
    (hdem : ∀ a t z i, yh a t z i = LY a t z - θ * (X a (t + 1) z i - LP a t z))
    (hX0 : BridgeExtensions.UProc l (fun a (_ : ℕ) z => cen wt (X a 0 z)) fun a => e a ^ 1)
    (w0 : Ω) :
    (fun a => Sequences.dsum 𝔼 β
        (fun t z => BridgeExtensions.periodU u v wt θ Ybar (yh a t z) (xu a t z) (xv a t z)) w0 -
      (BridgeExtensions.W0615 𝔼 α β θ ω σ Φ Ybar (BridgeExtensions.dY u (Ybar, 0))
          (fun t z => logP wt θ (X a (t + 1) z) - logP wt θ (X a t z)) (F a) (K a) w0 -
        LargeDistortions.OmegaTilde Ybar (BridgeExtensions.dY u (Ybar, 0)) α β θ ω σ Φ *
          Sequences.dsum 𝔼 β (LargeDistortions.loss615 α β θ ω σ sC Φ
            (fun t z => logP wt θ (X a (t + 1) z) - logP wt θ (X a t z))
            (fun t z => BridgeExtensions.logYidx wt θ (yh a t z)) (G a) (cb a) (q a) (muw a)
            (tau a)) w0 +
        BridgeExtensions.tip615 𝔼 α β θ ω σ sC Φ Ybar (BridgeExtensions.dY u (Ybar, 0))
          (fun t z => BridgeExtensions.tip51 u v Ybar (xu a t z) (xv a t z))
          (fun t z => crossVar wt (X a t z)) (G a) (cb a) (q a) (muw a) (tau a) w0))
      =O[l] fun a => e a ^ 3 := by
  obtain ⟨hV, hD, hDO, hpO⟩ :=
    goods_state_package he hw0 hw1 (by linarith) hθ.ne' hα1.ne hyh hG hdem hX0
  exact BridgeExtensions.prop615_layerB 𝔼 hα0 hα1 hβ0 hβ1 hθ hω hσ hsC hΦ0 hΦ hMd he hw0 hw1 hu
    hv hucc hvy hvyy hM hyh hxu hxv hiO hxrO hFO hKO hfO hkO hGO hcbO hqO hmO htO hpO hDO hg hq
    hV hD w0

end Woodford.StabilizationWelfare.BridgeLinks
