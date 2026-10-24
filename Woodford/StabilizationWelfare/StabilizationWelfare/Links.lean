/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.HabitWelfare
import StabilizationWelfare.Transactions
import StabilizationWelfare.TwoSectorWelfare
import StabilizationWelfare.LargeDistortions
import StabilizationWelfare.PriceDispersion

/-!
# Cross-chain links

Woodford (2003), *Interest and Prices*, Chapter 6 (pp. 381–463) and Appendix E (pp. 692–708).
The welfare approximations of the chapter were proved with some ingredients taken as explicit
hypotheses or as atoms of a stated weight. This module discharges them from the results proved
elsewhere in the library.

## Main results

* The CES aggregator (E.5), p. 694: the atom `r_C` of `E_i ŷ = Ŷ − ½(1 − θ⁻¹) var_i ŷ + r_C`
  (`cesAtom`) is `O(‖ŷ‖³)` (`cesAtom_isBigO`) and of weight three along every ray
  (`cesAtom_ray`), from `ExpLogCES.log_outputIndex_expansion`. Hence (5.1) with the actual CES
  index (`eq51_ces`) and the habit model's (E.5) (`habit_E5_ces`).
* The price index, App. E.2, p. 695: the remainder `ρ` of `log P = P̄ + ½(1 − θ)Δ + ρ`
  (`priceAtom`) is `O(‖log p − c‖³)` (`priceAtom_isBigO`), which discharges the `ρ` of
  `TwoSectorWelfare.infl_discrepancy_rho` (`infl_discrepancy_ces`); the discrepancy
  `e_t = (P̄_t − P̄_{t−1}) − π_t` has weight two (`eDisc_isBigO`) and the error
  `(π + e)² − π²` it causes in (5.2)–(5.3) is `O(s³)` (`pib_sq_sub_isBigO`).
* The Calvo goods population (App. E.2, p. 695, (2.12), (2.20), (2.24)): a population of goods
  on a probability space following the Calvo (or indexation) reset rule (`GoodsCalvo`)
  satisfies the dispersion recursion in both forms used by the chapter (`goods_disp_rec`,
  `goods_disp_rec_lag`); with Dixit–Stiglitz demand this discharges the hypotheses
  `var_i ŷ = θ²Δ` and (2.20)/(2.24) of Proposition 6.6's loss (`welfare228_goods`,
  `welfare229_goods`), the dispersion hypothesis of Proposition 6.8 (`prop_6_8_goods`), and
  the hypotheses `hV`, `hD` of Proposition 6.14 (`prop614_goods`).
* `κ` consistency: without habits (`η = 0`) the habit model's `κ` (Ch. 5 (1.29)) is the Calvo
  slope `Moments.calvoKappa` used by Propositions 6.4 and 6.14 (`habit_kappa_eta_zero`), its
  `λ` is `κ/θ` (`habit_lam_eta_zero`), and its normalising factor `Λ` is Proposition 6.4's `Θ`
  (`habit_Lam_eta_zero`).
-/

namespace Woodford.StabilizationWelfare.Links

open Filter Topology Asymptotics MeasureTheory
open Sequences (Bdd lagS lagS_succ lagS_zero)
open CrossSection (crossMean crossVar)

/-! ### The CES aggregator (E.5): the atom `r_C` -/

namespace CES

variable {ι : Type*} [Fintype ι]

/-- Woodford (2003), eq. (E.5), p. 694: the CES atom
`r_C = E_i ŷ − [Ŷ − ½(1 − θ⁻¹) var_i ŷ]`, where `Ŷ = log(Y/Ȳ)` is the log of the Dixit–Stiglitz
index (exponent `1 − θ⁻¹`) of `y(i)/Ȳ = e^{ŷ(i)}`. -/
noncomputable def cesAtom (w : ι → ℝ) (θ : ℝ) (yh : ι → ℝ) : ℝ :=
  ExpLogCES.crossMean w yh -
    (Real.log (ExpLogCES.cesIndex w (1 - θ⁻¹) (fun i => Real.exp (yh i))) -
      (1 - θ⁻¹) / 2 * ExpLogCES.crossVar w yh)

/-- Woodford (2003), eq. (E.5), p. 694 (exact, by definition of the atom):
`E_i ŷ = Ŷ − ½(1 − θ⁻¹) var_i ŷ + r_C`. -/
theorem ces_relation (w : ι → ℝ) (θ : ℝ) (yh : ι → ℝ) :
    ExpLogCES.crossMean w yh =
      Real.log (ExpLogCES.cesIndex w (1 - θ⁻¹) (fun i => Real.exp (yh i))) -
        (1 - θ⁻¹) / 2 * ExpLogCES.crossVar w yh + cesAtom w θ yh := by
  unfold cesAtom; ring

/-- Woodford (2003), eq. (E.5), p. 694 (the "O(‖ŷ‖³)" of the CES expansion): the atom `r_C` is
of third order, from `ExpLogCES.log_outputIndex_expansion`. -/
theorem cesAtom_isBigO {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {θ : ℝ}
    (hθ1 : θ ≠ 1) : cesAtom w θ =O[𝓝 0] fun yh => ‖yh‖ ^ 3 :=
  (ExpLogCES.log_outputIndex_expansion hw hw1 hθ1).neg_left.congr_left fun yh => by
    unfold cesAtom; ring

/-- Woodford (2003), eq. (E.5), p. 694, and (5.1), p. 455 (the weight-three atom `r_C` of
`LargeDistortions.R51`): along every ray `ŷ = s ŷ₁`, `r_C = O(s³)`. -/
theorem cesAtom_ray {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {θ : ℝ}
    (hθ1 : θ ≠ 1) (yh : ι → ℝ) :
    (fun s : ℝ => cesAtom w θ (fun i => s * yh i)) =O[𝓝 0] fun s => s ^ 3 := by
  have ht : Tendsto (fun s : ℝ => fun i => s * yh i) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun s : ℝ => fun i => s * yh i) := by fun_prop
    have h0 := hc.tendsto 0
    simp only [zero_mul] at h0
    exact h0
  refine ((cesAtom_isBigO hw hw1 hθ1).comp_tendsto ht).trans ?_
  refine IsBigO.of_bound (‖yh‖ ^ 3) (Eventually.of_forall fun s => ?_)
  have hn : ‖(fun i => s * yh i : ι → ℝ)‖ = |s| * ‖yh‖ := by
    rw [← Real.norm_eq_abs, ← norm_smul]
    rfl
  rw [Function.comp_apply, hn, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_pow, mul_pow]
  exact le_of_eq (by ring)

/-- Woodford (2003), eq. (5.1), p. 455 (Layer A) with the CES atom discharged: when `Ŷ` is the
log of the Dixit–Stiglitz index of the `e^{ŷ(i)}`, the hypothesis (E.5) of
`LargeDistortions.eq51_exact` holds with `r_C = cesAtom` (of weight three, `cesAtom_ray`). -/
theorem eq51_ces (w : ι → ℝ) (hw : ∑ i, w i = 1)
    {Ybar uc ucc ucxi vy vyy vyxi σ ω θ Φ g q : ℝ}
    (hucc : ucc = -(σ * uc / Ybar)) (hucxi : ucxi = σ * uc * g) (hvy : vy = (1 - Φ) * uc)
    (hvyy : vyy = ω * vy / Ybar) (hvyxi : vyxi = -(ω * vy * q))
    (ubar uxi uxixi vbar vxi vxixi Y rY : ℝ) (yh ry : ι → ℝ)
    (hY : Y = Real.log (ExpLogCES.cesIndex w (1 - θ⁻¹) (fun i => Real.exp (yh i)))) :
    Prop61.uTaylor ubar uc ucc uxi ucxi uxixi (Ybar * (Y + Y ^ 2 / 2 + rY)) -
        ∑ i, w i *
          Prop61.vTaylor vbar vy vyy vxi vyxi vxixi (Ybar * (yh i + yh i ^ 2 / 2 + ry i)) =
      -(Ybar * uc / 2) * LargeDistortions.quad51 σ ω θ Φ g q Y (ExpLogCES.crossVar w yh) +
        ((ubar + uxi + uxixi / 2) - (vbar + vxi + vxixi / 2)) +
        Ybar * uc * LargeDistortions.R51 σ ω θ Φ g q Y (ExpLogCES.crossVar w yh) rY
          (cesAtom w θ yh) (∑ i, w i * Prop61.Rv 0 ω q (yh i) (ry i)) :=
  LargeDistortions.eq51_exact w hw hucc hucxi hvy hvyy hvyxi ubar uxi uxixi vbar vxi vxixi Y rY
    (cesAtom w θ yh) yh ry (by rw [hY]; exact ces_relation w θ yh)

/-- Woodford (2003), eq. (E.5), p. 694, in the habit model (App. E.3): the Layer-A relation
`E_i ŷ = m₁(Ŷ, var_i ŷ) + r_C` used by `HabitWelfare.E4_identity` holds with the CES atom. -/
theorem habit_E5_ces (w : ι → ℝ) (θ : ℝ) (yh : ι → ℝ) {Y : ℝ}
    (hY : Y = Real.log (ExpLogCES.cesIndex w (1 - θ⁻¹) (fun i => Real.exp (yh i)))) :
    ExpLogCES.crossMean w yh =
      HabitWelfare.m1Of θ Y (ExpLogCES.crossVar w yh) + cesAtom w θ yh := by
  rw [hY]; unfold HabitWelfare.m1Of cesAtom; ring

/-! ### The price index: the atoms `ρ` and `e_t` -/

/-- Woodford (2003), App. E.2, p. 695: the remainder `ρ = log P − P̄ − ½(1 − θ)Δ` of the price
index, with `P̄ = E_i log p` and `Δ = var_i log p`. -/
noncomputable def priceAtom (w : ι → ℝ) (θ : ℝ) (q : ι → ℝ) : ℝ :=
  Real.log (ExpLogCES.cesIndex w (1 - θ) (fun i => Real.exp (q i))) -
    ExpLogCES.crossMean w q - (1 - θ) / 2 * ExpLogCES.crossVar w q

/-- Woodford (2003), App. E.2, p. 695: `ρ = O(‖log p − c‖³)` around any common log price `c`
(from `ExpLogCES.log_priceIndex_expansion`). -/
theorem priceAtom_isBigO {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {θ : ℝ}
    (hθ : θ ≠ 1) (c : ℝ) : priceAtom w θ =O[𝓝 (fun _ => c)] fun q => ‖q - fun _ => c‖ ^ 3 :=
  (ExpLogCES.log_priceIndex_expansion hw hw1 hθ c).congr_left fun q => by
    unfold priceAtom; ring

/-- Woodford (2003), App. E.2 and E.7, pp. 695 and 706: `TwoSectorWelfare.infl_discrepancy_rho`
with the CES remainders discharged: for log-price cross-sections `q` (date `t`) and `q₋`
(date `t − 1`), `π̄_t − π_t = −½(1 − θ)(Δ_t − Δ_{t−1}) − (ρ_t − ρ_{t−1})` with `ρ = priceAtom`,
of third order (`priceAtom_isBigO`). -/
theorem infl_discrepancy_ces (w : ι → ℝ) (θ : ℝ) (q qm : ι → ℝ) :
    (ExpLogCES.crossMean w q - ExpLogCES.crossMean w qm) -
        (Real.log (ExpLogCES.cesIndex w (1 - θ) (fun i => Real.exp (q i))) -
          Real.log (ExpLogCES.cesIndex w (1 - θ) (fun i => Real.exp (qm i)))) =
      -((1 - θ) / 2 * (ExpLogCES.crossVar w q - ExpLogCES.crossVar w qm)) -
        (priceAtom w θ q - priceAtom w θ qm) :=
  TwoSectorWelfare.infl_discrepancy_rho (by unfold priceAtom; ring) (by unfold priceAtom; ring)

/-- Woodford (2003), Prop. 6.3 (App. E.2, p. 695) and (5.2)–(5.3), p. 456 (the weight-two atom
`e_t` of `LargeDistortions.pib_sq_scaling`): the discrepancy
`e_t = (P̄_t − P̄_{t−1}) − (log P_t − log P_{t−1})` between mean-price and index inflation is
`O(‖log p_t − c‖² + ‖log p_{t−1} − c‖²)` (from `ExpLogCES.log_priceIndex_sub_mean_isBigO`). -/
theorem eDisc_isBigO {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {θ : ℝ}
    (hθ : θ ≠ 1) (c : ℝ) :
    (fun z : (ι → ℝ) × (ι → ℝ) =>
      (ExpLogCES.crossMean w z.1 - ExpLogCES.crossMean w z.2) -
        (Real.log (ExpLogCES.cesIndex w (1 - θ) (fun i => Real.exp (z.1 i))) -
          Real.log (ExpLogCES.cesIndex w (1 - θ) (fun i => Real.exp (z.2 i)))))
      =O[𝓝 ((fun _ => c), (fun _ => c))]
      fun z => ‖z.1 - fun _ => c‖ ^ 2 + ‖z.2 - fun _ => c‖ ^ 2 := by
  have h := ExpLogCES.log_priceIndex_sub_mean_isBigO hw hw1 hθ c
  have h1 := h.comp_tendsto
    (continuous_fst.tendsto (((fun _ => c), (fun _ => c)) : (ι → ℝ) × (ι → ℝ)))
  have h2 := h.comp_tendsto
    (continuous_snd.tendsto (((fun _ => c), (fun _ => c)) : (ι → ℝ) × (ι → ℝ)))
  have b1 : (fun z : (ι → ℝ) × (ι → ℝ) => ‖z.1 - fun _ => c‖ ^ 2)
      =O[𝓝 ((fun _ => c), (fun _ => c))]
      fun z => ‖z.1 - fun _ => c‖ ^ 2 + ‖z.2 - fun _ => c‖ ^ 2 :=
    IsBigO.of_bound 1 (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        abs_of_nonneg (by positivity)]
      nlinarith [sq_nonneg ‖z.2 - fun _ => c‖])
  have b2 : (fun z : (ι → ℝ) × (ι → ℝ) => ‖z.2 - fun _ => c‖ ^ 2)
      =O[𝓝 ((fun _ => c), (fun _ => c))]
      fun z => ‖z.1 - fun _ => c‖ ^ 2 + ‖z.2 - fun _ => c‖ ^ 2 :=
    IsBigO.of_bound 1 (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        abs_of_nonneg (by positivity)]
      nlinarith [sq_nonneg ‖z.1 - fun _ => c‖])
  refine ((h2.trans b2).sub (h1.trans b1)).congr_left fun z => ?_
  simp only [Function.comp_apply]
  ring

end CES

/-- Woodford (2003), Prop. 6.3 (App. E.2, p. 695) and Prop. 6.14, (5.2)–(5.3), p. 456: if
inflation is `O(s)` and the discrepancy `e = π̄ − π` is `O(s²)` (`CES.eDisc_isBigO`), then
replacing `π̄²` by `π²` costs `(π + e)² − π² = O(s³)` (cf. `LargeDistortions.pib_sq_scaling`). -/
theorem pib_sq_sub_isBigO {π e : ℝ → ℝ} (hπ : π =O[𝓝 0] fun s => s ^ 1)
    (he : e =O[𝓝 0] fun s => s ^ 2) :
    (fun s => (π s + e s) ^ 2 - π s ^ 2) =O[𝓝 0] fun s => s ^ 3 := by
  have h1 := OneParamTaylor.bigO_mul hπ he (by norm_num : 1 + 2 = 3)
  have h2 := OneParamTaylor.bigO_weaken (by norm_num : 3 ≤ 4)
    (OneParamTaylor.bigO_mul he he (by norm_num : 2 + 2 = 4))
  exact ((h1.const_mul_left 2).add h2).congr_left fun s => by ring

/-! ### The Calvo population of goods: the dispersion hypotheses -/

namespace GoodsPop

variable {G : Type*} [MeasurableSpace G] (μ : Measure G) (α : ℝ) (X : ℕ → G → ℝ)
variable (R : ℕ → Set G) (ps d : ℕ → ℝ)

/-- Woodford (2003), App. E.2, p. 695, and (2.23)–(2.24), p. 402: a population of goods `G`
(probability measure `μ`) whose log prices `X (t + 1)` at date `t` (`X 0` at date `−1`) follow
staggered pricing: the goods of a reset set `R t` of measure `1 − α` charge `p*_t`, the others
keep their price raised by the indexation increment `d t` (`d = 0` for Calvo), and the
non-resetting goods are representative of the old cross-section. -/
structure Calvo where
  /-- The reset sets are measurable. -/
  meas : ∀ t, MeasurableSet (R t)
  /-- A fraction `1 − α` of goods resets each period. -/
  mass : ∀ t, μ.real (R t) = 1 - α
  /-- Log prices are integrable. -/
  int1 : ∀ t, Integrable (X t) μ
  /-- Squared log prices are integrable. -/
  int2 : ∀ t, Integrable (fun i => X t i ^ 2) μ
  /-- The non-resetting goods carry a fraction `α` of the first moment. -/
  rep1 : ∀ t, ∫ i in (R t)ᶜ, X t i ∂μ = α * ∫ i, X t i ∂μ
  /-- The non-resetting goods carry a fraction `α` of the second moment. -/
  rep2 : ∀ t, ∫ i in (R t)ᶜ, X t i ^ 2 ∂μ = α * ∫ i, X t i ^ 2 ∂μ
  /-- Resetting goods charge the common new price. -/
  reset : ∀ t, ∀ i ∈ R t, X (t + 1) i = ps t
  /-- The other goods keep their price, indexed by `d t`. -/
  keep : ∀ t, ∀ i ∉ R t, X (t + 1) i = X t i + d t

end GoodsPop

variable {G : Type*} [MeasurableSpace G]

/-- Woodford (2003), (E.8), p. 695, and (2.24), p. 402, along a goods population
(`CrossSection.goods_index_var` at every date):
`Δ_t = αΔ_{t−1} + α/(1 − α)(P̄_t − P̄_{t−1} − d_t)²`. -/
theorem goods_disp_rec (μ : Measure G) [IsProbabilityMeasure μ] {α : ℝ} {X : ℕ → G → ℝ}
    {R : ℕ → Set G} {ps d : ℕ → ℝ} (hG : GoodsPop.Calvo μ α X R ps d) (hα : α ≠ 1)
    (t : ℕ) :
    crossVar μ (X (t + 1)) = α * crossVar μ (X t) +
      α / (1 - α) * (crossMean μ (X (t + 1)) - crossMean μ (X t) - d t) ^ 2 :=
  (CrossSection.goods_index_var μ (hG.meas t) hα (hG.mass t) (hG.int1 t) (hG.int2 t)
    (hG.rep1 t) (hG.rep2 t) (hG.reset t) (hG.keep t)).2

/-- Woodford (2003), (2.20)/(2.24), pp. 399–402, in the lagged form used by Proposition 6.6
(`Δ_{−1} = var X₀`): `Δ_t = α lag(Δ)_t + α/(1 − α)(P̄_t − P̄_{t−1} − d_t)²`. -/
theorem goods_disp_rec_lag (μ : Measure G) [IsProbabilityMeasure μ] {α : ℝ} {X : ℕ → G → ℝ}
    {R : ℕ → Set G} {ps d : ℕ → ℝ} (hG : GoodsPop.Calvo μ α X R ps d) (hα : α ≠ 1)
    (t : ℕ) :
    crossVar μ (X (t + 1)) =
      α * lagS (crossVar μ (X 0)) (fun s => crossVar μ (X (s + 1))) t +
        α / (1 - α) * (crossMean μ (X (t + 1)) - crossMean μ (X t) - d t) ^ 2 := by
  have h : lagS (crossVar μ (X 0)) (fun s => crossVar μ (X (s + 1))) t = crossVar μ (X t) := by
    cases t <;> rfl
  rw [h]
  exact goods_disp_rec μ hG hα t

/-- **Woodford (2003), (2.21) with (2.28), pp. 400–405 (Proposition 6.6's loss) from the Calvo
population.** `HabitWelfare.welfare228` with its hypotheses `var_i ŷ_t = θ²Δ_t` ((2.12),
`CrossSection.crossVar_demand`) and the dispersion law (2.20) (`goods_disp_rec_lag`)
discharged: `Δ_t = var_i log p_t(i)`, `p_t = P̄_t − P̄_{t−1}`, and `var_i ŷ_t` the dispersion of
log output under Dixit–Stiglitz demand. -/
theorem welfare228_goods {P : HabitWelfare.Par} (hP : P.Std) (μ : Measure G)
    [IsProbabilityMeasure μ] {α : ℝ} {X ly : ℕ → G → ℝ} {R : ℕ → Set G} {ps LY LP : ℕ → ℝ}
    (hG : GoodsPop.Calvo μ α X R ps fun _ => 0)
    (hdem : ∀ t i, ly t i = LY t - P.θ * (X (t + 1) i - LP t))
    (e : HabitWelfare.Exo) (Ym1 : ℝ) (Y : ℕ → ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hθ : 0 < P.θ)
    (hY : Bdd Y) (he : e.Bounded)
    (hp : Bdd fun t => crossMean μ (X (t + 1)) - crossMean μ (X t)) :
    ∑' t, P.β ^ t * HabitWelfare.Useq P e Ym1 Y (fun t => crossVar μ (ly t)) t =
      -P.Lam α * ∑' t, P.β ^ t * ((crossMean μ (X (t + 1)) - crossMean μ (X t)) ^ 2 +
          P.lam α * HabitWelfare.gapSq P e Ym1 Y t) -
        (1 - P.β * P.η) * ∑' t, P.β ^ t * (HabitWelfare.rS P e t * HabitWelfare.xS e Y t) +
        (HabitWelfare.tipTotal P e Ym1 - (1 - P.β * P.η) / 2 * (P.θ * (1 + P.ω * P.θ)) *
          (α * crossVar μ (X 0) / (1 - α * P.β))) +
        ∑' t, P.β ^ t * HabitWelfare.RUseq P e Ym1 Y (fun t => crossVar μ (ly t)) t :=
  HabitWelfare.welfare228 hP (Δ := fun t => crossVar μ (X (t + 1))) e Ym1 Y _ hα0 hα1 hθ hY hp
    he (fun t => by simpa using goods_disp_rec_lag μ hG hα1.ne t)
    (fun t => CrossSection.crossVar_demand μ (hG.int1 (t + 1)) (hdem t))

/-- **Woodford (2003), (2.29), p. 405 (indexation) from the population with indexation.**
`HabitWelfare.welfare229` with `var_i ŷ_t = θ²Δ_t` and the indexation law (2.24) discharged:
non-resetting prices are raised by `γπ_{t−1}`, `π_t = P̄_t − P̄_{t−1}` (`π_{−1}` given). -/
theorem welfare229_goods {P : HabitWelfare.Par} (hP : P.Std) (μ : Measure G)
    [IsProbabilityMeasure μ] {α γ πm1 : ℝ} {X ly : ℕ → G → ℝ} {R : ℕ → Set G}
    {ps LY LP : ℕ → ℝ}
    (hG : GoodsPop.Calvo μ α X R ps fun t =>
      γ * lagS πm1 (fun s => crossMean μ (X (s + 1)) - crossMean μ (X s)) t)
    (hdem : ∀ t i, ly t i = LY t - P.θ * (X (t + 1) i - LP t))
    (e : HabitWelfare.Exo) (Ym1 : ℝ) (Y : ℕ → ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hθ : 0 < P.θ)
    (hY : Bdd Y) (he : e.Bounded)
    (hπ : Bdd fun t => crossMean μ (X (t + 1)) - crossMean μ (X t)) :
    ∑' t, P.β ^ t * HabitWelfare.Useq P e Ym1 Y (fun t => crossVar μ (ly t)) t =
      -P.Lam α * ∑' t, P.β ^ t * ((crossMean μ (X (t + 1)) - crossMean μ (X t) -
          γ * lagS πm1 (fun s => crossMean μ (X (s + 1)) - crossMean μ (X s)) t) ^ 2 +
          P.lam α * HabitWelfare.gapSq P e Ym1 Y t) -
        (1 - P.β * P.η) * ∑' t, P.β ^ t * (HabitWelfare.rS P e t * HabitWelfare.xS e Y t) +
        (HabitWelfare.tipTotal P e Ym1 - (1 - P.β * P.η) / 2 * (P.θ * (1 + P.ω * P.θ)) *
          (α * crossVar μ (X 0) / (1 - α * P.β))) +
        ∑' t, P.β ^ t * HabitWelfare.RUseq P e Ym1 Y (fun t => crossVar μ (ly t)) t :=
  HabitWelfare.welfare229 hP (Δ := fun t => crossVar μ (X (t + 1))) e Ym1 Y _ hα0 hα1 hθ hY hπ
    he (fun t => goods_disp_rec_lag μ hG hα1.ne t)
    (fun t => CrossSection.crossVar_demand μ (hG.int1 (t + 1)) (hdem t))

/-- **Woodford (2003), Proposition 6.8, (4.10)–(4.11), p. 423, from the Calvo population.**
`Transactions.prop_6_8` with its dispersion hypothesis (Props. 6.3/6.4,
`∑βᵗ var_i ŷ_t = θ²(ψ∑βᵗπ_t² + T₀)`) discharged: `var_i ŷ_t = θ²Δ_t` by Dixit–Stiglitz demand,
`Δ` follows the Calvo law along the population (`goods_disp_rec_lag`), and the discounted sum is
`Sequences.disp_discounted`, with `π_t = P̄_t − P̄_{t−1}` and the t.i.p.
`T₀ = αΔ_{−1}/(1 − αβ)`. -/
theorem prop_6_8_goods (P : Transactions.TxParams) (μ : Measure G) [IsProbabilityMeasure μ]
    {α β θ : ℝ} {X ly : ℕ → G → ℝ} {R : ℕ → Set G} {ps LY LP : ℕ → ℝ}
    (hG : GoodsPop.Calvo μ α X R ps fun _ => 0)
    (hdem : ∀ t i, ly t i = LY t - θ * (X (t + 1) i - LP t))
    (hπ : Bdd fun t => crossMean μ (X (t + 1)) - crossMean μ (X t))
    (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ : 0 < θ)
    (hθi : P.thetaInv = 1 / θ) (hω : 0 ≤ P.omega) (hΩ : 0 < Transactions.omegaMC P)
    (hv : P.vbar ≠ 0) {X2 I2 : ℕ → ℝ} {A B : ℝ} (hX : HasSum (fun t => β ^ t * X2 t) A)
    (hI : HasSum (fun t => β ^ t * I2 t) B) :
    HasSum (fun t => β ^ t * (Transactions.omegaMC P * X2 t + P.etaI / P.vbar * I2 t +
        (P.thetaInv + P.omega) * crossVar μ (ly t)))
      (θ * (1 + P.omega * θ) * Moments.calvoK α β *
          (∑' t, β ^ t * (crossMean μ (X (t + 1)) - crossMean μ (X t)) ^ 2 +
            Transactions.lambdaX P α β θ * A +
            Transactions.lambdaI P (Transactions.lambdaX P α β θ) * B) +
        (P.thetaInv + P.omega) * θ ^ 2 * (α * crossVar μ (X 0) / (1 - α * β))) ∧
    HasSum (fun t => β ^ t * ((crossMean μ (X (t + 1)) - crossMean μ (X t)) ^ 2 +
        Transactions.lambdaX P α β θ * X2 t +
        Transactions.lambdaI P (Transactions.lambdaX P α β θ) * I2 t))
      (∑' t, β ^ t * (crossMean μ (X (t + 1)) - crossMean μ (X t)) ^ 2 +
        Transactions.lambdaX P α β θ * A +
        Transactions.lambdaI P (Transactions.lambdaX P α β θ) * B) := by
  have hrec : ∀ t, crossVar μ (X (t + 1)) =
      α * lagS (crossVar μ (X 0)) (fun s => crossVar μ (X (s + 1))) t +
        α / (1 - α) * (crossMean μ (X (t + 1)) - crossMean μ (X t)) ^ 2 := fun t => by
    simpa using goods_disp_rec_lag μ hG hα1.ne t
  have hΔb := Sequences.disp_bdd hα0.le hα1 hπ hrec
  have hD := Sequences.disp_discounted hβ0 hβ1 hα0.le hα1 hπ hrec
  have hV : HasSum (fun t => β ^ t * crossVar μ (ly t))
      (θ ^ 2 * (Moments.calvoK α β *
        ∑' t, β ^ t * (crossMean μ (X (t + 1)) - crossMean μ (X t)) ^ 2 +
          α * crossVar μ (X 0) / (1 - α * β))) := by
    have h := ((hΔb.summable hβ0 hβ1).hasSum).mul_left (θ ^ 2)
    rw [hD] at h
    convert h using 1
    · funext t
      rw [CrossSection.crossVar_demand μ (hG.int1 (t + 1)) (hdem t)]
      ring
    · have h1 : (1 : ℝ) - α ≠ 0 := by linarith
      have h2 : (1 : ℝ) - α * β ≠ 0 := by nlinarith
      unfold Moments.calvoK
      field_simp
      ring
  exact Transactions.prop_6_8 P hα0 hα1 hβ1 hθ hθi hω hΩ hv hX hI
    ((hπ.pow 2).summable hβ0 hβ1).hasSum hV

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- **Woodford (2003), Proposition 6.14, (5.2)–(5.3), p. 456, from the Calvo population.**
`LargeDistortions.prop614` with its hypotheses `hV` (`var_i ŷ_t = θ²Δ_t`, (2.12)) and `hD` (the
Calvo law (E.8)) discharged: in every state the cross-section of goods follows the Calvo rule,
`D_t = var_i log p_{t−1}(i)`, `π̄_t = P̄_t − P̄_{t−1}` and `V_t = var_i ŷ_t(i)` under
Dixit–Stiglitz demand. -/
theorem prop614_goods (μ : Measure G) [IsProbabilityMeasure μ]
    {α β θ ω σ Φ Ybar uc : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ : 0 < θ) (hω : 0 < ω) (hσ : 0 < σ) (hΦ : Φ < 1)
    {U Y infl g q V D pib tipU R : ℕ → Ω → ℝ} {X ly : ℕ → Ω → G → ℝ} {Rs : ℕ → Ω → Set G}
    {ps LY LP : ℕ → Ω → ℝ}
    (hG : ∀ w, GoodsPop.Calvo μ α (fun t => X t w) (fun t => Rs t w) (fun t => ps t w)
      fun _ => 0)
    (hdem : ∀ t w i, ly t w i = LY t w - θ * (X (t + 1) w i - LP t w))
    (hVd : ∀ t w, V t w = crossVar μ (ly t w)) (hDd : ∀ t w, D t w = crossVar μ (X t w))
    (hpd : ∀ t w, pib t w = crossMean μ (X (t + 1) w) - crossMean μ (X t w))
    (hYb : BoundedProc Y) (hib : BoundedProc infl) (hgb : BoundedProc g) (hqb : BoundedProc q)
    (hDb : BoundedProc D) (hpb : BoundedProc pib) (htb : BoundedProc tipU)
    (hRb : BoundedProc R)
    (h51 : ∀ t, U t = (fun w => -(Ybar * uc / 2) *
        LargeDistortions.quad51 σ ω θ Φ (g t w) (q t w) (Y t w) (V t w)) + tipU t + R t)
    (w : Ω) :
    Sequences.dsum 𝔼 β U w =
      -LargeDistortions.OmegaW Ybar uc (Moments.calvoKappa α β ω θ σ) θ Φ ω σ *
          Sequences.dsum 𝔼 β
            (LargeDistortions.loss614 (Moments.calvoKappa α β ω θ σ) θ Φ ω σ infl Y g q) w +
        (Sequences.dsum 𝔼 β tipU w -
          LargeDistortions.OmegaW Ybar uc (Moments.calvoKappa α β ω θ σ) θ Φ ω σ * (1 - α) *
            𝔼.E 0 (D 0) w) +
        (Sequences.dsum 𝔼 β R w -
          LargeDistortions.OmegaW Ybar uc (Moments.calvoKappa α β ω θ σ) θ Φ ω σ *
          (Sequences.dsum 𝔼 β (fun t => pib t ^ 2) w -
            Sequences.dsum 𝔼 β (fun t => infl t ^ 2) w)) := by
  refine LargeDistortions.prop614 𝔼 hα0 hα1 hβ0 hβ1 hθ hω hσ hΦ hYb hib hgb hqb hDb hpb htb hRb
    h51 (fun t => ?_) (fun t => ?_) w
  · funext w'
    rw [hVd, Pi.smul_apply, hDd, smul_eq_mul]
    exact CrossSection.crossVar_demand μ ((hG w').int1 (t + 1)) (hdem t w')
  · funext w'
    have h := goods_disp_rec μ (hG w') hα1.ne t
    simp only [sub_zero] at h
    simp only [Pi.add_apply, Pi.smul_apply, Pi.pow_apply, smul_eq_mul, hDd, hpd]
    exact h

/-! ### `κ` consistency -/

/-- Woodford (2003), (2.28), p. 405, and Ch. 5 (1.29) vs Ch. 3 (2.19) (Props. 6.4, 6.14):
without habits (`η = 0`) the habit model's `κ = ξ_p(B + √(B² − 4β(ηφ)²))/2` is the Calvo slope
`κ = ξ_p(ω + σ⁻¹)` (`Moments.calvoKappa`, the `κ` of `PriceDispersion` and
`LargeDistortions`), with `σ⁻¹ = (1 − βη)φ`. -/
theorem habit_kappa_eta_zero {P : HabitWelfare.Par} (hP : P.Std) (hη : P.η = 0) (α : ℝ) :
    P.kappa α = Moments.calvoKappa α P.β P.ω P.θ P.sinv := by
  obtain ⟨-, -, -, -, hφ, hω⟩ := hP
  have hs : Real.sqrt (HabitWelfare.habDisc P.β P.ω P.φ P.η) = P.ω + P.φ := by
    unfold HabitWelfare.habDisc HabitWelfare.habB
    rw [hη, show (P.ω + P.φ * (1 + P.β * 0 ^ 2)) ^ 2 - 4 * P.β * (0 * P.φ) ^ 2 =
      (P.ω + P.φ) ^ 2 by ring]
    exact Real.sqrt_sq (by linarith)
  rw [Moments.calvoKappa_eq]
  unfold HabitWelfare.Par.kappa HabitWelfare.habKappa HabitWelfare.Par.sinv
  rw [hs]
  unfold HabitWelfare.habB
  rw [hη]
  ring

/-- Woodford (2003), (2.28), p. 405, at `η = 0`: the habit model's `λ = κ/θ` is the weight
`κ/θ` of Proposition 6.4 (`PriceDispersion.calvo_weight`). -/
theorem habit_lam_eta_zero {P : HabitWelfare.Par} (hP : P.Std) (hη : P.η = 0) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hθ : 0 < P.θ) :
    P.lam α = Moments.calvoKappa α P.β P.ω P.θ P.sinv / P.θ := by
  rw [HabitWelfare.lam_eq_kappa_div_theta hP hα0 hα1 hθ, habit_kappa_eta_zero hP hη]

/-- Woodford (2003), (2.21), p. 400, at `η = 0`: the habit model's normalising factor `Λ` is
Proposition 6.4's `Θ = ½θ(1 + ωθ)α/((1 − α)(1 − αβ))` (`PriceDispersion.ThetaCalvo`). -/
theorem habit_Lam_eta_zero (P : HabitWelfare.Par) (hη : P.η = 0) (α : ℝ) :
    P.Lam α = PriceDispersion.ThetaCalvo α P.β P.θ P.ω := by
  unfold HabitWelfare.Par.Lam PriceDispersion.ThetaCalvo Moments.calvoK
  rw [hη]
  ring

end Woodford.StabilizationWelfare.Links
