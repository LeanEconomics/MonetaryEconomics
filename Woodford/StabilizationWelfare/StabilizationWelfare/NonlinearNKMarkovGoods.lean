/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearNKMarkovMeasure
import StabilizationWelfare.NonlinearNKMarkovGeneral
import StabilizationWelfare.Links
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration

/-!
# The goods-level cross-section behind the Markov equilibrium, and the Ramsey obstruction

Woodford (2003), *Interest and Prices*, Chapter 6, §2.2 (pp. 396–405: the Calvo cross-section,
(2.12), (2.20), Proposition 6.3), App. E.2 (p. 695, (E.8)), §5 (pp. 455–463) and Chapter 3
(the Calvo model); Chapter 7 for optimal policy.

## The Calvo goods population (`GoodsPop`)

The goods are `G = ℕ → Bool` (a good's reset history: `g t = true` iff it resets at `t`) with the
product of Bernoulli(`1 − α`) laws (`bern`, `goodsMeasure`; Mathlib's `Measure.infinitePi`). Reset
histories are independent across dates, so the goods that do not reset at `t` are EXACTLY
representative of the date-`t` cross-section (`setIntegral_compl_reset`, from the independence of
the past and of the date-`t` draw, `indep_past_now`). Given any path of reset prices `p*_t`, log
prices follow the Calvo rule (`priceProc`), and

* `calvo_goodsPop`: the population satisfies `Links.GoodsPop.Calvo` (Chapter 3's Calvo model as a
  measure on goods), hence the exact dispersion recursion of log prices `hD`
  (`Links.goods_disp_rec`, `goods_hD`) and the demand relation `hV` (`goods_hV`);
* `integral_reset_split`: for every `φ`, `∫φ(p_{t+1}) = (1−α)φ(p*_t) + α∫φ(p_t)`;
* `goods_priceIndex`: if `(π_t, x̂_t)` satisfy the model's price index and `p*_t = log P_t + x̂_t`,
  the Dixit–Stiglitz index of the population is the model's `P_t`, so index inflation is the
  model's `π_t`;
* `goods_dispersion`: the population's efficiency-dispersion index `∫(p(i)/P)^{−θ(1+ω)}` obeys
  EXACTLY the model's law `NonlinearNKMarkovLinks.dispLaw`;
* `goods_of_markov`: along any shock path, the Markov equilibrium's `(π, x̂)` define such a
  population.

What remains for `BridgeLinks.prop615_goods_layerB` is stated in the report: that theorem needs a
FINITE weighted cross-section (`Fintype ι`), whereas the Calvo population is necessarily a
continuum (every reset history occurs with positive density only as a measure).

## Sequence-space uniqueness on a measure-theoretic system

`MeasSeqEqm` (the conditions almost surely with Mathlib's `condExp`), `seqEqm_of_meas` and
`meas_seq_uniqueness`: on a finite, fully supported probability space the almost-sure conditions
are the core conditions of bridge (b), so `NonlinearNKMarkovGeneral.seq_uniqueness` applies.

## The Ramsey obstruction

`priceIndex_curve_deriv` and `dispLaw_pi_deriv`: along the price-index manifold the response of
dispersion to inflation is `θ(1+ω)α(Δ_{t−1} − 1)`. Hence in the Ramsey first-order condition for
inflation the multiplier of the dispersion law is multiplied by a term in the lagged dispersion:
under optimal policy `Δ` feeds back into the forward-looking block (unlike under the Taylor rule,
`NonlinearNKMarkovLinks.eqm_lift_iff`), so the Markov equilibrium needs policy functions of
`(Δ_{t−1}, λ_{t−1}, s_t)` composed with the endogenous law of motion.
-/

namespace Woodford.StabilizationWelfare.NonlinearNKMarkovGoods

open MeasureTheory ProbabilityTheory Filter Topology
open CrossSection (crossVar crossMean)

/-! ## The goods population -/

/-- The goods: reset histories `g : ℕ → Bool`. -/
abbrev Goods : Type := ℕ → Bool

/-- Woodford (2003), Ch. 3 (the Calvo lottery): the law of one date's reset draw,
Bernoulli(`1 − α`). -/
noncomputable def bernM (α : ℝ) : Measure Bool :=
  ENNReal.ofReal (1 - α) • Measure.dirac true + ENNReal.ofReal α • Measure.dirac false

/-- Woodford (2003), Ch. 3: the reset draw has total mass one. -/
theorem bernM_univ {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : bernM α Set.univ = 1 := by
  simp only [bernM, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) hα0]; simp

/-- Woodford (2003), Ch. 3: the reset draw as a probability measure. -/
noncomputable def bern (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : ProbabilityMeasure Bool :=
  ⟨bernM α, ⟨bernM_univ hα0 hα1⟩⟩

/-- Woodford (2003), App. E.2, p. 695: the population of goods, independent reset draws
across dates. -/
noncomputable def goodsMeasure (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : Measure Goods :=
  Measure.infinitePi fun _ : ℕ => (bern α hα0 hα1 : Measure Bool)

/-- Woodford (2003), App. E.2: the goods population is a probability space. -/
theorem isProb_goods {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    IsProbabilityMeasure (goodsMeasure α hα0 hα1) := by
  unfold goodsMeasure; infer_instance

/-- The information in the draws before date `t`. -/
noncomputable abbrev past (t : ℕ) : MeasurableSpace Goods :=
  ⨆ j ∈ Set.Iio t, MeasurableSpace.comap (fun g : Goods => g j) inferInstance

/-- The information in the date-`t` draw. -/
noncomputable abbrev now (t : ℕ) : MeasurableSpace Goods :=
  ⨆ j ∈ ({t} : Set ℕ), MeasurableSpace.comap (fun g : Goods => g j) inferInstance

/-- Woodford (2003), App. E.2: the reset draws are independent across dates, so the past is
independent of the date-`t` draw. -/
theorem indep_past_now {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (t : ℕ) :
    Indep (past t) (now t) (goodsMeasure α hα0 hα1) := by
  have hind : iIndep (fun j => MeasurableSpace.comap (fun g : Goods => g j) inferInstance)
      (goodsMeasure α hα0 hα1) :=
    (iIndepFun_infinitePi (P := fun _ : ℕ => (bern α hα0 hα1 : Measure Bool))
      (X := fun _ => id) (fun _ => measurable_id)).iIndep
  exact indep_iSup_of_disjoint (fun j => (measurable_pi_apply j).comap_le) hind
    (by simp : Disjoint (Set.Iio t) {t})

/-- The past draws are measurable events of the goods space. -/
theorem past_le (t : ℕ) : past t ≤ MeasurableSpace.pi :=
  iSup₂_le fun j _ => (measurable_pi_apply j).comap_le

/-- Woodford (2003), App. E.2: information about past draws accumulates. -/
theorem past_mono {s t : ℕ} (h : s ≤ t) : past s ≤ past t :=
  iSup₂_le fun j hj => le_iSup₂ (f := fun j (_ : j ∈ Set.Iio t) =>
    MeasurableSpace.comap (fun g : Goods => g j) inferInstance) j
      (lt_of_lt_of_le (Set.mem_Iio.1 hj) h)

/-- Woodford (2003), App. E.2: a draw before `t` is part of the date-`t` past. -/
theorem measurable_draw_past {s t : ℕ} (h : s < t) :
    Measurable[past t] (fun g : Goods => g s) :=
  Measurable.of_comap_le (le_iSup₂ (f := fun j (_ : j ∈ Set.Iio t) =>
    MeasurableSpace.comap (fun g : Goods => g j) inferInstance) s h)

/-- Woodford (2003), App. E.2: the date-`t` draw is `now t`-measurable. -/
theorem measurable_draw_now (t : ℕ) : Measurable[now t] (fun g : Goods => g t) :=
  Measurable.of_comap_le (le_iSup₂ (f := fun j (_ : j ∈ ({t} : Set ℕ)) =>
    MeasurableSpace.comap (fun g : Goods => g j) inferInstance) t rfl)

/-- The goods that reset at date `t`. -/
def reset (t : ℕ) : Set Goods := {g | g t = true}

/-- Woodford (2003), Ch. 3: the reset set is measurable. -/
theorem measurableSet_reset (t : ℕ) : MeasurableSet (reset t) := by
  have : reset t = (fun g : Goods => g t) ⁻¹' {true} := rfl
  rw [this]
  exact measurable_pi_apply t (measurableSet_singleton true)

/-- Woodford (2003), Ch. 3: a fraction `1 − α` of goods resets at every date. -/
theorem measure_reset {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (t : ℕ) :
    (goodsMeasure α hα0 hα1).real (reset t) = 1 - α := by
  have hmap := Measure.infinitePi_map_eval (fun _ : ℕ => (bern α hα0 hα1 : Measure Bool)) t
  have h : goodsMeasure α hα0 hα1 (reset t) = (bern α hα0 hα1 : Measure Bool) {true} := by
    rw [← hmap, Measure.map_apply (measurable_pi_apply t) (measurableSet_singleton true)]
    rfl
  rw [Measure.real, h]
  change (bernM α {true}).toReal = 1 - α
  simp [bernM, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 - α)]

/-- Woodford (2003), App. E.2, p. 695 (**the non-resetting goods are exactly representative**):
for every function `f` of the draws before `t`, `∫_{not reset at t} f = α∫f`. -/
theorem setIntegral_compl_reset {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {t : ℕ} {f : Goods → ℝ}
    (hf : Measurable[past t] f) :
    ∫ g in (reset t)ᶜ, f g ∂(goodsMeasure α hα0 hα1) = α * ∫ g, f g ∂(goodsMeasure α hα0 hα1) := by
  have := isProb_goods hα0 hα1
  set μ := goodsMeasure α hα0 hα1
  set h : Goods → ℝ := fun g => if g t = true then 0 else 1 with hh
  have hhm : Measurable[now t] h :=
    Measurable.ite ((measurable_draw_now t) (measurableSet_singleton true)) measurable_const
      measurable_const
  have hind : IndepFun h f μ := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left (indep_past_now hα0 hα1 t).symm
      hhm.comap_le) hf.comap_le
  have hfm : Measurable f := hf.mono (past_le t) le_rfl
  have hhm' : Measurable h := hhm.mono (iSup₂_le fun j _ => (measurable_pi_apply j).comap_le)
    le_rfl
  have hint := hind.integral_mul_eq_mul_integral hhm'.aestronglyMeasurable
    hfm.aestronglyMeasurable
  have h1 : ∫ g, h g ∂μ = α := by
    have e : h = (reset t)ᶜ.indicator (fun _ => (1 : ℝ)) := by
      funext g; simp only [hh, reset, Set.indicator, Set.mem_compl_iff, Set.mem_ofPred_eq]
      cases g t <;> simp
    rw [e, integral_indicator (measurableSet_reset t).compl, setIntegral_const, smul_eq_mul,
      mul_one, measureReal_compl (measurableSet_reset t), probReal_univ, measure_reset hα0 hα1]
    ring
  rw [← integral_indicator (measurableSet_reset t).compl]
  have e2 : (reset t)ᶜ.indicator f = h * f := by
    funext g; simp only [hh, reset, Set.indicator, Set.mem_compl_iff, Set.mem_ofPred_eq,
      Pi.mul_apply]
    cases g t <;> simp
  rw [e2, hint, h1]

/-- The complementary statement: `∫_{reset at t} f = (1 − α)∫f`. -/
theorem setIntegral_reset {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {t : ℕ} {f : Goods → ℝ}
    (hf : Measurable[past t] f) {C : ℝ} (hC : ∀ g, |f g| ≤ C) :
    ∫ g in reset t, f g ∂(goodsMeasure α hα0 hα1) =
      (1 - α) * ∫ g, f g ∂(goodsMeasure α hα0 hα1) := by
  have := isProb_goods hα0 hα1
  have hfm : Measurable f := hf.mono (past_le t) le_rfl
  have hint : Integrable f (goodsMeasure α hα0 hα1) :=
    Integrable.of_bound hfm.aestronglyMeasurable C (Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs]; exact hC g)
  have := integral_add_compl (measurableSet_reset t) hint
  rw [setIntegral_compl_reset hα0 hα1 hf] at this
  linarith

/-! ## Log prices under Calvo pricing -/

/-- Woodford (2003), Ch. 3 (**log prices of the goods**): `p_0 = log P_{−1}` for every good;
a good that resets at `t` charges `p*_t`, the others keep their price. -/
def priceProc (lp0 : ℝ) (ps : ℕ → ℝ) : ℕ → Goods → ℝ
  | 0 => fun _ => lp0
  | t + 1 => fun g => if g t = true then ps t else priceProc lp0 ps t g

/-- Woodford (2003), Ch. 3: the date-`t` log price depends only on draws before `t`. -/
theorem measurable_priceProc (lp0 : ℝ) (ps : ℕ → ℝ) (t : ℕ) :
    Measurable[past t] (priceProc lp0 ps t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact Measurable.ite ((measurable_draw_past (Nat.lt_succ_self t))
      (measurableSet_singleton true)) measurable_const (ih.mono (past_mono (Nat.le_succ t)) le_rfl)

/-- Woodford (2003), Ch. 3: log prices stay within the bound of the reset prices. -/
theorem abs_priceProc_le {lp0 : ℝ} {ps : ℕ → ℝ} {C : ℝ} (h0 : |lp0| ≤ C)
    (hps : ∀ t, |ps t| ≤ C) (t : ℕ) (g : Goods) : |priceProc lp0 ps t g| ≤ C := by
  induction t with
  | zero => exact h0
  | succ t ih =>
    simp only [priceProc]
    split_ifs
    · exact hps t
    · exact ih

/-- Woodford (2003), (E.8) ingredients (**the reset split**): for every function `φ` bounded on
the price range, `∫φ(p_{t+1}) = (1 − α)φ(p*_t) + α∫φ(p_t)`. -/
theorem integral_reset_split {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {lp0 : ℝ} {ps : ℕ → ℝ}
    {φ : ℝ → ℝ} (hφ : Measurable φ) {B : ℝ}
    (hB : ∀ t g, |φ (priceProc lp0 ps t g)| ≤ B) (t : ℕ) :
    ∫ g, φ (priceProc lp0 ps (t + 1) g) ∂(goodsMeasure α hα0 hα1) =
      (1 - α) * φ (ps t) + α * ∫ g, φ (priceProc lp0 ps t g) ∂(goodsMeasure α hα0 hα1) := by
  have := isProb_goods hα0 hα1
  set μ := goodsMeasure α hα0 hα1
  have hm : Measurable[past t] (fun g => φ (priceProc lp0 ps t g)) :=
    hφ.comp (measurable_priceProc lp0 ps t)
  have hm1 : Measurable (fun g => φ (priceProc lp0 ps (t + 1) g)) :=
    hφ.comp ((measurable_priceProc lp0 ps (t + 1)).mono (past_le _) le_rfl)
  have hint : Integrable (fun g => φ (priceProc lp0 ps (t + 1) g)) μ :=
    Integrable.of_bound hm1.aestronglyMeasurable B (Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs]; exact hB _ g)
  rw [← integral_add_compl (measurableSet_reset t) hint]
  have e1 : ∫ g in reset t, φ (priceProc lp0 ps (t + 1) g) ∂μ =
      ∫ g in reset t, (fun _ => φ (ps t)) g ∂μ :=
    setIntegral_congr_fun (measurableSet_reset t) fun g hg => by
      simp [priceProc, show g t = true from hg]
  have e2 : ∫ g in (reset t)ᶜ, φ (priceProc lp0 ps (t + 1) g) ∂μ =
      ∫ g in (reset t)ᶜ, φ (priceProc lp0 ps t g) ∂μ :=
    setIntegral_congr_fun (measurableSet_reset t).compl fun g hg => by
      have : ¬ g t = true := hg
      simp [priceProc, this]
  rw [e1, e2, setIntegral_const, setIntegral_compl_reset hα0 hα1 hm,
    measure_reset hα0 hα1, smul_eq_mul]

/-- Woodford (2003), Ch. 3 and App. E.2 (**the goods population is a Calvo population**): it
satisfies `Links.GoodsPop.Calvo` (reset mass `1 − α`, representative non-resetters, reset goods at
the common `p*_t`, the others unchanged). -/
theorem calvo_goodsPop {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {lp0 C : ℝ} {ps : ℕ → ℝ}
    (h0 : |lp0| ≤ C) (hps : ∀ t, |ps t| ≤ C) :
    Links.GoodsPop.Calvo (goodsMeasure α hα0 hα1) α (priceProc lp0 ps) reset ps
      fun _ => 0 := by
  have := isProb_goods hα0 hα1
  have hb := abs_priceProc_le h0 hps
  have hmeas : ∀ t, Measurable (priceProc lp0 ps t) := fun t =>
    (measurable_priceProc lp0 ps t).mono (past_le t) le_rfl
  have hC : 0 ≤ C := (abs_nonneg _).trans h0
  refine ⟨measurableSet_reset, measure_reset hα0 hα1, fun t => ?_, fun t => ?_, fun t => ?_,
    fun t => ?_, fun t g hg => ?_, fun t g hg => ?_⟩
  · exact Integrable.of_bound (hmeas t).aestronglyMeasurable C
      (Eventually.of_forall fun g => by rw [Real.norm_eq_abs]; exact hb t g)
  · exact Integrable.of_bound ((hmeas t).pow_const 2).aestronglyMeasurable (C ^ 2)
      (Eventually.of_forall fun g => by
        rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb t g) 2)
  · exact setIntegral_compl_reset hα0 hα1 (measurable_priceProc lp0 ps t)
  · exact setIntegral_compl_reset hα0 hα1 ((measurable_priceProc lp0 ps t).pow_const 2)
  · simp [priceProc, show g t = true from hg]
  · have : ¬ g t = true := hg
    simp [priceProc, this]

/-- Woodford (2003), (2.20), p. 399 (**the hypothesis `hD` from the population**): the
cross-sectional variance of log prices obeys `Δ_t = αΔ_{t−1} + α/(1−α)(P̄_t − P̄_{t−1})²`
exactly. -/
theorem goods_hD {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {lp0 C : ℝ} {ps : ℕ → ℝ}
    (h0 : |lp0| ≤ C) (hps : ∀ t, |ps t| ≤ C) (t : ℕ) :
    crossVar (goodsMeasure α hα0 hα1.le) (priceProc lp0 ps (t + 1)) =
      α * crossVar (goodsMeasure α hα0 hα1.le) (priceProc lp0 ps t) +
        α / (1 - α) * (crossMean (goodsMeasure α hα0 hα1.le) (priceProc lp0 ps (t + 1)) -
          crossMean (goodsMeasure α hα0 hα1.le) (priceProc lp0 ps t) - 0) ^ 2 := by
  have := isProb_goods hα0 hα1.le
  exact Links.goods_disp_rec _ (calvo_goodsPop hα0 hα1.le h0 hps) hα1.ne t

/-- Woodford (2003), (2.12), p. 396 (**the hypothesis `hV` from the population**): with
Dixit–Stiglitz demand `log y_t(i) = log Y_t − θ(p_t(i) − log P_t)`,
`var_i log y_t = θ² var_i p_t`. -/
theorem goods_hV {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {lp0 C θ : ℝ} {ps : ℕ → ℝ}
    (h0 : |lp0| ≤ C) (hps : ∀ t, |ps t| ≤ C) (LY LP : ℕ → ℝ) (t : ℕ) :
    crossVar (goodsMeasure α hα0 hα1)
        (fun g => LY t - θ * (priceProc lp0 ps (t + 1) g - LP t)) =
      θ ^ 2 * crossVar (goodsMeasure α hα0 hα1) (priceProc lp0 ps (t + 1)) := by
  have := isProb_goods hα0 hα1
  exact CrossSection.crossVar_demand _ ((calvo_goodsPop hα0 hα1 h0 hps).int1 (t + 1))
    fun _ => rfl

/-! ## The population reproduces the model's aggregates -/

/-- Woodford (2003), §5 (**the population's Dixit–Stiglitz index is the model's price level**):
if `(π_t, x̂_t)` satisfy the price index `α(e^{(θ−1)π_t} − 1) + (1−α)(e^{−(θ−1)x̂_t} − 1) = 0`,
`log P_{t} = log P_{t−1} + π_t` and `p*_t = log P_t + x̂_t`, then
`∫e^{(1−θ)p_t(i)} = e^{(1−θ)log P_{t−1}}` at every date. -/
theorem goods_priceIndex {α θ : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {lp0 C : ℝ} {π xh : ℕ → ℝ}
    (lP : ℕ → ℝ) (hlP0 : lP 0 = lp0) (hlP : ∀ t, lP (t + 1) = lP t + π t)
    (hPI : ∀ t, α * (Real.exp ((θ - 1) * π t) - 1) +
      (1 - α) * (Real.exp (-((θ - 1) * xh t)) - 1) = 0)
    (h0 : |lp0| ≤ C) (hps : ∀ t, |lP (t + 1) + xh t| ≤ C) (t : ℕ) :
    ∫ g, Real.exp ((1 - θ) * priceProc lp0 (fun s => lP (s + 1) + xh s) t g)
        ∂(goodsMeasure α hα0 hα1) = Real.exp ((1 - θ) * lP t) := by
  have := isProb_goods hα0 hα1
  have hB : ∀ s g, |Real.exp ((1 - θ) * priceProc lp0 (fun s => lP (s + 1) + xh s) s g)| ≤
      Real.exp (|1 - θ| * C) := fun s g => by
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.2
    calc (1 - θ) * _ ≤ |(1 - θ) * priceProc lp0 (fun s => lP (s + 1) + xh s) s g| :=
          le_abs_self _
      _ ≤ |1 - θ| * C := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_priceProc_le h0 hps s g)
            (abs_nonneg _)
  induction t with
  | zero =>
    simp [priceProc, hlP0]
  | succ t ih =>
    rw [integral_reset_split hα0 hα1 (φ := fun v => Real.exp ((1 - θ) * v))
      (by fun_prop) hB t, ih, hlP]
    have e := hPI t
    have k1 : Real.exp ((1 - θ) * (lP t + π t + xh t)) =
        Real.exp ((1 - θ) * (lP t + π t)) * Real.exp (-((θ - 1) * xh t)) := by
      rw [← Real.exp_add]; ring_nf
    have k2 : Real.exp ((1 - θ) * lP t) =
        Real.exp ((1 - θ) * (lP t + π t)) * Real.exp ((θ - 1) * π t) := by
      rw [← Real.exp_add]; ring_nf
    rw [k1, k2]
    linear_combination Real.exp ((1 - θ) * (lP t + π t)) * e

/-- Woodford (2003), (2.12)–(2.13) and §5 (**the population's dispersion index obeys the model's
exact law**): with `Δ_t = ∫e^{−θ(1+ω)(p_{t+1}(i) − log P_t)}` and the reset gap `x̂_t`,
`Δ_t = αe^{θ(1+ω)π_t}Δ_{t−1} + (1−α)e^{−θ(1+ω)x̂_t}`, `Δ_{−1} = 1`. -/
theorem goods_dispersion {α a : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {lp0 C : ℝ} {π xh : ℕ → ℝ}
    (lP : ℕ → ℝ) (hlP : ∀ t, lP (t + 1) = lP t + π t)
    (h0 : |lp0| ≤ C) (hps : ∀ t, |lP (t + 1) + xh t| ≤ C) (t : ℕ) :
    ∫ g, Real.exp (-(a * (priceProc lp0 (fun s => lP (s + 1) + xh s) (t + 1) g - lP (t + 1))))
        ∂(goodsMeasure α hα0 hα1) =
      α * Real.exp (a * π t) * ∫ g, Real.exp (-(a * (priceProc lp0 (fun s => lP (s + 1) + xh s)
          t g - lP t))) ∂(goodsMeasure α hα0 hα1) +
        (1 - α) * Real.exp (-(a * xh t)) := by
  have := isProb_goods hα0 hα1
  set c := lP (t + 1)
  have hB : ∀ s g, |Real.exp (-(a * (priceProc lp0 (fun s => lP (s + 1) + xh s) s g - c)))| ≤
      Real.exp (|a| * (C + |c|)) := fun s g => by
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.2
    have h1 := abs_priceProc_le h0 hps s g
    calc -(a * (_ - c)) ≤ |a * (priceProc lp0 (fun s => lP (s + 1) + xh s) s g - c)| :=
          neg_le_abs _
      _ ≤ |a| * (C + |c|) := by
          rw [abs_mul]; refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          exact (abs_sub _ _).trans (by linarith)
  rw [integral_reset_split hα0 hα1 (φ := fun v => Real.exp (-(a * (v - c)))) (by fun_prop)
    hB t]
  have e : ∀ g, Real.exp (-(a * (priceProc lp0 (fun s => lP (s + 1) + xh s) t g - c))) =
      Real.exp (a * π t) * Real.exp (-(a * (priceProc lp0 (fun s => lP (s + 1) + xh s) t g -
        lP t))) := fun g => by
    rw [← Real.exp_add, show c = lP t + π t from hlP t]; ring_nf
  simp only [e, integral_const_mul]
  have e2 : Real.exp (-(a * (lP (t + 1) + xh t - c))) = Real.exp (-(a * xh t)) := by
    congr 1; ring
  rw [e2]
  ring

/-- Woodford (2003), §5 (**the Markov equilibrium defines the goods population**): along any
path `s_t` of the exogenous state, a Markov equilibrium `w` of amplitude `ε` gives
`π_t = w(s_t)₁` and `x̂_t = (K̂ − F̂)/(1+ωθ)` satisfying the price index at every date, so (with
`log P_t` cumulated from `π`) the goods population of `goods_priceIndex`/`goods_dispersion`
reproduces its price level and its dispersion law `NonlinearNKMarkovLinks.dispLaw` exactly. -/
theorem goods_of_markov {p : NonlinearNKMarkov.Par} {S : Type*} [Fintype S]
    {P : S → S → ℝ} (ξ : S → Fin 5 → ℝ) (ε : ℝ) (w : S → Fin 4 → ℝ)
    (hw : NonlinearNKMarkov.IsMarkovEqm p (NonlinearNKMarkov.chainOp P) ξ ε w) (sh : ℕ → S)
    (t : ℕ) :
    p.α * (Real.exp ((p.θ - 1) * w (sh t) 1) - 1) +
        (1 - p.α) * (Real.exp (-((p.θ - 1) * ((w (sh t) 3 - w (sh t) 2) / p.c0))) - 1) = 0 ∧
      ∀ Δ, NonlinearNKMarkovLinks.dispLaw p Δ (w (sh t)) =
        p.α * Real.exp (p.θ * (1 + p.ω) * w (sh t) 1) * Δ +
          (1 - p.α) * Real.exp (-(p.θ * (1 + p.ω) * ((w (sh t) 3 - w (sh t) 2) / p.c0))) := by
  refine ⟨NonlinearNKMarkovMeasure.meas_priceIndex (Ω := Unit) ξ ε w hw (fun t _ => sh t) t (),
    fun Δ => ?_⟩
  unfold NonlinearNKMarkovLinks.dispLaw
  ring

/-! ## Sequence-space uniqueness on a measure-theoretic system (finite, full support) -/

/-- Woodford (2003), (A.11) on a probability space (**the exact stochastic conditions almost
surely**): `Q(e_t, z_t) + μ[N(e_{t+1}, z_{t+1}) | 𝓕_t] = 0` a.s., componentwise. -/
def MeasSeqEqm {Ω : Type*} [MeasurableSpace Ω] (p : NonlinearNKMarkov.Par)
    (E : ExpectationsMeasure.MeasExpectationSystem Ω) (e : ℕ → Ω → Fin 5 → ℝ)
    (z : ℕ → Ω → Fin 4 → ℝ) : Prop :=
  ∀ t (i : Fin 4), (fun ω => NonlinearNKMarkov.Qmap p (e t ω, z t ω) i +
    E.E t (fun ω' => NonlinearNKMarkov.Nmap p (e (t + 1) ω', z (t + 1) ω') i) ω) =ᵐ[E.μ] 0

/-- Bridge (b): on a finite, fully supported space the almost-sure conditions are the core
conditions `NonlinearNKMarkovGeneral.SeqEqm` for `toExpectationSystem`. -/
theorem seqEqm_of_meas {Ω : Type*} [MeasurableSpace Ω] [Finite Ω] [DiscreteMeasurableSpace Ω]
    {p : NonlinearNKMarkov.Par} (E : ExpectationsMeasure.MeasExpectationSystem Ω)
    (hfull : ∀ ω, E.μ {ω} ≠ 0) {e : ℕ → Ω → Fin 5 → ℝ} {z : ℕ → Ω → Fin 4 → ℝ}
    (h : MeasSeqEqm p E e z) :
    NonlinearNKMarkovGeneral.SeqEqm p (E.toExpectationSystem hfull) e z :=
  fun t ω => by
    funext i
    have := congrFun (E.eq_of_ae_eq hfull (h t i)) ω
    simpa [ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem_E] using this

/-- Woodford (2003), App. A.3 and Proposition 4.3 (**sequence-space uniqueness with Mathlib's
conditional expectations, finite fully supported space**): two bounded solutions within `ρ` of the
almost-sure stochastic equilibrium conditions coincide. -/
theorem meas_seq_uniqueness {p : NonlinearNKMarkov.Par} (hp : p.Std) :
    ∃ ρ > 0, ∀ (Ω : Type*) [MeasurableSpace Ω] [Finite Ω] [DiscreteMeasurableSpace Ω]
      (E : ExpectationsMeasure.MeasExpectationSystem Ω), (∀ ω, E.μ {ω} ≠ 0) →
      ∀ (e : ℕ → Ω → Fin 5 → ℝ) (z z' : ℕ → Ω → Fin 4 → ℝ), (∀ t ω, ‖e t ω‖ ≤ ρ) →
        (∀ t ω, ‖z t ω‖ ≤ ρ) → (∀ t ω, ‖z' t ω‖ ≤ ρ) → MeasSeqEqm p E e z →
          MeasSeqEqm p E e z' → z = z' := by
  obtain ⟨ρ, hρ, h⟩ := NonlinearNKMarkovGeneral.seq_uniqueness hp
  exact ⟨ρ, hρ, fun Ω _ _ _ E hfull e z z' he hz hz' hE hE' =>
    h Ω (E.toExpectationSystem hfull) e z z' he hz hz' (seqEqm_of_meas E hfull hE)
      (seqEqm_of_meas E hfull hE')⟩

/-! ## The Ramsey obstruction -/

/-- Woodford (2003), Ch. 3 (**the reset gap along the price-index manifold**): if `x(π)` solves the
price index identically near `0`, with `x(0) = 0` and `x` differentiable at `0`, then
`x′(0) = α/(1 − α)`. -/
theorem priceIndex_curve_deriv {α θ : ℝ} (hα1 : α < 1) (hθ : 1 < θ) {x : ℝ → ℝ} {x' : ℝ}
    (hx : HasDerivAt x x' 0) (hx0 : x 0 = 0)
    (hPI : ∀ π, α * (Real.exp ((θ - 1) * π) - 1) +
      (1 - α) * (Real.exp (-((θ - 1) * x π)) - 1) = 0) :
    x' = α / (1 - α) := by
  have a1 := HasDerivAt.const_mul α (HasDerivAt.sub_const 1 (HasDerivAt.exp
    (HasDerivAt.const_mul (θ - 1) (hasDerivAt_id (0 : ℝ)))))
  have a2 := HasDerivAt.const_mul (1 - α) (HasDerivAt.sub_const 1 (HasDerivAt.exp
    (HasDerivAt.neg (HasDerivAt.const_mul (θ - 1) hx))))
  have hsum := HasDerivAt.add a1 a2
  have h2 : HasDerivAt (fun π => α * (Real.exp ((θ - 1) * id π) - 1) +
      (1 - α) * (Real.exp (-((θ - 1) * x π)) - 1)) 0 0 := by
    have : (fun π => α * (Real.exp ((θ - 1) * id π) - 1) +
        (1 - α) * (Real.exp (-((θ - 1) * x π)) - 1)) = fun _ => 0 := funext fun π => hPI π
    rw [this]; exact hasDerivAt_const _ _
  have e := hsum.unique h2
  simp only [id, Pi.neg_apply, mul_zero, Real.exp_zero, hx0, neg_zero, one_mul, mul_one] at e
  have h1α : 1 - α ≠ 0 := by linarith
  have hθ1 : θ - 1 ≠ 0 := by linarith
  have : (θ - 1) * (α - (1 - α) * x') = 0 := by linear_combination e
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hθ1
  · field_simp; linarith

/-- Woodford (2003), Ch. 7 / §5 (**dispersion responds to inflation in proportion to lagged
dispersion minus one**): along the price-index manifold (`x(0) = 0`, `x′(0) = α/(1−α)`),
`d/dπ [αΔe^{aπ} + (1−α)e^{−a x(π)}] = aα(Δ − 1)` at `π = 0`, `a = θ(1+ω)`. In the Ramsey
first-order condition for inflation this term multiplies the multiplier of the dispersion law, so
the lagged dispersion `Δ_{t−1}` enters the forward-looking block at FIRST order whenever
`Δ_{t−1} ≠ 1`: the dispersion-independence of the Taylor-rule equilibrium
(`NonlinearNKMarkovLinks.eqm_lift_iff`) fails under optimal policy. -/
theorem dispLaw_pi_deriv {α a Δ : ℝ} (hα1 : α < 1) {x : ℝ → ℝ}
    (hx : HasDerivAt x (α / (1 - α)) 0) (hx0 : x 0 = 0) :
    HasDerivAt (fun π => α * Δ * Real.exp (a * π) + (1 - α) * Real.exp (-(a * x π)))
      (a * α * (Δ - 1)) 0 := by
  have a1 := HasDerivAt.const_mul (α * Δ) (HasDerivAt.exp
    (HasDerivAt.const_mul a (hasDerivAt_id (0 : ℝ))))
  have a2 := HasDerivAt.const_mul (1 - α) (HasDerivAt.exp
    (HasDerivAt.neg (HasDerivAt.const_mul a hx)))
  have hsum := HasDerivAt.add a1 a2
  have h1α : 1 - α ≠ 0 := by linarith
  refine hsum.congr_deriv ?_
  simp only [id, Pi.neg_apply, mul_zero, Real.exp_zero, hx0, neg_zero, mul_one, one_mul]
  field_simp
  ring

end Woodford.StabilizationWelfare.NonlinearNKMarkovGoods
