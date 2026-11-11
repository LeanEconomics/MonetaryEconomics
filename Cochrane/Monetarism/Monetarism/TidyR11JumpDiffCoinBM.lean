/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR11JumpDiffStep
import Monetarism.TidyR10TwoBMExist
import Monetarism.TidyR10DoobProductStep
import Monetarism.TidyR7ProductStepCoin
import Monetarism.TidyR7ProductStepJumpCoin

/-!
# A Brownian motion and an independent coin revealed at time 1

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for the jump-diffusion product
step of (1.32) (`TidyR11JumpDiffStep`): a probability space carrying BOTH a Brownian motion and a
jump martingale. On the Brownian filtration alone every martingale is continuous, so a
martingale jump at a fixed date needs extra information: here a fair coin, independent of `W`,
revealed at time `1`.

## Main definitions

* `cbMeasure = gaussSeq ⊗ coinMeasure` on `(ℕ → ℝ) × Bool`; `cbW t ω = bmPath t ω.1`.
* `cbF u = σ(W_r, r ≤ u) ⊔ σ(coin revealed at 1)` (`coinFiltration` pulled back by the second
  projection).
* `cbJ e u ω = e·ξ(ω)·1{u ≥ 1}`, `ξ = ±1`: the jump martingale.

## Main results

* `isBrownianReal_cbW`, `cbF_isBM`: `W` is a Brownian motion (every path continuous) and `cbF`
  is admissible for it (`TidyR7BrownianQV.BMFiltration`): the coin does not disturb the
  independence of Brownian increments (`TidyR10TwoBMExist.indep_sup_sup`).
* `martingale_cbJ`: `e·ξ·1{u ≥ 1}` is a martingale for `cbF` (the coin is independent of
  `σ(W_r, r ≤ u)` for `u < 1`).
* `itoProcess_const_mul_bm`: `c·W` is a driftless Itô process with diffusion `c`.
* `cb_integrable_pathSup_mul_pathVar`: the domination conditions of
  `TidyR7ProductStepJump.JumpStepData` for processes bounded by `a + b|W|` against
  bounded-variation factors with bounded measurable variation.
-/

namespace Cochrane.Monetarism.TidyR11JumpDiffCoinBM

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesIntegral Cochrane.Monetarism.TidyR7StieltjesSums
  Cochrane.Monetarism.TidyR7CondDominated Cochrane.Monetarism.TidyR7ProductStep
  Cochrane.Monetarism.TidyR7BrownianTools Cochrane.Monetarism.TidyR7BrownianQV
  Cochrane.Monetarism.TidyR7BrownianSchauder Cochrane.Monetarism.TidyR7BrownianExist
  Cochrane.Monetarism.TidyR7ItoIntegral Cochrane.Monetarism.TidyR7ItoProcess
  Cochrane.Monetarism.TidyR7ProductStepCoin Cochrane.Monetarism.TidyR7ProductStepJumpCoin
  Cochrane.Monetarism.TidyR10TwoBMExist Cochrane.Monetarism.TidyR10DoobIto
  Cochrane.Monetarism.TidyR10DoobContinuous Cochrane.Monetarism.TidyR10DoobProductStep
open scoped NNReal

/-! ## The space -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the product of the Gaussian sequence space and the
fair coin, `gaussSeq ⊗ coinMeasure`. -/
noncomputable def cbMeasure : Measure ((ℕ → ℝ) × Bool) := gaussSeq.prod coinMeasure

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `cbMeasure` is a probability measure. -/
theorem isProbabilityMeasure_cbMeasure : IsProbabilityMeasure cbMeasure := by
  have := isProbabilityMeasure_gaussSeq
  unfold cbMeasure
  infer_instance

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the Brownian motion `W_t(ω) = bmPath t ω.1`. -/
noncomputable def cbW (t : ℝ≥0) (ω : (ℕ → ℝ) × Bool) : ℝ := bmPath t ω.1

/-- Cochrane (2023), A1 §1.6, pp. 567–568: each `W_t` is measurable. -/
theorem measurable_cbW (t : ℝ≥0) : Measurable (cbW t) :=
  (measurable_bmPath t).comp measurable_fst

/-- Cochrane (2023), A1 §1.6, pp. 567–568: every path of `W` is continuous. -/
theorem continuous_cbW (ω : (ℕ → ℝ) × Bool) : Continuous fun t => cbW t ω :=
  continuous_bmPath ω.1

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **`W` is a Brownian motion** on the product space
(the first projection carries `cbMeasure` to `gaussSeq`).
Transports `TidyR7BrownianExist.isBrownianReal_bmPath` along the first projection. -/
theorem isBrownianReal_cbW : IsBrownianReal cbW cbMeasure := by
  have := isProbabilityMeasure_gaussSeq
  have hfst : HasLaw Prod.fst gaussSeq cbMeasure := measurePreserving_fst.hasLaw
  exact ⟨⟨fun I => (isBrownianReal_bmPath.hasLaw I).comp hfst⟩,
    Eventually.of_forall fun ω => continuous_bmPath ω.1⟩

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `W` is pre-Brownian.
Transports `TidyR7BrownianExist.isPreBrownianReal_bmPath` along the first projection. -/
theorem isPreBrownianReal_cbW : IsPreBrownianReal cbW cbMeasure :=
  isBrownianReal_cbW.toIsPreBrownianReal

/-! ## The filtration -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (the information `E_t` of (1.32) with a coin):
`cbF u = σ(W_r, r ≤ u) ⊔ σ(coin, if u ≥ 1)`. -/
noncomputable def cbF : Filtration ℝ (inferInstance : MeasurableSpace ((ℕ → ℝ) × Bool)) where
  seq u := MeasurableSpace.comap Prod.fst (bmFiltrationReal bmPath measurable_bmPath u) ⊔
    MeasurableSpace.comap Prod.snd (coinFiltration u)
  mono' _ _ h := sup_le_sup
    (MeasurableSpace.comap_mono ((bmFiltrationReal bmPath measurable_bmPath).mono h))
    (MeasurableSpace.comap_mono (coinFiltration.mono h))
  le' u := sup_le
    ((MeasurableSpace.comap_mono ((bmFiltrationReal bmPath measurable_bmPath).le u)).trans
      measurable_fst.comap_le)
    ((MeasurableSpace.comap_mono (coinFiltration.le u)).trans measurable_snd.comap_le)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the definition of `cbF`. -/
theorem cbF_apply (u : ℝ) : cbF u = MeasurableSpace.comap Prod.fst
    (bmFiltrationReal bmPath measurable_bmPath u) ⊔ MeasurableSpace.comap Prod.snd
      (coinFiltration u) := rfl

/-- Cochrane (2023), A1 §1.6, pp. 567–568: before time `1`, `cbF u` is the Brownian past. -/
theorem cbF_lt {u : ℝ} (hu : u < 1) :
    cbF u = MeasurableSpace.comap Prod.fst (bmFiltrationReal bmPath measurable_bmPath u) := by
  rw [cbF_apply, coinFiltration_lt hu, MeasurableSpace.comap_bot, sup_bot_eq]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the two coordinates are independent under
`cbMeasure` (Mathlib `ProbabilityTheory.indepFun_prod`). -/
theorem cb_indep_fst_snd :
    Indep (MeasurableSpace.comap (Prod.fst : (ℕ → ℝ) × Bool → ℕ → ℝ) inferInstance)
      (MeasurableSpace.comap (Prod.snd : (ℕ → ℝ) × Bool → Bool) inferInstance) cbMeasure := by
  have := isProbabilityMeasure_gaussSeq
  exact (IndepFun_iff_Indep _ _ _).1
    (indepFun_prod (μ := gaussSeq) (ν := coinMeasure) (X := id) (Y := id) measurable_id
      measurable_id)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the independence of a Brownian increment from the
Brownian past on `gaussSeq` transports to the first coordinate of `cbMeasure`. -/
theorem indep_comap_fst_incr {u v : ℝ} (huv : u ≤ v) :
    Indep (MeasurableSpace.comap Prod.fst (MeasurableSpace.comap (incr bmPath u v) inferInstance))
      (MeasurableSpace.comap Prod.fst (bmFiltrationReal bmPath measurable_bmPath u)) cbMeasure := by
  have := isProbabilityMeasure_gaussSeq
  have hmp : MeasurePreserving (Prod.fst : (ℕ → ℝ) × Bool → ℕ → ℝ) cbMeasure gaussSeq :=
    measurePreserving_fst
  have hinc : Measurable (incr bmPath u v) := (measurable_bmPath _).sub (measurable_bmPath _)
  have h := (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath).indep u v huv
  rw [Indep_iff]
  rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  have ha' : MeasurableSet a := hinc.comap_le _ ha
  have hb' : MeasurableSet b := (bmFiltrationReal bmPath measurable_bmPath).le u _ hb
  rw [← Set.preimage_inter, hmp.measure_preimage (ha'.inter hb').nullMeasurableSet,
    hmp.measure_preimage ha'.nullMeasurableSet, hmp.measure_preimage hb'.nullMeasurableSet]
  exact (Indep_iff _ _ _).1 h _ _ ha hb

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the filtration with the coin is admissible for
`W`**: `W_u` is `cbF u`-measurable and the increment `W_v − W_u` is independent of `cbF u`. -/
theorem cbF_isBM : BMFiltration cbMeasure cbW cbF where
  adapted u := ((bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath).adapted
    u).comp_measurable (comap_measurable Prod.fst) |>.mono le_sup_left
  indep u v huv := by
    have := isProbabilityMeasure_gaussSeq
    have := isProbabilityMeasure_cbMeasure
    have hinc : Measurable (incr bmPath u v) :=
      (measurable_bmPath _).sub (measurable_bmPath _)
    have e : MeasurableSpace.comap (incr cbW u v) inferInstance = MeasurableSpace.comap
        Prod.fst (MeasurableSpace.comap (incr bmPath u v) inferInstance) := by
      rw [MeasurableSpace.comap_comp]
      rfl
    have h₁ := indep_comap_fst_incr huv
    have h := indep_sup_sup h₁ (indep_bot_left (MeasurableSpace.comap Prod.snd (coinFiltration u)))
      cb_indep_fst_snd
      (MeasurableSpace.comap_mono ((bmFiltrationReal bmPath measurable_bmPath).le u))
      (MeasurableSpace.comap_mono hinc.comap_le) (MeasurableSpace.comap_mono (coinFiltration.le u))
      bot_le measurable_fst.comap_le measurable_snd.comap_le
    rw [sup_bot_eq] at h
    rw [e, cbF_apply]
    exact h

/-! ## The jump martingale -/

/-- Cochrane (2023), A1 §1.6, p. 567: the jump martingale `e·ξ·1{u ≥ 1}`, `ξ = ±1` the coin. -/
noncomputable def cbJ (e : ℝ) (u : ℝ) (ω : (ℕ → ℝ) × Bool) : ℝ := e * coinXi ω.2 * stepAt 1 u

/-- Cochrane (2023), A1 §1.6, p. 567: the paths of `cbJ e` are affine steps
`0 + (eξ)·1{u ≥ 1}`.
Mirrors `TidyR7ProductStepJumpCoin.coinM_path`. -/
theorem cbJ_path (e : ℝ) (ω : (ℕ → ℝ) × Bool) :
    (fun u => cbJ e u ω) = fun u => 0 + e * coinXi ω.2 * stepAt 1 u :=
  funext fun u => by simp [cbJ]

/-- Cochrane (2023), A1 §1.6, p. 567: `|e·ξ·1{u ≥ 1}| ≤ |e|`. -/
theorem abs_cbJ_le (e u : ℝ) (ω : (ℕ → ℝ) × Bool) : |cbJ e u ω| ≤ |e| := by
  simp only [cbJ, abs_mul, abs_coinXi, mul_one]
  have : |stepAt 1 u| ≤ 1 := by
    simp only [stepAt]
    split_ifs <;> norm_num
  calc |e| * |stepAt 1 u| ≤ |e| * 1 := mul_le_mul_of_nonneg_left this (abs_nonneg e)
    _ = |e| := mul_one _

/-- Cochrane (2023), A1 §1.6, p. 567: before time `1`, `cbJ e u = 0`.
Mirrors `TidyR7ProductStepCoin.coinM_lt` on the product space. -/
theorem cbJ_lt (e : ℝ) {u : ℝ} (hu : u < 1) : cbJ e u = fun _ => 0 :=
  funext fun ω => by simp [cbJ, stepAt, not_le.2 hu]

/-- Cochrane (2023), A1 §1.6, p. 567: from time `1` on, `cbJ e u = e·ξ`.
Mirrors `TidyR7ProductStepCoin.coinM_ge` on the product space. -/
theorem cbJ_ge (e : ℝ) {u : ℝ} (hu : 1 ≤ u) : cbJ e u = fun ω => e * coinXi ω.2 :=
  funext fun ω => by simp [cbJ, stepAt, hu]

/-- Cochrane (2023), A1 §1.6, p. 567: the coin `e·ξ` is `cbF u`-measurable for `u ≥ 1`. -/
theorem cb_stronglyMeasurable_coin (e : ℝ) {u : ℝ} (hu : 1 ≤ u) :
    StronglyMeasurable[cbF u] fun ω : (ℕ → ℝ) × Bool => e * coinXi ω.2 := by
  have h : StronglyMeasurable[MeasurableSpace.comap Prod.snd (coinFiltration u)]
      fun ω : (ℕ → ℝ) × Bool => e * coinXi ω.2 := by
    rw [coinFiltration_ge hu]
    exact (measurable_of_finite fun b => e * coinXi b).stronglyMeasurable.comp_measurable
      (comap_measurable Prod.snd)
  exact h.mono (by rw [cbF_apply]; exact le_sup_right)

/-- Cochrane (2023), A1 §1.6, p. 567: `E[e·ξ] = 0` under `cbMeasure`.
Lifts `TidyR7ProductStepCoin.integral_coinXi` to the product space. -/
theorem integral_cb_coin (e : ℝ) : ∫ ω, e * coinXi ω.2 ∂cbMeasure = 0 := by
  have := isProbabilityMeasure_gaussSeq
  have hmp : MeasurePreserving (Prod.snd : (ℕ → ℝ) × Bool → Bool) cbMeasure coinMeasure :=
    measurePreserving_snd
  have h := integral_map (μ := cbMeasure) measurable_snd.aemeasurable
    (measurable_of_finite fun b : Bool => e * coinXi b).aestronglyMeasurable
  rw [hmp.map_eq] at h
  rw [← h, integral_const_mul, integral_coinXi, mul_zero]

/-- **Cochrane (2023), A1 §1.6, p. 567: `e·ξ·1{u ≥ 1}` is a martingale for `cbF`**: before
time `1` the coin is independent of the information `σ(W_r, r ≤ u)` and has mean `0`.
Generalises `TidyR7ProductStepCoin.martingale_coinM`. -/
theorem martingale_cbJ (e : ℝ) : Martingale (cbJ e) cbF cbMeasure := by
  have := isProbabilityMeasure_cbMeasure
  have hint : ∀ u, Integrable (cbJ e u) cbMeasure := fun u =>
    Integrable.of_bound (measurable_of_finite (fun b : Bool => e * coinXi b) |>.comp
      measurable_snd |>.mul measurable_const).aestronglyMeasurable |e|
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact abs_cbJ_le e u ω)
  have had : ∀ u, StronglyMeasurable[cbF u] (cbJ e u) := fun u => by
    by_cases hu : u < 1
    · rw [cbJ_lt e hu]
      exact stronglyMeasurable_const
    · rw [cbJ_ge e (not_lt.1 hu)]
      exact cb_stronglyMeasurable_coin e (not_lt.1 hu)
  refine ⟨had, fun i j hij => ?_⟩
  by_cases hj : j < 1
  · rw [cbJ_lt e hj, cbJ_lt e (lt_of_le_of_lt hij hj)]
    exact (condExp_const (cbF.le i) (0 : ℝ)).le.eventuallyLE.antisymm
      (condExp_const (cbF.le i) (0 : ℝ)).ge.eventuallyLE
  by_cases hi : 1 ≤ i
  · have e1 : cbJ e j = cbJ e i := by
      rw [cbJ_ge e (not_lt.1 hj), cbJ_ge e hi]
    rw [e1]
    exact (condExp_of_stronglyMeasurable (cbF.le i) (had i) (hint i)).eventuallyEq
  · have hi' : i < 1 := not_le.1 hi
    rw [cbJ_ge e (not_lt.1 hj), cbJ_lt e hi']
    have hle : cbF i ≤ MeasurableSpace.comap (Prod.fst : (ℕ → ℝ) × Bool → ℕ → ℝ)
        inferInstance := by
      rw [cbF_lt hi']
      exact MeasurableSpace.comap_mono ((bmFiltrationReal bmPath measurable_bmPath).le i)
    have hind := indep_of_indep_of_le_right cb_indep_fst_snd.symm hle
    have hsm : StronglyMeasurable[MeasurableSpace.comap
        (Prod.snd : (ℕ → ℝ) × Bool → Bool) inferInstance]
        fun ω : (ℕ → ℝ) × Bool => e * coinXi ω.2 :=
      (measurable_of_finite fun b => e * coinXi b).stronglyMeasurable.comp_measurable
        (comap_measurable Prod.snd)
    have h := condExp_indep_eq measurable_snd.comap_le (cbF.le i) hsm hind
    rw [integral_cb_coin] at h
    exact h

/-! ## Scaled Brownian motion as an Itô process -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `c·W` is a driftless Itô process with diffusion
`c`** (`TidyR7ItoIntegral.itoInt_const`). -/
theorem itoProcess_const_mul_bm {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ} {s t : ℝ} (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (c : ℝ) :
    ItoProcess P 𝓕 W (fun u ω => c * bmReal W u ω) (fun _ _ => 0) (fun _ _ => c) s t 0 |c| where
  adapted u _ := (h𝓕.adapted u).const_mul c
  init := ((hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two).const_mul c
  drift := itoIntegrand_const stronglyMeasurable_const (fun _ => by simp)
  diff := itoIntegrand_const (c := fun _ => c) stronglyMeasurable_const (fun _ => le_rfl)
  eq u hu := by
    filter_upwards [itoInt_const hB hW h𝓕 hs hu.1 (c := fun _ => c) (C := |c|)
      stronglyMeasurable_const (fun _ => le_rfl)] with ω hω
    rw [hω]
    simp only [incr, intervalIntegral.integral_zero]
    ring

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `c·W` is a martingale for every admissible
filtration (`TidyR10DoobProductStep.martingale_bmReal_of_bmFiltration`). -/
theorem martingale_const_mul_bm {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) (c : ℝ) :
    Martingale (fun u ω => c * bmReal W u ω) 𝓕 P :=
  (martingale_bmReal_of_bmFiltration hB hW h𝓕).smul c

/-! ## Domination -/

/-- **Cochrane (2023), A1 §1.6, p. 567: the domination conditions of the jump step for
processes dominated by `a + b|W|`.** If `|Y_u| ≤ a + b|W_u|` on `[s, t]` (`a, b ≥ 0`), the
values of `Y` are measurable, and `Var_{[s,t]}(Z)` is measurable and `≤ V`, then
`sup_{[s,t]}|Y| · Var_{[s,t]}(Z)` is integrable (Doob, `TidyR10DoobIto.doob_sq_bm`). -/
theorem cb_integrable_pathSup_mul_pathVar {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    {s t a b V : ℝ} (hst : s < t) (ha : 0 ≤ a) (hb : 0 ≤ b) {Y Z : ℝ → Ω → ℝ}
    (hYm : ∀ u ∈ Set.Icc s t, Measurable (Y u))
    (hY : ∀ u ∈ Set.Icc s t, ∀ ω, |Y u ω| ≤ a + b * |bmReal W u ω|)
    (hZm : Measurable (pathVar s t Z)) (hZ : ∀ ω, pathVar s t Z ω ≤ V) :
    Integrable (fun ω => pathSup s t Y ω * pathVar s t Z ω) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hm : Measurable (pathSup s t (bmReal W)) := measurable_pathSup fun _ _ => hW _
  have hsq := (doob_sq_bm hB hW h𝓕 (ae_of_all _ hcont) hst).1
  have hWs : Integrable (pathSup s t (bmReal W)) P :=
    ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 hsq).integrable one_le_two
  have hbd : ∀ ω, pathSup s t Y ω ≤ a + b * pathSup s t (bmReal W) ω := fun ω =>
    pathSup_le_of_forall_abs_le hst.le fun u hu => (hY u hu ω).trans
      (add_le_add_right (mul_le_mul_of_nonneg_left (abs_le_pathSup_of_continuousOn
        (continuous_bmReal (hcont ω)).continuousOn hu) hb) a)
  have hR : Integrable (fun ω => (a + b * pathSup s t (bmReal W) ω) * V) P :=
    ((integrable_const a).add (hWs.const_mul b)).mul_const V
  refine hR.mono' ((measurable_pathSup hYm).mul hZm).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  have hpv : 0 ≤ pathVar s t Z ω := ENNReal.toReal_nonneg
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pathSup_nonneg s t Y ω), abs_of_nonneg hpv]
  exact mul_le_mul (hbd ω) (hZ ω) hpv (add_nonneg ha (mul_nonneg hb (pathSup_nonneg s t _ ω)))

end Cochrane.Monetarism.TidyR11JumpDiffCoinBM
