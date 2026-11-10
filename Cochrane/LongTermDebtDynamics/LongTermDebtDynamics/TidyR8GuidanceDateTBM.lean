/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR8SurplusInterchange
import LongTermDebtDynamics.TidyR7GuidanceItoCex

/-!
# Forward guidance announced at a date `a > 0` on the constructed Brownian motion

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.2.1,
pp. 559–561: non-vacuity of TidyR8GuidanceDateT and TidyR8SurplusInterchange with
nontrivial date-`a` information. At `a > 0` the natural filtration `bmF a` of
`TidyR7BrownianExist.bmPath` is not trivial (unlike `bmF 0`, `TidyR7GuidanceItoCex.bmF_zero`),
and the conditional expectations below depend on the state through `W_a`.

## The economy

* Discount factor `bmSDF κ r (a + τ) ι` (TidyR7GuidanceItoBM): `Λ_t = e^{−rt}(1 + κW_t)` up to
  `a + τ`, then `Λ_{a+τ} e^{−ι(t−a−τ)}`. From the announcement date `a` it solves
  `dΛ = −rΛ dt + κe^{−rt} dW` on `[a, a + τ]` (`bmSDF_mid`, from the date-0 product-rule
  identity and additivity of the Itô integral), so `GuidanceSDFAt` holds (`guidanceSDFAt_bm`).
* Surpluses `bmSurplus s̄ σ`: `s_j = s̄ + σW_j`, random and adapted; `E_a s_{a+j} = s̄ + σW_a`
  (`condExp_bmSurplus`, the martingale property).

## Main results

* `pvSurplusAt_bm`: `E_a ∫_0^∞ e^{−rj} s_{a+j} dj = (s̄ + σW_a)/r` via the interchange
  `pvSurplusAt_interchange`; `pvSurplusAt_bm_not_const`: for `σ ≠ 0`, `a > 0` it is not a.s.
  equal to any constant.
* `condExp_debtAt_bm`: `E_a ∫_0^∞ ϖe^{−ϖj}Λ_{a+j} dj = cfgValue r i ϖ τ · e^{−ra}(1 + κW_a)`;
  `condExp_debtAt_bm_not_const`: not a.s. constant for `κ ≠ 0`, `a > 0`.
* `bm_guidance_jump_at` (**non-vacuity of `guidance_jump_at` at `a ≥ 0`**): with
  `P_a = cfgValue r i ϖ τ · r/(s̄ + σW_a)` (a random price level), the valuation equations hold
  and `P_a/P_a' − 1 = cfgJump r i ϖ τ` wherever `s̄ + σW_a > 0`.
* `bm_random_debtValueAt_pos`, `bm_random_jump_at` (**non-vacuity of `random_jump_at` at
  `a ≥ 0`**): with news `ι = i₁` if `W_{a+τ} > 0`, else `i₂`, and `κ = 0`, the price level
  `P_a = debtValueAt · r/(s̄ + σW_a)` satisfies the valuation equation and the corrected formula
  holds wherever `s̄ + σW_a > 0`.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR8GuidanceDateTBM

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.LongTermDebtDynamics.TidyR7BrownianExist
  Cochrane.LongTermDebtDynamics.TidyR7BrownianSchauder
  Cochrane.LongTermDebtDynamics.TidyR7BrownianTools
  Cochrane.LongTermDebtDynamics.TidyR7BrownianQV Cochrane.LongTermDebtDynamics.TidyR7ItoIntegral
  Cochrane.LongTermDebtDynamics.TidyR7ItoBridge
  Cochrane.LongTermDebtDynamics.TidyR7GuidanceSDF
  Cochrane.LongTermDebtDynamics.TidyR7GuidanceItoValuation
  Cochrane.LongTermDebtDynamics.TidyR7GuidanceItoBM
  Cochrane.LongTermDebtDynamics.TidyR7GuidanceItoCex
  Cochrane.LongTermDebtDynamics.TidyR8GuidanceDateT
  Cochrane.LongTermDebtDynamics.TidyR8SurplusInterchange
  Cochrane.LongTermDebtDynamics.ForwardGuidance
open scoped NNReal

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: joint integrability with a moving
date.** If `|F(j, ω)| ≤ w(j)(1 + |κ||W_{g(j)}(ω)|)` on `I` with `g ≥ 0` on `I`, `w ≥ 0`
measurable and `w(j)(1 + |κ|(1 + g(j)))` integrable on `I`, then `F` is integrable on
`I × Ω` (uses `E|W_u| ≤ 1 + u`). Generalises `TidyR7GuidanceItoBM.integrable_prod_bound`. -/
theorem integrable_prod_bound_idx {κ : ℝ} {I : Set ℝ} (hIm : MeasurableSet I)
    {g : ℝ → ℝ} (hg0 : ∀ j ∈ I, 0 ≤ g j) (hgm : Measurable g) {w : ℝ → ℝ}
    (hw0 : ∀ j, 0 ≤ w j) (hwm : Measurable w)
    (hwi : IntegrableOn (fun j => w j * (1 + |κ| * (1 + g j))) I)
    {F : ℝ × (ℕ → ℝ) → ℝ} (hFm : Measurable F)
    (hF : ∀ j ∈ I, ∀ ω, |F (j, ω)| ≤ w j * (1 + |κ| * |bmW (g j) ω|)) :
    Integrable F ((volume.restrict I).prod gaussSeq) := by
  have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
  have hWm : Measurable fun p : ℝ × (ℕ → ℝ) => bmW (g p.1) p.2 :=
    measurable_bmW.comp ((hgm.comp measurable_fst).prodMk measurable_snd)
  have hGm : Measurable fun p : ℝ × (ℕ → ℝ) => w p.1 * (1 + |κ| * |bmW (g p.1) p.2|) :=
    (hwm.comp measurable_fst).mul
      (measurable_const.add (measurable_const.mul (continuous_abs.measurable.comp hWm)))
  have hj1 : ∀ j, Integrable (fun ω => w j * (1 + |κ| * |bmW (g j) ω|)) gaussSeq :=
    fun j => ((integrable_const (1 : ℝ)).add
      ((integrable_bmW (g j)).abs.const_mul |κ|)).const_mul (w j)
  have hj2 : ∀ j ∈ I, ∫ ω, ‖w j * (1 + |κ| * |bmW (g j) ω|)‖ ∂gaussSeq
      ≤ w j * (1 + |κ| * (1 + g j)) := by
    intro j hj
    have hn : ∀ ω, ‖w j * (1 + |κ| * |bmW (g j) ω|)‖
        = w j * (1 + |κ| * |bmW (g j) ω|) := fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by have := hw0 j; positivity)]
    simp_rw [hn]
    rw [integral_const_mul, integral_add (integrable_const 1)
      ((integrable_bmW _).abs.const_mul |κ|), integral_const_mul]
    have h1 := integral_abs_bmW_le (hg0 j hj)
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have : |κ| * ∫ ω, |bmW (g j) ω| ∂gaussSeq ≤ |κ| * (1 + g j) :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg κ)
    nlinarith [hw0 j]
  have hGint : Integrable (fun p : ℝ × (ℕ → ℝ) => w p.1 * (1 + |κ| * |bmW (g p.1) p.2|))
      ((volume.restrict I).prod gaussSeq) := by
    refine (integrable_prod_iff hGm.aestronglyMeasurable).2 ⟨ae_of_all _ fun j => hj1 j, ?_⟩
    refine hwi.mono' hGm.norm.aestronglyMeasurable.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem hIm] with j hj
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ω => norm_nonneg _)]
    exact hj2 j hj
  refine hGint.mono' hFm.aestronglyMeasurable ?_
  have hfst := (Measure.quasiMeasurePreserving_fst (μ := volume.restrict I)
    (ν := gaussSeq)).ae (ae_restrict_mem hIm)
  filter_upwards [hfst] with p hp
  rw [Real.norm_eq_abs]
  exact hF p.1 hp p.2

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: from the announcement date `a` the
model economy solves `dΛ = −rΛ dt + κe^{−rt} dW`**: a.s., for `u ∈ [a, T]` (`0 ≤ a`),
`Λ_u = Λ_a − r ∫_a^u Λ_v dv + ∫_a^u κe^{−rv} dW_v` (the date-0 identity
`TidyR7GuidanceItoBM.bmSDF_pre_eq` at `u` minus at `a`, with
`TidyR7ItoIntegral.itoInt_add_itoInt`). -/
theorem bmSDF_mid_eq (κ : ℝ) {r T a : ℝ} (hr : 0 ≤ r) (ι : (ℕ → ℝ) → ℝ) (ha : 0 ≤ a)
    {u : ℝ} (hu : u ∈ Set.Icc a T) :
    bmSDF κ r T ι u =ᵐ[gaussSeq] fun ω => bmSDF κ r T ι a ω
      - r * (∫ v in a..u, bmSDF κ r T ι v ω)
      + itoInt gaussSeq bmF bmPath (fun v _ => κ * Real.exp (-r * v)) a u ω := by
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  have hau : a ≤ u := hu.1
  have huT : u ≤ T := hu.2
  have e1 := bmSDF_pre_eq κ hr ι (T := T) (u := u) ⟨ha.trans hau, huT⟩
  have e2 := bmSDF_pre_eq κ hr ι (T := T) (u := a) ⟨ha, hau.trans huT⟩
  have hH : ItoIntegrand gaussSeq bmF (fun v _ => κ * Real.exp (-r * v)) 0 u |κ| :=
    itoIntegrand_deterministic (h := fun v => κ * Real.exp (-r * v)) (by fun_prop)
      (fun v hv => by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        have : Real.exp (-r * v) ≤ 1 :=
          Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg hr hv.1])
        nlinarith [abs_nonneg κ])
  have e3 := itoInt_add_itoInt hB measurable_bmPath h𝓕 le_rfl ha hau hH
  filter_upwards [e1, e2, e3] with ω h1 h2 h3
  have hc : Continuous fun v => Real.exp (-r * v) * (1 + κ * bmW v ω) :=
    (by fun_prop : Continuous fun v : ℝ => Real.exp (-r * v)).mul
      (continuous_const.add (continuous_const.mul (continuous_bmReal (continuous_bmPath ω))))
  have hcont : ContinuousOn (fun v => bmSDF κ r T ι v ω) (Set.Icc 0 T) := by
    refine hc.continuousOn.congr fun v hv => ?_
    simp only [bmSDF, hv.2, ↓reduceIte]
  have hi1 : IntervalIntegrable (fun v => bmSDF κ r T ι v ω) volume 0 a :=
    (hcont.mono (by
      rw [Set.uIcc_of_le ha]
      exact Set.Icc_subset_Icc le_rfl (hau.trans huT))).intervalIntegrable
  have hi2 : IntervalIntegrable (fun v => bmSDF κ r T ι v ω) volume a u :=
    (hcont.mono (by
      rw [Set.uIcc_of_le hau]
      exact Set.Icc_subset_Icc ha huT)).intervalIntegrable
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  rw [h1, h2]
  linear_combination h3 + r * hsplit

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the model economy on `[a, T]` is an
`SDFPiece`** with rate `r` and diffusion `κe^{−rv}` (`r ≥ 0`, `0 ≤ a ≤ T`, `ι ≥ 0`
measurable); the date-`a` value `Λ_a = e^{−ra}(1 + κW_a)` is random and `𝓕_a`-measurable.
Generalises `TidyR7GuidanceItoBM.bmSDF_pre` to an announcement at date `a`. -/
theorem bmSDF_mid (κ : ℝ) {r T a : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) (haT : a ≤ T)
    {ι : (ℕ → ℝ) → ℝ} (hιm : Measurable ι) (hι : ∀ ω, 0 ≤ ι ω) :
    SDFPiece gaussSeq bmF bmPath (bmSDF κ r T ι) (fun v _ => κ * Real.exp (-r * v))
      (fun _ => r) a T |κ| where
  adapted := by
    have : bmSDF κ r T ι a = fun ω => Real.exp (-r * a) * (1 + κ * bmW a ω) :=
      funext fun ω => by simp [bmSDF, haT]
    rw [this]
    exact stronglyMeasurable_const.mul (stronglyMeasurable_const.add
      (stronglyMeasurable_const.mul ((bmFiltrationReal_isBM isPreBrownianReal_bmPath
        measurable_bmPath).adapted a)))
  rate := stronglyMeasurable_const
  rate_finite := ⟨{r}, fun _ => Finset.mem_singleton_self r⟩
  integ := integrable_prod_bound (κ := κ) (ha.trans haT) measurableSet_Ioc
    (fun _ hj => Set.mem_Ici.2 (ha.trans (le_of_lt hj.1))) (w := fun _ => 1)
    (fun _ => zero_le_one) measurable_const (integrableOn_const (by simp) (by simp))
    (measurable_bmSDF κ r T hιm)
    (fun j hj ω => by
      simpa using abs_bmSDF_le (κ := κ) hr (ha.trans haT) hι (ha.trans (le_of_lt hj.1)) ω)
  integ_at u hu := integrable_bmSDF hr (ha.trans haT) hιm hι (ha.trans hu.1)
  diff := itoIntegrand_deterministic (h := fun v => κ * Real.exp (-r * v)) (by fun_prop)
    (fun v hv => by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      have : Real.exp (-r * v) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg hr (ha.trans hv.1)])
      nlinarith [abs_nonneg κ])
  eq u hu := bmSDF_mid_eq κ hr ι ha hu

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the model economy satisfies the
announcement structure at date `a`** (`GuidanceSDFAt`): rate `r` on `[a, a + τ]`, then `ι`
known at `a + τ` (finitely many values, `ι ≥ 0`); `r ≥ 0`, `a, τ ≥ 0`.
Generalises `TidyR7GuidanceItoBM.guidanceSDF_bm` to an announcement at date `a`. -/
theorem guidanceSDFAt_bm (κ : ℝ) {r a τ : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) (hτ : 0 ≤ τ)
    {ι : (ℕ → ℝ) → ℝ} (hιT : StronglyMeasurable[bmF (a + τ)] ι)
    (hfin : ∃ S : Finset ℝ, ∀ ω, ι ω ∈ S) (hι : ∀ ω, 0 ≤ ι ω) :
    GuidanceSDFAt gaussSeq bmF bmPath (bmSDF κ r (a + τ) ι)
      (fun v _ => κ * Real.exp (-r * v)) (fun _ _ => 0) r ι a τ where
  pre := ⟨|κ|, bmSDF_mid κ hr ha (by linarith) (hιT.mono (bmF.le _)).measurable hι⟩
  post t _ := ⟨0, bmSDF_post κ hr (by linarith) hιT hfin hι t⟩

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the date-`a` debt payoffs of the model
economy are jointly integrable**: `(j, ω) ↦ ϖe^{−ϖj}Λ_{a+j}(ω)` on `(0, ∞) × Ω` (`ϖ > 0`).
Generalises `TidyR7GuidanceItoBM.integrable_debt_bm` to an announcement at date `a`. -/
theorem integrable_debtAt_bm (κ : ℝ) {r a τ ϖ : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) (hτ : 0 ≤ τ)
    (hϖ : 0 < ϖ) {ι : (ℕ → ℝ) → ℝ} (hιm : Measurable ι) (hι : ∀ ω, 0 ≤ ι ω) :
    Integrable (fun p : ℝ × (ℕ → ℝ) =>
      ϖ * Real.exp (-ϖ * p.1) * bmSDF κ r (a + τ) ι (a + p.1) p.2)
      ((volume.restrict (Set.Ioi 0)).prod gaussSeq) := by
  have hT : 0 ≤ a + τ := by linarith
  have hw : IntegrableOn (fun j => ϖ * Real.exp (-ϖ * j)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul ϖ
  have hgm : Measurable fun j : ℝ => min (a + j) (a + τ) :=
    (measurable_const.add measurable_id').min measurable_const
  have hwi : IntegrableOn
      (fun j => ϖ * Real.exp (-ϖ * j) * (1 + |κ| * (1 + min (a + j) (a + τ)))) (Set.Ioi 0) := by
    refine (hw.mul_const (1 + |κ| * (1 + (a + τ)))).mono'
      (((by fun_prop : Measurable fun j : ℝ => ϖ * Real.exp (-ϖ * j)).mul
        (measurable_const.add (measurable_const.mul
          (measurable_const.add hgm)))).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with j hj
    have hj0 : (0 : ℝ) < j := hj
    have h0 : 0 ≤ min (a + j) (a + τ) := le_min (by linarith) hT
    have hm : min (a + j) (a + τ) ≤ a + τ := min_le_right _ _
    have hwj : 0 < ϖ * Real.exp (-ϖ * j) := by positivity
    have hk := mul_nonneg (abs_nonneg κ) (by linarith : (0 : ℝ) ≤ 1 + min (a + j) (a + τ))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hwj.le (by linarith))]
    exact mul_le_mul_of_nonneg_left (by nlinarith [abs_nonneg κ]) hwj.le
  refine integrable_prod_bound_idx (κ := κ) measurableSet_Ioi
    (g := fun j => min (a + j) (a + τ))
    (fun j hj => le_min (by linarith [le_of_lt (Set.mem_Ioi.1 hj)]) hT) hgm
    (w := fun j => ϖ * Real.exp (-ϖ * j)) (fun j => by positivity) (by fun_prop) hwi
    ((by fun_prop : Measurable fun p : ℝ × (ℕ → ℝ) => ϖ * Real.exp (-ϖ * p.1)).mul
      ((measurable_bmSDF κ r (a + τ) hιm).comp
        ((measurable_const.add measurable_fst).prodMk measurable_snd))) (fun j hj ω => ?_)
  change |ϖ * Real.exp (-ϖ * j) * bmSDF κ r (a + τ) ι (a + j) ω|
    ≤ ϖ * Real.exp (-ϖ * j) * (1 + |κ| * |bmW (min (a + j) (a + τ)) ω|)
  rw [abs_mul, abs_of_pos (by positivity : 0 < ϖ * Real.exp (-ϖ * j))]
  exact mul_le_mul_of_nonneg_left
    (abs_bmSDF_le hr hT hι (by linarith [le_of_lt (Set.mem_Ioi.1 hj)]) ω) (by positivity)

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 559: **random surpluses** `s_j = s̄ + σW_j`
on the constructed Brownian motion (adapted, with `E|s_j| < ∞`). -/
noncomputable def bmSurplus (sbar σ : ℝ) (j : ℝ) (ω : ℕ → ℝ) : ℝ := sbar + σ * bmW j ω

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 559: the expected surplus given date-`a`
information**: `E[s_u | 𝓕_a] = s̄ + σW_a` a.s. for `a ≤ u` (the martingale property of `W`,
`TidyR7BrownianTools.martingale_bmReal`). -/
theorem condExp_bmSurplus (sbar σ : ℝ) {a u : ℝ} (hau : a ≤ u) :
    gaussSeq[bmSurplus sbar σ u | bmF a] =ᵐ[gaussSeq] fun ω => sbar + σ * bmW a ω := by
  have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
  have hmart := (martingale_bmReal isPreBrownianReal_bmPath measurable_bmPath).condExp_ae_eq hau
  have e : bmSurplus sbar σ u = (fun _ => sbar) + σ • bmW u := by
    funext ω
    simp [bmSurplus, smul_eq_mul]
  rw [e]
  filter_upwards [condExp_add (m := bmF a) (integrable_const sbar) ((integrable_bmW u).smul σ),
    condExp_smul (μ := gaussSeq) σ (bmW u) (bmF a), hmart] with ω h1 h2 h3
  rw [h1, Pi.add_apply, condExp_const (bmF.le a), h2, Pi.smul_apply, h3, smul_eq_mul]

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 559: the discounted random surpluses are
jointly integrable** on `(0, ∞) × Ω` (`r > 0`, `a ≥ 0`): the integrable majorant is
`(1 + |s̄|)e^{−rj}(1 + |σ||W_{a+j}|)`, with `E|W_{a+j}| ≤ 1 + a + j`. -/
theorem integrable_surplusAt_bm (sbar σ : ℝ) {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) :
    Integrable (fun p : ℝ × (ℕ → ℝ) => Real.exp (-r * p.1) * bmSurplus sbar σ (a + p.1) p.2)
      ((volume.restrict (Set.Ioi 0)).prod gaussSeq) := by
  have he : IntegrableOn (fun j : ℝ => Real.exp (-r * j)) (Set.Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hj : IntegrableOn (fun j : ℝ => j * Real.exp (-r * j)) (Set.Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := r) (by norm_num) one_pos
      hr).congr_fun (fun x _ => by simp only [Real.rpow_one]) measurableSet_Ioi
  have hwi : IntegrableOn
      (fun j => (1 + |sbar|) * Real.exp (-r * j) * (1 + |σ| * (1 + (a + j)))) (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun ((he.const_mul ((1 + |sbar|) * (1 + |σ| * (1 + a)))).add
      (hj.const_mul ((1 + |sbar|) * |σ|))) (fun j _ => ?_) measurableSet_Ioi
    change (1 + |sbar|) * (1 + |σ| * (1 + a)) * Real.exp (-r * j)
        + (1 + |sbar|) * |σ| * (j * Real.exp (-r * j))
      = (1 + |sbar|) * Real.exp (-r * j) * (1 + |σ| * (1 + (a + j)))
    ring
  refine integrable_prod_bound_idx (κ := σ) measurableSet_Ioi (g := fun j => a + j)
    (fun j hj => by linarith [le_of_lt (Set.mem_Ioi.1 hj)])
    (measurable_const.add measurable_id')
    (w := fun j => (1 + |sbar|) * Real.exp (-r * j)) (fun j => by positivity) (by fun_prop)
    hwi ((by fun_prop : Measurable fun p : ℝ × (ℕ → ℝ) => Real.exp (-r * p.1)).mul
      (measurable_const.add (measurable_const.mul (measurable_bmW.comp
        ((measurable_const.add measurable_fst).prodMk measurable_snd))))) (fun j _ ω => ?_)
  change |Real.exp (-r * j) * (sbar + σ * bmW (a + j) ω)|
    ≤ (1 + |sbar|) * Real.exp (-r * j) * (1 + |σ| * |bmW (a + j) ω|)
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 : |sbar + σ * bmW (a + j) ω| ≤ |sbar| + |σ| * |bmW (a + j) ω| := by
    calc _ ≤ |sbar| + |σ * bmW (a + j) ω| := abs_add_le _ _
      _ = _ := by rw [abs_mul]
  have h2 := mul_nonneg (abs_nonneg sbar) (mul_nonneg (abs_nonneg σ) (abs_nonneg (bmW (a + j) ω)))
  have h4 : |sbar + σ * bmW (a + j) ω| ≤ (1 + |sbar|) * (1 + |σ| * |bmW (a + j) ω|) := by
    nlinarith [abs_nonneg sbar, mul_nonneg (abs_nonneg σ) (abs_nonneg (bmW (a + j) ω))]
  calc Real.exp (-r * j) * |sbar + σ * bmW (a + j) ω|
      ≤ Real.exp (-r * j) * ((1 + |sbar|) * (1 + |σ| * |bmW (a + j) ω|)) :=
        mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
    _ = _ := by ring

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 559: the present value of the random
surpluses at date `a`**: `E_a ∫_0^∞ e^{−rj}s_{a+j} dj = (s̄ + σW_a)/r` a.s. (`r > 0`,
`a ≥ 0`), by the interchange `TidyR8SurplusInterchange.pvSurplusAt_interchange` with the
version `m_j = s̄ + σW_a`.
Generalises `TidyR7GuidanceItoBM.pvSurplus_const` (the case `σ = 0`, `a = 0`). -/
theorem pvSurplusAt_bm (sbar σ : ℝ) {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) :
    pvSurplusAt gaussSeq bmF r a (bmSurplus sbar σ) =ᵐ[gaussSeq]
      fun ω => (sbar + σ * bmW a ω) / r := by
  have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
  have hWa : StronglyMeasurable[bmF a] (bmW a) :=
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath).adapted a
  have hm : StronglyMeasurable[@Prod.instMeasurableSpace ℝ (ℕ → ℝ) _ (bmF a)]
      (Function.uncurry fun (_ : ℝ) ω => sbar + σ * bmW a ω) :=
    stronglyMeasurable_const.add (stronglyMeasurable_const.mul
      (hWa.comp_measurable (@measurable_snd ℝ (ℕ → ℝ) _ (bmF a))))
  have h := pvSurplusAt_interchange (integrable_surplusAt_bm sbar σ hr ha) hm
    (fun j hj => (condExp_bmSurplus sbar σ (by linarith [le_of_lt (Set.mem_Ioi.1 hj)])).symm)
  refine h.trans (ae_of_all _ fun ω => ?_)
  change ∫ j in Set.Ioi (0 : ℝ), Real.exp (-r * j) * (sbar + σ * bmW a ω)
    = (sbar + σ * bmW a ω) / r
  rw [integral_mul_const, integral_exp_mul_Ioi (by linarith) 0, mul_zero, Real.exp_zero,
    neg_div_neg_eq, one_div, inv_mul_eq_div]

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: **date-`a` information is nontrivial**:
for `a > 0`, `W_a` is not a.s. equal to any constant (its law charges every half-line,
`TidyR7GuidanceItoCex.gaussSeq_preimage_pos`). -/
theorem bmW_not_ae_const {a : ℝ} (ha : 0 < a) (d : ℝ) : ¬ (bmW a =ᵐ[gaussSeq] fun _ => d) := by
  intro h
  have hpos := gaussSeq_preimage_pos ha measurableSet_Ioi (A := Set.Ioi d) (by simp)
  exact hpos (measure_mono_null (fun ω hω => (Set.mem_Ioi.1 hω).ne') (ae_iff.1 h))

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 559: the date-`a` present value of
surpluses depends on the state.** For `σ ≠ 0`, `r > 0`, `a > 0`,
`E_a ∫_0^∞ e^{−rj}s_{a+j} dj = (s̄ + σW_a)/r` is not a.s. equal to any constant `c`. -/
theorem pvSurplusAt_bm_not_const (sbar : ℝ) {σ r a : ℝ} (hσ : σ ≠ 0) (hr : 0 < r)
    (ha : 0 < a) (c : ℝ) :
    ¬ (pvSurplusAt gaussSeq bmF r a (bmSurplus sbar σ) =ᵐ[gaussSeq] fun _ => c) := by
  intro h
  refine bmW_not_ae_const ha ((c * r - sbar) / σ) ?_
  filter_upwards [h, pvSurplusAt_bm sbar σ hr ha.le] with ω h1 h2
  rw [h2] at h1
  have h3 := (div_eq_iff hr.ne').1 h1
  rw [eq_div_iff hσ]
  linarith

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the date-`a` value of the debt in the
model economy**: with the known announcement (`r` on `[a, a + τ]`, `i ≥ 0` after; `r ≥ 0`,
`ϖ > 0`), `E_a ∫_0^∞ ϖe^{−ϖj}Λ_{a+j} dj = cfgValue r i ϖ τ · e^{−ra}(1 + κW_a)` a.s.
(`TidyR8GuidanceDateT.condExp_debtValueAt` on `guidanceSDFAt_bm`). -/
theorem condExp_debtAt_bm (κ : ℝ) {r i a τ ϖ : ℝ} (hr : 0 ≤ r) (hi : 0 ≤ i) (ha : 0 ≤ a)
    (hτ : 0 ≤ τ) (hϖ : 0 < ϖ) :
    gaussSeq[fun ω => ∫ j in Set.Ioi (0 : ℝ),
        ϖ * Real.exp (-ϖ * j) * bmSDF κ r (a + τ) (fun _ => i) (a + j) ω | bmF a]
      =ᵐ[gaussSeq] fun ω => cfgValue r i ϖ τ * (Real.exp (-r * a) * (1 + κ * bmW a ω)) := by
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  have hG := guidanceSDFAt_bm κ hr ha hτ (ι := fun _ => i) stronglyMeasurable_const
    ⟨{i}, fun _ => Finset.mem_singleton_self i⟩ (fun _ => hi)
  have hI := integrable_debtAt_bm κ hr ha hτ hϖ (ι := fun _ => i) measurable_const
    (fun _ => hi)
  refine (condExp_debtValueAt hB measurable_bmPath h𝓕 ha hτ hG (by linarith) (by linarith)
    hI).trans (ae_of_all _ fun ω => ?_)
  change cfgValue r i ϖ τ * bmSDF κ r (a + τ) (fun _ => i) a ω = _
  simp only [bmSDF, le_add_of_nonneg_right hτ, ↓reduceIte]

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the date-`a` value of the debt depends
on the state.** For `κ ≠ 0`, `a > 0` (and `r ≥ 0`, `i ≥ 0`, `ϖ > 0`, `τ ≥ 0`), the
conditional expectation of `condExp_debtAt_bm` is not a.s. equal to any constant. -/
theorem condExp_debtAt_bm_not_const {κ r i a τ ϖ : ℝ} (hκ : κ ≠ 0) (hr : 0 ≤ r) (hi : 0 ≤ i)
    (ha : 0 < a) (hτ : 0 ≤ τ) (hϖ : 0 < ϖ) (c : ℝ) :
    ¬ (gaussSeq[fun ω => ∫ j in Set.Ioi (0 : ℝ),
        ϖ * Real.exp (-ϖ * j) * bmSDF κ r (a + τ) (fun _ => i) (a + j) ω | bmF a]
      =ᵐ[gaussSeq] fun _ => c) := by
  intro h
  have hV := cfgValue_pos hϖ (by linarith) (by linarith) hτ (r := r) (i := i)
  have hE := Real.exp_pos (-r * a)
  refine bmW_not_ae_const ha ((c / (cfgValue r i ϖ τ * Real.exp (-r * a)) - 1) / κ) ?_
  filter_upwards [h, condExp_debtAt_bm κ hr hi ha.le hτ hϖ] with ω h1 h2
  rw [h2] at h1
  rw [eq_div_iff hκ, eq_sub_iff_add_eq, eq_div_iff (by positivity)]
  linear_combination h1

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: non-vacuity of the forward-guidance
formula at a date `a ≥ 0` with random date-`a` information.** In the model economy with
guidance (`bmSDF κ r (a + τ) i`) and without (`bmSDF κ' r (a + τ) r`), random surpluses
`s̄ + σW_j`, `B_a = 1`, `r > 0`, `i ≥ 0`, `ϖ > 0`: the random price levels
`P_a = cfgValue r i ϖ τ · r/(s̄ + σW_a)` and `P_a' = cfgValue r r ϖ τ · r/(s̄ + σW_a)` satisfy
the date-`a` valuation equations a.s. where `Λ_a ≠ 0`, and `guidance_jump_at` gives
`P_a/P_a' − 1 = cfgJump r i ϖ τ` a.s. where `1 + κW_a`, `1 + κ'W_a ≠ 0` and `s̄ + σW_a > 0`.
Generalises `TidyR7GuidanceItoBM.bm_guidance_jump` to an announcement at date `a`. -/
theorem bm_guidance_jump_at (κ κ' : ℝ) {r i ϖ a τ : ℝ} (sbar σ : ℝ) (hr : 0 < r) (hi : 0 ≤ i)
    (hϖ : 0 < ϖ) (ha : 0 ≤ a) (hτ : 0 ≤ τ) :
    (∀ᵐ ω ∂gaussSeq, bmSDF κ r (a + τ) (fun _ => i) a ω ≠ 0 →
        1 / (cfgValue r i ϖ τ * r / (sbar + σ * bmW a ω))
          * debtValueAt gaussSeq bmF (bmSDF κ r (a + τ) fun _ => i) a ϖ ω
        = pvSurplusAt gaussSeq bmF r a (bmSurplus sbar σ) ω)
    ∧ (∀ᵐ ω ∂gaussSeq, bmSDF κ' r (a + τ) (fun _ => r) a ω ≠ 0 →
        1 / (cfgValue r r ϖ τ * r / (sbar + σ * bmW a ω))
          * debtValueAt gaussSeq bmF (bmSDF κ' r (a + τ) fun _ => r) a ϖ ω
        = pvSurplusAt gaussSeq bmF r a (bmSurplus sbar σ) ω)
    ∧ ∀ᵐ ω ∂gaussSeq, 1 + κ * bmW a ω ≠ 0 → 1 + κ' * bmW a ω ≠ 0 →
        0 < sbar + σ * bmW a ω →
        cfgValue r i ϖ τ * r / (sbar + σ * bmW a ω)
          / (cfgValue r r ϖ τ * r / (sbar + σ * bmW a ω)) - 1 = cfgJump r i ϖ τ := by
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  have hrv : 0 < r + ϖ := by linarith
  have hiv : 0 < i + ϖ := by linarith
  have hV := cfgValue_pos hϖ hrv hiv hτ
  have hV' := cfgValue_pos hϖ hrv hrv hτ
  have hG := guidanceSDFAt_bm κ hr.le ha hτ (ι := fun _ => i) stronglyMeasurable_const
    ⟨{i}, fun _ => Finset.mem_singleton_self i⟩ (fun _ => hi)
  have hG' := guidanceSDFAt_bm κ' hr.le ha hτ (ι := fun _ => r) stronglyMeasurable_const
    ⟨{r}, fun _ => Finset.mem_singleton_self r⟩ (fun _ => hr.le)
  have hI := integrable_debtAt_bm κ hr.le ha hτ hϖ (ι := fun _ => i) measurable_const
    (fun _ => hi)
  have hI' := integrable_debtAt_bm κ' hr.le ha hτ hϖ (ι := fun _ => r) measurable_const
    (fun _ => hr.le)
  have hpv := pvSurplusAt_bm sbar σ hr ha
  have hΛa : ∀ (c : ℝ) (ι : (ℕ → ℝ) → ℝ) ω,
      bmSDF c r (a + τ) ι a ω = Real.exp (-r * a) * (1 + c * bmW a ω) := fun c ι ω => by
    simp only [bmSDF, le_add_of_nonneg_right hτ, ↓reduceIte]
  have key : ∀ {V S : ℝ}, V ≠ 0 → 1 / (V * r / S) * V = S / r := fun {V S} hV0 => by
    rw [one_div_div, div_mul_eq_mul_div, mul_comm V r, mul_div_mul_right _ _ hV0]
  have hval : ∀ᵐ ω ∂gaussSeq, bmSDF κ r (a + τ) (fun _ => i) a ω ≠ 0 →
      1 / (cfgValue r i ϖ τ * r / (sbar + σ * bmW a ω))
        * debtValueAt gaussSeq bmF (bmSDF κ r (a + τ) fun _ => i) a ϖ ω
      = pvSurplusAt gaussSeq bmF r a (bmSurplus sbar σ) ω := by
    filter_upwards [debtValueAt_guidance hB measurable_bmPath h𝓕 ha hτ hG hrv hiv hI, hpv]
      with ω e1 e2 h0
    rw [e1 h0, e2]
    exact key hV.ne'
  have hval' : ∀ᵐ ω ∂gaussSeq, bmSDF κ' r (a + τ) (fun _ => r) a ω ≠ 0 →
      1 / (cfgValue r r ϖ τ * r / (sbar + σ * bmW a ω))
        * debtValueAt gaussSeq bmF (bmSDF κ' r (a + τ) fun _ => r) a ϖ ω
      = pvSurplusAt gaussSeq bmF r a (bmSurplus sbar σ) ω := by
    filter_upwards [debtValueAt_guidance hB measurable_bmPath h𝓕 ha hτ hG' hrv hrv hI', hpv]
      with ω e1 e2 h0
    rw [e1 h0, e2]
    exact key hV'.ne'
  refine ⟨hval, hval', ?_⟩
  have hj := guidance_jump_at hB measurable_bmPath h𝓕 ha hτ hϖ hrv hiv (B := fun _ => 1)
    (Pa := fun ω => cfgValue r i ϖ τ * r / (sbar + σ * bmW a ω))
    (Pa' := fun ω => cfgValue r r ϖ τ * r / (sbar + σ * bmW a ω))
    (s := bmSurplus sbar σ) hG hI hG' hI' hval hval'
  filter_upwards [hj, hpv] with ω hω e2 h1 h1' hS
  exact hω (by rw [hΛa]; exact mul_ne_zero (Real.exp_pos _).ne' h1)
    (by rw [hΛa]; exact mul_ne_zero (Real.exp_pos _).ne' h1')
    (by rw [e2]; exact (div_pos hS hr).ne') (div_pos (mul_pos hV hr) hS)
    (div_pos (mul_pos hV' hr) hS)

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: a lower bound for the date-`a` debt value
with news** (positive by `TidyR7GuidanceItoBM.cfgValue_pos`). In the model economy with `κ = 0`
(`Λ_t = e^{−rt}` up to `a + τ`) and the rate
from `a + τ` on the news `ι = i₁` if `W_{a+τ} > 0`, else `i₂` (`TidyR7GuidanceItoCex.newsRate`),
a.s. `debtValueAt ≥ min(cfgValue r i₁ ϖ τ, cfgValue r i₂ ϖ τ)` (`r, i₁, i₂ ≥ 0`, `ϖ > 0`). -/
theorem bm_random_debtValueAt_pos {r i₁ i₂ ϖ a τ : ℝ} (hr : 0 ≤ r) (hi₁ : 0 ≤ i₁)
    (hi₂ : 0 ≤ i₂) (hϖ : 0 < ϖ) (ha : 0 ≤ a) (hτ : 0 ≤ τ) :
    ∀ᵐ ω ∂gaussSeq, min (cfgValue r i₁ ϖ τ) (cfgValue r i₂ ϖ τ) ≤
      debtValueAt gaussSeq bmF (bmSDF 0 r (a + τ) (newsRate i₁ i₂ (a + τ))) a ϖ ω := by
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
  have hι0 : ∀ ω, 0 ≤ newsRate i₁ i₂ (a + τ) ω := fun ω => by
    unfold newsRate
    split_ifs
    · exact hi₁
    · exact hi₂
  have hιT := stronglyMeasurable_newsRate i₁ i₂ (a + τ)
  have hιm : Measurable (newsRate i₁ i₂ (a + τ)) := (hιT.mono (bmF.le _)).measurable
  have hG := guidanceSDFAt_bm 0 hr ha hτ hιT (newsRate_finite i₁ i₂ (a + τ)) hι0
  have hI := integrable_debtAt_bm 0 hr ha hτ hϖ hιm hι0
  have hV := condExp_debtValueAt_random hB measurable_bmPath h𝓕 ha hτ hG (by linarith)
    (fun ω => by linarith [hι0 ω]) hI
  have hV1 := cfgValue_pos hϖ (by linarith) (by linarith) hτ (r := r) (i := i₁)
  have hV2 := cfgValue_pos hϖ (by linarith) (by linarith) hτ (r := r) (i := i₂)
  have hΛ : ∀ t ω, t ≤ a + τ →
      bmSDF 0 r (a + τ) (newsRate i₁ i₂ (a + τ)) t ω = Real.exp (-r * t) :=
    fun t ω ht => by simp [bmSDF, ht]
  have hY : (fun ω => Real.exp (r * τ) * bmSDF 0 r (a + τ) (newsRate i₁ i₂ (a + τ)) (a + τ) ω
      * cfgValue r (newsRate i₁ i₂ (a + τ) ω) ϖ τ)
      = fun ω => Real.exp (-r * a) * cfgValue r (newsRate i₁ i₂ (a + τ) ω) ϖ τ := by
    funext ω
    rw [hΛ _ _ le_rfl, ← Real.exp_add]
    congr 2
    ring
  have hcm : Measurable fun ω => Real.exp (-r * a) * cfgValue r (newsRate i₁ i₂ (a + τ) ω) ϖ τ := by
    have : Measurable fun x : ℝ => cfgValue r x ϖ τ := by unfold cfgValue; fun_prop
    exact measurable_const.mul (this.comp hιm)
  have hcV : ∀ ω, min (cfgValue r i₁ ϖ τ) (cfgValue r i₂ ϖ τ)
      ≤ cfgValue r (newsRate i₁ i₂ (a + τ) ω) ϖ τ
      ∧ cfgValue r (newsRate i₁ i₂ (a + τ) ω) ϖ τ ≤ cfgValue r i₁ ϖ τ + cfgValue r i₂ ϖ τ := by
    intro ω
    unfold newsRate
    split_ifs
    · exact ⟨min_le_left _ _, by linarith⟩
    · exact ⟨min_le_right _ _, by linarith⟩
  have hYint : Integrable
      (fun ω => Real.exp (-r * a) * cfgValue r (newsRate i₁ i₂ (a + τ) ω) ϖ τ) gaussSeq := by
    refine (integrable_const (Real.exp (-r * a) * (cfgValue r i₁ ϖ τ + cfgValue r i₂ ϖ τ))).mono'
      hcm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    have hpos : 0 < cfgValue r (newsRate i₁ i₂ (a + τ) ω) ϖ τ :=
      (lt_min hV1 hV2).trans_le (hcV ω).1
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) hpos)]
    exact mul_le_mul_of_nonneg_left (hcV ω).2 (Real.exp_pos _).le
  have hmono := condExp_mono (m := bmF a)
    (integrable_const (Real.exp (-r * a) * min (cfgValue r i₁ ϖ τ) (cfgValue r i₂ ϖ τ))) hYint
    (ae_of_all _ fun ω => mul_le_mul_of_nonneg_left (hcV ω).1 (Real.exp_pos _).le)
  rw [condExp_const (bmF.le a)] at hmono
  filter_upwards [hV, hmono] with ω e1 e2
  rw [debtValueAt, e1, hY, hΛ _ _ (le_add_of_nonneg_right hτ),
    le_div_iff₀ (Real.exp_pos _), mul_comm]
  exact e2

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: non-vacuity of the corrected
formula with news at a date `a ≥ 0`.** In the model economy with `κ = 0`, news
`ι = newsRate i₁ i₂ (a + τ)` revealed at `a + τ`, the economy without guidance
`bmSDF κ' r (a + τ) r`, random surpluses `s̄ + σW_j` and `B_a = 1` (`r > 0`, `i₁, i₂ ≥ 0`,
`ϖ > 0`): the random price levels `P_a = debtValueAt · r/(s̄ + σW_a)`,
`P_a' = cfgValue r r ϖ τ · r/(s̄ + σW_a)` satisfy the valuation equations, and a.s. where
`1 + κ'W_a ≠ 0` and `s̄ + σW_a > 0`,
`P_a/P_a' − 1 = E_a[e^{rτ}Λ_{a+τ} cfgJump r ι ϖ τ]/Λ_a` (`random_jump_at`).
Generalises `TidyR7GuidanceItoCex.bm_random_jump` and `TidyR7GuidanceItoCex.bm_random_valuation` to
date `a`. -/
theorem bm_random_jump_at (κ' : ℝ) {r i₁ i₂ ϖ a τ : ℝ} (sbar σ : ℝ) (hr : 0 < r)
    (hi₁ : 0 ≤ i₁) (hi₂ : 0 ≤ i₂) (hϖ : 0 < ϖ) (ha : 0 ≤ a) (hτ : 0 ≤ τ) :
    ∀ᵐ ω ∂gaussSeq, 1 + κ' * bmW a ω ≠ 0 → 0 < sbar + σ * bmW a ω →
      debtValueAt gaussSeq bmF (bmSDF 0 r (a + τ) (newsRate i₁ i₂ (a + τ))) a ϖ ω * r
          / (sbar + σ * bmW a ω) / (cfgValue r r ϖ τ * r / (sbar + σ * bmW a ω)) - 1
        = gaussSeq[fun ω => Real.exp (r * τ)
            * bmSDF 0 r (a + τ) (newsRate i₁ i₂ (a + τ)) (a + τ) ω
            * cfgJump r (newsRate i₁ i₂ (a + τ) ω) ϖ τ | bmF a] ω
          / bmSDF 0 r (a + τ) (newsRate i₁ i₂ (a + τ)) a ω := by
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  have hrv : 0 < r + ϖ := by linarith
  have hι0 : ∀ ω, 0 ≤ newsRate i₁ i₂ (a + τ) ω := fun ω => by
    unfold newsRate
    split_ifs
    · exact hi₁
    · exact hi₂
  have hιT := stronglyMeasurable_newsRate i₁ i₂ (a + τ)
  have hιm : Measurable (newsRate i₁ i₂ (a + τ)) := (hιT.mono (bmF.le _)).measurable
  have hG := guidanceSDFAt_bm 0 hr.le ha hτ hιT (newsRate_finite i₁ i₂ (a + τ)) hι0
  have hI := integrable_debtAt_bm 0 hr.le ha hτ hϖ hιm hι0
  have hG' := guidanceSDFAt_bm κ' hr.le ha hτ (ι := fun _ => r) stronglyMeasurable_const
    ⟨{r}, fun _ => Finset.mem_singleton_self r⟩ (fun _ => hr.le)
  have hI' := integrable_debtAt_bm κ' hr.le ha hτ hϖ (ι := fun _ => r) measurable_const
    (fun _ => hr.le)
  have hV1 := cfgValue_pos hϖ hrv (by linarith) hτ (r := r) (i := i₁)
  have hV2 := cfgValue_pos hϖ hrv (by linarith) hτ (r := r) (i := i₂)
  have hV' := cfgValue_pos hϖ hrv hrv hτ
  have hpv := pvSurplusAt_bm sbar σ hr ha
  have hpos := bm_random_debtValueAt_pos hr.le hi₁ hi₂ hϖ ha hτ
  have hΛa : ∀ (c : ℝ) (ι : (ℕ → ℝ) → ℝ) ω,
      bmSDF c r (a + τ) ι a ω = Real.exp (-r * a) * (1 + c * bmW a ω) := fun c ι ω => by
    simp only [bmSDF, le_add_of_nonneg_right hτ, ↓reduceIte]
  have key : ∀ {V S : ℝ}, V ≠ 0 → 1 / (V * r / S) * V = S / r := fun {V S} hV0 => by
    rw [one_div_div, div_mul_eq_mul_div, mul_comm V r, mul_div_mul_right _ _ hV0]
  set D := debtValueAt gaussSeq bmF (bmSDF 0 r (a + τ) (newsRate i₁ i₂ (a + τ))) a ϖ with hD
  have hval : ∀ᵐ ω ∂gaussSeq, bmSDF 0 r (a + τ) (newsRate i₁ i₂ (a + τ)) a ω ≠ 0 →
      1 / (D ω * r / (sbar + σ * bmW a ω)) * D ω
      = pvSurplusAt gaussSeq bmF r a (bmSurplus sbar σ) ω := by
    filter_upwards [hpos, hpv] with ω e1 e2 _
    rw [e2]
    exact key ((lt_min hV1 hV2).trans_le e1).ne'
  have hval' : ∀ᵐ ω ∂gaussSeq, bmSDF κ' r (a + τ) (fun _ => r) a ω ≠ 0 →
      1 / (cfgValue r r ϖ τ * r / (sbar + σ * bmW a ω))
        * debtValueAt gaussSeq bmF (bmSDF κ' r (a + τ) fun _ => r) a ϖ ω
      = pvSurplusAt gaussSeq bmF r a (bmSurplus sbar σ) ω := by
    filter_upwards [debtValueAt_guidance hB measurable_bmPath h𝓕 ha hτ hG' hrv hrv hI', hpv]
      with ω e1 e2 h0
    rw [e1 h0, e2]
    exact key hV'.ne'
  have hj := random_jump_at hB measurable_bmPath h𝓕 ha hτ hϖ hrv
    (fun ω => by linarith [hι0 ω]) (B := fun _ => 1)
    (Pa := fun ω => D ω * r / (sbar + σ * bmW a ω))
    (Pa' := fun ω => cfgValue r r ϖ τ * r / (sbar + σ * bmW a ω))
    (s := bmSurplus sbar σ) hG hI hG' hI' hval hval'
  filter_upwards [hj, hpv, hpos] with ω hω e2 e3 h1' hS
  exact hω (by rw [hΛa]; simp [(Real.exp_pos _).ne'])
    (by rw [hΛa]; exact mul_ne_zero (Real.exp_pos _).ne' h1')
    (by rw [e2]; exact (div_pos hS hr).ne')
    (div_pos (mul_pos ((lt_min hV1 hV2).trans_le e3) hr) hS) (div_pos (mul_pos hV' hr) hS)

end Cochrane.LongTermDebtDynamics.TidyR8GuidanceDateTBM
