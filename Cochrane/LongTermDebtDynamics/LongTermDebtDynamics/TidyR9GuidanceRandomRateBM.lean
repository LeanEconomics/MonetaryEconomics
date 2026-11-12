/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR9GuidanceRandomRate
import LongTermDebtDynamics.TidyR7GuidanceItoCex

/-!
# A continuous-valued random rate on the constructed Brownian motion: `i_u = ī + c sin W_u`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §A1.2.1,
pp. 559–561: non-vacuity of TidyR9GuidanceRandomRate on `TidyR7BrownianExist.bmPath` with its
natural filtration, and a strict failure of the book's formula at the expected rate.

## The economy

* The rate after the news date `T` is `sinRate ī c`: `i_u = ī + c sin W_u` with `|c| ≤ ī`
  (so `0 ≤ i ≤ ī + |c|`). It is an Itô process (`itoProcess_sinRate`, by Itô's formula for
  `sin`) with continuous paths, and its mean is `ī` at every date (`integral_sinRate`, the
  Gaussian law of `W_u` is symmetric).
* The discount factor is `Λ_t = rateDisc r T i t`: `e^{−rt}` up to `T`, then
  `e^{−rT}exp(−∫_T^t i)`; `Λ > 0` everywhere (`rateBM_pos`), and `exp(−∫_T^t i)` is an Itô
  process with drift `−i exp(−∫_T^t i)` (`itoProcess_rateBM_post`): `i` is the short rate.

## Main results

* `rateSDF_bm`, `integrable_debt_rateBM`: the hypotheses of TidyR9GuidanceRandomRate hold.
* `ae_sin_bmW_ne_zero`, `exists_integral_sin_not_ae_zero`: `sin W_t ≠ 0` a.s. for `t > 0`, and
  for `c ≠ 0` some `∫_T^{j₀} i` is not a.s. equal to its mean.
* `bm_bondPrice_sinRate`: the bond prices are `E_T[exp(−∫_T^{T+j} i)]`, with mean strictly above
  the book's `e^{−īj}` at some maturity.
* `bm_sinRate_jump` (**headline**): with `c ≠ 0`, `r > 0`, `ϖ > 0`, `T ≥ 0`, `s̄ > 0`: positive
  price levels `P_0 = E[rateValue]·r/s̄` (random rate) and `P_0' = cfgValue r r ϖ T · r/s̄`
  (rate `r` throughout) satisfy the stochastic valuation equations with `Λ, Λ' > 0`
  throughout; `P_0/P_0' − 1 = E[rateJump]` (`random_rate_jump`), and
  **`cfgJump r ī ϖ T < P_0/P_0' − 1`**: the book's formula at the expected rate `E[i_u] = ī`
  understates the jump (Jensen: the bond prices `E[exp(−∫ i)]` exceed `exp(−∫ E i)`). There is
  no covariance term here since `Λ_T = e^{−rT}` is deterministic.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR9GuidanceRandomRateBM

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.LongTermDebtDynamics.TidyR7BrownianExist
  Cochrane.LongTermDebtDynamics.TidyR7BrownianSchauder
  Cochrane.LongTermDebtDynamics.TidyR7BrownianTools
  Cochrane.LongTermDebtDynamics.TidyR7BrownianQV Cochrane.LongTermDebtDynamics.TidyR7ItoIntegral
  Cochrane.LongTermDebtDynamics.TidyR7ItoBridge Cochrane.LongTermDebtDynamics.TidyR7ItoProcess
  Cochrane.LongTermDebtDynamics.TidyR7ItoProductRule Cochrane.LongTermDebtDynamics.TidyR9ItoFormula
  Cochrane.LongTermDebtDynamics.TidyR7GuidanceSDF
  Cochrane.LongTermDebtDynamics.TidyR7GuidanceItoValuation
  Cochrane.LongTermDebtDynamics.TidyR7GuidanceItoBM
  Cochrane.LongTermDebtDynamics.TidyR7GuidanceItoCex
  Cochrane.LongTermDebtDynamics.TidyR9GuidanceRandomRate
  Cochrane.LongTermDebtDynamics.ForwardGuidance
open scoped NNReal

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: a continuous-valued random rate**,
`i_u = ī + c sin W_u` on the constructed Brownian motion. -/
noncomputable def sinRate (ib c : ℝ) (u : ℝ) (ω : ℕ → ℝ) : ℝ := ib + c * Real.sin (bmW u ω)

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the rate is jointly measurable. -/
theorem measurable_sinRate (ib c : ℝ) : Measurable (Function.uncurry (sinRate ib c)) :=
  measurable_const.add (measurable_const.mul (Real.measurable_sin.comp measurable_bmW))

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: for `|c| ≤ ī`,
`0 ≤ ī + c sin W_u ≤ ī + |c|` (a nonnegative nominal rate). -/
theorem sinRate_bound {ib c : ℝ} (hc : |c| ≤ ib) (u : ℝ) (ω : ℕ → ℝ) :
    0 ≤ sinRate ib c u ω ∧ sinRate ib c u ω ≤ ib + |c| := by
  have h := abs_le.1 (show |c * Real.sin (bmW u ω)| ≤ |c| by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg c) (Real.abs_sin_le_one _))
  exact ⟨by unfold sinRate; linarith, by unfold sinRate; linarith⟩

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the rate has continuous paths. -/
theorem continuous_sinRate (ib c : ℝ) (ω : ℕ → ℝ) : Continuous fun u => sinRate ib c u ω :=
  continuous_const.add (continuous_const.mul
    (Real.continuous_sin.comp (continuous_bmReal (continuous_bmPath ω))))

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the rate is an admissible Itô integrand on
`[s, t]` (adapted, bounded by `ī + |c|`, continuous paths).
An instance of `TidyR9ItoFormula.itoIntegrand_comp`. -/
theorem itoIntegrand_sinRate {ib c : ℝ} (hc : |c| ≤ ib) (s t : ℝ) :
    ItoIntegrand gaussSeq bmF (sinRate ib c) s t (ib + |c|) where
  adapted u _ := stronglyMeasurable_const.add (stronglyMeasurable_const.mul
    (Real.continuous_sin.comp_stronglyMeasurable
      ((bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath).adapted u)))
  bound u _ ω := by
    have h := sinRate_bound hc u ω
    rw [abs_of_nonneg h.1]
    exact h.2
  cont := ae_of_all _ fun ω => (continuous_sinRate ib c ω).continuousOn

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561 (Itô's formula for `sin`,
`TidyR9ItoFormula.itoProcess_comp`): the rate `ī + c sin W` is an Itô process** on `[s, t]`,
`0 ≤ s`, with drift `−(c/2) sin W` and diffusion `c cos W`.
Generalises `TidyR9ItoFormula.itoProcess_sin_bm`. -/
theorem itoProcess_sinRate (ib c : ℝ) {s t : ℝ} (hs : 0 ≤ s) :
    ItoProcess gaussSeq bmF bmPath (sinRate ib c)
      (fun u ω => c * Real.cos (bmW u ω) * 0 + -(c * Real.sin (bmW u ω)) / 2 * (1 * 1))
      (fun u ω => c * Real.cos (bmW u ω) * 1) s t (|c| * 0 + |c| / 2 * (1 * 1)) (|c| * 1) := by
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  exact itoProcess_comp (t := t) hB measurable_bmPath h𝓕 hs
    (itoProcess_bm hB measurable_bmPath h𝓕 hs)
    (ae_of_all _ fun ω => (continuous_bmReal (continuous_bmPath ω)).continuousOn)
    (f := fun x => ib + c * Real.sin x) (f' := fun x => c * Real.cos x)
    (f'' := fun x => -(c * Real.sin x))
    (fun x => by simpa using (Real.hasDerivAt_sin x).const_mul c |>.const_add ib)
    (fun x => by simpa using (Real.hasDerivAt_cos x).const_mul c)
    (by fun_prop) (L1 := |c|) (L2 := |c|)
    (fun x => by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg c) (Real.abs_cos_le_one x))
    (fun x => by
      rw [abs_neg, abs_mul]; exact mul_le_of_le_one_right (abs_nonneg c) (Real.abs_sin_le_one x))

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: `E[sin W_u] = 0` (the law
`gaussianReal 0 u` of `W_u` is symmetric, Mathlib `gaussianReal_map_neg`). -/
theorem integral_sin_bmW (u : ℝ) : ∫ ω, Real.sin (bmW u ω) ∂gaussSeq = 0 := by
  have h := (isPreBrownianReal_bmPath.hasLaw_eval u.toNNReal).integral_comp
    (f := Real.sin) (by fun_prop)
  have hG : (gaussianReal 0 u.toNNReal).map (fun x => -x) = gaussianReal 0 u.toNNReal := by
    simpa using gaussianReal_map_neg (μ := 0) (v := u.toNNReal)
  have h1 : ∫ x, Real.sin x ∂(gaussianReal 0 u.toNNReal) =
      ∫ x, Real.sin (-x) ∂(gaussianReal 0 u.toNNReal) := by
    conv_lhs => rw [← hG]
    rw [integral_map (by fun_prop) (by fun_prop)]
  simp only [Real.sin_neg, integral_neg] at h1
  change ∫ ω, Real.sin (bmPath u.toNNReal ω) ∂gaussSeq = 0
  exact h.trans (by linarith)

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the expected rate is `ī`** at every date,
`E[ī + c sin W_u] = ī`. -/
theorem integral_sinRate (ib c u : ℝ) : ∫ ω, sinRate ib c u ω ∂gaussSeq = ib := by
  have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
  have hs : Integrable (fun ω => Real.sin (bmW u ω)) gaussSeq :=
    (integrable_const (1 : ℝ)).mono'
      (Real.measurable_sin.comp (measurable_bmPath _)).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  simp only [sinRate]
  rw [integral_add (integrable_const ib) (hs.const_mul c), integral_const_mul, integral_sin_bmW,
    integral_const]
  simp

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the model discount factor is positive**,
`Λ_t = rateDisc r T i t > 0` for every `t` and state. -/
theorem rateBM_pos (r T ib c t : ℝ) (ω : ℕ → ℝ) : 0 < rateDisc r T (sinRate ib c) t ω :=
  Real.exp_pos _

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the hypotheses of the random-rate
valuation hold**: `rateDisc r T (ī + c sin W)` is a `RateSDF` with the known rate `r` and no
diffusion on `[0, T]` (`r ≥ 0`, `T ≥ 0`, `|c| ≤ ī`). -/
theorem rateSDF_bm {r T ib c : ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T) (hc : |c| ≤ ib) :
    RateSDF gaussSeq bmF bmPath (rateDisc r T (sinRate ib c)) (fun _ _ => 0) (sinRate ib c)
      r T (ib + |c|) where
  pre := by
    have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
    have hm := measurable_rateDisc (measurable_sinRate ib c) (sinRate_bound hc) r T
    have hb : ∀ t, 0 ≤ t → ∀ ω, ‖rateDisc r T (sinRate ib c) t ω‖ ≤ 1 := fun t ht ω => by
      have h := rateDisc_mem (measurable_sinRate ib c) (sinRate_bound hc) hr hT ht ω (r := r)
      rw [Real.norm_eq_abs, abs_of_pos h.1]
      exact h.2
    refine ⟨0, ?_⟩
    exact
      { adapted := by
          have e : rateDisc r T (sinRate ib c) 0 = fun _ => Real.exp (-r * 0) :=
            funext fun ω => rateDisc_of_le r _ hT ω
          rw [e]
          exact stronglyMeasurable_const
        rate := stronglyMeasurable_const
        rate_finite := ⟨{r}, fun _ => Finset.mem_singleton_self r⟩
        integ := by
          refine (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable ?_
          have hfst := (Measure.quasiMeasurePreserving_fst
            (μ := volume.restrict (Set.Ioc (0 : ℝ) T)) (ν := gaussSeq)).ae
            (ae_restrict_mem measurableSet_Ioc)
          filter_upwards [hfst] with p hp
          exact hb p.1 (le_of_lt hp.1) p.2
        integ_at := fun u hu => (integrable_const (1 : ℝ)).mono'
          (hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
          (ae_of_all _ fun ω => hb u hu.1 ω)
        diff := itoIntegrand_deterministic (h := fun _ => 0) continuousOn_const
          (fun _ _ => by simp)
        eq := fun u hu => by
          have hz := itoInt_const (W := bmPath) (P := gaussSeq) (𝓕 := bmF)
            isPreBrownianReal_bmPath measurable_bmPath
            (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) le_rfl hu.1
            (c := fun _ => (0 : ℝ)) stronglyMeasurable_const (C := 0) (fun _ => by simp)
          filter_upwards [hz] with ω hω
          rw [hω, zero_mul, add_zero]
          have hcongr : ∫ v in (0 : ℝ)..u, rateDisc r T (sinRate ib c) v ω =
              ∫ v in (0 : ℝ)..u, Real.exp (-r * v) := by
            refine intervalIntegral.integral_congr fun v hv => ?_
            rw [Set.uIcc_of_le hu.1] at hv
            exact rateDisc_of_le r _ (hv.2.trans hu.2) ω
          have hE : r * ∫ v in (0 : ℝ)..u, Real.exp (-r * v) = 1 - Real.exp (-r * u) := by
            rw [← intervalIntegral.integral_const_mul]
            have hd : ∀ x ∈ Set.uIcc 0 u, HasDerivAt (fun w => -Real.exp (-r * w))
                (r * Real.exp (-r * x)) x := fun x _ => by
              have h := (((hasDerivAt_id x).const_mul (-r)).exp).neg
              refine h.congr_deriv ?_
              simp only [id]
              ring
            rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
              apply Continuous.intervalIntegrable; fun_prop)]
            simp only [mul_zero, Real.exp_zero]
            ring_nf
          rw [hcongr, rateDisc_of_le r _ hu.2 ω, rateDisc_of_le r _ hT ω]
          simp only [mul_zero, Real.exp_zero]
          linarith }
  adaptedT := by
    have e : rateDisc r T (sinRate ib c) T = fun _ => Real.exp (-r * T) :=
      funext fun ω => rateDisc_of_le r _ le_rfl ω
    rw [e]
    exact stronglyMeasurable_const
  post u hu := ae_of_all _ fun ω => by
    simp only
    rw [rateDisc_of_ge r _ hu ω, rateDisc_of_le r _ le_rfl ω]
  rate_meas := measurable_sinRate ib c
  rate_bound := sinRate_bound hc

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the debt payoffs of the model economy are
jointly integrable on `(0, ∞) × Ω` (`ϖ > 0`). -/
theorem integrable_debt_rateBM {r T ib c ϖ : ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T) (hc : |c| ≤ ib)
    (hϖ : 0 < ϖ) :
    Integrable (fun p : ℝ × (ℕ → ℝ) =>
      ϖ * Real.exp (-ϖ * p.1) * rateDisc r T (sinRate ib c) p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod gaussSeq) := by
  have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
  refine ((integrableOn_weight hϖ).mul_prod (integrable_const (1 : ℝ) (μ := gaussSeq))).mono'
    ((by fun_prop : Measurable fun p : ℝ × (ℕ → ℝ) => ϖ * Real.exp (-ϖ * p.1)).mul
      (measurable_rateDisc (measurable_sinRate ib c) (sinRate_bound hc) r T)).aestronglyMeasurable
    ?_
  have hfst := (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (ν := gaussSeq)).ae (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [hfst] with p hp
  have h := rateDisc_mem (measurable_sinRate ib c) (sinRate_bound hc) hr hT (le_of_lt hp) p.2
    (r := r)
  have hw : 0 < ϖ * Real.exp (-ϖ * p.1) := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hw, abs_of_pos h.1]
  exact mul_le_mul_of_nonneg_left h.2 hw.le

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561 (with `itoProcess_rateDisc`): in the
model economy `i = ī + c sin W` is the short rate after `T`**: `exp(−∫_T^u i)` is an Itô
process on `[T, t]` with drift `−i exp(−∫_T^u i)` and no diffusion (`0 ≤ T ≤ t`, `|c| ≤ ī`). -/
theorem itoProcess_rateBM_post {ib c T t : ℝ} (hc : |c| ≤ ib) (hT : 0 ≤ T) (hTt : T ≤ t) :
    ItoProcess gaussSeq bmF bmPath (fun u ω => Real.exp (-∫ v in T..u, sinRate ib c v ω))
      (fun u ω => -(sinRate ib c u ω * Real.exp (-∫ v in T..u, sinRate ib c v ω)))
      (fun _ _ => 0) T t
      (Real.exp ((ib + |c|) * (t - T)) * (|-1| * (ib + |c|))
        + Real.exp ((ib + |c|) * (t - T)) / 2 * (0 * 0))
      (Real.exp ((ib + |c|) * (t - T)) * 0) :=
  itoProcess_rateDisc isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) hT hTt
    ((abs_nonneg c).trans hc |>.trans (le_add_of_nonneg_right (abs_nonneg c)))
    (itoIntegrand_sinRate hc T t) (fun ω => (continuous_sinRate ib c ω).continuousOn)

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: for `t > 0`, `sin W_t ≠ 0` a.s. (the
zeros `πℤ` of `sin` are countable, hence Lebesgue-null, and the law of `W_t` is absolutely
continuous, Mathlib `gaussianReal_absolutelyContinuous`). -/
theorem ae_sin_bmW_ne_zero {t : ℝ} (ht : 0 < t) : ∀ᵐ ω ∂gaussSeq, Real.sin (bmW t ω) ≠ 0 := by
  set Z : Set ℝ := {x | Real.sin x = 0} with hZ
  have hZc : Z.Countable := by
    have e : Z = Set.range fun n : ℤ => (n : ℝ) * Real.pi := by
      ext x
      simp only [hZ, Set.mem_range, Real.sin_eq_zero_iff]
      exact Iff.rfl
    rw [e]
    exact Set.countable_range _
  have hZm : MeasurableSet Z := hZc.measurableSet
  have hlaw := (isPreBrownianReal_bmPath.hasLaw_eval t.toNNReal).map_eq
  have hne : t.toNNReal ≠ 0 := by simpa using ht
  have h1 : gaussSeq (bmW t ⁻¹' Z) = gaussianReal 0 t.toNNReal Z := by
    rw [← hlaw, Measure.map_apply (measurable_bmPath _) hZm]
    rfl
  have h2 : gaussianReal 0 t.toNNReal Z = 0 :=
    gaussianReal_absolutelyContinuous 0 hne (hZc.measure_zero volume)
  rw [ae_iff]
  have e : {ω | ¬ Real.sin (bmW t ω) ≠ 0} = bmW t ⁻¹' Z := by
    ext ω
    simp [hZ]
  rw [e, h1, h2]

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the integrated rate is genuinely
random.** For `c ≠ 0` and `T ≥ 0` there is a maturity `j₀ > T` such that `∫_T^{j₀} i` is not
a.s. equal to its mean `∫_T^{j₀} E[i] = ī(j₀ − T)`. Proof: otherwise, a.s., `∫_T^q sin W = 0`
for every rational `q > T`, hence (continuity) for every `q > T`, and differentiating at
`T + 1` gives `sin W_{T+1} = 0`, contradicting `ae_sin_bmW_ne_zero`. -/
theorem exists_integral_sin_not_ae_zero {ib c T : ℝ} (hc0 : c ≠ 0) (hT : 0 ≤ T) :
    ∃ j₀, T < j₀ ∧ ¬ ((fun ω => ∫ v in T..j₀, sinRate ib c v ω) =ᵐ[gaussSeq]
      fun _ => ∫ v in T..j₀, ∫ ω, sinRate ib c v ω ∂gaussSeq) := by
  have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
  have hsc : ∀ ω, Continuous fun v => Real.sin (bmW v ω) := fun ω =>
    Real.continuous_sin.comp (continuous_bmReal (continuous_bmPath ω))
  have hsplit : ∀ j ω, ∫ v in T..j, sinRate ib c v ω =
      (j - T) * ib + c * ∫ v in T..j, Real.sin (bmW v ω) := fun j ω => by
    simp only [sinRate]
    rw [intervalIntegral.integral_add intervalIntegrable_const
      ((hsc ω).intervalIntegrable _ _ |>.const_mul c), intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, smul_eq_mul]
  by_contra hall
  push Not at hall
  have hq : ∀ q : ℚ, ∀ᵐ ω ∂gaussSeq, T < (q : ℝ) → ∫ v in T..(q : ℝ), Real.sin (bmW v ω) = 0 :=
    fun q => by
      by_cases hqT : T < (q : ℝ)
      · filter_upwards [hall q hqT] with ω hω _
        simp_rw [integral_sinRate, intervalIntegral.integral_const, smul_eq_mul] at hω
        rw [hsplit] at hω
        have : c * ∫ v in T..(q : ℝ), Real.sin (bmW v ω) = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hc0
      · exact ae_of_all _ fun _ h => (hqT h).elim
  have hall' := ae_all_iff.2 hq
  obtain ⟨ω, hω, hsin⟩ := (hall'.and (ae_sin_bmW_ne_zero (t := T + 1) (by linarith))).exists
  set F : ℝ → ℝ := fun x => ∫ v in T..x, Real.sin (bmW v ω) with hF
  have hFc : Continuous F := intervalIntegral.continuous_primitive
    (fun a b => (hsc ω).intervalIntegrable a b) T
  have hzero : Set.Ioi T ⊆ {x | F x = 0} := by
    have hcl : IsClosed {x | F x = 0} := isClosed_eq hFc continuous_const
    refine (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioi).trans
      (hcl.closure_subset_iff.2 fun x ⟨hx, q, hq'⟩ => ?_)
    subst hq'
    exact hω q hx
  have hd0 : HasDerivAt F 0 (T + 1) := by
    refine (hasDerivAt_const (T + 1) (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (show T < T + 1 by linarith)] with x hx
    exact hzero hx
  have hd1 : HasDerivAt F (Real.sin (bmW (T + 1) ω)) (T + 1) :=
    intervalIntegral.integral_hasDerivAt_right ((hsc ω).intervalIntegrable _ _)
      ((hsc ω).stronglyMeasurableAtFilter _ _) (hsc ω).continuousAt
  exact hsin (hd1.unique hd0)

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the book's formula at the expected rate
fails for a continuous-valued random rate — headline.** On the constructed Brownian motion,
with the rate `r > 0` until `T ≥ 0` and `i_u = ī + c sin W_u` after (`c ≠ 0`, `|c| ≤ ī`),
`ϖ > 0`, surpluses `s̄ > 0`, `B_0 = 1`: the positive price levels
`P_0 = E[rateValue]·r/s̄` (with the random rate, discount factor `rateDisc r T i > 0`) and
`P_0' = cfgValue r r ϖ T · r/s̄` (rate `r` throughout, discount factor `e^{−rt} > 0`) satisfy
the stochastic valuation equations; the corrected formula `random_rate_jump` applies and gives
`P_0/P_0' − 1 = E[rateJump]`; and `cfgJump r ī ϖ T < P_0/P_0' − 1` although `E[i_u] = ī` at
every date. -/
theorem bm_sinRate_jump {r ib c ϖ T sbar : ℝ} (hr : 0 < r) (hc0 : c ≠ 0) (hc : |c| ≤ ib)
    (hϖ : 0 < ϖ) (hT : 0 ≤ T) (hs : 0 < sbar) :
    (∀ t ω, 0 < rateDisc r T (sinRate ib c) t ω ∧ 0 < bmSDF 0 r T (fun _ => r) t ω)
      ∧ 0 < (∫ ω, rateValue r ϖ T (sinRate ib c) ω ∂gaussSeq) * r / sbar
      ∧ 0 < cfgValue r r ϖ T * r / sbar
      ∧ (∀ᵐ ω ∂gaussSeq, 1 / ((∫ ω, rateValue r ϖ T (sinRate ib c) ω ∂gaussSeq) * r / sbar)
          * debtValue gaussSeq bmF (rateDisc r T (sinRate ib c)) ϖ ω
          = pvSurplus gaussSeq bmF r (fun _ _ => sbar) ω)
      ∧ (∀ᵐ ω ∂gaussSeq, 1 / (cfgValue r r ϖ T * r / sbar)
          * debtValue gaussSeq bmF (bmSDF 0 r T fun _ => r) ϖ ω
          = pvSurplus gaussSeq bmF r (fun _ _ => sbar) ω)
      ∧ (∀ i, ∫ ω, sinRate ib c i ω ∂gaussSeq = ib)
      ∧ (∫ ω, rateValue r ϖ T (sinRate ib c) ω ∂gaussSeq) * r / sbar
          / (cfgValue r r ϖ T * r / sbar) - 1 = ∫ ω, rateJump r ϖ T (sinRate ib c) ω ∂gaussSeq
      ∧ cfgJump r ib ϖ T < (∫ ω, rateValue r ϖ T (sinRate ib c) ω ∂gaussSeq) * r / sbar
          / (cfgValue r r ϖ T * r / sbar) - 1 := by
  have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  have hrv : 0 < r + ϖ := by linarith
  have hib : 0 ≤ ib := (abs_nonneg c).trans hc
  have hiv : 0 < ib + ϖ := by linarith
  have hRS := rateSDF_bm hr.le hT hc
  have hI := integrable_debt_rateBM hr.le hT hc hϖ
  have hG' := guidanceSDF_bm 0 hr.le hT (ι := fun _ => r) stronglyMeasurable_const
    ⟨{r}, fun _ => Finset.mem_singleton_self r⟩ (fun _ => hr.le)
  have hI' := integrable_debt_bm 0 hr.le hT hϖ (ι := fun _ => r) measurable_const
    (fun _ => hr.le)
  set V := ∫ ω, rateValue r ϖ T (sinRate ib c) ω ∂gaussSeq with hV
  -- the mean rate path is `ī`
  have hmean : (fun v (_ : ℕ → ℝ) => ∫ ω, sinRate ib c v ω ∂gaussSeq) = fun _ _ => ib := by
    funext v _
    exact integral_sinRate ib c v
  have hJen := integral_rateValue_ge (P := gaussSeq) (measurable_sinRate ib c)
    (sinRate_bound hc) hr.le hT hϖ (fun _ => 0)
  rw [hmean, rateValue_const hrv hiv hT] at hJen
  have hstrict : cfgValue r ib ϖ T < V := hJen.2 (by
    obtain ⟨j₀, hj₀, hne⟩ := exists_integral_sin_not_ae_zero (ib := ib) hc0 hT
    exact ⟨j₀, hj₀, hne⟩)
  have hVpos : 0 < V := lt_trans (cfgValue_pos hϖ hrv hiv hT) hstrict
  have hV' := cfgValue_pos hϖ hrv hrv hT
  have hP : 0 < V * r / sbar := by positivity
  have hP' : 0 < cfgValue r r ϖ T * r / sbar := by positivity
  -- the debt value with the random rate is `E[rateValue]`
  have hΛ0 : ∀ ω, rateDisc r T (sinRate ib c) 0 ω = 1 := fun ω => by
    rw [rateDisc_of_le r _ hT ω]; simp
  have hZ : ∀ ω, Real.exp (r * T) * rateDisc r T (sinRate ib c) T ω = 1 := fun ω => by
    rw [rateDisc_of_le r _ le_rfl ω, ← Real.exp_add]; simp
  have hdv : ∀ᵐ ω ∂gaussSeq, debtValue gaussSeq bmF (rateDisc r T (sinRate ib c)) ϖ ω = V := by
    filter_upwards [condExp_debtValue_rate hB measurable_bmPath h𝓕 hT hr.le hϖ hRS hI]
      with ω hω
    rw [debtValue, hω, hΛ0, div_one, condExp_bmF_zero]
    simp_rw [hZ, one_mul]
    exact hV.symm
  have h00 : ∀ ω, bmSDF 0 r T (fun _ => r) 0 ω = 1 := fun ω => by
    simp [bmSDF, hT, bmW_zero]
  have hval : ∀ᵐ ω ∂gaussSeq, 1 / (V * r / sbar)
      * debtValue gaussSeq bmF (rateDisc r T (sinRate ib c)) ϖ ω
      = pvSurplus gaussSeq bmF r (fun _ _ => sbar) ω := by
    filter_upwards [hdv] with ω hω
    rw [hω, pvSurplus_const hr]
    field_simp
  have hval' : ∀ᵐ ω ∂gaussSeq, 1 / (cfgValue r r ϖ T * r / sbar)
      * debtValue gaussSeq bmF (bmSDF 0 r T fun _ => r) ϖ ω
      = pvSurplus gaussSeq bmF r (fun _ _ => sbar) ω := by
    filter_upwards [debtValue_guidance hB measurable_bmPath h𝓕 hT hG' hrv hrv hI'] with ω hω
    rw [hω (by rw [h00]; exact one_ne_zero), pvSurplus_const hr]
    field_simp
  -- the corrected formula of `random_rate_jump`
  have hjump : V * r / sbar / (cfgValue r r ϖ T * r / sbar) - 1
      = ∫ ω, rateJump r ϖ T (sinRate ib c) ω ∂gaussSeq := by
    have hj := random_rate_jump hB measurable_bmPath h𝓕 hT hr.le hϖ (B0 := fun _ => 1)
      (P0 := fun _ => V * r / sbar) (P0' := fun _ => cfgValue r r ϖ T * r / sbar)
      hRS hI hG' hI' (fun _ => hP) (fun _ => hP') hval hval'
    obtain ⟨ω, hω⟩ := hj.exists
    rw [hω (by rw [hΛ0]; exact one_ne_zero) (by rw [h00]; exact one_ne_zero)
      (by rw [pvSurplus_const hr]; positivity), condExp_bmF_zero, hΛ0, div_one]
    simp_rw [hZ, one_mul]
  have hJint : ∫ ω, rateJump r ϖ T (sinRate ib c) ω ∂gaussSeq = V * ((r + ϖ) / ϖ) - 1 := by
    have hVi : Integrable (rateValue r ϖ T (sinRate ib c)) gaussSeq :=
      (integrable_const (1 : ℝ)).mono'
        (measurable_rateValue (measurable_sinRate ib c) (sinRate_bound hc) r ϖ
          T).aestronglyMeasurable
        (ae_of_all _ fun ω => by
          have h := rateValue_mem (measurable_sinRate ib c) (sinRate_bound hc) hr.le hT hϖ ω
          rw [Real.norm_eq_abs, abs_of_nonneg h.1]
          exact h.2)
    simp only [rateJump]
    rw [integral_sub (hVi.mul_const _) (integrable_const 1), integral_mul_const,
      integral_const]
    simp [← hV]
  refine ⟨fun t ω => ⟨rateBM_pos r T ib c t ω, ?_⟩, hP, hP', hval, hval',
    fun i => integral_sinRate ib c i, hjump, ?_⟩
  · unfold bmSDF
    split_ifs <;> simp [Real.exp_pos]
  · rw [hjump, hJint]
    have e := cfgJump_add_one (r := r) (x := ib) T hϖ.ne' hrv.ne' hiv.ne'
    have hk : 0 < (r + ϖ) / ϖ := by positivity
    nlinarith [mul_lt_mul_of_pos_right hstrict hk]

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: bond prices at the news date in the
model economy** (non-vacuity of `bondPrice_rate`). For every `j ≥ 0`, a.s.
`Q_T^{(T+j)} = E_T[Λ_{T+j}]/Λ_T = E_T[exp(−∫_T^{T+j} (ī + c sin W))]` (`Λ_T = e^{−rT} > 0`);
and for `c ≠ 0` some maturity `j₀ > 0` has mean bond price strictly above the book's
`e^{−īj₀}` at the expected rate (Jensen, `integral_rateDisc_ge`). -/
theorem bm_bondPrice_sinRate {r T ib c : ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T) (hc : |c| ≤ ib)
    (hc0 : c ≠ 0) :
    (∀ j, 0 ≤ j → ∀ᵐ ω ∂gaussSeq, gaussSeq[rateDisc r T (sinRate ib c) (T + j) | bmF T] ω
        / rateDisc r T (sinRate ib c) T ω
        = gaussSeq[fun ω => Real.exp (-∫ v in T..T + j, sinRate ib c v ω) | bmF T] ω)
    ∧ ∃ j₀, 0 < j₀ ∧ Real.exp (-ib * j₀)
        < ∫ ω, Real.exp (-∫ v in T..T + j₀, sinRate ib c v ω) ∂gaussSeq := by
  have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
  refine ⟨fun j hj => (bondPrice_rate isPreBrownianReal_bmPath hT (rateSDF_bm hr hT hc)
    hj).mono fun ω h => h (rateBM_pos r T ib c T ω).ne', ?_⟩
  obtain ⟨j₁, hj₁, hne⟩ := exists_integral_sin_not_ae_zero (ib := ib) hc0 hT
  have h := (integral_rateDisc_ge (P := gaussSeq) (measurable_sinRate ib c) (sinRate_bound hc)
    r T j₁ (fun _ => 0)).2 hj₁ hne
  have hmean : (fun v (_ : ℕ → ℝ) => ∫ ω, sinRate ib c v ω ∂gaussSeq) = fun _ _ => ib := by
    funext v _
    exact integral_sinRate ib c v
  rw [hmean, rateDisc_const, min_eq_right hj₁.le, max_eq_left (sub_nonneg.2 hj₁.le)] at h
  simp_rw [rateDisc_of_ge r _ hj₁.le] at h
  rw [integral_const_mul] at h
  have e : Real.exp (-(r * T + ib * (j₁ - T))) = Real.exp (-r * T) * Real.exp (-ib * (j₁ - T)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e] at h
  refine ⟨j₁ - T, by linarith, ?_⟩
  rw [add_sub_cancel]
  exact lt_of_mul_lt_mul_left h (Real.exp_pos _).le

end Cochrane.LongTermDebtDynamics.TidyR9GuidanceRandomRateBM
