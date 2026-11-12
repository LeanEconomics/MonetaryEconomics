/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR7MonetarismValuation
import Monetarism.TidyR7ProductStepCases
import Monetarism.ContinuousTime

/-!
# Links: the `C¹` case, the deterministic case and the `Δ`-grid

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). The stochastic chain
`TidyR7MonetarismModel` / `TidyR7MonetarismValuation` specialises to the earlier forms.

## The `C¹` case (`c1Model`)

If `n = Λ/P`, `B` and `M` have `C¹` paths with `ṅ = −in`, `Ḃ = iB + i^mM − Ps − Ṁ` (with `Λ := nP`,
`A = n`, `N = 0`), the model `TidyR7MonetarismModel.MonetaryModel` holds (`c1Model`), and
* `incr_1_32_C1`: `TidyR7MonetarismModel.MonetaryModel.incr_1_32` gives exactly
  `E_s[n_tB_t − n_sB_s] = E_s∫_s^t −n(Ps + Ṁ)`, the conclusion (ii) of
  `TidyR7ProductStepCases.product_step_1_32_C1` and the martingale condition of
  `TidyR6StochasticDrift.drift_1_32_fv`;
* `valuation_1_33_C1`: `TidyR7MonetarismValuation.MonetaryModel.valuation_1_33` gives exactly the
  equivalence of `TidyR6StochasticDrift.valuation_1_33_fv` (under the domination conditions; the
  `C¹` proof needs none because the bracket vanishes identically).

## The deterministic case

On the one-point space (`Unit`, Dirac measure, constant filtration `unitFilt`) conditional
expectations are the identity: `money_printing_recovered` and `money_interest_recovered` derive the
conclusions of `ContinuousTime.money_printing_iff` ((1.33)) and `ContinuousTime.money_interest_iff`
((1.34)) from the stochastic `TidyR7MonetarismValuation.MonetaryModel.valuation_1_33` and
`TidyR7MonetarismValuation.MonetaryModel.valuation_1_34` (for globally `C¹` paths with
continuous derivatives and `N > 0`; the `ContinuousTime` versions need these only on `[t, ∞)`).

## The `Δ`-grid

`TidyR6StochasticDrift.incr_1_32` and `TidyR6StochasticDrift.incr_1_34` are the exact discrete
forms. They are consistent with the continuous-time drifts in two ways:
* `grid_1_32_eq`: the discrete increment is `−E_k[n_{k+1}](P_ks_kΔ + ΔM_k)`: each period's flow is
  discounted by the expected end-of-period `n`, the grid analogue of `−E_s[∫ Λs dr + ∫ n dM]`;
* `grid_1_32_rate`, `grid_1_34_rate`: per unit time (with `ΔM = mΔ`) the increments tend, as
  `Δ → 0`, to the drifts `−n(Ps + m)` of `TidyR7MonetarismModel.MonetaryModel.hasDrift_1_32_ac`
  (`i^m = 0`) and `−n(Ps + (i − i^m)M)` of `TidyR7MonetarismModel.MonetaryModel.hasDrift_1_34`
  (`Λ = nP`).
-/

namespace Cochrane.Monetarism.TidyR7MonetarismLinks

open MeasureTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesIntegral Cochrane.Monetarism.TidyR7ProductStep
  Cochrane.Monetarism.TidyR7MonetarismAC Cochrane.Monetarism.TidyR7MonetarismModel
  Cochrane.Monetarism.TidyR7MonetarismValuation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ}

/-! ## The `C¹` case -/

/-- Cochrane (2023), A1 §1.6, p. 567: with `Λ = nP`, `Λ/P = n`. -/
theorem disc_mul {n Pr : ℝ → Ω → ℝ} (hP : ∀ u ω, 0 < Pr u ω) :
    disc (fun u ω => n u ω * Pr u ω) Pr = n :=
  funext fun u => funext fun ω => mul_div_cancel_right₀ _ (hP u ω).ne'

/-- **Cochrane (2023), A1 §1.6, (1.31)–(1.32), p. 567: the `C¹` model.** If `n > 0`, `P > 0`, `B`,
`M` are adapted, `n` has `C¹` paths with `ṅ = −in`, `M` has derivative `Ṁ` (continuous), `B` has
derivative `iB + i^mM − Ps − Ṁ` (the flow (1.31)), `i` and the flow rate `iB + i^mM − Ps` are
continuous, then `TidyR7MonetarismModel.MonetaryModel` holds with `Λ = nP`, `A = n`, `N = 0`. -/
theorem c1Model [IsFiniteMeasure μ] {n B M Pr sp i im dM : ℝ → Ω → ℝ}
    (hn : ∀ ω r, HasDerivAt (fun u => n u ω) (-(i r ω * n r ω)) r) (hnpos : ∀ u ω, 0 < n u ω)
    (hM : ∀ ω r, HasDerivAt (fun u => M u ω) (dM r ω) r)
    (hB : ∀ ω r, HasDerivAt (fun u => B u ω)
      (i r ω * B r ω + im r ω * M r ω - Pr r ω * sp r ω - dM r ω) r)
    (hP : ∀ u ω, 0 < Pr u ω) (hic : ∀ ω, Continuous fun r => i r ω)
    (hdMc : ∀ ω, Continuous fun r => dM r ω)
    (hfc : ∀ ω, Continuous fun r => i r ω * B r ω + im r ω * M r ω - Pr r ω * sp r ω)
    (hna : ∀ u, StronglyMeasurable[𝓕 u] (n u)) (hPa : ∀ u, StronglyMeasurable[𝓕 u] (Pr u))
    (hBa : ∀ u, StronglyMeasurable[𝓕 u] (B u)) (hMa : ∀ u, StronglyMeasurable[𝓕 u] (M u)) :
    MonetaryModel μ 𝓕 (fun u ω => n u ω * Pr u ω) Pr B M n (fun _ _ => 0) i im sp := by
  have hd := disc_mul (n := n) hP
  have hnc : ∀ ω, Continuous fun r => n r ω := fun ω =>
    TidyR7ProductStepCases.continuous_of_hasDerivAt (hn ω)
  have hrc : ∀ ω, Continuous fun r => -(i r ω * n r ω) := fun ω => ((hic ω).mul (hnc ω)).neg
  refine
    { P_pos := hP
      Λ_pos := fun u ω => mul_pos (hnpos u ω) (hP u ω)
      Λ_adapted := fun u => (hna u).mul (hPa u)
      P_adapted := hPa
      dec := fun u ω => by rw [hd]; ring
      A_incr := fun ω u v _ => ?_
      A_int := fun ω u v => ?_
      N_mart := martingale_const _ _ _
      N_cadlag := fun _ => IsCadlag.const
      B_adapted := hBa
      M_adapted := hMa
      M_cont := fun ω => TidyR7ProductStepCases.continuous_of_hasDerivAt (hM ω)
      M_bv := fun ω a b => TidyR7ProductStepCases.bv_of_hasDerivAt (hM ω) (hdMc ω)
      flow := fun ω u v _ => ?_
      flow_int := fun ω u v => (hfc ω).intervalIntegrable u v }
  · rw [hd, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hn ω r)
      ((hrc ω).intervalIntegrable u v)]
  · rw [hd]
    exact (hrc ω).intervalIntegrable u v
  · have hW : ∀ r, HasDerivAt (fun u => addProc B M u ω) (flowRate B M Pr i im sp r ω) r :=
      fun r => ((hB ω r).add (hM ω r)).congr_deriv (by simp only [flowRate]; ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hW r)
      ((hfc ω).intervalIntegrable u v)]

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: in the `C¹` model, path by path,
`∫_s^T Λs dr + ∫_s^T n dM = ∫_s^T n(Ps + Ṁ) dr` for `s ≤ T` (`Λ = nP`). -/
theorem flow133_C1 {n M Pr sp dM : ℝ → Ω → ℝ} (hP : ∀ u ω, 0 < Pr u ω)
    (hnc : ∀ ω, Continuous fun r => n r ω) (hM : ∀ ω r, HasDerivAt (fun u => M u ω) (dM r ω) r)
    (hdMc : ∀ ω, Continuous fun r => dM r ω)
    (hpc : ∀ ω, Continuous fun r => Pr r ω * sp r ω) {s T : ℝ} (hsT : s ≤ T) (ω : Ω) :
    flow133 (fun u ω => n u ω * Pr u ω) Pr M sp s T ω =
      ∫ r in s..T, n r ω * (Pr r ω * sp r ω + dM r ω) := by
  have c1 : Continuous fun r => n r ω * Pr r ω * sp r ω :=
    ((hnc ω).mul (hpc ω)).congr fun r => by simp only [Pi.mul_apply]; ring
  have c2 : Continuous fun r => n r ω * dM r ω := (hnc ω).mul (hdMc ω)
  rw [flow133, disc_mul hP, TidyR7ProductStepCases.rsInt_eq_integral_mul_deriv hsT
    (hnc ω).continuousOn (hM ω) (hdMc ω), ← intervalIntegral.integral_add
    (c1.intervalIntegrable s T) (c2.intervalIntegrable s T)]
  exact intervalIntegral.integral_congr fun r _ => by ring

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the `C¹` case recovered.** In the `C¹` model with
`i^m = 0` (`Ḃ = iB − Ps − Ṁ`) and the domination conditions on `[s, t]`,
`TidyR7MonetarismModel.MonetaryModel.incr_1_32` gives a.s.
`E_s[n_tB_t − n_sB_s] = E_s∫_s^t −n(Ps + Ṁ)`: the conclusion (ii) of
`TidyR7ProductStepCases.product_step_1_32_C1`, i.e. the martingale condition of
`TidyR6StochasticDrift.drift_1_32_fv`. -/
theorem incr_1_32_C1 [IsFiniteMeasure μ] {n B M Pr sp i dM : ℝ → Ω → ℝ}
    (hn : ∀ ω r, HasDerivAt (fun u => n u ω) (-(i r ω * n r ω)) r) (hnpos : ∀ u ω, 0 < n u ω)
    (hM : ∀ ω r, HasDerivAt (fun u => M u ω) (dM r ω) r)
    (hB : ∀ ω r, HasDerivAt (fun u => B u ω) (i r ω * B r ω - Pr r ω * sp r ω - dM r ω) r)
    (hP : ∀ u ω, 0 < Pr u ω) (hic : ∀ ω, Continuous fun r => i r ω)
    (hdMc : ∀ ω, Continuous fun r => dM r ω)
    (hfc : ∀ ω, Continuous fun r => i r ω * B r ω - Pr r ω * sp r ω)
    (hna : ∀ u, StronglyMeasurable[𝓕 u] (n u)) (hPa : ∀ u, StronglyMeasurable[𝓕 u] (Pr u))
    (hBa : ∀ u, StronglyMeasurable[𝓕 u] (B u)) (hMa : ∀ u, StronglyMeasurable[𝓕 u] (M u))
    {s t : ℝ} (hst : s ≤ t) (hdom : Dominated μ n (fun _ _ => 0) s t B n) :
    μ[fun ω => n t ω * B t ω - n s ω * B s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => ∫ r in s..t, -(n r ω * (Pr r ω * sp r ω + dM r ω)) | 𝓕 s] := by
  have hm := c1Model (μ := μ) (𝓕 := 𝓕) (n := n) (B := B) (M := M) (Pr := Pr) (sp := sp)
    (i := i) (im := fun _ _ => 0) (dM := dM) hn hnpos hM
    (fun ω r => (hB ω r).congr_deriv (by ring)) hP hic hdMc
    (fun ω => (hfc ω).congr fun r => by ring) hna hPa hBa hMa
  have hnc : ∀ ω, Continuous fun r => n r ω := fun ω =>
    TidyR7ProductStepCases.continuous_of_hasDerivAt (hn ω)
  have hpc : ∀ ω, Continuous fun r => Pr r ω * sp r ω := fun ω => by
    have := ((hic ω).mul (TidyR7ProductStepCases.continuous_of_hasDerivAt (hB ω))).sub (hfc ω)
    exact this.congr fun r => by simp only [Pi.mul_apply, Pi.sub_apply]; ring
  have h : μ[fun ω => disc (fun u ω => n u ω * Pr u ω) Pr t ω * B t ω -
      disc (fun u ω => n u ω * Pr u ω) Pr s ω * B s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => -flow133 (fun u ω => n u ω * Pr u ω) Pr M sp s t ω | 𝓕 s] :=
    hm.incr_1_32 hst (by rw [disc_mul hP]; exact hdom) fun _ _ => rfl
  have e2 : (fun ω => -flow133 (fun u ω => n u ω * Pr u ω) Pr M sp s t ω) =
      fun ω => ∫ r in s..t, -(n r ω * (Pr r ω * sp r ω + dM r ω)) := funext fun ω => by
    rw [flow133_C1 hP hnc hM hdMc hpc hst ω, intervalIntegral.integral_neg]
  rw [disc_mul hP, e2] at h
  exact h

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the `C¹` case recovered.** In the `C¹` model with
`i^m = 0`, the domination conditions on every `[t₀, T]`, `n_TB_T` integrable and
`∫_{t₀}^T n(Ps + Ṁ) → G` in `L¹`: `n_{t₀}B_{t₀} = E_{t₀}[G]` a.s. iff `E_{t₀}[n_TB_T] → 0` in `L¹`,
the equivalence of `TidyR6StochasticDrift.valuation_1_33_fv`, here derived from
`TidyR7MonetarismValuation.MonetaryModel.valuation_1_33`. -/
theorem valuation_1_33_C1 [IsFiniteMeasure μ] {n B M Pr sp i dM : ℝ → Ω → ℝ}
    (hn : ∀ ω r, HasDerivAt (fun u => n u ω) (-(i r ω * n r ω)) r) (hnpos : ∀ u ω, 0 < n u ω)
    (hM : ∀ ω r, HasDerivAt (fun u => M u ω) (dM r ω) r)
    (hB : ∀ ω r, HasDerivAt (fun u => B u ω) (i r ω * B r ω - Pr r ω * sp r ω - dM r ω) r)
    (hP : ∀ u ω, 0 < Pr u ω) (hic : ∀ ω, Continuous fun r => i r ω)
    (hdMc : ∀ ω, Continuous fun r => dM r ω)
    (hfc : ∀ ω, Continuous fun r => i r ω * B r ω - Pr r ω * sp r ω)
    (hna : ∀ u, StronglyMeasurable[𝓕 u] (n u)) (hPa : ∀ u, StronglyMeasurable[𝓕 u] (Pr u))
    (hBa : ∀ u, StronglyMeasurable[𝓕 u] (B u)) (hMa : ∀ u, StronglyMeasurable[𝓕 u] (M u))
    {t0 : ℝ} (hdom : ∀ T, t0 ≤ T → Dominated μ n (fun _ _ => 0) t0 T B n)
    (hYi : ∀ T, t0 ≤ T → Integrable (fun ω => n T ω * B T ω) μ) {G : Ω → ℝ}
    (hG : Integrable G μ)
    (hconv : Tendsto (fun T => ∫ ω, |(∫ r in t0..T, n r ω * (Pr r ω * sp r ω + dM r ω)) - G ω| ∂μ)
      atTop (𝓝 0)) :
    (fun ω => n t0 ω * B t0 ω) =ᵐ[μ] μ[G | 𝓕 t0] ↔
      Tendsto (fun T => ∫ ω, |μ[fun ω => n T ω * B T ω | 𝓕 t0] ω| ∂μ) atTop (𝓝 0) := by
  have hm := c1Model (μ := μ) (𝓕 := 𝓕) (n := n) (B := B) (M := M) (Pr := Pr) (sp := sp)
    (i := i) (im := fun _ _ => 0) (dM := dM) hn hnpos hM
    (fun ω r => (hB ω r).congr_deriv (by ring)) hP hic hdMc
    (fun ω => (hfc ω).congr fun r => by ring) hna hPa hBa hMa
  have hnc : ∀ ω, Continuous fun r => n r ω := fun ω =>
    TidyR7ProductStepCases.continuous_of_hasDerivAt (hn ω)
  have hpc : ∀ ω, Continuous fun r => Pr r ω * sp r ω := fun ω => by
    have := ((hic ω).mul (TidyR7ProductStepCases.continuous_of_hasDerivAt (hB ω))).sub (hfc ω)
    exact this.congr fun r => by simp only [Pi.mul_apply, Pi.sub_apply]; ring
  have hconv' : Tendsto (fun T => ∫ ω,
      |flow133 (fun u ω => n u ω * Pr u ω) Pr M sp t0 T ω - G ω| ∂μ) atTop (𝓝 0) := by
    refine hconv.congr' ?_
    filter_upwards [eventually_ge_atTop t0] with T hT
    simp only [flow133_C1 hP hnc hM hdMc hpc hT]
  have h := MonetaryModel.valuation_1_33 hm (fun _ _ => rfl) (s := t0)
    (fun T hT => by rw [disc_mul hP]; exact hdom T hT)
    (fun T hT => by rw [disc_mul hP]; exact hYi T hT) hG hconv'
  rw [disc_mul hP] at h
  exact h

/-! ## The deterministic case -/

/-- Cochrane (2023), A1 §1.6, p. 567: the constant filtration on the one-point space. -/
noncomputable def unitFilt : Filtration ℝ (inferInstance : MeasurableSpace Unit) :=
  Filtration.const ℝ (inferInstance : MeasurableSpace Unit) le_rfl

/-- Cochrane (2023), A1 §1.6, p. 567: on the one-point space `E_s` is the identity. -/
theorem condExp_unit (s : ℝ) (F : Unit → ℝ) : (Measure.dirac ())[F | unitFilt s] = F :=
  condExp_of_stronglyMeasurable (unitFilt.le s) StronglyMeasurable.of_subsingleton_dom
    Integrable.of_finite

/-- Cochrane (2023), A1 §1.6, p. 567: almost sure equality on the one-point space is equality. -/
theorem ae_unit {f g : Unit → ℝ} : f =ᵐ[Measure.dirac ()] g ↔ f () = g () :=
  ae_dirac_iff (MeasurableSet.of_discrete)

/-- Cochrane (2023), A1 §1.6, p. 567: the integral on the one-point space is evaluation.
Mathlib `integral_dirac`. -/
theorem integral_unit (f : Unit → ℝ) : ∫ ω, f ω ∂Measure.dirac () = f () :=
  integral_dirac f ()

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: `ContinuousTime.money_printing_iff` recovered
from the stochastic (1.33).** For globally `C¹` deterministic paths with `N' = −iN`, `N > 0`,
`P > 0`, `dM = iB − Ps − dB`, `i`, `dB`, `dM` continuous and `N P(s + dM/P)` integrable on
`(t, ∞)`: `N_TB_T → 0` iff `B_t/P_t = ∫_t^∞ (N_τP_τ/(N_tP_t))(s_τ + dM_τ/P_τ) dτ`. Proof: the
model `c1Model` on the one-point space and
`TidyR7MonetarismValuation.MonetaryModel.valuation_1_33`. -/
theorem money_printing_recovered {N B M P s i dB dM : ℝ → ℝ} {t : ℝ}
    (hN : ∀ τ, HasDerivAt N (-(i τ) * N τ) τ) (hNpos : ∀ τ, 0 < N τ)
    (hB : ∀ τ, HasDerivAt B (dB τ) τ) (hM : ∀ τ, HasDerivAt M (dM τ) τ) (hP : ∀ τ, 0 < P τ)
    (hflow : ∀ τ, dM τ = i τ * B τ - P τ * s τ - dB τ) (hic : Continuous i)
    (hdBc : Continuous dB) (hdMc : Continuous dM)
    (hint : IntegrableOn (fun τ => N τ * P τ * (s τ + dM τ / P τ)) (Set.Ioi t)) :
    Tendsto (fun T => N T * B T) atTop (𝓝 0) ↔
      B t / P t = ∫ τ in Set.Ioi t, N τ * P τ / (N t * P t) * (s τ + dM τ / P τ) := by
  have hfc : Continuous fun r => i r * B r - P r * s r :=
    (hdBc.add hdMc).congr fun r => by simp only [Pi.add_apply]; rw [hflow r]; ring
  have hm := c1Model (μ := Measure.dirac ()) (𝓕 := unitFilt) (n := fun u _ => N u)
    (B := fun u _ => B u) (M := fun u _ => M u) (Pr := fun u _ => P u) (sp := fun u _ => s u)
    (i := fun u _ => i u) (im := fun _ _ => 0) (dM := fun u _ => dM u)
    (fun _ r => (hN r).congr_deriv (by ring)) (fun u _ => hNpos u) (fun _ r => hM r)
    (fun _ r => (hB r).congr_deriv (by rw [hflow r]; ring)) (fun u _ => hP u) (fun _ => hic)
    (fun _ => hdMc) (fun _ => hfc.congr fun r => by ring)
    (fun _ => StronglyMeasurable.of_subsingleton_dom)
    (fun _ => StronglyMeasurable.of_subsingleton_dom)
    (fun _ => StronglyMeasurable.of_subsingleton_dom)
    (fun _ => StronglyMeasurable.of_subsingleton_dom)
  have hP' : ∀ (u : ℝ) (_ : Unit), 0 < P u := fun u _ => hP u
  have hpc : Continuous fun r => P r * s r :=
    (hic.mul (TidyR7ProductStepCases.continuous_of_hasDerivAt hB)).sub hfc |>.congr
      fun r => by simp only [Pi.mul_apply, Pi.sub_apply]; ring
  have hnc : Continuous N := TidyR7ProductStepCases.continuous_of_hasDerivAt hN
  have hint' : IntegrableOn (fun τ => N τ * (P τ * s τ + dM τ)) (Set.Ioi t) :=
    hint.congr_fun (fun τ _ => by field_simp [(hP τ).ne']) measurableSet_Ioi
  set Gv := ∫ τ in Set.Ioi t, N τ * (P τ * s τ + dM τ) with hGv
  have hconv : Tendsto (fun T => ∫ ω, |flow133 (fun u (_ : Unit) => N u * P u) (fun u _ => P u)
      (fun u _ => M u) (fun u _ => s u) t T ω - (fun _ => Gv) ω| ∂Measure.dirac ())
      atTop (𝓝 0) := by
    have hI := intervalIntegral_tendsto_integral_Ioi t hint' tendsto_id
    have h2 : Tendsto (fun T => |(∫ τ in t..T, N τ * (P τ * s τ + dM τ)) - Gv|) atTop (𝓝 0) := by
      have := (hI.sub_const Gv).abs
      rwa [sub_self, abs_zero] at this
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop t] with T hT
    rw [integral_unit, flow133_C1 (n := fun u _ => N u) (dM := fun u _ => dM u) hP'
      (fun _ => hnc) (fun _ r => hM r) (fun _ => hdMc) (fun _ => hpc) hT ()]
  have h := MonetaryModel.valuation_1_33 hm (fun _ _ => rfl) (s := t)
    (fun _ _ => ⟨Integrable.of_finite, Integrable.of_finite, fun _ _ _ _ _ => Integrable.of_finite⟩)
    (fun _ _ => Integrable.of_finite) (G := fun _ => Gv) Integrable.of_finite hconv
  simp only [disc_mul hP', condExp_unit, integral_unit, ae_unit] at h
  have hR : ∫ τ in Set.Ioi t, N τ * P τ / (N t * P t) * (s τ + dM τ / P τ) = Gv / (N t * P t) := by
    rw [hGv, ← integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
    field_simp [(hP τ).ne']
  have e : B t / P t = Gv / (N t * P t) ↔ N t * B t = Gv := by
    rw [div_eq_div_iff (hP t).ne' (mul_pos (hNpos t) (hP t)).ne']
    constructor
    · intro hh
      refine mul_right_cancel₀ (hP t).ne' ?_
      rw [← hh]
      ring
    · intro hh
      rw [← hh]
      ring
  rw [hR, e, h, tendsto_zero_iff_norm_tendsto_zero]
  simp only [Real.norm_eq_abs]

/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567: `ContinuousTime.money_interest_iff` recovered
from the stochastic (1.34).** For globally `C¹` deterministic paths with `N' = −iN`, `N > 0`,
`P > 0`, `dM = iB + i^mM − Ps − dB`, `i`, `dB`, `dM` continuous and
`N P(s + (i − i^m)M/P)` integrable on `(t, ∞)`: `N_T(M_T + B_T) → 0` iff
`(M_t + B_t)/P_t = ∫_t^∞ (N_τP_τ/(N_tP_t))(s_τ + (i_τ − i^m_τ)M_τ/P_τ) dτ`. Proof: `c1Model` on
the one-point space and `TidyR7MonetarismValuation.MonetaryModel.valuation_1_34`. -/
theorem money_interest_recovered {N B M P s i im dB dM : ℝ → ℝ} {t : ℝ}
    (hN : ∀ τ, HasDerivAt N (-(i τ) * N τ) τ) (hNpos : ∀ τ, 0 < N τ)
    (hB : ∀ τ, HasDerivAt B (dB τ) τ) (hM : ∀ τ, HasDerivAt M (dM τ) τ) (hP : ∀ τ, 0 < P τ)
    (hflow : ∀ τ, dM τ = i τ * B τ + im τ * M τ - P τ * s τ - dB τ) (hic : Continuous i)
    (hdBc : Continuous dB) (hdMc : Continuous dM)
    (hint : IntegrableOn (fun τ => N τ * P τ * (s τ + (i τ - im τ) * M τ / P τ)) (Set.Ioi t)) :
    Tendsto (fun T => N T * (M T + B T)) atTop (𝓝 0) ↔
      (M t + B t) / P t =
        ∫ τ in Set.Ioi t, N τ * P τ / (N t * P t) * (s τ + (i τ - im τ) * M τ / P τ) := by
  have hfc : Continuous fun r => i r * B r + im r * M r - P r * s r :=
    (hdBc.add hdMc).congr fun r => by simp only [Pi.add_apply]; rw [hflow r]; ring
  have hm := c1Model (μ := Measure.dirac ()) (𝓕 := unitFilt) (n := fun u _ => N u)
    (B := fun u _ => B u) (M := fun u _ => M u) (Pr := fun u _ => P u) (sp := fun u _ => s u)
    (i := fun u _ => i u) (im := fun u _ => im u) (dM := fun u _ => dM u)
    (fun _ r => (hN r).congr_deriv (by ring)) (fun u _ => hNpos u) (fun _ r => hM r)
    (fun _ r => (hB r).congr_deriv (by rw [hflow r]; ring)) (fun u _ => hP u) (fun _ => hic)
    (fun _ => hdMc) (fun _ => hfc)
    (fun _ => StronglyMeasurable.of_subsingleton_dom)
    (fun _ => StronglyMeasurable.of_subsingleton_dom)
    (fun _ => StronglyMeasurable.of_subsingleton_dom)
    (fun _ => StronglyMeasurable.of_subsingleton_dom)
  have hP' : ∀ (u : ℝ) (_ : Unit), 0 < P u := fun u _ => hP u
  have hint' : IntegrableOn (fun τ => N τ * P τ * s τ + (i τ - im τ) * N τ * M τ)
      (Set.Ioi t) :=
    hint.congr_fun (fun τ _ => by field_simp [(hP τ).ne']) measurableSet_Ioi
  set Gv := ∫ τ in Set.Ioi t, (N τ * P τ * s τ + (i τ - im τ) * N τ * M τ) with hGv
  have hconv : Tendsto (fun T => ∫ ω, |flow134 (fun u (_ : Unit) => N u * P u) (fun u _ => P u)
      (fun u _ => M u) (fun u _ => i u) (fun u _ => im u) (fun u _ => s u) t T ω -
        (fun _ => Gv) ω| ∂Measure.dirac ()) atTop (𝓝 0) := by
    have hI := intervalIntegral_tendsto_integral_Ioi t hint' tendsto_id
    have h2 : Tendsto (fun T => |(∫ τ in t..T, (N τ * P τ * s τ + (i τ - im τ) * N τ * M τ)) -
        Gv|) atTop (𝓝 0) := by
      have := (hI.sub_const Gv).abs
      rwa [sub_self, abs_zero] at this
    refine h2.congr' (Eventually.of_forall fun T => ?_)
    simp only [integral_unit, flow134, disc_mul hP']
  have h := MonetaryModel.valuation_1_34 hm (s := t)
    (fun _ _ _ =>
      ⟨Integrable.of_finite, Integrable.of_finite, fun _ _ _ _ _ => Integrable.of_finite⟩)
    (fun _ => Integrable.of_finite) (G := fun _ => Gv) Integrable.of_finite hconv
  simp only [disc_mul hP', condExp_unit, integral_unit, ae_unit, addProc] at h
  have hR : ∫ τ in Set.Ioi t, N τ * P τ / (N t * P t) * (s τ + (i τ - im τ) * M τ / P τ) =
      Gv / (N t * P t) := by
    rw [hGv, ← integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
    field_simp [(hP τ).ne']
  have e : (M t + B t) / P t = Gv / (N t * P t) ↔ N t * (B t + M t) = Gv := by
    rw [div_eq_div_iff (hP t).ne' (mul_pos (hNpos t) (hP t)).ne']
    constructor
    · intro hh
      refine mul_right_cancel₀ (hP t).ne' ?_
      rw [← hh]
      ring
    · intro hh
      rw [← hh]
      ring
  rw [hR, e, h, tendsto_zero_iff_norm_tendsto_zero]
  simp only [Real.norm_eq_abs, add_comm (M _)]

/-! ## The `Δ`-grid -/

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the `Δ`-grid increment discounts the period flow
by `E_k[n_{k+1}]`.** With the grid rate `(1 + i_kΔ)E_k[n_{k+1}] = n_k`, the right side of
`TidyR6StochasticDrift.incr_1_32`, `−n_k(P_ks_kΔ + ΔM_k)/(1 + i_kΔ)`, equals
`−E_k[n_{k+1}](P_ks_kΔ + ΔM_k)`. -/
theorem grid_1_32_eq {Δ n Pk sk dMk ik Enk1 : ℝ} (hi : 1 + ik * Δ ≠ 0)
    (hrate : (1 + ik * Δ) * Enk1 = n) :
    -(n * (Pk * sk * Δ + dMk) / (1 + ik * Δ)) = -(Enk1 * (Pk * sk * Δ + dMk)) := by
  have e : Enk1 = n / (1 + ik * Δ) := by rw [eq_div_iff hi]; linarith
  rw [e]
  ring

/-- Cochrane (2023), A1 §1.6, p. 567: `−(aΔ/(1 + iΔ))/Δ → −a` as `Δ → 0`, `Δ ≠ 0`.
Generalises `TidyR6StochasticDrift.rate_increment_tendsto`. -/
theorem tendsto_per_unit (a ik : ℝ) :
    Tendsto (fun Δ : ℝ => -(a * Δ / (1 + ik * Δ)) / Δ) (𝓝[≠] 0) (𝓝 (-a)) := by
  have hden : Tendsto (fun Δ : ℝ => 1 + ik * Δ) (𝓝 0) (𝓝 (1 + ik * 0)) :=
    (continuous_const.add (continuous_const.mul continuous_id)).tendsto 0
  simp only [mul_zero, add_zero] at hden
  have hc : Tendsto (fun Δ : ℝ => -a / (1 + ik * Δ)) (𝓝 0) (𝓝 (-a)) := by
    have := (tendsto_const_nhds (x := -a)).div hden one_ne_zero
    rwa [div_one] at this
  refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with Δ hΔ
  have hΔ' : Δ ≠ 0 := hΔ
  by_cases hD : 1 + ik * Δ = 0
  · simp [hD]
  · field_simp

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the `Δ`-grid and the continuous-time drift.** With
`ΔM = mΔ`, the increment of `TidyR6StochasticDrift.incr_1_32` per unit time,
`−n(PsΔ + mΔ)/((1 + iΔ)Δ)`, tends to `−n(Ps + m)` as `Δ → 0`: the drift of `nB` in
`TidyR7MonetarismModel.MonetaryModel.hasDrift_1_32_ac` (`i^m = 0`, `Λs = nPs`) and of
`TidyR6StochasticDrift.drift_1_32_fv`. -/
theorem grid_1_32_rate (n Pk sk m ik : ℝ) :
    Tendsto (fun Δ : ℝ => -(n * (Pk * sk * Δ + m * Δ) / (1 + ik * Δ)) / Δ) (𝓝[≠] 0)
      (𝓝 (-(n * (Pk * sk + m)))) := by
  have e : (fun Δ : ℝ => -(n * (Pk * sk * Δ + m * Δ) / (1 + ik * Δ)) / Δ) =
      fun Δ => -(n * (Pk * sk + m) * Δ / (1 + ik * Δ)) / Δ := funext fun Δ => by ring
  rw [e]
  exact tendsto_per_unit _ ik

/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567: the `Δ`-grid and the continuous-time drift.** The
increment of `TidyR6StochasticDrift.incr_1_34` per unit time,
`−n(Ps + (i − i^m)M)Δ/((1 + iΔ)Δ)`, tends to `−n(Ps + (i − i^m)M)` as `Δ → 0`: the drift of
`n(B + M)` in `TidyR7MonetarismModel.MonetaryModel.hasDrift_1_34` (`Λs = nPs`). -/
theorem grid_1_34_rate (n Pk sk Mk ik imk : ℝ) :
    Tendsto (fun Δ : ℝ => -(n * (Pk * sk + (ik - imk) * Mk) * Δ / (1 + ik * Δ)) / Δ) (𝓝[≠] 0)
      (𝓝 (-(n * (Pk * sk + (ik - imk) * Mk)))) :=
  tendsto_per_unit _ ik

end Cochrane.Monetarism.TidyR7MonetarismLinks
