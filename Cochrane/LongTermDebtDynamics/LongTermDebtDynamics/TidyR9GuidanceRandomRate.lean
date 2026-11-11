/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR7GuidanceItoValuation
import LongTermDebtDynamics.TidyR9ItoFormulaVariants

/-!
# Forward guidance with a continuous-valued random rate after the news date

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §A1.2.1,
pp. 559–561 (the continuous-time valuation equation and the forward-guidance formula of
p. 561), under uncertainty, with a short rate after the news date `T` that is a bounded,
measurable random process `i_u` (e.g. an Itô process with continuous values), instead
of the finitely-valued, piecewise-known rates of `TidyR7GuidanceSDF.SDFPiece`.

## Setting

`RateSDF P 𝓕 W Λ H i r T M`: on `[0, T]` the nominal discount factor solves
`dΛ = −rΛ dt + H dW` with the known rate `r` (an `SDFPiece`), `Λ_T` is known at `T`, and from
`T` on `Λ_u = Λ_T exp(−∫_T^u i_v dv)` a.s., with `(u, ω) ↦ i_u(ω)` jointly measurable and
`0 ≤ i ≤ M`. By Itô's formula for the exponential (`TidyR9ItoFormulaVariants.itoProcess_exp`)
the factor `exp(−∫_T^u i)` is an Itô process with drift `−i exp(−∫_T^u i)` and no diffusion
when `i` is an admissible integrand with continuous paths (`itoProcess_rateDisc`): `i` is the
short rate, `dΛ = −iΛ dt`.

## Main results

* `condExp_bond_rate`, `bondPrice_rate`: **the bond prices at the news date are
  `Q_T^{(T+j)} = E_T[exp(−∫_T^{T+j} i)]`** (not the book's `e^{−ij}`).
* `condExp_debtValue_rate`: `E_0 ∫_0^∞ ϖe^{−ϖj}Λ_j dj = E_0[e^{rT}Λ_T · rateValue]`, where
  `rateValue = ∫_0^∞ ϖe^{−ϖj} rateDisc_j dj` is the pathwise value with the realised rate.
* `random_rate_jump`: **`P_0/P_0' − 1 = E_0[e^{rT}Λ_T · rateJump]/Λ_0`**,
  `rateJump = rateValue·(r+ϖ)/ϖ − 1`; generalises `TidyR7GuidanceItoValuation.random_jump_ito`
  from finitely many values to a continuous-valued rate.
* Relation to the book: `deterministic_rate_jump` (a deterministic rate path: the jump is the
  deterministic `rateJump`, state by state) and `constant_rate_jump` (**the book's formula
  verbatim** for a constant `i`, via `rateJump_const`); `random_rate_jump_decomp` (the jump is
  `E_0[rateJump]` plus the covariance term `(E_0[ZJ] − E_0[Z]E_0[J])/Λ_0`, `Z = e^{rT}Λ_T`);
  `integral_rateValue_ge` (**Jensen**: `E[rateValue] ≥ rateValue` at the mean rate path,
  strictly as soon as `∫_T^{j₀} i` is not a.s. equal to its mean for some `j₀ > T`).
-/

namespace Cochrane.LongTermDebtDynamics.TidyR9GuidanceRandomRate

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.LongTermDebtDynamics.TidyR7StieltjesSums
  Cochrane.LongTermDebtDynamics.TidyR7BrownianTools Cochrane.LongTermDebtDynamics.TidyR7BrownianQV
  Cochrane.LongTermDebtDynamics.TidyR7ItoL2 Cochrane.LongTermDebtDynamics.TidyR7ItoIntegral
  Cochrane.LongTermDebtDynamics.TidyR7ItoBridge Cochrane.LongTermDebtDynamics.TidyR7ItoProcess
  Cochrane.LongTermDebtDynamics.TidyR9ItoFormula
  Cochrane.LongTermDebtDynamics.TidyR9ItoFormulaVariants
  Cochrane.LongTermDebtDynamics.TidyR7GuidanceSDF
  Cochrane.LongTermDebtDynamics.TidyR7GuidanceItoValuation
  Cochrane.LongTermDebtDynamics.ForwardGuidance
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → ℝ}

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the pathwise discount to maturity `j`**
with the rate `r` until `T` and the random rate `i` after:
`exp(−(r min(j, T) + ∫_T^{max(j,T)} i_v dv))`. For a constant `i` it is the book's
`exp(−(r min(j,T) + i max(j−T, 0)))` (`rateDisc_const`). -/
noncomputable def rateDisc (r T : ℝ) (i : ℝ → Ω → ℝ) (j : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-(r * min j T + ∫ v in T..max j T, i v ω))

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the pathwise value of the debt per unit**,
`∫_0^∞ ϖe^{−ϖj} rateDisc_j dj` (the book's `ϖ ∫_0^∞ Q_0^{(j)} e^{−ϖj} dj` along the realised rate
path; `cfgValue` for a constant rate, `rateValue_const`). -/
noncomputable def rateValue (r ϖ T : ℝ) (i : ℝ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∫ j in Set.Ioi (0 : ℝ), ϖ * Real.exp (-ϖ * j) * rateDisc r T i j ω

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the pathwise forward-guidance jump**,
`rateValue·(r + ϖ)/ϖ − 1` (`cfgJump` for a constant rate, `rateJump_const`). -/
noncomputable def rateJump (r ϖ T : ℝ) (i : ℝ → Ω → ℝ) (ω : Ω) : ℝ :=
  rateValue r ϖ T i ω * ((r + ϖ) / ϖ) - 1

variable (P 𝓕 W) (Λ H i : ℝ → Ω → ℝ) (r T M : ℝ)

/-- **Cochrane (2023), Online Appendix §A1.2.1, pp. 559–561 (under uncertainty): the nominal
discount factor with a random rate after the news date.** On `[0, T]`,
`dΛ = −rΛ dt + H dW` with the known rate `r` (an `SDFPiece`); `Λ_T` is known at `T`; from `T`
on, `Λ_u = Λ_T exp(−∫_T^u i_v dv)` a.s., with `i` jointly measurable and `0 ≤ i ≤ M`. -/
structure RateSDF where
  pre : ∃ C, SDFPiece P 𝓕 W Λ H (fun _ => r) 0 T C
  adaptedT : StronglyMeasurable[𝓕 T] (Λ T)
  post : ∀ u, T ≤ u → Λ u =ᵐ[P] fun ω => Λ T ω * Real.exp (-∫ v in T..u, i v ω)
  rate_meas : Measurable (Function.uncurry i)
  rate_bound : ∀ u ω, 0 ≤ i u ω ∧ i u ω ≤ M

variable {P 𝓕 W Λ H i r T M}

/-! ### The rate integral -/

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: a measurable rate bounded by `M ≥ 0` is
integrable along each path on every interval. -/
theorem intervalIntegrable_rate (hi : Measurable (Function.uncurry i))
    (hb : ∀ u ω, 0 ≤ i u ω ∧ i u ω ≤ M) (ω : Ω) (a b : ℝ) :
    IntervalIntegrable (fun v => i v ω) volume a b := by
  have hm : Measurable fun v => i v ω := hi.comp (measurable_id.prodMk measurable_const)
  refine (intervalIntegrable_const (c := M)).mono_fun hm.aestronglyMeasurable
    (ae_of_all _ fun v => ?_)
  have h := hb v ω
  change ‖i v ω‖ ≤ |M|
  rw [Real.norm_eq_abs, abs_of_nonneg h.1, abs_of_nonneg (h.1.trans h.2)]
  exact h.2

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the integrated rate is continuous in the
maturity, path by path. -/
theorem continuous_integral_rate (hi : Measurable (Function.uncurry i))
    (hb : ∀ u ω, 0 ≤ i u ω ∧ i u ω ≤ M) (ω : Ω) (T : ℝ) :
    Continuous fun u => ∫ v in T..u, i v ω :=
  intervalIntegral.continuous_primitive (intervalIntegrable_rate hi hb ω) T

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the integrated rate is measurable in the
state (Mathlib `StronglyMeasurable.integral_prod_left`). -/
theorem measurable_integral_rate (hi : Measurable (Function.uncurry i)) (T u : ℝ) :
    Measurable fun ω => ∫ v in T..u, i v ω := by
  have h1 := (hi.stronglyMeasurable).integral_prod_left (μ := volume.restrict (Set.Ioc T u))
  have h2 := (hi.stronglyMeasurable).integral_prod_left (μ := volume.restrict (Set.Ioc u T))
  exact h1.measurable.sub h2.measurable

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: `0 ≤ ∫_T^u i ≤ M(u − T)` for `T ≤ u`. -/
theorem integral_rate_mem (hi : Measurable (Function.uncurry i))
    (hb : ∀ u ω, 0 ≤ i u ω ∧ i u ω ≤ M) (ω : Ω) {T u : ℝ} (hTu : T ≤ u) :
    0 ≤ ∫ v in T..u, i v ω ∧ ∫ v in T..u, i v ω ≤ M * (u - T) := by
  refine ⟨intervalIntegral.integral_nonneg hTu fun v _ => (hb v ω).1, ?_⟩
  have h := intervalIntegral.integral_mono_on hTu (intervalIntegrable_rate hi hb ω T u)
    (intervalIntegrable_const (c := M)) fun v _ => (hb v ω).2
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  linarith

/-! ### The pathwise discount and value -/

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: before the news date the discount is the
known `e^{−rj}`. -/
theorem rateDisc_of_le (r : ℝ) {T j : ℝ} (i : ℝ → Ω → ℝ) (hjT : j ≤ T) (ω : Ω) :
    rateDisc r T i j ω = Real.exp (-r * j) := by
  rw [rateDisc, min_eq_left hjT, max_eq_right hjT, intervalIntegral.integral_same, add_zero,
    neg_mul]

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: after the news date the discount is
`e^{−rT} exp(−∫_T^j i)`. -/
theorem rateDisc_of_ge (r : ℝ) {T j : ℝ} (i : ℝ → Ω → ℝ) (hjT : T ≤ j) (ω : Ω) :
    rateDisc r T i j ω = Real.exp (-r * T) * Real.exp (-∫ v in T..j, i v ω) := by
  rw [rateDisc, min_eq_right hjT, max_eq_left hjT, ← Real.exp_add]
  congr 1
  ring

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: `0 < rateDisc ≤ 1` at maturities
`j ≥ 0` (`r ≥ 0`, `T ≥ 0`, `i ≥ 0`). -/
theorem rateDisc_mem (hi : Measurable (Function.uncurry i))
    (hb : ∀ u ω, 0 ≤ i u ω ∧ i u ω ≤ M) {r T j : ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T) (hj : 0 ≤ j)
    (ω : Ω) : 0 < rateDisc r T i j ω ∧ rateDisc r T i j ω ≤ 1 := by
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.2 ?_⟩
  have h1 := (integral_rate_mem hi hb ω (le_max_right j T)).1
  have h2 : 0 ≤ r * min j T := mul_nonneg hr (le_min hj hT)
  linarith

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the pathwise discount is jointly
measurable in maturity and state. -/
theorem measurable_rateDisc (hi : Measurable (Function.uncurry i))
    (hb : ∀ u ω, 0 ≤ i u ω ∧ i u ω ≤ M) (r T : ℝ) :
    Measurable (Function.uncurry (rateDisc r T i)) := by
  refine measurable_uncurry_of_continuous_of_measurable (fun ω => ?_) (fun j => ?_)
  · exact Real.continuous_exp.comp (((continuous_const.mul (continuous_id.min continuous_const)).add
      ((continuous_integral_rate hi hb ω T).comp (continuous_id.max continuous_const))).neg)
  · exact Real.measurable_exp.comp ((measurable_const.add
      (measurable_integral_rate hi T (max j T))).neg)

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the maturity density `ϖe^{−ϖj}` is
integrable on `(0, ∞)` (`ϖ > 0`).
Mathlib `integrableOn_exp_mul_Ioi`. -/
theorem integrableOn_weight {ϖ : ℝ} (hϖ : 0 < ϖ) :
    IntegrableOn (fun j : ℝ => ϖ * Real.exp (-ϖ * j)) (Set.Ioi 0) :=
  (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul ϖ

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: `∫_0^∞ ϖe^{−ϖj} dj = 1` (`ϖ > 0`).
Mathlib `integral_exp_mul_Ioi`. -/
theorem integral_weight {ϖ : ℝ} (hϖ : 0 < ϖ) :
    ∫ j in Set.Ioi (0 : ℝ), ϖ * Real.exp (-ϖ * j) = 1 := by
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0]
  field_simp
  simp

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the valuation integrand along a path is
integrable on `(0, ∞)`. -/
theorem integrableOn_rateDisc (hi : Measurable (Function.uncurry i))
    (hb : ∀ u ω, 0 ≤ i u ω ∧ i u ω ≤ M) {r T ϖ : ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T) (hϖ : 0 < ϖ)
    (ω : Ω) :
    IntegrableOn (fun j => ϖ * Real.exp (-ϖ * j) * rateDisc r T i j ω) (Set.Ioi 0) := by
  have hm : Measurable fun j => rateDisc r T i j ω :=
    (measurable_rateDisc hi hb r T).comp (measurable_id.prodMk measurable_const)
  refine (integrableOn_weight hϖ).mono' (((by fun_prop : Measurable fun j : ℝ =>
    ϖ * Real.exp (-ϖ * j)).mul hm).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with j hj
  have h := rateDisc_mem hi hb hr hT (le_of_lt hj) ω (r := r)
  have hw : 0 < ϖ * Real.exp (-ϖ * j) := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hw, abs_of_pos h.1]
  exact mul_le_of_le_one_right hw.le h.2

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: `0 ≤ rateValue ≤ 1`. -/
theorem rateValue_mem (hi : Measurable (Function.uncurry i))
    (hb : ∀ u ω, 0 ≤ i u ω ∧ i u ω ≤ M) {r T ϖ : ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T) (hϖ : 0 < ϖ)
    (ω : Ω) : 0 ≤ rateValue r ϖ T i ω ∧ rateValue r ϖ T i ω ≤ 1 := by
  refine ⟨setIntegral_nonneg measurableSet_Ioi fun j hj => ?_, ?_⟩
  · have h := rateDisc_mem hi hb hr hT (le_of_lt hj) ω (r := r)
    exact mul_nonneg (by positivity) h.1.le
  · rw [← integral_weight hϖ, rateValue]
    refine setIntegral_mono_on (integrableOn_rateDisc hi hb hr hT hϖ ω) (integrableOn_weight hϖ)
      measurableSet_Ioi fun j hj => ?_
    have h := rateDisc_mem hi hb hr hT (le_of_lt hj) ω (r := r)
    exact mul_le_of_le_one_right (by positivity) h.2

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the pathwise value is measurable in the
state. -/
theorem measurable_rateValue (hi : Measurable (Function.uncurry i))
    (hb : ∀ u ω, 0 ≤ i u ω ∧ i u ω ≤ M) (r ϖ T : ℝ) :
    Measurable (rateValue r ϖ T i) := by
  have hm : Measurable fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1) * rateDisc r T i p.1 p.2 :=
    (by fun_prop : Measurable fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1)).mul
      (measurable_rateDisc hi hb r T)
  exact (hm.stronglyMeasurable.integral_prod_left
    (f := fun j ω => ϖ * Real.exp (-ϖ * j) * rateDisc r T i j ω)
    (μ := volume.restrict (Set.Ioi 0))).measurable

/-! ### Valuation -/

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561 (under uncertainty): bond prices at the
news date with a random rate.** For `j ≥ 0`,
`E[Λ_{T+j} | 𝓕_T] = Λ_T · E[exp(−∫_T^{T+j} i) | 𝓕_T]` a.s.
Generalises `TidyR7GuidanceItoValuation.condExp_guidance` (constant rate after `T`). -/
theorem condExp_bond_rate (hB : IsPreBrownianReal W P) (hT : 0 ≤ T)
    (hΛ : RateSDF P 𝓕 W Λ H i r T M) {j : ℝ} (hj : 0 ≤ j) :
    P[Λ (T + j) | 𝓕 T] =ᵐ[P]
      fun ω => Λ T ω * P[fun ω => Real.exp (-∫ v in T..T + j, i v ω) | 𝓕 T] ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨C, hpre⟩ := hΛ.pre
  have hΛT : Integrable (Λ T) P := hpre.integ_at T ⟨hT, le_rfl⟩
  set g : Ω → ℝ := fun ω => Real.exp (-∫ v in T..T + j, i v ω) with hgdef
  have hgm : Measurable g :=
    Real.measurable_exp.comp (measurable_integral_rate hΛ.rate_meas T (T + j)).neg
  have hgb : ∀ ω, ‖g ω‖ ≤ 1 := fun ω => by
    have h := (integral_rate_mem hΛ.rate_meas hΛ.rate_bound ω (T := T) (u := T + j)
      (le_add_of_nonneg_right hj)).1
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by linarith)
  have hg : Integrable g P :=
    (integrable_const (1 : ℝ)).mono' hgm.aestronglyMeasurable (ae_of_all _ hgb)
  have hfg : Integrable (Λ T * g) P := by
    have h := hΛT.bdd_mul (c := 1) hgm.aestronglyMeasurable (ae_of_all _ hgb)
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only [Pi.mul_apply]
    ring
  have h1 : P[Λ (T + j) | 𝓕 T] =ᵐ[P] P[Λ T * g | 𝓕 T] :=
    condExp_congr_ae (hΛ.post (T + j) (le_add_of_nonneg_right hj))
  exact h1.trans (condExp_mul_of_stronglyMeasurable_left hΛ.adaptedT hfg hg)

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561 (under uncertainty): the zero-coupon
price at the news date is `Q_T^{(T+j)} = E_T[exp(−∫_T^{T+j} i)]`**, a.s. where `Λ_T ≠ 0`;
for a random rate this is not `e^{−E_T[∫ i]}` (Jensen, `integral_rateValue_ge`).
Generalises `TidyR7GuidanceItoValuation.bondPrice_guidance`. -/
theorem bondPrice_rate (hB : IsPreBrownianReal W P) (hT : 0 ≤ T)
    (hΛ : RateSDF P 𝓕 W Λ H i r T M) {j : ℝ} (hj : 0 ≤ j) :
    ∀ᵐ ω ∂P, Λ T ω ≠ 0 → P[Λ (T + j) | 𝓕 T] ω / Λ T ω =
      P[fun ω => Real.exp (-∫ v in T..T + j, i v ω) | 𝓕 T] ω := by
  filter_upwards [condExp_bond_rate hB hT hΛ hj] with ω hω h0
  rw [hω]
  field_simp

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561 (under uncertainty): the value of the
debt with a random rate after the news date.** With `r ≥ 0`, `ϖ > 0`, `T ≥ 0` and the debt
payoffs jointly integrable,
`E_0 ∫_0^∞ ϖe^{−ϖj}Λ_j dj = E_0[e^{rT}Λ_T · rateValue r ϖ T i]` a.s.: the pathwise value at the
realised rate path, weighted by the discount factor at the news date.
Generalises `TidyR7GuidanceItoValuation.condExp_debtValue_random` (finitely valued news rate). -/
theorem condExp_debtValue_rate (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hT : 0 ≤ T) (hr : 0 ≤ r) {ϖ : ℝ} (hϖ : 0 < ϖ)
    (hΛ : RateSDF P 𝓕 W Λ H i r T M)
    (hint : Integrable (fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1) * Λ p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod P)) :
    P[fun ω => ∫ j in Set.Ioi (0 : ℝ), ϖ * Real.exp (-ϖ * j) * Λ j ω | 𝓕 0] =ᵐ[P]
      P[fun ω => Real.exp (r * T) * Λ T ω * rateValue r ϖ T i ω | 𝓕 0] := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨C, hpre⟩ := hΛ.pre
  have hΛT : Integrable (Λ T) P := hpre.integ_at T ⟨hT, le_rfl⟩
  have hΛTm : Measurable (Λ T) := (hΛ.adaptedT.mono (𝓕.le T)).measurable
  have hVm := measurable_rateValue hΛ.rate_meas hΛ.rate_bound r ϖ T
  have hVb : ∀ ω, ‖rateValue r ϖ T i ω‖ ≤ 1 := fun ω => by
    have h := rateValue_mem hΛ.rate_meas hΛ.rate_bound hr hT hϖ ω
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2
  have hYint : Integrable (fun ω => Real.exp (r * T) * Λ T ω * rateValue r ϖ T i ω) P := by
    have h := (hΛT.const_mul (Real.exp (r * T))).bdd_mul (c := 1) hVm.aestronglyMeasurable
      (ae_of_all _ hVb)
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only
    ring
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le 0) hint.integral_prod_right
    (fun _ _ _ => integrable_condExp.integrableOn) (fun A hA _ => ?_)
    stronglyMeasurable_condExp.aestronglyMeasurable).symm
  have hA' : MeasurableSet A := 𝓕.le 0 A hA
  set G : ℝ → Ω → ℝ := fun j ω =>
    Real.exp (r * T) * Λ T ω * (ϖ * Real.exp (-ϖ * j) * rateDisc r T i j ω) with hG
  have hL : ∀ ω, Real.exp (r * T) * Λ T ω * rateValue r ϖ T i ω =
      ∫ j in Set.Ioi (0 : ℝ), G j ω := fun ω => by
    rw [rateValue, ← integral_const_mul]
  have hGint : Integrable (Function.uncurry G)
      ((volume.restrict (Set.Ioi 0)).prod (P.restrict A)) := by
    have hprod := (integrableOn_weight hϖ).mul_prod
      ((hΛT.abs.const_mul (Real.exp (r * T))).integrableOn (s := A))
    refine hprod.mono' ?_ ?_
    · exact ((measurable_const.mul (hΛTm.comp measurable_snd)).mul
        ((by fun_prop : Measurable fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1)).mul
          (measurable_rateDisc hΛ.rate_meas hΛ.rate_bound r T))).aestronglyMeasurable
    · have hfst := (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (ν := P.restrict A)).ae (ae_restrict_mem measurableSet_Ioi)
      filter_upwards [hfst] with p hp
      have h := rateDisc_mem hΛ.rate_meas hΛ.rate_bound hr hT (le_of_lt hp) p.2 (r := r)
      have hw : 0 < ϖ * Real.exp (-ϖ * p.1) := by positivity
      rw [Real.norm_eq_abs]
      change |Real.exp (r * T) * Λ T p.2 * (ϖ * Real.exp (-ϖ * p.1) * rateDisc r T i p.1 p.2)|
        ≤ ϖ * Real.exp (-ϖ * p.1) * (Real.exp (r * T) * |Λ T p.2|)
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_pos hw, abs_of_pos h.1]
      have h0 := abs_nonneg (Λ T p.2)
      have he := Real.exp_pos (r * T)
      calc Real.exp (r * T) * |Λ T p.2| * (ϖ * Real.exp (-ϖ * p.1) * rateDisc r T i p.1 p.2)
          ≤ Real.exp (r * T) * |Λ T p.2| * (ϖ * Real.exp (-ϖ * p.1) * 1) := by gcongr; exact h.2
        _ = _ := by ring
  rw [setIntegral_condExp (𝓕.le 0) hYint hA, setIntegral_congr_fun hA' (fun ω _ => hL ω),
    ← integral_integral_swap hGint,
    ← integral_integral_swap (integrable_restrict_prod
      (F := fun j ω => ϖ * Real.exp (-ϖ * j) * Λ j ω) hint A)]
  refine setIntegral_congr_fun measurableSet_Ioi fun j hj => ?_
  have hj0 : (0 : ℝ) ≤ j := le_of_lt hj
  rcases le_or_gt j T with hjT | hjT
  · have h1 := setIntegral_sdf hB hW h𝓕 le_rfl hpre hA (fun _ _ => rfl) ⟨hj0, hjT⟩
    have h2 := setIntegral_sdf hB hW h𝓕 le_rfl hpre hA (fun _ _ => rfl) ⟨hT, le_rfl⟩
    have e : ∀ ω, G j ω = (Real.exp (r * T) * (ϖ * Real.exp (-ϖ * j) * Real.exp (-r * j)))
        * Λ T ω := fun ω => by
      simp only [hG, rateDisc_of_le r i hjT]
      ring
    simp_rw [e]
    rw [sub_zero] at h1 h2
    rw [integral_const_mul, integral_const_mul, h1, h2]
    have e2 : Real.exp (r * T) * Real.exp (-r * T) = 1 := by
      rw [← Real.exp_add]; simp
    linear_combination (ϖ * Real.exp (-ϖ * j) * Real.exp (-r * j) * ∫ ω in A, Λ 0 ω ∂P) * e2
  · have e : ∀ᵐ ω ∂P, G j ω = ϖ * Real.exp (-ϖ * j) * Λ j ω := by
      filter_upwards [hΛ.post j hjT.le] with ω hω
      simp only [hG, rateDisc_of_ge r i hjT.le, hω]
      have e2 : Real.exp (r * T) * Real.exp (-r * T) = 1 := by
        rw [← Real.exp_add]; simp
      linear_combination (ϖ * Real.exp (-ϖ * j) * Λ T ω
        * Real.exp (-∫ v in T..j, i v ω)) * e2
    exact integral_congr_ae (ae_restrict_of_ae e)

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561 (under uncertainty): the weights of the
`T`-forward measure have conditional mean one, `E_0[e^{rT}Λ_T] = Λ_0` a.s. (the known rate on
`[0, T]`, `TidyR7GuidanceSDF.condExp_sdf_const`). -/
theorem condExp_forward_weight (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hT : 0 ≤ T) (hΛ : RateSDF P 𝓕 W Λ H i r T M) :
    P[fun ω => Real.exp (r * T) * Λ T ω | 𝓕 0] =ᵐ[P] Λ 0 := by
  obtain ⟨C, hpre⟩ := hΛ.pre
  have hpreT := condExp_sdf_const hB hW h𝓕 le_rfl hpre ⟨hT, le_rfl⟩
  have hlin := condExp_smul (μ := P) (Real.exp (r * T)) (Λ T) (𝓕 0)
  have e : (fun ω => Real.exp (r * T) * Λ T ω) = Real.exp (r * T) • Λ T := by
    funext ω
    simp [smul_eq_mul]
  rw [e]
  filter_upwards [hlin, hpreT] with ω l1 l2
  rw [l1, Pi.smul_apply, l2, smul_eq_mul, ← mul_assoc, ← Real.exp_add, sub_zero,
    show r * T + -r * T = 0 by ring, Real.exp_zero, one_mul]

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561, under uncertainty about the future
rate: the forward-guidance formula with a continuous-valued random rate.** As in
`TidyR7GuidanceItoValuation.random_jump_ito`, two economies with the same debt and surpluses:
`Λ` with the rate `r` until `T` and the random rate `i` after (`RateSDF`), `Λ'` with `r`
throughout. If the valuation equations hold, then a.s. where `Λ_0, Λ'_0 ≠ 0` and the present
value of surpluses is nonzero,
`P_0/P_0' − 1 = E_0[e^{rT}Λ_T · rateJump r ϖ T i]/Λ_0`: the pathwise jump at the realised rate
path, averaged under the `T`-forward measure (`r ≥ 0`, `ϖ > 0`, `T ≥ 0`). -/
theorem random_rate_jump (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hT : 0 ≤ T) (hr : 0 ≤ r) {ϖ : ℝ} (hϖ : 0 < ϖ)
    {Λ' H' K' s : ℝ → Ω → ℝ} {B0 P0 P0' : Ω → ℝ} (hΛ : RateSDF P 𝓕 W Λ H i r T M)
    (hint : Integrable (fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1) * Λ p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod P))
    (hΛ' : GuidanceSDF P 𝓕 W Λ' H' K' r (fun _ => r) T)
    (hint' : Integrable (fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1) * Λ' p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod P))
    (hP0 : ∀ ω, 0 < P0 ω) (hP0' : ∀ ω, 0 < P0' ω)
    (hval : ∀ᵐ ω ∂P, B0 ω / P0 ω * debtValue P 𝓕 Λ ϖ ω = pvSurplus P 𝓕 r s ω)
    (hval' : ∀ᵐ ω ∂P, B0 ω / P0' ω * debtValue P 𝓕 Λ' ϖ ω = pvSurplus P 𝓕 r s ω) :
    ∀ᵐ ω ∂P, Λ 0 ω ≠ 0 → Λ' 0 ω ≠ 0 → pvSurplus P 𝓕 r s ω ≠ 0 →
      P0 ω / P0' ω - 1 =
        P[fun ω => Real.exp (r * T) * Λ T ω * rateJump r ϖ T i ω | 𝓕 0] ω / Λ 0 ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hrv : 0 < r + ϖ := by linarith
  obtain ⟨C, hpre⟩ := hΛ.pre
  have hΛT : Integrable (Λ T) P := hpre.integ_at T ⟨hT, le_rfl⟩
  have hJm : Measurable (rateJump r ϖ T i) :=
    ((measurable_rateValue hΛ.rate_meas hΛ.rate_bound r ϖ T).mul_const _).sub_const _
  have hJb : ∀ ω, ‖rateJump r ϖ T i ω‖ ≤ (r + ϖ) / ϖ + 1 := fun ω => by
    have h := rateValue_mem hΛ.rate_meas hΛ.rate_bound hr hT hϖ ω
    have hk : 0 ≤ (r + ϖ) / ϖ := by positivity
    rw [Real.norm_eq_abs, rateJump, abs_le]
    constructor <;> nlinarith [mul_nonneg h.1 hk, mul_le_mul_of_nonneg_right h.2 hk]
  have hZint : Integrable (fun ω => Real.exp (r * T) * Λ T ω * rateJump r ϖ T i ω) P := by
    have h := (hΛT.const_mul (Real.exp (r * T))).bdd_mul (c := (r + ϖ) / ϖ + 1)
      hJm.aestronglyMeasurable (ae_of_all _ hJb)
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only
    ring
  have hΛTe : Integrable (fun ω => Real.exp (r * T) * Λ T ω) P := hΛT.const_mul _
  set k : ℝ := (r + ϖ) / ϖ with hk
  have hpt : (k • fun ω => Real.exp (r * T) * Λ T ω * rateValue r ϖ T i ω) =
      (fun ω => Real.exp (r * T) * Λ T ω * rateJump r ϖ T i ω)
        + fun ω => Real.exp (r * T) * Λ T ω := by
    funext ω
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, rateJump, hk]
    ring
  have hlin1 := condExp_smul (μ := P) k
    (fun ω => Real.exp (r * T) * Λ T ω * rateValue r ϖ T i ω) (𝓕 0)
  have hlin2 := condExp_add (m := 𝓕 0) hZint hΛTe
  have hV := condExp_debtValue_rate hB hW h𝓕 hT hr hϖ hΛ hint
  filter_upwards [hV, debtValue_guidance hB hW h𝓕 hT hΛ' hrv hrv hint', hval, hval', hlin1,
    hlin2, condExp_forward_weight hB hW h𝓕 hT hΛ] with ω e1 e2 v1 v2 l1 l2 l3 h0 h0' hS0
  rw [e2 h0', cfgValue_same r ϖ T hrv] at v2
  rw [debtValue, e1] at v1
  rw [hpt] at l1
  rw [l2, Pi.add_apply, l3] at l1
  rw [Pi.smul_apply, smul_eq_mul] at l1
  set Y := P[fun ω => Real.exp (r * T) * Λ T ω * rateValue r ϖ T i ω | 𝓕 0] ω with hY
  set Z := P[fun ω => Real.exp (r * T) * Λ T ω * rateJump r ϖ T i ω | 𝓕 0] ω with hZ
  have hB0 : B0 ω ≠ 0 := by
    intro hb
    rw [hb, zero_div, zero_mul] at v2
    exact hS0 v2.symm
  have hP := (hP0 ω).ne'
  have hP' := (hP0' ω).ne'
  have hrv' := hrv.ne'
  have hϖ' := hϖ.ne'
  rw [hk] at l1
  have heq : B0 ω * Y * (P0' ω * (r + ϖ)) = B0 ω * ϖ * (P0 ω * Λ 0 ω) := by
    have h := v1.trans v2.symm
    rw [div_mul_div_comm, div_mul_div_comm,
      div_eq_div_iff (mul_ne_zero hP h0) (mul_ne_zero hP' hrv')] at h
    linear_combination h
  have heq2 : Y * (P0' ω * (r + ϖ)) = ϖ * (P0 ω * Λ 0 ω) :=
    mul_left_cancel₀ hB0 (by linear_combination heq)
  have l1' : (r + ϖ) * Y = (Z + Λ 0 ω) * ϖ := by
    rw [div_mul_eq_mul_div, eq_div_iff hϖ'] at l1
    exact l1.symm
  rw [div_sub_one hP', div_eq_div_iff hP' h0]
  apply mul_left_cancel₀ hϖ'
  linear_combination (-1) * heq2 + P0' ω * l1'

/-! ### Relation to the book's formula -/

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: for a constant rate `i₀` after `T` the
pathwise discount is the book's `exp(−(r min(j,T) + i₀ max(j−T, 0)))`. -/
theorem rateDisc_const (r T i₀ j : ℝ) (ω : Ω) :
    rateDisc r T (fun _ _ => i₀) j ω = Real.exp (-(r * min j T + i₀ * max (j - T) 0)) := by
  rw [rateDisc, intervalIntegral.integral_const, smul_eq_mul, ← max_sub_sub_right, sub_self,
    mul_comm (max (j - T) 0) i₀]

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: for a constant rate the pathwise value is
the book's `cfgValue r i₀ ϖ T` (`ForwardGuidance.integral_cfg`). -/
theorem rateValue_const {r ϖ T i₀ : ℝ} (hrv : 0 < r + ϖ) (hiv : 0 < i₀ + ϖ) (hT : 0 ≤ T)
    (ω : Ω) : rateValue r ϖ T (fun _ _ => i₀) ω = cfgValue r i₀ ϖ T := by
  rw [rateValue, ← integral_cfg hrv hiv hT]
  refine setIntegral_congr_fun measurableSet_Ioi fun j _ => ?_
  rw [rateDisc_const, cfgIntegrand]

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: for a constant rate the pathwise jump is
the book's `cfgJump r i₀ ϖ T = e^{−(r+ϖ)T}((r+ϖ)/(i₀+ϖ) − 1)`. -/
theorem rateJump_const {r ϖ T i₀ : ℝ} (hϖ : 0 < ϖ) (hrv : 0 < r + ϖ) (hiv : 0 < i₀ + ϖ)
    (hT : 0 ≤ T) (ω : Ω) : rateJump r ϖ T (fun _ _ => i₀) ω = cfgJump r i₀ ϖ T := by
  rw [rateJump, rateValue_const hrv hiv hT, ← cfgJump_add_one T hϖ.ne' hrv.ne' hiv.ne']
  ring

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: a deterministic rate path after `T`.**
If the rate after `T` is a deterministic path `ι`, then, under the hypotheses of
`random_rate_jump`, `P_0/P_0' − 1 = rateJump r ϖ T ι` state by state: the book's valuation with
the announced path, whatever the diffusion of `Λ` before `T` and of the surpluses. -/
theorem deterministic_rate_jump (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hT : 0 ≤ T) (hr : 0 ≤ r) {ϖ : ℝ} (hϖ : 0 < ϖ) {ι : ℝ → ℝ}
    {Λ' H' K' s : ℝ → Ω → ℝ} {B0 P0 P0' : Ω → ℝ}
    (hΛ : RateSDF P 𝓕 W Λ H (fun v _ => ι v) r T M)
    (hint : Integrable (fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1) * Λ p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod P))
    (hΛ' : GuidanceSDF P 𝓕 W Λ' H' K' r (fun _ => r) T)
    (hint' : Integrable (fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1) * Λ' p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod P))
    (hP0 : ∀ ω, 0 < P0 ω) (hP0' : ∀ ω, 0 < P0' ω)
    (hval : ∀ᵐ ω ∂P, B0 ω / P0 ω * debtValue P 𝓕 Λ ϖ ω = pvSurplus P 𝓕 r s ω)
    (hval' : ∀ᵐ ω ∂P, B0 ω / P0' ω * debtValue P 𝓕 Λ' ϖ ω = pvSurplus P 𝓕 r s ω) :
    ∀ᵐ ω ∂P, Λ 0 ω ≠ 0 → Λ' 0 ω ≠ 0 → pvSurplus P 𝓕 r s ω ≠ 0 →
      P0 ω / P0' ω - 1 = rateJump r ϖ T (fun v _ => ι v) ω := by
  rcases isEmpty_or_nonempty Ω with hΩ | ⟨⟨ω₀⟩⟩
  · exact Filter.Eventually.of_forall fun ω => (hΩ.false ω).elim
  set J : ℝ := rateJump r ϖ T (fun v (_ : Ω) => ι v) ω₀ with hJ
  have hconst : ∀ ω, rateJump r ϖ T (fun v (_ : Ω) => ι v) ω = J := fun _ => rfl
  have e : (fun ω => Real.exp (r * T) * Λ T ω * rateJump r ϖ T (fun v _ => ι v) ω) =
      J • fun ω => Real.exp (r * T) * Λ T ω := by
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul, hconst ω]
    ring
  filter_upwards [random_rate_jump hB hW h𝓕 hT hr hϖ hΛ hint hΛ' hint' hP0 hP0' hval hval',
    condExp_smul (μ := P) J (fun ω => Real.exp (r * T) * Λ T ω) (𝓕 0),
    condExp_forward_weight hB hW h𝓕 hT hΛ] with ω h1 h2 h3 h0 h0' hS
  rw [h1 h0 h0' hS, e, h2, Pi.smul_apply, h3, smul_eq_mul, mul_div_assoc, div_self h0, mul_one,
    hconst ω]

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the book's formula verbatim.** With a
constant rate `i₀ ≥ 0` after `T` (a `RateSDF` with `i = i₀`), under the hypotheses of
`random_rate_jump`, `P_0/P_0' − 1 = e^{−(r+ϖ)T}((r+ϖ)/(i₀+ϖ) − 1)` (`ForwardGuidance.cfgJump`)
state by state.
Restates `TidyR7GuidanceItoValuation.guidance_jump_ito` in the `RateSDF` setting. -/
theorem constant_rate_jump (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hT : 0 ≤ T) (hr : 0 ≤ r) {ϖ : ℝ} (hϖ : 0 < ϖ) {i₀ : ℝ}
    (hi₀ : 0 ≤ i₀) {Λ' H' K' s : ℝ → Ω → ℝ} {B0 P0 P0' : Ω → ℝ}
    (hΛ : RateSDF P 𝓕 W Λ H (fun _ _ => i₀) r T M)
    (hint : Integrable (fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1) * Λ p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod P))
    (hΛ' : GuidanceSDF P 𝓕 W Λ' H' K' r (fun _ => r) T)
    (hint' : Integrable (fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1) * Λ' p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod P))
    (hP0 : ∀ ω, 0 < P0 ω) (hP0' : ∀ ω, 0 < P0' ω)
    (hval : ∀ᵐ ω ∂P, B0 ω / P0 ω * debtValue P 𝓕 Λ ϖ ω = pvSurplus P 𝓕 r s ω)
    (hval' : ∀ᵐ ω ∂P, B0 ω / P0' ω * debtValue P 𝓕 Λ' ϖ ω = pvSurplus P 𝓕 r s ω) :
    ∀ᵐ ω ∂P, Λ 0 ω ≠ 0 → Λ' 0 ω ≠ 0 → pvSurplus P 𝓕 r s ω ≠ 0 →
      P0 ω / P0' ω - 1 = cfgJump r i₀ ϖ T := by
  filter_upwards [deterministic_rate_jump hB hW h𝓕 hT hr hϖ (ι := fun _ => i₀) hΛ hint hΛ' hint'
    hP0 hP0' hval hval'] with ω h h0 h0' hS
  rw [h h0 h0' hS, rateJump_const hϖ (by linarith) (by linarith) hT]

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the corrected jump is the mean jump plus
a covariance term.** With `Z = e^{rT}Λ_T` (`E_0 Z = Λ_0`, `condExp_forward_weight`), a.s. where
`Λ_0 ≠ 0`, `E_0[Z·J]/Λ_0 = E_0[J] + (E_0[Z·J] − E_0[Z]E_0[J])/Λ_0` for `J = rateJump r ϖ T i`:
the book's formula averaged over the rate paths, corrected by the covariance of the forward
weights with the jump.
The general form of the decomposition behind `TidyR7GuidanceItoCex.bm_cov_identity`. -/
theorem random_rate_jump_decomp (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hT : 0 ≤ T) (hΛ : RateSDF P 𝓕 W Λ H i r T M) (ϖ : ℝ) :
    ∀ᵐ ω ∂P, Λ 0 ω ≠ 0 →
      P[fun ω => Real.exp (r * T) * Λ T ω * rateJump r ϖ T i ω | 𝓕 0] ω / Λ 0 ω =
        P[rateJump r ϖ T i | 𝓕 0] ω
        + (P[fun ω => Real.exp (r * T) * Λ T ω * rateJump r ϖ T i ω | 𝓕 0] ω
          - P[fun ω => Real.exp (r * T) * Λ T ω | 𝓕 0] ω * P[rateJump r ϖ T i | 𝓕 0] ω)
          / Λ 0 ω := by
  filter_upwards [condExp_forward_weight hB hW h𝓕 hT hΛ] with ω h h0
  rw [h]
  field_simp
  ring

/-! ### Jensen's inequality for the discount -/

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: **Jensen's inequality for `exp`** with the
gap made explicit: for a bounded measurable `Y` on a probability space,
`exp(E Y) ≤ E exp(Y)`, strictly unless `Y` is a.s. equal to its mean. The gap is
`E[e^Y − e^{EY}(1 + Y − EY)] ≥ 0` (Mathlib `Real.add_one_le_exp`, `Real.add_one_lt_exp`).
Jensen for `exp`; compare Mathlib `ConvexOn.map_integral_le`. -/
theorem exp_integral_le_integral_exp [IsProbabilityMeasure P] {Y : Ω → ℝ} (hYm : Measurable Y)
    {K : ℝ} (hYb : ∀ ω, |Y ω| ≤ K) :
    Real.exp (∫ ω, Y ω ∂P) ≤ ∫ ω, Real.exp (Y ω) ∂P ∧
      (¬ (Y =ᵐ[P] fun _ => ∫ ω, Y ω ∂P) →
        Real.exp (∫ ω, Y ω ∂P) < ∫ ω, Real.exp (Y ω) ∂P) := by
  set y := ∫ ω, Y ω ∂P with hy
  have hYi : Integrable Y P := (integrable_const K).mono' hYm.aestronglyMeasurable
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hYb ω)
  have hEi : Integrable (fun ω => Real.exp (Y ω)) P :=
    (integrable_const (Real.exp K)).mono' (Real.measurable_exp.comp hYm).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 ((le_abs_self _).trans (hYb ω)))
  set g : Ω → ℝ := fun ω => Real.exp (Y ω) - Real.exp y * (Y ω - y + 1) with hg
  have hsplit : ∀ ω, Real.exp (Y ω) = Real.exp y * Real.exp (Y ω - y) := fun ω => by
    rw [← Real.exp_add]; congr 1; ring
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => by
    have h1 := Real.add_one_le_exp (Y ω - y)
    have h2 := Real.exp_pos y
    simp only [hg]
    rw [hsplit ω]
    nlinarith
  have hlin : Integrable (fun ω => Real.exp y * (Y ω - y + 1)) P :=
    ((hYi.sub (integrable_const y)).add (integrable_const 1)).const_mul _
  have hgi : Integrable g P := hEi.sub hlin
  have hYy : Integrable (fun ω => Y ω - y) P := hYi.sub (integrable_const y)
  have hgint : ∫ ω, g ω ∂P = ∫ ω, Real.exp (Y ω) ∂P - Real.exp y := by
    simp only [hg]
    rw [integral_sub hEi hlin, integral_const_mul, integral_add hYy (integrable_const 1),
      integral_sub hYi (integrable_const y), integral_const, integral_const]
    simp [← hy]
  refine ⟨by linarith [integral_nonneg (f := g) (μ := P) hg0], fun hne => ?_⟩
  have hpos : 0 < ∫ ω, g ω ∂P := by
    refine (integral_pos_iff_support_of_nonneg (f := g) hg0 hgi).2 ?_
    have hn : P {ω | ¬ Y ω = y} ≠ 0 := fun h => hne (ae_iff.2 h)
    refine lt_of_lt_of_le (pos_iff_ne_zero.2 hn) (measure_mono fun ω hω => ?_)
    have h1 := Real.add_one_lt_exp (sub_ne_zero.2 hω)
    have h2 := Real.exp_pos y
    change g ω ≠ 0
    simp only [hg]
    rw [hsplit ω]
    nlinarith
  linarith

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the mean of the integrated rate is the
integral of the mean rate (Fubini), `E ∫_T^b i = ∫_T^b E i` for `T ≤ b`.
Fubini, Mathlib `intervalIntegral_integral_swap`. -/
theorem integral_integral_rate [IsProbabilityMeasure P] (hi : Measurable (Function.uncurry i))
    (hb : ∀ u ω, 0 ≤ i u ω ∧ i u ω ≤ M) {T b : ℝ} (hTb : T ≤ b) :
    ∫ ω, (∫ v in T..b, i v ω) ∂P = ∫ v in T..b, ∫ ω, i v ω ∂P := by
  have hint : Integrable (Function.uncurry i) ((volume.restrict (Set.uIoc T b)).prod P) := by
    rw [Set.uIoc_of_le hTb]
    refine (integrable_const M).mono' hi.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    have h := hb p.1 p.2
    rw [Real.norm_eq_abs, Function.uncurry_apply_pair, abs_of_nonneg h.1]
    exact h.2
  exact (intervalIntegral_integral_swap hint).symm

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the mean rate path `E[i_v]` is measurable
and bounded like `i`. -/
theorem meanRate_props [IsProbabilityMeasure P] (hi : Measurable (Function.uncurry i))
    (hb : ∀ u ω, 0 ≤ i u ω ∧ i u ω ≤ M) :
    Measurable (Function.uncurry fun v (_ : Ω) => ∫ ω, i v ω ∂P) ∧
      ∀ (u : ℝ) (_ : Ω), 0 ≤ ∫ ω, i u ω ∂P ∧ ∫ ω, i u ω ∂P ≤ M := by
  refine ⟨((hi.stronglyMeasurable.integral_prod_right (ν := P)).measurable).comp measurable_fst,
    fun u _ => ⟨integral_nonneg fun ω => (hb u ω).1, ?_⟩⟩
  have h := integral_mono (μ := P) ((integrable_const M).mono'
    (hi.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (ae_of_all _ fun ω => by
      change ‖i u ω‖ ≤ M
      rw [Real.norm_eq_abs, abs_of_nonneg (hb u ω).1]
      exact (hb u ω).2)) (integrable_const M) fun ω => (hb u ω).2
  simpa using h

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: Jensen for the bond prices.** The
expected discount to maturity `j` is at least the discount along the mean rate path,
`rateDisc(E i)_j ≤ E[rateDisc(i)_j]`, strictly when `j > T` and `∫_T^j i` is not a.s. equal
to its mean `∫_T^j E i`.
Generalises `TidyR7GuidanceItoCex.bm_jensen` (two-valued rate) to any bounded rate. -/
theorem integral_rateDisc_ge [IsProbabilityMeasure P] (hi : Measurable (Function.uncurry i))
    (hb : ∀ u ω, 0 ≤ i u ω ∧ i u ω ≤ M) (r T j : ℝ) (ω₀ : Ω) :
    rateDisc r T (fun v _ => ∫ ω, i v ω ∂P) j ω₀ ≤ ∫ ω, rateDisc r T i j ω ∂P ∧
      (T < j → ¬ ((fun ω => ∫ v in T..j, i v ω) =ᵐ[P] fun _ => ∫ v in T..j, ∫ ω, i v ω ∂P) →
        rateDisc r T (fun v _ => ∫ ω, i v ω ∂P) j ω₀ < ∫ ω, rateDisc r T i j ω ∂P) := by
  set Y : Ω → ℝ := fun ω => -∫ v in T..max j T, i v ω with hY
  have hYm : Measurable Y := (measurable_integral_rate hi T (max j T)).neg
  have hYb : ∀ ω, |Y ω| ≤ M * (max j T - T) := fun ω => by
    have h := integral_rate_mem hi hb ω (le_max_right j T)
    rw [hY, abs_neg, abs_of_nonneg h.1]
    exact h.2
  have hEY : ∫ ω, Y ω ∂P = -∫ v in T..max j T, ∫ ω, i v ω ∂P := by
    rw [hY, integral_neg, integral_integral_rate hi hb (le_max_right j T)]
  have hD : ∀ ω, rateDisc r T i j ω = Real.exp (-(r * min j T)) * Real.exp (Y ω) := fun ω => by
    rw [rateDisc, ← Real.exp_add]; congr 1; ring
  have hDm : rateDisc r T (fun v _ => ∫ ω, i v ω ∂P) j ω₀ =
      Real.exp (-(r * min j T)) * Real.exp (∫ ω, Y ω ∂P) := by
    rw [hEY, rateDisc, ← Real.exp_add]; congr 1; ring
  have hJ := exp_integral_le_integral_exp (P := P) hYm hYb
  have he := Real.exp_pos (-(r * min j T))
  simp_rw [hD]
  rw [integral_const_mul, hDm]
  refine ⟨mul_le_mul_of_nonneg_left hJ.1 he.le, fun hj hne => ?_⟩
  refine mul_lt_mul_of_pos_left (hJ.2 fun hae => hne ?_) he
  rw [max_eq_left hj.le] at hEY
  filter_upwards [hae] with ω hω
  have h1 : Y ω = -∫ v in T..j, i v ω := by rw [hY, max_eq_left hj.le]
  linarith

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the pathwise discount is continuous in the
maturity. -/
theorem continuous_rateDisc (hi : Measurable (Function.uncurry i))
    (hb : ∀ u ω, 0 ≤ i u ω ∧ i u ω ≤ M) (r T : ℝ) (ω : Ω) :
    Continuous fun j => rateDisc r T i j ω :=
  Real.continuous_exp.comp (((continuous_const.mul (continuous_id.min continuous_const)).add
    ((continuous_integral_rate hi hb ω T).comp (continuous_id.max continuous_const))).neg)

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: Jensen for the value of the debt.**
`rateValue` along the mean rate path `E[i_v]` is at most the mean `E[rateValue]`
(`r ≥ 0`, `T ≥ 0`, `ϖ > 0`), strictly if for some `j₀ > T` the integrated rate `∫_T^{j₀} i` is
not a.s. equal to its mean. With trivial date-0 information, `E_0 = E`: the mean pathwise
value, and so the mean jump, exceed the book's at the expected rate path.
Generalises `TidyR7GuidanceItoCex.bm_jensen` (two-valued rate) to any bounded rate. -/
theorem integral_rateValue_ge [IsProbabilityMeasure P] (hi : Measurable (Function.uncurry i))
    (hb : ∀ u ω, 0 ≤ i u ω ∧ i u ω ≤ M) {r T ϖ : ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T) (hϖ : 0 < ϖ)
    (ω₀ : Ω) :
    rateValue r ϖ T (fun v _ => ∫ ω, i v ω ∂P) ω₀ ≤ ∫ ω, rateValue r ϖ T i ω ∂P ∧
      ((∃ j₀, T < j₀ ∧ ¬ ((fun ω => ∫ v in T..j₀, i v ω) =ᵐ[P]
          fun _ => ∫ v in T..j₀, ∫ ω, i v ω ∂P)) →
        rateValue r ϖ T (fun v _ => ∫ ω, i v ω ∂P) ω₀ < ∫ ω, rateValue r ϖ T i ω ∂P) := by
  obtain ⟨hmm, hmb⟩ := meanRate_props (P := P) hi hb
  set F : ℝ → Ω → ℝ := fun j ω => ϖ * Real.exp (-ϖ * j) * rateDisc r T i j ω with hF
  have hFm : Measurable (Function.uncurry F) :=
    (by fun_prop : Measurable fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1)).mul
      (measurable_rateDisc hi hb r T)
  have hFint : Integrable (Function.uncurry F) ((volume.restrict (Set.Ioi 0)).prod P) := by
    refine ((integrableOn_weight hϖ).mul_prod (integrable_const (1 : ℝ) (μ := P))).mono'
      hFm.aestronglyMeasurable ?_
    have hfst := (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (ν := P)).ae (ae_restrict_mem measurableSet_Ioi)
    filter_upwards [hfst] with p hp
    have h := rateDisc_mem hi hb hr hT (le_of_lt hp) p.2 (r := r)
    have hw : 0 < ϖ * Real.exp (-ϖ * p.1) := by positivity
    rw [Real.norm_eq_abs]
    change |ϖ * Real.exp (-ϖ * p.1) * rateDisc r T i p.1 p.2| ≤ ϖ * Real.exp (-ϖ * p.1) * 1
    rw [abs_mul, abs_of_pos hw, abs_of_pos h.1]
    exact mul_le_mul_of_nonneg_left h.2 hw.le
  have hEV : ∫ ω, rateValue r ϖ T i ω ∂P = ∫ j in Set.Ioi (0 : ℝ), ∫ ω, F j ω ∂P := by
    simp only [rateValue]
    exact (integral_integral_swap hFint).symm
  have hEF : ∀ j, ∫ ω, F j ω ∂P = ϖ * Real.exp (-ϖ * j) * ∫ ω, rateDisc r T i j ω ∂P :=
    fun j => integral_const_mul _ _
  set h : ℝ → ℝ := fun j => ϖ * Real.exp (-ϖ * j) * (∫ ω, rateDisc r T i j ω ∂P
    - rateDisc r T (fun v _ => ∫ ω, i v ω ∂P) j ω₀) with hh
  have hI1 : IntegrableOn (fun j => ∫ ω, F j ω ∂P) (Set.Ioi 0) := hFint.integral_prod_left
  have hI2 : IntegrableOn (fun j => ϖ * Real.exp (-ϖ * j)
      * rateDisc r T (fun v _ => ∫ ω, i v ω ∂P) j ω₀) (Set.Ioi 0) :=
    integrableOn_rateDisc hmm hmb hr hT hϖ ω₀
  have hdiff : ∫ ω, rateValue r ϖ T i ω ∂P - rateValue r ϖ T (fun v _ => ∫ ω, i v ω ∂P) ω₀
      = ∫ j in Set.Ioi (0 : ℝ), h j := by
    rw [hEV, rateValue, ← integral_sub hI1 hI2]
    refine setIntegral_congr_fun measurableSet_Ioi fun j _ => ?_
    simp only [hh, hEF j]
    ring
  have hh0 : ∀ j, 0 ≤ h j := fun j => mul_nonneg (by positivity)
    (sub_nonneg.2 (integral_rateDisc_ge hi hb r T j ω₀).1)
  have hnn : 0 ≤ ∫ j in Set.Ioi (0 : ℝ), h j :=
    setIntegral_nonneg measurableSet_Ioi fun j _ => hh0 j
  refine ⟨by linarith, fun ⟨j₀, hj₀, hne⟩ => ?_⟩
  have hhj₀ : 0 < h j₀ := mul_pos (by positivity)
    (sub_pos.2 ((integral_rateDisc_ge hi hb r T j₀ ω₀).2 hj₀ hne))
  have hj₀0 : 0 < j₀ := lt_of_le_of_lt hT hj₀
  have hcont : ContinuousOn h (Set.Ioi 0) := by
    have hE : ContinuousOn (fun j => ∫ ω, rateDisc r T i j ω ∂P) (Set.Ioi 0) := by
      refine continuousOn_of_dominated (bound := fun _ => 1)
        (fun j _ => ((measurable_rateDisc hi hb r T).comp
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
        (fun j hj => ae_of_all _ fun ω => ?_) (integrable_const 1)
        (ae_of_all _ fun ω => (continuous_rateDisc hi hb r T ω).continuousOn)
      have h1 := rateDisc_mem hi hb hr hT (le_of_lt hj) ω (r := r)
      rw [Real.norm_eq_abs, abs_of_pos h1.1]
      exact h1.2
    exact ((by fun_prop : Continuous fun j : ℝ => ϖ * Real.exp (-ϖ * j)).continuousOn).mul
      (hE.sub (continuous_rateDisc hmm hmb r T ω₀).continuousOn)
  have hhint : IntegrableOn h (Set.Ioi 0) := by
    have e : h = fun j => ∫ ω, F j ω ∂P - ϖ * Real.exp (-ϖ * j)
        * rateDisc r T (fun v _ => ∫ ω, i v ω ∂P) j ω₀ := by
      funext j
      simp only [hh, hEF j]
      ring
    rw [e]
    exact hI1.sub hI2
  have hev : ∀ᶠ j in 𝓝 j₀, 0 < h j ∧ 0 < j :=
    ((hcont.continuousAt (Ioi_mem_nhds hj₀0)).eventually (lt_mem_nhds hhj₀)).and
      (Ioi_mem_nhds hj₀0)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hsub : Set.Ioo (j₀ - ε) (j₀ + ε) ⊆ Function.support h ∩ Set.Ioi 0 := fun j hj => by
    have hd : dist j j₀ < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hj.1, hj.2]
    exact ⟨(hball hd).1.ne', (hball hd).2⟩
  have hpos : 0 < ∫ j in Set.Ioi (0 : ℝ), h j := by
    refine (setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun j => hh0 j) hhint).2 ?_
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.2 (by linarith)
  linarith

/-! ### `i` is the short rate: the Itô process `exp(−∫_T^u i)` -/

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the time integral of an adapted process
with continuous paths is adapted, `∫_T^u i ∈ 𝓕_u` (limit of left-point Riemann sums along
dyadic partitions, `TidyR7ItoL2.tendsto_riemannSum`). -/
theorem stronglyMeasurable_integral_adapted {T u : ℝ} (hTu : T ≤ u)
    (hia : ∀ v ∈ Set.Icc T u, StronglyMeasurable[𝓕 v] (i v))
    (hic : ∀ ω, ContinuousOn (fun v => i v ω) (Set.Icc T u)) :
    StronglyMeasurable[𝓕 u] (fun ω => ∫ v in T..u, i v ω) := by
  rcases hTu.eq_or_lt with h | h
  · subst h
    simp only [intervalIntegral.integral_same]
    exact stronglyMeasurable_const
  · refine stronglyMeasurable_of_tendsto (f := fun k ω => riemannSum (dyadic h k)
      (fun v => i v ω)) atTop (fun k => ?_) ?_
    · simp only [riemannSum]
      refine Finset.stronglyMeasurable_fun_sum _ fun n hn => ?_
      have hmem := t_mem (dyadic h k) (Finset.mem_range.1 hn).le
      exact ((hia _ hmem).mono (𝓕.mono hmem.2)).mul_const _
    · exact tendsto_pi_nhds.2 fun ω => tendsto_riemannSum (hic ω) _ (tendsto_mesh_dyadic h)

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561, with Itô's formula for the exponential
(`TidyR9ItoFormulaVariants.itoProcess_exp`): the random rate is the short rate.** If `i` is an
admissible integrand on `[T, t]` (adapted, `|i| ≤ C`) with continuous paths, `0 ≤ T ≤ t`,
`0 ≤ C`, then `D_u = exp(−∫_T^u i)` is an Itô process on `[T, t]` with drift `−i_u D_u` and no
diffusion: `dD = −iD dt`, so `Λ_u = Λ_T D_u` has the short rate `i`. -/
theorem itoProcess_rateDisc (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hT : 0 ≤ T) {t C : ℝ} (hTt : T ≤ t) (hC : 0 ≤ C)
    (hi : ItoIntegrand P 𝓕 i T t C) (hic : ∀ ω, ContinuousOn (fun v => i v ω) (Set.Icc T t)) :
    ItoProcess P 𝓕 W (fun u ω => Real.exp (-∫ v in T..u, i v ω))
      (fun u ω => -(i u ω * Real.exp (-∫ v in T..u, i v ω))) (fun _ _ => 0) T t
      (Real.exp (C * (t - T)) * (|-1| * C) + Real.exp (C * (t - T)) / 2 * (0 * 0))
      (Real.exp (C * (t - T)) * 0) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hX : ItoProcess P 𝓕 W (fun u ω => -∫ v in T..u, i v ω) (fun u ω => -1 * i u ω)
      (fun _ _ => 0) T t (|-1| * C) 0 :=
    { adapted := fun u hu => (stronglyMeasurable_integral_adapted hu.1
        (fun v hv => hi.adapted v ⟨hv.1, hv.2.trans hu.2⟩)
        (fun ω => (hic ω).mono (Set.Icc_subset_Icc_right hu.2))).neg
      init := by
        simp only [intervalIntegral.integral_same, neg_zero]
        exact memLp_const 0
      drift := hi.const_mul (-1)
      diff := itoIntegrand_deterministic (h := fun _ => 0) continuousOn_const
        (fun _ _ => by simp)
      eq := fun u hu => by
        have hz := itoInt_const (W := W) (P := P) (𝓕 := 𝓕) hB hW h𝓕 hT hu.1
          (c := fun _ => (0 : ℝ)) stronglyMeasurable_const (C := 0) (fun _ => by simp)
        filter_upwards [hz] with ω hω
        rw [hω, zero_mul, add_zero, intervalIntegral.integral_same, neg_zero, zero_add,
          intervalIntegral.integral_const_mul]
        ring }
  have hXc : ∀ᵐ ω ∂P, ContinuousOn (fun u => -∫ v in T..u, i v ω) (Set.Icc T t) :=
    ae_of_all _ fun ω => by
      have h := intervalIntegral.continuousOn_primitive_interval'
        ((hic ω).intervalIntegrable_of_Icc (μ := volume) hTt) Set.left_mem_uIcc
      rw [Set.uIcc_of_le hTt] at h
      exact h.neg
  have hXb : ∀ u ∈ Set.Icc T t, ∀ ω, |-∫ v in T..u, i v ω| ≤ C * (t - T) := fun u hu ω => by
    rw [abs_neg, ← Real.norm_eq_abs]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := T) (b := u)
      (f := fun v => i v ω) (C := C) fun v hv => by
        rw [Set.uIoc_of_le hu.1] at hv
        rw [Real.norm_eq_abs]
        exact hi.bound v ⟨hv.1.le, hv.2.trans hu.2⟩ ω
    rw [abs_of_nonneg (sub_nonneg.2 hu.1)] at h
    exact h.trans (mul_le_mul_of_nonneg_left (by linarith [hu.2]) hC)
  have h := itoProcess_exp hB hW h𝓕 hT hTt hX hXc (mul_nonneg hC (sub_nonneg.2 hTt)) hXb
  exact itoProcess_of_coeff_eq h (fun u ω => by ring) (fun u ω => by ring)

end Cochrane.LongTermDebtDynamics.TidyR9GuidanceRandomRate
