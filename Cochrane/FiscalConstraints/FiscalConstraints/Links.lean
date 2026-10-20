/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.RvsG
import FiscalConstraints.DebtLimitStochastic
import FiscalConstraints.DiscountGrowth
import FiscalConstraints.GrowthTheoryTVC
import FiscalConstraints.AggregateUncertainty

/-!
# Links between the Chapter 6 developments

Cochrane (2023), Chapter 6, *Fiscal constraints*, §6.2 and §6.4 (pp. 191–207). The chapter was
formalised in two independent chains; this module proves that their objects agree where the
book talks about the same thing.

## Main results

* `forward_integral_eq_pv`, `forward_present_value_eq_pv`: the forward present value of (6.9)
  (`LinearODE.forward_present_value`, used in `MoneyLiquidity`) is `RvsG.pv`, the present value
  of §6.4.1 (pp. 196, 201).
* `valueOfDebt_eq_pv`: the value of debt (6.2) after substituting (6.1)/(6.6) is `RvsG.pv` of a
  constant surplus ratio, discounted at `r − g` (pp. 191, 195).
* `marginalValue_consumption`, `euler_iff_rate`, `rate_population_lt_growth_iff`: the
  first-order condition of §6.2 (`DiscountGrowth`) and of §6.4.4 (`GrowthTheoryTVC`) are the
  same equation (6.1) = (6.6) (pp. 191, 199–200).
* `growth_tvc_term_eq_levels`, `growth_tvc_iff_levels_tvc`, `steady_debt_is_pv`,
  `growth_tvc_from_rvsg`: the growth-theory TVC of p. 200 is the TVC in levels of §6.4.1
  (`RvsG.tvc_levels_iff`) for debt in a steady ratio to output; `r > g` makes the steady ratio
  the present value (p. 196).
* `debt_gdp_solvesD`, `debtPath_solvesD`, `debtPath_abs_le`, `gaussian_not_bddD`: the stochastic
  debt path of Theorem S is, path by path, the discrete solution of (6.4) studied in `RvsG`
  (D5). With bounded surpluses every path is bounded (D5, "indeterminacy, not infinity"); with
  i.i.d. Gaussian surpluses almost every path is unbounded (Theorem S, p. 197).
* `deterministic_rf_lt_g_iff`, `rf_lt_g_pv_finite_needs_risk`: without risk, `r_f < g` is
  exactly divergence of the present value (Theorem D of `RvsG`); with lognormal growth risk the
  two separate (Bohn's case, pp. 205–206).
-/

namespace Cochrane.FiscalConstraints.Links

open Real MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.FiscalConstraints.AggregateUncertainty (riskFreeGross lognormalMoment)

/-! ### Forward present values (§6.4.1 and §6.4.5) -/

/-- Cochrane (2023), (6.9) p. 201 and §6.4.1 p. 196: the forward integral of (6.9),
`∫_t^∞ e^{−a(τ−t)} f_τ dτ`, is the present value `RvsG.pv a f t = ∫₀^∞ e^{−a u} f_{t+u} du`. -/
theorem forward_integral_eq_pv (a : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    ∫ τ in Set.Ioi t, exp (-a * (τ - t)) * f τ = RvsG.pv a f t := by
  have h := ExpIntegrals.integral_Ioi_comp_add (fun τ => exp (-a * (τ - t)) * f τ) t
  simp only [add_sub_cancel_left] at h
  unfold RvsG.pv
  exact h.symm

/-- Cochrane (2023), (6.9) p. 201 and §6.4.1 p. 196: a solution of `w' = a w − f` on `ℝ`
satisfying the transversality condition from `t` equals the present value `RvsG.pv a f t` of
§6.4.1 (for `a = r − g > 0` and bounded continuous `f`). -/
theorem forward_present_value_eq_pv {a K : ℝ} (ha : 0 < a) {w f : ℝ → ℝ}
    (hw : ∀ τ, HasDerivAt w (a * w τ - f τ) τ) (hf : Continuous f) (hK : ∀ τ, |f τ| ≤ K)
    (t : ℝ) (htvc : Tendsto (fun T => exp (-a * (T - t)) * w T) atTop (𝓝 0)) :
    w t = RvsG.pv a f t := by
  rw [(LinearODE.forward_present_value ha hw hf hK t htvc).2, forward_integral_eq_pv]

/-- Cochrane (2023), (6.2) p. 191 and (6.3) p. 195: the value of debt with `r = δ + γ g`
substituted, `σ/(δ + (γ − 1) g)`, is the present value `RvsG.pv` of the constant surplus
ratio `σ` discounted at `r − g > 0`. -/
theorem valueOfDebt_eq_pv {σ δ γ g : ℝ} (h : g < GrowthTheoryTVC.rate δ γ g) (t : ℝ) :
    DiscountGrowth.valueOfDebt σ δ γ g =
      RvsG.pv (GrowthTheoryTVC.rate δ γ g - g) (fun _ => σ) t := by
  rw [RvsG.pv_const (sub_pos.2 h)]
  rfl

/-! ### The consumer's first-order condition: (6.1) = (6.6) -/

/-- Cochrane (2023), (6.1) p. 191 and (6.6) p. 199: the marginal value of a unit invested at `r`
(`DiscountGrowth.marginalValue`) along balanced growth is discounted marginal utility
(`GrowthTheoryTVC.marginalUtility`) times `e^{r t}`. -/
theorem marginalValue_consumption (δ γ r c₀ g t : ℝ) :
    DiscountGrowth.marginalValue δ γ r (GrowthTheoryTVC.consumption c₀ g) t =
      GrowthTheoryTVC.marginalUtility δ γ c₀ g t * exp (r * t) := rfl

/-- Cochrane (2023), (6.1) p. 191 and (6.6) p. 199: along `c_t = c₀ e^{g t}` the first-order
condition of §6.2 (the marginal value is constant) holds iff `r` is the rate of §6.4.4,
`r = δ + γ g`. -/
theorem euler_iff_rate {c₀ : ℝ} (hc₀ : 0 < c₀) (δ γ r g : ℝ) :
    (∀ t, DiscountGrowth.marginalValue δ γ r (GrowthTheoryTVC.consumption c₀ g) t =
        DiscountGrowth.marginalValue δ γ r (GrowthTheoryTVC.consumption c₀ g) 0) ↔
      r = GrowthTheoryTVC.rate δ γ g :=
  DiscountGrowth.euler_exponential_iff hc₀ δ γ r g

/-- Cochrane (2023), p. 200 ("population growth `n` allows `r < g` more easily"): with
`r = δ + γ (g − n)`, `r < g` iff `δ + (γ − 1) g < γ n` (`DiscountGrowth.r_lt_g_population_iff`
for the rate of `GrowthTheoryTVC`). -/
theorem rate_population_lt_growth_iff (δ γ g n : ℝ) :
    GrowthTheoryTVC.rate δ γ (g - n) < g ↔ δ + (γ - 1) * g < γ * n :=
  DiscountGrowth.r_lt_g_population_iff rfl

/-! ### The transversality condition: §6.4.4 vs §6.4.1 -/

/-- Cochrane (2023), pp. 196 and 200: the growth-theory TVC term for debt `b_T = κ c_T` is
`c₀^{−γ}` times the §6.4.1 levels term `e^{−r T} b_T` with `r = (r − g) + g` and
`b_T = κ · c₀ e^{g T}`. -/
theorem growth_tvc_term_eq_levels {c₀ : ℝ} (hc : 0 < c₀) (δ γ g κ T : ℝ) :
    GrowthTheoryTVC.marginalUtility δ γ c₀ g T * (κ * GrowthTheoryTVC.consumption c₀ g T) =
      c₀ ^ (-γ) * (exp (-((GrowthTheoryTVC.rate δ γ g - g) + g) * T) *
        (κ * (c₀ * exp (g * T)))) := by
  rw [GrowthTheoryTVC.marginalUtility_eq hc, sub_add_cancel]
  unfold GrowthTheoryTVC.consumption
  ring

/-- Cochrane (2023), pp. 196 and 200: for debt in a steady positive ratio `κ` to output, the
§6.4.1 transversality condition in levels, `e^{−r T} b_T → 0`, holds iff `r > g`, exactly the
growth-theory condition `GrowthTheoryTVC.tvc_iff`. -/
theorem growth_tvc_iff_levels_tvc {c₀ κ : ℝ} (hc : 0 < c₀) (hκ : 0 < κ) (δ γ g : ℝ) :
    Tendsto (fun T => exp (-((GrowthTheoryTVC.rate δ γ g - g) + g) * T) *
        (κ * (c₀ * exp (g * T)))) atTop (𝓝 0) ↔ g < GrowthTheoryTVC.rate δ γ g := by
  have hp : 0 < c₀ ^ (-γ) := Real.rpow_pos_of_pos hc _
  have e : ∀ T, exp (-((GrowthTheoryTVC.rate δ γ g - g) + g) * T) * (κ * (c₀ * exp (g * T))) =
      (c₀ ^ (-γ))⁻¹ * (GrowthTheoryTVC.marginalUtility δ γ c₀ g T *
        (κ * GrowthTheoryTVC.consumption c₀ g T)) := by
    intro T
    rw [growth_tvc_term_eq_levels hc]
    exact (inv_mul_cancel_left₀ hp.ne' _).symm
  rw [tendsto_congr e, ← GrowthTheoryTVC.tvc_iff hc hκ δ γ g]
  constructor
  · intro h
    have h2 := h.const_mul (c₀ ^ (-γ))
    rw [mul_zero] at h2
    exact h2.congr fun T => mul_inv_cancel_left₀ hp.ne' _
  · intro h
    have h2 := h.const_mul (c₀ ^ (-γ))⁻¹
    rwa [mul_zero] at h2

/-- Cochrane (2023), §6.4.1 p. 196 and §6.4.2 p. 198: debt held in a steady ratio `κ` solves
(6.4) with the steady surplus ratio `(r − g) κ`, and for `r > g` it equals the present value of
those surpluses. -/
theorem steady_debt_is_pv {κ δ γ g : ℝ} (h : g < GrowthTheoryTVC.rate δ γ g) :
    RvsG.SolvesOn (GrowthTheoryTVC.rate δ γ g - g)
        (fun _ => (GrowthTheoryTVC.rate δ γ g - g) * κ) (fun _ => κ) ∧
      κ = RvsG.pv (GrowthTheoryTVC.rate δ γ g - g)
        (fun _ => (GrowthTheoryTVC.rate δ γ g - g) * κ) 0 := by
  refine ⟨(RvsG.steady_state_iff _ _ _).2 rfl, ?_⟩
  rw [RvsG.pv_const (sub_pos.2 h)]
  exact (mul_div_cancel_left₀ κ (sub_pos.2 h).ne').symm

/-- Cochrane (2023), pp. 196 and 200: for `r > g` the growth-theory TVC for a steady debt ratio
follows from §6.4.1 alone (`RvsG.tvc_levels_iff` and `steady_debt_is_pv`), independently of
`GrowthTheoryTVC.tvc_iff`. -/
theorem growth_tvc_from_rvsg {c₀ κ δ γ g : ℝ} (hc : 0 < c₀)
    (h : g < GrowthTheoryTVC.rate δ γ g) :
    Tendsto (fun T => exp (-((GrowthTheoryTVC.rate δ γ g - g) + g) * T) *
        (κ * (c₀ * exp (g * T)))) atTop (𝓝 0) := by
  obtain ⟨hx, h0⟩ := steady_debt_is_pv (κ := κ) h
  exact (RvsG.tvc_levels_iff hc.ne' (sub_pos.2 h) continuous_const
    (M := |(GrowthTheoryTVC.rate δ γ g - g) * κ|) (fun _ => le_rfl) hx).2 h0

/-! ### Discrete debt dynamics: Theorem D (D5) vs Theorem S -/

/-- Cochrane (2023), (6.4) p. 196: the discrete debt/GDP recursion of `LinearODE` is a solution
of the discrete equation `RvsG.SolvesD` with `γ = (1 + r)/(1 + g)`. -/
theorem debt_gdp_solvesD {b y s : ℕ → ℝ} {r g : ℝ}
    (hb : ∀ t, b (t + 1) = (1 + r) * b t - s (t + 1))
    (hy : ∀ t, y (t + 1) = (1 + g) * y t) (hy0 : ∀ t, y t ≠ 0) (hg : 1 + g ≠ 0) :
    RvsG.SolvesD ((1 + r) / (1 + g)) (fun t => s (t + 1) / y (t + 1)) (fun t => b t / y t) :=
  fun t => LinearODE.debt_gdp_discrete hb hy hy0 hg t

/-- Cochrane (2023), (6.4) p. 196 and p. 197: every path of the stochastic debt ratio of
Theorem S solves the discrete equation (6.4) of `RvsG` (D5). -/
theorem debtPath_solvesD {Ω : Type*} (γ x₀ : ℝ) (σ : ℕ → Ω → ℝ) (ω : Ω) :
    RvsG.SolvesD γ (fun t => σ t ω) (fun t => DebtLimitStochastic.debtPath γ x₀ σ t ω) :=
  RvsG.iterD_solves γ _ x₀

/-- Cochrane (2023), pp. 196–197 (D5 applied path by path): with `r < g` (`0 ≤ γ < 1`) and
surpluses bounded by `M` on a path, the debt ratio on that path stays within
`|x₀| + M/(1 − γ)`: bounded surpluses give the indeterminacy branch of Theorem D, never the
explosion of Theorem S. -/
theorem debtPath_abs_le {Ω : Type*} {γ x₀ M : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {σ : ℕ → Ω → ℝ} {ω : Ω} (hM : ∀ t, |σ t ω| ≤ M) (t : ℕ) :
    |DebtLimitStochastic.debtPath γ x₀ σ t ω| ≤ |x₀| + M / (1 - γ) :=
  RvsG.abs_le_of_lt_one hγ0 hγ1 hM (debtPath_solvesD γ x₀ σ ω) t

/-- Cochrane (2023), p. 197 vs p. 196: with `r < g` and i.i.d. Gaussian surpluses (truncated
above), almost every debt path is NOT bounded in the sense of `RvsG.BddD`, although every path
with bounded surpluses is (`debtPath_abs_le`): Theorem S lives outside Theorem D's hypotheses. -/
theorem gaussian_not_bddD {Ω : Type*} [MeasureSpace Ω] {γ x₀ K : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) {σ : ℕ → Ω → ℝ} (hσ : ∀ t, Measurable (σ t)) (hind : iIndepFun σ volume)
    (hident : ∀ t, IdentDistrib (σ t) (σ 0) volume volume) (hK : ∀ t, ∀ᵐ ω, σ t ω ≤ K)
    {m : ℝ} {v : NNReal} (hv : v ≠ 0) (hlaw : Measure.map (σ 0) volume = gaussianReal m v) :
    ∀ᵐ ω, ¬ RvsG.BddD (fun t => DebtLimitStochastic.debtPath γ x₀ σ t ω) := by
  filter_upwards [DebtLimitStochastic.gaussian_iid_unbounded hγ0 hγ1 hσ hind hident hK hv
    hlaw] with ω hω
  rintro ⟨B, hB⟩
  obtain ⟨t, ht⟩ := (hω B).exists
  exact absurd ((le_abs_self _).trans (hB t)) (not_le.mpr ht)

/-! ### `r_f < g` with and without risk: Theorem D vs §6.4.7 -/

/-- Cochrane (2023), pp. 195–196 and 205–206: without growth risk (`σ² = 0`) the risk-free
rate is below growth iff the correct present-value ratio `β E[G^{1−γ}]` exceeds one, i.e. iff
the present value of a growing surplus diverges: the deterministic `r < g` of Theorem D. -/
theorem deterministic_rf_lt_g_iff (δ γ μ : ℝ) :
    riskFreeGross (exp (-δ)) γ (lognormalMoment μ 0) < lognormalMoment μ 0 1 ↔
      1 < exp (-δ) * lognormalMoment μ 0 (1 - γ) := by
  rw [AggregateUncertainty.riskFree_lt_growth_iff, AggregateUncertainty.lognormal_correct,
    AggregateUncertainty.incorrectExponent, Real.one_lt_exp_iff]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), pp. 196 and 205–206: under perfect foresight `r_f < g` rules out a finite
present value (`β E[G^{1−γ}] < 1` fails), but with lognormal growth risk (`σ² > 0`, `γ > 0`)
there are `μ` and `δ > 0` with a finite present value and `r_f < E[G]` (Bohn's case). -/
theorem rf_lt_g_pv_finite_needs_risk {γ v : ℝ} (hγ : 0 < γ) (hv : 0 < v) :
    (∀ δ μ, riskFreeGross (exp (-δ)) γ (lognormalMoment μ 0) < lognormalMoment μ 0 1 →
        ¬ exp (-δ) * lognormalMoment μ 0 (1 - γ) < 1) ∧
      ∃ μ δ, 0 < δ ∧ exp (-δ) * lognormalMoment μ v (1 - γ) < 1 ∧
        riskFreeGross (exp (-δ)) γ (lognormalMoment μ v) < lognormalMoment μ v 1 :=
  ⟨fun δ μ h => not_lt.mpr ((deterministic_rf_lt_g_iff δ γ μ).1 h).le,
    AggregateUncertainty.bohn_region hγ hv⟩

end Cochrane.FiscalConstraints.Links
