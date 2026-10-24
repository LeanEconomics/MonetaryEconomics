/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.ExpIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Growth theory, the transversality condition and `r < g`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.4, pp. 199–200.

The dynastic representative agent with utility `∫ e^{−δt} c_t^{1−γ}/(1−γ) dt` on a balanced
growth path `c_t = c₀ e^{g t}` has marginal utility `Λ_t = e^{−δt} c_t^{−γ}`, and the real
rate is its rate of decline, `r = δ + γ g` (6.6). The transversality condition for debt held
in a steady ratio to consumption, `lim e^{−δT} u'(c_T) b_T = 0`, holds exactly when `r > g`;
with `δ = 0` it holds iff `γ > 1` (p. 200). With population growth `n` and per-capita
consumption growing at `g − n`, `r = δ + γ (g − n)`, the transversality condition becomes
`r > g − n`, and `r < g` becomes compatible with it.

## Main results

* `hasDerivAt_log_marginalUtility`: (6.6) as an exact derivative, `−(d/dt) log Λ_t = δ + γ g`.
* `marginalUtility_ratio`: `Λ_τ/Λ_t = e^{−(δ+γg)(τ−t)}`, the discount factor of p. 203.
* `rate_gt_growth_iff`, `rate_gt_growth_of_standard`, `rate_lt_growth_iff`.
* `tvc_iff`: the TVC with a steady debt/consumption ratio holds iff `r > g`.
* `tvc_delta_zero_iff`: with `δ = 0` and `g > 0`, the TVC holds iff `γ > 1` (p. 200);
  `tvc_diverges_of_lt_one`: for `γ < 1` the TVC expression grows without bound.
* `rate_population`, `tvc_population_iff`, `population_allows_r_lt_g`: population growth
  (the criterion `r < g ⇔ δ + (γ − 1) g < γ n` is `DiscountGrowth.r_lt_g_population_iff`).
-/

namespace Cochrane.FiscalConstraints.GrowthTheoryTVC

open Filter Topology
open Cochrane.FiscalConstraints.ExpIntegrals
  (tendsto_const_mul_exp_zero_iff tendsto_const_mul_exp_atTop)

/-- Cochrane (2023), p. 199: balanced-growth consumption `c_t = c₀ e^{g t}`. -/
noncomputable def consumption (c₀ g t : ℝ) : ℝ := c₀ * Real.exp (g * t)

/-- Cochrane (2023), p. 199: discounted marginal utility `Λ_t = e^{−δt} c_t^{−γ}` of power
utility `c^{1−γ}/(1−γ)`. -/
noncomputable def marginalUtility (δ γ c₀ g t : ℝ) : ℝ :=
  Real.exp (-δ * t) * consumption c₀ g t ^ (-γ)

/-- Cochrane (2023), (6.6) p. 199: the consumer's real rate `r = δ + γ g`. -/
def rate (δ γ g : ℝ) : ℝ := δ + γ * g

/-- Cochrane (2023), p. 199: for `c₀ > 0`, `c_t^a = c₀^a e^{a g t}`. -/
theorem consumption_rpow {c₀ : ℝ} (hc : 0 < c₀) (g t a : ℝ) :
    consumption c₀ g t ^ a = c₀ ^ a * Real.exp (a * g * t) := by
  unfold consumption
  rw [Real.mul_rpow hc.le (Real.exp_pos _).le, ← Real.exp_mul]
  ring_nf

/-- Cochrane (2023), (6.6) p. 199: the log of discounted marginal utility is affine in time,
`log Λ_t = −γ log c₀ − (δ + γ g) t`. -/
theorem log_marginalUtility {c₀ : ℝ} (hc : 0 < c₀) (δ γ g t : ℝ) :
    Real.log (marginalUtility δ γ c₀ g t) = -γ * Real.log c₀ - rate δ γ g * t := by
  unfold marginalUtility rate
  rw [consumption_rpow hc, Real.log_mul (Real.exp_pos _).ne'
      (mul_pos (Real.rpow_pos_of_pos hc _) (Real.exp_pos _)).ne',
    Real.log_mul (Real.rpow_pos_of_pos hc _).ne' (Real.exp_pos _).ne', Real.log_exp,
    Real.log_exp, Real.log_rpow hc]
  ring

/-- Cochrane (2023), (6.6) p. 199, as an exact derivative: the rate of decline of marginal
utility is `−(d/dt) log Λ_t = δ + γ g`, i.e. `(d/dt) log Λ_t = −(δ + γ g)`. -/
theorem hasDerivAt_log_marginalUtility {c₀ : ℝ} (hc : 0 < c₀) (δ γ g t : ℝ) :
    HasDerivAt (fun s => Real.log (marginalUtility δ γ c₀ g s)) (-rate δ γ g) t := by
  have h : (fun s => Real.log (marginalUtility δ γ c₀ g s)) =
      fun s => -γ * Real.log c₀ - rate δ γ g * s := by
    funext s; exact log_marginalUtility hc δ γ g s
  rw [h]
  have := ((hasDerivAt_id t).const_mul (rate δ γ g)).const_sub (-γ * Real.log c₀)
  simpa using this

/-- Cochrane (2023), (6.6) p. 199: discounted marginal utility is
`Λ_t = c₀^{−γ} e^{−(δ + γ g) t}`. -/
theorem marginalUtility_eq {c₀ : ℝ} (hc : 0 < c₀) (δ γ g t : ℝ) :
    marginalUtility δ γ c₀ g t = c₀ ^ (-γ) * Real.exp (-rate δ γ g * t) := by
  unfold marginalUtility rate
  rw [consumption_rpow hc, mul_left_comm, ← Real.exp_add]
  congr 2
  ring

/-- Cochrane (2023), p. 203: the marginal rate of substitution is the risk-free discount
factor, `Λ_τ/Λ_t = e^{−r (τ − t)}` with `r = δ + γ g`. -/
theorem marginalUtility_ratio {c₀ : ℝ} (hc : 0 < c₀) (δ γ g t τ : ℝ) :
    marginalUtility δ γ c₀ g τ / marginalUtility δ γ c₀ g t =
      Real.exp (-rate δ γ g * (τ - t)) := by
  have h1 : 0 < c₀ ^ (-γ) := Real.rpow_pos_of_pos hc _
  rw [marginalUtility_eq hc, marginalUtility_eq hc, mul_div_mul_left _ _ h1.ne',
    ← Real.exp_sub]
  congr 1
  ring

/-- Cochrane (2023), p. 199: `r > g` iff `δ + (γ − 1) g > 0`. -/
theorem rate_gt_growth_iff (δ γ g : ℝ) : g < rate δ γ g ↔ 0 < δ + (γ - 1) * g := by
  unfold rate; constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 199: `r < g` iff `δ < (1 − γ) g`. -/
theorem rate_lt_growth_iff (δ γ g : ℝ) : rate δ γ g < g ↔ δ < (1 - γ) * g := by
  unfold rate; constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 199 ("we usually think that `δ > 0` ... and that `γ ≥ 1`. Hence
`r > g`"), for non-negative growth. -/
theorem rate_gt_growth_of_standard {δ γ g : ℝ} (hδ : 0 < δ) (hγ : 1 ≤ γ) (hg : 0 ≤ g) :
    g < rate δ γ g := by
  rw [rate_gt_growth_iff]
  nlinarith

/-- Cochrane (2023), p. 199 ("one can deliver `r < g` with small `δ`, `γ < 1` and low `g`"):
for `γ < 1` and `g > 0`, every `0 ≤ δ < (1 − γ) g` gives `r < g`, and such `δ > 0` exist. -/
theorem rate_lt_growth_possible {γ g : ℝ} (hγ : γ < 1) (hg : 0 < g) :
    ∃ δ, 0 < δ ∧ rate δ γ g < g := by
  refine ⟨(1 - γ) * g / 2, by nlinarith, ?_⟩
  rw [rate_lt_growth_iff]
  nlinarith

/-- Cochrane (2023), p. 200: the transversality-condition term with `δ = 0`,
`u'(c_T) b_T = c_T^{1−γ} (b_T/c_T)`. -/
theorem tvc_term_identity {c b : ℝ} (hc : 0 < c) (γ : ℝ) :
    c ^ (-γ) * b = c ^ (1 - γ) * (b / c) := by
  rw [Real.rpow_sub hc, Real.rpow_one, Real.rpow_neg hc.le]
  field_simp

/-- Cochrane (2023), p. 200: the discounted value of debt held in the steady ratio
`b_T = κ c_T`, `e^{−δT} u'(c_T) b_T = κ c₀^{1−γ} e^{(−δ + (1−γ) g) T}`. -/
theorem tvc_term_eq {c₀ : ℝ} (hc : 0 < c₀) (δ γ g κ T : ℝ) :
    marginalUtility δ γ c₀ g T * (κ * consumption c₀ g T) =
      κ * c₀ ^ (1 - γ) * Real.exp ((-δ + (1 - γ) * g) * T) := by
  unfold marginalUtility
  have h := consumption_rpow hc g T (-γ)
  have h1 : consumption c₀ g T = c₀ * Real.exp (g * T) := rfl
  rw [h, h1, Real.rpow_sub hc, Real.rpow_one, Real.rpow_neg hc.le]
  have hexp : Real.exp ((-δ + (1 - γ) * g) * T) =
      Real.exp (-δ * T) * Real.exp (-γ * g * T) * Real.exp (g * T) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [hexp]
  have hc' : (c₀ ^ γ) ≠ 0 := (Real.rpow_pos_of_pos hc γ).ne'
  field_simp

/-- Cochrane (2023), p. 200: the transversality condition for debt in a steady positive
ratio `κ` to consumption, `lim_{T→∞} e^{−δT} u'(c_T) b_T = 0`, holds iff `r > g`. -/
theorem tvc_iff {c₀ κ : ℝ} (hc : 0 < c₀) (hκ : 0 < κ) (δ γ g : ℝ) :
    Tendsto (fun T => marginalUtility δ γ c₀ g T * (κ * consumption c₀ g T)) atTop (𝓝 0) ↔
      g < rate δ γ g := by
  have hK : 0 < κ * c₀ ^ (1 - γ) := mul_pos hκ (Real.rpow_pos_of_pos hc _)
  simp_rw [tvc_term_eq hc]
  rw [tendsto_const_mul_exp_zero_iff hK, rate_gt_growth_iff]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 200: with `δ = 0` and growth `g > 0`, a steady debt/consumption
ratio satisfies the transversality condition iff `γ > 1`. -/
theorem tvc_delta_zero_iff {c₀ κ γ g : ℝ} (hc : 0 < c₀) (hκ : 0 < κ) (hg : 0 < g) :
    Tendsto (fun T => marginalUtility 0 γ c₀ g T * (κ * consumption c₀ g T)) atTop (𝓝 0) ↔
      1 < γ := by
  rw [tvc_iff hc hκ, rate_gt_growth_iff]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- Cochrane (2023), p. 200 ("for `γ < 1`, the right-hand side continues to grow"): with
`δ = 0`, `g > 0` and `γ < 1`, `u'(c_T) b_T → ∞` for a steady debt/consumption ratio. -/
theorem tvc_diverges_of_lt_one {c₀ κ γ g : ℝ} (hc : 0 < c₀) (hκ : 0 < κ) (hg : 0 < g)
    (hγ : γ < 1) :
    Tendsto (fun T => marginalUtility 0 γ c₀ g T * (κ * consumption c₀ g T)) atTop atTop := by
  have hK : 0 < κ * c₀ ^ (1 - γ) := mul_pos hκ (Real.rpow_pos_of_pos hc _)
  simp_rw [tvc_term_eq hc]
  exact tendsto_const_mul_exp_atTop hK (by nlinarith)

/-- Cochrane (2023), p. 200: with population growing at rate `n` and aggregate consumption at
`g`, per-capita consumption grows at `g − n` and the consumer's rate is
`r = δ + γ (g − n)`, as the exact rate of decline of marginal utility. -/
theorem rate_population {c₀ : ℝ} (hc : 0 < c₀) (δ γ g n t : ℝ) :
    HasDerivAt (fun s => Real.log (marginalUtility δ γ c₀ (g - n) s))
      (-(δ + γ * (g - n))) t :=
  hasDerivAt_log_marginalUtility hc δ γ (g - n) t

/-- Cochrane (2023), p. 200: with population growth the transversality condition for
per-capita debt in a steady ratio to per-capita consumption holds iff `r > g − n`, where
`r = δ + γ (g − n)`. -/
theorem tvc_population_iff {c₀ κ : ℝ} (hc : 0 < c₀) (hκ : 0 < κ) (δ γ g n : ℝ) :
    Tendsto (fun T => marginalUtility δ γ c₀ (g - n) T * (κ * consumption c₀ (g - n) T))
      atTop (𝓝 0) ↔ g - n < rate δ γ (g - n) :=
  tvc_iff hc hκ δ γ (g - n)

/-- Cochrane (2023), p. 200: with standard preferences (`δ > 0`, `γ = 1`), population growth
can deliver `r < g` for aggregate growth while the per-capita transversality condition holds:
`δ = 1%`, `g = 3%`, `n = 2%` give `r = 2% ∈ (g − n, g)`. -/
theorem population_allows_r_lt_g :
    rate (1 / 100) 1 (3 / 100 - 2 / 100) < 3 / 100 ∧
      3 / 100 - 2 / 100 < rate (1 / 100) 1 (3 / 100 - 2 / 100) := by
  unfold rate; norm_num

/-- Cochrane (2023), p. 200 ("population growth must eventually end"): with `n = 0` the
population formula reduces to (6.6). -/
theorem rate_population_zero (δ γ g : ℝ) : rate δ γ (g - 0) = rate δ γ g := by
  rw [sub_zero]

end Cochrane.FiscalConstraints.GrowthTheoryTVC
