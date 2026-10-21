/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OpenEconomy.OptimalPolicy
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The welfare criterion of the small open economy

Galí (2015), Chapter 8, §8.4.3 (pp. 249–250), eqs. (43)–(44), and Appendix 8.1
(pp. 255–256), for the special case `σ = η = 1`, `Z ≡ 1`, around the efficient steady state
(the optimal subsidy `(1−τ)(1−υ)ℳ = 1` of `OptimalPolicy` in place).

## Main results

* **Lemma 1 and the analytic tools**: Lemma 1 is imported from `Supply` (`Supply.dispersion`,
  `Supply.bigTheta`, `Supply.crossVar`, `Supply.dispersion_second_order`:
  `d = (ε/(2Θ)) var_i p_H(i) + O(s³)`); restated from the Chapter 4 project here:
  `logPriceIndex_second_order`, `taylor_two`, `exp_taylor_two`, `bigO_mul`.
* **Exact layer.** `utility_exact`: with `U = log C − N^{1+φ}/(1+φ)`,
  `U(C e^ĉ, N e^n̂) − U(C, N) = ĉ − N^{1+φ}(e^{(1+φ)n̂} − 1)/(1+φ)` exactly; `marginal_utilities`
  (`U_c C = 1`, `U_n N = −N^{1+φ}`); `efficiency_iff` (`−U_n/U_c = (1−υ)(1−α)C/N` iff
  `N^{1+φ} = (1−υ)(1−α)`); `consumption_logdev` (`ĉ = (1−υ)ŷ + υŷ*` **exactly**, from
  `C = Y^{1−υ}(Y*)^υ`); `secondOrder_eq` (completing the square, exact identity with the
  explicit remainder `(1−υ)((ε/2Θ)v − d)`).
* **Analytic layer.** `period_utility_second_order`: along any one-parameter family of size `s`
  (`ŷ, â = O(s)`, `v = O(s²)`, Lemma 1 `d − (ε/2Θ)v = O(s³)`, exact employment identity
  `(1−α)n̂ = ŷ − â + d`), `(U_t − U)/(U_c C) = −((1−υ)/2)[(ε/Θ)v + ((1+φ)/(1−α))(ŷ − â)²]
  + t.i.p. + O(s³)`, with t.i.p. `= (1−υ)â + υŷ*` (world output enters only through
  t.i.p.).
* **The sign of `𝕎`** (survey error 1). `welfare_sign`: with `𝕎 ≡ −∑ βᵗ (U_t − U)/(U_c C)`,
  `𝕎 = +((1−υ)/2) ∑ βᵗ Q_t − ∑ βᵗ t.i.p._t`; `appendix_sign_error`: the displays of p. 255
  (last) and p. 256 (first), `𝕎 = −((1−υ)/2) …`, are false whenever the quadratic part is
  nonzero.
* **Lemma 2** (restated, exact for the Calvo cross-section, from the Chapter 4 project):
  `lemma2_hasSum`, `lemma2`, `lemma2_calvo`; `lemma2_printed_fails` (survey error 9): with an
  inherited dispersion `V_0 > 0` the printed equality fails by the policy-independent term
  `θV_0/(1−βθ)`, so Lemma 2 holds only up to t.i.p. (and with `π_H` replaced by `Δm`, which
  agrees to second order: `inflation_sq_sub_meanChange_sq`).
* **(43) and (44).** `welfare_eq_loss43`: exact given the Calvo recursion;
  `loss43_eq_pathLoss`, `loss43_weights_pos` connect (43) to `OptimalPolicy.optimal_policy`
  (SDIT minimises it); `welfare_stationary44`: the discounted loss of stationary variances is
  `𝕍/(1 − β)`, (44); `closed_economy_weights`: up to the factor `1 − υ` the weights are those
  of Ch. 4 with `σ = 1`.
* **`ỹ = (1−α)ñ`** (p. 256). `gap_eq_employment`: in the special case `yⁿ = a`, `nⁿ = 0`, and
  `ỹ = (1−α)ñ − d` exactly, i.e. `ỹ = (1−α)ñ` up to the second-order dispersion term.
-/

namespace Gali.OpenEconomy.Welfare

open MeasureTheory ProbabilityTheory Asymptotics Filter Topology
open Gali.OpenEconomy.Preferences.Variety (priceIndex)
open Gali.OpenEconomy.Supply (dispersion bigTheta crossVar priceIndex_family crossVar_family
  cgf_taylor_comp)

variable {G : Type*} [MeasurableSpace G]

/-! ### Lemma 1: price dispersion to second order

The dispersion term `Supply.dispersion`, `Supply.bigTheta`, `Supply.crossVar` and Lemma 1
(`Supply.dispersion_second_order`, with `Supply.cgf_taylor`, `Supply.priceIndex_family`,
`Supply.crossVar_family`, ...) are imported from `Supply` (restated there from the Chapter 3
project); the CES index is `Preferences.Variety.priceIndex`. -/

variable {μ : Measure G} {α ε : ℝ}

/-- Galí (2015), App. 4.1, p. 119 (Lemma 2's first-order link, the log index versus the mean):
along `p(i) = p̄ + s z(i)` the log CES price index satisfies
`log P(s) = E_i p(i) + ((1 − ε)/2) var_i p(i) + O(s³)`; in particular `log P − E_i p = O(s²)`. -/
theorem logPriceIndex_second_order [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ i, |z i| ≤ B) (hε : ε ≠ 1) (pbar : ℝ) :
    (fun s => Real.log (priceIndex μ ε (fun i => Real.exp (pbar + s * z i))) -
        (pbar + s * ∫ i, z i ∂μ) - (1 - ε) / 2 * crossVar μ (fun i => pbar + s * z i))
      =O[𝓝 0] fun s => s ^ 3 := by
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have heq : (fun s => Real.log (priceIndex μ ε (fun i => Real.exp (pbar + s * z i))) -
        (pbar + s * ∫ i, z i ∂μ) - (1 - ε) / 2 * crossVar μ (fun i => pbar + s * z i))
      = fun s => (1 - ε)⁻¹ * (cgf z μ ((1 - ε) * s) - (∫ i, z i ∂μ) * ((1 - ε) * s) -
          (∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) / 2 * ((1 - ε) * s) ^ 2) := by
    funext s
    rw [priceIndex_family hz hB hε, Real.log_exp, crossVar_family hz hB]
    field_simp
    ring
  rw [heq]
  exact (cgf_taylor_comp hz hB _).const_mul_left _

/-! ### Bookkeeping for orders of magnitude -/

/-- Orders of magnitude multiply: `f = O(sᵃ)` and `g = O(sᵇ)` give `f g = O(sᵃ⁺ᵇ)`
(used throughout App. 4.1, Galí 2015, pp. 117–119). -/
theorem bigO_mul {f g : ℝ → ℝ} {a b : ℕ} (hf : f =O[𝓝 0] fun s => s ^ a)
    (hg : g =O[𝓝 0] fun s => s ^ b) :
    (fun s => f s * g s) =O[𝓝 0] fun s => s ^ (a + b) := by
  have := hf.mul hg
  simpa [pow_add] using this

/-- Higher orders are smaller near `0`: `O(sᵇ) ⊆ O(sᵃ)` for `a ≤ b` (Galí 2015, App. 4.1,
"ignoring terms of third or higher order", p. 118). -/
theorem bigO_weaken {f : ℝ → ℝ} {a b : ℕ} (hab : a ≤ b) (hf : f =O[𝓝 0] fun s => s ^ b) :
    f =O[𝓝 0] fun s => s ^ a := by
  rcases hab.lt_or_eq with h | h
  · exact hf.trans (isLittleO_pow_pow h).isBigO
  · rw [h]
    exact hf

/-- A process that is `O(s)` tends to `0` (Galí 2015, App. 4.1: the economy stays in a
neighbourhood of the steady state). -/
theorem tendsto_zero_of_bigO {f : ℝ → ℝ} (hf : f =O[𝓝 0] fun s => s ^ 1) :
    Tendsto f (𝓝 0) (𝓝 0) := by
  have h : Tendsto (fun s : ℝ => s ^ 1) (𝓝 0) (𝓝 0) := by
    simp only [pow_one]
    exact tendsto_id
  exact hf.trans_tendsto h

/-! ### One-dimensional Taylor expansions -/

/-- Galí (2015), App. 4.1, p. 117 (**second-order Taylor expansion with a cubic remainder**):
if `f` is `C³` near `x₀`, then
`f x = f x₀ + f'(x₀)(x − x₀) + f''(x₀)/2 (x − x₀)² + O((x − x₀)³)`.
This is Mathlib's one-dimensional Taylor theorem (`taylor_isLittleO`) at order three on an open
ball, with the cubic Taylor term absorbed into the `O`. -/
theorem taylor_two {f : ℝ → ℝ} {x₀ : ℝ} (hf : ContDiffAt ℝ 3 f x₀) :
    (fun x => f x - f x₀ - deriv f x₀ * (x - x₀) - iteratedDeriv 2 f x₀ / 2 * (x - x₀) ^ 2)
      =O[𝓝 x₀] fun x => (x - x₀) ^ 3 := by
  obtain ⟨U, hU, hfU⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hU
  have hs : ContDiffOn ℝ 3 f (Metric.ball x₀ r) := hfU.mono hball
  have hT := taylor_isLittleO (convex_ball x₀ r) (Metric.mem_ball_self hr) hs
  rw [nhdsWithin_eq_nhds.2 (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))] at hT
  have hx0 := Metric.mem_ball_self hr (x := x₀)
  have e1 := iteratedDerivWithin_of_isOpen (n := 1) (f := f) Metric.isOpen_ball hx0
  have e2 := iteratedDerivWithin_of_isOpen (n := 2) (f := f) Metric.isOpen_ball hx0
  have e3 := iteratedDerivWithin_of_isOpen (n := 3) (f := f) Metric.isOpen_ball hx0
  have heq : (fun x => f x - f x₀ - deriv f x₀ * (x - x₀) -
      iteratedDeriv 2 f x₀ / 2 * (x - x₀) ^ 2)
      = fun x => (f x - taylorWithinEval f 3 (Metric.ball x₀ r) x₀ x) +
        iteratedDeriv 3 f x₀ / 6 * (x - x₀) ^ 3 := by
    funext x
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDerivWithin_zero, e1, e2,
      e3, iteratedDeriv_one, smul_eq_mul]
    norm_num [Nat.factorial]
    ring
  rw [heq]
  exact hT.isBigO.add ((isBigO_refl _ _).const_mul_left _)

/-- Galí (2015), App. 4.1, p. 117: `e^x = 1 + x + x²/2 + O(x³)`, the expansion behind
`(X_t − X)/X ≃ x_t + x_t²/2`. -/
theorem exp_taylor_two :
    (fun x => Real.exp x - 1 - x - x ^ 2 / 2) =O[𝓝 0] fun x => x ^ 3 := by
  have h := taylor_two (f := Real.exp) (x₀ := 0) Real.contDiff_exp.contDiffAt
  have h2 : iteratedDeriv 2 Real.exp 0 = 1 := by
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.exp_zero]
  simp only [Real.deriv_exp, Real.exp_zero, h2, sub_zero] at h
  convert h using 2 with x
  ring

/-- Galí (2015), App. 4.1, p. 117: `e^x − 1 = O(x)`. -/
theorem exp_sub_one_bigO : (fun x => Real.exp x - 1) =O[𝓝 0] fun x => x ^ 1 := by
  have h3 := bigO_weaken (by norm_num : 1 ≤ 3) exp_taylor_two
  have h1 : (fun x : ℝ => x) =O[𝓝 0] fun x => x ^ 1 := by simpa using isBigO_refl _ _
  have h2 : (fun x : ℝ => x ^ 2 / 2) =O[𝓝 0] fun x => x ^ 1 :=
    bigO_weaken (by norm_num : 1 ≤ 2) ((isBigO_refl _ _).const_mul_left (1 / 2) |>.congr_left
      (fun x => by ring))
  have := (h3.add h1).add h2
  refine this.congr_left fun x => ?_
  ring

/-! ### Lemma 2: the exact Calvo cross-section -/

/-- Galí (2015), p. 119 (Lemma 2 setting): a cross-sectional distribution of log prices is
admissible when it is a probability measure with finite first and second moments. -/
def GoodDist (ν : Measure ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ Integrable (fun x => x) ν ∧ Integrable (fun x => x ^ 2) ν

/-- Galí (2015), p. 119: the cross-sectional mean of log prices `m = ∫ p ν(dp)`. -/
noncomputable def crossMean (ν : Measure ℝ) : ℝ := ∫ x, x ∂ν

/-- Galí (2015), p. 119: the cross-sectional variance of log prices `var_i p(i)`. -/
noncomputable def crossVarDist (ν : Measure ℝ) : ℝ := ∫ x, (x - crossMean ν) ^ 2 ∂ν

/-- Galí (2015), App. 3.2–3.3 and p. 119: the Calvo law of motion of the cross-section of log
prices, `ν_t = θ ν_{t−1} + (1 − θ) δ_{p*_t}` (derived from the firm-level model in the
Chapter 3 project, `dist_law_of_motion`). -/
noncomputable def calvoMix (θ : ℝ) (ν : Measure ℝ) (p : ℝ) : Measure ℝ :=
  ENNReal.ofReal θ • ν + ENNReal.ofReal (1 - θ) • Measure.dirac p

/-- Restated from the Chapter 3 project (`integral_calvo_mix`). Galí (2015), App. 3.2:
integrating against `θ ν + (1 − θ) δ_p` gives `θ ∫ f dν + (1 − θ) f(p)`. -/
theorem integral_calvoMix {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (p : ℝ)
    {f : ℝ → ℝ} (hf : Integrable f ν) :
    ∫ x, f x ∂(calvoMix θ ν p) = θ * ∫ x, f x ∂ν + (1 - θ) * f p := by
  have hd : Integrable f (Measure.dirac p) := integrable_dirac (by simp)
  rw [calvoMix, integral_add_measure (hf.smul_measure ENNReal.ofReal_ne_top)
      (hd.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul, smul_eq_mul]

/-- Galí (2015), p. 119: `var = E p² − (E p)²` for an admissible cross-section. -/
theorem crossVarDist_eq {ν : Measure ℝ} (hg : GoodDist ν) :
    crossVarDist ν = ∫ x, x ^ 2 ∂ν - crossMean ν ^ 2 := by
  obtain ⟨hp, h1, h2⟩ := hg
  have hpt : ∀ x, (x - crossMean ν) ^ 2 = x ^ 2 + (-2 * crossMean ν) * x + crossMean ν ^ 2 :=
    fun x => by ring
  unfold crossVarDist
  simp_rw [hpt]
  have e1 := integral_add (μ := ν) (f := fun x => x ^ 2 + (-2 * crossMean ν) * x)
    (g := fun _ => crossMean ν ^ 2) (h2.add (h1.const_mul _)) (integrable_const _)
  have e2 := integral_add (μ := ν) (f := fun x => x ^ 2) (g := fun x => (-2 * crossMean ν) * x)
    h2 (h1.const_mul _)
  rw [e1, e2, integral_const_mul, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  unfold crossMean
  ring

/-- Galí (2015), p. 119: the Calvo law of motion preserves admissibility. -/
theorem calvoMix_good {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (p : ℝ)
    (hg : GoodDist ν) : GoodDist (calvoMix θ ν p) := by
  obtain ⟨hp, hi1, hi2⟩ := hg
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · rw [calvoMix, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ,
      measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      ← ENNReal.ofReal_add h0 (by linarith)]
    simp
  · exact (hi1.smul_measure ENNReal.ofReal_ne_top).add_measure
      ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
  · exact (hi2.smul_measure ENNReal.ofReal_ne_top).add_measure
      ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)

/-- Galí (2015), p. 119 (exact): the cross-sectional mean moves as
`m_t = θ m_{t−1} + (1 − θ) p*_t`, i.e. `Δm_t = (1 − θ)(p*_t − m_{t−1})`. -/
theorem calvoMix_mean {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (p : ℝ)
    (hg : GoodDist ν) : crossMean (calvoMix θ ν p) = θ * crossMean ν + (1 - θ) * p := by
  unfold crossMean
  exact integral_calvoMix h0 h1 p hg.2.1

/-- Galí (2015), p. 119 (**exact variance recursion**):
`var_t = θ var_{t−1} + θ(1 − θ)(p*_t − m_{t−1})²`. -/
theorem calvoMix_var {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (p : ℝ)
    (hg : GoodDist ν) :
    crossVarDist (calvoMix θ ν p)
      = θ * crossVarDist ν + θ * (1 - θ) * (p - crossMean ν) ^ 2 := by
  rw [crossVarDist_eq (calvoMix_good h0 h1 p hg), crossVarDist_eq hg, calvoMix_mean h0 h1 p hg]
  have h2 : ∫ x, x ^ 2 ∂(calvoMix θ ν p) = θ * ∫ x, x ^ 2 ∂ν + (1 - θ) * p ^ 2 :=
    integral_calvoMix h0 h1 p hg.2.2
  rw [h2]
  ring

/-- Galí (2015), p. 119 (**exact, in terms of the change in the mean**): for `θ < 1`,
`var_t = θ var_{t−1} + (θ/(1 − θ)) (Δm_t)²` with `Δm_t = m_t − m_{t−1}`. -/
theorem calvoMix_var_meanChange {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (p : ℝ)
    (hg : GoodDist ν) :
    crossVarDist (calvoMix θ ν p)
      = θ * crossVarDist ν + θ / (1 - θ) * (crossMean (calvoMix θ ν p) - crossMean ν) ^ 2 := by
  rw [calvoMix_var h0 h1.le p hg, calvoMix_mean h0 h1.le p hg]
  have : (1 : ℝ) - θ ≠ 0 := by linarith
  field_simp
  ring

/-- Galí (2015), p. 119: along a Calvo sequence `ν_{t+1} = θ ν_t + (1 − θ) δ_{p*_t}` started
from an admissible `ν_0`, every cross-section is admissible. -/
theorem calvo_good {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {ν : ℕ → Measure ℝ} {pstar : ℕ → ℝ}
    (hν : ∀ t, ν (t + 1) = calvoMix θ (ν t) (pstar t)) (hg : GoodDist (ν 0)) :
    ∀ t, GoodDist (ν t) := by
  intro t
  induction t with
  | zero => exact hg
  | succ t ih =>
    rw [hν t]
    exact calvoMix_good h0 h1 _ ih

/-- Galí (2015), p. 119 (**exact recursion along the Calvo sequence**; index `t + 1` is the
book's `t`, so `ν_0` is the inherited cross-section `ν_{−1}`):
`var_{t+1} = θ var_t + (θ/(1−θ))(m_{t+1} − m_t)²`. -/
theorem calvo_var_recursion {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) {ν : ℕ → Measure ℝ}
    {pstar : ℕ → ℝ} (hν : ∀ t, ν (t + 1) = calvoMix θ (ν t) (pstar t)) (hg : GoodDist (ν 0))
    (t : ℕ) :
    crossVarDist (ν (t + 1))
      = θ * crossVarDist (ν t) + θ / (1 - θ) * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2 := by
  rw [hν t]
  exact calvoMix_var_meanChange h0 h1 _ (calvo_good h0 h1.le hν hg t)

/-- Galí (2015), p. 119 (Lemma 2, partial sums): if `V_{t+1} = θ V_t + c q_t`, then
`∑_{t ≤ N} βᵗ V_{t+1} = θ V_0 + θβ ∑_{t < N} βᵗ V_{t+1} + c ∑_{t ≤ N} βᵗ q_t`. -/
theorem lemma2_partial {θ β c : ℝ} {V q : ℕ → ℝ} (hrec : ∀ t, V (t + 1) = θ * V t + c * q t)
    (N : ℕ) :
    ∑ t ∈ Finset.range (N + 1), β ^ t * V (t + 1)
      = θ * V 0 + θ * β * ∑ t ∈ Finset.range N, β ^ t * V (t + 1) +
        c * ∑ t ∈ Finset.range (N + 1), β ^ t * q t := by
  have h : ∀ t, β ^ (t + 1) * V (t + 1 + 1) = θ * β * (β ^ t * V (t + 1)) +
      c * (β ^ (t + 1) * q (t + 1)) := fun t => by
    rw [hrec (t + 1)]
    ring
  rw [Finset.sum_range_succ' (fun t => β ^ t * V (t + 1)),
    Finset.sum_range_succ' (fun t => β ^ t * q t), Finset.sum_congr rfl (fun t _ => h t),
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hrec 0]
  ring

/-- Galí (2015), p. 119: a variance recursion `V_{t+1} = θ V_t + c q_t` with nonnegative data
stays nonnegative. -/
theorem lemma2_nonneg {θ c : ℝ} {V q : ℕ → ℝ} (hθ : 0 ≤ θ) (hc : 0 ≤ c) (hV0 : 0 ≤ V 0)
    (hq : ∀ t, 0 ≤ q t) (hrec : ∀ t, V (t + 1) = θ * V t + c * q t) : ∀ t, 0 ≤ V t := by
  intro t
  induction t with
  | zero => exact hV0
  | succ t ih =>
    rw [hrec t]
    have := mul_nonneg hc (hq t)
    have := mul_nonneg hθ ih
    linarith

/-- Galí (2015), p. 119 (**Lemma 2, general form, exact**): if `V_{t+1} = θ V_t + c q_t`
with `θ, β, c ≥ 0`, `βθ < 1`, `V_0 ≥ 0`, `q ≥ 0` and `∑ βᵗ q_t` summable, then
`∑ βᵗ V_{t+1}` converges and equals `(θ V_0 + c ∑ βᵗ q_t)/(1 − βθ)`. The term `θ V_0` is the
inherited dispersion of Yun (2005), cited p. 116. -/
theorem lemma2_hasSum {θ β c : ℝ} {V q : ℕ → ℝ} (hθ : 0 ≤ θ) (hβ : 0 ≤ β) (hβθ : β * θ < 1)
    (hc : 0 ≤ c) (hV0 : 0 ≤ V 0) (hq : ∀ t, 0 ≤ q t)
    (hrec : ∀ t, V (t + 1) = θ * V t + c * q t) (hQ : Summable fun t => β ^ t * q t) :
    HasSum (fun t => β ^ t * V (t + 1))
      ((θ * V 0 + c * ∑' t, β ^ t * q t) / (1 - β * θ)) := by
  have hV := lemma2_nonneg hθ hc hV0 hq hrec
  have hf0 : ∀ t, 0 ≤ β ^ t * V (t + 1) := fun t => mul_nonneg (pow_nonneg hβ t) (hV _)
  have hq0 : ∀ t, 0 ≤ β ^ t * q t := fun t => mul_nonneg (pow_nonneg hβ t) (hq t)
  set Q := ∑' t, β ^ t * q t with hQdef
  have hQle : ∀ N, ∑ t ∈ Finset.range N, β ^ t * q t ≤ Q := fun N =>
    hQ.sum_le_tsum _ (fun i _ => hq0 i)
  have hpos : 0 < 1 - β * θ := by linarith
  have hQ0 : 0 ≤ Q := tsum_nonneg hq0
  have hbound : ∀ N, ∑ t ∈ Finset.range N, β ^ t * V (t + 1) ≤
      (θ * V 0 + c * Q) / (1 - β * θ) := by
    intro N
    cases N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact div_nonneg (add_nonneg (mul_nonneg hθ hV0) (mul_nonneg hc hQ0)) hpos.le
    | succ M =>
      rw [le_div_iff₀ hpos]
      have hp := lemma2_partial (β := β) hrec M
      have hmono : ∑ t ∈ Finset.range M, β ^ t * V (t + 1) ≤
          ∑ t ∈ Finset.range (M + 1), β ^ t * V (t + 1) := by
        rw [Finset.sum_range_succ]
        linarith [hf0 M]
      have h1 := mul_le_mul_of_nonneg_left hmono (mul_nonneg hθ hβ)
      have h2 := mul_le_mul_of_nonneg_left (hQle (M + 1)) hc
      nlinarith
  have hsum : Summable fun t => β ^ t * V (t + 1) := summable_of_sum_range_le hf0 hbound
  have hg : Summable fun t => β ^ t * V t := by
    refine (summable_nat_add_iff 1).1 ?_
    have : (fun t => β ^ (t + 1) * V (t + 1)) = fun t => β * (β ^ t * V (t + 1)) := by
      funext t
      ring
    rw [this]
    exact hsum.mul_left β
  have hg0 := hg.tsum_eq_zero_add
  have hshift : ∑' t, β ^ (t + 1) * V (t + 1) = β * ∑' t, β ^ t * V (t + 1) := by
    rw [← tsum_mul_left]
    congr 1
    funext t
    ring
  have hS : ∑' t, β ^ t * V (t + 1) = θ * ∑' t, β ^ t * V t + c * Q := by
    have : (fun t => β ^ t * V (t + 1)) = fun t => θ * (β ^ t * V t) + c * (β ^ t * q t) := by
      funext t
      rw [hrec t]
      ring
    rw [this, (hg.mul_left θ).tsum_add (hQ.mul_left c), tsum_mul_left, tsum_mul_left]
  rw [hg0, hshift] at hS
  simp only [pow_zero, one_mul] at hS
  have hval : ∑' t, β ^ t * V (t + 1) = (θ * V 0 + c * Q) / (1 - β * θ) := by
    rw [eq_div_iff hpos.ne']
    linarith
  rw [← hval]
  exact hsum.hasSum

/-- Galí (2015), p. 119 (**Lemma 2 as printed, exact**): with no inherited dispersion
(`V_0 = 0`, p. 102) and `V_{t+1} = θ V_t + (θ/(1−θ)) q_t`,
`∑ βᵗ V_{t+1} = θ/((1 − βθ)(1 − θ)) ∑ βᵗ q_t`. -/
theorem lemma2 {θ β : ℝ} {V q : ℕ → ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hV0 : V 0 = 0) (hq : ∀ t, 0 ≤ q t)
    (hrec : ∀ t, V (t + 1) = θ * V t + θ / (1 - θ) * q t) (hQ : Summable fun t => β ^ t * q t) :
    HasSum (fun t => β ^ t * V (t + 1))
      (θ / ((1 - β * θ) * (1 - θ)) * ∑' t, β ^ t * q t) := by
  have hβθ : β * θ < 1 := by nlinarith
  have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
  have h2 : 1 - β * θ ≠ 0 := by linarith
  have h := lemma2_hasSum hθ0 hβ0 hβθ (div_nonneg hθ0 (by linarith)) hV0.ge hq hrec hQ
  rw [hV0] at h
  convert h using 1
  field_simp
  ring

/-- Galí (2015), p. 119 (**Lemma 2 for the Calvo cross-section, exact in `Δm`**): along
`ν_{t+1} = θ ν_t + (1 − θ) δ_{p*_t}` from an admissible `ν_0` with inherited dispersion
`var ν_0`, `∑ βᵗ var_i p_{t+1}(i) = (θ var ν_0 + (θ/(1−θ)) ∑ βᵗ (Δm_t)²)/(1 − βθ)`. -/
theorem lemma2_calvo_inherited {θ β : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {ν : ℕ → Measure ℝ} {pstar : ℕ → ℝ}
    (hν : ∀ t, ν (t + 1) = calvoMix θ (ν t) (pstar t)) (hg : GoodDist (ν 0))
    (hQ : Summable fun t => β ^ t * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) :
    HasSum (fun t => β ^ t * crossVarDist (ν (t + 1)))
      ((θ * crossVarDist (ν 0) + θ / (1 - θ) *
        ∑' t, β ^ t * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) / (1 - β * θ)) := by
  have hβθ : β * θ < 1 := by nlinarith
  have hV0 : 0 ≤ crossVarDist (ν 0) := integral_nonneg fun x => sq_nonneg _
  have hc : (0 : ℝ) ≤ θ / (1 - θ) := div_nonneg hθ0 (by linarith)
  exact lemma2_hasSum (c := θ / (1 - θ)) (V := fun t => crossVarDist (ν t)) hθ0 hβ0 hβθ hc hV0
    (fun t => sq_nonneg _) (calvo_var_recursion hθ0 hθ1 hν hg) hQ

/-- Galí (2015), p. 119 (**Lemma 2 for the Calvo cross-section, as printed**): with no
inherited dispersion, `∑ βᵗ var_i p_t(i) = θ/((1−βθ)(1−θ)) ∑ βᵗ (Δm_t)²` exactly. -/
theorem lemma2_calvo {θ β : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {ν : ℕ → Measure ℝ} {pstar : ℕ → ℝ} (hν : ∀ t, ν (t + 1) = calvoMix θ (ν t) (pstar t))
    (hg : GoodDist (ν 0)) (hV0 : crossVarDist (ν 0) = 0)
    (hQ : Summable fun t => β ^ t * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) :
    HasSum (fun t => β ^ t * crossVarDist (ν (t + 1)))
      (θ / ((1 - β * θ) * (1 - θ)) *
        ∑' t, β ^ t * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) :=
  lemma2 (V := fun t => crossVarDist (ν t))
    (q := fun t => (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) hθ0 hθ1 hβ0 hβ1 hV0
    (fun _ => sq_nonneg _) (calvo_var_recursion hθ0 hθ1 hν hg) hQ

/-- Galí (2015), p. 119 (**`Δm_t = π_t` to first order**): for log-price families
`p_k(i) = p̄ + s z_k(i)` at two consecutive dates, inflation `π = log P_1 − log P_0` (CES
indices) and the change in the cross-sectional mean `Δm = E p_1 − E p_0` differ by `O(s²)`. -/
theorem inflation_sub_meanChange [IsProbabilityMeasure μ] {z₀ z₁ : G → ℝ} (hz₀ : Measurable z₀)
    (hz₁ : Measurable z₁) {B₀ B₁ : ℝ} (hB₀ : ∀ i, |z₀ i| ≤ B₀) (hB₁ : ∀ i, |z₁ i| ≤ B₁)
    (hε : ε ≠ 1) (pbar : ℝ) :
    (fun s => (Real.log (priceIndex μ ε (fun i => Real.exp (pbar + s * z₁ i))) -
        Real.log (priceIndex μ ε (fun i => Real.exp (pbar + s * z₀ i)))) -
        ((pbar + s * ∫ i, z₁ i ∂μ) - (pbar + s * ∫ i, z₀ i ∂μ))) =O[𝓝 0] fun s => s ^ 2 := by
  have hvar : ∀ {z : G → ℝ} {B : ℝ}, Measurable z → (∀ i, |z i| ≤ B) →
      (fun s => (1 - ε) / 2 * crossVar μ (fun i => pbar + s * z i)) =O[𝓝 0]
        fun s => s ^ 2 := fun {z} {B} hz hB => by
    have : (fun s => (1 - ε) / 2 * crossVar μ (fun i => pbar + s * z i))
        = fun s => ((1 - ε) / 2 * ∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) * s ^ 2 := by
      funext s
      rw [crossVar_family hz hB]
      ring
    rw [this]
    exact (isBigO_refl _ _).const_mul_left _
  have e₁ := (bigO_weaken (by norm_num : 2 ≤ 3)
    (logPriceIndex_second_order (μ := μ) hz₁ hB₁ hε pbar)).add
    (hvar hz₁ hB₁)
  have e₀ := (bigO_weaken (by norm_num : 2 ≤ 3)
    (logPriceIndex_second_order (μ := μ) hz₀ hB₀ hε pbar)).add
    (hvar hz₀ hB₀)
  refine (e₁.sub e₀).congr_left fun s => ?_
  ring

/-- Galí (2015), p. 119 (**`π_t² = (Δm_t)² + O(s³)`**): in the setting of
`inflation_sub_meanChange`, the squares of inflation and of the change in the cross-sectional
mean agree to second order, so Lemma 2 (exact in `Δm`) holds with `π` to second order. -/
theorem inflation_sq_sub_meanChange_sq [IsProbabilityMeasure μ] {z₀ z₁ : G → ℝ}
    (hz₀ : Measurable z₀) (hz₁ : Measurable z₁) {B₀ B₁ : ℝ} (hB₀ : ∀ i, |z₀ i| ≤ B₀)
    (hB₁ : ∀ i, |z₁ i| ≤ B₁) (hε : ε ≠ 1) (pbar : ℝ) :
    (fun s => (Real.log (priceIndex μ ε (fun i => Real.exp (pbar + s * z₁ i))) -
        Real.log (priceIndex μ ε (fun i => Real.exp (pbar + s * z₀ i)))) ^ 2 -
        ((pbar + s * ∫ i, z₁ i ∂μ) - (pbar + s * ∫ i, z₀ i ∂μ)) ^ 2) =O[𝓝 0]
      fun s => s ^ 3 := by
  have hD := inflation_sub_meanChange (μ := μ) hz₀ hz₁ hB₀ hB₁ hε pbar
  have hm : (fun s => (pbar + s * ∫ i, z₁ i ∂μ) - (pbar + s * ∫ i, z₀ i ∂μ)) =O[𝓝 0]
      fun s => s ^ 1 := by
    have : (fun s => (pbar + s * ∫ i, z₁ i ∂μ) - (pbar + s * ∫ i, z₀ i ∂μ))
        = fun s => ((∫ i, z₁ i ∂μ) - ∫ i, z₀ i ∂μ) * s ^ 1 := by
      funext s
      ring
    rw [this]
    exact (isBigO_refl _ _).const_mul_left _
  have hsum := (bigO_weaken (by norm_num : 1 ≤ 2) hD).add (hm.const_mul_left 2)
  refine (bigO_mul hD hsum).congr_left fun s => ?_
  ring


/-! ### App. 8.1: the exact layer (p. 255) -/

/-- Galí (2015), p. 233 (eq. (22)): `λ = (1 − θ)(1 − βθ)Θ/θ`, with `Θ = (1−α)/(1−α+αε)`. -/
noncomputable def lambdaH (β θ α ε : ℝ) : ℝ := (1 - θ) * (1 - β * θ) / θ * bigTheta α ε

/-- Galí (2015), App. 8.1, p. 255: period utility for `σ = 1`, `Z ≡ 1`,
`U(C, N) = log C − N^{1+φ}/(1+φ)`. -/
noncomputable def periodUtility (φ C N : ℝ) : ℝ := Real.log C - N ^ (1 + φ) / (1 + φ)

/-- Galí (2015), App. 8.1, p. 255: the marginal utilities `U_c = 1/C`, `U_n = −N^φ` (exact
derivatives), so `U_c C = 1` and `U_n N = −N^{1+φ}`. -/
theorem marginal_utilities {φ C N : ℝ} (hφ : 0 ≤ φ) (hC : 0 < C) (hN : 0 < N) :
    HasDerivAt (fun c => periodUtility φ c N) C⁻¹ C ∧
      HasDerivAt (fun n => periodUtility φ C n) (-(N ^ φ)) N ∧
      C⁻¹ * C = 1 ∧ -(N ^ φ) * N = -(N ^ (1 + φ)) := by
  refine ⟨(Real.hasDerivAt_log hC.ne').sub_const _, ?_, inv_mul_cancel₀ hC.ne', ?_⟩
  · have h2 : HasDerivAt (fun n : ℝ => n ^ (1 + φ) / (1 + φ)) (N ^ φ) N := by
      refine ((Real.hasDerivAt_rpow_const (p := 1 + φ) (Or.inr (by linarith))).div_const
        (1 + φ)).congr_deriv ?_
      rw [show (1 : ℝ) + φ - 1 = φ by ring]
      field_simp
    exact h2.const_sub (Real.log C)
  · rw [Real.rpow_add hN, Real.rpow_one]
    ring

/-- Galí (2015), App. 8.1, p. 255 (and p. 246): efficiency of the steady state,
`−U_n/U_c = (1−υ)(1−α) C/N` with `U_c = 1/C`, `U_n = −N^φ`, holds **iff**
`N^{1+φ} = (1−υ)(1−α)`. -/
theorem efficiency_iff {υ φ α C N : ℝ} (hC : 0 < C) (hN : 0 < N) :
    -(-(N ^ φ)) / C⁻¹ = (1 - υ) * (1 - α) * C / N ↔ N ^ (1 + φ) = (1 - υ) * (1 - α) := by
  rw [Real.rpow_add hN, Real.rpow_one, neg_neg, div_inv_eq_mul, eq_div_iff hN.ne']
  constructor
  · intro h
    have := mul_left_cancel₀ hC.ne' (by linear_combination h : C * (N ^ φ * N) =
      C * ((1 - υ) * (1 - α)))
    linear_combination this
  · intro h
    linear_combination C * h

/-- Galí (2015), App. 8.1, p. 255 (**exact**): with `C_t = C e^{ĉ}`, `N_t = N e^{n̂}`,
`U(C_t, N_t) − U(C, N) = ĉ − N^{1+φ}(e^{(1+φ)n̂} − 1)/(1+φ)`. -/
theorem utility_exact {φ C N : ℝ} (hC : 0 < C) (hN : 0 < N) (c n : ℝ) :
    periodUtility φ (C * Real.exp c) (N * Real.exp n) - periodUtility φ C N
      = c - N ^ (1 + φ) * (Real.exp ((1 + φ) * n) - 1) / (1 + φ) := by
  unfold periodUtility
  rw [Real.log_mul hC.ne' (Real.exp_pos c).ne', Real.log_exp,
    Real.mul_rpow hN.le (Real.exp_pos n).le, ← Real.exp_mul]
  rw [show n * (1 + φ) = (1 + φ) * n by ring]
  ring

/-- Galí (2015), App. 8.1, p. 255: `ĉ = (1 − υ)ŷ + υŷ*` holds **exactly** in log deviations
along the possibilities set `C = Y^{1−υ}(Y*)^υ` (`OptimalPolicy.consumption_possibilities`). -/
theorem consumption_logdev {υ Y Ys Yt Yst : ℝ} (hY : 0 < Y) (hYs : 0 < Ys) (hYt : 0 < Yt)
    (hYst : 0 < Yst) :
    Real.log (Yt ^ (1 - υ) * Yst ^ υ) - Real.log (Y ^ (1 - υ) * Ys ^ υ)
      = (1 - υ) * (Real.log Yt - Real.log Y) + υ * (Real.log Yst - Real.log Ys) := by
  rw [OptimalPolicy.log_consumption hYt hYst, OptimalPolicy.log_consumption hY hYs]
  ring

/-- Galí (2015), App. 8.1, p. 255 (**completing the square, exact**): if
`(1−α)n̂ = ŷ − â + d` (exact employment identity, `d` the dispersion term), then
`(1−υ)ŷ + υŷ* − (1−υ)(1−α)(n̂ + ((1+φ)/2)n̂²)
 = −((1−υ)/2)[(ε/Θ)v + (1+φ)(1−α)n̂²] + ((1−υ)â + υŷ*) + (1−υ)((ε/2Θ)v − d)`
for every `v`. The left side is the book's second-order polynomial with `U_c C = 1` and the
efficiency condition `U_n N = −(1−υ)(1−α)`. -/
theorem secondOrder_eq {υ φ α ε y ystar a n d v : ℝ} (hn : (1 - α) * n = y - a + d) :
    (1 - υ) * y + υ * ystar - (1 - υ) * (1 - α) * (n + (1 + φ) / 2 * n ^ 2)
      = -((1 - υ) / 2) * (ε / bigTheta α ε * v + (1 + φ) * (1 - α) * n ^ 2) +
          ((1 - υ) * a + υ * ystar) + (1 - υ) * (ε / (2 * bigTheta α ε) * v - d) := by
  linear_combination (-(1 - υ)) * hn

/-- Galí (2015), App. 8.1, p. 256: the employment term in output-gap form,
`(1+φ)(1−α)n̂² = ((1+φ)/(1−α))(ŷ − â + d)²` (exact, `α ≠ 1`). -/
theorem gap_form {φ α y a n d : ℝ} (hα : α ≠ 1) (hn : (1 - α) * n = y - a + d) :
    (1 + φ) * (1 - α) * n ^ 2 = (1 + φ) / (1 - α) * (y - a + d) ^ 2 := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  rw [← hn]
  field_simp

/-! ### App. 8.1: the analytic layer -/

/-- Galí (2015), App. 8.1, pp. 255–256 (**second-order approximation of period utility,
rigorous form**). Utility `log C − N^{1+φ}/(1+φ)` (`σ = 1`, `Z ≡ 1`; `U_c C = 1`), efficient
steady state `N^{1+φ} = (1−υ)(1−α)`, consumption on the possibilities set
`C_t = C e^{(1−υ)ŷ + υŷ*}`. Along a one-parameter family of size `s` with `ŷ, â = O(s)`, a
cross-sectional price variance `v = O(s²)`, Lemma 1 `d − (ε/2Θ)v = O(s³)` and the exact
employment identity `(1−α)n̂ = ŷ − â + d`:
`U_t − U = −((1−υ)/2)[(ε/Θ)v + ((1+φ)/(1−α))(ŷ − â)²] + ((1−υ)â + υŷ*) + O(s³)`.
No order assumption on `ŷ*` is needed: it enters only the terms independent of policy. -/
theorem period_utility_second_order {υ φ α ε C N : ℝ} {y ystar a n d v : ℝ → ℝ}
    (hC : 0 < C) (hN : 0 < N) (hEff : N ^ (1 + φ) = (1 - υ) * (1 - α)) (hφ : 0 ≤ φ)
    (hα : α ≠ 1) (hy : y =O[𝓝 0] fun s => s ^ 1) (ha : a =O[𝓝 0] fun s => s ^ 1)
    (hv : v =O[𝓝 0] fun s => s ^ 2)
    (hd : (fun s => d s - ε / (2 * bigTheta α ε) * v s) =O[𝓝 0] fun s => s ^ 3)
    (hn : ∀ s, (1 - α) * n s = y s - a s + d s) :
    (fun s => periodUtility φ (C * Real.exp ((1 - υ) * y s + υ * ystar s))
          (N * Real.exp (n s)) - periodUtility φ C N
        - (-((1 - υ) / 2) * (ε / bigTheta α ε * v s + (1 + φ) / (1 - α) * (y s - a s) ^ 2) +
          ((1 - υ) * a s + υ * ystar s)))
      =O[𝓝 0] fun s => s ^ 3 := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have hφ1 : (1 : ℝ) + φ ≠ 0 := by linarith
  set c := ε / (2 * bigTheta α ε) with hc
  have hd2 : d =O[𝓝 0] fun s => s ^ 2 :=
    ((bigO_weaken (by norm_num : 2 ≤ 3) hd).add (hv.const_mul_left c)).congr_left
      fun s => by ring
  have hd1 : d =O[𝓝 0] fun s => s ^ 1 := bigO_weaken (by norm_num) hd2
  have hn1 : n =O[𝓝 0] fun s => s ^ 1 :=
    (((hy.sub ha).add hd1).const_mul_left (1 - α)⁻¹).congr_left fun s => by
      rw [← hn s]
      field_simp
  have hx1 : (fun s => (1 + φ) * n s) =O[𝓝 0] fun s => s ^ 1 := hn1.const_mul_left _
  have cube : (fun s => ((1 + φ) * n s) ^ 3) =O[𝓝 0] fun s => s ^ 3 := by
    have := hx1.pow 3
    simpa [← pow_mul] using this
  have hR : (fun s => Real.exp ((1 + φ) * n s) - 1 - (1 + φ) * n s - ((1 + φ) * n s) ^ 2 / 2)
      =O[𝓝 0] fun s => s ^ 3 :=
    (exp_taylor_two.comp_tendsto (tendsto_zero_of_bigO hx1)).trans cube
  have T1 : (fun s => (1 - υ) * (c * v s - d s)) =O[𝓝 0] fun s => s ^ 3 :=
    (hd.neg_left.const_mul_left (1 - υ)).congr_left fun s => by ring
  have T2 := hR.const_mul_left (-(N ^ (1 + φ)) / (1 + φ))
  have T3 : (fun s => -((1 - υ) / 2) * ((1 + φ) / (1 - α)) *
      (2 * (y s - a s) * d s + d s ^ 2)) =O[𝓝 0] fun s => s ^ 3 := by
    have e1 : (fun s => 2 * (y s - a s) * d s) =O[𝓝 0] fun s => s ^ (1 + 2) :=
      (bigO_mul ((hy.sub ha).const_mul_left 2) hd2).congr_left fun s => by ring
    have e2 : (fun s => d s ^ 2) =O[𝓝 0] fun s => s ^ 3 :=
      bigO_weaken (by norm_num : 3 ≤ 2 + 2) ((bigO_mul hd2 hd2).congr_left fun s => by ring)
    exact (e1.add e2).const_mul_left _
  refine ((T1.add T2).add T3).congr_left fun s => ?_
  rw [utility_exact hC hN, hEff]
  have hns : n s = (y s - a s + d s) / (1 - α) := by
    rw [eq_div_iff h1]; linear_combination hn s
  generalize Real.exp ((1 + φ) * n s) = E
  rw [hns, hc]
  field_simp
  ring

/-! ### The sign of `𝕎` (survey error 1) -/

/-- Galí (2015), App. 8.1, pp. 255–256 (**the correct sign**): with
`𝕎 ≡ −∑ βᵗ (U_t − U)/(U_c C)` and `(U_t − U)/(U_c C) = −((1−υ)/2) Q_t + t.i.p._t`, the
welfare loss is `𝕎 = +((1−υ)/2) ∑ βᵗ Q_t − ∑ βᵗ t.i.p._t`. -/
theorem welfare_sign {υ β : ℝ} {dU Q tip : ℕ → ℝ}
    (hdU : ∀ t, dU t = -((1 - υ) / 2) * Q t + tip t) (hQ : Summable fun t => β ^ t * Q t)
    (hT : Summable fun t => β ^ t * tip t) :
    HasSum (fun t => -(β ^ t * dU t)) ((1 - υ) / 2 * ∑' t, β ^ t * Q t - ∑' t, β ^ t * tip t) := by
  have h := (hQ.hasSum.mul_left ((1 - υ) / 2)).sub hT.hasSum
  convert h using 1
  funext t
  rw [hdU t]
  ring

/-- Galí (2015), App. 8.1, p. 255 last display and p. 256 first display (**survey error 1**):
the printed `𝕎 = −((1−υ)/2) E₀ ∑ βᵗ […]` (up to t.i.p.) is false. For `υ < 1`, nonnegative
quadratic terms `Q_t` with `∑ βᵗ Q_t ≠ 0`, the true policy-dependent part of `𝕎` is
`+((1−υ)/2)∑ βᵗ Q_t > 0`, which differs from the printed `−((1−υ)/2)∑ βᵗ Q_t < 0`. -/
theorem appendix_sign_error {υ β : ℝ} {Q : ℕ → ℝ} (hυ : υ < 1) (hβ : 0 ≤ β)
    (hQ0 : ∀ t, 0 ≤ Q t) (hne : ∑' t, β ^ t * Q t ≠ 0) :
    0 < (1 - υ) / 2 * ∑' t, β ^ t * Q t ∧ -((1 - υ) / 2) * ∑' t, β ^ t * Q t < 0 ∧
      (1 - υ) / 2 * ∑' t, β ^ t * Q t ≠ -((1 - υ) / 2) * ∑' t, β ^ t * Q t := by
  have hS : 0 < ∑' t, β ^ t * Q t :=
    lt_of_le_of_ne (tsum_nonneg fun t => mul_nonneg (pow_nonneg hβ t) (hQ0 t)) (Ne.symm hne)
  have hp : 0 < (1 - υ) / 2 * ∑' t, β ^ t * Q t := mul_pos (by linarith) hS
  refine ⟨hp, by linarith, fun h => by linarith⟩

/-! ### Lemma 2 up to t.i.p. (survey error 9) -/

/-- Galí (2015), Lemma 2, p. 256 (**survey error 9**): the printed equality
`∑ βᵗ var_t = θ/((1−βθ)(1−θ)) ∑ βᵗ π²` fails as an exact statement once there is inherited
dispersion: with `V_0 > 0`, `θ > 0` the left side exceeds the right side by the
policy-independent term `θ V_0/(1 − βθ)` (and `π_H` must be read as `Δm`, to second order,
`inflation_sq_sub_meanChange_sq`). -/
theorem lemma2_printed_fails {θ β : ℝ} {V q : ℕ → ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hV0 : 0 < V 0) (hq : ∀ t, 0 ≤ q t)
    (hrec : ∀ t, V (t + 1) = θ * V t + θ / (1 - θ) * q t) (hQ : Summable fun t => β ^ t * q t) :
    ∑' t, β ^ t * V (t + 1)
        = θ / ((1 - β * θ) * (1 - θ)) * ∑' t, β ^ t * q t + θ * V 0 / (1 - β * θ) ∧
      ∑' t, β ^ t * V (t + 1) ≠ θ / ((1 - β * θ) * (1 - θ)) * ∑' t, β ^ t * q t := by
  have hβθ : β * θ < 1 := by nlinarith
  have h := lemma2_hasSum hθ0.le hβ0 hβθ (div_nonneg hθ0.le (by linarith)) hV0.le hq hrec hQ
  have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
  have h2 : 0 < 1 - β * θ := by linarith
  have e : ∑' t, β ^ t * V (t + 1)
      = θ / ((1 - β * θ) * (1 - θ)) * ∑' t, β ^ t * q t + θ * V 0 / (1 - β * θ) := by
    rw [h.tsum_eq]
    field_simp
    ring
  refine ⟨e, fun h' => ?_⟩
  rw [e] at h'
  have : 0 < θ * V 0 / (1 - β * θ) := div_pos (mul_pos hθ0 hV0) h2
  linarith

/-! ### The loss function (43) and the average loss (44) -/

/-- Galí (2015), eq. (43), p. 249: the period loss
`((1−υ)/2)[((1+φ)/(1−α)) ỹ² + (ε/λ) π_H²]`. -/
noncomputable def periodLoss43 (β θ υ φ α ε ygap inflH : ℝ) : ℝ :=
  (1 - υ) / 2 * ((1 + φ) / (1 - α) * ygap ^ 2 + ε / lambdaH β θ α ε * inflH ^ 2)

/-- Galí (2015), eq. (43), p. 249: `𝕎 = ∑ βᵗ ((1−υ)/2)[((1+φ)/(1−α)) ỹ_t² + (ε/λ) π_{H,t}²]`
for a given path. -/
noncomputable def loss43 (β θ υ φ α ε : ℝ) (ygap inflH : ℕ → ℝ) : ℝ :=
  ∑' t, β ^ t * periodLoss43 β θ υ φ α ε (ygap t) (inflH t)

/-- Galí (2015), App. 8.1, p. 256: `(ε/Θ) · θ/((1 − βθ)(1 − θ)) = ε/λ`. -/
theorem inflWeight_of_dispersion {β θ α ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβθ : β * θ < 1)
    (hα : α < 1) :
    ε / bigTheta α ε * (θ / ((1 - β * θ) * (1 - θ))) = ε / lambdaH β θ α ε := by
  have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
  have h2 : 1 - β * θ ≠ 0 := by linarith
  have h3 : (1 : ℝ) - α ≠ 0 := by linarith
  unfold lambdaH bigTheta
  field_simp

/-- Galí (2015), App. 8.1, p. 256 and eq. (43) (**exact given the Calvo recursion**): if the
cross-sectional variance of domestic prices follows `V_{t+1} = θV_t + (θ/(1−θ))(Δm_t)²` with
no inherited dispersion, then
`∑ βᵗ ((1−υ)/2)[((1+φ)/(1−α)) ỹ_t² + (ε/Θ) V_{t+1}] = 𝕎(ỹ, Δm)` of (43). -/
theorem welfare_eq_loss43 {β θ υ φ α ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hα : α < 1) {ygap Dm V : ℕ → ℝ} (hV0 : V 0 = 0)
    (hrec : ∀ t, V (t + 1) = θ * V t + θ / (1 - θ) * Dm t ^ 2)
    (hY : Summable fun t => β ^ t * ygap t ^ 2) (hD : Summable fun t => β ^ t * Dm t ^ 2) :
    HasSum (fun t => β ^ t * ((1 - υ) / 2 *
        ((1 + φ) / (1 - α) * ygap t ^ 2 + ε / bigTheta α ε * V (t + 1))))
      (loss43 β θ υ φ α ε ygap Dm) := by
  have hβθ : β * θ < 1 := by nlinarith
  have hL := lemma2 (q := fun t => Dm t ^ 2) hθ0.le hθ1 hβ0 hβ1 hV0 (fun _ => sq_nonneg _)
    hrec hD
  have hA := ((hY.hasSum.mul_left ((1 + φ) / (1 - α))).add
    (hL.mul_left (ε / bigTheta α ε))).mul_left ((1 - υ) / 2)
  have hB := ((hY.hasSum.mul_left ((1 + φ) / (1 - α))).add
    (hD.hasSum.mul_left (ε / lambdaH β θ α ε))).mul_left ((1 - υ) / 2)
  have hW : loss43 β θ υ φ α ε ygap Dm = (1 - υ) / 2 * ((1 + φ) / (1 - α) *
      ∑' t, β ^ t * ygap t ^ 2 + ε / lambdaH β θ α ε * ∑' t, β ^ t * Dm t ^ 2) := by
    rw [← hB.tsum_eq]
    unfold loss43 periodLoss43
    congr 1
    funext t
    ring
  rw [hW, ← inflWeight_of_dispersion hθ0 hθ1 hβθ hα]
  convert hA using 1
  · funext t
    ring
  · ring

/-- Galí (2015), eqs. (43)–(44), p. 249: the weights of (43) are positive for `υ < 1`,
`φ ≥ 0`, `0 ≤ α < 1`, `ε > 0`, `0 < θ < 1`, `β < 1`. -/
theorem loss43_weights_pos {β θ υ φ α ε : ℝ} (hυ : υ < 1) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hε : 0 < ε) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ1 : β < 1) :
    0 < (1 - υ) / 2 * ((1 + φ) / (1 - α)) ∧ 0 < (1 - υ) / 2 * (ε / lambdaH β θ α ε) := by
  have h1α : (0 : ℝ) < 1 - α := by linarith
  have hβθ : 0 < 1 - β * θ := by nlinarith
  have hΘ : 0 < bigTheta α ε := div_pos h1α (by nlinarith)
  have hl : 0 < lambdaH β θ α ε := mul_pos (div_pos (mul_pos (by linarith) hβθ) hθ0) hΘ
  exact ⟨mul_pos (by linarith) (div_pos (by linarith) h1α),
    mul_pos (by linarith) (div_pos hε hl)⟩

/-- Galí (2015), eq. (43), p. 249: (43) along a state `ω` is the loss `pathLoss a b β` of
`OptimalPolicy` with `a = ((1−υ)/2)(1+φ)/(1−α)`, `b = ((1−υ)/2)ε/λ`; hence
(`OptimalPolicy.optimal_policy`, `loss43_weights_pos`) SDIT minimises it. -/
theorem loss43_eq_pathLoss {Ω : Type*} (β θ υ φ α ε : ℝ) (ygap inflH : ℕ → Ω → ℝ) (ω : Ω) :
    loss43 β θ υ φ α ε (fun t => ygap t ω) (fun t => inflH t ω)
      = OptimalPolicy.pathLoss ((1 - υ) / 2 * ((1 + φ) / (1 - α)))
          ((1 - υ) / 2 * (ε / lambdaH β θ α ε)) β ygap inflH ω := by
  unfold loss43 periodLoss43 OptimalPolicy.pathLoss
  congr 1
  funext t
  ring

/-- Galí (2015), eq. (44), p. 249: the expected period loss
`𝕍 = ((1−υ)/2)[((1+φ)/(1−α)) var(ỹ) + (ε/λ) var(π_H)]`. -/
noncomputable def avgLoss44 (β θ υ φ α ε varY varPi : ℝ) : ℝ :=
  (1 - υ) / 2 * ((1 + φ) / (1 - α) * varY + ε / lambdaH β θ α ε * varPi)

/-- Galí (2015), eq. (44), p. 249 (**from (43) to (44)**): if the expected squared gap and
squared domestic inflation equal stationary variances at every date, the discounted expected
loss is `𝕍/(1 − β)`. -/
theorem welfare_stationary44 {β θ υ φ α ε varY varPi : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {eY eP : ℕ → ℝ} (heY : ∀ t, eY t = varY) (heP : ∀ t, eP t = varPi) :
    HasSum (fun t => β ^ t * ((1 - υ) / 2 * ((1 + φ) / (1 - α) * eY t +
        ε / lambdaH β θ α ε * eP t)))
      (avgLoss44 β θ υ φ α ε varY varPi / (1 - β)) := by
  have h := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right (avgLoss44 β θ υ φ α ε varY varPi)
  convert h using 1
  · funext t
    rw [heY, heP, avgLoss44]
  · rw [div_eq_inv_mul]

/-- Galí (2015), p. 249: "up to the multiplicative term `(1 − υ)`" the weights are those of the
closed economy (Ch. 4, p. 111) with `σ = 1`: `σ + (φ+α)/(1−α) = (1+φ)/(1−α)` at `σ = 1`. -/
theorem closed_economy_weights {φ α : ℝ} (hα : α ≠ 1) :
    1 + (φ + α) / (1 - α) = (1 + φ) / (1 - α) := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  field_simp
  ring

/-! ### `ỹ = (1 − α) ñ` (p. 256) -/

/-- Galí (2015), App. 8.1, p. 256: in the special case (`σ = η = 1`, `z = 0`) natural output
(35) is `yⁿ = Γ_a a + Γ_* y* = a`; at flexible prices there is no dispersion, so
`(1−α)nⁿ = yⁿ − a` gives `nⁿ = 0`; with `(1−α)n̂ = ŷ − â + d`,
`ỹ = ŷ − yⁿ = (1−α)(n̂ − nⁿ) − d` **exactly**, so the book's `ỹ = (1−α)ñ` holds up to the
second-order dispersion term `d`. -/
theorem gap_eq_employment {υ φ α a ystar yn nn y n d : ℝ} (hφ : 0 ≤ φ) (hα : α < 1)
    (hyn : yn = Supply.GammaA 1 1 υ φ α * a + Supply.GammaZ 1 1 υ φ α * 0 +
      Supply.GammaStar 1 1 υ φ α * ystar)
    (hnn : (1 - α) * nn = yn - a) (hn : (1 - α) * n = y - a + d) :
    yn = a ∧ nn = 0 ∧ y - yn = (1 - α) * (n - nn) - d := by
  obtain ⟨-, -, -, hA, hS, -, -⟩ := OptimalPolicy.special_case υ φ α hφ
  have hyn' : yn = a := by rw [hyn, hA, hS]; ring
  have hnn' : nn = 0 := by
    rw [hyn', sub_self] at hnn
    exact (mul_eq_zero.1 hnn).resolve_left (by linarith)
  refine ⟨hyn', hnn', ?_⟩
  rw [hyn', hnn']
  linear_combination -hn

end Gali.OpenEconomy.Welfare
