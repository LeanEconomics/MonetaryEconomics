/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.TidyR7ItoDiscountFactor
import Generality.ContinuousLong

/-!
# `E_t[d(ΛW)] = 0` and `E_t[d(ΛV)] = −Λs dt` on the constructed Brownian motion

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.6, pp. 70–77, and
Online Appendix A1.4–A1.5, pp. 564–566. Non-vacuity of `TidyR7ItoDiscountFactor` on the
constructed motion `TidyR7BrownianExist.bmPath` (law `gaussSeq`, natural filtration `bmF`), and
its link with the deterministic results of `ContinuousLong` (`σ = 0`).

Both factors diffuse, with the same Brownian motion, and the bracket `d[Λ, V]` is not zero, so
these are genuinely stochastic instances. `ramp u = min 1 (max 0 (1 − u))` (`= 1 − u` on
`[0, 1]`, `0` after).

## Economy W (zero surplus: `E_t[d(ΛW)] = 0`)

`Λ_u = 1 − ∫_0^u ramp + I_u`, `W_u = 2 + ∫_0^u ramp + I_u`, `I_u = ∫_0^u φ dW` with
`φ = √((2 − ramp²)·ramp)`; drifts `∓ramp`, common diffusion `φ`. The pricing condition
`Λ a_W + W a_Λ + φ² = ramp·(Λ − W) + φ² = 0` holds because `W − Λ = 2 − ramp²` on `[0, ∞)`
(`wModel`). Then `E_0[Λ_1W_1 − Λ_0W_0] = 0` (`w_step`), checked directly:
`E[Λ_1W_1] = 2 = Λ_0W_0` (`w_expectation`, `w_initial`); the bracket is
`∫_0^1 φ² = 3/4` (`w_bracket`), so the bracket-free step fails (`w_bookForm_fails`).

## Economy V (surplus, infinite horizon, transversality holds)

`Λ_u = 3/4 + ∫_0^u (3/4)ramp² + I_u`, `V_u = 7/12 − ∫_0^u (3/4)ramp² − I_u`, `I = ∫ ramp dW`,
surplus `s = (3/2)ramp²`; `V + Λ = 4/3` makes the pricing condition exact (`vModel`). For
`T ≥ 1`: `E_0[Λ_TV_T] = 1·(1/3) − ∫_0^T ramp² = 0`, so **the transversality condition holds**
(`v_tvc`) and the valuation equation `Λ_0V_0 = lim E_0∫_0^{T_k} Λs = 7/16` holds
(`v_valuation`, `v_initial`) with a nonzero bracket `−1/3` (`v_bookForm_fails`).

## Link with the deterministic project (`σ = 0`)

`itoProcess_det`: a `C¹` path is an Itô process with zero diffusion. `recovers_Lambda_W_const`:
the stochastic `E_t[d(ΛW)] = 0` applied to deterministic `Λ' = −rΛ`, `W' = rW` gives
`Λ_tW_t = Λ_sW_s`, the statement `ContinuousLong.Lambda_W_const` (which it also restates);
`recovers_Lambda_flow`: for `V' = rV − s`, `Λ_tV_t − Λ_sV_s = −∫_s^t Λs`, the integrated form of
the first part of `ContinuousLong.Lambda_valuation`.
-/

namespace Cochrane.Generality.TidyR7ItoDiscountFactorCex

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Generality.TidyR7StieltjesSums Cochrane.Generality.TidyR7BrownianTools
  Cochrane.Generality.TidyR7BrownianQV Cochrane.Generality.TidyR7ItoL2
  Cochrane.Generality.TidyR7ItoSums Cochrane.Generality.TidyR7ItoIntegral
  Cochrane.Generality.TidyR7ItoUnbounded Cochrane.Generality.TidyR7ItoProducts
  Cochrane.Generality.TidyR7ItoProcess Cochrane.Generality.TidyR7ItoProductRule
  Cochrane.Generality.TidyR7ItoBondStep Cochrane.Generality.TidyR7ItoBridge
  Cochrane.Generality.TidyR7BrownianExist Cochrane.Generality.TidyR7BrownianSchauder
  Cochrane.Generality.TidyR7ItoDiscountFactor
open scoped ENNReal NNReal

/-! ## Generic test processes -/

/-- Cochrane (2023), §3.6, (3.44), p. 77 (`dx = μ dt + σ dz` with deterministic coefficients):
**`X_u = f(u) + c∫_0^u h dW` is an Itô process on `[s, t]`**, `0 ≤ s ≤ t`, with drift `g` and
diffusion `c h`, when `f(u) = f(s) + ∫_s^u g` on `[s, t]` and `g`, `h` are continuous and
bounded.
Generalises `TidyR7ItoProductRule.itoProcess_bm`. -/
theorem itoProcess_wiener {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ} {s t : ℝ} (hBM : IsPreBrownianReal W μ)
    (hWm : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s ≤ t)
    {f g h : ℝ → ℝ} {Cg Ch : ℝ} (c : ℝ) (hh : ContinuousOn h (Set.Icc 0 t))
    (hhb : ∀ u ∈ Set.Icc 0 t, |h u| ≤ Ch) (hg : ContinuousOn g (Set.Icc s t))
    (hgb : ∀ u ∈ Set.Icc s t, |g u| ≤ Cg)
    (hfg : ∀ u ∈ Set.Icc s t, f u = f s + ∫ r in s..u, g r) :
    ItoProcess μ 𝓕 W (fun u ω => f u + c * itoInt μ 𝓕 W (fun r _ => h r) 0 u ω)
      (fun u _ => g u) (fun u _ => c * h u) s t Cg (|c| * Ch) := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have hH : ItoIntegrand μ 𝓕 (fun r _ => h r) 0 t Ch := itoIntegrand_deterministic hh hhb
  exact
    { adapted := fun _ _ => stronglyMeasurable_const.add
        (stronglyMeasurable_const.mul stronglyMeasurable_itoInt)
      init := (memLp_const (f s)).add
        ((memLp_itoInt hBM hWm h𝓕 le_rfl (hH.mono le_rfl hst)).const_mul c)
      drift := itoIntegrand_deterministic hg hgb
      diff := (hH.mono hs le_rfl).const_mul c
      eq := fun u hu => by
        filter_upwards [itoInt_add_itoInt hBM hWm h𝓕 le_rfl hs hu.1 (hH.mono le_rfl hu.2),
          itoInt_const_mul hBM hWm h𝓕 hs (hH.mono hs hu.2) c] with ω h1 h2
        show f u + c * itoInt μ 𝓕 W (fun r _ => h r) 0 u ω =
          f s + c * itoInt μ 𝓕 W (fun r _ => h r) 0 s ω + (∫ r in s..u, g r)
            + itoInt μ 𝓕 W (fun u _ => c * h u) s u ω
        rw [h1, h2, hfg u hu]
        ring }

/-- Cochrane (2023), §3.6, (3.44), p. 77, with `σ = 0`: **a deterministic path is an Itô process
with zero diffusion** on `[s, t]`, `0 ≤ s`, drift `g`, when `f(u) = f(s) + ∫_s^u g` on `[s, t]`
and `g` is continuous and bounded.
Generalises `TidyR7ItoProductRule.itoProcess_id`. -/
theorem itoProcess_det {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ} {s t : ℝ} (hBM : IsPreBrownianReal W μ)
    (hWm : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) {f g : ℝ → ℝ}
    {Cg : ℝ} (hg : ContinuousOn g (Set.Icc s t)) (hgb : ∀ u ∈ Set.Icc s t, |g u| ≤ Cg)
    (hfg : ∀ u ∈ Set.Icc s t, f u = f s + ∫ r in s..u, g r) :
    ItoProcess μ 𝓕 W (fun u _ => f u) (fun u _ => g u) (fun _ _ => 0) s t Cg 0 := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  exact
    { adapted := fun _ _ => stronglyMeasurable_const
      init := memLp_const (f s)
      drift := itoIntegrand_deterministic hg hgb
      diff := itoIntegrand_const (c := fun _ => (0 : ℝ)) stronglyMeasurable_const
        (fun _ => by simp)
      eq := fun u hu => by
        filter_upwards [itoInt_const hBM hWm h𝓕 hs hu.1 (c := fun _ => (0 : ℝ))
          stronglyMeasurable_const (C := 0) (fun _ => by simp)] with ω hω
        show f u = f s + (∫ r in s..u, g r) + itoInt μ 𝓕 W (fun _ _ => (0 : ℝ)) s u ω
        rw [hω, hfg u hu]
        simp }

/-- Cochrane (2023), §3.6, (3.44), p. 77: a primitive `a + ∫_0^u g` of a continuous `g`
satisfies `f(u) = f(s) + ∫_s^u g`.
Restates Mathlib `intervalIntegral.integral_add_adjacent_intervals`. -/
theorem primitive_split (a : ℝ) {g : ℝ → ℝ} (hg : Continuous g) (s u : ℝ) :
    a + ∫ r in (0 : ℝ)..u, g r = (a + ∫ r in (0 : ℝ)..s, g r) + ∫ r in s..u, g r := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable 0 s)
    (hg.intervalIntegrable s u)]
  ring

/-! ## The probability space -/

/-- Cochrane (2023), §3.6, (3.44), p. 77: the natural filtration of the constructed Brownian
motion `bmPath`, indexed by `ℝ`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7MonetarismItoCex.bmF). -/
noncomputable abbrev bmF : Filtration ℝ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
  bmFiltrationReal bmPath measurable_bmPath

/-- Cochrane (2023), §3.6, (3.44), p. 77: `gaussSeq` is a probability measure.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7MonetarismItoCex.isProb). -/
theorem isProb : IsProbabilityMeasure gaussSeq :=
  isPreBrownianReal_bmPath.isGaussianProcess.isProbabilityMeasure

/-- Cochrane (2023), §3.6, p. 77: **`𝓕_0` is trivial** (`W_0 = 0`), so `E_0` is the expectation.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7MonetarismItoCexInf.bmF_zero). -/
theorem bmF_zero : bmF 0 = ⊥ := by
  change bmFiltration bmPath measurable_bmPath (0 : ℝ).toNNReal = ⊥
  rw [Real.toNNReal_zero, bmFiltration_eq_comap]
  have : (fun ω (r : Set.Iic (0 : ℝ≥0)) => bmPath r ω) = fun _ _ => 0 := by
    funext ω r
    have h : (r : ℝ≥0) = 0 := le_antisymm r.2 (by positivity)
    rw [h, bmPath_zero]
  rw [this]
  exact MeasurableSpace.comap_const _

/-! ## The ramp -/

/-- Cochrane (2023), §3.6, p. 77 (a test coefficient): `ramp u = min 1 (max 0 (1 − u))`. -/
noncomputable def ramp (u : ℝ) : ℝ := min 1 (max 0 (1 - u))

/-- Cochrane (2023), §3.6, p. 77: `ramp` is continuous. -/
theorem continuous_ramp : Continuous ramp :=
  continuous_const.min (continuous_const.max (continuous_const.sub continuous_id))

/-- Cochrane (2023), §3.6, p. 77: `0 ≤ ramp u ≤ 1`. -/
theorem ramp_mem (u : ℝ) : 0 ≤ ramp u ∧ ramp u ≤ 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

/-- Cochrane (2023), §3.6, p. 77: `ramp u = 1 − u` on `[0, 1]`. -/
theorem ramp_of_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : ramp u = 1 - u := by
  simp only [ramp, max_eq_right (by linarith : (0 : ℝ) ≤ 1 - u),
    min_eq_right (by linarith : 1 - u ≤ 1)]

/-- Cochrane (2023), §3.6, p. 77: `ramp u = 0` for `u ≥ 1`. -/
theorem ramp_of_ge {u : ℝ} (h1 : 1 ≤ u) : ramp u = 0 := by
  simp only [ramp, max_eq_left (by linarith : 1 - u ≤ 0), min_eq_right zero_le_one]

/-- Cochrane (2023), §3.6, p. 77: for `n ≥ 1` and `u ≥ 0`,
`∫_0^u ramp^n = (1 − ramp(u)^{n+1})/(n + 1)`. -/
theorem integral_ramp_pow {n : ℕ} (hn : n ≠ 0) {u : ℝ} (hu : 0 ≤ u) :
    ∫ r in (0 : ℝ)..u, ramp r ^ n = (1 - ramp u ^ (n + 1)) / (n + 1) := by
  have key : ∀ v, 0 ≤ v → v ≤ 1 →
      ∫ r in (0 : ℝ)..v, ramp r ^ n = (1 - (1 - v) ^ (n + 1)) / (n + 1) := by
    intro v hv0 hv1
    have e : ∫ r in (0 : ℝ)..v, ramp r ^ n = ∫ r in (0 : ℝ)..v, (1 - r) ^ n := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [Set.uIcc_of_le hv0] at hr
      simp only [ramp_of_le hr.1 (hr.2.trans hv1)]
    rw [e, intervalIntegral.integral_comp_sub_left (fun x => x ^ n), integral_pow]
    simp
  rcases le_or_gt u 1 with hu1 | hu1
  · rw [key u hu hu1, ramp_of_le hu hu1]
  · have c : Continuous fun r => ramp r ^ n := continuous_ramp.pow n
    have h2 : ∫ r in (1 : ℝ)..u, ramp r ^ n = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun r hr => ?_]
      · simp
      · rw [Set.uIcc_of_le hu1.le] at hr
        simp only [ramp_of_ge hr.1, zero_pow hn]
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1) (c.intervalIntegrable _ _)
      (c.intervalIntegrable _ _), key 1 zero_le_one le_rfl, h2, ramp_of_ge hu1.le]
    simp

/-- Cochrane (2023), §3.6, p. 77: `∫_0^u ramp = (1 − ramp(u)²)/2` for `u ≥ 0`. -/
theorem integral_ramp {u : ℝ} (hu : 0 ≤ u) :
    ∫ r in (0 : ℝ)..u, ramp r = (1 - ramp u ^ 2) / 2 := by
  have h := integral_ramp_pow one_ne_zero hu
  simp only [pow_one] at h
  rw [h]
  norm_num

/-! ## Economy W: `E_t[d(ΛW)] = 0` with a nonzero bracket -/

/-- Cochrane (2023), A1.5, p. 566 (economy W): the common diffusion
`φ = √((2 − ramp²)·ramp)`. -/
noncomputable def phiW (u : ℝ) : ℝ := Real.sqrt ((2 - ramp u ^ 2) * ramp u)

/-- Cochrane (2023), A1.5, p. 566 (economy W): `φ² = (2 − ramp²)·ramp`. -/
theorem phiW_mul_self (u : ℝ) : phiW u * phiW u = (2 - ramp u ^ 2) * ramp u := by
  have h := ramp_mem u
  exact Real.mul_self_sqrt (mul_nonneg (by nlinarith) h.1)

/-- Cochrane (2023), A1.5, p. 566 (economy W): `φ` is continuous. -/
theorem continuous_phiW : Continuous phiW :=
  Real.continuous_sqrt.comp ((continuous_const.sub (continuous_ramp.pow 2)).mul continuous_ramp)

/-- Cochrane (2023), A1.5, p. 566 (economy W): `|φ| ≤ 2`. -/
theorem abs_phiW_le (u : ℝ) : |phiW u| ≤ 2 := by
  have h := ramp_mem u
  rw [phiW, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (Real.sqrt_le_left (by norm_num)).2 (by nlinarith)

/-- Cochrane (2023), A1.5, p. 566 (economy W): the discount factor
`Λ_u = 1 + ∫_0^u (−ramp) + ∫_0^u φ dW`. -/
noncomputable abbrev wΛ : ℝ → (ℕ → ℝ) → ℝ := fun u ω =>
  (1 + ∫ r in (0 : ℝ)..u, -ramp r) + 1 * itoInt gaussSeq bmF bmPath (fun r _ => phiW r) 0 u ω

/-- Cochrane (2023), A1.5, p. 566 (economy W): the cumulative return
`W_u = 2 + ∫_0^u ramp + ∫_0^u φ dW`. -/
noncomputable abbrev wW : ℝ → (ℕ → ℝ) → ℝ := fun u ω =>
  (2 + ∫ r in (0 : ℝ)..u, ramp r) + 1 * itoInt gaussSeq bmF bmPath (fun r _ => phiW r) 0 u ω

/-- **Cochrane (2023), A1.5, p. 566 (economy W): a zero-surplus pricing model on every
`[s, t]`, `0 ≤ s ≤ t`.** `Λ` (drift `−ramp`, diffusion `φ`) and `W` (drift `ramp`, diffusion
`φ`) satisfy `Λ a_W + W a_Λ + φ·φ = 0`: the book's `E_t[d(ΛW)] = 0`. -/
theorem wModel {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ItoDiscountModel gaussSeq bmF bmPath wΛ wW (fun u _ => -ramp u) (fun u _ => 1 * phiW u)
      (fun u _ => ramp u) (fun u _ => 1 * phiW u) (fun _ _ => 0) s t 1 (|1| * 2) 1
      (|1| * 2) := by
  have hBM := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hBM measurable_bmPath
  exact
    { lam_ito := itoProcess_wiener hBM measurable_bmPath h𝓕 hs hst 1
        continuous_phiW.continuousOn (fun u _ => abs_phiW_le u)
        continuous_ramp.neg.continuousOn
        (fun u _ => by rw [abs_neg, abs_of_nonneg (ramp_mem u).1]; exact (ramp_mem u).2)
        (fun u _ => primitive_split 1 continuous_ramp.neg s u)
      val_ito := itoProcess_wiener hBM measurable_bmPath h𝓕 hs hst 1
        continuous_phiW.continuousOn (fun u _ => abs_phiW_le u) continuous_ramp.continuousOn
        (fun u _ => by rw [abs_of_nonneg (ramp_mem u).1]; exact (ramp_mem u).2)
        (fun u _ => primitive_split 2 continuous_ramp s u)
      pricing := fun u hu ω => by
        have hu0 : 0 ≤ u := hs.trans hu.1
        simp only [wΛ, wW, intervalIntegral.integral_neg, integral_ramp hu0]
        linear_combination phiW_mul_self u }

/-- Cochrane (2023), A1.5, p. 566 (economy W): `Λ_0W_0 = 1·2 = 2`. -/
theorem w_initial (ω : ℕ → ℝ) : wΛ 0 ω * wW 0 ω = 2 := by
  simp only [wΛ, wW, intervalIntegral.integral_same, itoInt_of_le (le_refl (0 : ℝ)),
    Pi.zero_apply]
  norm_num

/-- **Cochrane (2023), A1.5, p. 566 (economy W, the theorem): `E_0[Λ_1W_1 − Λ_0W_0] = 0`** a.s.,
an instance of `TidyR7ItoDiscountFactor.ItoDiscountModel.step_W`. -/
theorem w_step :
    gaussSeq[fun ω => wΛ 1 ω * wW 1 ω - wΛ 0 ω * wW 0 ω | bmF 0] =ᵐ[gaussSeq] 0 :=
  (wModel le_rfl zero_le_one).step_W isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) le_rfl zero_lt_one

/-- Cochrane (2023), A1.5, p. 566 (economy W): the bracket `∫_0^1 φ·φ du = 2·(1/2) − 1/4 = 3/4`. -/
theorem w_bracket : ∫ u in (0 : ℝ)..1, 1 * phiW u * (1 * phiW u) = 3 / 4 := by
  have e : (fun u => 1 * phiW u * (1 * phiW u)) = fun u => 2 * ramp u ^ 1 - ramp u ^ 3 :=
    funext fun u => by linear_combination phiW_mul_self u
  have c1 : Continuous fun u => 2 * ramp u ^ 1 := (continuous_ramp.pow 1).const_mul 2
  have c3 : Continuous fun u => ramp u ^ 3 := continuous_ramp.pow 3
  rw [e, intervalIntegral.integral_sub (c1.intervalIntegrable _ _) (c3.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_ramp_pow one_ne_zero zero_le_one,
    integral_ramp_pow (by norm_num) zero_le_one, ramp_of_ge le_rfl]
  norm_num

/-- **Cochrane (2023), A1.5, p. 566 (economy W, direct check): `E[Λ_1W_1] = 2`.**
`Λ_1 = 1/2 + I_1`, `W_1 = 5/2 + I_1`, `E[I_1] = 0`, `E[I_1²] = ∫_0^1 φ² = 3/4` (Wiener isometry
`TidyR7ItoBridge.integral_itoInt_deterministic_sq`): `5/4 + 3/4 = 2 = Λ_0W_0`. -/
theorem w_expectation : ∫ ω, wΛ 1 ω * wW 1 ω ∂gaussSeq = 2 := by
  have := isProb
  have hBM := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hBM measurable_bmPath
  set I := itoInt gaussSeq bmF bmPath (fun r _ => phiW r) 0 1 with hI
  have hD : ItoIntegrand gaussSeq bmF (fun r _ => phiW r) 0 1 2 :=
    itoIntegrand_deterministic continuous_phiW.continuousOn fun u _ => abs_phiW_le u
  have mI : MemLp I 2 gaussSeq := memLp_itoInt hBM measurable_bmPath h𝓕 le_rfl hD
  have j1 : ∫ r in (0 : ℝ)..1, ramp r = 1 / 2 := by
    rw [integral_ramp zero_le_one, ramp_of_ge le_rfl]
    norm_num
  have e : (fun ω => wΛ 1 ω * wW 1 ω) = fun ω => 5 / 4 + 3 * I ω + I ω ^ 2 := by
    funext ω
    simp only [wΛ, wW, intervalIntegral.integral_neg, j1, ← hI]
    ring
  have i1 : Integrable I gaussSeq := mI.integrable one_le_two
  have i2 : Integrable (fun ω => I ω ^ 2) gaussSeq := mI.integrable_sq
  have hsq : ∫ ω, I ω ^ 2 ∂gaussSeq = 3 / 4 := by
    rw [hI, integral_itoInt_deterministic_sq hBM measurable_bmPath h𝓕 le_rfl zero_le_one
      continuous_phiW.continuousOn (fun u _ => abs_phiW_le u)]
    have := w_bracket
    simp only [one_mul] at this
    rw [← this]
    exact intervalIntegral.integral_congr fun u _ => by ring
  have h12 : Integrable (fun ω => (5 : ℝ) / 4 + 3 * I ω) gaussSeq :=
    (integrable_const _).add (i1.const_mul _)
  have hsplit : ∫ ω, ((5 : ℝ) / 4 + 3 * I ω + I ω ^ 2) ∂gaussSeq
      = 5 / 4 + 3 * (∫ ω, I ω ∂gaussSeq) + ∫ ω, I ω ^ 2 ∂gaussSeq := by
    rw [integral_add h12 i2, integral_add (integrable_const _) (i1.const_mul _),
      integral_const_mul]
    simp
  rw [e, hsplit, hsq, hI, integral_itoInt hBM measurable_bmPath h𝓕 le_rfl hD]
  norm_num

/-- **Cochrane (2023), A1.5, p. 566 (economy W): the step without the covariation term fails.**
`E_0[Λ_1W_1 − Λ_0W_0]` is not a.s. equal to `E_0[∫_0^1 Λ a_W du + ∫_0^1 W a_Λ du]`, because
the bracket `E_0[∫_0^1 φ·φ du] = 3/4 ≠ 0`
(`TidyR7ItoDiscountFactor.ItoDiscountModel.bookForm_iff`). -/
theorem w_bookForm_fails :
    ¬ (gaussSeq[fun ω => wΛ 1 ω * wW 1 ω - wΛ 0 ω * wW 0 ω | bmF 0] =ᵐ[gaussSeq]
      gaussSeq[fun ω => dtInt gaussSeq bmF (fun u ω => wΛ u ω * (fun u (_ : ℕ → ℝ) => ramp u) u ω)
          0 1 ω + dtInt gaussSeq bmF
          (fun u ω => wW u ω * (fun u (_ : ℕ → ℝ) => -ramp u) u ω) 0 1 ω | bmF 0]) := by
  have := isProb
  intro h
  have hiff := ((wModel le_rfl zero_le_one).bookForm_iff isPreBrownianReal_bmPath
    measurable_bmPath (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) le_rfl
    zero_lt_one).1 h
  have e : (fun _ : ℕ → ℝ => ∫ u in (0 : ℝ)..1, 1 * phiW u * (1 * phiW u)) =
      fun _ => (3 / 4 : ℝ) := funext fun _ => w_bracket
  beta_reduce at hiff
  rw [e, condExp_const ((bmF).le 0)] at hiff
  obtain ⟨ω, hω⟩ := hiff.exists
  norm_num at hω

/-! ## Economy V: surplus, infinite horizon, transversality -/

/-- Cochrane (2023), A1.5, p. 566 (economy V): the discount factor
`Λ_u = 3/4 + ∫_0^u (3/4)ramp² + ∫_0^u ramp dW`. -/
noncomputable abbrev vΛ : ℝ → (ℕ → ℝ) → ℝ := fun u ω =>
  (3 / 4 + ∫ r in (0 : ℝ)..u, 3 / 4 * ramp r ^ 2)
    + 1 * itoInt gaussSeq bmF bmPath (fun r _ => ramp r) 0 u ω

/-- Cochrane (2023), A1.5, p. 566 (economy V): the value of debt
`V_u = 7/12 − ∫_0^u (3/4)ramp² − ∫_0^u ramp dW` (so `V + Λ = 4/3`). -/
noncomputable abbrev vV : ℝ → (ℕ → ℝ) → ℝ := fun u ω =>
  (7 / 12 + ∫ r in (0 : ℝ)..u, -(3 / 4 * ramp r ^ 2))
    + -1 * itoInt gaussSeq bmF bmPath (fun r _ => ramp r) 0 u ω

/-- Cochrane (2023), A1.5, p. 566 (economy V): the surplus `s = (3/2)ramp²`. -/
noncomputable abbrev vSp : ℝ → (ℕ → ℝ) → ℝ := fun u _ => 3 / 2 * ramp u ^ 2

/-- **Cochrane (2023), A1.5, p. 566 (economy V): a pricing model with surplus on every
`[s, t]`, `0 ≤ s ≤ t`.** `Λ` (drift `(3/4)ramp²`, diffusion `ramp`), `V` (drift
`−(3/4)ramp²`, diffusion `−ramp`), `s = (3/2)ramp²`:
`Λ a_V + V a_Λ + σ_Λσ_V = (3/4)ramp²(V − Λ) − ramp² = −(3/2)ramp²Λ = −Λs` since `V + Λ = 4/3`. -/
theorem vModel {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ItoDiscountModel gaussSeq bmF bmPath vΛ vV (fun u _ => 3 / 4 * ramp u ^ 2)
      (fun u _ => 1 * ramp u) (fun u _ => -(3 / 4 * ramp u ^ 2)) (fun u _ => -1 * ramp u) vSp
      s t (3 / 4) (|1| * 1) (3 / 4) (|-1| * 1) := by
  have hBM := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hBM measurable_bmPath
  have c2 : Continuous fun u => 3 / 4 * ramp u ^ 2 := (continuous_ramp.pow 2).const_mul _
  have b2 : ∀ u, |3 / 4 * ramp u ^ 2| ≤ 3 / 4 := fun u => by
    have h := ramp_mem u
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have b1 : ∀ u, |ramp u| ≤ 1 := fun u => by
    rw [abs_of_nonneg (ramp_mem u).1]; exact (ramp_mem u).2
  exact
    { lam_ito := itoProcess_wiener hBM measurable_bmPath h𝓕 hs hst 1
        continuous_ramp.continuousOn (fun u _ => b1 u) c2.continuousOn (fun u _ => b2 u)
        (fun u _ => primitive_split (3 / 4) c2 s u)
      val_ito := itoProcess_wiener hBM measurable_bmPath h𝓕 hs hst (-1)
        continuous_ramp.continuousOn (fun u _ => b1 u) c2.neg.continuousOn
        (fun u _ => by rw [abs_neg]; exact b2 u)
        (fun u _ => primitive_split (7 / 12) c2.neg s u)
      pricing := fun u _ ω => by
        simp only [vΛ, vV, vSp, intervalIntegral.integral_neg]
        ring }

/-- Cochrane (2023), A1.5, p. 566 (economy V): `Λ_0V_0 = (3/4)(7/12) = 7/16`. -/
theorem v_initial (ω : ℕ → ℝ) : vΛ 0 ω * vV 0 ω = 7 / 16 := by
  simp only [vΛ, vV, intervalIntegral.integral_same, itoInt_of_le (le_refl (0 : ℝ)),
    Pi.zero_apply]
  norm_num

/-- Cochrane (2023), A1.5, p. 566 (economy V): `∫_0^T ramp² = 1/3` for `T ≥ 1`. -/
theorem integral_ramp_sq {T : ℝ} (hT : 1 ≤ T) : ∫ r in (0 : ℝ)..T, ramp r ^ 2 = 1 / 3 := by
  rw [integral_ramp_pow (by norm_num) (by linarith), ramp_of_ge hT]
  norm_num

/-- **Cochrane (2023), A1.5, p. 566 (economy V): `E[Λ_TV_T] = 1·(1/3) − ∫_0^T ramp² = 0`** for
`T ≥ 1` (Wiener isometry).
Uses `TidyR7ItoBridge.integral_itoInt_deterministic_sq`. -/
theorem v_tvc_value {T : ℝ} (hT : 1 ≤ T) : ∫ ω, vΛ T ω * vV T ω ∂gaussSeq = 0 := by
  have := isProb
  have hBM := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hBM measurable_bmPath
  have hT0 : (0 : ℝ) ≤ T := by linarith
  set I := itoInt gaussSeq bmF bmPath (fun r _ => ramp r) 0 T with hI
  have hD : ItoIntegrand gaussSeq bmF (fun r _ => ramp r) 0 T 1 :=
    itoIntegrand_deterministic continuous_ramp.continuousOn fun u _ => by
      rw [abs_of_nonneg (ramp_mem u).1]; exact (ramp_mem u).2
  have mI : MemLp I 2 gaussSeq := memLp_itoInt hBM measurable_bmPath h𝓕 le_rfl hD
  have j : ∫ r in (0 : ℝ)..T, 3 / 4 * ramp r ^ 2 = 1 / 4 := by
    rw [intervalIntegral.integral_const_mul, integral_ramp_sq hT]
    norm_num
  have e : (fun ω => vΛ T ω * vV T ω) = fun ω => 1 / 3 + (-2 / 3) * I ω - I ω ^ 2 := by
    funext ω
    simp only [vΛ, vV, intervalIntegral.integral_neg, j, ← hI]
    ring
  have i1 : Integrable I gaussSeq := mI.integrable one_le_two
  have i2 : Integrable (fun ω => I ω ^ 2) gaussSeq := mI.integrable_sq
  have hsq : ∫ ω, I ω ^ 2 ∂gaussSeq = 1 / 3 := by
    rw [hI, integral_itoInt_deterministic_sq hBM measurable_bmPath h𝓕 le_rfl hT0
      continuous_ramp.continuousOn (fun u _ => by
        rw [abs_of_nonneg (ramp_mem u).1]; exact (ramp_mem u).2), integral_ramp_sq hT]
  have h12 : Integrable (fun ω => (1 : ℝ) / 3 + -2 / 3 * I ω) gaussSeq :=
    (integrable_const _).add (i1.const_mul _)
  have hsplit : ∫ ω, ((1 : ℝ) / 3 + -2 / 3 * I ω - I ω ^ 2) ∂gaussSeq
      = 1 / 3 + -2 / 3 * (∫ ω, I ω ∂gaussSeq) - ∫ ω, I ω ^ 2 ∂gaussSeq := by
    rw [integral_sub h12 i2, integral_add (integrable_const _) (i1.const_mul _),
      integral_const_mul]
    simp
  rw [e, hsplit, hsq, hI, integral_itoInt hBM measurable_bmPath h𝓕 le_rfl hD]
  norm_num

/-- **Cochrane (2023), A1.5, p. 566 (economy V): the transversality condition holds**,
`E_0[Λ_{T_k}V_{T_k}] = 0` for `T_k = k + 1`. -/
theorem v_tvc :
    ∀ᵐ ω ∂gaussSeq, Tendsto (fun k : ℕ => gaussSeq[fun ω => vΛ ((k : ℝ) + 1) ω
      * vV ((k : ℝ) + 1) ω | bmF 0] ω) atTop (𝓝 0) := by
  have := isProb
  refine ae_of_all _ fun ω => ?_
  have e : ∀ k : ℕ, gaussSeq[fun ω => vΛ ((k : ℝ) + 1) ω * vV ((k : ℝ) + 1) ω | bmF 0] ω
      = 0 := fun k => by
    rw [bmF_zero, condExp_bot, v_tvc_value (by have := k.cast_nonneg (α := ℝ); linarith)]
  simp_rw [e]
  exact tendsto_const_nhds

/-- **Cochrane (2023), (3.31)–(3.36), pp. 70–75, and A1.5, p. 566 (economy V): the valuation
equation `Λ_0V_0 = E_0∫_0^∞ Λ s` holds with diffusions**, in the limit form along
`T_k = k + 1`: `E_0[∫_0^{T_k} Λs du] → Λ_0V_0 = 7/16` a.s., an instance of
`TidyR7ItoDiscountFactor.ItoDiscountModel.valuation_seq` with the transversality condition
`v_tvc`. -/
theorem v_valuation :
    ∀ᵐ ω ∂gaussSeq, Tendsto (fun k : ℕ => gaussSeq[dtInt gaussSeq bmF
      (fun u ω => vΛ u ω * vSp u ω) 0 ((k : ℝ) + 1) | bmF 0] ω) atTop (𝓝 (7 / 16)) := by
  have h := (ItoDiscountModel.valuation_seq (CΛf := fun _ => 3 / 4) (CΛσf := fun _ => |1| * 1)
    (CVf := fun _ => 3 / 4) (CVσf := fun _ => |-1| * 1) (fun T hT => vModel le_rfl hT.le)
    isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) le_rfl
    (T := fun k : ℕ => (k : ℝ) + 1) (fun k => by positivity)).2 v_tvc
  filter_upwards [h] with ω hω
  rwa [v_initial] at hω

/-- Cochrane (2023), A1.5, p. 566 (economy V): the bracket `∫_0^1 σ_Λσ_V du = −∫_0^1 ramp² =
−1/3`. -/
theorem v_bracket : ∫ u in (0 : ℝ)..1, 1 * ramp u * (-1 * ramp u) = -(1 / 3) := by
  have e : (fun u => 1 * ramp u * (-1 * ramp u)) = fun u => -(ramp u ^ 2) :=
    funext fun u => by ring
  rw [e, intervalIntegral.integral_neg, integral_ramp_sq le_rfl]

/-- **Cochrane (2023), A1.5, p. 566 (economy V): the step without the covariation fails.**
`E_0[Λ_1V_1 − Λ_0V_0]` is not a.s. `E_0[∫_0^1 Λ a_V + ∫_0^1 V a_Λ]`: the bracket is `−1/3`. -/
theorem v_bookForm_fails :
    ¬ (gaussSeq[fun ω => vΛ 1 ω * vV 1 ω - vΛ 0 ω * vV 0 ω | bmF 0] =ᵐ[gaussSeq]
      gaussSeq[fun ω => dtInt gaussSeq bmF
          (fun u ω => vΛ u ω * (fun u (_ : ℕ → ℝ) => -(3 / 4 * ramp u ^ 2)) u ω) 0 1 ω
        + dtInt gaussSeq bmF
          (fun u ω => vV u ω * (fun u (_ : ℕ → ℝ) => 3 / 4 * ramp u ^ 2) u ω) 0 1 ω
          | bmF 0]) := by
  have := isProb
  intro h
  have hiff := ((vModel le_rfl zero_le_one).bookForm_iff isPreBrownianReal_bmPath
    measurable_bmPath (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) le_rfl
    zero_lt_one).1 h
  have e : (fun _ : ℕ → ℝ => ∫ u in (0 : ℝ)..1, 1 * ramp u * (-1 * ramp u)) =
      fun _ => (-(1 / 3) : ℝ) := funext fun _ => v_bracket
  beta_reduce at hiff
  rw [e, condExp_const ((bmF).le 0)] at hiff
  obtain ⟨ω, hω⟩ := hiff.exists
  norm_num at hω

/-! ## `σ = 0`: the deterministic results -/

/-- Cochrane (2023), (3.31)–(3.36), pp. 70–75 (`σ = 0`): a `C¹` path with continuous derivative
satisfies `f(u) = f(s) + ∫_s^u f'`.
Restates Mathlib `intervalIntegral.integral_eq_sub_of_hasDerivAt`. -/
theorem ftc_split {f f' : ℝ → ℝ} (hf : ∀ τ, HasDerivAt f (f' τ) τ) (hc : Continuous f')
    (s u : ℝ) : f u = f s + ∫ r in s..u, f' r := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hf x) (hc.intervalIntegrable _ _)]
  ring

/-- Cochrane (2023), (3.31)–(3.36), pp. 70–75 (`σ = 0`): a continuous function is bounded on a
compact interval.
Mathlib `IsCompact.exists_bound_of_continuousOn` on `isCompact_Icc`. -/
theorem exists_bound_Icc {g : ℝ → ℝ} (hg : Continuous g) (s t : ℝ) :
    ∃ C, ∀ u ∈ Set.Icc s t, |g u| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := g) hg.continuousOn
  exact ⟨C, fun u hu => by simpa [Real.norm_eq_abs] using hC u hu⟩

/-- **Cochrane (2023), A1.5, p. 566 (`σ = 0`): the stochastic `E_t[d(ΛW)] = 0` recovers
`ContinuousLong.Lambda_W_const`.** For deterministic `C¹` paths with `Λ' = −rΛ`, `W' = rW`
(`r` continuous), viewed as Itô processes with zero diffusion on the constructed motion,
`TidyR7ItoDiscountFactor.ItoDiscountModel.step_W` gives `Λ_tW_t = Λ_sW_s`, `0 ≤ s < t`; the
second conjunct is the same statement from `ContinuousLong.Lambda_W_const`. -/
theorem recovers_Lambda_W_const {r Λ W : ℝ → ℝ} (hr : Continuous r)
    (hΛ : ∀ τ, HasDerivAt Λ (-(r τ) * Λ τ) τ) (hW : ∀ τ, HasDerivAt W (r τ * W τ) τ) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s < t) :
    Λ t * W t = Λ s * W s ∧ Λ t * W t = Λ s * W s := by
  have := isProb
  have hBM := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hBM measurable_bmPath
  have cΛ : Continuous Λ := continuous_iff_continuousAt.2 fun τ => (hΛ τ).continuousAt
  have cW : Continuous W := continuous_iff_continuousAt.2 fun τ => (hW τ).continuousAt
  have gΛ : Continuous fun τ => -(r τ) * Λ τ := hr.neg.mul cΛ
  have gW : Continuous fun τ => r τ * W τ := hr.mul cW
  obtain ⟨C1, hC1⟩ := exists_bound_Icc gΛ s t
  obtain ⟨C2, hC2⟩ := exists_bound_Icc gW s t
  have hm : ItoDiscountModel gaussSeq bmF bmPath (fun u _ => Λ u) (fun u _ => W u)
      (fun u _ => -(r u) * Λ u) (fun _ _ => 0) (fun u _ => r u * W u) (fun _ _ => 0)
      (fun _ _ => 0) s t C1 0 C2 0 :=
    { lam_ito := itoProcess_det hBM measurable_bmPath h𝓕 hs gΛ.continuousOn hC1
        (fun u _ => ftc_split hΛ gΛ s u)
      val_ito := itoProcess_det hBM measurable_bmPath h𝓕 hs gW.continuousOn hC2
        (fun u _ => ftc_split hW gW s u)
      pricing := fun _ _ _ => by ring }
  refine ⟨?_, ?_⟩
  · have h := hm.step_W hBM measurable_bmPath h𝓕 hs hst
    rw [condExp_const ((bmF).le s)] at h
    obtain ⟨ω, hω⟩ := h.exists
    simp only [Pi.zero_apply] at hω
    linarith
  · exact ContinuousLong.Lambda_W_const cΛ.continuousOn cW.continuousOn
      (fun τ _ => hΛ τ) (fun τ _ => hW τ) hst.le

/-- **Cochrane (2023), A1.5, p. 566 (`σ = 0`): the stochastic `E_t[d(ΛV)] = −Λs dt` recovers the
deterministic flow `d(ΛV) = −Λs dt`** (the first part of `ContinuousLong.Lambda_valuation`), in
integrated form: for `C¹` paths with `Λ' = −rΛ`, `V' = rV − s` (`r`, `s` continuous),
`Λ_tV_t − Λ_sV_s = −∫_s^t Λ_u s_u du`, `0 ≤ s < t`. -/
theorem recovers_Lambda_flow {r sp Λ V : ℝ → ℝ} (hr : Continuous r) (hsp : Continuous sp)
    (hΛ : ∀ τ, HasDerivAt Λ (-(r τ) * Λ τ) τ) (hV : ∀ τ, HasDerivAt V (r τ * V τ - sp τ) τ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    Λ t * V t - Λ s * V s = -∫ u in s..t, Λ u * sp u := by
  have := isProb
  have hBM := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hBM measurable_bmPath
  have cΛ : Continuous Λ := continuous_iff_continuousAt.2 fun τ => (hΛ τ).continuousAt
  have cV : Continuous V := continuous_iff_continuousAt.2 fun τ => (hV τ).continuousAt
  have gΛ : Continuous fun τ => -(r τ) * Λ τ := hr.neg.mul cΛ
  have gV : Continuous fun τ => r τ * V τ - sp τ := (hr.mul cV).sub hsp
  obtain ⟨C1, hC1⟩ := exists_bound_Icc gΛ s t
  obtain ⟨C2, hC2⟩ := exists_bound_Icc gV s t
  have hm : ItoDiscountModel gaussSeq bmF bmPath (fun u _ => Λ u) (fun u _ => V u)
      (fun u _ => -(r u) * Λ u) (fun _ _ => 0) (fun u _ => r u * V u - sp u) (fun _ _ => 0)
      (fun u _ => sp u) s t C1 0 C2 0 :=
    { lam_ito := itoProcess_det hBM measurable_bmPath h𝓕 hs gΛ.continuousOn hC1
        (fun u _ => ftc_split hΛ gΛ s u)
      val_ito := itoProcess_det hBM measurable_bmPath h𝓕 hs gV.continuousOn hC2
        (fun u _ => ftc_split hV gV s u)
      pricing := fun _ _ _ => by ring }
  have h := hm.step hBM measurable_bmPath h𝓕 hs hst
  have hd := dtInt_ae_eq_integral (P := gaussSeq) (𝓕 := bmF) hst.le
    (hm.msIntegrand_lamSp hBM measurable_bmPath h𝓕 hs)
    (ae_of_all _ fun _ => (cΛ.mul hsp).continuousOn)
  have hneg : (fun ω => -dtInt gaussSeq bmF (fun u (_ : ℕ → ℝ) => Λ u * sp u) s t ω)
      =ᵐ[gaussSeq] fun _ => -∫ u in s..t, Λ u * sp u := by
    filter_upwards [hd] with ω hω
    rw [hω]
  have h2 := h.trans (condExp_congr_ae hneg)
  rw [condExp_const ((bmF).le s), condExp_const ((bmF).le s)] at h2
  obtain ⟨ω, hω⟩ := h2.exists
  exact hω

end Cochrane.Generality.TidyR7ItoDiscountFactorCex
