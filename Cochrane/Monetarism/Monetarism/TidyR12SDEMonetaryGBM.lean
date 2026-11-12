/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR12SDEMonetary
import Monetarism.TidyR12SDEGBM
import Monetarism.TidyR9MonetarismItoPositive
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# A positive diffusive `Λ/P` with a KNOWN constant rate: the (1.32) step in a GBM economy

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.32) (Track 3, chunk B4). B1's positive economy
(`TidyR9MonetarismItoPositive.posModel`, `Λ/P = 2 + sin W`) used the random rate
`i = sin W/(2(2 + sin W))`, which that choice of `n` forces. Bounded coefficients do not force it
in general (on a bounded horizon `e^{−iu}(2 + e^{(u−T)/2} sin W_u)` is positive and diffusive with
constant `i`), but here the canonical lognormal `Λ/P` is used: with Itô processes with
mean-square continuous coefficients (`TidyR12SDEProcess.ItoProcessMS`) and geometric Brownian
motion (`TidyR12SDEGBM`) it has a known constant rate.

## The economy (`gbmModel`, on `bmPath` under `gaussSeq` with its natural filtration)

`P = 1`; **`Λ/P = n_u = n₀e^{−iu}exp(σW_u − σ²u/2)`** (`gbmΛ`, a geometric Brownian motion,
`dn = −i n dt + σ n dW`), positive, with a **constant known rate `i`**; bonds
`B = b₀ + c·arctan W` (`arcB`, bounded, diffusion `σ_B = c/(1 + W²)`, positive when `c > 0`);
money `M = M₀ − c·arctan W` (forced by (1.31): `B + M` riskless); `i^m = 0`; surplus `s = iB`.
The bracket density is `σ_Xσ_B = σc·n/(1 + W²)`, of the sign of `σc` on every path.

## Main results

* `gbmΛ_pos`, `gbm_condExp_bondPricing` (`E_s[n_t] = e^{−i(t − s)}n_s`: the bond-pricing condition
  `E_t d(Λ/P) = −i(Λ/P)dt` with the known rate), `gbmModel`.
* `itoProcess_affine_arctan`, `itoIntegrand_affine_arctan`: bonds and money.
* `gbm_bracket_ne` (`E[∫_s^t σ_Xσ_B du] ≠ 0` for `σc ≠ 0`), **`gbm_book_fails`** (the book's
  last line of (1.32) fails on EVERY `[s, t]`, `0 ≤ s < t`, for every `σ ≠ 0`, `c ≠ 0`),
  **`gbm_corrected`** (the corrected (1.32) holds), `gbm_book_holds_bv` (with `c = 0`, bonds
  constant, the book's line holds although `Λ/P` is diffusive), **`gbm_headline`**.
-/

namespace Cochrane.Monetarism.TidyR12SDEMonetaryGBM

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoSums Cochrane.Monetarism.TidyR7ItoIntegral
  Cochrane.Monetarism.TidyR7ItoUnbounded Cochrane.Monetarism.TidyR7ItoProducts
  Cochrane.Monetarism.TidyR7ItoProcess Cochrane.Monetarism.TidyR7ItoProductRule
  Cochrane.Monetarism.TidyR7ItoBondStep
  Cochrane.Monetarism.TidyR7MonetarismModel Cochrane.Monetarism.TidyR7MonetarismIto
  Cochrane.Monetarism.TidyR7MonetarismItoCex Cochrane.Monetarism.TidyR7BrownianExist
  Cochrane.Monetarism.TidyR7BrownianSchauder Cochrane.Monetarism.TidyR9ItoFormula
  Cochrane.Monetarism.TidyR12SDEProcess Cochrane.Monetarism.TidyR12SDEProductRule
  Cochrane.Monetarism.TidyR12SDEMonetary Cochrane.Monetarism.TidyR12SDEGBM
open scoped ENNReal NNReal

/-! ## Bonds `b₀ + c·arctan W` -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `(1 + x²)⁻¹` has derivative `−2x/(1 + x²)²`. -/
lemma hasDerivAt_inv_one_add_sq (x : ℝ) :
    HasDerivAt (fun x : ℝ => (1 + x ^ 2)⁻¹) (-(2 * x) / (1 + x ^ 2) ^ 2) x := by
  have hne : (1 : ℝ) + x ^ 2 ≠ 0 := by positivity
  have h := ((hasDerivAt_pow 2 x).const_add 1).inv hne
  refine h.congr_deriv ?_
  push_cast
  ring

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `|2x| ≤ (1 + x²)²`, so `|−2x/(1 + x²)²| ≤ 1`. -/
lemma abs_two_mul_div_le (x : ℝ) : |-(2 * x) / (1 + x ^ 2) ^ 2| ≤ 1 := by
  have hpos : (0 : ℝ) < (1 + x ^ 2) ^ 2 := by positivity
  rw [abs_div, abs_of_pos hpos, div_le_one hpos, abs_neg]
  have h1 : |2 * x| ≤ 1 + x ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1)]
  nlinarith [sq_nonneg x]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `0 < (1 + x²)⁻¹ ≤ 1`. -/
lemma inv_one_add_sq_bounds (x : ℝ) : 0 < (1 + x ^ 2)⁻¹ ∧ (1 + x ^ 2)⁻¹ ≤ 1 :=
  ⟨by positivity, inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])⟩

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (bonds with positive diffusion): `a₀ + c·arctan W`
is an Itô process** on every `[s, t]`, `0 ≤ s`, for a Brownian motion with continuous paths:
drift `c·(−2W/(1 + W²)²)/2`, diffusion `c(1 + W²)⁻¹` (`TidyR9ItoFormula.itoProcess_comp`). -/
theorem itoProcess_affine_arctan {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ} {s t : ℝ} (hBM : IsPreBrownianReal W μ)
    (hWm : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration μ W 𝓕)
    (hcont : ∀ ω, Continuous fun t => W t ω) (hs : 0 ≤ s) (a0 c : ℝ) :
    ItoProcess μ 𝓕 W (fun u ω => a0 + c * Real.arctan (bmReal W u ω))
      (fun u ω => c * (-(2 * bmReal W u ω) / (1 + bmReal W u ω ^ 2) ^ 2) / 2)
      (fun u ω => c * (1 + bmReal W u ω ^ 2)⁻¹) s t (|c| / 2) |c| := by
  have h := itoProcess_comp (t := t) hBM hWm h𝓕 hs (itoProcess_bm hBM hWm h𝓕 hs)
    (ae_of_all _ fun ω => (continuous_bmReal (hcont ω)).continuousOn)
    (f := fun x => a0 + c * Real.arctan x) (f' := fun x => c * (1 + x ^ 2)⁻¹)
    (f'' := fun x => c * (-(2 * x) / (1 + x ^ 2) ^ 2))
    (fun x => HasDerivAt.const_add a0 (HasDerivAt.const_mul c (Real.hasDerivAt_arctan' x)))
    (fun x => HasDerivAt.const_mul c (hasDerivAt_inv_one_add_sq x))
    (continuous_const.mul ((continuous_const.mul continuous_id).neg.div (by fun_prop)
      fun x => by positivity)) (L1 := |c|) (L2 := |c|)
    (fun x => by
      rw [abs_mul, abs_of_pos (inv_one_add_sq_bounds x).1]
      exact mul_le_of_le_one_right (abs_nonneg _) (inv_one_add_sq_bounds x).2)
    (fun x => by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_two_mul_div_le x))
  have e1 : |c| * 0 + |c| / 2 * (1 * 1) = |c| / 2 := by ring
  have e2 : |c| * 1 = |c| := mul_one _
  rw [e1, e2] at h
  exact itoProcess_of_coeff_eq h (fun u ω => by ring) (fun u ω => by ring)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **`a₀ + c·arctan W` is a bounded admissible
integrand** (`|·| ≤ |a₀| + |c|π/2`, adapted, continuous paths). -/
theorem itoIntegrand_affine_arctan {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ} {s t : ℝ} (h𝓕 : BMFiltration μ W 𝓕)
    (hcont : ∀ ω, Continuous fun t => W t ω) (a0 c : ℝ) :
    ItoIntegrand μ 𝓕 (fun u ω => a0 + c * Real.arctan (bmReal W u ω)) s t
      (|a0| + |c| * (Real.pi / 2)) where
  adapted u _ := stronglyMeasurable_const.add (stronglyMeasurable_const.mul
    (Real.continuous_arctan.comp_stronglyMeasurable (h𝓕.adapted u)))
  bound u _ ω := by
    have h1 := Real.arctan_lt_pi_div_two (bmReal W u ω)
    have h2 := Real.neg_pi_div_two_lt_arctan (bmReal W u ω)
    have h3 : |Real.arctan (bmReal W u ω)| ≤ Real.pi / 2 := abs_le.2 ⟨h2.le, h1.le⟩
    calc |a0 + c * Real.arctan (bmReal W u ω)| ≤ |a0| + |c| * |Real.arctan (bmReal W u ω)| := by
          rw [← abs_mul]
          exact abs_add_le _ _
      _ ≤ |a0| + |c| * (Real.pi / 2) := by gcongr
  cont := ae_of_all _ fun ω =>
    (continuous_const.add (continuous_const.mul (Real.continuous_arctan.comp
      (continuous_bmReal (hcont ω))))).continuousOn

/-! ## The economy -/

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (the GBM economy): **`Λ/P = n₀e^{−iu}exp(σW_u −
σ²u/2)`**, geometric Brownian motion from `0` (`TidyR12SDEGBM.gbm` with `κ = −i − σ²/2`). -/
noncomputable abbrev gbmΛ (n0 ι σ : ℝ) : ℝ → (ℕ → ℝ) → ℝ :=
  gbm bmPath (fun _ => n0) 0 (-ι - σ ^ 2 / 2) σ

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (the GBM economy): bonds `B = b₀ + c·arctan W`. -/
noncomputable abbrev arcB (b0 c : ℝ) : ℝ → (ℕ → ℝ) → ℝ :=
  fun u ω => b0 + c * Real.arctan (bmReal bmPath u ω)

/-- Cochrane (2023), A1 §1.6, (1.31), p. 567 (the GBM economy): money `M = M₀ − c·arctan W`. -/
noncomputable abbrev arcM (M0 c : ℝ) : ℝ → (ℕ → ℝ) → ℝ :=
  fun u ω => M0 + -c * Real.arctan (bmReal bmPath u ω)

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (the GBM economy): the drift `c(−2W/(1+W²)²)/2` of
`b₀ + c·arctan W`. -/
noncomputable abbrev arcβ (c : ℝ) : ℝ → (ℕ → ℝ) → ℝ :=
  fun u ω => c * (-(2 * bmReal bmPath u ω) / (1 + bmReal bmPath u ω ^ 2) ^ 2) / 2

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (the GBM economy): the diffusion `c(1 + W²)⁻¹` of
`b₀ + c·arctan W`. -/
noncomputable abbrev arcσ (c : ℝ) : ℝ → (ℕ → ℝ) → ℝ :=
  fun u ω => c * (1 + bmReal bmPath u ω ^ 2)⁻¹

/-- Cochrane (2023), A1 §1.6, (1.31), p. 567 (the GBM economy): the surplus `s = iB`, so that
(1.31) holds with `β + m = 0`. -/
noncomputable abbrev arcSp (ι b0 c : ℝ) : ℝ → (ℕ → ℝ) → ℝ := fun u ω => ι * arcB b0 c u ω

/-- Cochrane (2023), A1 §1.6, p. 567: **`Λ/P > 0`** in the GBM economy (`n₀ > 0`), and
`Λ/P = Λ` (`P = 1`). -/
theorem gbmΛ_pos {n0 : ℝ} (hn0 : 0 < n0) (ι σ u : ℝ) (ω : ℕ → ℝ) :
    0 < gbmΛ n0 ι σ u ω ∧ disc (gbmΛ n0 ι σ) (constP 1) u ω = gbmΛ n0 ι σ u ω :=
  ⟨gbm_pos (fun _ => hn0) u ω, by simp [disc]⟩

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: bond pricing with the KNOWN rate**: in the GBM
economy `E_s[n_t] = e^{−i(t − s)}n_s` for `0 ≤ s ≤ t`, i.e. `E_t d(Λ/P) = −i(Λ/P)dt` with a
constant `i` (`TidyR12SDEGBM.condExp_gbm` restarted at `s`). -/
theorem gbm_condExp_bondPricing (n0 ι σ : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    gaussSeq[gbmΛ n0 ι σ t | bmF s] =ᵐ[gaussSeq]
      fun ω => Real.exp (-ι * (t - s)) * gbmΛ n0 ι σ s ω := by
  have := isProb
  have hBM := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hBM measurable_bmPath
  have hG := gbm_ms (κ := -ι - σ ^ 2 / 2) (σ := σ) hBM measurable_bmPath h𝓕 le_rfl
    (ξ := fun _ => n0) (memLp_const n0) stronglyMeasurable_const (s + t)
  have hξ : StronglyMeasurable[bmF s] (gbmΛ n0 ι σ s) := hG.adapted s ⟨hs, by linarith⟩
  have hξ2 : MemLp (gbmΛ n0 ι σ s) 2 gaussSeq := hG.memLp s ⟨hs, by linarith⟩
  have e : gbmΛ n0 ι σ t = gbm bmPath (gbmΛ n0 ι σ s) s (-ι - σ ^ 2 / 2) σ t :=
    funext fun ω => gbm_step (W := bmPath) (ξ := fun _ => n0) (s := 0) (κ := -ι - σ ^ 2 / 2)
      (σ := σ) s t ω
  rw [e]
  filter_upwards [condExp_gbm hBM measurable_bmPath h𝓕 hs hξ2 hξ hst] with ω h
  rw [h, congrFun gbm_self ω]
  ring_nf

/-- **Cochrane (2023), A1 §1.6, (1.31)–(1.32), pp. 567–568: the GBM economy is a model with
diffusive bonds and a positive, unbounded, diffusive `Λ/P` with a constant rate** on every
`[s, t]`, `0 ≤ s`: `P = 1`, `Λ/P = n₀e^{−iu}exp(σW_u − σ²u/2)` (drift `−i n`, diffusion `σn`),
`i` constant, `i^m = 0`, `s = iB`, `B = b₀ + c·arctan W`, `M = M₀ − c·arctan W`. -/
theorem gbmModel (n0 ι σ b0 c M0 : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ItoMonetaryModelMS gaussSeq bmF bmPath (gbmΛ n0 ι σ) (constP 1) (arcB b0 c) (arcM M0 c)
      (constP ι) (constP 0) (arcSp ι b0 c) (arcβ c) (arcσ c) (arcβ (-c)) (arcσ (-c))
      (fun u ω => σ * gbmΛ n0 ι σ u ω) s t (|b0| + |c| * (Real.pi / 2)) (|c| / 2) |c|
      (|-c| / 2) |-c| := by
  have := isProb
  have hBM := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hBM measurable_bmPath
  have hn := (gbm_itoProcessMS (κ := -ι - σ ^ 2 / 2) (σ := σ) hBM measurable_bmPath h𝓕 le_rfl
    (ξ := fun _ => n0) (memLp_const n0) stronglyMeasurable_const t).mono hBM
    measurable_bmPath h𝓕 le_rfl hs hst le_rfl
  exact
    { P_pos := fun _ _ => one_pos
      disc_ito := by
        have e1 : disc (gbmΛ n0 ι σ) (constP 1) = gbmΛ n0 ι σ :=
          funext fun u => funext fun ω => by simp [disc]
        rw [e1]
        have e2 : (fun u ω => -(constP ι u ω * gbmΛ n0 ι σ u ω)) =
            fun u ω => (-ι - σ ^ 2 / 2 + σ ^ 2 / 2) * gbmΛ n0 ι σ u ω :=
          funext fun u => funext fun ω => by simp only [constP]; ring
        rw [e2]
        exact hn
      bonds_ito := itoProcess_affine_arctan hBM measurable_bmPath h𝓕 continuous_bmPath hs b0 c
      bonds_bdd := itoIntegrand_affine_arctan h𝓕 continuous_bmPath b0 c
      money_ito := itoProcess_affine_arctan hBM measurable_bmPath h𝓕 continuous_bmPath hs M0 (-c)
      flow_drift := fun u ω => by
        simp only [flowRate, arcSp, constP]
        ring
      flow_diff := fun u ω => by ring }

/-! ## The bracket and the (1.32) step -/

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: the paths of `Λ/P` are continuous. -/
theorem continuous_gbmΛ (n0 ι σ : ℝ) (ω : ℕ → ℝ) : Continuous fun u => gbmΛ n0 ι σ u ω := by
  have h := continuous_bmReal (W := bmPath) (continuous_bmPath ω)
  simp only [gbmΛ, gbm, incr]
  fun_prop

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: **for every path, `∫_s^t n/(1 + W²) du > 0`**,
`s < t`. -/
theorem integral_gbm_bracket_pos {n0 : ℝ} (hn0 : 0 < n0) (ι σ : ℝ) {s t : ℝ} (hst : s < t)
    (ω : ℕ → ℝ) :
    0 < ∫ u in s..t, gbmΛ n0 ι σ u ω * (1 + bmReal bmPath u ω ^ 2)⁻¹ := by
  have hc : Continuous fun u => gbmΛ n0 ι σ u ω * (1 + bmReal bmPath u ω ^ 2)⁻¹ := by
    have h1 := continuous_gbmΛ n0 ι σ ω
    have h2 := continuous_bmReal (W := bmPath) (continuous_bmPath ω)
    exact h1.mul ((continuous_const.add (h2.pow 2)).inv₀ fun u =>
      (by positivity : (0 : ℝ) < 1 + bmReal bmPath u ω ^ 2).ne')
  refine intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable _ _)
    (fun u _ => mul_pos (gbmΛ_pos hn0 ι σ u ω).1 (inv_one_add_sq_bounds _).1) hst

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567 (the bracket of the GBM economy):**
`E[∫_s^t σ_Xσ_B du] = σc·E[∫_s^t n/(1 + W²) du]`, with `E[∫_s^t n/(1 + W²) du] > 0`; hence it is
nonzero whenever `σ ≠ 0`, `c ≠ 0`, `0 ≤ s < t`. -/
theorem gbm_bracket_ne {n0 : ℝ} (hn0 : 0 < n0) (ι : ℝ) {σ c : ℝ} (hσ : σ ≠ 0) (hc : c ≠ 0)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    ∫ ω, dtInt gaussSeq bmF (fun u ω => (fun u ω => σ * gbmΛ n0 ι σ u ω) u ω * arcσ c u ω) s t ω
      ∂gaussSeq ≠ 0 := by
  have := isProb
  have hBM := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hBM measurable_bmPath
  have hm := gbmModel n0 ι σ 0 c 0 hs hst.le
  have G5 := MSIntegrand.mul_itoIntegrand hm.disc_ito.diff hm.bonds_ito.diff
  set F : (ℕ → ℝ) → ℝ := fun ω => ∫ u in s..t, (σ * c) *
    (gbmΛ n0 ι σ u ω * (1 + bmReal bmPath u ω ^ 2)⁻¹) with hF
  have hcont : ∀ᵐ ω ∂gaussSeq, ContinuousOn (fun u => (fun u ω => σ * gbmΛ n0 ι σ u ω) u ω *
      arcσ c u ω) (Set.Icc s t) := ae_of_all _ fun ω => by
    have h1 := continuous_gbmΛ n0 ι σ ω
    have h2 := continuous_bmReal (W := bmPath) (continuous_bmPath ω)
    exact ((continuous_const.mul h1).mul (continuous_const.mul
      ((continuous_const.add (h2.pow 2)).inv₀ fun u =>
      (by positivity : (0 : ℝ) < 1 + bmReal bmPath u ω ^ 2).ne'))).continuousOn
  have hd := dtInt_ae_eq_integral hst.le G5 hcont
  have eF : dtInt gaussSeq bmF (fun u ω => (fun u ω => σ * gbmΛ n0 ι σ u ω) u ω * arcσ c u ω)
      s t =ᵐ[gaussSeq] F := by
    filter_upwards [hd] with ω h
    rw [h]
    exact intervalIntegral.integral_congr fun u _ => by simp only [arcσ]; ring
  have iF : Integrable F gaussSeq := ((memLp_dtInt G5).integrable one_le_two).congr eF
  set G : (ℕ → ℝ) → ℝ := fun ω => ∫ u in s..t,
    gbmΛ n0 ι σ u ω * (1 + bmReal bmPath u ω ^ 2)⁻¹ with hG
  have eFG : F = fun ω => (σ * c) * G ω := funext fun ω => by
    simp only [hF, hG]
    rw [intervalIntegral.integral_const_mul]
  have hσc : σ * c ≠ 0 := mul_ne_zero hσ hc
  have iG : Integrable G gaussSeq := by
    have h := iF.const_mul (σ * c)⁻¹
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only [eFG]
    field_simp
  have hGpos : 0 < ∫ ω, G ω ∂gaussSeq := by
    rw [integral_pos_iff_support_of_nonneg (fun ω => (integral_gbm_bracket_pos hn0 ι σ hst
      ω).le) iG]
    have e : Function.support G = Set.univ :=
      Set.eq_univ_of_forall fun ω => (integral_gbm_bracket_pos hn0 ι σ hst ω).ne'
    rw [e, measure_univ]
    exact one_pos
  rw [integral_congr_ae eF, eFG, integral_const_mul]
  exact mul_ne_zero hσc hGpos.ne'

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567 (counterexample with `Λ/P > 0` and a KNOWN
constant rate): the last line of (1.32) as printed fails** in the GBM economy on every `[s, t]`,
`0 ≤ s < t`, for every `σ ≠ 0` and `c ≠ 0`: `E_s[n_tB_t − n_sB_s]` is not a.s.
`−E_s[∫_s^t Λs du + ∫_s^t n dM]`.
Strengthens `TidyR9MonetarismItoPositive.pos_book_fails` (random rate, `[0, t]` only). -/
theorem gbm_book_fails {n0 : ℝ} (hn0 : 0 < n0) (ι b0 M0 : ℝ) {σ c : ℝ} (hσ : σ ≠ 0)
    (hc : c ≠ 0) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    ¬ (gaussSeq[fun ω => disc (gbmΛ n0 ι σ) (constP 1) t ω * arcB b0 c t ω
        - disc (gbmΛ n0 ι σ) (constP 1) s ω * arcB b0 c s ω | bmF s] =ᵐ[gaussSeq]
      gaussSeq[fun ω => -(dtInt gaussSeq bmF (fun u ω => gbmΛ n0 ι σ u ω * arcSp ι b0 c u ω
        - constP 0 u ω * disc (gbmΛ n0 ι σ) (constP 1) u ω * arcM M0 c u ω) s t ω
        + moneyInt gaussSeq bmF bmPath (gbmΛ n0 ι σ) (constP 1) (arcβ (-c)) (arcσ (-c)) s t ω)
        | bmF s]) := by
  have hBM := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hBM measurable_bmPath
  have hQ := gbm_bracket_ne hn0 ι hσ hc hs hst
  exact (gbmModel n0 ι σ b0 c M0 hs hst.le).incr_1_32_ms_book_fails hBM measurable_bmPath
    h𝓕 hs hst hQ

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the corrected (1.32) holds** in the GBM economy
on every `[s, t]`, `0 ≤ s < t`: the book's right-hand side plus the bracket
`E_s∫_s^t σ_Xσ_B du`, `σ_Xσ_B = σc·n/(1 + W²)`.
The instance of `TidyR12SDEMonetary.ItoMonetaryModelMS.incr_1_32_ms_general`. -/
theorem gbm_corrected (n0 ι σ b0 c M0 : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    gaussSeq[fun ω => disc (gbmΛ n0 ι σ) (constP 1) t ω * arcB b0 c t ω
        - disc (gbmΛ n0 ι σ) (constP 1) s ω * arcB b0 c s ω | bmF s] =ᵐ[gaussSeq]
      gaussSeq[fun ω => -(dtInt gaussSeq bmF (fun u ω => gbmΛ n0 ι σ u ω * arcSp ι b0 c u ω
        - constP 0 u ω * disc (gbmΛ n0 ι σ) (constP 1) u ω * arcM M0 c u ω) s t ω
        + moneyInt gaussSeq bmF bmPath (gbmΛ n0 ι σ) (constP 1) (arcβ (-c)) (arcσ (-c)) s t ω)
        + dtInt gaussSeq bmF (fun u ω => (fun u ω => σ * gbmΛ n0 ι σ u ω) u ω * arcσ c u ω)
          s t ω | bmF s] :=
  (gbmModel n0 ι σ b0 c M0 hs hst.le).incr_1_32_ms_general isPreBrownianReal_bmPath
    measurable_bmPath (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) hs hst

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: where the book's step holds**: with constant
bonds (`c = 0`, `σ_B = 0`) the last line of (1.32) as printed holds in the GBM economy although
`Λ/P` is diffusive (`TidyR12SDEMonetary.ItoMonetaryModelMS.incr_1_32_ms_uncorrelated`). -/
theorem gbm_book_holds_bv (n0 ι σ b0 M0 : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    gaussSeq[fun ω => disc (gbmΛ n0 ι σ) (constP 1) t ω * arcB b0 0 t ω
        - disc (gbmΛ n0 ι σ) (constP 1) s ω * arcB b0 0 s ω | bmF s] =ᵐ[gaussSeq]
      gaussSeq[fun ω => -(dtInt gaussSeq bmF (fun u ω => gbmΛ n0 ι σ u ω * arcSp ι b0 0 u ω
        - constP 0 u ω * disc (gbmΛ n0 ι σ) (constP 1) u ω * arcM M0 0 u ω) s t ω
        + moneyInt gaussSeq bmF bmPath (gbmΛ n0 ι σ) (constP 1) (arcβ (-0)) (arcσ (-0)) s t ω)
        | bmF s] :=
  (gbmModel n0 ι σ b0 0 M0 hs hst.le).incr_1_32_ms_uncorrelated isPreBrownianReal_bmPath
    measurable_bmPath (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) hs hst
    fun u _ ω => by simp only [arcσ]; ring

/-- **Cochrane (2023), A1 §1.6, (1.31)–(1.32), pp. 567–568: headline.** In the GBM economy
(`0 < n₀`, `σ ≠ 0`, `c ≠ 0`, `0 ≤ s < t`): `Λ/P > 0` everywhere, the bond-pricing condition holds
with the KNOWN constant rate `i` (`E_s n_t = e^{−i(t − s)}n_s`), the expected bracket
`E∫_s^t σ_Xσ_B du` is nonzero, the book's last line of (1.32) fails, and the corrected (1.32)
holds. The forced random rate of B1's positive economy is not needed.
The known-rate counterpart of `TidyR9MonetarismItoPositive.pos_headline`. -/
theorem gbm_headline {n0 : ℝ} (hn0 : 0 < n0) (ι b0 M0 : ℝ) {σ c : ℝ} (hσ : σ ≠ 0) (hc : c ≠ 0)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    (∀ u ω, 0 < disc (gbmΛ n0 ι σ) (constP 1) u ω) ∧
    (gaussSeq[gbmΛ n0 ι σ t | bmF s] =ᵐ[gaussSeq]
      fun ω => Real.exp (-ι * (t - s)) * gbmΛ n0 ι σ s ω) ∧
    (∫ ω, dtInt gaussSeq bmF (fun u ω => (fun u ω => σ * gbmΛ n0 ι σ u ω) u ω * arcσ c u ω)
      s t ω ∂gaussSeq ≠ 0) ∧
    (¬ (gaussSeq[fun ω => disc (gbmΛ n0 ι σ) (constP 1) t ω * arcB b0 c t ω
        - disc (gbmΛ n0 ι σ) (constP 1) s ω * arcB b0 c s ω | bmF s] =ᵐ[gaussSeq]
      gaussSeq[fun ω => -(dtInt gaussSeq bmF (fun u ω => gbmΛ n0 ι σ u ω * arcSp ι b0 c u ω
        - constP 0 u ω * disc (gbmΛ n0 ι σ) (constP 1) u ω * arcM M0 c u ω) s t ω
        + moneyInt gaussSeq bmF bmPath (gbmΛ n0 ι σ) (constP 1) (arcβ (-c)) (arcσ (-c)) s t ω)
        | bmF s])) ∧
    (gaussSeq[fun ω => disc (gbmΛ n0 ι σ) (constP 1) t ω * arcB b0 c t ω
        - disc (gbmΛ n0 ι σ) (constP 1) s ω * arcB b0 c s ω | bmF s] =ᵐ[gaussSeq]
      gaussSeq[fun ω => -(dtInt gaussSeq bmF (fun u ω => gbmΛ n0 ι σ u ω * arcSp ι b0 c u ω
        - constP 0 u ω * disc (gbmΛ n0 ι σ) (constP 1) u ω * arcM M0 c u ω) s t ω
        + moneyInt gaussSeq bmF bmPath (gbmΛ n0 ι σ) (constP 1) (arcβ (-c)) (arcσ (-c)) s t ω)
        + dtInt gaussSeq bmF (fun u ω => (fun u ω => σ * gbmΛ n0 ι σ u ω) u ω * arcσ c u ω)
          s t ω | bmF s]) :=
  ⟨fun u ω => by rw [(gbmΛ_pos hn0 ι σ u ω).2]; exact (gbmΛ_pos hn0 ι σ u ω).1,
    gbm_condExp_bondPricing n0 ι σ hs hst.le, gbm_bracket_ne hn0 ι hσ hc hs hst,
    gbm_book_fails hn0 ι b0 M0 hσ hc hs hst, gbm_corrected n0 ι σ b0 c M0 hs hst⟩

end Cochrane.Monetarism.TidyR12SDEMonetaryGBM
