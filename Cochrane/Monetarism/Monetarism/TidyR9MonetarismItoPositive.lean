/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR9ItoFormulaVariants
import Monetarism.TidyR7MonetarismItoCex

/-!
# A positive diffusive `Λ/P` in the §1.6 economy: the book's (1.32) step fails with `Λ > 0`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). The counterexample economies of
`TidyR7MonetarismItoCex` used `Λ/P = 1 + W`, which is negative with positive probability (the
caveat stated there and in `TidyR8MonetarismItoDomInf`). With Itô's formula
(`TidyR9ItoFormula.itoProcess_comp`) a POSITIVE diffusive `Λ/P` with bounded coefficients is
available: `n = 2 + sin W ∈ [1, 3]`, drift `−½ sin W`, diffusion `cos W`.

## The economy (`posModel`, on `bmPath` under `gaussSeq` with its natural filtration)

`P = 1`, `Λ = Λ/P = 2 + sin W` (so `1 ≤ Λ ≤ 3`); the bond-pricing drift `−i n` of
`TidyR7MonetarismIto.ItoMonetaryModel` forces the **random adapted rate**
`i = sin W / (2(2 + sin W))` (`posI`, `|i| ≤ ½`); bonds `B = b + c sin W` (drift `−½c sin W`,
diffusion `c cos W`), money `M = M₀ − c sin W` (forced by (1.31): `B + M` riskless), `i^m = 0`,
surplus `s = iB` (so that (1.31) holds with `β + m = 0`). The bracket density is
`σ_Xσ_B = c cos²W`.

## Main results

* `posΛ_bounds`, `posI_bound`: `1 ≤ Λ/P = Λ ≤ 3`, `P = 1 > 0`, `|i| ≤ ½`.
* `posModel`: the economy is an `ItoMonetaryModel` on every `[s, t]`, `0 ≤ s`.
* `pos_bracket_pos` (`E∫_0^t σ_Xσ_B du = c E∫_0^t cos²W du`, nonzero for `c ≠ 0`, `t > 0`).
* `pos_book_fails` (**the book's last line of (1.32) fails on `[0, t]` with `Λ > 0` throughout**,
  for every `c ≠ 0`, `t > 0`); `pos_corrected` (the corrected (1.32) holds); `pos_1_34` ((1.34)'s
  line holds verbatim); `pos_headline`.
-/

namespace Cochrane.Monetarism.TidyR9MonetarismItoPositive

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoSums Cochrane.Monetarism.TidyR7ItoIntegral
  Cochrane.Monetarism.TidyR7ItoUnbounded Cochrane.Monetarism.TidyR7ItoProducts
  Cochrane.Monetarism.TidyR7ItoProcess Cochrane.Monetarism.TidyR7ItoProductRule
  Cochrane.Monetarism.TidyR7MonetarismModel Cochrane.Monetarism.TidyR7MonetarismIto
  Cochrane.Monetarism.TidyR7MonetarismItoCex Cochrane.Monetarism.TidyR7BrownianExist
  Cochrane.Monetarism.TidyR7BrownianSchauder Cochrane.Monetarism.TidyR9ItoFormula
  Cochrane.Monetarism.TidyR9ItoFormulaVariants
open scoped ENNReal NNReal

/-! ## `a + c sin W` -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (test processes for (1.32) via Itô's formula):
`a₀ + c sin W` is an Itô process** on every `[s, t]`, `0 ≤ s`, for a Brownian motion with
continuous paths: drift `−½c sin W`, diffusion `c cos W`.
Generalises `TidyR9ItoFormula.itoProcess_sin_bm`; the sine analogue of
`TidyR7MonetarismItoCex.itoProcess_affine`. -/
theorem itoProcess_affine_sin {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ} {s t : ℝ} (hBM : IsPreBrownianReal W μ)
    (hWm : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration μ W 𝓕)
    (hcont : ∀ ω, Continuous fun t => W t ω) (hs : 0 ≤ s) (a0 c : ℝ) :
    ItoProcess μ 𝓕 W (fun u ω => a0 + c * Real.sin (bmReal W u ω))
      (fun u ω => -(c * Real.sin (bmReal W u ω) / 2)) (fun u ω => c * Real.cos (bmReal W u ω))
      s t (|c| / 2) |c| := by
  have h := itoProcess_comp (t := t) hBM hWm h𝓕 hs (itoProcess_bm hBM hWm h𝓕 hs)
    (ae_of_all _ fun ω => (continuous_bmReal (hcont ω)).continuousOn)
    (f := fun x => a0 + c * Real.sin x) (f' := fun x => c * Real.cos x)
    (f'' := fun x => c * -Real.sin x)
    (fun x => HasDerivAt.const_add a0 (HasDerivAt.const_mul c (Real.hasDerivAt_sin x)))
    (fun x => HasDerivAt.const_mul c (Real.hasDerivAt_cos x))
    (continuous_const.mul Real.continuous_sin.neg) (L1 := |c|) (L2 := |c|)
    (fun x => by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one x))
    (fun x => by
      rw [abs_mul, abs_neg]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one x))
  have e1 : |c| * 0 + |c| / 2 * (1 * 1) = |c| / 2 := by ring
  have e2 : |c| * 1 = |c| := mul_one _
  rw [e1, e2] at h
  exact itoProcess_of_coeff_eq h (fun u ω => by ring) (fun u ω => by ring)

/-! ## The economy -/

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (positive counterexample): the SDF
`Λ = 2 + sin W` (with `P = 1`, `Λ/P = Λ ∈ [1, 3]`). -/
noncomputable abbrev posΛ : ℝ → (ℕ → ℝ) → ℝ := fun u ω => 2 + Real.sin (bmReal bmPath u ω)

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (positive counterexample): **the nominal rate**
`i = sin W/(2(2 + sin W))`, forced by the bond-pricing drift `E_t d(Λ/P) = −i(Λ/P) dt`. -/
noncomputable abbrev posI : ℝ → (ℕ → ℝ) → ℝ :=
  fun u ω => Real.sin (bmReal bmPath u ω) / (2 * (2 + Real.sin (bmReal bmPath u ω)))

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (positive counterexample): bonds `B = b + c sin W`. -/
noncomputable abbrev posB (b c : ℝ) : ℝ → (ℕ → ℝ) → ℝ :=
  fun u ω => b + c * Real.sin (bmReal bmPath u ω)

/-- Cochrane (2023), A1 §1.6, (1.31), p. 567 (positive counterexample): money
`M = M₀ − c sin W`. -/
noncomputable abbrev posM (M0 c : ℝ) : ℝ → (ℕ → ℝ) → ℝ :=
  fun u ω => M0 + -c * Real.sin (bmReal bmPath u ω)

/-- Cochrane (2023), A1 §1.6, (1.31), p. 567 (positive counterexample): the surplus `s = iB`
(interest on the debt), so that (1.31) holds with `β + m = 0`. -/
noncomputable abbrev posSp (b c : ℝ) : ℝ → (ℕ → ℝ) → ℝ := fun u ω => posI u ω * posB b c u ω

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **`1 ≤ Λ/P = Λ ≤ 3` and `P = 1 > 0`** in the positive
economy, for every time and state. -/
theorem posΛ_bounds (u : ℝ) (ω : ℕ → ℝ) :
    1 ≤ posΛ u ω ∧ posΛ u ω ≤ 3 ∧ disc posΛ (constP 1) u ω = posΛ u ω ∧ 0 < constP 1 u ω := by
  have h1 := Real.neg_one_le_sin (bmReal bmPath u ω)
  have h2 := Real.sin_le_one (bmReal bmPath u ω)
  refine ⟨by simp only [posΛ]; linarith, by simp only [posΛ]; linarith, by simp [disc], one_pos⟩

/-- Cochrane (2023), A1 §1.6, p. 567: **the nominal rate of the positive economy is bounded**,
`|i| ≤ ½`. -/
theorem posI_bound (u : ℝ) (ω : ℕ → ℝ) : |posI u ω| ≤ 1 / 2 := by
  have h1 := Real.neg_one_le_sin (bmReal bmPath u ω)
  have h2 := Real.abs_sin_le_one (bmReal bmPath u ω)
  have hpos : 0 < 2 * (2 + Real.sin (bmReal bmPath u ω)) := by linarith
  simp only [posI]
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  linarith

/-- **Cochrane (2023), A1 §1.6, (1.31)–(1.34), pp. 567–568: the positive economy is a model with
diffusive bonds and positive diffusive `Λ/P`** on every `[s, t]`, `0 ≤ s`: `P = 1`,
`Λ/P = 2 + sin W` (drift `−i(Λ/P) = −½ sin W`, diffusion `σ_X = cos W`), `i = posI`, `i^m = 0`,
`s = iB`, `B = b + c sin W` (`β = −½c sin W`, `σ_B = c cos W`), `M = M₀ − c sin W`
(`m = ½c sin W`, `σ_M = −c cos W`). -/
theorem posModel (b c M0 : ℝ) {s t : ℝ} (hs : 0 ≤ s) :
    ItoMonetaryModel gaussSeq bmF bmPath posΛ (constP 1) (posB b c) (posM M0 c) posI
      (constP 0) (posSp b c) (fun u ω => -(c * Real.sin (bmReal bmPath u ω) / 2))
      (fun u ω => c * Real.cos (bmReal bmPath u ω))
      (fun u ω => -(-c * Real.sin (bmReal bmPath u ω) / 2))
      (fun u ω => -c * Real.cos (bmReal bmPath u ω))
      (fun u ω => Real.cos (bmReal bmPath u ω)) s t
      (|1| / 2) |1| (|c| / 2) |c| (|-c| / 2) |-c| := by
  have hBM := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hBM measurable_bmPath
  have hn := itoProcess_affine_sin (t := t) hBM measurable_bmPath h𝓕 continuous_bmPath hs 2 1
  exact
    { P_pos := fun _ _ => one_pos
      disc_ito := by
        refine itoProcess_of_coeff_eq (a := fun u ω => -(1 * Real.sin (bmReal bmPath u ω) / 2))
          (H := fun u ω => 1 * Real.cos (bmReal bmPath u ω)) ?_ (fun u ω => ?_)
          (fun u ω => one_mul _)
        · have e : (fun u ω => 2 + 1 * Real.sin (bmReal bmPath u ω)) = disc posΛ (constP 1) :=
            funext fun u => funext fun ω => by simp [disc]
          rw [← e]
          exact hn
        · have h1 := Real.neg_one_le_sin (bmReal bmPath u ω)
          have hne : 2 + Real.sin (bmReal bmPath u ω) ≠ 0 := by linarith
          simp only [posI, disc, posΛ, constP, div_one]
          field_simp
      bonds_ito := itoProcess_affine_sin hBM measurable_bmPath h𝓕 continuous_bmPath hs b c
      money_ito := itoProcess_affine_sin hBM measurable_bmPath h𝓕 continuous_bmPath hs M0 (-c)
      flow_drift := fun u ω => by
        simp only [flowRate, posSp, constP]
        ring
      flow_diff := fun u ω => by ring }

/-! ## The bracket and the failure of the book's step -/

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: for every path, `∫_0^t cos²W_u du > 0`, `t > 0`
(`cos²W_0 = 1`). -/
theorem integral_cos_sq_pos {t : ℝ} (ht : 0 < t) (ω : ℕ → ℝ) :
    0 < ∫ u in (0 : ℝ)..t, Real.cos (bmReal bmPath u ω) * Real.cos (bmReal bmPath u ω) := by
  have hc : Continuous fun u => Real.cos (bmReal bmPath u ω) :=
    Real.continuous_cos.comp (continuous_bmReal (continuous_bmPath ω))
  refine intervalIntegral.integral_pos ht (hc.mul hc).continuousOn
    (fun x _ => mul_self_nonneg _) ⟨0, ⟨le_rfl, ht.le⟩, ?_⟩
  simp [bmReal, bmPath_zero]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `cos W` is an admissible integrand on `[s, t]`
(bounded by `1`, adapted, continuous paths).
An instance of `TidyR9ItoFormula.itoIntegrand_comp`. -/
theorem itoIntegrand_cos_bm {s t : ℝ} :
    ItoIntegrand gaussSeq bmF (fun u ω => Real.cos (bmReal bmPath u ω)) s t 1 :=
  itoIntegrand_comp (g := fun _ x => Real.cos x)
    (fun u _ => (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath).adapted u)
    (ae_of_all _ fun ω => (continuous_bmReal (continuous_bmPath ω)).continuousOn)
    (Real.continuous_cos.comp continuous_snd) fun _ _ x => Real.abs_cos_le_one x

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567 (the bracket of the positive economy):**
`E[∫_0^t σ_Xσ_B du] = c·E[∫_0^t cos²W_u du]` with `E[∫_0^t cos²W_u du] > 0`, `t > 0`. -/
theorem pos_bracket_pos (c : ℝ) {t : ℝ} (ht : 0 < t) :
    ∫ ω, (∫ u in (0 : ℝ)..t, Real.cos (bmReal bmPath u ω) *
        (c * Real.cos (bmReal bmPath u ω))) ∂gaussSeq
      = c * ∫ ω, (∫ u in (0 : ℝ)..t, Real.cos (bmReal bmPath u ω) *
        Real.cos (bmReal bmPath u ω)) ∂gaussSeq ∧
    0 < ∫ ω, (∫ u in (0 : ℝ)..t, Real.cos (bmReal bmPath u ω) *
        Real.cos (bmReal bmPath u ω)) ∂gaussSeq := by
  have := isProb
  have hint : Integrable (fun ω => ∫ u in (0 : ℝ)..t, Real.cos (bmReal bmPath u ω) *
      Real.cos (bmReal bmPath u ω)) gaussSeq :=
    (memLp_integral_drift (itoIntegrand_mul (itoIntegrand_cos_bm (s := 0) (t := t))
      itoIntegrand_cos_bm) le_rfl ht.le le_rfl).integrable one_le_two
  refine ⟨?_, ?_⟩
  · rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun u _ => by ring
  · rw [integral_pos_iff_support_of_nonneg (fun ω => (integral_cos_sq_pos ht ω).le) hint]
    have e : Function.support (fun ω => ∫ u in (0 : ℝ)..t, Real.cos (bmReal bmPath u ω) *
        Real.cos (bmReal bmPath u ω)) = Set.univ :=
      Set.eq_univ_of_forall fun ω => (integral_cos_sq_pos ht ω).ne'
    rw [e, measure_univ]
    exact one_pos

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567 (counterexample with `Λ > 0` throughout): the
last line of (1.32) as printed fails** in the positive economy on `[0, t]`, `t > 0`, for every
`c ≠ 0`: `E_0[n_tB_t − n_0B_0]` is not a.s. `−E_0[∫_0^t Λs du + ∫_0^t n dM]`, because the bracket
`E∫_0^t σ_Xσ_B du = cE∫_0^t cos²W du ≠ 0` (`ItoMonetaryModel.incr_1_32_ito_book_iff`). -/
theorem pos_book_fails (b M0 : ℝ) {c : ℝ} (hc : c ≠ 0) {t : ℝ} (ht : 0 < t) :
    ¬ (gaussSeq[fun ω => disc posΛ (constP 1) t ω * posB b c t ω
        - disc posΛ (constP 1) 0 ω * posB b c 0 ω | bmF 0] =ᵐ[gaussSeq]
      gaussSeq[fun ω => -(dtInt gaussSeq bmF (fun u ω => posΛ u ω * posSp b c u ω
        - constP 0 u ω * disc posΛ (constP 1) u ω * posM M0 c u ω) 0 t ω
        + moneyInt gaussSeq bmF bmPath posΛ (constP 1)
          (fun u ω => -(-c * Real.sin (bmReal bmPath u ω) / 2))
          (fun u ω => -c * Real.cos (bmReal bmPath u ω)) 0 t ω) | bmF 0]) := by
  have := isProb
  have hBM := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hBM measurable_bmPath
  intro h
  have hiff := ((posModel b c M0 (s := 0) (t := t) le_rfl).incr_1_32_ito_book_iff hBM
    measurable_bmPath h𝓕 le_rfl ht).1 h
  have hI := integral_condExp (μ := gaussSeq) (bmF.le 0) (f := fun ω => ∫ u in (0 : ℝ)..t,
    Real.cos (bmReal bmPath u ω) * (c * Real.cos (bmReal bmPath u ω)))
  rw [integral_congr_ae hiff, Pi.zero_def, integral_zero, (pos_bracket_pos c ht).1] at hI
  have hp := (pos_bracket_pos c ht).2
  rcases mul_eq_zero.1 hI.symm with h0 | h0
  · exact hc h0
  · linarith

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the corrected (1.32) holds** in the positive
economy on every `[s, t]`, `0 ≤ s < t`.
The instance of `ItoMonetaryModel.incr_1_32_ito_general`. -/
theorem pos_corrected (b c M0 : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    gaussSeq[fun ω => disc posΛ (constP 1) t ω * posB b c t ω
        - disc posΛ (constP 1) s ω * posB b c s ω | bmF s] =ᵐ[gaussSeq]
      gaussSeq[fun ω => -(dtInt gaussSeq bmF (fun u ω => posΛ u ω * posSp b c u ω
        - constP 0 u ω * disc posΛ (constP 1) u ω * posM M0 c u ω) s t ω
        + moneyInt gaussSeq bmF bmPath posΛ (constP 1)
          (fun u ω => -(-c * Real.sin (bmReal bmPath u ω) / 2))
          (fun u ω => -c * Real.cos (bmReal bmPath u ω)) s t ω)
        + ∫ u in s..t, Real.cos (bmReal bmPath u ω) * (c * Real.cos (bmReal bmPath u ω))
        | bmF s] :=
  (posModel b c M0 hs).incr_1_32_ito_general isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) hs hst

/-- **Cochrane (2023), A1 §1.6, p. 567, (1.34) in the positive economy:** the line before (1.34)
holds verbatim on every `[s, t]`, `0 ≤ s < t`.
The instance of `ItoMonetaryModel.incr_1_34_ito`. -/
theorem pos_1_34 (b c M0 : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    gaussSeq[fun ω => disc posΛ (constP 1) t ω
        * TidyR7ProductStep.addProc (posB b c) (posM M0 c) t ω
      - disc posΛ (constP 1) s ω * TidyR7ProductStep.addProc (posB b c) (posM M0 c) s ω
        | bmF s] =ᵐ[gaussSeq]
      gaussSeq[fun ω => -dtInt gaussSeq bmF (fun u ω => posΛ u ω * posSp b c u ω
        + (posI u ω - constP 0 u ω) * disc posΛ (constP 1) u ω * posM M0 c u ω) s t ω
        | bmF s] :=
  (posModel b c M0 hs).incr_1_34_ito isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) hs hst

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: headline (positive `Λ/P`).** In the positive
economy (`1 ≤ Λ/P = Λ ≤ 3`, `P = 1`, `|i| ≤ ½`), for `c ≠ 0` and `t > 0`: the bracket has mean
`cE∫_0^t cos²W du ≠ 0`, the book's last line of (1.32) fails on `[0, t]`, the corrected one
holds. -/
theorem pos_headline (b M0 : ℝ) {c : ℝ} (hc : c ≠ 0) {t : ℝ} (ht : 0 < t) :
    (∀ u ω, 1 ≤ disc posΛ (constP 1) u ω ∧ 0 < posΛ u ω ∧ |posI u ω| ≤ 1 / 2) ∧
    (∫ ω, (∫ u in (0 : ℝ)..t, Real.cos (bmReal bmPath u ω) *
        (c * Real.cos (bmReal bmPath u ω))) ∂gaussSeq ≠ 0) ∧
    (¬ (gaussSeq[fun ω => disc posΛ (constP 1) t ω * posB b c t ω
        - disc posΛ (constP 1) 0 ω * posB b c 0 ω | bmF 0] =ᵐ[gaussSeq]
      gaussSeq[fun ω => -(dtInt gaussSeq bmF (fun u ω => posΛ u ω * posSp b c u ω
        - constP 0 u ω * disc posΛ (constP 1) u ω * posM M0 c u ω) 0 t ω
        + moneyInt gaussSeq bmF bmPath posΛ (constP 1)
          (fun u ω => -(-c * Real.sin (bmReal bmPath u ω) / 2))
          (fun u ω => -c * Real.cos (bmReal bmPath u ω)) 0 t ω) | bmF 0])) ∧
    (gaussSeq[fun ω => disc posΛ (constP 1) t ω * posB b c t ω
        - disc posΛ (constP 1) 0 ω * posB b c 0 ω | bmF 0] =ᵐ[gaussSeq]
      gaussSeq[fun ω => -(dtInt gaussSeq bmF (fun u ω => posΛ u ω * posSp b c u ω
        - constP 0 u ω * disc posΛ (constP 1) u ω * posM M0 c u ω) 0 t ω
        + moneyInt gaussSeq bmF bmPath posΛ (constP 1)
          (fun u ω => -(-c * Real.sin (bmReal bmPath u ω) / 2))
          (fun u ω => -c * Real.cos (bmReal bmPath u ω)) 0 t ω)
        + ∫ u in (0 : ℝ)..t, Real.cos (bmReal bmPath u ω) * (c * Real.cos (bmReal bmPath u ω))
        | bmF 0]) := by
  refine ⟨fun u ω => ?_, ?_, pos_book_fails b M0 hc ht, pos_corrected b c M0 le_rfl ht⟩
  · obtain ⟨h1, -, h3, -⟩ := posΛ_bounds u ω
    exact ⟨h3 ▸ h1, by linarith, posI_bound u ω⟩
  · rw [(pos_bracket_pos c ht).1]
    exact mul_ne_zero hc (pos_bracket_pos c ht).2.ne'

end Cochrane.Monetarism.TidyR9MonetarismItoPositive
