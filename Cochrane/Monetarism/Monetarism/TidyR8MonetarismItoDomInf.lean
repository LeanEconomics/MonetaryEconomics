/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR8MonetarismItoDom
import Monetarism.TidyR7MonetarismItoCexInf

/-!
# The dominated (1.33) with the bracket on the Brownian economy 3

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", p. 567, eqs. (1.32)–(1.33). Non-vacuity of
`TidyR8MonetarismItoDom.valuation_1_33_ito_dom_pathwise` on `[0, ∞)`, in economy 3 of
`TidyR7MonetarismItoCexInf` (on the constructed Brownian motion: `P = 1`, `Λ/P = 1 + I`,
`I = ∫_0^· φ dW`, `φ = rampDown`, bonds `B = 1/3 − I`, money `M = M₀ + I`,
`i = i^m = s = 0`).

## Verifying the hypotheses

* the drift flow `d = Λs − i^m nM + n m` is `0` (`flowDrift_inf`);
* the bracket density `σ_Xσ_B = −φ²` is continuous, vanishes after `1` and is integrable on
  `(0, ∞)` with `∫_0^∞ σ_Xσ_B = −1/3` (`integrableOn_bracket_inf`, `bracketInf_inf`);
* money's diffusion `σ_M = φ` vanishes after `1`, so `J_k = ∫_0^{k+1} nφ dW = ∫_0^1 nφ dW = J`
  a.s. (`TidyR8MonetarismItoDom.itoInt_eventually_const`), with `|J_k| ≤ |J|` integrable.

## Results (`itoDomInf_headline`)

The corrected flows converge a.s. to `G = J + 1/3`; the dominated (1.33) with the bracket holds,
`n_0B_0 = 1/3 = E_0[G]` (`E[J] = 0`), as the transversality condition holds; the book's dominated
(1.33), `n_0B_0 = E_0[J]`, fails (`E_0[J] = 0 ≠ 1/3`), exactly because
`E_0[∫_0^∞ σ_Xσ_B] = −1/3 ≠ 0`.
-/

namespace Cochrane.Monetarism.TidyR8MonetarismItoDomInf

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoSums Cochrane.Monetarism.TidyR7ItoIntegral
  Cochrane.Monetarism.TidyR7ItoUnbounded Cochrane.Monetarism.TidyR7ItoProducts
  Cochrane.Monetarism.TidyR7ItoProcess Cochrane.Monetarism.TidyR7ItoBondStep
  Cochrane.Monetarism.TidyR7MonetarismModel Cochrane.Monetarism.TidyR7MonetarismIto
  Cochrane.Monetarism.TidyR7MonetarismItoValuation Cochrane.Monetarism.TidyR7MonetarismItoCex
  Cochrane.Monetarism.TidyR7MonetarismItoCexInf Cochrane.Monetarism.TidyR7BrownianExist
  Cochrane.Monetarism.TidyR7BrownianSchauder Cochrane.Monetarism.TidyR8MonetarismItoDom
open scoped ENNReal NNReal

/-- Cochrane (2023), A1 §1.6, p. 567 (economy 3): `φ(u) = 0` for `u ≥ 1`. -/
theorem rampDown_of_ge {u : ℝ} (hu : 1 ≤ u) : rampDown u = 0 := by
  simp only [rampDown, max_eq_left (by linarith : 1 - u ≤ 0)]
  norm_num

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567 (economy 3): the drift flow
`d = Λs − i^m nM + n m` is `0` (`s = i^m = m = 0`). -/
theorem flowDrift_inf (M0 : ℝ) (u : ℝ) (ω : ℕ → ℝ) :
    flowDrift infΛ (constP 1) (infM M0) (constP 0) (constP 0) (constP 0) u ω = 0 := by
  simp [flowDrift]

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567 (economy 3): the bracket density `σ_Xσ_B = −φ²` is
integrable on `(0, ∞)` (continuous on `[0, 1]`, zero after `1`). -/
theorem integrableOn_bracket_inf :
    IntegrableOn (fun u : ℝ => rampDown u * (-1 * rampDown u)) (Set.Ioi 0) := by
  have c : Continuous fun u : ℝ => rampDown u * (-1 * rampDown u) :=
    continuous_ramps.1.mul (continuous_const.mul continuous_ramps.1)
  have h1 : IntegrableOn (fun u : ℝ => rampDown u * (-1 * rampDown u)) (Set.Ioc 0 1) :=
    (c.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have h2 : IntegrableOn (fun u : ℝ => rampDown u * (-1 * rampDown u)) (Set.Ioi 1) :=
    (integrableOn_zero).congr_fun (fun u hu => by
      simp only [rampDown_of_ge (le_of_lt hu), zero_mul]) measurableSet_Ioi
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact h1.union h2

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567 (economy 3): the bracket to infinity**
`∫_0^∞ σ_Xσ_B du = −∫_0^1 φ² = −1/3`. -/
theorem bracketInf_inf (ω : ℕ → ℝ) :
    bracketInf (fun r (_ : ℕ → ℝ) => rampDown r) (fun r _ => -1 * rampDown r) 0 ω = -(1 / 3) := by
  have hseq : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have h := intervalIntegral_tendsto_integral_Ioi 0 integrableOn_bracket_inf hseq
  have e : ∀ k : ℕ, ∫ u in (0 : ℝ)..((k : ℝ) + 1), rampDown u * (-1 * rampDown u) = -(1 / 3) :=
    fun k => inf_bracket (by have := k.cast_nonneg (α := ℝ); linarith) ω
  simp_rw [e] at h
  exact (tendsto_nhds_unique tendsto_const_nhds h).symm

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (economy 3): `nφ` is mean-square continuous on every
`[0, T]` (`n` an Itô process, `φ` bounded). -/
theorem msIntegrand_nphi (M0 : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    MSIntegrand gaussSeq bmF (fun u ω => disc infΛ (constP 1) u ω * rampDown u) 0 T := by
  have := isProb
  have h := infModel M0 hT
  exact MSIntegrand.mul_itoIntegrand
    (h.disc_ito.toMS isPreBrownianReal_bmPath measurable_bmPath
      (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) le_rfl)
    h.money_ito.diff

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567 (economy 3): the Itô part of the flows,
`J = ∫_0^1 nφ dW`. -/
noncomputable def infJ : (ℕ → ℝ) → ℝ :=
  itoInt gaussSeq bmF bmPath (fun u ω => disc infΛ (constP 1) u ω * rampDown u) 0 1

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567 (economy 3): the Itô part is constant after `1`:**
`∫_0^{k+1} nφ dW = J` a.s. for every `k`. -/
theorem infJ_const (M0 : ℝ) : ∀ᵐ ω ∂gaussSeq, ∀ k : ℕ,
    itoInt gaussSeq bmF bmPath (fun u ω => disc infΛ (constP 1) u ω * rampDown u) 0
      ((k : ℝ) + 1) ω = infJ ω := by
  refine ae_all_iff.2 fun k => ?_
  have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by have := k.cast_nonneg (α := ℝ); linarith
  exact itoInt_eventually_const isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) le_rfl zero_le_one hk
    (msIntegrand_nphi M0 (by linarith)) (fun u hu ω => by rw [rampDown_of_ge hu, mul_zero])

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567 (economy 3): `E_0[J] = E[J] = 0`
(`TidyR7ItoUnbounded.condExp_itoInt_ms`, `𝓕_0` trivial). -/
theorem integral_infJ (M0 : ℝ) : ∫ ω, infJ ω ∂gaussSeq = 0 := by
  have := isProb
  have h := condExp_itoInt_ms isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) le_rfl
    (msIntegrand_nphi M0 zero_le_one)
  rw [bmF_zero, condExp_bot] at h
  obtain ⟨ω, hω⟩ := h.exists
  exact hω

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567 (economy 3): `J` is integrable. -/
theorem integrable_infJ (M0 : ℝ) : Integrable infJ gaussSeq := by
  have := isProb
  exact (memLp_itoInt_ms isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) le_rfl
    (msIntegrand_nphi M0 zero_le_one)).integrable one_le_two

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567 (economy 3): the corrected flow to infinity is
`G = J + 1/3`. -/
theorem domLimit_inf (M0 : ℝ) (ω : ℕ → ℝ) :
    domLimit infΛ (constP 1) (infM M0) (constP 0) (constP 0) (constP 0)
      (fun r _ => rampDown r) (fun r _ => -1 * rampDown r) 0 infJ ω = infJ ω + 1 / 3 := by
  simp only [domLimit, flowDrift_inf, integral_zero, bracketInf_inf]
  ring

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567 (economy 3): the book's flow to infinity is `J`. -/
theorem domLimitBook_inf (M0 : ℝ) (ω : ℕ → ℝ) :
    domLimitBook infΛ (constP 1) (infM M0) (constP 0) (constP 0) (constP 0) 0 infJ ω = infJ ω := by
  simp only [domLimitBook, flowDrift_inf, integral_zero, zero_add]

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567 (economy 3): headline — the dominated (1.33)
with the bracket holds, the book's dominated (1.33) fails.** Along `T_k = k + 1`:
(i) the hypotheses of `TidyR8MonetarismItoDom.valuation_1_33_ito_dom_pathwise` hold, so its
conclusion holds;
(ii) the corrected flows converge a.s. to `G = J + 1/3` and `|F^c_{T_k}| ≤ 1/3 + |J|`;
(iii) `n_0B_0 = 1/3 = E_0[G]` (the dominated (1.33) with the bracket);
(iv) `E_0[∫_0^∞ σ_Xσ_B] = −1/3` and the book's dominated (1.33), `n_0B_0 = E_0[J] = 0`, fails. -/
theorem itoDomInf_headline (M0 : ℝ) :
    (∀ᵐ ω ∂gaussSeq, Tendsto (fun k : ℕ => flowItoC gaussSeq bmF bmPath infΛ (constP 1)
      (infM M0) (constP 0) (constP 0) (constP 0) (fun r _ => rampDown r)
      (fun r _ => rampDown r) (fun r _ => -1 * rampDown r) 0 ((k : ℝ) + 1) ω) atTop
        (𝓝 (infJ ω + 1 / 3))) ∧
    (∀ k : ℕ, ∀ᵐ ω ∂gaussSeq, |flowItoC gaussSeq bmF bmPath infΛ (constP 1)
      (infM M0) (constP 0) (constP 0) (constP 0) (fun r _ => rampDown r)
      (fun r _ => rampDown r) (fun r _ => -1 * rampDown r) 0 ((k : ℝ) + 1) ω| ≤
        1 / 3 + |infJ ω|) ∧
    (fun ω => disc infΛ (constP 1) 0 ω * infB 0 ω) =ᵐ[gaussSeq]
      gaussSeq[domLimit infΛ (constP 1) (infM M0) (constP 0) (constP 0) (constP 0)
        (fun r _ => rampDown r) (fun r _ => -1 * rampDown r) 0 infJ | bmF 0] ∧
    gaussSeq[domLimit infΛ (constP 1) (infM M0) (constP 0) (constP 0) (constP 0)
        (fun r _ => rampDown r) (fun r _ => -1 * rampDown r) 0 infJ | bmF 0] = (fun _ => 1 / 3) ∧
    gaussSeq[bracketInf (fun r _ => rampDown r) (fun r _ => -1 * rampDown r) 0 | bmF 0] =
      (fun _ => -(1 / 3)) ∧
    gaussSeq[domLimitBook infΛ (constP 1) (infM M0) (constP 0) (constP 0) (constP 0) 0 infJ |
      bmF 0] = (fun _ => 0) ∧
    ¬ (fun ω => disc infΛ (constP 1) 0 ω * infB 0 ω) =ᵐ[gaussSeq]
      gaussSeq[domLimitBook infΛ (constP 1) (infM M0) (constP 0) (constP 0) (constP 0) 0 infJ |
        bmF 0] := by
  have := isProb
  have hBM := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hBM measurable_bmPath
  have hseq : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hc1 : ∀ᵐ ω ∂gaussSeq, ContinuousOn (fun u => infΛ u ω * constP 0 u ω -
      constP 0 u ω * disc infΛ (constP 1) u ω * infM M0 u ω) (Set.Ici 0) :=
    ae_of_all _ fun ω => (continuousOn_const (c := (0 : ℝ))).congr fun u _ => by simp
  have hc2 : ∀ᵐ ω ∂gaussSeq, ContinuousOn (fun u => disc infΛ (constP 1) u ω * constP 0 u ω)
      (Set.Ici 0) :=
    ae_of_all _ fun ω => (continuousOn_const (c := (0 : ℝ))).congr fun u _ => by simp
  have hz : ∀ ω, (fun u => flowDrift infΛ (constP 1) (infM M0) (constP 0) (constP 0)
      (constP 0) u ω) = fun _ => 0 := fun ω => funext fun u => flowDrift_inf M0 u ω
  have hi : ∀ᵐ ω ∂gaussSeq, IntegrableOn (fun u => flowDrift infΛ (constP 1) (infM M0)
      (constP 0) (constP 0) (constP 0) u ω) (Set.Ioi 0) ∧
      IntegrableOn (fun u => (fun r (_ : ℕ → ℝ) => rampDown r) u ω *
        (fun r (_ : ℕ → ℝ) => -1 * rampDown r) u ω) (Set.Ioi 0) :=
    ae_of_all _ fun ω => ⟨by rw [hz ω]; exact integrableOn_zero, integrableOn_bracket_inf⟩
  set c : ℝ := ∫ u in Set.Ioi (0 : ℝ), |rampDown u * (-1 * rampDown u)| with hc
  have hH₁b : ∀ᵐ ω ∂gaussSeq, (∫ u in Set.Ioi (0 : ℝ), |flowDrift infΛ (constP 1) (infM M0)
      (constP 0) (constP 0) (constP 0) u ω|) +
      (∫ u in Set.Ioi (0 : ℝ), |(fun r (_ : ℕ → ℝ) => rampDown r) u ω *
        (fun r (_ : ℕ → ℝ) => -1 * rampDown r) u ω|) ≤ (fun _ => c) ω :=
    ae_of_all _ fun ω => by simp [flowDrift_inf, hc]
  have hJ := infJ_const M0
  have hJlim : ∀ᵐ ω ∂gaussSeq, Tendsto (fun k : ℕ => itoInt gaussSeq bmF bmPath
      (fun u ω => disc infΛ (constP 1) u ω * (fun r (_ : ℕ → ℝ) => rampDown r) u ω) 0
        ((k : ℝ) + 1) ω) atTop (𝓝 (infJ ω)) := by
    filter_upwards [hJ] with ω h
    exact tendsto_const_nhds.congr fun k => (h k).symm
  have hJb : ∀ k : ℕ, ∀ᵐ ω ∂gaussSeq, |itoInt gaussSeq bmF bmPath
      (fun u ω => disc infΛ (constP 1) u ω * (fun r (_ : ℕ → ℝ) => rampDown r) u ω) 0
        ((k : ℝ) + 1) ω| ≤ |infJ ω| := fun k => by
    filter_upwards [hJ] with ω h
    simp only [h k, le_refl]
  have hmain := valuation_1_33_ito_dom_pathwise (infModels M0) hBM measurable_bmPath h𝓕 le_rfl
    (T := fun k : ℕ => (k : ℝ) + 1) (fun k => by positivity) hseq hc1 hc2 hi
    (H₁ := fun _ => c) (integrable_const _) hH₁b (J := infJ) (H₂ := fun ω => |infJ ω|)
    (integrable_infJ M0).abs hJlim hJb
  obtain ⟨hlim, hbd, hval, -⟩ := hmain
  have htvc := inf_tvc
  have hv := hval.2 htvc
  have hc3 : c = 1 / 3 := by
    have e : (fun u : ℝ => |rampDown u * (-1 * rampDown u)|) =
        fun u => -(rampDown u * (-1 * rampDown u)) := funext fun u => by
      rw [abs_of_nonpos (by nlinarith [sq_nonneg (rampDown u)])]
    rw [hc, e, integral_neg]
    have := bracketInf_inf (fun _ => 0)
    simp only [bracketInf] at this
    rw [this]
    norm_num
  have hEG : gaussSeq[domLimit infΛ (constP 1) (infM M0) (constP 0) (constP 0) (constP 0)
      (fun r _ => rampDown r) (fun r _ => -1 * rampDown r) 0 infJ | bmF 0] = fun _ => 1 / 3 := by
    rw [bmF_zero, condExp_bot]
    funext _
    simp_rw [domLimit_inf]
    rw [integral_add (integrable_infJ M0) (integrable_const _), integral_infJ M0]
    simp
  have hEB : gaussSeq[bracketInf (fun r _ => rampDown r) (fun r _ => -1 * rampDown r) 0 |
      bmF 0] = fun _ => -(1 / 3) := by
    rw [bmF_zero, condExp_bot]
    funext _
    simp_rw [bracketInf_inf]
    simp
  have hEJ : gaussSeq[domLimitBook infΛ (constP 1) (infM M0) (constP 0) (constP 0) (constP 0)
      0 infJ | bmF 0] = fun _ => 0 := by
    rw [bmF_zero, condExp_bot]
    funext _
    simp_rw [domLimitBook_inf]
    exact integral_infJ M0
  refine ⟨?_, ?_, hv, hEG, hEB, hEJ, ?_⟩
  · filter_upwards [hlim] with ω h
    rwa [domLimit_inf] at h
  · intro k
    filter_upwards [hbd k] with ω h
    rwa [hc3] at h
  · rw [hEJ]
    intro h
    obtain ⟨ω, hω⟩ := h.exists
    have hω' : disc infΛ (constP 1) 0 ω * infB 0 ω = 0 := hω
    rw [inf_initial] at hω'
    norm_num at hω'

end Cochrane.Monetarism.TidyR8MonetarismItoDomInf
