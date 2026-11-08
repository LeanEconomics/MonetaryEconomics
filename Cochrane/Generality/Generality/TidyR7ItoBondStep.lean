/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.TidyR7ItoProductRule

/-!
# The general (1.32) product step for diffusive bonds and a diffusive `Λ/P`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). The step from the middle line of (1.32) to its
last line is the product step `E_t d(BX) = X dB + B E_t dX` with `X = Λ/P`. For bonds `B` and
`X = Λ/P` both Itô processes driven by the same Brownian motion `W`,
`B_u = B_s + ∫_s^u β dr + ∫_s^u σ_B dW`, `X_u = X_s + ∫_s^u ν dr + ∫_s^u σ_X dW`
(`TidyR7ItoProcess.ItoProcess`), the correct step is
`E_t d(BX) = X dB + B E_t dX + E_t d[B, X]` with `d[B, X] = σ_Bσ_X dt`.

## Main results

* `bond_step` (conditional form over `[s, t]`, `0 ≤ s < t`): a.s.
  `E_s[B_tX_t − B_sX_s] = E_s[∫_s^t B ν du + ∫_s^t X β du + ∫_s^t σ_Bσ_X du]`.
* `bond_step_expIncr` (expected-increment limit form, the reading of
  `TidyR7ProductStep.ExpIncrLimit`): along any partitions with mesh `→ 0`, in `L¹`,
  `E_s[Σ B_iΔX_i] → E_s∫B ν du` (`B E_t dX`), `E_s[Σ X_iΔB_i] → E_s∫X β du` (`X dB`) and
  `E_s[Σ ΔB_iΔX_i] → E_s∫σ_Bσ_X du` (`E_t d[B, X]`).
* `bond_step_bv`: if `σ_B = 0` on `[s, t]` a.s. (bonds of bounded variation; `Λ/P` may still
  diffuse) the bracket vanishes and the book's step holds. This is the case the book's derivation
  covers; Track 1 proves it with a general martingale `Λ/P`
  (`TidyR7ProductStep.ProductStepData.product_step`), and `bond_step_bv` reproduces it term by
  term for Itô `Λ/P`.
* `bond_step_book_iff`: for a given pair, the book's bracket-free step holds iff
  `E_s[∫_s^t σ_Bσ_X du] = 0` a.s.
* `bookForm_forall_iff` (**the precise extent of the book's step**): for given Itô bonds, the
  book's step holds against EVERY Itô process `X` iff `σ_B = 0` on `[s, t]` almost surely
  (test with `X = ∫σ_B dW`, whose bracket with `B` is `∫σ_B² du`).
* Tools: `dtSum_add`, `dtSum_const_mul`, `dtInt_add`, `dtInt_const_mul` (linearity of the
  mean-square time integral `TidyR7ItoProducts.dtInt`), `MSIntegrand.add`,
  `MSIntegrand.const_mul` (mean-square continuous integrands form a vector space),
  `condExp_eq_of_ae_eq_add`, `itoProcess_itoInt` (`u ↦ ∫_s^u H dW` is an Itô process),
  `condExp_bracket_zero`, `ae_zero_of_condExp_integral_sq`.
-/

namespace Cochrane.Generality.TidyR7ItoBondStep

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Generality.TidyR7StieltjesSums Cochrane.Generality.TidyR7BrownianTools
  Cochrane.Generality.TidyR7BrownianQV Cochrane.Generality.TidyR7ItoL2
  Cochrane.Generality.TidyR7ItoSums Cochrane.Generality.TidyR7ItoIntegral
  Cochrane.Generality.TidyR7ItoUnbounded Cochrane.Generality.TidyR7ItoProducts
  Cochrane.Generality.TidyR7ItoProcess Cochrane.Generality.TidyR7ItoProductRule
open Cochrane.Generality.TidyR7ProductStep (sumRS sumCross)
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → ℝ} {s t : ℝ}

/-! ## Tools: linearity of the mean-square time integral -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (the `dt`-terms of (1.32)): Riemann sums are additive
in the integrand.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7ItoBondStep.dtSum_add). -/
theorem dtSum_add (G K : ℝ → Ω → ℝ) (p : Partition s t) (ω : Ω) :
    dtSum (fun u ω => G u ω + K u ω) p ω = dtSum G p ω + dtSum K p ω := by
  simp only [dtSum, riemannSum, ← Finset.sum_add_distrib, add_mul]

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (the `dt`-terms of (1.32)): Riemann sums are
homogeneous in the integrand.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBondStep.dtSum_const_mul). -/
theorem dtSum_const_mul (c : ℝ) (G : ℝ → Ω → ℝ) (p : Partition s t) (ω : Ω) :
    dtSum (fun u ω => c * G u ω) p ω = c * dtSum G p ω := by
  simp only [dtSum, riemannSum, Finset.mul_sum, mul_assoc]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the mean-square time integral is additive**,
`∫(G + K) du = ∫G du + ∫K du` a.s. for mean-square continuous `G, K`.
The time-integral analogue of `TidyR7ItoIntegral.itoInt_add`.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7ItoBondStep.dtInt_add). -/
theorem dtInt_add {G K : ℝ → Ω → ℝ} (hG : MSIntegrand μ 𝓕 G s t)
    (hK : MSIntegrand μ 𝓕 K s t) :
    dtInt μ 𝓕 (fun u ω => G u ω + K u ω) s t =ᵐ[μ] dtInt μ 𝓕 G s t + dtInt μ 𝓕 K s t := by
  rcases lt_or_ge s t with hst | hts
  · have h2 : L2Tendsto μ (fun k => dtSum (fun u ω => G u ω + K u ω) (dyadic hst k))
        (dtInt μ 𝓕 G s t + dtInt μ 𝓕 K s t) :=
      ((L2Tendsto_dyadic_dt hst hG).add (L2Tendsto_dyadic_dt hst hK)).congr_seq
        (fun k => ae_of_all _ fun ω => (dtSum_add G K (dyadic hst k) ω).symm)
    have h1 := (dtInt_spec hst ⟨_, stronglyMeasurable_dtInt.add stronglyMeasurable_dtInt,
      h2⟩).2
    exact ae_eq_of_L2Tendsto h1 h2
  · rw [dtInt_of_le hts, dtInt_of_le hts, dtInt_of_le hts]
    exact ae_of_all _ fun ω => by simp

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the mean-square time integral is homogeneous**,
`∫cG du = c∫G du` a.s. for mean-square continuous `G`.
The time-integral analogue of `TidyR7ItoIntegral.itoInt_const_mul`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBondStep.dtInt_const_mul). -/
theorem dtInt_const_mul {G : ℝ → Ω → ℝ} (hG : MSIntegrand μ 𝓕 G s t) (c : ℝ) :
    dtInt μ 𝓕 (fun u ω => c * G u ω) s t =ᵐ[μ] fun ω => c * dtInt μ 𝓕 G s t ω := by
  rcases lt_or_ge s t with hst | hts
  · have h2 : L2Tendsto μ (fun k => dtSum (fun u ω => c * G u ω) (dyadic hst k))
        (fun ω => c * dtInt μ 𝓕 G s t ω) :=
      ((L2Tendsto_dyadic_dt hst hG).const_mul c).congr_seq
        (fun k => ae_of_all _ fun ω => (dtSum_const_mul c G (dyadic hst k) ω).symm)
    have h1 := (dtInt_spec hst ⟨_, stronglyMeasurable_dtInt.const_mul c, h2⟩).2
    exact ae_eq_of_L2Tendsto h1 h2
  · rw [dtInt_of_le hts, dtInt_of_le hts]
    exact ae_of_all _ fun ω => by simp

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: mean-square continuous integrands are closed under
sums** (`E[((G + K)_u − (G + K)_v)²] ≤ 2E[(G_u − G_v)²] + 2E[(K_u − K_v)²]`).
The analogue of `TidyR7ItoIntegral.ItoIntegrand.add`; uses `TidyR7ItoProcess.add_sq_le_two`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBondStep.MSIntegrand.add). -/
theorem MSIntegrand.add {G K : ℝ → Ω → ℝ} (hG : MSIntegrand μ 𝓕 G s t)
    (hK : MSIntegrand μ 𝓕 K s t) : MSIntegrand μ 𝓕 (fun u ω => G u ω + K u ω) s t where
  adapted u hu := (hG.adapted u hu).add (hK.adapted u hu)
  memLp u hu := (hG.memLp u hu).add (hK.memLp u hu)
  cont ε hε := by
    obtain ⟨δ1, hδ1, h1⟩ := hG.cont (ε / 4) (by positivity)
    obtain ⟨δ2, hδ2, h2⟩ := hK.cont (ε / 4) (by positivity)
    refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun u hu v hv huv => ?_⟩
    have i1 : Integrable (fun ω => (G u ω - G v ω) ^ 2) μ :=
      ((hG.memLp u hu).sub (hG.memLp v hv)).integrable_sq
    have i2 : Integrable (fun ω => (K u ω - K v ω) ^ 2) μ :=
      ((hK.memLp u hu).sub (hK.memLp v hv)).integrable_sq
    have i0 : Integrable (fun ω => (G u ω + K u ω - (G v ω + K v ω)) ^ 2) μ :=
      (((hG.memLp u hu).add (hK.memLp u hu)).sub
        ((hG.memLp v hv).add (hK.memLp v hv))).integrable_sq
    have hle : ∫ ω, (G u ω + K u ω - (G v ω + K v ω)) ^ 2 ∂μ ≤
        ∫ ω, (2 * (G u ω - G v ω) ^ 2 + 2 * (K u ω - K v ω) ^ 2) ∂μ :=
      integral_mono i0 ((i1.const_mul 2).add (i2.const_mul 2)) fun ω => by
        nlinarith [sq_nonneg (G u ω - G v ω - (K u ω - K v ω))]
    rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul,
      integral_const_mul] at hle
    have e1 := h1 u hu v hv (huv.trans (min_le_left _ _))
    have e2 := h2 u hu v hv (huv.trans (min_le_right _ _))
    change ∫ ω, (G u ω + K u ω - (G v ω + K v ω)) ^ 2 ∂μ ≤ ε
    linarith

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: mean-square continuous integrands are closed under
constant multiples** (`E[(cG_u − cG_v)²] = c²E[(G_u − G_v)²]`).
The analogue of `TidyR7ItoIntegral.ItoIntegrand.const_mul`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBondStep.MSIntegrand.const_mul). -/
theorem MSIntegrand.const_mul {G : ℝ → Ω → ℝ} (hG : MSIntegrand μ 𝓕 G s t) (c : ℝ) :
    MSIntegrand μ 𝓕 (fun u ω => c * G u ω) s t where
  adapted u hu := (hG.adapted u hu).const_mul c
  memLp u hu := (hG.memLp u hu).const_mul c
  cont ε hε := by
    obtain ⟨δ, hδ, h1⟩ := hG.cont (ε / (c ^ 2 + 1)) (by positivity)
    refine ⟨δ, hδ, fun u hu v hv huv => ?_⟩
    have e : ∫ ω, (c * G u ω - c * G v ω) ^ 2 ∂μ = c ^ 2 * ∫ ω, (G u ω - G v ω) ^ 2 ∂μ := by
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun ω => by ring)
    have hb := h1 u hu v hv huv
    have h0 : 0 ≤ ∫ ω, (G u ω - G v ω) ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
    change ∫ ω, (c * G u ω - c * G v ω) ^ 2 ∂μ ≤ ε
    rw [e]
    have hc : 0 < c ^ 2 + 1 := by positivity
    have : (∫ ω, (G u ω - G v ω) ^ 2 ∂μ) * (c ^ 2 + 1) ≤ ε := by
      rwa [le_div_iff₀ hc] at hb
    nlinarith [sq_nonneg c]

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (dropping a term with conditional mean zero, such as
`∫ · dW` in (1.32)): if `f = g + h` a.s., `g, h` integrable and `E[h | m] = 0`, then
`E[f | m] = E[g | m]` a.s.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBondStep.condExp_eq_of_ae_eq_add). -/
theorem condExp_eq_of_ae_eq_add {m : MeasurableSpace Ω} {f g h : Ω → ℝ}
    (hfg : f =ᵐ[μ] g + h) (hg : Integrable g μ) (hh : Integrable h μ)
    (h0 : μ[h | m] =ᵐ[μ] 0) : μ[f | m] =ᵐ[μ] μ[g | m] := by
  filter_upwards [condExp_congr_ae (m := m) hfg, condExp_add hg hh m, h0] with ω h1 h2 h3
  rw [h1, h2, Pi.add_apply, h3, Pi.zero_apply, add_zero]

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (a diffusive test process for (1.32)): the running
Itô integral `u ↦ ∫_s^u H dW` of a bounded admissible integrand is an Itô process on `[s, t]`
with drift `0` and diffusion `H`.
Generalises `TidyR7ItoProductRule.itoProcess_bm` (`H = 1`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBondStep.itoProcess_itoInt). -/
theorem itoProcess_itoInt {H : ℝ → Ω → ℝ} {C : ℝ} [IsFiniteMeasure μ]
    (hH : ItoIntegrand μ 𝓕 H s t C) :
    ItoProcess μ 𝓕 W (fun u ω => itoInt μ 𝓕 W H s u ω) (fun _ _ => 0) H s t 0 C where
  adapted _ _ := stronglyMeasurable_itoInt
  init := by
    rw [itoInt_of_le (le_refl s)]
    exact MemLp.zero
  drift := itoIntegrand_const (c := fun _ => (0 : ℝ)) stronglyMeasurable_const
    (fun _ => by simp)
  diff := hH
  eq u _ := ae_of_all _ fun ω => by
    change itoInt μ 𝓕 W H s u ω = itoInt μ 𝓕 W H s s ω + (∫ _r in s..u, (0 : ℝ))
      + itoInt μ 𝓕 W H s u ω
    rw [itoInt_of_le (le_refl s)]
    simp

/-- Cochrane (2023), A1 §1.6, pp. 567–568: if the diffusion of bonds vanishes on `[s, t]` a.s.,
the bracket `E_s[∫_s^t σ_Bσ_X du]` is `0` a.s.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBondStep.condExp_bracket_zero). -/
theorem condExp_bracket_zero {σB σX : ℝ → Ω → ℝ} (hst : s ≤ t)
    (hσ : ∀ᵐ ω ∂μ, ∀ u ∈ Set.Icc s t, σB u ω = 0) :
    μ[fun ω => ∫ u in s..t, σB u ω * σX u ω | 𝓕 s] =ᵐ[μ] 0 := by
  have e : (fun ω => ∫ u in s..t, σB u ω * σX u ω) =ᵐ[μ] 0 := by
    filter_upwards [hσ] with ω hω
    have : ∀ u ∈ Set.uIcc s t, σB u ω * σX u ω = 0 := fun u hu => by
      rw [Set.uIcc_of_le hst] at hu
      rw [hω u hu, zero_mul]
    rw [intervalIntegral.integral_congr this]
    simp
  filter_upwards [condExp_congr_ae (m := 𝓕 s) e] with ω hω
  rw [hω, condExp_zero]

/-! ## The general product step -/

variable {B X β ν σB σX : ℝ → Ω → ℝ} {Cβ CB Cν CX : ℝ}

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the general product step, conditional form.**
For bonds `B` (drift `β`, diffusion `σ_B`) and `X = Λ/P` (drift `ν`, diffusion `σ_X`), Itô
processes on `[s, t]` driven by the same `W`, `0 ≤ s < t`, almost surely
`E_s[B_tX_t − B_sX_s] = E_s[∫_s^t B ν du + ∫_s^t X β du + ∫_s^t σ_Bσ_X du]`:
integrated, `E_t d(BX) = B E_t dX + X E_t dB + E_t d[B, X]`, `d[B, X] = σ_Bσ_X dt`.
The case `X := B`, `Y := X` of `TidyR7ItoProductRule.condExp_product_rule`.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7ItoBondStep.bond_step). -/
theorem bond_step (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hBo : ItoProcess μ 𝓕 W B β σB s t Cβ CB) (hX : ItoProcess μ 𝓕 W X ν σX s t Cν CX) :
    μ[fun ω => B t ω * X t ω - B s ω * X s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => dtInt μ 𝓕 (fun u ω => B u ω * ν u ω) s t ω
        + dtInt μ 𝓕 (fun u ω => X u ω * β u ω) s t ω
        + ∫ u in s..t, σB u ω * σX u ω | 𝓕 s] :=
  condExp_product_rule hBM hWm h𝓕 hs hst hBo hX

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the general product step, expected-increment
limit form.** Under the hypotheses of `bond_step`, along any partitions of `[s, t]` with mesh
`→ 0`, in `L¹`: `E_s[Σ B_iΔX_i] → E_s∫_s^t B ν du` (the book's `B E_t d(Λ/P)`),
`E_s[Σ X_iΔB_i] → E_s∫_s^t X β du` (the book's `(Λ/P) dB`, the `dW` part having conditional mean
`0`) and `E_s[Σ ΔB_iΔX_i] → E_s∫_s^t σ_Bσ_X du` (`E_t d[B, Λ/P]`), and the conditional form
`bond_step` holds.
The case `X := B`, `Y := X` of `TidyR7ItoProductRule.expected_increment_product_rule`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBondStep.bond_step_expIncr). -/
theorem bond_step_expIncr (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hBo : ItoProcess μ 𝓕 W B β σB s t Cβ CB) (hX : ItoProcess μ 𝓕 W X ν σX s t Cν CX)
    (ps : ℕ → Partition s t) (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    (μ[fun ω => B t ω * X t ω - B s ω * X s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => dtInt μ 𝓕 (fun u ω => B u ω * ν u ω) s t ω
        + dtInt μ 𝓕 (fun u ω => X u ω * β u ω) s t ω
        + ∫ u in s..t, σB u ω * σX u ω | 𝓕 s]) ∧
    Tendsto (fun k => ∫ ω, |μ[sumRS (ps k) B X | 𝓕 s] ω
      - μ[dtInt μ 𝓕 (fun u ω => B u ω * ν u ω) s t | 𝓕 s] ω| ∂μ) atTop (𝓝 0) ∧
    Tendsto (fun k => ∫ ω, |μ[sumRS (ps k) X B | 𝓕 s] ω
      - μ[dtInt μ 𝓕 (fun u ω => X u ω * β u ω) s t | 𝓕 s] ω| ∂μ) atTop (𝓝 0) ∧
    Tendsto (fun k => ∫ ω, |μ[sumCross (ps k) B X | 𝓕 s] ω
      - μ[fun ω => ∫ u in s..t, σB u ω * σX u ω | 𝓕 s] ω| ∂μ) atTop (𝓝 0) :=
  expected_increment_product_rule hBM hWm h𝓕 hs hst hBo hX ps hps

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the book's step for bonds of bounded variation,
with `Λ/P` still diffusive.** If `σ_B = 0` on `[s, t]` a.s., then a.s.
`E_s[B_tX_t − B_sX_s] = E_s[∫_s^t B ν du + ∫_s^t X β du]`: no bracket, whatever `σ_X` is. This is
exactly the case the book's derivation covers (and Track 1 proves for martingale `Λ/P`,
`TidyR7ProductStep.ProductStepData.product_step`).
The case `X := B` of `TidyR7ItoProductRule.condExp_product_rule_bv`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBondStep.bond_step_bv). -/
theorem bond_step_bv (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hBo : ItoProcess μ 𝓕 W B β σB s t Cβ CB) (hX : ItoProcess μ 𝓕 W X ν σX s t Cν CX)
    (hσ : ∀ᵐ ω ∂μ, ∀ u ∈ Set.Icc s t, σB u ω = 0) :
    μ[fun ω => B t ω * X t ω - B s ω * X s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => dtInt μ 𝓕 (fun u ω => B u ω * ν u ω) s t ω
        + dtInt μ 𝓕 (fun u ω => X u ω * β u ω) s t ω | 𝓕 s] :=
  (condExp_product_rule_bookForm_iff hBM hWm h𝓕 hs hst hBo hX).2
    (condExp_bracket_zero hst.le hσ)

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: when the book's step is right, for a given
pair.** Under the hypotheses of `bond_step`, the bracket-free step
`E_s[B_tX_t − B_sX_s] = E_s[∫_s^t B ν du + ∫_s^t X β du]` holds a.s. **iff**
`E_s[∫_s^t σ_Bσ_X du] = 0` a.s.
The case `X := B`, `Y := X` of `TidyR7ItoProductRule.condExp_product_rule_bookForm_iff`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBondStep.bond_step_book_iff). -/
theorem bond_step_book_iff (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hBo : ItoProcess μ 𝓕 W B β σB s t Cβ CB) (hX : ItoProcess μ 𝓕 W X ν σX s t Cν CX) :
    (μ[fun ω => B t ω * X t ω - B s ω * X s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => dtInt μ 𝓕 (fun u ω => B u ω * ν u ω) s t ω
        + dtInt μ 𝓕 (fun u ω => X u ω * β u ω) s t ω | 𝓕 s]) ↔
      μ[fun ω => ∫ u in s..t, σB u ω * σX u ω | 𝓕 s] =ᵐ[μ] 0 :=
  condExp_product_rule_bookForm_iff hBM hWm h𝓕 hs hst hBo hX

/-- Cochrane (2023), A1 §1.6, pp. 567–568: if `E_s[∫_s^t σ² du] = 0` a.s. and `σ` is an
admissible integrand (a.s. continuous paths), then `σ = 0` on `[s, t]` almost surely.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBondStep.ae_zero_of_condExp_integral_sq). -/
theorem ae_zero_of_condExp_integral_sq [IsProbabilityMeasure μ] {σ : ℝ → Ω → ℝ} {C : ℝ}
    (hst : s < t) (hσ : ItoIntegrand μ 𝓕 σ s t C)
    (h0 : μ[fun ω => ∫ u in s..t, σ u ω * σ u ω | 𝓕 s] =ᵐ[μ] 0) :
    ∀ᵐ ω ∂μ, ∀ u ∈ Set.Icc s t, σ u ω = 0 := by
  have hi : Integrable (fun ω => ∫ u in s..t, σ u ω * σ u ω) μ :=
    (memLp_integral_drift (itoIntegrand_mul hσ hσ) le_rfl hst.le le_rfl).integrable one_le_two
  have hE : ∫ ω, (∫ u in s..t, σ u ω * σ u ω) ∂μ = 0 := by
    rw [← integral_condExp (𝓕.le s), integral_congr_ae h0]
    simp
  have hnn : ∀ ω, 0 ≤ ∫ u in s..t, σ u ω * σ u ω := fun ω =>
    intervalIntegral.integral_nonneg hst.le fun u _ => mul_self_nonneg _
  have hz := (integral_eq_zero_iff_of_nonneg hnn hi).1 hE
  filter_upwards [hz, hσ.cont] with ω hω hc u hu
  by_contra hne
  have hpos : 0 < ∫ u in s..t, σ u ω * σ u ω :=
    intervalIntegral.integral_pos hst (hc.mul hc) (fun _ _ => mul_self_nonneg _)
      ⟨u, hu, mul_self_pos.2 hne⟩
  have : (∫ u in s..t, σ u ω * σ u ω) = 0 := hω
  linarith

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the precise extent of the book's product step.**
For Itô bonds `B` on `[s, t]`, `0 ≤ s < t`, the bracket-free step
`E_s[B_tX_t − B_sX_s] = E_s[∫_s^t B ν du + ∫_s^t X β du]` holds for EVERY Itô process `X`
(`= Λ/P`, any drift `ν`, any diffusion `σ_X`) **iff** bonds have no diffusive part,
`σ_B = 0` on `[s, t]` almost surely. Necessity: test with `X = ∫_s^· σ_B dW`
(`itoProcess_itoInt`), whose bracket with `B` is `∫σ_B² du`; sufficiency: `bond_step_bv`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBondStep.bookForm_forall_iff). -/
theorem bookForm_forall_iff (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hBo : ItoProcess μ 𝓕 W B β σB s t Cβ CB) :
    (∀ (X ν σX : ℝ → Ω → ℝ) (Cν CX : ℝ), ItoProcess μ 𝓕 W X ν σX s t Cν CX →
      μ[fun ω => B t ω * X t ω - B s ω * X s ω | 𝓕 s] =ᵐ[μ]
        μ[fun ω => dtInt μ 𝓕 (fun u ω => B u ω * ν u ω) s t ω
          + dtInt μ 𝓕 (fun u ω => X u ω * β u ω) s t ω | 𝓕 s]) ↔
      ∀ᵐ ω ∂μ, ∀ u ∈ Set.Icc s t, σB u ω = 0 := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  constructor
  · intro h
    have hX := itoProcess_itoInt (W := W) hBo.diff
    have h1 := (bond_step_book_iff hBM hWm h𝓕 hs hst hBo hX).1 (h _ _ _ _ _ hX)
    exact ae_zero_of_condExp_integral_sq hst hBo.diff h1
  · intro hσ X ν σX Cν CX hX
    exact bond_step_bv hBM hWm h𝓕 hs hst hBo hX hσ

end Cochrane.Generality.TidyR7ItoBondStep
