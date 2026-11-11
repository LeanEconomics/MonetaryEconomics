/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR10DoobIto
import Monetarism.TidyR7ItoProductRule
import Monetarism.TidyR10DoobProductStep

/-!
# The Itô isometry in Fubini form

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34) (Track 3, chunk B3, item 3b). For a
mean-square continuous integrand (`TidyR7ItoUnbounded.MSIntegrand`) I5d proved the isometry only
in Riemann-limit form (`TidyR7ItoUnbounded.tendsto_sum_integral_sq_ms`:
`Σ E[G_{t_i}²]Δt_i → E[(∫G dW)²]`). Here `u ↦ E[G_u²]` is shown continuous on `[s, t]`, so the
Riemann sums converge to the integral, and

`E[(∫_s^t G dW)²] = ∫_s^t E[G_u²] du`.

No joint measurability of `(u, ω) ↦ G_u(ω)` is assumed (it is not part of `MSIntegrand`), which is
why the right side is `∫E[G²]du`, not `E[∫G²du]`. For bounded integrands with a.s. continuous
paths both forms hold, so `E[∫_s^t H_u² du] = ∫_s^t E[H_u²] du` (`integral_integral_sq_comm`), a
Fubini identity obtained from the two isometries without Mathlib's product-measure Fubini.

## Main results

* `continuousOn_integral_sq_ms`: `u ↦ E[G_u²]` is continuous on `[s, t]`.
* `integral_itoInt_sq_ms` (**isometry, Fubini form**).
* `integral_integral_sq_comm`: `E[∫H²du] = ∫E[H²]du` for `TidyR7ItoIntegral.ItoIntegrand`.
* `doob_sq_itoInt_fubini_ms`: `E[(sup_{[s,T]}|X|)²] ≤ 4∫_s^T E[G_u²] du` for any a.s.
  right-continuous modification `X`.
* Non-vacuity on `TidyR7BrownianExist.bmPath`: `integral_itoInt_bm_sq_fubini_bmPath`
  (`E[(∫_0^1 W dW)²] = ∫_0^1 E[W_u²]du`, an unbounded integrand) and
  `integral_integral_cos_sq_bmPath` (`E[∫_0^1 cos² W_u du] = ∫_0^1 E[cos² W_u] du`).
-/

namespace Cochrane.Monetarism.TidyR10DoobFubini

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianExist Cochrane.Monetarism.TidyR7BrownianSchauder
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoIntegral Cochrane.Monetarism.TidyR7ItoUnbounded
  Cochrane.Monetarism.TidyR7ItoProcess Cochrane.Monetarism.TidyR7ItoProductRule
  Cochrane.Monetarism.TidyR7CondDominated Cochrane.Monetarism.TidyR10DoobIto
  Cochrane.Monetarism.TidyR10DoobProductStep
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ} {G : ℝ → Ω → ℝ} {s t : ℝ}

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `u ↦ E[G_u²]` is continuous on `[s, t]`** for a
mean-square continuous integrand: `|E[G_a²] − E[G_b²]|² ≤ E[(G_a − G_b)²]·E[(G_a + G_b)²]` and
`E[(G_a + G_b)²] ≤ 2E[(G_a − G_b)²] + 8E[G_b²]`. -/
theorem continuousOn_integral_sq_ms (hG : MSIntegrand P 𝓕 G s t) :
    ContinuousOn (fun u => ∫ ω, G u ω ^ 2 ∂P) (Set.Icc s t) := by
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  set fb := ∫ ω, G b ω ^ 2 ∂P with hfb
  have hfb0 : 0 ≤ fb := integral_nonneg fun _ => sq_nonneg _
  set η := min 1 (ε ^ 2 / (2 + 8 * fb + 1)) with hη
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη2 : η * (2 + 8 * fb) < ε ^ 2 := by
    have h1 : η ≤ ε ^ 2 / (2 + 8 * fb + 1) := min_le_right _ _
    have h2 : η * (2 + 8 * fb + 1) ≤ ε ^ 2 := by
      rw [le_div_iff₀ (by positivity)] at h1
      exact h1
    nlinarith
  obtain ⟨δ, hδ, hδb⟩ := hG.cont η hη0
  refine ⟨δ, hδ, fun a ha hab => ?_⟩
  rw [Real.dist_eq] at hab ⊢
  have hd := hδb a ha b hb hab.le
  have hma := hG.memLp a ha
  have hmb := hG.memLp b hb
  have hcs := sq_integral_mul_le (hma.sub hmb) (hma.add hmb)
  simp only [Pi.sub_apply, Pi.add_apply] at hcs
  have e1 : ∫ ω, (G a ω - G b ω) * (G a ω + G b ω) ∂P
      = ∫ ω, G a ω ^ 2 ∂P - ∫ ω, G b ω ^ 2 ∂P := by
    rw [← integral_sub hma.integrable_sq hmb.integrable_sq]
    exact integral_congr_ae (ae_of_all _ fun ω => by ring)
  have e2 : ∫ ω, (G a ω + G b ω) ^ 2 ∂P ≤ 2 * ∫ ω, (G a ω - G b ω) ^ 2 ∂P + 8 * fb := by
    have i1 : Integrable (fun ω => (G a ω - G b ω) ^ 2) P := (hma.sub hmb).integrable_sq
    have i2 : Integrable (fun ω => G b ω ^ 2) P := hmb.integrable_sq
    have i3 : Integrable (fun ω => (G a ω + G b ω) ^ 2) P := (hma.add hmb).integrable_sq
    calc ∫ ω, (G a ω + G b ω) ^ 2 ∂P
        ≤ ∫ ω, (2 * (G a ω - G b ω) ^ 2 + 8 * G b ω ^ 2) ∂P :=
          integral_mono i3 ((i1.const_mul 2).add (i2.const_mul 8)) fun ω => by
            nlinarith [sq_nonneg (G a ω - G b ω - 2 * G b ω)]
      _ = 2 * ∫ ω, (G a ω - G b ω) ^ 2 ∂P + 8 * fb := by
          rw [integral_add (i1.const_mul 2) (i2.const_mul 8), integral_const_mul,
            integral_const_mul]
  have hη' : ∫ ω, (G a ω - G b ω) ^ 2 ∂P ≤ η := hd
  have hnn : 0 ≤ ∫ ω, (G a ω - G b ω) ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
  have hsq : (∫ ω, G a ω ^ 2 ∂P - fb) ^ 2 < ε ^ 2 := by
    rw [← e1]
    calc _ ≤ (∫ ω, (G a ω - G b ω) ^ 2 ∂P) * ∫ ω, (G a ω + G b ω) ^ 2 ∂P := hcs
      _ ≤ η * (2 * η + 8 * fb) := by
          refine mul_le_mul hη' (e2.trans (by linarith)) (integral_nonneg fun _ => sq_nonneg _)
            hη0.le
      _ ≤ η * (2 + 8 * fb) := by nlinarith
      _ < ε ^ 2 := hη2
  have := (pow_lt_pow_iff_left₀ (abs_nonneg _) hε.le two_ne_zero).1 (by rwa [sq_abs])
  exact this

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Track 3, item 3b): the Itô isometry in Fubini
form** for a mean-square continuous integrand, `0 ≤ s ≤ t`:
`E[(∫_s^t G dW)²] = ∫_s^t E[G_u²] du`.
The integral form of `TidyR7ItoUnbounded.tendsto_sum_integral_sq_ms`. -/
theorem integral_itoInt_sq_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s ≤ t) (hG : MSIntegrand P 𝓕 G s t) :
    ∫ ω, itoInt P 𝓕 W G s t ω ^ 2 ∂P = ∫ u in s..t, ∫ ω, G u ω ^ 2 ∂P := by
  rcases hst.lt_or_eq with hst | hst
  · have h1 := tendsto_sum_integral_sq_ms hB hW h𝓕 hs hst hG _ (tendsto_mesh_dyadic hst)
    have h2 := tendsto_riemannSum (continuousOn_integral_sq_ms hG) _ (tendsto_mesh_dyadic hst)
    exact tendsto_nhds_unique h1 h2
  · rw [hst, itoInt_of_le le_rfl, intervalIntegral.integral_same]
    simp

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Track 3, item 3b): a Fubini identity for bounded
integrands**, `E[∫_s^t H_u² du] = ∫_s^t E[H_u²] du` for `H` admissible on `[s, t]`
(`TidyR7ItoIntegral.ItoIntegrand`), `0 ≤ s ≤ t`, from the two isometries
`TidyR7ItoIntegral.integral_itoInt_sq` and `integral_itoInt_sq_ms`. -/
theorem integral_integral_sq_comm {H : ℝ → Ω → ℝ} {C : ℝ} (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s ≤ t)
    (hH : ItoIntegrand P 𝓕 H s t C) :
    ∫ ω, (∫ u in s..t, H u ω ^ 2) ∂P = ∫ u in s..t, ∫ ω, H u ω ^ 2 ∂P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [← integral_itoInt_sq hB hW h𝓕 hs hst hH,
    integral_itoInt_sq_ms hB hW h𝓕 hs hst (TidyR7ItoUnbounded.ItoIntegrand.toMS hH)]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Track 3, items 1 and 3b): Doob's bound in Fubini
form.** For `G` mean-square continuous on `[s, T]`, `0 ≤ s < T`, and any modification `X` of
`t ↦ ∫_s^t G dW` with a.s. right-continuous paths on `[s, T]`,
`E[(sup_{[s,T]}|X|)²] ≤ 4∫_s^T E[G_u²] du`. -/
theorem doob_sq_itoInt_fubini_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {T : ℝ} (hs : 0 ≤ s) (hsT : s < T) (hG : MSIntegrand P 𝓕 G s T)
    {X : ℝ → Ω → ℝ} (hXI : ∀ t ∈ Set.Icc s T, X t =ᵐ[P] itoInt P 𝓕 W G s t)
    (hXr : ∀ᵐ ω ∂P, ∀ x ∈ Set.Icc s T, ContinuousWithinAt (fun u => X u ω) (Set.Icc x T) x) :
    Integrable (fun ω => pathSup s T X ω ^ 2) P ∧
      ∫ ω, pathSup s T X ω ^ 2 ∂P ≤ 4 * ∫ u in s..T, ∫ ω, G u ω ^ 2 ∂P := by
  have h := doob_sq_itoInt_ms hB hW h𝓕 hs hsT hG hXI hXr
  rw [integral_itoInt_sq_ms hB hW h𝓕 hs hsT.le hG] at h
  exact h

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Track 3, item 4, non-vacuity): the Fubini isometry
for the unbounded integrand `W`** on the constructed motion:
`E[(∫_0^1 W dW)²] = ∫_0^1 E[W_u²] du`, an instance of `integral_itoInt_sq_ms` (W is mean-square
continuous, `TidyR7ItoProcess.ItoProcess.toMS` of `TidyR7ItoProductRule.itoProcess_bm`). -/
theorem integral_itoInt_bm_sq_fubini_bmPath :
    ∫ ω, itoInt gaussSeq (bmFiltrationReal bmPath measurable_bmPath) bmPath (bmReal bmPath) 0 1
      ω ^ 2 ∂gaussSeq = ∫ u in (0 : ℝ)..1, ∫ ω, bmReal bmPath u ω ^ 2 ∂gaussSeq := by
  have h𝓕 := bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath
  exact integral_itoInt_sq_ms isPreBrownianReal_bmPath measurable_bmPath h𝓕 le_rfl zero_le_one
    ((itoProcess_bm isPreBrownianReal_bmPath measurable_bmPath h𝓕 le_rfl (t := 1)).toMS
      isPreBrownianReal_bmPath measurable_bmPath h𝓕 le_rfl)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Track 3, item 4, non-vacuity): the Fubini identity
for a random bounded integrand** on the constructed motion:
`E[∫_0^1 cos²(W_u) du] = ∫_0^1 E[cos²(W_u)] du`. -/
theorem integral_integral_cos_sq_bmPath :
    ∫ ω, (∫ u in (0 : ℝ)..1, Real.cos (bmReal bmPath u ω) ^ 2) ∂gaussSeq
      = ∫ u in (0 : ℝ)..1, ∫ ω, Real.cos (bmReal bmPath u ω) ^ 2 ∂gaussSeq :=
  integral_integral_sq_comm isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) le_rfl zero_le_one
    itoIntegrand_cos_bmPath

end Cochrane.Monetarism.TidyR10DoobFubini
