/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR12SDETools

/-!
# Itô processes with unbounded, mean-square continuous coefficients

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34) (Track 3, chunk B4). The class
`TidyR7ItoProcess.ItoProcess` asks for bounded drift and diffusion with a.s. continuous paths.
The solutions of stochastic differential equations that the §1.6 economy needs, such as the
geometric Brownian motion `dn = −i n dt + σ n dW` for a positive `Λ/P` with a known rate, have
unbounded coefficients (`σ n`). This module defines the wider class.

## The class

`ItoProcessMS P 𝓕 W X a H s t`: `X` adapted on `[s, t]`, `X_s` square integrable, drift `a` and
diffusion `H` mean-square continuous integrands (`TidyR7ItoUnbounded.MSIntegrand`: adapted,
square integrable, uniformly continuous in mean square; no bound and no path regularity), and
for every `u ∈ [s, t]`, almost surely `X_u = X_s + ∫_s^u a dr + ∫_s^u H dW`, with the
mean-square time integral `TidyR7ItoProducts.dtInt` and the Itô integral
`TidyR7ItoIntegral.itoInt`.

## Main results

* `ItoProcess.toItoProcessMS`: **every Itô process with bounded coefficients is one** (its
  pathwise drift integral is the mean-square one, `TidyR7ItoProducts.dtInt_ae_eq_integral`).
* `ItoProcessMS.memLp`, `ItoProcessMS.incr_eq` (`X_v − X_u = ∫_u^v a + ∫_u^v H dW` a.s.),
  `ItoProcessMS.integral_incr_sq_le` (`E[(X_v − X_u)²] ≤ 2(v − u)²M_a + 2(v − u)M_H`),
  `ItoProcessMS.toMS` (**an `ItoProcessMS` is itself a mean-square continuous integrand**),
  `ItoProcessMS.mono` (restriction to `[s', t'] ⊆ [s, t]`).
-/

namespace Cochrane.Monetarism.TidyR12SDEProcess

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoSums Cochrane.Monetarism.TidyR7ItoIntegral
  Cochrane.Monetarism.TidyR7ItoUnbounded Cochrane.Monetarism.TidyR7ItoProducts
  Cochrane.Monetarism.TidyR7ItoProcess Cochrane.Monetarism.TidyR8MonetarismItoDom
  Cochrane.Monetarism.TidyR12SDETools
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

variable (P : Measure Ω) (𝓕 : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ℝ) (X a H : ℝ → Ω → ℝ) (s t : ℝ)

/-- **Cochrane (2023), A1 §1.6, (1.32)–(1.34), pp. 567–568: an Itô process with mean-square
continuous coefficients on `[s, t]`** (for `Λ/P` solving an SDE with unbounded coefficients,
e.g. `dn = −i n dt + σ n dW`): `X` adapted, `X_s` square integrable, drift `a` and diffusion `H`
mean-square continuous integrands, and `X_u = X_s + ∫_s^u a dr + ∫_s^u H dW` a.s. for each
`u ∈ [s, t]` (mean-square time integral, Itô integral). -/
structure ItoProcessMS where
  adapted : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (X u)
  init : MemLp (X s) 2 P
  drift : MSIntegrand P 𝓕 a s t
  diff : MSIntegrand P 𝓕 H s t
  eq : ∀ u ∈ Set.Icc s t,
    X u =ᵐ[P] fun ω => X s ω + dtInt P 𝓕 a s u ω + itoInt P 𝓕 W H s u ω

variable {P 𝓕 W X a H s t}

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **an Itô process with bounded coefficients is an Itô
process with mean-square continuous coefficients** (`0 ≤ s`): its pathwise drift integral is
the mean-square one (`TidyR7ItoProducts.dtInt_ae_eq_integral`). -/
theorem ItoProcess.toItoProcessMS {Ca CH : ℝ} (hX : ItoProcess P 𝓕 W X a H s t Ca CH)
    (hB : IsPreBrownianReal W P) : ItoProcessMS P 𝓕 W X a H s t := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨hX.adapted, hX.init, ItoIntegrand.toMS hX.drift, ItoIntegrand.toMS hX.diff,
    fun u hu => ?_⟩
  have hd := dtInt_ae_eq_integral (𝓕 := 𝓕) hu.1 ((ItoIntegrand.toMS hX.drift).mono le_rfl hu.2)
    ((hX.drift.mono le_rfl hu.2).cont)
  filter_upwards [hX.eq u hu, hd] with ω h1 h2
  rw [h1, h2]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the values of an `ItoProcessMS` are square
integrable on `[s, t]`, `0 ≤ s`. -/
theorem ItoProcessMS.memLp (hX : ItoProcessMS P 𝓕 W X a H s t) (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {u : ℝ}
    (hu : u ∈ Set.Icc s t) : MemLp (X u) 2 P := by
  have h0 : MemLp (fun ω => X s ω + dtInt P 𝓕 a s u ω + itoInt P 𝓕 W H s u ω) 2 P :=
    (hX.init.add (memLp_dtInt (hX.drift.mono le_rfl hu.2))).add
      (memLp_itoInt_ms hB hW h𝓕 hs (hX.diff.mono le_rfl hu.2))
  exact h0.ae_eq (hX.eq u hu).symm

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: increments of an `ItoProcessMS`**: for
`s ≤ u ≤ v ≤ t`, `0 ≤ s`, a.s. `X_v − X_u = ∫_u^v a dr + ∫_u^v H dW`. -/
theorem ItoProcessMS.incr_eq (hX : ItoProcessMS P 𝓕 W X a H s t) (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {u v : ℝ}
    (hsu : s ≤ u) (huv : u ≤ v) (hvt : v ≤ t) :
    (fun ω => X v ω - X u ω) =ᵐ[P]
      fun ω => dtInt P 𝓕 a u v ω + itoInt P 𝓕 W H u v ω := by
  have hu : u ∈ Set.Icc s t := ⟨hsu, huv.trans hvt⟩
  have hv : v ∈ Set.Icc s t := ⟨hsu.trans huv, hvt⟩
  filter_upwards [hX.eq u hu, hX.eq v hv,
    itoInt_add_itoInt_ms hB hW h𝓕 hs hsu huv (hX.diff.mono le_rfl hvt),
    dtInt_add_dtInt hsu huv (hX.drift.mono le_rfl hvt)] with ω h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  ring

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the mean-square increment bound.** If
`E[a_r²] ≤ Ma` and `E[H_r²] ≤ MH` on `[s, t]`, then for `s ≤ u ≤ v ≤ t`, `0 ≤ s`,
`E[(X_v − X_u)²] ≤ 2(v − u)²Ma + 2(v − u)MH`.
The analogue of `TidyR7ItoProcess.ItoProcess.integral_incr_sq_le`. -/
theorem ItoProcessMS.integral_incr_sq_le (hX : ItoProcessMS P 𝓕 W X a H s t)
    (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕)
    (hs : 0 ≤ s) {Ma MH : ℝ} (hMa : ∀ r ∈ Set.Icc s t, ∫ ω, a r ω ^ 2 ∂P ≤ Ma)
    (hMH : ∀ r ∈ Set.Icc s t, ∫ ω, H r ω ^ 2 ∂P ≤ MH) {u v : ℝ} (hsu : s ≤ u) (huv : u ≤ v)
    (hvt : v ≤ t) :
    ∫ ω, (X v ω - X u ω) ^ 2 ∂P ≤ 2 * (v - u) ^ 2 * Ma + 2 * (v - u) * MH := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have ha := hX.drift.mono hsu hvt
  have hH := hX.diff.mono hsu hvt
  have iD := memLp_dtInt ha
  have iI := memLp_itoInt_ms hB hW h𝓕 (hs.trans hsu) hH
  have hMa' : ∀ r ∈ Set.Icc u v, ∫ ω, a r ω ^ 2 ∂P ≤ Ma := fun r hr =>
    hMa r ⟨hsu.trans hr.1, hr.2.trans hvt⟩
  have hMH' : ∀ r ∈ Set.Icc u v, ∫ ω, H r ω ^ 2 ∂P ≤ MH := fun r hr =>
    hMH r ⟨hsu.trans hr.1, hr.2.trans hvt⟩
  have b1 := integral_dtInt_sq_le_const huv ha hMa'
  have b2 := integral_itoInt_sq_le_const hB hW h𝓕 (hs.trans hsu) huv hH hMH'
  have e : ∫ ω, (X v ω - X u ω) ^ 2 ∂P
      = ∫ ω, (dtInt P 𝓕 a u v ω + itoInt P 𝓕 W H u v ω) ^ 2 ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hX.incr_eq hB hW h𝓕 hs hsu huv hvt] with ω h
    rw [h]
  rw [e]
  calc ∫ ω, (dtInt P 𝓕 a u v ω + itoInt P 𝓕 W H u v ω) ^ 2 ∂P
      ≤ ∫ ω, (2 * dtInt P 𝓕 a u v ω ^ 2 + 2 * itoInt P 𝓕 W H u v ω ^ 2) ∂P :=
        integral_mono (iD.add iI).integrable_sq
          ((iD.integrable_sq.const_mul 2).add (iI.integrable_sq.const_mul 2))
          fun ω => add_sq_le_two _ _
    _ = 2 * ∫ ω, dtInt P 𝓕 a u v ω ^ 2 ∂P + 2 * ∫ ω, itoInt P 𝓕 W H u v ω ^ 2 ∂P := by
        rw [integral_add (iD.integrable_sq.const_mul 2) (iI.integrable_sq.const_mul 2),
          integral_const_mul, integral_const_mul]
    _ ≤ 2 * ((v - u) ^ 2 * Ma) + 2 * ((v - u) * MH) := by linarith
    _ = 2 * (v - u) ^ 2 * Ma + 2 * (v - u) * MH := by ring

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: an Itô process with mean-square continuous
coefficients is a mean-square continuous integrand** on `[s, t]`, `0 ≤ s`, so
`TidyR7ItoUnbounded` integrates it.
The analogue of `TidyR7ItoProcess.ItoProcess.toMS`. -/
theorem ItoProcessMS.toMS (hX : ItoProcessMS P 𝓕 W X a H s t) (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) :
    MSIntegrand P 𝓕 X s t where
  adapted := hX.adapted
  memLp _ hu := hX.memLp hB hW h𝓕 hs hu
  cont ε hε := by
    obtain ⟨Ma, hMa0, hMa⟩ := exists_bound_integral_sq_ms hX.drift
    obtain ⟨MH, hMH0, hMH⟩ := exists_bound_integral_sq_ms hX.diff
    set δ := min 1 (ε / (2 * Ma + 2 * MH + 1)) with hδ
    have hδ0 : 0 < δ := lt_min one_pos (by positivity)
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδ2 : δ * (2 * Ma + 2 * MH + 1) ≤ ε := by
      have h := min_le_right 1 (ε / (2 * Ma + 2 * MH + 1))
      rw [← hδ, le_div_iff₀ (by positivity)] at h
      exact h
    have key : ∀ u v, s ≤ u → u ≤ v → v ≤ t → v - u ≤ δ →
        ∫ ω, (X v ω - X u ω) ^ 2 ∂P ≤ ε := by
      intro u v hsu huv hvt hd
      have h := hX.integral_incr_sq_le hB hW h𝓕 hs hMa hMH hsu huv hvt
      have h0 : 0 ≤ v - u := sub_nonneg.2 huv
      have h1 : (v - u) ^ 2 ≤ δ := by nlinarith
      nlinarith
    refine ⟨δ, hδ0, fun u hu v hv huv => ?_⟩
    rcases le_total u v with h | h
    · have e : ∫ ω, (X u ω - X v ω) ^ 2 ∂P = ∫ ω, (X v ω - X u ω) ^ 2 ∂P :=
        integral_congr_ae (ae_of_all _ fun ω => by ring)
      rw [e]
      exact key u v hu.1 h hv.2 (by rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)] at huv
                                    exact huv)
    · exact key v u hv.1 h hu.2 (by rw [abs_of_nonneg (sub_nonneg.2 h)] at huv; exact huv)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **an `ItoProcessMS` on `[s, t]` is one on every
`[s', t'] ⊆ [s, t]`**, `0 ≤ s` (start the integrals at `s'` by additivity). -/
theorem ItoProcessMS.mono (hX : ItoProcessMS P 𝓕 W X a H s t) (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {s' t' : ℝ}
    (hss' : s ≤ s') (hs't' : s' ≤ t') (ht't : t' ≤ t) : ItoProcessMS P 𝓕 W X a H s' t' where
  adapted u hu := hX.adapted u ⟨hss'.trans hu.1, hu.2.trans ht't⟩
  init := hX.memLp hB hW h𝓕 hs ⟨hss', hs't'.trans ht't⟩
  drift := hX.drift.mono hss' ht't
  diff := hX.diff.mono hss' ht't
  eq u hu := by
    filter_upwards [hX.incr_eq hB hW h𝓕 hs hss' hu.1 (hu.2.trans ht't)] with ω h
    linarith

end Cochrane.Monetarism.TidyR12SDEProcess
