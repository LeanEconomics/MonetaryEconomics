/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR10DoobContinuous
import Monetarism.TidyR7ItoContinuity
import Monetarism.TidyR7ItoBridge
import Monetarism.TidyR8MonetarismItoDom

/-!
# Doob's `L²` inequality for Brownian motion and for Itô integrals

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for (1.32) with diffusive
bonds (Track 3, chunk B3, item 1): `TidyR10DoobContinuous.doob_sq_pathSup` applied to the
Brownian motion and to the Itô integral `t ↦ ∫_s^t G dW`.

## Main results

* `doob_sq_bm`: `E[(sup_{[s,T]}|W|)²] ≤ 4E[W_T²]` for a pre-Brownian `W` with a.s. continuous
  paths and any admissible filtration (`TidyR7BrownianQV.BMFiltration`).
* `integral_mul_itoInt_sub_ms`: the increments `∫_s^T G dW − ∫_s^u G dW` are orthogonal to the
  square-integrable `𝓕_u`-measurable past, for a mean-square continuous integrand
  (`TidyR7ItoUnbounded.MSIntegrand`).
* `doob_sq_itoInt_ms`: for a mean-square continuous `G` and ANY modification `X` of
  `t ↦ ∫_s^t G dW` with a.s. right-continuous paths on `[s, T]`,
  `E[(sup_{[s,T]}|X|)²] ≤ 4E[(∫_s^T G dW)²]`.
* `doob_sq_itoInt` (bounded integrands, `TidyR7ItoIntegral.ItoIntegrand`):
  `E[(sup_{[s,T]}|X|)²] ≤ 4E[∫_s^T H_u² du]`; `exists_continuous_modification_doob`: the
  continuous modification of `TidyR7ItoContinuity.exists_continuous_modification` satisfies it.
* Non-vacuity on the constructed motion `TidyR7BrownianExist.bmPath`: `doob_sq_bmPath`
  (`E[(sup_{[0,T]}|W|)²] ≤ 4T`) and `doob_sq_itoInt_id_bmPath` (a continuous version of
  `∫_0^t u dW_u` with `E[(sup_{[0,1]}|X|)²] ≤ 4/3`).
-/

namespace Cochrane.Monetarism.TidyR10DoobIto

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianExist Cochrane.Monetarism.TidyR7BrownianSchauder
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoSums Cochrane.Monetarism.TidyR7ItoIntegral
  Cochrane.Monetarism.TidyR7ItoContinuity Cochrane.Monetarism.TidyR7ItoUnbounded
  Cochrane.Monetarism.TidyR7ItoBridge Cochrane.Monetarism.TidyR7CondDominated
  Cochrane.Monetarism.TidyR10DoobContinuous Cochrane.Monetarism.TidyR8MonetarismItoDom
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ} {s T : ℝ}

/-- Cochrane (2023), A1 §1.6, p. 567: a path continuous on `[s, T]` is right-continuous on
`[s, T]` in the sense of `TidyR10DoobContinuous.doob_sq_pathSup`. -/
theorem rightCont_of_continuousOn {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc s T)) :
    ∀ x ∈ Set.Icc s T, ContinuousWithinAt f (Set.Icc x T) x := fun x hx =>
  (hf x hx).mono (Set.Icc_subset_Icc_left hx.1)

/-! ## Brownian motion -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Track 3, item 1): Doob's `L²` inequality for
Brownian motion.** For a pre-Brownian `W` with measurable values and a.s. continuous paths, any
admissible filtration and `s < T`, `(sup_{[s,T]}|W|)²` is integrable and
`E[(sup_{[s,T]}|W|)²] ≤ 4E[W_T²]`. -/
theorem doob_sq_bm (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ᵐ ω ∂P, Continuous fun t => W t ω) (hsT : s < T) :
    Integrable (fun ω => pathSup s T (bmReal W) ω ^ 2) P ∧
      ∫ ω, pathSup s T (bmReal W) ω ^ 2 ∂P ≤ 4 * ∫ ω, bmReal W T ω ^ 2 ∂P := by
  have hmem : ∀ u, MemLp (bmReal W u) 2 P := fun u =>
    (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
  refine doob_sq_pathSup (𝓕 := 𝓕) hsT (fun u _ => h𝓕.adapted u) (fun u _ => hmem u)
    (fun u hu G hG _ => ?_) (fun _ _ => ae_of_all _ fun _ => rfl) ?_
  · exact integral_mul_incr hB hW h𝓕 hu.2 hG
  · filter_upwards [hcont] with ω hω
    exact rightCont_of_continuousOn (continuous_bmReal hω).continuousOn

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Track 3, item 4, non-vacuity): Doob's inequality on
the constructed motion**, `E[(sup_{[0,T]}|W|)²] ≤ 4T` for `TidyR7BrownianExist.bmPath`,
`T > 0`. -/
theorem doob_sq_bmPath {T : ℝ} (hT : 0 < T) :
    Integrable (fun ω => pathSup 0 T (bmReal bmPath) ω ^ 2) gaussSeq ∧
      ∫ ω, pathSup 0 T (bmReal bmPath) ω ^ 2 ∂gaussSeq ≤ 4 * T := by
  have h := doob_sq_bm isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath)
    (ae_of_all _ continuous_bmPath) hT
  have e : ∫ ω, bmReal bmPath T ω ^ 2 ∂gaussSeq = T := by
    have h2 := integral_incr_sq (W := bmPath) isPreBrownianReal_bmPath le_rfl hT.le
    simpa [incr, bmReal, bmPath_zero] using h2
  rw [e] at h
  exact h

/-! ## Itô integrals -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the Itô integral has orthogonal increments.** For a
mean-square continuous integrand on `[s, T]`, `0 ≤ s`, `u ∈ [s, T]` and a square-integrable
`𝓕_u`-strongly measurable `Z`, `E[Z(∫_s^T G dW − ∫_s^u G dW)] = 0`.
The increment form of `TidyR7ItoUnbounded.integral_mul_itoInt_ms`. -/
theorem integral_mul_itoInt_sub_ms {G : ℝ → Ω → ℝ} (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s)
    (hG : MSIntegrand P 𝓕 G s T) {u : ℝ} (hu : u ∈ Set.Icc s T) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[𝓕 u] Z) (hZ2 : MemLp Z 2 P) :
    ∫ ω, Z ω * (itoInt P 𝓕 W G s T ω - itoInt P 𝓕 W G s u ω) ∂P = 0 := by
  have hadd := itoInt_add_itoInt_ms hB hW h𝓕 hs hu.1 hu.2 hG
  rw [← integral_mul_itoInt_ms hB hW h𝓕 (hs.trans hu.1) (hG.mono hu.1 le_rfl) hZ hZ2]
  refine integral_congr_ae ?_
  filter_upwards [hadd] with ω hω
  rw [hω]
  ring

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Track 3, item 1): Doob's `L²` inequality for the
Itô integral of a mean-square continuous integrand.** Let `0 ≤ s < T`, `G` mean-square
continuous on `[s, T]` (`TidyR7ItoUnbounded.MSIntegrand`), and `X` any modification of
`t ↦ ∫_s^t G dW` on `[s, T]` with a.s. right-continuous paths. Then `(sup_{[s,T]}|X|)²` is
integrable and `E[(sup_{[s,T]}|X|)²] ≤ 4E[(∫_s^T G dW)²]`. -/
theorem doob_sq_itoInt_ms {G : ℝ → Ω → ℝ} (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hsT : s < T)
    (hG : MSIntegrand P 𝓕 G s T) {X : ℝ → Ω → ℝ}
    (hXI : ∀ t ∈ Set.Icc s T, X t =ᵐ[P] itoInt P 𝓕 W G s t)
    (hXr : ∀ᵐ ω ∂P, ∀ x ∈ Set.Icc s T, ContinuousWithinAt (fun u => X u ω) (Set.Icc x T) x) :
    Integrable (fun ω => pathSup s T X ω ^ 2) P ∧
      ∫ ω, pathSup s T X ω ^ 2 ∂P ≤ 4 * ∫ ω, itoInt P 𝓕 W G s T ω ^ 2 ∂P := by
  have h := doob_sq_pathSup (𝓕 := 𝓕) (Y := fun t => itoInt P 𝓕 W G s t) hsT
    (fun u _ => stronglyMeasurable_itoInt)
    (fun u hu => memLp_itoInt_ms hB hW h𝓕 hs (hG.mono le_rfl hu.2))
    (fun u hu Z hZ hZ2 => integral_mul_itoInt_sub_ms hB hW h𝓕 hs hG hu hZ hZ2) hXI hXr
  have e : ∫ ω, X T ω ^ 2 ∂P = ∫ ω, itoInt P 𝓕 W G s T ω ^ 2 ∂P :=
    integral_congr_ae ((hXI T ⟨hsT.le, le_rfl⟩).mono fun ω hω => by simp only [hω])
  rw [e] at h
  exact h

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Track 3, item 1): Doob's `L²` inequality for the
Itô integral of a bounded integrand.** For `H` admissible on `[s, T]`
(`TidyR7ItoIntegral.ItoIntegrand`), `0 ≤ s < T`, and any modification `X` of `t ↦ ∫_s^t H dW`
on `[s, T]` with a.s. right-continuous paths:
`E[(sup_{[s,T]}|X|)²] ≤ 4E[∫_s^T H_u² du]` (Doob and the Itô isometry). -/
theorem doob_sq_itoInt {H : ℝ → Ω → ℝ} {C : ℝ} (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hsT : s < T)
    (hH : ItoIntegrand P 𝓕 H s T C) {X : ℝ → Ω → ℝ}
    (hXI : ∀ t ∈ Set.Icc s T, X t =ᵐ[P] itoInt P 𝓕 W H s t)
    (hXr : ∀ᵐ ω ∂P, ∀ x ∈ Set.Icc s T, ContinuousWithinAt (fun u => X u ω) (Set.Icc x T) x) :
    Integrable (fun ω => pathSup s T X ω ^ 2) P ∧
      ∫ ω, pathSup s T X ω ^ 2 ∂P ≤ 4 * ∫ ω, (∫ u in s..T, H u ω ^ 2) ∂P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h := doob_sq_itoInt_ms hB hW h𝓕 hs hsT (TidyR7ItoUnbounded.ItoIntegrand.toMS hH) hXI hXr
  rw [integral_itoInt_sq hB hW h𝓕 hs hsT.le hH] at h
  exact h

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Track 3, item 1): the continuous modification
satisfies Doob's bound.** If `W` has a.s. continuous paths, `H` is admissible on `[s, T]`,
`0 ≤ s < T`, there is `X` with `X_t = ∫_s^t H dW` a.s. for each `t ∈ [s, T]`, a.s. continuous
paths on `[s, T]`, `(sup_{[s,T]}|X|)²` integrable and
`E[(sup_{[s,T]}|X|)²] ≤ 4E[∫_s^T H_u² du]`.
Uses `TidyR7ItoContinuity.exists_continuous_modification`. -/
theorem exists_continuous_modification_doob {H : ℝ → Ω → ℝ} {C : ℝ}
    (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => W t ω) (hs : 0 ≤ s) (hsT : s < T)
    (hH : ItoIntegrand P 𝓕 H s T C) :
    ∃ X : ℝ → Ω → ℝ, (∀ t ∈ Set.Icc s T, X t =ᵐ[P] itoInt P 𝓕 W H s t) ∧
      (∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Icc s T)) ∧
      Integrable (fun ω => pathSup s T X ω ^ 2) P ∧
      ∫ ω, pathSup s T X ω ^ 2 ∂P ≤ 4 * ∫ ω, (∫ u in s..T, H u ω ^ 2) ∂P := by
  obtain ⟨X, hXI, hXc⟩ := exists_continuous_modification hB hW h𝓕 hcont hs hsT hH
  exact ⟨X, hXI, hXc, doob_sq_itoInt hB hW h𝓕 hs hsT hH hXI
    (hXc.mono fun _ hω => rightCont_of_continuousOn hω)⟩

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the deterministic integrand `u ↦ u` is admissible on
`[0, 1]` for any filtration, with bound `1`. -/
theorem itoIntegrand_id_unit {𝓖 : Filtration ℝ mΩ} :
    ItoIntegrand P 𝓖 (fun u _ => u) 0 1 1 where
  adapted _ _ := stronglyMeasurable_const
  bound u hu _ := by
    rw [abs_of_nonneg hu.1]
    exact hu.2
  cont := ae_of_all _ fun _ => continuousOn_id

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Track 3, item 4, non-vacuity): Doob's inequality
for a Wiener integral on the constructed motion.** For `TidyR7BrownianExist.bmPath` and its
natural filtration there is a continuous modification `X` of `t ↦ ∫_0^t u dW_u` on `[0, 1]`
with `E[(sup_{[0,1]}|X|)²] ≤ 4·E[(∫_0^1 u dW_u)²] = 4/3`. -/
theorem doob_sq_itoInt_id_bmPath :
    ∃ X : ℝ → (ℕ → ℝ) → ℝ, (∀ t ∈ Set.Icc (0 : ℝ) 1, X t =ᵐ[gaussSeq]
        itoInt gaussSeq (bmFiltrationReal bmPath measurable_bmPath) bmPath (fun u _ => u) 0 t) ∧
      (∀ᵐ ω ∂gaussSeq, ContinuousOn (fun t => X t ω) (Set.Icc 0 1)) ∧
      Integrable (fun ω => pathSup 0 1 X ω ^ 2) gaussSeq ∧
      ∫ ω, pathSup 0 1 X ω ^ 2 ∂gaussSeq ≤ 4 / 3 := by
  have : IsProbabilityMeasure gaussSeq :=
    isPreBrownianReal_bmPath.isGaussianProcess.isProbabilityMeasure
  have h𝓕 := bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath
  obtain ⟨X, hXI, hXc⟩ := exists_continuous_modification isPreBrownianReal_bmPath
    measurable_bmPath h𝓕 (ae_of_all _ continuous_bmPath) le_rfl zero_lt_one itoIntegrand_id_unit
  have h := doob_sq_itoInt_ms isPreBrownianReal_bmPath measurable_bmPath h𝓕 le_rfl zero_lt_one
    (TidyR7ItoUnbounded.ItoIntegrand.toMS (P := gaussSeq) itoIntegrand_id_unit) hXI
    (hXc.mono fun _ hω => rightCont_of_continuousOn hω)
  rw [integral_itoInt_id_bmPath_sq] at h
  refine ⟨X, hXI, hXc, h.1, ?_⟩
  linarith [h.2]

end Cochrane.Monetarism.TidyR10DoobIto
