/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR7GuidanceItoValuation

/-!
# The continuous-time forward-guidance formula announced at a general date `t`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.2.1,
pp. 559–561. The valuation equation of p. 559 holds at every date `t`:
`∫_0^∞ Q_t^{(t+j)} B_t^{(t+j)} dj / P_t = E_t ∫_0^∞ e^{−rj} s_{t+j} dj`. The forward-guidance
formula of p. 561 is derived for an announcement at `0`; here it is proved for an
announcement at an arbitrary date `a ≥ 0`, for a general filtration `𝓕` of the Brownian motion
`W` (TidyR7GuidanceItoValuation treats `a = 0`).

## Setting

`GuidanceSDFAt P 𝓕 W Λ H K r ι a τ`: from the announcement date `a` the short rate is `r` on
`[a, a + τ]` and `ι` (known at `a + τ`) after, `dΛ = −rΛ dt + H dW` on `[a, a + τ]`,
`dΛ = −ιΛ dt + K dW` on every `[a + τ, t]` (`TidyR7GuidanceSDF.SDFPiece`). The debt at `a` is
the geometric portfolio `B_a^{(a+j)} = ϖ e^{−ϖj} B_a`; its value per unit is
`debtValueAt = E_a[∫_0^∞ ϖe^{−ϖj} Λ_{a+j} dj]/Λ_a`, and the surpluses are valued by
`pvSurplusAt = E_a ∫_0^∞ e^{−rj} s_{a+j} dj`. `debtValueAt_eq_Ioi` and `pvSurplusAt_eq_Ioi`
restate them in the book's form `∫_a^∞ ϖ e^{−ϖ(j−a)} Λ_j dj`, `∫_a^∞ e^{−r(j−a)} s_j dj`.

## Main results

* `condExp_guidanceAt`: `E_a Λ_{a+j} = e^{−(r min(j,τ) + i max(j−τ,0))} Λ_a` for a known path.
* `condExp_debtValueAt` (**the interchange `E_a ∫ = ∫ E_a` at date `a`**):
  `E_a ∫_0^∞ ϖe^{−ϖj} Λ_{a+j} dj = cfgValue r i ϖ τ · Λ_a`; `condExp_debtValueAt_Ioi` in the
  book's form; `debtValueAt_guidance`: the value per unit is `cfgValue r i ϖ τ` on `Λ_a ≠ 0`.
* `guidance_jump_at` (**verbatim, state by state, at date `a`**):
  `P_a/P_a' − 1 = e^{−(r+ϖ)τ}((r+ϖ)/(i+ϖ) − 1)` a.s. on `Λ_a, Λ'_a ≠ 0`.
* `condExp_debtValueAt_random`, `random_jump_at` (**the random-rate correction at date `a`**):
  with the rate after `a + τ` news revealed at `a + τ`,
  `P_a/P_a' − 1 = E_a[e^{rτ} Λ_{a+τ} cfgJump r ι ϖ τ]/Λ_a`.
* `GuidanceSDF.toAt`, `debtValueAt_zero`, `pvSurplusAt_zero`: `a = 0` is the date-0 setting.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR8GuidanceDateT

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.LongTermDebtDynamics.TidyR7BrownianTools
  Cochrane.LongTermDebtDynamics.TidyR7BrownianQV Cochrane.LongTermDebtDynamics.TidyR7ItoIntegral
  Cochrane.LongTermDebtDynamics.TidyR7GuidanceSDF
  Cochrane.LongTermDebtDynamics.TidyR7GuidanceItoValuation
  Cochrane.LongTermDebtDynamics.ForwardGuidance
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → ℝ}

variable (P 𝓕 W) (Λ H K : ℝ → Ω → ℝ) (r : ℝ) (ι : Ω → ℝ) (a τ : ℝ)

/-- **Cochrane (2023), Online Appendix §A1.2.1, pp. 559–561 (under uncertainty): the nominal
discount factor under an announcement made at date `a`.** The short rate is `r` on
`[a, a + τ]` and `ι` on `[a + τ, ∞)`: `dΛ = −rΛ dt + H dW` on `[a, a + τ]` and
`dΛ = −ιΛ dt + K dW` on every `[a + τ, t]`, `ι` known at `a + τ`.
Generalises `TidyR7GuidanceItoValuation.GuidanceSDF` to an announcement at date `a`. -/
structure GuidanceSDFAt where
  pre : ∃ C, SDFPiece P 𝓕 W Λ H (fun _ => r) a (a + τ) C
  post : ∀ t, a + τ ≤ t → ∃ C, SDFPiece P 𝓕 W Λ K ι (a + τ) t C

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 559 (under uncertainty): the market value at
date `a` of the geometric debt portfolio `B_a^{(a+j)} = ϖe^{−ϖj}B_a` per unit of `B_a`, over
`P_a`: `E_a[∫_0^∞ ϖe^{−ϖj} Λ_{a+j} dj]/Λ_a` (the book's `∫_0^∞ Q_a^{(a+j)}ϖe^{−ϖj} dj`).
Generalises `TidyR7GuidanceItoValuation.debtValue` to an announcement at date `a`. -/
noncomputable def debtValueAt (ϖ : ℝ) : Ω → ℝ := fun ω =>
  P[fun ω' => ∫ j in Set.Ioi (0 : ℝ), ϖ * Real.exp (-ϖ * j) * Λ (a + j) ω' | 𝓕 a] ω / Λ a ω

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 559 (under uncertainty): the present value of
surpluses at date `a`, `E_a ∫_0^∞ e^{−rj} s_{a+j} dj`.
Generalises `TidyR7GuidanceItoValuation.pvSurplus` to an announcement at date `a`. -/
noncomputable def pvSurplusAt (s : ℝ → Ω → ℝ) : Ω → ℝ :=
  P[fun ω => ∫ j in Set.Ioi (0 : ℝ), Real.exp (-r * j) * s (a + j) ω | 𝓕 a]

variable {P 𝓕 W Λ H K r ι a τ}

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 559: the change of variables `j ↦ a + j`,
`∫_0^∞ f(a + j) dj = ∫_a^∞ f(j) dj` (translation invariance of Lebesgue measure, Mathlib
`MeasurePreserving.setIntegral_preimage_emb`). -/
theorem setIntegral_Ioi_shift (a : ℝ) (f : ℝ → ℝ) :
    ∫ j in Set.Ioi (0 : ℝ), f (a + j) = ∫ j in Set.Ioi a, f j := by
  have h := (measurePreserving_add_left volume a).setIntegral_preimage_emb
    (measurableEmbedding_addLeft a) f (Set.Ioi a)
  rw [Set.preimage_const_add_Ioi, sub_self] at h
  exact h

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 559: the debt value at `a` in the book's form,
`E_a[∫_a^∞ ϖe^{−ϖ(j−a)} Λ_j dj]/Λ_a`. -/
theorem debtValueAt_eq_Ioi (ϖ : ℝ) : debtValueAt P 𝓕 Λ a ϖ = fun ω =>
    P[fun ω' => ∫ j in Set.Ioi a, ϖ * Real.exp (-ϖ * (j - a)) * Λ j ω' | 𝓕 a] ω / Λ a ω := by
  have e : (fun ω' => ∫ j in Set.Ioi a, ϖ * Real.exp (-ϖ * (j - a)) * Λ j ω') =
      fun ω' => ∫ j in Set.Ioi (0 : ℝ), ϖ * Real.exp (-ϖ * j) * Λ (a + j) ω' := by
    funext ω'
    rw [← setIntegral_Ioi_shift a]
    simp only [add_sub_cancel_left]
  rw [e]
  rfl

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 559: the present value of surpluses at `a` in
the book's form, `E_a ∫_a^∞ e^{−r(j−a)} s_j dj`. -/
theorem pvSurplusAt_eq_Ioi (s : ℝ → Ω → ℝ) : pvSurplusAt P 𝓕 r a s =
    P[fun ω => ∫ j in Set.Ioi a, Real.exp (-r * (j - a)) * s j ω | 𝓕 a] := by
  have e : (fun ω => ∫ j in Set.Ioi a, Real.exp (-r * (j - a)) * s j ω) =
      fun ω => ∫ j in Set.Ioi (0 : ℝ), Real.exp (-r * j) * s (a + j) ω := by
    funext ω
    rw [← setIntegral_Ioi_shift a]
    simp only [add_sub_cancel_left]
  rw [e]
  rfl

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the date-0 announcement structure
`TidyR7GuidanceItoValuation.GuidanceSDF` is the case `a = 0` of `GuidanceSDFAt`. -/
theorem GuidanceSDF.toAt {T : ℝ} (hΛ : GuidanceSDF P 𝓕 W Λ H K r ι T) :
    GuidanceSDFAt P 𝓕 W Λ H K r ι 0 T where
  pre := by simpa only [zero_add] using hΛ.pre
  post := by simpa only [zero_add] using hΛ.post

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: at `a = 0`, `debtValueAt` is the date-0
debt value `TidyR7GuidanceItoValuation.debtValue`. -/
theorem debtValueAt_zero (ϖ : ℝ) : debtValueAt P 𝓕 Λ 0 ϖ = debtValue P 𝓕 Λ ϖ := by
  funext ω
  rw [debtValueAt, debtValue]
  simp only [zero_add]

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 559: at `a = 0`, `pvSurplusAt` is the date-0
present value `TidyR7GuidanceItoValuation.pvSurplus`. -/
theorem pvSurplusAt_zero (s : ℝ → Ω → ℝ) : pvSurplusAt P 𝓕 r 0 s = pvSurplus P 𝓕 r s := by
  simp only [pvSurplusAt, pvSurplus, zero_add]

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561 (under uncertainty): bond prices at the
announcement date `a`.** With rate `r` on `[a, a + τ]` and a deterministic `i` after,
`E[Λ_{a+j} | 𝓕_a] = e^{−(r min(j,τ) + i max(j−τ,0))} Λ_a` a.s. for every `j ≥ 0`
(`a ≥ 0`, `τ ≥ 0`).
Generalises `TidyR7GuidanceItoValuation.condExp_guidance` to an announcement at date `a`. -/
theorem condExp_guidanceAt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (ha : 0 ≤ a) (hτ : 0 ≤ τ) {i : ℝ}
    (hΛ : GuidanceSDFAt P 𝓕 W Λ H K r (fun _ => i) a τ) {j : ℝ} (hj : 0 ≤ j) :
    P[Λ (a + j) | 𝓕 a] =ᵐ[P]
      fun ω => Real.exp (-(r * min j τ + i * max (j - τ) 0)) * Λ a ω := by
  obtain ⟨C, hpre⟩ := hΛ.pre
  rcases le_or_gt j τ with hjT | hjT
  · have h := condExp_sdf_const hB hW h𝓕 ha hpre (u := a + j) ⟨by linarith, by linarith⟩
    refine h.trans (ae_of_all _ fun ω => ?_)
    simp only [min_eq_left hjT, max_eq_right (sub_nonpos.2 hjT), mul_zero, add_zero]
    ring_nf
  · obtain ⟨C', hpost⟩ := hΛ.post (a + j) (by linarith)
    have h1 := condExp_sdf_const hB hW h𝓕 (by linarith) hpost (u := a + j)
      ⟨by linarith, le_rfl⟩
    have h2 := condExp_sdf_const hB hW h𝓕 ha hpre (u := a + τ) ⟨by linarith, le_rfl⟩
    have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
    have h3 := (condExp_condExp_of_le (μ := P) (f := Λ (a + j))
      (𝓕.mono (by linarith : a ≤ a + τ)) (𝓕.le (a + τ))).symm
    have h4 : P[P[Λ (a + j) | 𝓕 (a + τ)] | 𝓕 a] =ᵐ[P]
        P[(Real.exp (-i * (a + j - (a + τ)))) • Λ (a + τ) | 𝓕 a] :=
      condExp_congr_ae (h1.trans (ae_of_all _ fun ω => by simp [smul_eq_mul]))
    have h5 := condExp_smul (μ := P) (Real.exp (-i * (a + j - (a + τ)))) (Λ (a + τ)) (𝓕 a)
    filter_upwards [h3, h4, h5, h2] with ω e3 e4 e5 e2
    rw [e3, e4, e5, Pi.smul_apply, e2, smul_eq_mul, min_eq_right hjT.le,
      max_eq_left (sub_nonneg.2 hjT.le), ← mul_assoc, ← Real.exp_add]
    congr 2
    ring

/-- **Cochrane (2023), Online Appendix §A1.2.1, pp. 559–561 (under uncertainty): the
interchange `E_a ∫_0^∞ = ∫_0^∞ E_a` for the debt at the announcement date `a`.** Under a known
announced path (`r` on `[a, a + τ]`, `i` after), with `r + ϖ > 0`, `i + ϖ > 0`, `a, τ ≥ 0` and
`(j, ω) ↦ ϖe^{−ϖj}Λ_{a+j}(ω)` integrable on `(0, ∞) × Ω`,
`E_a ∫_0^∞ ϖe^{−ϖj} Λ_{a+j} dj = cfgValue r i ϖ τ · Λ_a` a.s.
Generalises `TidyR7GuidanceItoValuation.condExp_debtValue` to an announcement at date `a`. -/
theorem condExp_debtValueAt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (ha : 0 ≤ a) (hτ : 0 ≤ τ) {i ϖ : ℝ}
    (hΛ : GuidanceSDFAt P 𝓕 W Λ H K r (fun _ => i) a τ) (hrv : 0 < r + ϖ) (hiv : 0 < i + ϖ)
    (hint : Integrable (fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1) * Λ (a + p.1) p.2)
      ((volume.restrict (Set.Ioi 0)).prod P)) :
    P[fun ω => ∫ j in Set.Ioi (0 : ℝ), ϖ * Real.exp (-ϖ * j) * Λ (a + j) ω | 𝓕 a] =ᵐ[P]
      fun ω => cfgValue r i ϖ τ * Λ a ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨C, hpre⟩ := hΛ.pre
  have h0 : Integrable (Λ a) P := hpre.integ_at a ⟨le_rfl, by linarith⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le a) hint.integral_prod_right
    (fun _ _ _ => (h0.const_mul _).integrableOn) (fun A hA _ => ?_)
    (hpre.adapted.const_mul _).aestronglyMeasurable).symm
  have hA' : MeasurableSet A := 𝓕.le a A hA
  have hswap := integral_integral_swap (integrable_restrict_prod
    (F := fun j ω => ϖ * Real.exp (-ϖ * j) * Λ (a + j) ω) hint A)
  rw [← hswap, integral_const_mul]
  have hpt : ∀ j ∈ Set.Ioi (0 : ℝ), ∫ ω in A, ϖ * Real.exp (-ϖ * j) * Λ (a + j) ω ∂P =
      cfgIntegrand r i ϖ τ j * ∫ ω in A, Λ a ω ∂P := by
    intro j hj
    have hj0 : (0 : ℝ) ≤ j := le_of_lt hj
    have hc := condExp_guidanceAt hB hW h𝓕 ha hτ hΛ hj0
    have hj1 : Integrable (Λ (a + j)) P := by
      rcases le_or_gt j τ with hjT | hjT
      · exact hpre.integ_at (a + j) ⟨by linarith, by linarith⟩
      · obtain ⟨C', hpost⟩ := hΛ.post (a + j) (by linarith)
        exact hpost.integ_at (a + j) ⟨by linarith, le_rfl⟩
    rw [integral_const_mul, ← setIntegral_condExp (𝓕.le a) hj1 hA,
      setIntegral_congr_ae hA' (ae_imp_of_ae_restrict (ae_restrict_of_ae hc)),
      integral_const_mul, cfgIntegrand]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_mul_const,
    integral_cfg hrv hiv hτ]

/-- **Cochrane (2023), Online Appendix §A1.2.1, pp. 559–561 (under uncertainty): the
interchange at date `a` in the book's form**:
`E_a ∫_a^∞ ϖe^{−ϖ(j−a)} Λ_j dj = cfgValue r i ϖ τ · Λ_a` a.s., under the hypotheses of
`condExp_debtValueAt`. -/
theorem condExp_debtValueAt_Ioi (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (ha : 0 ≤ a) (hτ : 0 ≤ τ) {i ϖ : ℝ}
    (hΛ : GuidanceSDFAt P 𝓕 W Λ H K r (fun _ => i) a τ) (hrv : 0 < r + ϖ) (hiv : 0 < i + ϖ)
    (hint : Integrable (fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1) * Λ (a + p.1) p.2)
      ((volume.restrict (Set.Ioi 0)).prod P)) :
    P[fun ω => ∫ j in Set.Ioi a, ϖ * Real.exp (-ϖ * (j - a)) * Λ j ω | 𝓕 a] =ᵐ[P]
      fun ω => cfgValue r i ϖ τ * Λ a ω := by
  have e : (fun ω' => ∫ j in Set.Ioi a, ϖ * Real.exp (-ϖ * (j - a)) * Λ j ω') =
      fun ω' => ∫ j in Set.Ioi (0 : ℝ), ϖ * Real.exp (-ϖ * j) * Λ (a + j) ω' := by
    funext ω'
    rw [← setIntegral_Ioi_shift a]
    simp only [add_sub_cancel_left]
  rw [e]
  exact condExp_debtValueAt hB hW h𝓕 ha hτ hΛ hrv hiv hint

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561 (under uncertainty): the value of the
debt at the announcement date is the book's.** Under the hypotheses of `condExp_debtValueAt`,
a.s. on `Λ_a ≠ 0` the value per unit of debt is `debtValueAt = cfgValue r i ϖ τ`.
Generalises `TidyR7GuidanceItoValuation.debtValue_guidance` to an announcement at date `a`. -/
theorem debtValueAt_guidance (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (ha : 0 ≤ a) (hτ : 0 ≤ τ) {i ϖ : ℝ}
    (hΛ : GuidanceSDFAt P 𝓕 W Λ H K r (fun _ => i) a τ) (hrv : 0 < r + ϖ) (hiv : 0 < i + ϖ)
    (hint : Integrable (fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1) * Λ (a + p.1) p.2)
      ((volume.restrict (Set.Ioi 0)).prod P)) :
    ∀ᵐ ω ∂P, Λ a ω ≠ 0 → debtValueAt P 𝓕 Λ a ϖ ω = cfgValue r i ϖ τ := by
  filter_upwards [condExp_debtValueAt hB hW h𝓕 ha hτ hΛ hrv hiv hint] with ω hω h0
  rw [debtValueAt, hω, mul_div_assoc, div_self h0, mul_one]

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561, under uncertainty: the continuous
forward-guidance formula at an announcement date `a ≥ 0`, verbatim, state by state.** Two
economies with the same debt `B_a` and the same random surpluses `s`: `Λ` with the announcement
(rate `r` on `[a, a + τ]`, `i` after) and `Λ'` without (`r` throughout). If the valuation
equations `B_a/P_a · debtValueAt = E_a ∫ e^{−rj}s_{a+j} dj` hold a.s. where the discount factor
is nonzero, then a.s. where `Λ_a, Λ'_a ≠ 0`, the present value is nonzero and both price levels
are positive, `P_a/P_a' − 1 = e^{−(r+ϖ)τ}((r+ϖ)/(i+ϖ) − 1)` (`ForwardGuidance.cfgJump`).
Generalises `TidyR7GuidanceItoValuation.guidance_jump_ito` to an announcement at date `a`. -/
theorem guidance_jump_at (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (ha : 0 ≤ a) (hτ : 0 ≤ τ) {i ϖ : ℝ} (hϖ : 0 < ϖ)
    (hrv : 0 < r + ϖ) (hiv : 0 < i + ϖ) {Λ' H' K' s : ℝ → Ω → ℝ} {B Pa Pa' : Ω → ℝ}
    (hΛ : GuidanceSDFAt P 𝓕 W Λ H K r (fun _ => i) a τ)
    (hint : Integrable (fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1) * Λ (a + p.1) p.2)
      ((volume.restrict (Set.Ioi 0)).prod P))
    (hΛ' : GuidanceSDFAt P 𝓕 W Λ' H' K' r (fun _ => r) a τ)
    (hint' : Integrable (fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1) * Λ' (a + p.1) p.2)
      ((volume.restrict (Set.Ioi 0)).prod P))
    (hval : ∀ᵐ ω ∂P, Λ a ω ≠ 0 →
      B ω / Pa ω * debtValueAt P 𝓕 Λ a ϖ ω = pvSurplusAt P 𝓕 r a s ω)
    (hval' : ∀ᵐ ω ∂P, Λ' a ω ≠ 0 →
      B ω / Pa' ω * debtValueAt P 𝓕 Λ' a ϖ ω = pvSurplusAt P 𝓕 r a s ω) :
    ∀ᵐ ω ∂P, Λ a ω ≠ 0 → Λ' a ω ≠ 0 → pvSurplusAt P 𝓕 r a s ω ≠ 0 → 0 < Pa ω →
      0 < Pa' ω → Pa ω / Pa' ω - 1 = cfgJump r i ϖ τ := by
  filter_upwards [debtValueAt_guidance hB hW h𝓕 ha hτ hΛ hrv hiv hint,
    debtValueAt_guidance hB hW h𝓕 ha hτ hΛ' hrv hrv hint', hval, hval'] with
    ω e1 e2 v1 v2 h0 h0' hS hp hp'
  have v1 := v1 h0
  have v2 := v2 h0'
  rw [e1 h0] at v1
  rw [e2 h0'] at v2
  exact cfg_jump hrv hiv hϖ hp' hp v2 v1 hS

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561, under uncertainty about the future
rate, at the announcement date `a`: the value of the debt.** The rate is `r` on `[a, a + τ]`
and `ι` from `a + τ` on, `ι` revealed at `a + τ` (finitely many values, `ι + ϖ > 0`). Then
`E_a ∫_0^∞ ϖe^{−ϖj} Λ_{a+j} dj = E_a[e^{rτ} Λ_{a+τ} · cfgValue r ι ϖ τ]` a.s.
Generalises `TidyR7GuidanceItoValuation.condExp_debtValue_random` to an announcement at date `a`. -/
theorem condExp_debtValueAt_random (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (ha : 0 ≤ a) (hτ : 0 ≤ τ) {ϖ : ℝ}
    (hΛ : GuidanceSDFAt P 𝓕 W Λ H K r ι a τ) (hrv : 0 < r + ϖ) (hiv : ∀ ω, 0 < ι ω + ϖ)
    (hint : Integrable (fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1) * Λ (a + p.1) p.2)
      ((volume.restrict (Set.Ioi 0)).prod P)) :
    P[fun ω => ∫ j in Set.Ioi (0 : ℝ), ϖ * Real.exp (-ϖ * j) * Λ (a + j) ω | 𝓕 a] =ᵐ[P]
      P[fun ω => Real.exp (r * τ) * Λ (a + τ) ω * cfgValue r (ι ω) ϖ τ | 𝓕 a] := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨C, hpre⟩ := hΛ.pre
  obtain ⟨C0, hT0⟩ := hΛ.post (a + τ) le_rfl
  obtain ⟨S, hS⟩ := hT0.rate_finite
  set S' : Finset ℝ := S.filter fun x => 0 < x + ϖ with hS'def
  have hS' : ∀ ω, ι ω ∈ S' := fun ω => Finset.mem_filter.2 ⟨hS ω, hiv ω⟩
  have hιm : Measurable ι := (hT0.rate.mono (𝓕.le (a + τ))).measurable
  have hΛT : Integrable (Λ (a + τ)) P := hT0.integ_at (a + τ) ⟨le_rfl, le_rfl⟩
  have hvm : Measurable fun x : ℝ => cfgValue r x ϖ τ := by unfold cfgValue; fun_prop
  set M : ℝ := ∑ x ∈ S, |cfgValue r x ϖ τ| with hM
  have hYint : Integrable
      (fun ω => Real.exp (r * τ) * Λ (a + τ) ω * cfgValue r (ι ω) ϖ τ) P := by
    have h := (hΛT.const_mul (Real.exp (r * τ))).bdd_mul (c := M)
      (hvm.comp hιm).aestronglyMeasurable (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, hM]
        exact Finset.single_le_sum (f := fun x => |cfgValue r x ϖ τ|)
          (fun x _ => abs_nonneg _) (hS ω))
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only [Function.comp_apply]
    ring
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le a) hint.integral_prod_right
    (fun _ _ _ => integrable_condExp.integrableOn) (fun A hA _ => ?_)
    stronglyMeasurable_condExp.aestronglyMeasurable).symm
  have hA' : MeasurableSet A := 𝓕.le a A hA
  have hAT : MeasurableSet[𝓕 (a + τ)] A := 𝓕.mono (by linarith) A hA
  have hBm : ∀ x, MeasurableSet[𝓕 (a + τ)] (A ∩ ι ⁻¹' {x}) := fun x =>
    hAT.inter (hT0.rate.measurable (measurableSet_singleton x))
  have hBι : ∀ x, ∀ ω ∈ A ∩ ι ⁻¹' {x}, ι ω = x := fun x ω hω => Set.mem_singleton_iff.1 hω.2
  have hL : ∫ ω in A, Λ a ω ∂P =
      Real.exp (r * τ) * ∑ x ∈ S', ∫ ω in A ∩ ι ⁻¹' {x}, Λ (a + τ) ω ∂P := by
    have h1 := setIntegral_sdf hB hW h𝓕 ha hpre hA (fun _ _ => rfl) (u := a + τ)
      ⟨by linarith, le_rfl⟩
    have h2 := setIntegral_eq_sum_levels hS' hιm hA' hΛT.integrableOn
    rw [h2] at h1
    rw [h1, ← mul_assoc, ← Real.exp_add]
    have e : r * τ + -r * (a + τ - a) = 0 := by ring
    rw [e, Real.exp_zero, one_mul]
  have hpt : ∀ j ∈ Set.Ioi (0 : ℝ), ∫ ω in A, ϖ * Real.exp (-ϖ * j) * Λ (a + j) ω ∂P =
      ∑ x ∈ S', Real.exp (r * τ) * (∫ ω in A ∩ ι ⁻¹' {x}, Λ (a + τ) ω ∂P)
        * cfgIntegrand r x ϖ τ j := by
    intro j hj
    have hj0 : (0 : ℝ) ≤ j := le_of_lt hj
    rw [integral_const_mul]
    rcases le_or_gt j τ with hjT | hjT
    · have h1 := setIntegral_sdf hB hW h𝓕 ha hpre hA (fun _ _ => rfl) (u := a + j)
        ⟨by linarith, by linarith⟩
      rw [h1, hL, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [cfgIntegrand, min_eq_left hjT, max_eq_right (sub_nonpos.2 hjT)]
      simp only [mul_zero, add_zero]
      ring_nf
    · obtain ⟨Cj, hpj⟩ := hΛ.post (a + j) (by linarith)
      have hΛj : Integrable (Λ (a + j)) P := hpj.integ_at (a + j) ⟨by linarith, le_rfl⟩
      rw [setIntegral_eq_sum_levels hS' hιm hA' hΛj.integrableOn, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [setIntegral_sdf hB hW h𝓕 (by linarith) hpj (hBm x) (hBι x) (u := a + j)
        ⟨by linarith, le_rfl⟩, cfgIntegrand, min_eq_right hjT.le,
        max_eq_left (sub_nonneg.2 hjT.le)]
      have e0 : a + j - (a + τ) = j - τ := by ring
      rw [e0]
      have e : Real.exp (-(r * τ + x * (j - τ))) =
          Real.exp (-(r * τ)) * Real.exp (-x * (j - τ)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [e]
      have e2 : Real.exp (r * τ) * Real.exp (-(r * τ)) = 1 := by
        rw [← Real.exp_add]; simp
      linear_combination (ϖ * Real.exp (-ϖ * j) * Real.exp (-x * (j - τ))
        * ∫ ω in A ∩ ι ⁻¹' {x}, Λ (a + τ) ω ∂P) * e2.symm
  rw [setIntegral_condExp (𝓕.le a) hYint hA,
    ← integral_integral_swap (integrable_restrict_prod
      (F := fun j ω => ϖ * Real.exp (-ϖ * j) * Λ (a + j) ω) hint A),
    setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_finsetSum S' (fun x hx => ((integrableOn_cfgIntegrand τ hrv
      (Finset.mem_filter.1 hx).2).const_mul _)),
    setIntegral_eq_sum_levels hS' hιm hA' hYint.integrableOn]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [integral_const_mul, integral_cfg hrv (Finset.mem_filter.1 hx).2 hτ,
    setIntegral_congr_fun (𝓕.le (a + τ) _ (hBm x))
      (g := fun ω => (Real.exp (r * τ) * cfgValue r x ϖ τ) * Λ (a + τ) ω)
      (fun ω hω => by simp only [hBι x ω hω]; ring), integral_const_mul]
  ring

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561, under uncertainty about the future
rate: the corrected forward-guidance formula at the announcement date `a`.** As in
`guidance_jump_at`, but the rate from `a + τ` on is the news `ι`, revealed at `a + τ`
(finitely many values, `ι + ϖ > 0`). Then a.s. where `Λ_a, Λ'_a ≠ 0`, the present value of
surpluses is nonzero and both price levels are positive,
`P_a/P_a' − 1 = E_a[e^{rτ} Λ_{a+τ} · cfgJump r ι ϖ τ] / Λ_a`: the jump at each realised rate,
averaged with the `(a + τ)`-forward weights `e^{rτ}Λ_{a+τ}/Λ_a` (of `E_a`-mean one).
Generalises `TidyR7GuidanceItoValuation.random_jump_ito` to an announcement at date `a`. -/
theorem random_jump_at (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (ha : 0 ≤ a) (hτ : 0 ≤ τ) {ϖ : ℝ} (hϖ : 0 < ϖ)
    (hrv : 0 < r + ϖ) (hiv : ∀ ω, 0 < ι ω + ϖ) {Λ' H' K' s : ℝ → Ω → ℝ} {B Pa Pa' : Ω → ℝ}
    (hΛ : GuidanceSDFAt P 𝓕 W Λ H K r ι a τ)
    (hint : Integrable (fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1) * Λ (a + p.1) p.2)
      ((volume.restrict (Set.Ioi 0)).prod P))
    (hΛ' : GuidanceSDFAt P 𝓕 W Λ' H' K' r (fun _ => r) a τ)
    (hint' : Integrable (fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1) * Λ' (a + p.1) p.2)
      ((volume.restrict (Set.Ioi 0)).prod P))
    (hval : ∀ᵐ ω ∂P, Λ a ω ≠ 0 →
      B ω / Pa ω * debtValueAt P 𝓕 Λ a ϖ ω = pvSurplusAt P 𝓕 r a s ω)
    (hval' : ∀ᵐ ω ∂P, Λ' a ω ≠ 0 →
      B ω / Pa' ω * debtValueAt P 𝓕 Λ' a ϖ ω = pvSurplusAt P 𝓕 r a s ω) :
    ∀ᵐ ω ∂P, Λ a ω ≠ 0 → Λ' a ω ≠ 0 → pvSurplusAt P 𝓕 r a s ω ≠ 0 → 0 < Pa ω →
      0 < Pa' ω → Pa ω / Pa' ω - 1 =
        P[fun ω => Real.exp (r * τ) * Λ (a + τ) ω * cfgJump r (ι ω) ϖ τ | 𝓕 a] ω / Λ a ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨C, hpre⟩ := hΛ.pre
  obtain ⟨C0, hT0⟩ := hΛ.post (a + τ) le_rfl
  obtain ⟨S, hS⟩ := hT0.rate_finite
  have hιm : Measurable ι := (hT0.rate.mono (𝓕.le (a + τ))).measurable
  have hΛT : Integrable (Λ (a + τ)) P := hT0.integ_at (a + τ) ⟨le_rfl, le_rfl⟩
  have hjm : Measurable fun x : ℝ => cfgJump r x ϖ τ := by unfold cfgJump; fun_prop
  set M : ℝ := ∑ x ∈ S, |cfgJump r x ϖ τ| with hM
  have hZint : Integrable
      (fun ω => Real.exp (r * τ) * Λ (a + τ) ω * cfgJump r (ι ω) ϖ τ) P := by
    have h := (hΛT.const_mul (Real.exp (r * τ))).bdd_mul (c := M)
      (hjm.comp hιm).aestronglyMeasurable (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, hM]
        exact Finset.single_le_sum (f := fun x => |cfgJump r x ϖ τ|)
          (fun x _ => abs_nonneg _) (hS ω))
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only [Function.comp_apply]
    ring
  have hΛTe : Integrable (fun ω => Real.exp (r * τ) * Λ (a + τ) ω) P := hΛT.const_mul _
  set k : ℝ := (r + ϖ) / ϖ with hk
  have hpt : (k • fun ω => Real.exp (r * τ) * Λ (a + τ) ω * cfgValue r (ι ω) ϖ τ) =
      (fun ω => Real.exp (r * τ) * Λ (a + τ) ω * cfgJump r (ι ω) ϖ τ)
        + fun ω => Real.exp (r * τ) * Λ (a + τ) ω := by
    funext ω
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    have e := cfgJump_add_one (r := r) (x := ι ω) τ hϖ.ne' hrv.ne' (hiv ω).ne'
    rw [hk]
    linear_combination (-(Real.exp (r * τ) * Λ (a + τ) ω)) * e
  have hlin1 := condExp_smul (μ := P) k
    (fun ω => Real.exp (r * τ) * Λ (a + τ) ω * cfgValue r (ι ω) ϖ τ) (𝓕 a)
  have hlin2 := condExp_add (m := 𝓕 a) hZint hΛTe
  have hlin3 := condExp_smul (μ := P) (Real.exp (r * τ)) (Λ (a + τ)) (𝓕 a)
  have hpreT := condExp_sdf_const hB hW h𝓕 ha hpre (u := a + τ) ⟨by linarith, le_rfl⟩
  have hV := condExp_debtValueAt_random hB hW h𝓕 ha hτ hΛ hrv hiv hint
  filter_upwards [hV, debtValueAt_guidance hB hW h𝓕 ha hτ hΛ' hrv hrv hint', hval, hval',
    hlin1, hlin2, hlin3, hpreT] with ω e1 e2 v1 v2 l1 l2 l3 l4 h0 h0' hS0 hp hp'
  have v1 := v1 h0
  have v2 := v2 h0'
  rw [e2 h0', cfgValue_same r ϖ τ hrv] at v2
  rw [debtValueAt, e1] at v1
  rw [hpt] at l1
  have l3' : P[fun ω => Real.exp (r * τ) * Λ (a + τ) ω | 𝓕 a] ω = Real.exp (r * τ) *
      (Real.exp (-r * (a + τ - a)) * Λ a ω) := by
    have e : (fun ω => Real.exp (r * τ) * Λ (a + τ) ω) = Real.exp (r * τ) • Λ (a + τ) := by
      funext ω; simp [smul_eq_mul]
    rw [e, l3, Pi.smul_apply, l4, smul_eq_mul]
  have l3'' : P[fun ω => Real.exp (r * τ) * Λ (a + τ) ω | 𝓕 a] ω = Λ a ω := by
    rw [l3', ← mul_assoc, ← Real.exp_add]
    have e : r * τ + -r * (a + τ - a) = 0 := by ring
    rw [e, Real.exp_zero, one_mul]
  rw [l2, Pi.add_apply, l3''] at l1
  rw [Pi.smul_apply, smul_eq_mul] at l1
  set Y := P[fun ω => Real.exp (r * τ) * Λ (a + τ) ω * cfgValue r (ι ω) ϖ τ | 𝓕 a] ω with hY
  set Z := P[fun ω => Real.exp (r * τ) * Λ (a + τ) ω * cfgJump r (ι ω) ϖ τ | 𝓕 a] ω with hZ
  have hB0 : B ω ≠ 0 := by
    intro hb
    rw [hb, zero_div, zero_mul] at v2
    exact hS0 v2.symm
  have hP := hp.ne'
  have hP' := hp'.ne'
  have hrv' := hrv.ne'
  have hϖ' := hϖ.ne'
  rw [hk] at l1
  have heq : B ω * Y * (Pa' ω * (r + ϖ)) = B ω * ϖ * (Pa ω * Λ a ω) := by
    have h := v1.trans v2.symm
    rw [div_mul_div_comm, div_mul_div_comm,
      div_eq_div_iff (mul_ne_zero hP h0) (mul_ne_zero hP' hrv')] at h
    linear_combination h
  have heq2 : Y * (Pa' ω * (r + ϖ)) = ϖ * (Pa ω * Λ a ω) :=
    mul_left_cancel₀ hB0 (by linear_combination heq)
  have l1' : (r + ϖ) * Y = (Z + Λ a ω) * ϖ := by
    rw [div_mul_eq_mul_div, eq_div_iff hϖ'] at l1
    exact l1.symm
  rw [div_sub_one hP', div_eq_div_iff hP' h0]
  apply mul_left_cancel₀ hϖ'
  linear_combination (-1) * heq2 + Pa' ω * l1'

end Cochrane.LongTermDebtDynamics.TidyR8GuidanceDateT
