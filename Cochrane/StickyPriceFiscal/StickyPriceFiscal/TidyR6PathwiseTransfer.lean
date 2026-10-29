/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.TidyR6MeasResponses
import StickyPriceFiscal.TidyR6MeasLTDResponse
import StickyPriceFiscal.TidyR6MeasTable51

/-!
# Pathwise and expectation-free results in the probability model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.4, eqs. (5.22)–(5.28),
pp. 134–137 (moving averages and their coefficients), §5.1, eq. (5.6) (the roots) and the
comparative statics of §§5.1.2–5.3.

Many core results involve no expectation at all: the moving-average algebra of
`SurplusProcess` (`SurplusProcess.ma_representation`, `SurplusProcess.vstar_display`,
`SurplusProcess.s_ma_525`, `SurplusProcess.aCoef_526`), the coefficient facts
(`SurplusProcess.hasSum_aCoef`, `SurplusProcess.s_shape`), the roots of (5.6) and their
comparative statics (`NKModel.lam1_strictMonoOn`, `FiscalNK.perm_rise_pi0_strictAnti`,
`LongTermDebt.ltd_strictAnti_om`, `LongTermDebt.ltd_pi0_strictAnti_kappa`). They are stated for
an arbitrary type `Ω` (or for real numbers) and therefore hold verbatim for processes on a
probability space. The general transfer device for core statements that formally take an
`ExpectationSystem` only to express pathwise facts is `idSystem`: the identity is an
`ExpectationSystem` on **every** type (`idSystem_adapted`, `idSystem_pullOut`).

## Main results

* `idSystem`, `idSystem_adapted`, `idSystem_pullOut`, `idSystem_E`: the transfer device.
* `mma_representation`, `mvstar_display`, `ms_ma_525`: the moving-average representations
  (5.25)–(5.26) for processes on the probability space (the core theorems applied).
* **`minnov_ma`** (the innovation of a moving average of mean-zero shocks:
  `ΔE_{t+1} ma(c, ε)_{t+1+j} = c_j ε_{t+1}` a.e.) and **`msurplus_news`**: in the probability
  model the surplus news is `ΔE_{t+1} s̃_{t+1+j} = a_j ε_{t+1}` a.e.; with
  `SurplusProcess.s_shape` this is the s-shaped response (`msurplus_news_s_shape`) and with
  `SurplusProcess.hasSum_aCoef` its discounted sum is `β_s` (`msurplus_news_pv`).
* Comparative statics of the probability-model responses: `fig51_impact_strictAnti`
  (the impact revision per unit rate shock with one-period debt, `ρ/λ₁`, falls with `κ`),
  `fig54_impact_strictAnti_om` and `fig54_impact_strictAnti_kappa` (with long-term debt the
  impact revision per unit shock falls with maturity and with `κ`).
-/

namespace Cochrane.StickyPriceFiscal.TidyR6PathwiseTransfer

open MeasureTheory Filter Topology ExpectationsMeasure PolicyRulesMeasure SurplusProcess
  NKModel FiscalNK LongTermDebt

/-- Cochrane (2023), Ch. 2, p. 29 (tool, the transfer device): the identity is an expectation
system on every type — perfect foresight on an arbitrary state space. -/
def idSystem (Ω : Type*) : ExpectationSystem Ω where
  E := fun _ => LinearMap.id
  const := fun _ _ => rfl
  mono := fun _ _ _ h => h
  tower := fun _ _ => rfl
  known := fun _ _ => rfl

/-- Cochrane (2023), Ch. 2, p. 29 (tool): under `idSystem` every forecast is the variable. -/
theorem idSystem_E {Ω : Type*} (t : ℕ) (x : Ω → ℝ) : (idSystem Ω).E t x = x := rfl

/-- Cochrane (2023), Ch. 2, p. 29 (tool): under `idSystem` every process is adapted. -/
theorem idSystem_adapted {Ω : Type*} (x : ℕ → Ω → ℝ) : (idSystem Ω).Adapted x := fun _ => rfl

/-- Cochrane (2023), Ch. 2, p. 29 (tool): `idSystem` has the pull-out property. -/
theorem idSystem_pullOut {Ω : Type*} : (idSystem Ω).PullOut := fun _ _ _ _ => rfl

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-! ### The moving averages of §5.4 on the probability space -/

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), (5.25), p. 135, for processes on a probability space: with zero
pre-sample states, `u = ma(ηᵏ, ε)`, `v* = ma(vCoef, ε)` and `s̃_{t+1} = ma(aCoef, ε)_{t+1}`
(pathwise; `SurplusProcess.ma_representation` applied). -/
theorem mma_representation {ρ α βs η : ℝ} (hρ : ρ ≠ 0) {ε s vs u : ℕ → Ω → ℝ}
    (h : IsSurplusProc ρ α βs η ε s vs u) (hv0 : vs 0 = 0) (hu0 : u 0 = 0) (t : ℕ) :
    u t = ma (fun k => η ^ k) ε t ∧ vs t = ma (vCoef ρ α βs η) ε t ∧
      s (t + 1) = ma (aCoef ρ α βs η) ε (t + 1) :=
  ma_representation hρ h hv0 hu0 t

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 135 (first display), for processes on a probability space
(`SurplusProcess.vstar_display` applied). -/
theorem mvstar_display {ρ α βs η : ℝ} (hρ : ρ ≠ 0) {ε s vs u : ℕ → Ω → ℝ}
    (h : IsSurplusProc ρ α βs η ε s vs u) (hv0 : vs 0 = 0) (t : ℕ) :
    vs t = ma (fun k => ρ⁻¹ * gRoot ρ α ^ k) (fun r => βs • ε r - u r) t :=
  vstar_display hρ h hv0 t

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), eq. (5.25), p. 135, for processes on a probability space
(`SurplusProcess.s_ma_525` applied). -/
theorem ms_ma_525 {ρ α βs η : ℝ} (hρ : ρ ≠ 0) {ε s vs u : ℕ → Ω → ℝ}
    (h : IsSurplusProc ρ α βs η ε s vs u) (hv0 : vs 0 = 0) (t : ℕ) :
    s (t + 1) = ma (dCoef ρ α) u (t + 1) + ma (eCoef ρ α βs) ε (t + 1) :=
  s_ma_525 hρ h hv0 t

/-- Cochrane (2023), p. 135 (`SurplusProcess.innov_ma`), **in a probability model**: for adapted
integrable mean-zero shocks, `ΔE_{t+1} ma(c, ε)_{t+1+j} = c_j ε_{t+1}` a.e. -/
theorem minnov_ma {ε : ℕ → Ω → ℝ} (hεa : StronglyAdapted S.𝓕 ε)
    (hεi : ∀ t, Integrable (ε t) S.μ) (hε : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0) (c : ℕ → ℝ)
    (t j : ℕ) :
    S.innov t (ma c ε (t + 1 + j)) =ᵐ[S.μ] c j • ε (t + 1) := by
  -- the innovation of each shock
  have hfut : ∀ r m, r < m → S.E r (ε m) =ᵐ[S.μ] 0 := by
    intro r m hrm
    obtain ⟨d, rfl⟩ : ∃ d, m = r + d + 1 := ⟨m - r - 1, by omega⟩
    filter_upwards [(S.E_tower (Nat.le_add_right r d) (ε (r + d + 1))).symm,
      S.E_congr (hε (r + d)) r] with ω e1 e2
    rw [e1, e2, S.E_zero]
  have hk : ∀ m, S.innov t (ε m) =ᵐ[S.μ] if m = t + 1 then ε (t + 1) else 0 := by
    intro m
    rcases lt_trichotomy m (t + 1) with hm | hm | hm
    · have hm' : m ≤ t := by omega
      rw [TidyR6MeasTable51.minnov_known S ((hεa m).mono (S.𝓕.mono hm')) (hεi m)]
      simp [show m ≠ t + 1 by omega]
    · subst hm
      filter_upwards [hε t] with ω e
      simp only [MeasExpectationSystem.innov, Pi.sub_apply, ↓reduceIte,
        S.E_of_stronglyMeasurable (hεa (t + 1)) (hεi (t + 1)), e, Pi.zero_apply, sub_zero]
    · filter_upwards [hfut (t + 1) m hm, hfut t m (by omega)] with ω e1 e2
      simp only [MeasExpectationSystem.innov, Pi.sub_apply, e1, e2, sub_self,
        show m ≠ t + 1 by omega, ↓reduceIte, Pi.zero_apply]
  set n := t + 1 + j
  have hint : ∀ k ∈ Finset.range n, Integrable (c k • ε (n - k)) S.μ := fun k _ =>
    (hεi _).smul _
  have hs1 := condExp_finsetSum hint (S.𝓕 (t + 1)) (μ := S.μ)
  have hs0 := condExp_finsetSum hint (S.𝓕 t) (μ := S.μ)
  have hsm : ∀ k, S.innov t (c k • ε (n - k)) =ᵐ[S.μ] c k • S.innov t (ε (n - k)) := fun k =>
    TidyR6MeasTable51.minnov_smul S (c k) (ε (n - k)) t
  filter_upwards [hs1, hs0, ae_all_iff.2 hsm, ae_all_iff.2 fun k => hk (n - k)] with ω e1 e2 e3 e4
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, ma] at e3 ⊢
  have e1' : S.E (t + 1) (∑ k ∈ Finset.range n, c k • ε (n - k)) ω =
      (∑ k ∈ Finset.range n, S.E (t + 1) (c k • ε (n - k))) ω := e1
  have e2' : S.E t (∑ k ∈ Finset.range n, c k • ε (n - k)) ω =
      (∑ k ∈ Finset.range n, S.E t (c k • ε (n - k))) ω := e2
  rw [e1', e2', Finset.sum_apply, Finset.sum_apply, ← Finset.sum_sub_distrib]
  have hterm : ∀ k, S.E (t + 1) (c k • ε (n - k)) ω - S.E t (c k • ε (n - k)) ω =
      c k * (if n - k = t + 1 then ε (t + 1) ω else 0) := by
    intro k
    rw [e3 k, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    have := e4 k
    simp only [MeasExpectationSystem.innov, Pi.sub_apply] at this
    rw [this]
    split_ifs <;> rfl
  simp only [hterm]
  rw [Finset.sum_eq_single j]
  · simp only [show n - j = t + 1 by omega, ↓reduceIte, Pi.smul_apply, smul_eq_mul]
  · intro k _ hkj
    simp [show n - k ≠ t + 1 by omega]
  · intro hj
    exact absurd (Finset.mem_range.2 (by omega)) hj

/-- Cochrane (2023), (5.25)–(5.26), p. 135, **the surplus news in a probability model**: with zero
pre-sample states and mean-zero integrable adapted shocks, `ΔE_{t+1} s̃_{t+1+j} = a_j ε_{t+1}`
a.e. -/
theorem msurplus_news {ρ α βs η : ℝ} (hρ : ρ ≠ 0) {ε s vs u : ℕ → Ω → ℝ}
    (h : IsSurplusProc ρ α βs η ε s vs u) (hv0 : vs 0 = 0) (hu0 : u 0 = 0)
    (hεa : StronglyAdapted S.𝓕 ε) (hεi : ∀ t, Integrable (ε t) S.μ)
    (hε : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0) (t j : ℕ) :
    S.innov t (s (t + 1 + j)) =ᵐ[S.μ] aCoef ρ α βs η j • ε (t + 1) := by
  have e := (mma_representation hρ h hv0 hu0 (t + j)).2.2
  rw [show t + j + 1 = t + 1 + j by ring] at e
  rw [e]
  exact minnov_ma S hεa hεi hε _ t j

/-- Cochrane (2023), p. 135 ("a pretty s-shaped response"), **in a probability model**: under the
hypotheses of `SurplusProcess.s_shape` there is `K ≥ 1` such that the surplus news
`ΔE_{t+1} s̃_{t+1+j}` is a positive multiple of `ε_{t+1}` for `j < K` and a negative one for
`j > K` (a.e.). -/
theorem msurplus_news_s_shape {ρ α βs η : ℝ} (hρ : 0 < ρ) (hα0 : 0 < α) (hα1 : α < 1)
    (hη0 : 0 ≤ η) (hηg : η < gRoot ρ α)
    (hβ : βs < -((gRoot ρ α - ρ⁻¹) / (gRoot ρ α - η)) * ρ * gRoot ρ α / α)
    {ε s vs u : ℕ → Ω → ℝ} (h : IsSurplusProc ρ α βs η ε s vs u) (hv0 : vs 0 = 0)
    (hu0 : u 0 = 0) (hεa : StronglyAdapted S.𝓕 ε) (hεi : ∀ t, Integrable (ε t) S.μ)
    (hε : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0) :
    ∃ K, 1 ≤ K ∧ (∀ j < K, 0 < aCoef ρ α βs η j) ∧ (∀ j, K < j → aCoef ρ α βs η j < 0) ∧
      ∀ t j, S.innov t (s (t + 1 + j)) =ᵐ[S.μ] aCoef ρ α βs η j • ε (t + 1) := by
  obtain ⟨K, hK1, hpos, -, hneg⟩ := s_shape hρ hα0 hα1 hη0 hηg hβ
  exact ⟨K, hK1, hpos, hneg, fun t j =>
    msurplus_news S hρ.ne' h hv0 hu0 hεa hεi hε t j⟩

/-- Cochrane (2023), eq. (5.28), p. 135, **in a probability model**: the coefficients of the
surplus news have discounted sum `∑ ρʲ a_j = β_s` (`0 < α < 2`, `|ρη| < 1`), so the present value
of the news is `β_s ε_{t+1}`. -/
theorem msurplus_news_pv {ρ α βs η : ℝ} (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1)
    {ε s vs u : ℕ → Ω → ℝ} (h : IsSurplusProc ρ α βs η ε s vs u) (hv0 : vs 0 = 0)
    (hu0 : u 0 = 0) (hεa : StronglyAdapted S.𝓕 ε) (hεi : ∀ t, Integrable (ε t) S.μ)
    (hε : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * S.innov t (s (t + 1 + j)) ω) (βs * ε (t + 1) ω) := by
  filter_upwards [ae_all_iff.2 fun j => msurplus_news S hρ h hv0 hu0 hεa hεi hε t j] with ω e
  have := (hasSum_aCoef (βs := βs) hρ hα hη).mul_right (ε (t + 1) ω)
  convert this using 1
  funext j
  rw [e j, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### Comparative statics of the probability-model responses -/

/-- Cochrane (2023), §5.1.2, p. 122 ("stickier prices, larger impact"), **in a probability
model**: in `TidyR6MeasResponses.fig51_impact` the impact revision is `ε · m(κ)` with
`m(κ) = ρ/λ₁(κ)` strictly decreasing in `κ > 0` (`FiscalNK.perm_rise_pi0_strictAnti`). -/
theorem fig51_impact_strictAnti {σ β ρ B κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {ε : Ω → ℝ} (hεm : StronglyMeasurable[S.𝓕 1] ε)
    (hεb : ∀ᵐ ω ∂S.μ, |ε ω| ≤ B) (hε0 : S.E 0 ε =ᵐ[S.μ] 0) {x p v : ℕ → Ω → ℝ}
    (h : TidyR6MeasFiscalNK.MFTPLNK S σ β κ ρ (fun t => if t = 0 then 0 else ε) 0 0 x p v)
    (hvb : S.BddProc v) :
    (∀ᵐ ω ∂S.μ, S.E 1 (p 1) ω - S.E 0 (p 1) ω = ε ω * (fun k => ρ * (lam1 σ β k)⁻¹) κ) ∧
      StrictAntiOn (fun k => ρ * (lam1 σ β k)⁻¹) (Set.Ioi 0) := by
  refine ⟨?_, perm_rise_pi0_strictAnti hσ hβ hρ0⟩
  filter_upwards [TidyR6MeasResponses.fig51_impact S hσ hκ hβ hρ0 hρ1 hεm hεb hε0 h hvb]
    with ω e
  exact e.1

/-- Cochrane (2023), p. 129 ("a longer maturity structure produces a larger … disinflation"),
**in a probability model**: in `TidyR6MeasLTDResponse.fig54_disinflation` the impact revision is
`ε · m(ω̃)` with `m(ω̃) = 1 − (1 − ρ/λ₁)/(1 − ω̃)` strictly decreasing in `ω̃ < 1`
(`LongTermDebt.ltd_strictAnti_om`). -/
theorem fig54_impact_strictAnti_om {σ β κ ρ om B : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hom0 : 0 ≤ om) (hom1 : om < 1) {ε : Ω → ℝ}
    (hεm : StronglyMeasurable[S.𝓕 1] ε) (hεb : ∀ᵐ ω ∂S.μ, |ε ω| ≤ B)
    (hε0 : S.E 0 ε =ᵐ[S.μ] 0) {x p v q rn : ℕ → Ω → ℝ}
    (h : TidyR6MeasFiscalNK.MLTD S σ β κ ρ om (fun t => if t = 0 then 0 else ε) 0 0 0 x p v q rn)
    (hvb : S.BddProc v) :
    (∀ᵐ ω ∂S.μ, S.E 1 (p 1) ω - S.E 0 (p 1) ω =
        ε ω * (fun o => 1 - (1 - ρ * (lam1 σ β κ)⁻¹) / (1 - o) * (lam1 σ β κ)⁻¹ ^ 0) om) ∧
      StrictAntiOn (fun o => 1 - (1 - ρ * (lam1 σ β κ)⁻¹) / (1 - o) * (lam1 σ β κ)⁻¹ ^ 0)
        (Set.Iio 1) := by
  refine ⟨?_, ltd_strictAnti_om hσ hκ hβ hρ1 0⟩
  filter_upwards [TidyR6MeasLTDResponse.fig54_disinflation S hσ hκ hβ hρ0 hρ1 hom0 hom1 hεm
    hεb hε0 h hvb] with ω e
  rw [e.1]
  simp

/-- Cochrane (2023), p. 129 ("flexible prices, larger decline"), **in a probability model**: in
`TidyR6MeasLTDResponse.fig54_disinflation` the impact revision per unit shock
`1 − (1 − ρ/λ₁(κ))/(1 − ω̃)` is strictly decreasing in `κ > 0`
(`LongTermDebt.ltd_pi0_strictAnti_kappa`). -/
theorem fig54_impact_strictAnti_kappa {σ β κ ρ om B : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hom0 : 0 ≤ om) (hom1 : om < 1) {ε : Ω → ℝ}
    (hεm : StronglyMeasurable[S.𝓕 1] ε) (hεb : ∀ᵐ ω ∂S.μ, |ε ω| ≤ B)
    (hε0 : S.E 0 ε =ᵐ[S.μ] 0) {x p v q rn : ℕ → Ω → ℝ}
    (h : TidyR6MeasFiscalNK.MLTD S σ β κ ρ om (fun t => if t = 0 then 0 else ε) 0 0 0 x p v q rn)
    (hvb : S.BddProc v) :
    (∀ᵐ ω ∂S.μ, S.E 1 (p 1) ω - S.E 0 (p 1) ω =
        ε ω * (fun k => 1 - (1 - ρ * (lam1 σ β k)⁻¹) / (1 - om)) κ) ∧
      StrictAntiOn (fun k => 1 - (1 - ρ * (lam1 σ β k)⁻¹) / (1 - om)) (Set.Ioi 0) := by
  refine ⟨?_, ltd_pi0_strictAnti_kappa hσ hβ hρ0 hom1⟩
  filter_upwards [TidyR6MeasLTDResponse.fig54_disinflation S hσ hκ hβ hρ0 hρ1 hom0 hom1 hεm
    hεb hε0 h hvb] with ω e
  exact e.1

end Cochrane.StickyPriceFiscal.TidyR6PathwiseTransfer
