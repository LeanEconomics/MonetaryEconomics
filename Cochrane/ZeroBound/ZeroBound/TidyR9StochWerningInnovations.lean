/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR9StochWerningMRepVersion
import ZeroBound.TidyR8StochWerningMartingale

/-!
# Which innovation processes occur: `π = wPi + e^{−λ^b t}(M_0 + ∫_0^t H dW)`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.2, pp. 474–476: for
the same interest-rate path there remain "multiple forward-stable equilibrium inflation paths,
indexed by the free constant `C`" (p. 475, Figure 20.4), and the fiscal theorist picks one "by
the fiscal innovation at time `t = 0`" (p. 476). Under uncertainty, TidyR8StochWerningMartingale
showed that the equilibria of the trap experiment are exactly
`π_t = wPi(0)_t + e^{−λ^b t}M_t`, `κx_t = κwX(0)_t + λ^f e^{−λ^b t}M_t`, with `M` a continuous
adapted martingale and `e^{−λ^b t}M_t` bounded in `L¹`. Here, on the Brownian filtration, the
martingales are written as stochastic integrals (the martingale representation theorem of
`TidyR13MRepTheorem`), so the set of equilibria is indexed by a constant AND an innovation
loading process: the book's free constant `C` becomes the pair `(M_0, H)`.

The filtration. The every-path continuity required of equilibria (`TidyR7StochWerning.Regular`)
and adaptedness can only be had together for the completed filtration
`𝓖 = TidyR10DoobAugment.augment P 𝓕` of the natural filtration `𝓕 = bmFiltrationReal W`
(a continuous version of `∫ H dW` is continuous only outside a null set, which is not in `𝓕_t`).
Conditional expectations for `𝓖` and `𝓕` agree a.s. (`TidyR10DoobAugment.condExp_augment`), and
every equilibrium for `𝓕` is one for `𝓖` (`swinnov_isStochEqm_augment`,
`swinnov_regular_augment`). The integrand class is always that of `𝓕`.

## Main results

* **`swinnov_eqm_rep`** (which innovations occur): every regular `L¹`-bounded equilibrium for
  `𝓖` with `π_t ∈ L²` for every `t ≥ 0` is
  `π_t = wPi(0)_t + e^{−λ^b t}(c + ∫_0^t H dW)`, `x_t = wX(0)_t + (λ^f/κ)e^{−λ^b t}(c + ∫_0^t H dW)`
  a.s. for every `t ≥ 0`, with `c = E[π_0] − wPi(0)_0` and ONE `H` in the extended class on every
  `[0, T]` (all horizons at once); `swinnov_eqm_rep_unique`: `c` and `H` (`dt × dP`-a.e. on every
  `[0, T]`) are unique; `swinnov_eqm_rep_natural`: the same for equilibria of `𝓕` itself.
* **`swinnov_eqm_of_integrand`** (which innovations are allowed): conversely, for every constant
  `c` and every `H` in the class on every `[0, T]` with `E∫_0^t H² ≤ K e^{2λ^b t}` for `t ≥ 0`,
  there is a process `M` with every path continuous, `M_t = c + ∫_0^t H dW` a.s. for `t ≥ 0`, such
  that `wPi(0) + e^{−λ^b t}M`, `wX(0) + (λ^f/κ)e^{−λ^b t}M` is a regular equilibrium for `𝓖`,
  bounded in mean square. The growth condition holds for every bounded `H`
  (`swinnov_growth_of_bdd`).
* **`swinnov_eqm_rep_bddL2`** (exact description of the mean-square bounded equilibria): for
  them the growth condition is also necessary (`swinnov_growth_of_rep`), so they are exactly the
  pairs `(c, H)` with `E∫_0^t H² ≤ K e^{2λ^b t}`.
* **`swinnov_loading_continuous`** (non-`C¹` loadings): for every continuous deterministic
  loading `b` with `|b| ≤ B` the innovation `dπ_t = b(t)dW_t`
  (`M_t = ∫_0^t e^{λ^b u}b(u)dW_u`) gives a regular mean-square bounded equilibrium for `𝓖`.
  Generalises
  `TidyR8StochWerningMartingale.isStochEqm_loading` (`C¹` loadings, natural filtration).
* Non-vacuity on `TidyR7BrownianExist.bmPath`: `bmPath_swinnov_rep` (the constant-loading
  equilibrium has its representation), `bmPath_swinnov_window` (news arriving only between dates
  `1` and `2`, `H = 1_{(1,2]}`, an integrand that is not mean-square continuous),
  `bmPath_swinnov_abs_sin` (the continuous, not differentiable, loading `|sin t|`;
  `not_differentiableAt_abs_sin`).

What is not covered: martingales `M` with `M_t ∈ L¹` only (not `L²`). The representation
result used here is for square-integrable martingales; an `L¹` martingale of the Brownian filtration
is `M_0 + ∫ H dW` only with `∫_0^t H² < ∞` a.s. (a local-martingale integral), which is not
available here. Every `L²`-bounded equilibrium (e.g. all those built in TidyR7StochWerningExist
and TidyR8StochWerningMartingale) has `π_t ∈ L²`.
-/

namespace Cochrane.ZeroBound.TidyR9StochWerningInnovations

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.ContinuousTimeNK Cochrane.ZeroBound.WerningModel
open Cochrane.ZeroBound.TidyR7StochWerning Cochrane.ZeroBound.TidyR7StochWerningTrap
open Cochrane.ZeroBound.TidyR7StochWerningExist Cochrane.ZeroBound.TidyR7StochWerningNaturalExist
open Cochrane.ZeroBound.TidyR8StochWerningNaturalMean
  Cochrane.ZeroBound.TidyR8StochWerningMartingale
open Cochrane.ZeroBound.TidyR7BrownianTools Cochrane.ZeroBound.TidyR7BrownianQV
  Cochrane.ZeroBound.TidyR7ItoIntegral Cochrane.ZeroBound.TidyR7ItoUnbounded
  Cochrane.ZeroBound.TidyR10DoobAugment Cochrane.ZeroBound.TidyR13MRepIntegral
  Cochrane.ZeroBound.TidyR13MRepCutoff Cochrane.ZeroBound.TidyR13MRepTheorem
  Cochrane.ZeroBound.TidyR13MRepMonetarism Cochrane.ZeroBound.TidyR9StochWerningMRepVersion
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

/-! ## The completed filtration -/

/-- Cochrane (2023), (20.5)–(20.6), p. 474 (tool): `E_t dZ = D dt` for a filtration implies it
for the completed filtration (conditional expectations agree a.s.). -/
theorem swinnov_expDrift_augment [IsFiniteMeasure P] {𝓕 : Filtration ℝ mΩ}
    {Z D : ℝ → Ω → ℝ} (h : ExpDrift P 𝓕 Z D) : ExpDrift P (augment P 𝓕) Z D := by
  intro s t hs hst
  exact ⟨(h s t hs hst).1, (condExp_augment (P := P) (𝓕 := 𝓕) _ s).trans (h s t hs hst).2⟩

/-- Cochrane (2023), (20.5)–(20.6), p. 474: **every equilibrium for `𝓕` is an equilibrium for
the completed filtration.** -/
theorem swinnov_isStochEqm_augment [IsFiniteMeasure P] {σ ρ κ : ℝ} {𝓕 : Filtration ℝ mΩ}
    {i u g : ℝ → ℝ} {ν x π : ℝ → Ω → ℝ} (h : IsStochEqm σ ρ κ P 𝓕 i u g ν x π) :
    IsStochEqm σ ρ κ P (augment P 𝓕) i u g ν x π :=
  ⟨swinnov_expDrift_augment h.1, swinnov_expDrift_augment h.2⟩

/-- Cochrane (2023), §20.2.2, p. 474: a regular process for `𝓕` is regular for the completed
filtration. -/
theorem swinnov_regular_augment {𝓕 : Filtration ℝ mΩ} {Z : ℝ → Ω → ℝ} (h : Regular 𝓕 Z) :
    Regular (augment P 𝓕) Z :=
  ⟨h.1, fun t => (h.2 t).mono (le_augment t)⟩

/-- Cochrane (2023), §20.2.2, p. 475 (tool): **a martingale of the completed filtration is a.s.
a martingale of `𝓕`.** If `M` is adapted to `augment P 𝓕` with `E[M_t | 𝓖_s] = M_s` for
`0 ≤ s ≤ t` and `M_t` integrable, then `M'_t = E[M_t | 𝓕_t]` is `𝓕`-adapted, `M_t = M'_t` a.s.,
and `E[M'_t | 𝓕_s] = M'_s` for `0 ≤ s ≤ t`. -/
theorem swinnov_martingale_of_augment [IsFiniteMeasure P] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} (hMm : ∀ t, StronglyMeasurable[augment P 𝓕 t] (M t))
    (hMi : ∀ t, 0 ≤ t → Integrable (M t) P)
    (hmart : ∀ s t, 0 ≤ s → s ≤ t → P[M t | augment P 𝓕 s] =ᵐ[P] M s) :
    (∀ t, StronglyMeasurable[𝓕 t] (P[M t | 𝓕 t])) ∧
      (∀ t, 0 ≤ t → M t =ᵐ[P] P[M t | 𝓕 t]) ∧
      ∀ s t, 0 ≤ s → s ≤ t → P[P[M t | 𝓕 t] | 𝓕 s] =ᵐ[P] P[M s | 𝓕 s] := by
  have hMM : ∀ t, 0 ≤ t → M t =ᵐ[P] P[M t | 𝓕 t] := fun t ht => by
    have e := condExp_of_stronglyMeasurable ((augment P 𝓕).le t) (hMm t) (hMi t ht)
    exact (EventuallyEq.of_eq e.symm).trans (condExp_augment (P := P) (𝓕 := 𝓕) (M t) t)
  refine ⟨fun t => stronglyMeasurable_condExp, hMM, fun s t hs hst => ?_⟩
  exact (condExp_congr_ae (hMM t (hs.trans hst)).symm).trans
    (((condExp_augment (P := P) (𝓕 := 𝓕) (M t) s).symm.trans (hmart s t hs hst)).trans (hMM s hs))

/-! ## Which innovations occur -/

/-- **Cochrane (2023), §20.2.2, pp. 474–476: which innovation processes occur.** Let `W` be
pre-Brownian with measurable values and EVERY path continuous, `𝓕 = bmFiltrationReal W` and
`𝓖 = augment P 𝓕`, `σ, κ > 0`. In every regular `L¹`-bounded stochastic equilibrium `(x, π)` of the
trap experiment for `𝓖` with `π_t ∈ L²` for every `t ≥ 0`,
`π_t = wPi(0)_t + e^{−λ^b t}(c + ∫_0^t H dW)` and
`x_t = wX(0)_t + (λ^f/κ)e^{−λ^b t}(c + ∫_0^t H dW)` a.s. for every `t ≥ 0`, where
`c = E[π_0] − wPi(0)_0` and `H` is ONE integrand in the extended class (for `𝓕`) on every
`[0, T']`. The free constant `C` of p. 475 generalises to `(c, H)`.
Combines `TidyR8StochWerningMartingale.martingale_of_isStochEqm` with
`TidyR9StochWerningMRepVersion.swmrep_martingale_rep`. -/
theorem swinnov_eqm_rep (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    {T u g : ℝ} {x π : ℝ → Ω → ℝ} (hx : Regular (augment P (bmFiltrationReal W hW)) x)
    (hxb : BddL1 P x) (hπ : Regular (augment P (bmFiltrationReal W hW)) π) (hπb : BddL1 P π)
    (h : IsStochEqm σ ρ κ P (augment P (bmFiltrationReal W hW)) (fun _ => 0) (trapStep u T)
      (trapStep g T) (fun _ _ => 0) x π)
    (hπ2 : ∀ t, 0 ≤ t → MemLp (π t) 2 P) :
    ∃ H : ℝ → Ω → ℝ, (∀ T', MRepIntegrand P (bmFiltrationReal W hW) H 0 T') ∧
      (∀ t, 0 ≤ t → π t =ᵐ[P] fun ω => wPi σ κ ρ T u g 0 t + Real.exp (-(lamb ρ κ σ * t)) *
        ((∫ ω, π 0 ω ∂P) - wPi σ κ ρ T u g 0 0
          + mrepInt P (bmFiltrationReal W hW) W H 0 t ω)) ∧
      ∀ t, 0 ≤ t → x t =ᵐ[P] fun ω => wX σ κ ρ T u g 0 t + lamf ρ κ σ / κ *
        (Real.exp (-(lamb ρ κ σ * t)) * ((∫ ω, π 0 ω ∂P) - wPi σ κ ρ T u g 0 0
          + mrepInt P (bmFiltrationReal W hW) W H 0 t ω)) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set 𝓕 := bmFiltrationReal W hW with h𝓕def
  have h𝓕 : BMFiltration P W 𝓕 := bmFiltrationReal_isBM hB hW
  obtain ⟨hMc, hMm, hmart, -, hrepπ, hrepx⟩ := martingale_of_isStochEqm hσ hκ hx hxb hπ hπb h
  set M : ℝ → Ω → ℝ := fun t ω => Real.exp (lamb ρ κ σ * t) * (π t ω - wPi σ κ ρ T u g 0 t)
    with hMdef
  obtain ⟨Kπ, hKπ⟩ := hπb
  have hMi : ∀ t, 0 ≤ t → Integrable (M t) P := fun t ht =>
    ((hKπ t ht).1.sub (integrable_const _)).const_mul _
  have hM2 : ∀ t, 0 ≤ t → MemLp (M t) 2 P := fun t ht =>
    ((hπ2 t ht).sub (memLp_const _)).const_mul _
  obtain ⟨hM'm, hMM', hM'mart⟩ := swinnov_martingale_of_augment hMm hMi hmart
  obtain ⟨H, hH, hrep⟩ := swmrep_martingale_rep hB hW h𝓕 hcont
    (fun T' hT' => mrep_bmFiltrationReal_le hW hT') hM'm hM'mart
    (fun t ht => (hM2 t ht).ae_eq (hMM' t ht))
  have hc : ∫ ω, P[M 0 | 𝓕 0] ω ∂P = (∫ ω, π 0 ω ∂P) - wPi σ κ ρ T u g 0 0 := by
    rw [← integral_congr_ae (hMM' 0 le_rfl)]
    simp only [hMdef, mul_zero, Real.exp_zero, one_mul]
    rw [integral_sub (hKπ 0 le_rfl).1 (integrable_const _), integral_const, smul_eq_mul,
      probReal_univ, one_mul]
  rw [hc] at hrep
  have hMrep : ∀ t, 0 ≤ t → M t =ᵐ[P] fun ω => (∫ ω, π 0 ω ∂P) - wPi σ κ ρ T u g 0 0
      + mrepInt P 𝓕 W H 0 t ω := fun t ht => (hMM' t ht).trans (hrep t ht)
  refine ⟨H, hH, fun t ht => ?_, fun t ht => ?_⟩
  · filter_upwards [hMrep t ht] with ω hω
    rw [hrepπ t ω, hω]
  · filter_upwards [hrepx t ht, hMrep t ht] with ω h1 hω
    rw [h1, hω]

/-- **Cochrane (2023), §20.2.2, pp. 474–476: the pair `(c, H)` is unique.** If
`π_t = wPi(0)_t + e^{−λ^b t}(c + ∫_0^t H dW)` and
`π_t = wPi(0)_t + e^{−λ^b t}(c' + ∫_0^t H' dW)` a.s. for every `t ≥ 0`, with `H, H'` in the
extended class on every `[0, T']`, then `c = c'` and
`H = H'` `dt × dP`-a.e. on `(0, T'] × Ω` for every `T' ≥ 0`. -/
theorem swinnov_eqm_rep_unique (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    {σ ρ κ T u g c c' : ℝ} {π : ℝ → Ω → ℝ} {H H' : ℝ → Ω → ℝ}
    (hH : ∀ T', MRepIntegrand P (bmFiltrationReal W hW) H 0 T')
    (hH' : ∀ T', MRepIntegrand P (bmFiltrationReal W hW) H' 0 T')
    (hrep : ∀ t, 0 ≤ t → π t =ᵐ[P] fun ω => wPi σ κ ρ T u g 0 t + Real.exp (-(lamb ρ κ σ * t)) *
      (c + mrepInt P (bmFiltrationReal W hW) W H 0 t ω))
    (hrep' : ∀ t, 0 ≤ t → π t =ᵐ[P] fun ω => wPi σ κ ρ T u g 0 t + Real.exp (-(lamb ρ κ σ * t)) *
      (c' + mrepInt P (bmFiltrationReal W hW) W H' 0 t ω)) :
    c = c' ∧ ∀ T', 0 ≤ T' →
      Function.uncurry H =ᵐ[mrepMeasure P 0 T'] Function.uncurry H' := by
  set M : ℝ → Ω → ℝ := fun t ω => Real.exp (lamb ρ κ σ * t) * (π t ω - wPi σ κ ρ T u g 0 t)
  have hinv : ∀ t, Real.exp (lamb ρ κ σ * t) * Real.exp (-(lamb ρ κ σ * t)) = 1 := fun t => by
    rw [← Real.exp_add]; simp
  have key : ∀ (d : ℝ) (K : ℝ → Ω → ℝ), (∀ t, 0 ≤ t → π t =ᵐ[P] fun ω => wPi σ κ ρ T u g 0 t +
      Real.exp (-(lamb ρ κ σ * t)) * (d + mrepInt P (bmFiltrationReal W hW) W K 0 t ω)) →
      ∀ t, 0 ≤ t → M t =ᵐ[P] fun ω => d + mrepInt P (bmFiltrationReal W hW) W K 0 t ω := by
    intro d K hK t ht
    filter_upwards [hK t ht] with ω hω
    change Real.exp (lamb ρ κ σ * t) * (π t ω - wPi σ κ ρ T u g 0 t) = _
    rw [hω]
    linear_combination (d + mrepInt P (bmFiltrationReal W hW) W K 0 t ω) * hinv t
  exact swmrep_martingale_rep_unique hB hW (bmFiltrationReal_isBM hB hW) hH hH'
    (key c H hrep) (key c' H' hrep')

/-- **Cochrane (2023), §20.2.2, pp. 474–476: which innovations occur, natural filtration.** The
conclusion of `swinnov_eqm_rep` for regular `L¹`-bounded equilibria of `bmFiltrationReal W`
itself (they are equilibria of the completed filtration). -/
theorem swinnov_eqm_rep_natural (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    {T u g : ℝ} {x π : ℝ → Ω → ℝ} (hx : Regular (bmFiltrationReal W hW) x)
    (hxb : BddL1 P x) (hπ : Regular (bmFiltrationReal W hW) π) (hπb : BddL1 P π)
    (h : IsStochEqm σ ρ κ P (bmFiltrationReal W hW) (fun _ => 0) (trapStep u T)
      (trapStep g T) (fun _ _ => 0) x π)
    (hπ2 : ∀ t, 0 ≤ t → MemLp (π t) 2 P) :
    ∃ H : ℝ → Ω → ℝ, (∀ T', MRepIntegrand P (bmFiltrationReal W hW) H 0 T') ∧
      (∀ t, 0 ≤ t → π t =ᵐ[P] fun ω => wPi σ κ ρ T u g 0 t + Real.exp (-(lamb ρ κ σ * t)) *
        ((∫ ω, π 0 ω ∂P) - wPi σ κ ρ T u g 0 0
          + mrepInt P (bmFiltrationReal W hW) W H 0 t ω)) ∧
      ∀ t, 0 ≤ t → x t =ᵐ[P] fun ω => wX σ κ ρ T u g 0 t + lamf ρ κ σ / κ *
        (Real.exp (-(lamb ρ κ σ * t)) * ((∫ ω, π 0 ω ∂P) - wPi σ κ ρ T u g 0 0
          + mrepInt P (bmFiltrationReal W hW) W H 0 t ω)) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact swinnov_eqm_rep hB hW hcont hσ hκ (swinnov_regular_augment hx) hxb
    (swinnov_regular_augment hπ) hπb (swinnov_isStochEqm_augment h) hπ2

/-! ## Which innovations are allowed -/

/-- Cochrane (2023), §20.2.2, p. 475: the stable-direction innovation `ζ_t = e^{−λt}M_t` of a
martingale `M`. -/
noncomputable def innovZeta (lam : ℝ) (M : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-(lam * t)) * M t ω

/-- **Cochrane (2023), §20.2.2, pp. 474–476: every admissible innovation loading gives an
equilibrium.** Let `W` be pre-Brownian with measurable values and a.s. continuous paths, `𝓕`
admissible, `σ, κ > 0`, `c ∈ ℝ`, and `H` in the extended class on every `[0, T']` with
`E∫_0^t H² ≤ K e^{2λ^b t}` for `t ≥ 0`. There is `M` with EVERY path continuous and
`M_t = c + ∫_0^t H dW` a.s. for every `t ≥ 0` such that, with `ζ = e^{−λ^b t}M`,
`(wX(0) + (λ^f/κ)ζ, wPi(0) + ζ)` is a stochastic equilibrium of the trap experiment for the
completed filtration `augment P 𝓕`, both processes regular for it and bounded in mean square.
Applies `TidyR8StochWerningMartingale.isStochEqm_of_martingale` to
`TidyR9StochWerningMRepVersion.swmrep_exists_continuous_augment`. -/
theorem swinnov_eqm_of_integrand (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    {𝓕 : Filtration ℝ mΩ} (h𝓕 : BMFiltration P W 𝓕)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => W t ω) {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (T u g c : ℝ) {H : ℝ → Ω → ℝ} (hH : ∀ T', MRepIntegrand P 𝓕 H 0 T') {K : ℝ}
    (hK : ∀ t, 0 ≤ t → ∫ x, Function.uncurry H x ^ 2 ∂mrepMeasure P 0 t
      ≤ K * Real.exp (2 * lamb ρ κ σ * t)) :
    ∃ M : ℝ → Ω → ℝ, (∀ t, 0 ≤ t → M t =ᵐ[P] fun ω => c + mrepInt P 𝓕 W H 0 t ω) ∧
      (∀ ω, Continuous fun t => M t ω) ∧
      IsStochEqm σ ρ κ P (augment P 𝓕) (fun _ => 0) (trapStep u T) (trapStep g T)
        (fun _ _ => 0) (zX σ κ ρ T u g 0 (innovZeta (lamb ρ κ σ) M))
        (zPi σ κ ρ T u g 0 (innovZeta (lamb ρ κ σ) M)) ∧
      Regular (augment P 𝓕) (zX σ κ ρ T u g 0 (innovZeta (lamb ρ κ σ) M)) ∧
      Regular (augment P 𝓕) (zPi σ κ ρ T u g 0 (innovZeta (lamb ρ κ σ) M)) ∧
      BddL2 P (zX σ κ ρ T u g 0 (innovZeta (lamb ρ κ σ) M)) ∧
      BddL2 P (zPi σ κ ρ T u g 0 (innovZeta (lamb ρ κ σ) M)) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨X, hXm, hXI, -, hXc, hXmart⟩ := swmrep_exists_continuous_augment hB hW h𝓕 hcont
    le_rfl hH
  set lam := lamb ρ κ σ with hlam
  have hlam0 : 0 < lam := lamb_pos hκ hσ
  set M : ℝ → Ω → ℝ := fun t ω => c + X t ω with hMdef
  have hMI : ∀ t, 0 ≤ t → M t =ᵐ[P] fun ω => c + mrepInt P 𝓕 W H 0 t ω := fun t ht => by
    filter_upwards [hXI t ht] with ω hω
    simp only [hMdef, hω]
  have hXi : ∀ t, 0 ≤ t → Integrable (X t) P := fun t ht =>
    ((memLp_mrepInt hB hW h𝓕 le_rfl (hH t)).integrable one_le_two).congr (hXI t ht).symm
  have hMc : ∀ ω, Continuous fun t => M t ω := fun ω => continuous_const.add (hXc ω)
  have hMm : ∀ t, StronglyMeasurable[augment P 𝓕 t] (M t) := fun t =>
    stronglyMeasurable_const.add (hXm t)
  have hmart : ∀ s t, 0 ≤ s → s ≤ t → P[M t | augment P 𝓕 s] =ᵐ[P] M s := by
    intro s t hs hst
    have h3 := condExp_add (integrable_const c) (hXi t (hs.trans hst)) (augment P 𝓕 s)
    rw [condExp_const ((augment P 𝓕).le s)] at h3
    filter_upwards [h3, hXmart s t hs hst] with ω e1 e2
    change P[fun ω => c + X t ω | augment P 𝓕 s] ω = c + X s ω
    rw [show (fun ω => c + X t ω) = (fun _ => c) + X t from rfl, e1, Pi.add_apply, e2]
  have hL2 : BddL2 P (innovZeta lam M) := by
    refine ⟨c ^ 2 + K, fun t ht => ?_⟩
    have hI2 := memLp_mrepInt hB hW h𝓕 le_rfl (hH t)
    have hcI : MemLp (fun ω => c + mrepInt P 𝓕 W H 0 t ω) 2 P := (memLp_const c).add hI2
    have hz : innovZeta lam M t =ᵐ[P] fun ω =>
        Real.exp (-(lam * t)) * (c + mrepInt P 𝓕 W H 0 t ω) := by
      filter_upwards [hMI t ht] with ω hω
      simp only [innovZeta, hω]
    refine ⟨(hcI.const_mul (Real.exp (-(lam * t)))).ae_eq hz.symm, ?_⟩
    have hI1 : Integrable (mrepInt P 𝓕 W H 0 t) P := hI2.integrable one_le_two
    have hsq : Integrable (fun ω => mrepInt P 𝓕 W H 0 t ω ^ 2) P := hI2.integrable_sq
    have e1 : ∫ ω, innovZeta lam M t ω ^ 2 ∂P = Real.exp (-(lam * t)) ^ 2 *
        (c ^ 2 + ∫ x, Function.uncurry H x ^ 2 ∂mrepMeasure P 0 t) := by
      rw [integral_congr_ae (hz.mono fun ω hω => by rw [hω])]
      have e : (fun ω => (Real.exp (-(lam * t)) * (c + mrepInt P 𝓕 W H 0 t ω)) ^ 2) =
          fun ω => Real.exp (-(lam * t)) ^ 2 * (c ^ 2 + 2 * c * mrepInt P 𝓕 W H 0 t ω
            + mrepInt P 𝓕 W H 0 t ω ^ 2) := funext fun ω => by ring
      have i1 : Integrable (fun ω => c ^ 2 + 2 * c * mrepInt P 𝓕 W H 0 t ω) P :=
        (integrable_const _).add (hI1.const_mul _)
      rw [e, integral_const_mul, integral_add i1 hsq,
        integral_add (integrable_const _) (hI1.const_mul _), integral_const_mul,
        mrepInt_integral_eq_zero hB hW h𝓕 le_rfl (hH t), mrep_isometry hB hW h𝓕 le_rfl (hH t),
        integral_const, smul_eq_mul, probReal_univ]
      ring
    rw [e1]
    have hexp : Real.exp (-(lam * t)) ^ 2 * Real.exp (2 * lam * t) = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf; exact Real.exp_zero
    have he1 : Real.exp (-(lam * t)) ^ 2 ≤ 1 := by
      have : Real.exp (-(lam * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      nlinarith [Real.exp_pos (-(lam * t))]
    have hK0 := hK t ht
    have hpos : 0 ≤ Real.exp (-(lam * t)) ^ 2 := by positivity
    calc Real.exp (-(lam * t)) ^ 2 * (c ^ 2 + ∫ x, Function.uncurry H x ^ 2 ∂mrepMeasure P 0 t)
        ≤ Real.exp (-(lam * t)) ^ 2 * (c ^ 2 + K * Real.exp (2 * lam * t)) :=
          mul_le_mul_of_nonneg_left (by linarith) hpos
      _ = Real.exp (-(lam * t)) ^ 2 * c ^ 2 + K := by
          linear_combination K * hexp
      _ ≤ c ^ 2 + K := by nlinarith [sq_nonneg c]
  obtain ⟨heq, hrx, hrπ, -, -⟩ := isStochEqm_of_martingale hσ hκ T u g hMc hMm hmart hL2.bddL1
  refine ⟨M, hMI, hMc, heq, hrx, hrπ, ?_, ?_⟩
  · exact BddL2.add (bddL2_det (wPath_bdd (ρ := ρ) hκ hσ T u g 0).1) (BddL2.const_mul hL2 _)
  · exact BddL2.add (bddL2_det (wPath_bdd (ρ := ρ) hκ hσ T u g 0).2) hL2

/-- Cochrane (2023), §20.2.2, p. 475: **bounded integrands satisfy the growth condition** of
`swinnov_eqm_of_integrand`: if `|H| ≤ C` then `E∫_0^t H² ≤ C²t ≤ (C²/(2λ))e^{2λt}`, `λ > 0`. -/
theorem swinnov_growth_of_bdd [IsProbabilityMeasure P] {𝓕 : Filtration ℝ mΩ} {lam C : ℝ}
    (hlam : 0 < lam) {H : ℝ → Ω → ℝ} (hH : ∀ T', MRepIntegrand P 𝓕 H 0 T')
    (hC : ∀ u ω, |H u ω| ≤ C) (t : ℝ) (ht : 0 ≤ t) :
    ∫ x, Function.uncurry H x ^ 2 ∂mrepMeasure P 0 t
      ≤ C ^ 2 / (2 * lam) * Real.exp (2 * lam * t) := by
  have : IsFiniteMeasure (mrepMeasure P 0 t) := by
    unfold mrepMeasure
    infer_instance
  have hμ : (mrepMeasure P 0 t).real Set.univ = t := by
    rw [measureReal_def, mrepMeasure, ← Set.univ_prod_univ, Measure.prod_prod,
      Measure.restrict_apply_univ, Real.volume_Ioc, measure_univ, mul_one, sub_zero,
      ENNReal.toReal_ofReal ht]
  have hi := (hH t).memLp.integrable_sq
  have h1 : ∫ x, Function.uncurry H x ^ 2 ∂mrepMeasure P 0 t ≤ t * C ^ 2 := by
    calc ∫ x, Function.uncurry H x ^ 2 ∂mrepMeasure P 0 t ≤ ∫ _, C ^ 2 ∂mrepMeasure P 0 t :=
          integral_mono hi (integrable_const _) fun x => by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hC _ _) 2
      _ = t * C ^ 2 := by rw [integral_const, smul_eq_mul, hμ]
  have h2 : 2 * lam * t ≤ Real.exp (2 * lam * t) := by
    linarith [Real.add_one_le_exp (2 * lam * t)]
  calc ∫ x, Function.uncurry H x ^ 2 ∂mrepMeasure P 0 t ≤ t * C ^ 2 := h1
    _ = C ^ 2 / (2 * lam) * (2 * lam * t) := by field_simp
    _ ≤ C ^ 2 / (2 * lam) * Real.exp (2 * lam * t) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-- Cochrane (2023), §20.2.2, p. 475: **the growth condition is necessary for mean-square
bounded equilibria.** If `π_t = f(t) + e^{−λt}(c + ∫_0^t H dW)` a.s. for every `t ≥ 0` with `f`
bounded on `[0, ∞)`, `λ ≥ 0`, `H` in the extended class on every `[0, T']`, and `π` is bounded in
mean square, then `E∫_0^t H² ≤ K e^{2λt}` for some `K` and all `t ≥ 0`. -/
theorem swinnov_growth_of_rep (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    {𝓕 : Filtration ℝ mΩ} (h𝓕 : BMFiltration P W 𝓕) {lam c : ℝ} (hlam : 0 ≤ lam)
    {f : ℝ → ℝ} (hf : BddOnIci f) {π : ℝ → Ω → ℝ} {H : ℝ → Ω → ℝ}
    (hH : ∀ T', MRepIntegrand P 𝓕 H 0 T')
    (hrep : ∀ t, 0 ≤ t → π t =ᵐ[P] fun ω => f t + Real.exp (-(lam * t)) *
      (c + mrepInt P 𝓕 W H 0 t ω)) (hπ : BddL2 P π) :
    ∃ K, ∀ t, 0 ≤ t → ∫ x, Function.uncurry H x ^ 2 ∂mrepMeasure P 0 t
      ≤ K * Real.exp (2 * lam * t) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨Kπ, hKπ⟩ := hπ
  obtain ⟨Kf, hKf⟩ := hf
  refine ⟨4 * Kπ + 4 * Kf ^ 2 + 2 * c ^ 2, fun t ht => ?_⟩
  set E := Real.exp (lam * t) with hE
  have hE2 : E ^ 2 = Real.exp (2 * lam * t) := by
    rw [hE, sq, ← Real.exp_add]
    ring_nf
  have hE1 : 1 ≤ E ^ 2 := by
    rw [hE2]
    exact Real.one_le_exp (by positivity)
  have hinv : E * Real.exp (-(lam * t)) = 1 := by
    rw [hE, ← Real.exp_add]
    simp
  have hI : mrepInt P 𝓕 W H 0 t =ᵐ[P] fun ω => E * (π t ω - f t) - c := by
    filter_upwards [hrep t ht] with ω hω
    rw [hω]
    linear_combination (-(c + mrepInt P 𝓕 W H 0 t ω)) * hinv
  have hI2 := memLp_mrepInt hB hW h𝓕 le_rfl (hH t)
  have hπ2 := (hKπ t ht).1.integrable_sq
  have hf2 : f t ^ 2 ≤ Kf ^ 2 := by
    have h := hKf t ht
    nlinarith [abs_nonneg (f t), sq_abs (f t)]
  rw [← mrep_isometry hB hW h𝓕 le_rfl (hH t)]
  have hbd : ∀ᵐ ω ∂P, mrepInt P 𝓕 W H 0 t ω ^ 2 ≤
      4 * E ^ 2 * π t ω ^ 2 + (4 * E ^ 2 * f t ^ 2 + 2 * c ^ 2) := by
    filter_upwards [hI] with ω hω
    rw [hω]
    have h1 : (E * (π t ω - f t) - c) ^ 2 ≤ 2 * (E * (π t ω - f t)) ^ 2 + 2 * c ^ 2 := by
      nlinarith [sq_nonneg (E * (π t ω - f t) + c)]
    have h2 : (π t ω - f t) ^ 2 ≤ 2 * π t ω ^ 2 + 2 * f t ^ 2 := by
      nlinarith [sq_nonneg (π t ω + f t)]
    have h3 : (E * (π t ω - f t)) ^ 2 = E ^ 2 * (π t ω - f t) ^ 2 := by ring
    nlinarith [sq_nonneg E]
  have hint : Integrable (fun ω => 4 * E ^ 2 * π t ω ^ 2 + (4 * E ^ 2 * f t ^ 2 + 2 * c ^ 2)) P :=
    (hπ2.const_mul _).add (integrable_const _)
  calc ∫ ω, mrepInt P 𝓕 W H 0 t ω ^ 2 ∂P
      ≤ ∫ ω, 4 * E ^ 2 * π t ω ^ 2 + (4 * E ^ 2 * f t ^ 2 + 2 * c ^ 2) ∂P :=
        integral_mono_ae hI2.integrable_sq hint hbd
    _ = 4 * E ^ 2 * ∫ ω, π t ω ^ 2 ∂P + (4 * E ^ 2 * f t ^ 2 + 2 * c ^ 2) := by
        rw [integral_add (hπ2.const_mul _) (integrable_const _), integral_const_mul,
          integral_const, smul_eq_mul, probReal_univ, one_mul]
    _ ≤ 4 * E ^ 2 * Kπ + (4 * E ^ 2 * Kf ^ 2 + 2 * E ^ 2 * c ^ 2) := by
        have := (hKπ t ht).2
        have hc2 : c ^ 2 ≤ E ^ 2 * c ^ 2 := le_mul_of_one_le_left (sq_nonneg c) hE1
        nlinarith [sq_nonneg E]
    _ = (4 * Kπ + 4 * Kf ^ 2 + 2 * c ^ 2) * Real.exp (2 * lam * t) := by
        rw [← hE2]
        ring

/-- **Cochrane (2023), §20.2.2, pp. 474–476: the mean-square bounded equilibria are exactly the
pairs `(c, H)` with the growth condition.** In every regular mean-square bounded equilibrium of
the trap experiment for `𝓖 = augment P (bmFiltrationReal W)`, `π_t = wPi(0)_t +
e^{−λ^b t}(c + ∫_0^t H dW)` with `c = E[π_0] − wPi(0)_0` and `H` in the extended class with
`E∫_0^t H² ≤ K e^{2λ^b t}`; conversely every such pair gives one
(`swinnov_eqm_of_integrand`). -/
theorem swinnov_eqm_rep_bddL2 (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    {T u g : ℝ} {x π : ℝ → Ω → ℝ} (hx : Regular (augment P (bmFiltrationReal W hW)) x)
    (hxb : BddL2 P x) (hπ : Regular (augment P (bmFiltrationReal W hW)) π) (hπb : BddL2 P π)
    (h : IsStochEqm σ ρ κ P (augment P (bmFiltrationReal W hW)) (fun _ => 0) (trapStep u T)
      (trapStep g T) (fun _ _ => 0) x π) :
    ∃ H : ℝ → Ω → ℝ, (∀ T', MRepIntegrand P (bmFiltrationReal W hW) H 0 T') ∧
      (∃ K, ∀ t, 0 ≤ t → ∫ x, Function.uncurry H x ^ 2 ∂mrepMeasure P 0 t
        ≤ K * Real.exp (2 * lamb ρ κ σ * t)) ∧
      ∀ t, 0 ≤ t → π t =ᵐ[P] fun ω => wPi σ κ ρ T u g 0 t + Real.exp (-(lamb ρ κ σ * t)) *
        ((∫ ω, π 0 ω ∂P) - wPi σ κ ρ T u g 0 0
          + mrepInt P (bmFiltrationReal W hW) W H 0 t ω) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨H, hH, hrep, -⟩ := swinnov_eqm_rep hB hW hcont hσ hκ hx hxb.bddL1 hπ hπb.bddL1 h
    (fun t ht => ((Classical.choose_spec hπb) t ht).1)
  exact ⟨H, hH, swinnov_growth_of_rep hB hW (bmFiltrationReal_isBM hB hW)
    (lamb_pos hκ hσ).le (wPath_bdd (ρ := ρ) hκ hσ T u g 0).2 hH hrep hπb, hrep⟩

/-! ## Continuous loadings that are not `C¹` -/

/-- Cochrane (2023), §20.2.2, p. 475 (tool): a continuous deterministic integrand is mean-square
continuous. -/
theorem swinnov_msIntegrand_det [IsProbabilityMeasure P] (𝓕 : Filtration ℝ mΩ) {f : ℝ → ℝ}
    (hf : Continuous f) (s t : ℝ) : MSIntegrand P 𝓕 (fun u _ => f u) s t where
  adapted _ _ := stronglyMeasurable_const
  memLp _ _ := memLp_const _
  cont := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.1
      (isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn) (Real.sqrt ε)
      (Real.sqrt_pos.2 hε)
    refine ⟨δ / 2, half_pos hδ, fun u hu v hv huv => ?_⟩
    have h1 := h u hu v hv (by rw [Real.dist_eq]; linarith)
    rw [Real.dist_eq] at h1
    rw [integral_const, smul_eq_mul, probReal_univ, one_mul]
    calc (f u - f v) ^ 2 = |f u - f v| ^ 2 := (sq_abs _).symm
      _ ≤ Real.sqrt ε ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1.le 2
      _ = ε := Real.sq_sqrt hε.le

/-- **Cochrane (2023), (20.5)–(20.6), p. 474: equilibria with continuous (not necessarily `C¹`)
innovation loadings.** Let `W` be pre-Brownian with measurable values and a.s. continuous paths,
`𝓕` admissible, `σ, κ > 0`, and `b` continuous with `|b(u)| ≤ B` for `u ≥ 0`. With
`M_t = ∫_0^t e^{λ^b u}b(u) dW_u` (a continuous version, every path), the processes
`π = wPi(0) + e^{−λ^b t}M`, `x = wX(0) + (λ^f/κ)e^{−λ^b t}M` (innovations `dπ_t = b(t)dW_t`,
`dx_t = (λ^f/κ)b(t)dW_t`) are a stochastic equilibrium of the trap experiment for the completed
filtration, regular and bounded in mean square. Generalises
`TidyR8StochWerningMartingale.isStochEqm_loading` (`C¹` loadings). -/
theorem swinnov_loading_continuous (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    {𝓕 : Filtration ℝ mΩ} (h𝓕 : BMFiltration P W 𝓕)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => W t ω) {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (T u g : ℝ) {b : ℝ → ℝ} (hb : Continuous b) {B : ℝ} (hbB : ∀ u, 0 ≤ u → |b u| ≤ B) :
    ∃ M : ℝ → Ω → ℝ, (∀ t, 0 ≤ t → M t =ᵐ[P]
        itoInt P 𝓕 W (fun u _ => loadH (lamb ρ κ σ) b u) 0 t) ∧
      (∀ ω, Continuous fun t => M t ω) ∧
      IsStochEqm σ ρ κ P (augment P 𝓕) (fun _ => 0) (trapStep u T) (trapStep g T)
        (fun _ _ => 0) (zX σ κ ρ T u g 0 (innovZeta (lamb ρ κ σ) M))
        (zPi σ κ ρ T u g 0 (innovZeta (lamb ρ κ σ) M)) ∧
      Regular (augment P 𝓕) (zX σ κ ρ T u g 0 (innovZeta (lamb ρ κ σ) M)) ∧
      Regular (augment P 𝓕) (zPi σ κ ρ T u g 0 (innovZeta (lamb ρ κ σ) M)) ∧
      BddL2 P (zX σ κ ρ T u g 0 (innovZeta (lamb ρ κ σ) M)) ∧
      BddL2 P (zPi σ κ ρ T u g 0 (innovZeta (lamb ρ κ σ) M)) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set lam := lamb ρ κ σ with hlam
  have hlam0 : 0 < lam := lamb_pos hκ hσ
  have hhc : Continuous (loadH lam b) := by unfold loadH; fun_prop
  have hms : ∀ T', MSIntegrand P 𝓕 (fun u _ => loadH lam b u) 0 T' := fun T' =>
    swinnov_msIntegrand_det 𝓕 hhc 0 T'
  have hm : Measurable (Function.uncurry fun (u : ℝ) (_ : Ω) => loadH lam b u) :=
    hhc.measurable.comp measurable_fst
  have hag := fun T' => mrep_agree hB hW h𝓕 le_rfl (hms T') hm
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hbB 0 le_rfl)
  have hK : ∀ t, 0 ≤ t → ∫ x, Function.uncurry (fun (u : ℝ) (_ : Ω) => loadH lam b u) x ^ 2
      ∂mrepMeasure P 0 t ≤ B ^ 2 / (2 * lam) * Real.exp (2 * lam * t) := by
    intro t ht
    rw [mrep_integral_sq (hms t) hm ht]
    simp only [integral_const, smul_eq_mul, probReal_univ, one_mul]
    have e2 : ∫ u in (0 : ℝ)..t, loadH lam b u ^ 2 ≤
        ∫ u in (0 : ℝ)..t, B ^ 2 * Real.exp (lam * u) ^ 2 := by
      refine intervalIntegral.integral_mono_on ht
        ((by fun_prop : Continuous fun u => loadH lam b u ^ 2).intervalIntegrable 0 t)
        ((by fun_prop : Continuous fun u => B ^ 2 * Real.exp (lam * u) ^ 2).intervalIntegrable
          0 t) fun u hu => ?_
      simp only [loadH, mul_pow]
      rw [mul_comm]
      have : b u ^ 2 ≤ B ^ 2 := by
        have := hbB u hu.1
        nlinarith [abs_nonneg (b u), sq_abs (b u)]
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    rw [intervalIntegral.integral_const_mul,
      Cochrane.ZeroBound.TidyR7OrnsteinUhlenbeck.integral_exp_sq hlam0.ne', mul_zero,
      Real.exp_zero] at e2
    calc ∫ u in (0 : ℝ)..t, loadH lam b u ^ 2
        ≤ B ^ 2 * ((Real.exp (2 * lam * t) - 1) / (2 * lam)) := e2
      _ ≤ B ^ 2 / (2 * lam) * Real.exp (2 * lam * t) := by
          rw [show B ^ 2 * ((Real.exp (2 * lam * t) - 1) / (2 * lam)) =
            B ^ 2 / (2 * lam) * Real.exp (2 * lam * t) - B ^ 2 / (2 * lam) by ring]
          have : 0 ≤ B ^ 2 / (2 * lam) := by positivity
          linarith
  obtain ⟨M, hMI, hMc, heq, hrx, hrπ, hbx, hbπ⟩ := swinnov_eqm_of_integrand hB hW h𝓕 hcont hσ hκ
    T u g 0 (fun T' => (hag T').1) hK
  refine ⟨M, fun t ht => ?_, hMc, heq, hrx, hrπ, hbx, hbπ⟩
  filter_upwards [hMI t ht, (hag t).2] with ω e1 e2
  rw [e1, e2, zero_add]

/-! ## Non-vacuity on the constructed Brownian motion -/

open Cochrane.ZeroBound.TidyR7BrownianExist Cochrane.ZeroBound.TidyR7BrownianSchauder

/-- **Cochrane (2023), §20.2.2, p. 475 (non-vacuity): the representation of a constant-loading
equilibrium.** On bmPath at the book's calibration (`ρ = 0.05`, `σ = κ = 1`, `T = 5`,
`u_r = −2%`, `g = 0`), the Ornstein–Uhlenbeck equilibrium with loading `1` of
TidyR7StochWerningExist has `π_t = wPi(0)_t + e^{−λ^b t}(c + ∫_0^t H dW)` a.s. for every
`t ≥ 0`, with
one `H` in the extended class on every horizon. -/
theorem bmPath_swinnov_rep :
    ∃ H : ℝ → (ℕ → ℝ) → ℝ,
      (∀ T', MRepIntegrand gaussSeq (bmFiltrationReal bmPath measurable_bmPath) H 0 T') ∧
      ∀ t, 0 ≤ t → eqPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 1 bmPath t =ᵐ[gaussSeq] fun ω =>
        wPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 t + Real.exp (-(lamb (1 / 20) 1 1 * t)) *
          ((∫ ω, eqPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 1 bmPath 0 ω ∂gaussSeq)
            - wPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 0
            + mrepInt gaussSeq (bmFiltrationReal bmPath measurable_bmPath) bmPath H 0 t ω) := by
  have := isProbabilityMeasure_gaussSeq
  obtain ⟨heq, hπ, hbπ, hbx⟩ := bmPath_isStochEqm
  have hx := regular_eqX measurable_bmPath continuous_bmPath one_pos one_pos (ρ := 1 / 20) 5
    (-2 / 100) 0 0 1
  obtain ⟨H, hH, hrep, -⟩ := swinnov_eqm_rep_natural isPreBrownianReal_bmPath measurable_bmPath
    continuous_bmPath one_pos one_pos hx hbx.bddL1 hπ hbπ.bddL1 heq
    (fun t ht => ((Classical.choose_spec hbπ) t ht).1)
  exact ⟨H, hH, hrep⟩

/-- Cochrane (2023), §20.2.2, p. 476 (non-vacuity, tool): the window loading `1_{(1,2]}`
(news arrives only between dates `1` and `2`) is in the extended class on every horizon. -/
theorem bmPath_window_integrand (T' : ℝ) :
    MRepIntegrand gaussSeq (bmFiltrationReal bmPath measurable_bmPath)
      (mrepCut 1 2 fun _ _ => (1 : ℝ)) 0 T' := by
  have := isProbabilityMeasure_gaussSeq
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  have h2 := (mrep_cut hB measurable_bmPath h𝓕 le_rfl zero_le_one one_le_two (le_max_left 2 T')
    (G := fun _ _ => (1 : ℝ)) (swinnov_msIntegrand_det (P := gaussSeq)
      (bmFiltrationReal bmPath measurable_bmPath) (f := fun _ => (1 : ℝ)) continuous_const 1 2)
      measurable_const).1
  exact mrep_mono h2 le_rfl (le_max_right 2 T')

/-- **Cochrane (2023), §20.2.2, pp. 474–476 (non-vacuity): news in a window.** On bmPath at the
book's calibration, the innovation loading `H = 1_{(1,2]}` (not mean-square continuous: it jumps
at `1` and `2`) with `M_0 = c` gives, for every `c`, a regular mean-square bounded equilibrium for
the completed filtration with `M_t = c + ∫_0^t 1_{(1,2]} dW` a.s. -/
theorem bmPath_swinnov_window (c : ℝ) :
    ∃ M : ℝ → (ℕ → ℝ) → ℝ, (∀ t, 0 ≤ t → M t =ᵐ[gaussSeq] fun ω => c + mrepInt gaussSeq
        (bmFiltrationReal bmPath measurable_bmPath) bmPath (mrepCut 1 2 fun _ _ => (1 : ℝ))
          0 t ω) ∧
      IsStochEqm 1 (1 / 20) 1 gaussSeq (augment gaussSeq
          (bmFiltrationReal bmPath measurable_bmPath)) (fun _ => 0) (trapStep (-2 / 100) 5)
        (trapStep 0 5) (fun _ _ => 0)
        (zX 1 1 (1 / 20) 5 (-2 / 100) 0 0 (innovZeta (lamb (1 / 20) 1 1) M))
        (zPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 (innovZeta (lamb (1 / 20) 1 1) M)) ∧
      Regular (augment gaussSeq (bmFiltrationReal bmPath measurable_bmPath))
        (zPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 (innovZeta (lamb (1 / 20) 1 1) M)) ∧
      BddL2 gaussSeq (zPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 (innovZeta (lamb (1 / 20) 1 1) M)) := by
  have := isProbabilityMeasure_gaussSeq
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  have hC : ∀ (u : ℝ) (ω : ℕ → ℝ), |mrepCut 1 2 (fun _ _ => (1 : ℝ)) u ω| ≤ (1 : ℝ) :=
    fun u ω => by
      by_cases h : u ∈ Set.Ioc (1 : ℝ) 2 <;> simp [mrepCut, h]
  obtain ⟨M, hMI, -, heq, -, hrπ, -, hbπ⟩ := swinnov_eqm_of_integrand hB measurable_bmPath h𝓕
    (ae_of_all _ continuous_bmPath) one_pos one_pos (ρ := 1 / 20) 5 (-2 / 100) 0 c
    bmPath_window_integrand
    (swinnov_growth_of_bdd (lamb_pos one_pos one_pos) bmPath_window_integrand hC)
  exact ⟨M, hMI, heq, hrπ, hbπ⟩

/-- Cochrane (2023), §20.2.2, p. 475 (non-vacuity, tool): the loading `|sin t|` is continuous
but not differentiable at `0`, so it is not `C¹`. -/
theorem not_differentiableAt_abs_sin : ¬ DifferentiableAt ℝ (fun t => |Real.sin t|) 0 := by
  intro h
  have hd := h.hasDerivAt
  set d := deriv (fun t => |Real.sin t|) 0
  have heven : (fun t => |Real.sin t|) ∘ (fun t : ℝ => -t) = fun t => |Real.sin t| :=
    funext fun t => by simp [Real.sin_neg, abs_neg]
  have hd' : HasDerivAt (fun t => |Real.sin t|) d (-(0 : ℝ)) := by rwa [neg_zero]
  have hneg := hd'.comp (0 : ℝ) (hasDerivAt_neg 0)
  rw [heven] at hneg
  have h0 : d = d * -1 := hd.unique hneg
  have h1 : HasDerivWithinAt Real.sin 1 (Set.Icc 0 1) 0 := by
    simpa using (Real.hasDerivAt_sin 0).hasDerivWithinAt
  have hR : HasDerivWithinAt (fun t => |Real.sin t|) 1 (Set.Icc 0 1) 0 :=
    h1.congr_of_mem (fun t ht => abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ht.1
      (ht.2.trans (by linarith [Real.two_le_pi])))) ⟨le_rfl, zero_le_one⟩
  have h2 : d = 1 := (uniqueDiffOn_Icc zero_lt_one 0 ⟨le_rfl, zero_le_one⟩).eq_deriv _
    hd.hasDerivWithinAt hR
  linarith

/-- **Cochrane (2023), (20.5)–(20.6), p. 474 (non-vacuity): a continuous loading that is not
`C¹`.** On bmPath at the book's calibration, the innovation loading `b(t) = |sin t|` gives a
regular mean-square bounded equilibrium for the completed filtration, with
`M_t = ∫_0^t e^{λ^b u}|sin u| dW_u` a.s. -/
theorem bmPath_swinnov_abs_sin :
    ∃ M : ℝ → (ℕ → ℝ) → ℝ, (∀ t, 0 ≤ t → M t =ᵐ[gaussSeq] itoInt gaussSeq
        (bmFiltrationReal bmPath measurable_bmPath) bmPath
          (fun u _ => loadH (lamb (1 / 20) 1 1) (fun t => |Real.sin t|) u) 0 t) ∧
      IsStochEqm 1 (1 / 20) 1 gaussSeq (augment gaussSeq
          (bmFiltrationReal bmPath measurable_bmPath)) (fun _ => 0) (trapStep (-2 / 100) 5)
        (trapStep 0 5) (fun _ _ => 0)
        (zX 1 1 (1 / 20) 5 (-2 / 100) 0 0 (innovZeta (lamb (1 / 20) 1 1) M))
        (zPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 (innovZeta (lamb (1 / 20) 1 1) M)) ∧
      Regular (augment gaussSeq (bmFiltrationReal bmPath measurable_bmPath))
        (zPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 (innovZeta (lamb (1 / 20) 1 1) M)) ∧
      BddL2 gaussSeq (zPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 (innovZeta (lamb (1 / 20) 1 1) M)) := by
  have := isProbabilityMeasure_gaussSeq
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  obtain ⟨M, hMI, -, heq, -, hrπ, -, hbπ⟩ := swinnov_loading_continuous hB measurable_bmPath h𝓕
    (ae_of_all _ continuous_bmPath) one_pos one_pos (ρ := 1 / 20) 5 (-2 / 100) 0
    (b := fun t => |Real.sin t|) (by fun_prop) (B := 1) fun u _ => by
      rw [abs_abs]; exact Real.abs_sin_le_one u
  exact ⟨M, hMI, heq, hrπ, hbπ⟩

end Cochrane.ZeroBound.TidyR9StochWerningInnovations
