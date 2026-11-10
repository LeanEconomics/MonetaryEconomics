/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR7StochWerningSelect
import ZeroBound.Multipliers

/-!
# The frictionless limit and the multipliers under uncertainty

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.3, pp. 477–478 (the
puzzling frictionless limit) and §20.2.5, pp. 480–482 (magical multipliers), under uncertainty.

ZLBSelection and Multipliers prove the deterministic statements. In a stochastic equilibrium
(TidyR7StochWerning) the two selections act differently:

* the new-Keynesian selection `π_T = 0` (a.s.) removes all uncertainty during the trap
  (TidyR7StochWerningSelect.nk_selection), so the deterministic results hold **state by
  state**: `nk_multiplier_stoch` (`x_t(g) = x_t(0) + g · multNK_t` almost surely on `[0, T]`, and in
  mean at every date) and `nk_frictionless_stoch` (for every family of equilibria indexed by
  `κ`, almost surely `π_t → −∞` as `κ → ∞` at every `t ∈ [0, T)`, the discontinuity of
  p. 478);
* the fiscal no-jump selection `π_0 = 0` pins only the mean path
  (TidyR7StochWerningSelect.fiscal_pi0_mean), so the deterministic results hold **for the means**:
  `mean_piT_nj` (`Eπ_T = π_T^{nj}(g)`), `nj_mean_multiplier` (`E x_t(g) = E x_t(0) + g · multNJ_t`,
  with `−1 < multNJ_t < 0` during the trap, `nj_mean_multiplier_bounds`) and
  `nj_frictionless_stoch` (`E π_t → −u` on `(0, T)` and `→ 0` after `T` as `κ → ∞`: the smooth
  square-wave limit), whatever the innovations;
* conditional expectations follow the same family with `π_T` replaced by `E_sπ_T`
  (TidyR7StochWerningTrap.condExp_pi_eq_wPi, condExp_x_eq_wX).

The deterministic results are the case of processes constant in `ω` (`σ = 0` noise):
`det_nj_multiplier` recovers `Multipliers.xNJ_affine` for every bounded deterministic path with
`π_0 = 0` from the stochastic theorem (on the one-point probability space).
-/

namespace Cochrane.ZeroBound.TidyR8StochWerningLimits

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.ContinuousTimeNK Cochrane.ZeroBound.WerningModel
open Cochrane.ZeroBound.TidyR7StochWerning Cochrane.ZeroBound.TidyR7StochWerningTrap
open Cochrane.ZeroBound.TidyR7StochWerningSelect
open Cochrane.ZeroBound.ZLBSelection Cochrane.ZeroBound.Multipliers

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ## The new-Keynesian selection: state by state -/

/-- **Cochrane (2023), §20.2.5, p. 481, under uncertainty: the standard multiplier holds state by
state.** In every regular `L¹`-bounded equilibrium of the experiment with disturbance `g` and
`π_T = 0` almost surely, `x_t = x^{NK}_t(0) + g · multNK_t` almost surely for `0 ≤ t ≤ T`, and in
mean, `E x_t = x^{NK}_t(0) + g · multNK_t`, at every `t ≥ 0`.
The stochastic `Multipliers.xNK_affine`. -/
theorem nk_multiplier_stoch [IsProbabilityMeasure P] {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    {𝓕 : Filtration ℝ mΩ} {T u g : ℝ} (hT : 0 ≤ T) {x π : ℝ → Ω → ℝ} (hx : Regular 𝓕 x)
    (hxb : BddL1 P x) (hπ : Regular 𝓕 π) (hπb : BddL1 P π)
    (h : IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep g T) (fun _ _ => 0) x π)
    (hπT : π T =ᵐ[P] fun _ => 0) :
    (∀ t, 0 ≤ t → t ≤ T →
      x t =ᵐ[P] fun _ => xNK σ κ ρ T u 0 t + g * multNK σ κ ρ T t) ∧
    ∀ t, 0 ≤ t → ∫ ω, x t ω ∂P = xNK σ κ ρ T u 0 t + g * multNK σ κ ρ T t := by
  refine ⟨fun t ht htT => ?_, fun t ht => ?_⟩
  · filter_upwards [(nk_selection hσ hκ hx hxb hπ hπb h 0 hπT ht htT).2] with ω hω
    rw [hω, ← xNK_affine hσ hκ]
    rfl
  · have hm := (mean_eq_wPi hσ hκ hx hxb hπ hπb h hT ht).2
    rw [integral_congr_ae hπT, integral_const, smul_zero] at hm
    rw [hm, ← xNK_affine hσ hκ]
    rfl

/-- **Cochrane (2023), §20.2.3, pp. 477–478, under uncertainty: deflation without limit, state by
state.** Let `(x^κ, π^κ)` be, for each `κ > 0`, a regular `L¹`-bounded equilibrium of the trap
(`g = 0`, `u < 0`, `ρ ≥ 0`) with `π^κ_T = 0` almost surely. Then at every `t ∈ [0, T)`, for every
level `M`, eventually in `κ` the inflation `π^κ_t` is below `M` almost surely.
The stochastic `ZLBSelection.nk_tendsto_kappa`. -/
theorem nk_frictionless_stoch [IsProbabilityMeasure P] {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ)
    {𝓕 : Filtration ℝ mΩ} {T u : ℝ} (hu : u < 0) {x π : ℝ → ℝ → Ω → ℝ}
    (hx : ∀ κ, 0 < κ → Regular 𝓕 (x κ)) (hxb : ∀ κ, 0 < κ → BddL1 P (x κ))
    (hπ : ∀ κ, 0 < κ → Regular 𝓕 (π κ)) (hπb : ∀ κ, 0 < κ → BddL1 P (π κ))
    (h : ∀ κ, 0 < κ →
      IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep 0 T) (fun _ _ => 0) (x κ) (π κ))
    (hπT : ∀ κ, 0 < κ → π κ T =ᵐ[P] fun _ => 0) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) (M : ℝ) :
    ∀ᶠ κ in atTop, ∀ᵐ ω ∂P, π κ t ω < M := by
  filter_upwards [(nk_tendsto_kappa hσ hρ hu htT).eventually (eventually_lt_atBot M),
    eventually_gt_atTop 0] with κ hκ hκ0
  filter_upwards [(nk_selection hσ hκ0 (hx κ hκ0) (hxb κ hκ0) (hπ κ hκ0) (hπb κ hκ0) (h κ hκ0) 0
    (hπT κ hκ0) ht htT.le).1] with ω hω
  rw [hω]
  exact hκ

/-! ## The fiscal no-jump selection: the means -/

/-- Cochrane (2023), §20.2.2, p. 476, and §20.2.5, p. 481, under uncertainty: **with `π_0 = 0`
the expected end-of-trap inflation is the no-jump value**, `Eπ_T = π_T^{nj}(g)`
(`Multipliers.piTnjg`). -/
theorem mean_piT_nj [IsProbabilityMeasure P] {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    {𝓕 : Filtration ℝ mΩ} {T u g : ℝ} (hT : 0 ≤ T) {x π : ℝ → Ω → ℝ} (hx : Regular 𝓕 x)
    (hxb : BddL1 P x) (hπ : Regular 𝓕 π) (hπb : BddL1 P π)
    (h : IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep g T) (fun _ _ => 0) x π)
    (hπ0 : π 0 =ᵐ[P] fun _ => 0) : ∫ ω, π T ω ∂P = piTnjg σ κ ρ T u g := by
  have hm := (mean_eq_wPi hσ hκ hx hxb hπ hπb h hT le_rfl).1
  rw [integral_congr_ae hπ0, integral_const, smul_zero] at hm
  have h2 := nj_g_pi0 (σ := σ) (κ := κ) (ρ := ρ) (u := u) (g := g) hT
  rw [wPi_shift] at hm h2
  have hpos : 0 < Real.exp (lamb ρ κ σ * (T - 0)) := Real.exp_pos _
  have := mul_right_cancel₀ hpos.ne' (show (∫ ω, π T ω ∂P) * Real.exp (lamb ρ κ σ * (T - 0)) =
    piTnjg σ κ ρ T u g * Real.exp (lamb ρ κ σ * (T - 0)) by linarith)
  exact this

/-- **Cochrane (2023), §20.2.5, p. 481, under uncertainty: the no-jump multiplier holds for the
means.** In every regular `L¹`-bounded equilibrium with disturbance `g` and `π_0 = 0` almost
surely (any innovations), at every `t ≥ 0`: `E π_t = wPi(π_T^{nj}(g))_t` and
`E x_t = x^{NJ}_t(0) + g · multNJ_t`.
The stochastic `Multipliers.xNJ_affine`. -/
theorem nj_mean_multiplier [IsProbabilityMeasure P] {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    {𝓕 : Filtration ℝ mΩ} {T u g : ℝ} (hT : 0 ≤ T) {x π : ℝ → Ω → ℝ} (hx : Regular 𝓕 x)
    (hxb : BddL1 P x) (hπ : Regular 𝓕 π) (hπb : BddL1 P π)
    (h : IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep g T) (fun _ _ => 0) x π)
    (hπ0 : π 0 =ᵐ[P] fun _ => 0) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, π t ω ∂P = wPi σ κ ρ T u g (piTnjg σ κ ρ T u g) t ∧
      ∫ ω, x t ω ∂P = xNJ σ κ ρ T u 0 t + g * multNJ σ κ ρ T t := by
  have hm := mean_eq_wPi hσ hκ hx hxb hπ hπb h hT ht
  rw [mean_piT_nj hσ hκ hT hx hxb hπ hπb h hπ0] at hm
  refine ⟨hm.1, ?_⟩
  rw [hm.2, ← xNJ_affine hσ hκ]
  rfl

/-- Cochrane (2023), §20.2.5, p. 481 ("the multiplier in the no-jump equilibrium is small"), under
uncertainty: for two equilibria with `π_0 = 0` a.s., disturbances `g` and `0`, the mean
multiplier `(E x_t(g) − E x_t(0))/g` lies in `(−1, 0)` during the trap (`g ≠ 0`, `T > 0`).
The stochastic `Multipliers.multNJ_bounds`. -/
theorem nj_mean_multiplier_bounds [IsProbabilityMeasure P] {σ ρ κ : ℝ} (hσ : 0 < σ)
    (hκ : 0 < κ) {𝓕 : Filtration ℝ mΩ} {T u g : ℝ} (hT : 0 < T) {x π x0 π0 : ℝ → Ω → ℝ}
    (hx : Regular 𝓕 x) (hxb : BddL1 P x) (hπ : Regular 𝓕 π) (hπb : BddL1 P π)
    (h : IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep g T) (fun _ _ => 0) x π)
    (hπ0 : π 0 =ᵐ[P] fun _ => 0) (hx0 : Regular 𝓕 x0) (hxb0 : BddL1 P x0) (hπ' : Regular 𝓕 π0)
    (hπb0 : BddL1 P π0)
    (h0 : IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep 0 T) (fun _ _ => 0) x0 π0)
    (hπ00 : π0 0 =ᵐ[P] fun _ => 0) (hg : g ≠ 0) {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    -1 < (∫ ω, x t ω ∂P - ∫ ω, x0 t ω ∂P) / g ∧ (∫ ω, x t ω ∂P - ∫ ω, x0 t ω ∂P) / g < 0 := by
  have e1 := (nj_mean_multiplier hσ hκ hT.le hx hxb hπ hπb h hπ0 ht).2
  have e0 := (nj_mean_multiplier hσ hκ hT.le hx0 hxb0 hπ' hπb0 h0 hπ00 ht).2
  rw [e1, e0, zero_mul, add_zero, add_sub_cancel_left, mul_div_cancel_left₀ _ hg]
  exact multNJ_bounds hσ hκ hT ht htT

/-- **Cochrane (2023), §20.2.3, p. 478, under uncertainty: the smooth frictionless limit of the
no-jump selection, in mean.** Let `(x^κ, π^κ)` be, for each `κ > 0`, a regular `L¹`-bounded
equilibrium of the trap (`g = 0`, `u < 0`) with `π^κ_0 = 0` almost surely (any innovations).
Then `E π^κ_t → −u` for `t ∈ (0, T)` and `E π^κ_t → 0` for `t > T`, as `κ → ∞`.
The stochastic `ZLBSelection.nj_limit_trap` and `ZLBSelection.nj_limit_after`. -/
theorem nj_frictionless_stoch [IsProbabilityMeasure P] {σ ρ : ℝ} (hσ : 0 < σ)
    {𝓕 : Filtration ℝ mΩ} {T u : ℝ} (hT : 0 < T) (hu : u < 0) {x π : ℝ → ℝ → Ω → ℝ}
    (hx : ∀ κ, 0 < κ → Regular 𝓕 (x κ)) (hxb : ∀ κ, 0 < κ → BddL1 P (x κ))
    (hπ : ∀ κ, 0 < κ → Regular 𝓕 (π κ)) (hπb : ∀ κ, 0 < κ → BddL1 P (π κ))
    (h : ∀ κ, 0 < κ →
      IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep 0 T) (fun _ _ => 0) (x κ) (π κ))
    (hπ0 : ∀ κ, 0 < κ → π κ 0 =ᵐ[P] fun _ => 0) :
    (∀ t, 0 < t → t < T → Tendsto (fun κ => ∫ ω, π κ t ω ∂P) atTop (𝓝 (-u))) ∧
      ∀ t, T < t → Tendsto (fun κ => ∫ ω, π κ t ω ∂P) atTop (𝓝 0) := by
  have hmean : ∀ t, 0 ≤ t → (fun κ => wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) t) =ᶠ[atTop]
      fun κ => ∫ ω, π κ t ω ∂P := fun t ht => by
    filter_upwards [eventually_gt_atTop 0] with κ hκ
    rw [(nj_mean_multiplier hσ hκ hT.le (hx κ hκ) (hxb κ hκ) (hπ κ hκ) (hπb κ hκ) (h κ hκ)
      (hπ0 κ hκ) ht).1]
    congr 1
    simp only [piTnjg, piTnj, mul_zero]
    ring
  exact ⟨fun t ht htT => (nj_limit_trap hσ hu ht htT).congr' (hmean t ht.le),
    fun t ht => (nj_limit_after hσ hu hT ht).congr' (hmean t (hT.le.trans ht.le))⟩

/-! ## The deterministic case -/

/-- Cochrane (2023), §20.2.5, p. 481 (the case without uncertainty): **the deterministic no-jump
multiplier as a special case.** For a bounded continuous deterministic path `(x, π)` of the
experiment (`IsPath`) with `π_0 = 0`, `x_t = x^{NJ}_t(0) + g · multNJ_t` for `t ≥ 0` — derived
from `nj_mean_multiplier` on the one-point probability space, where every process is
deterministic (`TidyR7StochWerningTrap.det_bdd_iff`). -/
theorem det_nj_multiplier {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) {T u g : ℝ} (hT : 0 ≤ T)
    {x π : ℝ → ℝ} (hxc : Continuous x) (hπc : Continuous π)
    (hp : IsPath σ ρ κ (fun _ => 0) (trapStep u T) (trapStep g T) {T} x π) (hxb : BddOnIci x)
    (hπb : BddOnIci π) (hπ0 : π 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    x t = xNJ σ κ ρ T u 0 t + g * multNJ σ κ ρ T t := by
  let P1 : Measure Unit := Measure.dirac ()
  let F1 : Filtration ℝ (inferInstance : MeasurableSpace Unit) := ⊥
  have hbd : ∀ f : ℝ → ℝ, BddOnIci f → BddL1 P1 (fun t _ => f t) := fun f ⟨K, hK⟩ =>
    ⟨K, fun t ht => ⟨integrable_const _, by simpa using hK t ht⟩⟩
  have hreg : ∀ f : ℝ → ℝ, Continuous f → Regular F1 (fun t (_ : Unit) => f t) := fun f hf =>
    ⟨fun _ => hf, fun _ => stronglyMeasurable_const⟩
  have heq := (isStochEqm_det_iff (P := P1) (𝓕 := F1) hxc hπc).2 hp
  have := (nj_mean_multiplier hσ hκ hT (hreg x hxc) (hbd x hxb) (hreg π hπc) (hbd π hπb) heq
    (Eventually.of_forall fun _ => hπ0) ht).2
  simpa [P1] using this

end Cochrane.ZeroBound.TidyR8StochWerningLimits
