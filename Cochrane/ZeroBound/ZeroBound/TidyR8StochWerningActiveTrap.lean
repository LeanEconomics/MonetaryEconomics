/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR7StochWerningSelect

/-!
# The trap and the active rule in one stochastic model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.2, pp. 474–476
(equation (20.7) and the new-Keynesian choice of `π_T`), §20.2.4, pp. 478–479 (forward guidance:
a "glide path" after the trap), under uncertainty.

TidyR7StochWerningSelect treats the active rule after `T` (`active_rule_selects`) and the trap
before `T` (`nk_selection`) separately. Here they are one model on `[0, ∞)`: the interest rate is
`0` during the trap and follows the active rule (20.7) `i_t = i*_t + φ(π_t − π*_t)` after it,
with `i* = 0` (the natural rate after the trap) and target `π* = wPi(c)` — the member of the
family of Figure 20.4 with `π_T = c` (`c = 0` is the new-Keynesian choice, `c ≠ 0` a glide path
of forward guidance, e.g. the no-jump path of p. 476). The interest rate is random: it responds
to inflation after `T` (`ruleRate`, `IsActiveTrapEqm`).

## Main results

* `ae_forall_Ici_of_forall_ae`: a process with continuous paths that equals a continuous
  deterministic path almost surely at every date `t ≥ T` equals it on all of `[T, ∞)` for almost
  every path.
* **`active_trap_selects`**: for `σ, κ, ρ > 0`, `φ > 1`, `T ≥ 0`, every regular `L¹`-bounded
  stochastic equilibrium of the composed model is `π_t = wPi(c)_t`, `x_t = wX(c)_t` almost surely
  at every date `t ≥ 0`; `active_trap_selects_paths`: almost every path equals the chosen path
  on all of `[0, ∞)`. All uncertainty is removed, before and after `T`.
* **`active_trap_exists`**: the chosen path is an equilibrium of the composed model (regular,
  bounded). Together: the composed model has exactly one equilibrium.
* Non-vacuity at the book's calibration on bmPath: `bmPath_active_trap` (existence, and the
  Ornstein–Uhlenbeck equilibrium of TidyR7StochWerningExist with unit loading, an equilibrium of
  the trap with `i = 0` throughout, is not an equilibrium of the composed model).
-/

namespace Cochrane.ZeroBound.TidyR8StochWerningActiveTrap

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.ContinuousTimeNK Cochrane.ZeroBound.WerningModel
open Cochrane.ZeroBound.TidyR7StochWerning Cochrane.ZeroBound.TidyR7StochWerningTrap
open Cochrane.ZeroBound.TidyR7StochWerningExist Cochrane.ZeroBound.TidyR7StochWerningSelect

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Cochrane (2023), (20.7), p. 474, composed with the trap: the interest rate `0` before `T`
and `φ(π_t − π*_t)` from `T` on (`i* = 0`, the natural rate after the trap). -/
noncomputable def ruleRate (φ T : ℝ) (πs : ℝ → ℝ) (π : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  if t < T then 0 else φ * (π t ω - πs t)

/-- Cochrane (2023), (20.5)–(20.7), pp. 474–476, under uncertainty: **an equilibrium of the
composed model** — the trap experiment (natural rate `u` and disturbance `g` on `[0, T)`) with
the zero rate before `T` and the active rule `i = φ(π − wPi(c))` after `T`:
`E_t dx = σ(i_t − π_t − u_{r,t})dt`, `E_t dπ = (ρπ_t − κ(x_t + g_t))dt`. -/
def IsActiveTrapEqm (σ ρ κ φ : ℝ) (P : Measure Ω) (𝓕 : Filtration ℝ mΩ) (T u g c : ℝ)
    (x π : ℝ → Ω → ℝ) : Prop :=
  ExpDrift P 𝓕 x (fun r ω =>
      σ * (ruleRate φ T (wPi σ κ ρ T u g c) π r ω - π r ω - trapStep u T r)) ∧
    ExpDrift P 𝓕 π (fun r ω => ρ * π r ω - κ * (x r ω + trapStep g T r))

/-- Cochrane (2023), §20.2.2, p. 474 (tool): **from "almost surely at every date" to "almost every
path"**. If `Z` has continuous paths, `f` is continuous and `Z_t = f(t)` almost surely for every
`t ≥ T`, then almost every path has `Z_t = f(t)` for all `t ≥ T` (through the rational dates). -/
theorem ae_forall_Ici_of_forall_ae {Z : ℝ → Ω → ℝ} (hZ : ∀ ω, Continuous fun t => Z t ω)
    {f : ℝ → ℝ} (hf : Continuous f) {T : ℝ} (h : ∀ t, T ≤ t → Z t =ᵐ[P] fun _ => f t) :
    ∀ᵐ ω ∂P, ∀ t, T ≤ t → Z t ω = f t := by
  have hq : ∀ᵐ ω ∂P, ∀ q : ℚ, T < (q : ℝ) → Z q ω = f q := ae_all_iff.2 fun q => by
    by_cases hTq : T < (q : ℝ)
    · filter_upwards [h q hTq.le] with ω hω _
      exact hω
    · exact Eventually.of_forall fun _ h' => absurd h' hTq
  filter_upwards [hq] with ω hω t ht
  have hcl : IsClosed {r : ℝ | Z r ω = f r} := isClosed_eq (hZ ω) hf
  have hsub : Set.Ioi T ∩ Set.range ((↑) : ℚ → ℝ) ⊆ {r : ℝ | Z r ω = f r} := by
    rintro r ⟨hr, q, rfl⟩
    exact hω q hr
  have h1 : Set.Ioi T ⊆ {r : ℝ | Z r ω = f r} :=
    (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioi).trans
      (hcl.closure_subset_iff.2 hsub)
  have h2 : closure (Set.Ioi T) ⊆ {r : ℝ | Z r ω = f r} := hcl.closure_subset_iff.2 h1
  rw [closure_Ioi] at h2
  exact h2 ht

/-- Cochrane (2023), (20.5)–(20.7), p. 474 (tool): `E_t dZ = D dt` from `0` on gives it from
`T ≥ 0` on for any drift `D'` that agrees with `D` from `T` on. -/
theorem expDriftFrom_of_eq {𝓕 : Filtration ℝ mΩ} {Z D D' : ℝ → Ω → ℝ} (h : ExpDrift P 𝓕 Z D)
    {T : ℝ} (hT : 0 ≤ T) (hD : ∀ r ω, T ≤ r → D r ω = D' r ω) : ExpDriftFrom P 𝓕 T Z D' := by
  intro s t hs hst
  have e : (fun ω => Z t ω - Z s ω - ∫ r in s..t, D r ω) =
      fun ω => Z t ω - Z s ω - ∫ r in s..t, D' r ω := by
    funext ω
    congr 1
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le hst] at hr
    exact hD r ω (hs.trans hr.1)
  have h1 := h s t (hT.trans hs) hst
  rw [e] at h1
  exact h1

/-- Cochrane (2023), (20.5)–(20.7), p. 474 (tool): `E_t dZ = D dt` is unchanged when the drift is
changed on a null set of paths only. -/
theorem expDrift_of_ae_eq {𝓕 : Filtration ℝ mΩ} {Z D D' : ℝ → Ω → ℝ} (h : ExpDrift P 𝓕 Z D)
    (hD : ∀ᵐ ω ∂P, ∀ r, 0 ≤ r → D r ω = D' r ω) : ExpDrift P 𝓕 Z D' := by
  intro s t hs hst
  have e : (fun ω => Z t ω - Z s ω - ∫ r in s..t, D r ω) =ᵐ[P]
      fun ω => Z t ω - Z s ω - ∫ r in s..t, D' r ω := by
    filter_upwards [hD] with ω hω
    congr 1
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le hst] at hr
    exact hω r (hs.trans hr.1)
  obtain ⟨h1, h2⟩ := h s t hs hst
  exact ⟨h1.congr e, (condExp_congr_ae e.symm).trans h2⟩

/-- **Cochrane (2023), (20.7), p. 474, and pp. 475–476, under uncertainty: the active rule after
the trap selects a unique equilibrium of the whole model.** For `σ, κ, ρ > 0`, `φ > 1` and
`T ≥ 0`, every regular `L¹`-bounded equilibrium of the composed model (`IsActiveTrapEqm`) has
`π_t = wPi(c)_t` and `x_t = wX(c)_t` almost surely at every date `t ≥ 0`. After `T` this is
`TidyR7StochWerningSelect.active_rule_selects`; it pins `π_T = c` almost surely, and before `T`
the trap characterisation (`TidyR7StochWerningSelect.nk_selection`) then removes all
uncertainty. -/
theorem active_trap_selects [IsProbabilityMeasure P] {σ κ ρ φ T : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hρ : 0 < ρ) (hφ : 1 < φ) (hT : 0 ≤ T) {𝓕 : Filtration ℝ mΩ} {u g c : ℝ}
    {x π : ℝ → Ω → ℝ} (hx : Regular 𝓕 x) (hxb : BddL1 P x) (hπ : Regular 𝓕 π)
    (hπb : BddL1 P π) (h : IsActiveTrapEqm σ ρ κ φ P 𝓕 T u g c x π) {t : ℝ} (ht : 0 ≤ t) :
    π t =ᵐ[P] (fun _ => wPi σ κ ρ T u g c t) ∧ x t =ᵐ[P] (fun _ => wX σ κ ρ T u g c t) := by
  have hWc := wPi_continuous σ κ ρ T u g c hκ hσ
  have hXc := wX_continuous σ κ ρ T u g c hκ hσ
  -- after `T`: the active rule
  have hafter : ∀ t, T ≤ t →
      π t =ᵐ[P] (fun _ => wPi σ κ ρ T u g c t) ∧ x t =ᵐ[P] (fun _ => wX σ κ ρ T u g c t) :=
    fun t ht => active_rule_selects (istar := fun _ => 0) (u := trapStep u T)
      (g := trapStep g T) hσ hκ hρ hφ hT (fun a b => integrableOn_zero)
      (fun a b => trapStep_integrableOn u T measure_Ioc_lt_top.ne)
      (fun a b => trapStep_integrableOn g T measure_Ioc_lt_top.ne) hXc hWc
      (wPath_bdd (ρ := ρ) hκ hσ T u g c).1 (wPath_bdd (ρ := ρ) hκ hσ T u g c).2
      (fun s t hs hst => wPath_intForm (ρ := ρ) hκ hσ T u g c (hT.trans hs) hst)
      hx hxb hπ hπb
      (expDriftFrom_of_eq h.1 hT fun r ω hr => by
        simp only [ruleRate, not_lt.2 hr, ↓reduceIte, zero_add])
      (fun s t hs hst => h.2 s t (hT.trans hs) hst) ht
  -- almost every path follows the chosen path after `T`
  have hpath : ∀ᵐ ω ∂P, ∀ r, T ≤ r → π r ω = wPi σ κ ρ T u g c r :=
    ae_forall_Ici_of_forall_ae hπ.1 hWc fun r hr => (hafter r hr).1
  -- so the composed model is the trap model with `i = 0` throughout
  have htrap : IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep g T)
      (fun _ _ => 0) x π := by
    refine ⟨expDrift_of_ae_eq h.1 ?_, h.2⟩
    filter_upwards [hpath] with ω hω r _
    rcases lt_or_ge r T with hr | hr
    · simp [ruleRate, hr]
    · simp [ruleRate, not_lt.2 hr, hω r hr]
  have hcT : π T =ᵐ[P] fun _ => c := by
    filter_upwards [(hafter T le_rfl).1] with ω hω
    rw [hω, wPi_T hκ hσ]
  rcases le_total t T with htT | htT
  · exact nk_selection hσ hκ hx hxb hπ hπb htrap c hcT ht htT
  · exact hafter t htT

/-- Cochrane (2023), (20.7), p. 474, under uncertainty: **pathwise selection** — almost every
path of every regular `L¹`-bounded equilibrium of the composed model is the chosen path on all
of `[0, ∞)`. -/
theorem active_trap_selects_paths [IsProbabilityMeasure P] {σ κ ρ φ T : ℝ} (hσ : 0 < σ)
    (hκ : 0 < κ) (hρ : 0 < ρ) (hφ : 1 < φ) (hT : 0 ≤ T) {𝓕 : Filtration ℝ mΩ} {u g c : ℝ}
    {x π : ℝ → Ω → ℝ} (hx : Regular 𝓕 x) (hxb : BddL1 P x) (hπ : Regular 𝓕 π)
    (hπb : BddL1 P π) (h : IsActiveTrapEqm σ ρ κ φ P 𝓕 T u g c x π) :
    ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → π t ω = wPi σ κ ρ T u g c t ∧ x t ω = wX σ κ ρ T u g c t := by
  filter_upwards [ae_forall_Ici_of_forall_ae hπ.1 (wPi_continuous σ κ ρ T u g c hκ hσ)
      fun t ht => (active_trap_selects hσ hκ hρ hφ hT hx hxb hπ hπb h ht).1,
    ae_forall_Ici_of_forall_ae hx.1 (wX_continuous σ κ ρ T u g c hκ hσ)
      fun t ht => (active_trap_selects hσ hκ hρ hφ hT hx hxb hπ hπb h ht).2] with ω h1 h2 t ht
  exact ⟨h1 t ht, h2 t ht⟩

/-- **Cochrane (2023), (20.7), p. 474, under uncertainty: existence.** The chosen path
`(wX(c), wPi(c))`, as a deterministic process, is a regular, `L¹`-bounded equilibrium of the
composed model on every filtered probability space; along it the rule sets `i = 0`. -/
theorem active_trap_exists [IsProbabilityMeasure P] {σ κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (𝓕 : Filtration ℝ mΩ) (φ T u g c : ℝ) :
    IsActiveTrapEqm σ ρ κ φ P 𝓕 T u g c (fun t _ => wX σ κ ρ T u g c t)
        (fun t _ => wPi σ κ ρ T u g c t) ∧
      Regular 𝓕 (fun t (_ : Ω) => wX σ κ ρ T u g c t) ∧
      Regular 𝓕 (fun t (_ : Ω) => wPi σ κ ρ T u g c t) ∧
      BddL1 P (fun t (_ : Ω) => wX σ κ ρ T u g c t) ∧
      BddL1 P (fun t (_ : Ω) => wPi σ κ ρ T u g c t) := by
  have hrate : ∀ r (ω : Ω), ruleRate φ T (wPi σ κ ρ T u g c)
      (fun t _ => wPi σ κ ρ T u g c t) r ω = 0 := fun r ω => by
    unfold ruleRate
    split_ifs <;> simp
  obtain ⟨⟨KX, hKX⟩, ⟨KW, hKW⟩⟩ := wPath_bdd (ρ := ρ) hκ hσ T u g c
  refine ⟨⟨?_, ?_⟩, ⟨fun _ => wX_continuous σ κ ρ T u g c hκ hσ, fun _ =>
      stronglyMeasurable_const⟩, ⟨fun _ => wPi_continuous σ κ ρ T u g c hκ hσ, fun _ =>
      stronglyMeasurable_const⟩, ⟨KX, fun t ht => ⟨integrable_const _, by simpa using hKX t ht⟩⟩,
    ⟨KW, fun t ht => ⟨integrable_const _, by simpa using hKW t ht⟩⟩⟩
  · simp only [hrate]
    exact expDrift_det_iff.2 fun s t hs hst => (wPath_intForm (ρ := ρ) hκ hσ T u g c hs hst).1
  · exact expDrift_det_iff.2 fun s t hs hst => (wPath_intForm (ρ := ρ) hκ hσ T u g c hs hst).2

/-! ## Non-vacuity -/

open Cochrane.ZeroBound.TidyR7BrownianExist Cochrane.ZeroBound.TidyR7BrownianSchauder
open Cochrane.ZeroBound.TidyR7BrownianTools

/-- Cochrane (2023), (20.7), p. 474 (non-vacuity): at the book's calibration (`ρ = 0.05`,
`σ = κ = 1`, `T = 5`, `u_r = −2%`, `g = 0`), with `φ = 3/2` and the new-Keynesian target
`c = 0`, on the bmPath filtration: the chosen path is an equilibrium of the composed model, and
the Ornstein–Uhlenbeck process with unit loading (an `L²`-bounded equilibrium of the trap with
`i = 0` forever, `TidyR7StochWerningExist.isStochEqm_eq`) is not one. -/
theorem bmPath_active_trap :
    IsActiveTrapEqm 1 (1 / 20) 1 (3 / 2) gaussSeq (bmFiltrationReal bmPath measurable_bmPath) 5
        (-2 / 100) 0 0 (fun t _ => wX 1 1 (1 / 20) 5 (-2 / 100) 0 0 t)
        (fun t _ => wPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 t) ∧
      ¬ IsActiveTrapEqm 1 (1 / 20) 1 (3 / 2) gaussSeq (bmFiltrationReal bmPath measurable_bmPath)
        5 (-2 / 100) 0 0 (eqX 1 1 (1 / 20) 5 (-2 / 100) 0 0 1 bmPath)
        (eqPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 1 bmPath) := by
  have := isProbabilityMeasure_gaussSeq
  refine ⟨(active_trap_exists one_pos one_pos _ _ _ _ _ _).1, fun h => ?_⟩
  have hsel := fun t (ht : (0 : ℝ) ≤ t) => (active_trap_selects one_pos one_pos (by norm_num)
    (by norm_num) (by norm_num) (regular_eqX measurable_bmPath continuous_bmPath one_pos one_pos
      _ _ _ _ _) (bddL2_eqX isPreBrownianReal_bmPath measurable_bmPath continuous_bmPath
      bmPath_zero one_pos one_pos _ _ _ _ _).bddL1
    (regular_eqPi measurable_bmPath continuous_bmPath one_pos one_pos _ _ _ _ _)
    (bddL2_eqPi isPreBrownianReal_bmPath measurable_bmPath continuous_bmPath bmPath_zero one_pos
      one_pos _ _ _ _ _).bddL1 h ht).1
  have := (eqPi_inj isPreBrownianReal_bmPath measurable_bmPath continuous_bmPath bmPath_zero
    one_pos one_pos (πT := 0) (πT' := 0) (b := 0) (b' := 1) fun t ht => by
      filter_upwards [hsel t ht] with ω hω
      rw [hω]
      simp only [eqPi, TidyR7StochWerningExist.ouProc_loading _ 0, zero_mul, add_zero]).2
  norm_num at this

end Cochrane.ZeroBound.TidyR8StochWerningActiveTrap
