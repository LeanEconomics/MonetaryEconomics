/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.KingForm
import Mathlib.MeasureTheory.Measure.Map

/-!
# Identification of the new-Keynesian model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 16, §16.5 "Identification"
(pp. 370–372), §16.9 "Identification patches" (pp. 380–383) and §16.10.7 "Learning and other
selection devices" (pp. 394–395).

The simplest new-Keynesian model (16.1)–(16.2) is `i_t = E_t π_{t+1}`, `i_t = φ π_t + u_t`;
the new-Keynesian selection keeps the unique bounded ("locally bounded") solution of
(16.4) `E_t π_{t+1} = φ π_t + u_t`, which exists for `|φ| > 1`. The innovation operator and
shocks are those of `Innovation`, (16.4), its uniqueness lemma and the AR(1) path
`π = −u/(φ − η)` those of `SimplestModel` (`Eq164`, `eq164_unique`, `ar1Pi`, `ar1Pi_eq164`);
the equilibrium notions `NKEq`, `Selected`, `KingEq` and `FTPLEq` of this module are linked to
the `SimplestModel`, `KingForm` and `FTPLSimple` ones in `Links`.

Every result holds for an arbitrary `ExpectationSystem` (perfect foresight and genuine
uncertainty) and is **pathwise**: "observationally equivalent" means that the observable
processes are equal as functions `ℕ → Ω → ℝ`, which is stronger than equality of their laws
(`law_obs_eq`). Regression statements are finite-sample algebraic identities.

## Main results

* NI-1 (p. 371, reverse engineering): `reverse_nkEq`, `reverse_selected`: for every bounded
  adapted inflation process and EVERY `φ` with `|φ| > 1`, `u = i − φπ` makes it the selected
  equilibrium; `nk_fiber_eq` (the set of `φ` consistent with any data is all of `1 < |φ|`),
  `phi_not_identified`, `u_not_identified`. Conversely `u_eq_of_nkEq` (knowing `φ` gives `u`)
  and `phi_eq_of_same_u` (knowing `u` gives `φ`), as the book says.
* NI-2/NI-3, (16.9)–(16.11), (16.15)–(16.18): `ar1_selected`, `eq_16_10`, `eq_16_15`,
  `eq_16_16_innov`, `eq_16_18`, `ar1_obs`, `obs_selected_every_phi`, `ni2_same_iff`,
  `ni2_rescaled`.
* Finite-sample regressions: `olsNoInt_eq`, `olsSlope_eq`, `olsIntercept_eq_zero`,
  `ivEst_eq` (any instrument), `ni3_ols`, `ni3_ols_ne_phi`, `ni3_iv`, `ols_ar_eq`.
* NI-4, (16.19): `king_bounded_eq`, `king_eq_set`, `king_eq_set_indep`, `king_selection_zero`.
* §16.9: `thetaRule_eq_obs` (equilibrium data are `i = θπ + u`, free of `φ`),
  `iv_identifies_iff` (an instrument orthogonal to `u` measures `φ` iff `θ = φ`),
  `theta_eq_phi_no_shock_zero` (with `θ = φ`, `u = 0` the only bounded equilibrium is `π = 0`:
  identification needs other shocks), the real-rate-shock model `rr_iv_eq_phi_add` and
  `rr_iv_eq_phi_iff`, `rr_example` (a non-vacuous identified case).
* §16.10.7: `identified_iff_learnable`, `phi_not_learnable`, `ftpl_theta_identified`,
  `ftpl_theta_learnable`; `law_obs_eq` ("the likelihood does not involve `φ`").
-/

namespace Cochrane.NewKeynesianSelection.Identification

open Filter Topology
open Innovation (innov IsShock AR1Law innov_eq_sub_E isShock_smul)
open SimplestModel (Eq164 eq164_unique ar1Pi ar1Pi_eq164 ar1Pi_adapted ar1Pi_bounded)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The model -/

/-- Cochrane (2023), (16.1), p. 364: the interest rate implied by the Fisher equation,
`i_t = E_t π_{t+1}`. -/
def fisherRate (π : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := 𝔼.E t (π (t + 1))

/-- Cochrane (2023), (16.1)–(16.2), p. 364: `(π, i)` is an equilibrium of the simplest
new-Keynesian model with rule `i_t = φ π_t + u_t`: `π` adapted, `i_t = E_t π_{t+1}`,
`i_t = φ π_t + u_t`. -/
def NKEq (φ : ℝ) (u π i : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted π ∧ (∀ t, i t = 𝔼.E t (π (t + 1))) ∧ ∀ t, i t = φ • π t + u t

/-- Cochrane (2023), (16.4), p. 364: eliminating `i`, (16.1)–(16.2) hold iff (16.4) holds and
`i` is the Fisher rate. -/
theorem nkEq_iff (φ : ℝ) (u π i : ℕ → Ω → ℝ) :
    NKEq 𝔼 φ u π i ↔ 𝔼.Adapted π ∧ Eq164 𝔼 φ u π ∧ i = fisherRate 𝔼 π := by
  constructor
  · rintro ⟨ha, hf, hr⟩
    exact ⟨ha, fun t => (hf t).symm.trans (hr t), funext fun t => hf t⟩
  · rintro ⟨ha, h4, rfl⟩
    exact ⟨ha, fun t => rfl, fun t => h4 t⟩

/-- Cochrane (2023), (16.6), p. 364: the new-Keynesian selection. `π` is "the unique
locally-bounded equilibrium" given `(φ, u)`: it is bounded, adapted, solves (16.4), and every
bounded solution of (16.4) equals it. -/
def Selected (φ : ℝ) (u π : ℕ → Ω → ℝ) : Prop :=
  BoundedProc π ∧ 𝔼.Adapted π ∧ Eq164 𝔼 φ u π ∧
    ∀ π' : ℕ → Ω → ℝ, BoundedProc π' → Eq164 𝔼 φ u π' → π' = π

/-- Cochrane (2023), (16.6), p. 364: for `|φ| > 1` a bounded adapted solution of (16.4) is
the selected equilibrium. -/
theorem selected_of {φ : ℝ} (hφ : 1 < |φ|) {u π : ℕ → Ω → ℝ} (hb : BoundedProc π)
    (ha : 𝔼.Adapted π) (h : Eq164 𝔼 φ u π) : Selected 𝔼 φ u π :=
  ⟨hb, ha, h, fun _ hb' h' => eq164_unique 𝔼 hφ h' h hb' hb⟩

/-- Cochrane (2023), (16.6), p. 364: the selected equilibrium given `(φ, u)` is unique. -/
theorem selected_unique {φ : ℝ} {u π₁ π₂ : ℕ → Ω → ℝ} (h₁ : Selected 𝔼 φ u π₁)
    (h₂ : Selected 𝔼 φ u π₂) : π₁ = π₂ :=
  h₂.2.2.2 π₁ h₁.1 h₁.2.2.1

/-! ### NI-1: reverse engineering (p. 371) -/

/-- Cochrane (2023), p. 371: the reverse-engineered disturbance `u_t = i_t − φ π_t` with
`i_t = E_t π_{t+1}`. -/
def reverseU (φ : ℝ) (π : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := fisherRate 𝔼 π t - φ • π t

/-- Cochrane (2023), p. 371 ("Choose any process `{π_t}` … Choose any `φ`. Construct
`u_t = i_t − φπ_t`"): every adapted inflation process with `i_t = E_t π_{t+1}` is an equilibrium
of (16.1)–(16.2) for every `φ`. -/
theorem reverse_nkEq {π : ℕ → Ω → ℝ} (ha : 𝔼.Adapted π) (φ : ℝ) :
    NKEq 𝔼 φ (reverseU 𝔼 φ π) π (fisherRate 𝔼 π) :=
  ⟨ha, fun _ => rfl, fun t => by rw [reverseU]; abel⟩

/-- Cochrane (2023), p. 371: for every bounded adapted `π` and every `φ` with `|φ| > 1`, `π` is
the new-Keynesian selected (unique bounded) equilibrium of `(φ, u = i − φπ)`. -/
theorem reverse_selected {π : ℕ → Ω → ℝ} (ha : 𝔼.Adapted π) (hb : BoundedProc π) {φ : ℝ}
    (hφ : 1 < |φ|) : Selected 𝔼 φ (reverseU 𝔼 φ π) π :=
  selected_of 𝔼 hφ hb ha fun t => by
    change fisherRate 𝔼 π t = φ • π t + (fisherRate 𝔼 π t - φ • π t)
    abel

/-- Cochrane (2023), p. 371 ("observation of `π_t` and `i_t` cannot tell us `φ` and `u_t`"):
every bounded equilibrium of (16.1)–(16.2), whatever `(φ₀, u₀)` generated it, is the selected
equilibrium of `(φ, i − φπ)` for every `φ` with `|φ| > 1`. -/
theorem every_eq_selected {φ₀ : ℝ} {u₀ π i : ℕ → Ω → ℝ} (h : NKEq 𝔼 φ₀ u₀ π i)
    (hb : BoundedProc π) {φ : ℝ} (hφ : 1 < |φ|) :
    NKEq 𝔼 φ (fun t => i t - φ • π t) π i ∧ Selected 𝔼 φ (fun t => i t - φ • π t) π := by
  have hi : i = fisherRate 𝔼 π := ((nkEq_iff 𝔼 _ _ _ _).mp h).2.2
  subst hi
  exact ⟨reverse_nkEq 𝔼 h.1 φ, reverse_selected 𝔼 h.1 hb hφ⟩

/-- Cochrane (2023), p. 371 ("If you could observe the parameter `φ`, you could calculate
`u_t = i_t − φπ_t`"): given `φ`, the disturbance is determined by the data. -/
theorem u_eq_of_nkEq {φ : ℝ} {u π i : ℕ → Ω → ℝ} (h : NKEq 𝔼 φ u π i) (t : ℕ) :
    u t = i t - φ • π t := by
  rw [h.2.2 t]; abel

/-- Cochrane (2023), p. 371 ("If you could observe monetary policy disturbances `u_t` directly,
you could infer `φ`"): two values of `φ` with the same `u` and the same data agree as soon as
inflation is nonzero somewhere. -/
theorem phi_eq_of_same_u {φ₁ φ₂ : ℝ} {u π i : ℕ → Ω → ℝ} (h₁ : NKEq 𝔼 φ₁ u π i)
    (h₂ : NKEq 𝔼 φ₂ u π i) {t : ℕ} {ω : Ω} (hπ : π t ω ≠ 0) : φ₁ = φ₂ := by
  have e := congrFun ((h₁.2.2 t).symm.trans (h₂.2.2 t)) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_left_inj] at e
  exact mul_right_cancel₀ hπ e

/-- Cochrane (2023), p. 371: the reverse-engineered disturbances of two values of `φ` differ by
`(φ₂ − φ₁) π`, so the disturbance is not identified unless `π ≡ 0`. -/
theorem reverseU_sub (φ₁ φ₂ : ℝ) (π : ℕ → Ω → ℝ) (t : ℕ) :
    reverseU 𝔼 φ₁ π t - reverseU 𝔼 φ₂ π t = (φ₂ - φ₁) • π t := by
  simp only [reverseU, sub_smul]
  abel

/-! ### Identification and learnability as properties of a model class -/

/-- Cochrane (2023), §16.5, p. 370, and §16.10.7, p. 394: a parameter `par` is identified on
the set `S` of model specifications by the observation map `obs` if specifications in `S`
with the same observables have the same parameter. -/
def IdentifiedOn {M O P : Type*} (S : Set M) (obs : M → O) (par : M → P) : Prop :=
  ∀ m₁ ∈ S, ∀ m₂ ∈ S, obs m₁ = obs m₂ → par m₁ = par m₂

/-- Cochrane (2023), §16.10.7, p. 394 ("people in the economy cannot learn it any more than
econometricians can"): a parameter is identified iff some learning rule, a function of the
observables only, recovers it on the whole class. -/
theorem identified_iff_learnable {M O P : Type*} [Inhabited P] (S : Set M) (obs : M → O)
    (par : M → P) : IdentifiedOn S obs par ↔ ∃ L : O → P, ∀ m ∈ S, L (obs m) = par m := by
  classical
  constructor
  · intro h
    refine ⟨fun o => if hx : ∃ m ∈ S, obs m = o then par hx.choose else default,
      fun m hm => ?_⟩
    have hx : ∃ m' ∈ S, obs m' = obs m := ⟨m, hm, rfl⟩
    simp only [hx, ↓reduceDIte]
    exact h _ hx.choose_spec.1 m hm hx.choose_spec.2
  · rintro ⟨L, hL⟩ m₁ h₁ m₂ h₂ he
    rw [← hL m₁ h₁, ← hL m₂ h₂, he]

/-- Cochrane (2023), §16.5, p. 370: the class of new-Keynesian specifications `(φ, u, π)` with
`|φ| > 1` and `π` the selected equilibrium of `(φ, u)`. -/
def nkClass : Set (ℝ × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ)) :=
  {m | 1 < |m.1| ∧ Selected 𝔼 m.1 m.2.1 m.2.2}

/-- Cochrane (2023), §16.5, p. 371: what is observed of a specification, the processes
`(π, i)` with `i_t = E_t π_{t+1}`. -/
def nkObs (m : ℝ × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ)) : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) :=
  (m.2.2, fisherRate 𝔼 m.2.2)

/-- Cochrane (2023), p. 371 ("the observable dynamics are the same for any value of `φ`"): the
set of `φ` consistent with ANY observed equilibrium of the class is all of `{φ : 1 < |φ|}`. -/
theorem nk_fiber_eq {m : ℝ × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ)} (hm : m ∈ nkClass 𝔼) :
    {φ | ∃ m' ∈ nkClass 𝔼, nkObs 𝔼 m' = nkObs 𝔼 m ∧ m'.1 = φ} = {φ | 1 < |φ|} := by
  ext φ
  constructor
  · rintro ⟨m', hm', -, rfl⟩
    exact hm'.1
  · intro hφ
    exact ⟨(φ, reverseU 𝔼 φ m.2.2, m.2.2),
      ⟨hφ, reverse_selected 𝔼 hm.2.2.1 hm.2.1 hφ⟩, rfl, rfl⟩

/-- Cochrane (2023), p. 370 ("The parameter `φ` is not identified"): the zero process is the
selected equilibrium of `(φ, 0)` for every `|φ| > 1`. -/
theorem zero_selected {φ : ℝ} (hφ : 1 < |φ|) : Selected 𝔼 φ 0 0 :=
  selected_of 𝔼 hφ ⟨0, fun _ _ => by simp⟩ (fun t => by simp) fun t => by simp

/-- Cochrane (2023), §16.5, p. 370: `φ` is not identified from equilibrium time series. -/
theorem phi_not_identified : ¬ IdentifiedOn (nkClass 𝔼) (nkObs 𝔼) Prod.fst := by
  intro h
  have h2 : (2 : ℝ) ∈ {φ : ℝ | 1 < |φ|} := by norm_num
  have h3 : (3 : ℝ) ∈ {φ : ℝ | 1 < |φ|} := by norm_num
  have := h (2, 0, 0) ⟨h2, zero_selected 𝔼 h2⟩ (3, 0, 0) ⟨h3, zero_selected 𝔼 h3⟩ rfl
  norm_num at this

/-- Cochrane (2023), p. 371 ("The monetary-policy disturbances `u_t` are also not identified"):
whenever inflation is nonzero somewhere, the same data come from two different disturbance
processes. -/
theorem u_not_identified {π : ℕ → Ω → ℝ} (ha : 𝔼.Adapted π) (hb : BoundedProc π) {t : ℕ}
    {ω : Ω} (hπ : π t ω ≠ 0) :
    ∃ m₁ ∈ nkClass 𝔼, ∃ m₂ ∈ nkClass 𝔼, nkObs 𝔼 m₁ = nkObs 𝔼 m₂ ∧ m₁.2.1 ≠ m₂.2.1 := by
  have h2 : 1 < |(2 : ℝ)| := by norm_num
  have h3 : 1 < |(3 : ℝ)| := by norm_num
  refine ⟨(2, reverseU 𝔼 2 π, π), ⟨h2, reverse_selected 𝔼 ha hb h2⟩,
    (3, reverseU 𝔼 3 π, π), ⟨h3, reverse_selected 𝔼 ha hb h3⟩, rfl, fun he => hπ ?_⟩
  have e := congrFun (reverseU_sub 𝔼 2 3 π t) ω
  have e2 : reverseU 𝔼 2 π t ω = reverseU 𝔼 3 π t ω := by
    rw [show reverseU 𝔼 2 π = reverseU 𝔼 3 π from he]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e2, sub_self] at e
  linarith

/-- Cochrane (2023), §16.10.7, p. 394 ("the parameter `φ` … not identified … People in the
economy cannot learn it"): no learning rule, i.e. no function of the observed equilibrium
processes, recovers `φ` on the new-Keynesian class. -/
theorem phi_not_learnable :
    ¬ ∃ L : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) → ℝ, ∀ m ∈ nkClass 𝔼, L (nkObs 𝔼 m) = m.1 := by
  rw [← identified_iff_learnable]
  exact phi_not_identified 𝔼

/-- Cochrane (2023), p. 371 ("The likelihood function does not involve `φ`"): for any
probability model on `Ω` and any measurable structure on the observation space, the law of the
observables generated by `(φ₁, i − φ₁π)` and by `(φ₂, i − φ₂π)` is the same. -/
theorem law_obs_eq [MeasurableSpace Ω] (mO : MeasurableSpace (ℕ → ℝ × ℝ))
    (μ : MeasureTheory.Measure Ω) {m₁ m₂ : ℝ × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ)}
    (he : nkObs 𝔼 m₁ = nkObs 𝔼 m₂) :
    μ.map (fun ω t => ((nkObs 𝔼 m₁).1 t ω, (nkObs 𝔼 m₁).2 t ω)) =
      μ.map (fun ω t => ((nkObs 𝔼 m₂).1 t ω, (nkObs 𝔼 m₂).2 t ω)) := by
  rw [he]

/-! ### The AR(1) disturbance: (16.9)–(16.11), (16.15)–(16.18) -/

/-- Cochrane (2023), p. 365: the AR(1) disturbance `u_{t+1} = η u_t + ε_{i,t+1}`: `u` adapted,
`ε` a shock (`Innovation.IsShock`) and the law of motion `Innovation.AR1Law`. -/
def AR1 (η : ℝ) (u ε : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted u ∧ IsShock 𝔼 ε ∧ AR1Law η u ε

/-- Cochrane (2023), p. 365: an AR(1) disturbance has `E_t u_{t+1} = η u_t`. -/
theorem AR1.E_succ {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (t : ℕ) :
    𝔼.E t (u (t + 1)) = η • u t := by
  rw [h.2.2 t, map_add, map_smul, h.1 t, h.2.1.2 t, add_zero]

/-- Cochrane (2023), p. 365: an AR(1) disturbance is `IsAR1 η` in the sense of the core. -/
theorem AR1.isAR1 {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) : 𝔼.IsAR1 η u :=
  ⟨h.1, h.E_succ 𝔼⟩

/-- Cochrane (2023), (16.6) and (16.9), p. 365: for `|φ| > 1`, `φ ≠ η` and a bounded AR(1)
disturbance, `π_t = −u_t/(φ − η)` is the selected equilibrium. -/
theorem ar1_selected {φ η : ℝ} (hφ : 1 < |φ|) (hφη : φ ≠ η) {u ε : ℕ → Ω → ℝ}
    (h : AR1 𝔼 η u ε) (hub : BoundedProc u) : Selected 𝔼 φ u (ar1Pi φ η u) := by
  obtain ⟨M, hM⟩ := hub
  exact selected_of 𝔼 hφ (ar1Pi_bounded φ η hM) (ar1Pi_adapted 𝔼 φ η h.1)
    (ar1Pi_eq164 𝔼 hφη (h.isAR1 𝔼))

/-- Cochrane (2023), (16.10), p. 365: `π_{t+1} = η π_t − ε_{i,t+1}/(φ − η)`. -/
theorem eq_16_10 (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (t : ℕ) :
    ar1Pi φ η u (t + 1) = η • ar1Pi φ η u t + (-(φ - η)⁻¹) • ε (t + 1) :=
  SimplestModel.ar1_law_1610 h.2.2 t

/-- Cochrane (2023), (16.11) and (16.15), p. 365 and p. 371: in the selected equilibrium
`i_t = E_t π_{t+1} = −η u_t/(φ − η) = η π_t`, with no error. -/
theorem eq_16_15 (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (t : ℕ) :
    fisherRate 𝔼 (ar1Pi φ η u) t = η • ar1Pi φ η u t ∧
      fisherRate 𝔼 (ar1Pi φ η u) t = (-(η * (φ - η)⁻¹)) • u t := by
  have e : fisherRate 𝔼 (ar1Pi φ η u) t = η • ar1Pi φ η u t := by
    simp only [fisherRate, ar1Pi, map_smul, h.E_succ 𝔼 t, smul_smul, mul_comm]
  refine ⟨e, ?_⟩
  rw [e]
  simp only [ar1Pi, smul_smul]
  congr 1
  ring

/-- Cochrane (2023), (16.16), p. 371: the inflation innovation is
`ε_{π,t+1} = ΔE_{t+1} π_{t+1} = −ε_{i,t+1}/(φ − η)`. -/
theorem eq_16_16_innov (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (t : ℕ) :
    innov 𝔼 t (ar1Pi φ η u (t + 1)) = (-(φ - η)⁻¹) • ε (t + 1) := by
  rw [innov_eq_sub_E 𝔼 (ar1Pi_adapted 𝔼 φ η h.1 (t + 1)), ← fisherRate, (eq_16_15 𝔼 φ h t).1,
    eq_16_10 𝔼 φ h t]
  abel

/-- Cochrane (2023), (16.3) and (16.18), pp. 364, 371: with the passive fiscal response
`ε_{Σs,t+1} = −ΔE_{t+1} π_{t+1}`, `ε_{π,t+1} = −ε_{Σs,t+1}` and
`ε_{Σs,t+1} = ε_{i,t+1}/(φ − η)`. -/
theorem eq_16_18 (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (t : ℕ) :
    innov 𝔼 t (ar1Pi φ η u (t + 1)) = -(-innov 𝔼 t (ar1Pi φ η u (t + 1))) ∧
      -innov 𝔼 t (ar1Pi φ η u (t + 1)) = (φ - η)⁻¹ • ε (t + 1) := by
  refine ⟨(neg_neg _).symm, ?_⟩
  rw [eq_16_16_innov 𝔼 φ h t, neg_smul, neg_neg]

/-- Cochrane (2023), (16.16)–(16.17), p. 371: the observable system. `π` is adapted,
`π_{t+1} = η π_t + ε_{π,t+1}` with `ε_π` a shock, and `i_t = η π_t`. -/
def ObsAR1 (η : ℝ) (π i επ : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted π ∧ IsShock 𝔼 επ ∧ (∀ t, π (t + 1) = η • π t + επ (t + 1)) ∧ ∀ t, i t = η • π t

/-- Cochrane (2023), (16.16)–(16.18), p. 371 ("all we observe of the model"): the selected
AR(1) equilibrium obeys the observable system with persistence `η` and inflation shock
`ε_π = −ε_i/(φ − η)`; `φ` enters only through the scale of the shock. -/
theorem ar1_obs (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) :
    ObsAR1 𝔼 η (ar1Pi φ η u) (fisherRate 𝔼 (ar1Pi φ η u))
      (fun t => (-(φ - η)⁻¹) • ε t) := by
  exact ⟨ar1Pi_adapted 𝔼 φ η h.1, isShock_smul 𝔼 h.2.1 _, eq_16_10 𝔼 φ h,
    fun t => (eq_16_15 𝔼 φ h t).1⟩

/-- Cochrane (2023), p. 371 ("The observable `{i_t, π_t, s_t}` dynamics are the same for any
value of `φ`"): conversely, any bounded process obeying the observable system (16.16)–(16.17)
is, for EVERY `φ` with `|φ| > 1` and `φ ≠ η`, the selected equilibrium of the AR(1) model with
disturbance `u = −(φ − η) π` and shock `ε_i = −(φ − η) ε_π`. -/
theorem obs_selected_every_phi {η : ℝ} {π i επ : ℕ → Ω → ℝ} (h : ObsAR1 𝔼 η π i επ)
    (hb : BoundedProc π) {φ : ℝ} (hφ : 1 < |φ|) (hφη : φ ≠ η) :
    AR1 𝔼 η (fun t => (-(φ - η)) • π t) (fun t => (-(φ - η)) • επ t) ∧
      ar1Pi φ η (fun t => (-(φ - η)) • π t) = π ∧
      Selected 𝔼 φ (fun t => (-(φ - η)) • π t) π ∧ i = fisherRate 𝔼 π := by
  have hne : φ - η ≠ 0 := sub_ne_zero.mpr hφη
  obtain ⟨ha, ⟨hεa, hε0⟩, hπ, hi⟩ := h
  have har : AR1 𝔼 η (fun t => (-(φ - η)) • π t) (fun t => (-(φ - η)) • επ t) :=
    ⟨fun s => by simp only [map_smul, ha s], ⟨fun s => by simp only [map_smul, hεa s],
      fun s => by simp only [map_smul, hε0 s, smul_zero]⟩,
      fun t => by simp only [hπ t, smul_add, smul_smul, mul_comm]⟩
  have hpi : ar1Pi φ η (fun t => (-(φ - η)) • π t) = π := by
    funext t
    simp only [ar1Pi, smul_smul]
    rw [show -(φ - η)⁻¹ * -(φ - η) = 1 by field_simp, one_smul]
  have hEπ : ∀ t, 𝔼.E t (π (t + 1)) = η • π t := fun t => by
    rw [hπ t, map_add, map_smul, ha t, hε0 t, add_zero]
  obtain ⟨M, hM⟩ := hb
  have hub : BoundedProc (fun t => (-(φ - η)) • π t) :=
    ⟨|φ - η| * M, fun t ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)⟩
  refine ⟨har, hpi, ?_, funext fun t => (hi t).trans (hEπ t).symm⟩
  have hs := ar1_selected 𝔼 hφ hφη har hub
  rwa [hpi] at hs

/-- Cochrane (2023), pp. 370–371 (NI-2): with the same `η`, the selected equilibria of
`(φ, u)` and `(φ', u')` coincide iff `u/(φ − η) = u'/(φ' − η)`; `φ` and the disturbance enter
only through this ratio. -/
theorem ni2_same_iff (φ φ' η : ℝ) (u u' : ℕ → Ω → ℝ) :
    ar1Pi φ η u = ar1Pi φ' η u' ↔
      (fun t => (φ - η)⁻¹ • u t) = fun t => (φ' - η)⁻¹ • u' t := by
  constructor
  · intro h
    funext t
    have := congrFun h t
    simp only [ar1Pi, neg_smul] at this
    exact neg_inj.mp this
  · intro h
    funext t
    have := congrFun h t
    simp only [ar1Pi, neg_smul, this]

/-- Cochrane (2023), pp. 370–371 (NI-2): rescaling the disturbance (and so its shock
`ε' = ε (φ' − η)/(φ − η)`) by `(φ' − η)/(φ − η)` leaves the selected equilibrium unchanged. -/
theorem ni2_rescaled {φ φ' η : ℝ} (hφη : φ ≠ η) (hφη' : φ' ≠ η) (u : ℕ → Ω → ℝ) :
    ar1Pi φ' η (fun t => ((φ' - η) / (φ - η)) • u t) = ar1Pi φ η u := by
  have hne : φ - η ≠ 0 := sub_ne_zero.mpr hφη
  have hne' : φ' - η ≠ 0 := sub_ne_zero.mpr hφη'
  funext t
  simp only [ar1Pi, smul_smul]
  congr 1
  field_simp

/-! ### Finite-sample regressions -/

/-- Cochrane (2023), (16.15), p. 371: the OLS coefficient of `y` on `x` without intercept on
the sample `t = 0, …, T − 1`, `∑ x y / ∑ x²`. -/
noncomputable def olsNoInt (x y : ℕ → ℝ) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, x t * y t) / ∑ t ∈ Finset.range T, x t ^ 2

/-- Cochrane (2023), p. 371: the sample mean on `t = 0, …, T − 1`. -/
noncomputable def sampleMean (x : ℕ → ℝ) (T : ℕ) : ℝ := (∑ t ∈ Finset.range T, x t) / T

/-- Cochrane (2023), (16.15), p. 371: the OLS slope of `y` on `x` with an intercept,
`∑ (x − x̄)(y − ȳ) / ∑ (x − x̄)²`. -/
noncomputable def olsSlope (x y : ℕ → ℝ) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, (x t - sampleMean x T) * (y t - sampleMean y T)) /
    ∑ t ∈ Finset.range T, (x t - sampleMean x T) ^ 2

/-- Cochrane (2023), (16.15), p. 371: the OLS intercept `ȳ − b x̄`. -/
noncomputable def olsIntercept (x y : ℕ → ℝ) (T : ℕ) : ℝ :=
  sampleMean y T - olsSlope x y T * sampleMean x T

/-- Cochrane (2023), p. 371 ("No instrument can help") and p. 382: the instrumental-variables
estimate with instrument `z`, `∑ z y / ∑ z x`. -/
noncomputable def ivEst (z x y : ℕ → ℝ) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, z t * y t) / ∑ t ∈ Finset.range T, z t * x t

/-- Cochrane (2023), (16.15), p. 371: if `y_t = η x_t` on the sample and `∑ x² ≠ 0`, the OLS
coefficient without intercept is exactly `η`. -/
theorem olsNoInt_eq {x y : ℕ → ℝ} {η : ℝ} {T : ℕ} (h : ∀ t < T, y t = η * x t)
    (hx : ∑ t ∈ Finset.range T, x t ^ 2 ≠ 0) : olsNoInt x y T = η := by
  have e : ∑ t ∈ Finset.range T, x t * y t = η * ∑ t ∈ Finset.range T, x t ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [h t (Finset.mem_range.mp ht)]
    ring
  rw [olsNoInt, e, mul_div_assoc, div_self hx, mul_one]

/-- Cochrane (2023), (16.15), p. 371: if `y_t = η x_t` on the sample, `ȳ = η x̄`. -/
theorem sampleMean_eq {x y : ℕ → ℝ} {η : ℝ} {T : ℕ} (h : ∀ t < T, y t = η * x t) :
    sampleMean y T = η * sampleMean x T := by
  have e : ∑ t ∈ Finset.range T, y t = η * ∑ t ∈ Finset.range T, x t := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t ht => h t (Finset.mem_range.mp ht)
  rw [sampleMean, sampleMean, e, mul_div_assoc]

/-- Cochrane (2023), (16.15), p. 371: if `y_t = η x_t` on the sample and the sample variance of
`x` is positive, the OLS slope with intercept is exactly `η`. -/
theorem olsSlope_eq {x y : ℕ → ℝ} {η : ℝ} {T : ℕ} (h : ∀ t < T, y t = η * x t)
    (hx : ∑ t ∈ Finset.range T, (x t - sampleMean x T) ^ 2 ≠ 0) : olsSlope x y T = η := by
  have e : ∑ t ∈ Finset.range T, (x t - sampleMean x T) * (y t - sampleMean y T) =
      η * ∑ t ∈ Finset.range T, (x t - sampleMean x T) ^ 2 := by
    rw [Finset.mul_sum, sampleMean_eq h]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [h t (Finset.mem_range.mp ht)]
    ring
  rw [olsSlope, e, mul_div_assoc, div_self hx, mul_one]

/-- Cochrane (2023), (16.15), p. 371 ("with no error"): if `y_t = η x_t` on the sample, the OLS
intercept is zero. -/
theorem olsIntercept_eq_zero {x y : ℕ → ℝ} {η : ℝ} {T : ℕ} (h : ∀ t < T, y t = η * x t)
    (hx : ∑ t ∈ Finset.range T, (x t - sampleMean x T) ^ 2 ≠ 0) : olsIntercept x y T = 0 := by
  rw [olsIntercept, olsSlope_eq h hx, sampleMean_eq h, sub_self]

/-- Cochrane (2023), p. 382: if `y_t = b x_t + e_t` on the sample, the IV estimate is
`b + ∑ z e / ∑ z x`. -/
theorem ivEst_eq_add {z x y e : ℕ → ℝ} {b : ℝ} {T : ℕ} (h : ∀ t < T, y t = b * x t + e t)
    (hzx : ∑ t ∈ Finset.range T, z t * x t ≠ 0) :
    ivEst z x y T = b + (∑ t ∈ Finset.range T, z t * e t) / ∑ t ∈ Finset.range T, z t * x t := by
  have e1 : ∑ t ∈ Finset.range T, z t * y t =
      b * ∑ t ∈ Finset.range T, z t * x t + ∑ t ∈ Finset.range T, z t * e t := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [h t (Finset.mem_range.mp ht)]
    ring
  rw [ivEst, e1, add_div, mul_div_assoc, div_self hzx, mul_one]

/-- Cochrane (2023), p. 371 ("No instrument can help"): if `y_t = η x_t` on the sample, every
instrument with `∑ z x ≠ 0` gives exactly `η`. -/
theorem ivEst_eq {z x y : ℕ → ℝ} {η : ℝ} {T : ℕ} (h : ∀ t < T, y t = η * x t)
    (hzx : ∑ t ∈ Finset.range T, z t * x t ≠ 0) : ivEst z x y T = η := by
  rw [ivEst_eq_add (e := 0) (fun t ht => by rw [h t ht, Pi.zero_apply, add_zero]) hzx]
  simp

/-- Cochrane (2023), (16.15), p. 371 ("A regression of `i_t` on `π_t` in data from this model
produces `η` not `φ`"): in the selected AR(1) equilibrium, along every history `ω` and on every
sample with `∑ π² ≠ 0`, OLS of `i` on `π` gives exactly `η`, for every `φ`. -/
theorem ni3_ols (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (ω : Ω) {T : ℕ}
    (hx : ∑ t ∈ Finset.range T, ar1Pi φ η u t ω ^ 2 ≠ 0) :
    olsNoInt (fun t => ar1Pi φ η u t ω) (fun t => fisherRate 𝔼 (ar1Pi φ η u) t ω) T = η :=
  olsNoInt_eq (fun t _ => by
    simp only [(eq_16_15 𝔼 φ h t).1, Pi.smul_apply, smul_eq_mul]) hx

/-- Cochrane (2023), (16.15), p. 371: the same holds for OLS with an intercept. -/
theorem ni3_ols_slope (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (ω : Ω) {T : ℕ}
    (hx : ∑ t ∈ Finset.range T, (ar1Pi φ η u t ω - sampleMean (fun t => ar1Pi φ η u t ω) T) ^ 2
      ≠ 0) :
    olsSlope (fun t => ar1Pi φ η u t ω) (fun t => fisherRate 𝔼 (ar1Pi φ η u) t ω) T = η :=
  olsSlope_eq (fun t _ => by
    simp only [(eq_16_15 𝔼 φ h t).1, Pi.smul_apply, smul_eq_mul]) hx

/-- Cochrane (2023), p. 371: so the regression does not measure `φ` whenever `φ ≠ η`. -/
theorem ni3_ols_ne_phi {φ η : ℝ} (hφη : φ ≠ η) {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (ω : Ω)
    {T : ℕ} (hx : ∑ t ∈ Finset.range T, ar1Pi φ η u t ω ^ 2 ≠ 0) :
    olsNoInt (fun t => ar1Pi φ η u t ω) (fun t => fisherRate 𝔼 (ar1Pi φ η u) t ω) T ≠ φ := by
  rw [ni3_ols 𝔼 φ h ω hx]
  exact Ne.symm hφη

/-- Cochrane (2023), p. 371 ("No instrument can help"): every instrument gives `η`. -/
theorem ni3_iv (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (ω : Ω) (z : ℕ → ℝ)
    {T : ℕ} (hzx : ∑ t ∈ Finset.range T, z t * ar1Pi φ η u t ω ≠ 0) :
    ivEst z (fun t => ar1Pi φ η u t ω) (fun t => fisherRate 𝔼 (ar1Pi φ η u) t ω) T = η :=
  ivEst_eq (fun t _ => by
    simp only [(eq_16_15 𝔼 φ h t).1, Pi.smul_apply, smul_eq_mul]) hzx

/-- Cochrane (2023), (16.16), p. 371: the autoregression of observed inflation is the
finite-sample identity `b = η + ∑ π_t ε_{π,t+1} / ∑ π_t²`, which involves only observables. -/
theorem ols_ar_eq {η : ℝ} {π i επ : ℕ → Ω → ℝ} (h : ObsAR1 𝔼 η π i επ) (ω : Ω) {T : ℕ}
    (hx : ∑ t ∈ Finset.range T, π t ω ^ 2 ≠ 0) :
    olsNoInt (fun t => π t ω) (fun t => π (t + 1) ω) T =
      η + (∑ t ∈ Finset.range T, π t ω * επ (t + 1) ω) / ∑ t ∈ Finset.range T, π t ω ^ 2 := by
  have hsq : ∀ t, π t ω ^ 2 = π t ω * π t ω := fun t => sq _
  have e := ivEst_eq_add (z := fun t => π t ω) (x := fun t => π t ω)
    (y := fun t => π (t + 1) ω) (e := fun t => επ (t + 1) ω) (b := η) (T := T)
    (fun t _ => by simp only [h.2.2.1 t, Pi.add_apply, Pi.smul_apply, smul_eq_mul])
    (by simpa only [hsq] using hx)
  simp only [ivEst, ← hsq] at e
  exact e

/-! ### NI-4: the King form (16.12)/(16.19) -/

/-- Cochrane (2023), (16.1) and (16.12)/(16.19), pp. 366, 371: `(π, i)` is an equilibrium with
the rule `i_t = i*_t + φ(π_t − π*_t)`. -/
def KingEq (φ : ℝ) (istar pistar π i : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted π ∧ (∀ t, i t = 𝔼.E t (π (t + 1))) ∧ ∀ t, i t = istar t + φ • (π t - pistar t)

/-- Cochrane (2023), p. 366: the targets respect private-sector equilibrium,
`i*_t = E_t π*_{t+1}`, with `π*` adapted. -/
def TargetsConsistent (istar pistar : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted pistar ∧ ∀ t, istar t = 𝔼.E t (pistar (t + 1))

/-- Cochrane (2023), (16.19), p. 371: the targets themselves are an equilibrium for every `φ`. -/
theorem king_target_eq (φ : ℝ) {istar pistar : ℕ → Ω → ℝ}
    (hc : TargetsConsistent 𝔼 istar pistar) : KingEq 𝔼 φ istar pistar pistar istar :=
  ⟨hc.1, hc.2, fun t => by simp⟩

/-- Cochrane (2023), (16.14) and (16.19), pp. 367, 371: for `|φ| > 1` and bounded targets, the
only bounded equilibrium is `π = π*`, `i = i*`. -/
theorem king_bounded_eq {φ : ℝ} (hφ : 1 < |φ|) {istar pistar π i : ℕ → Ω → ℝ}
    (hc : TargetsConsistent 𝔼 istar pistar) (hbs : BoundedProc pistar)
    (h : KingEq 𝔼 φ istar pistar π i) (hb : BoundedProc π) : π = pistar ∧ i = istar := by
  have hd : Eq164 𝔼 φ 0 (fun t => π t - pistar t) := fun t => by
    rw [map_sub, ← h.2.1 t, ← hc.2 t, h.2.2 t, Pi.zero_apply, add_zero]
    abel
  have hz : Eq164 𝔼 φ 0 (fun _ => 0) := fun t => by simp
  obtain ⟨M, hM⟩ := hb
  obtain ⟨Ms, hMs⟩ := hbs
  have hdb : BoundedProc (fun t => π t - pistar t) :=
    ⟨M + Ms, fun t ω => (abs_sub _ _).trans (add_le_add (hM t ω) (hMs t ω))⟩
  have h0 := eq164_unique 𝔼 hφ hd hz hdb ⟨0, fun _ _ => by simp⟩
  have hπ : π = pistar := funext fun t => sub_eq_zero.mp (congrFun h0 t)
  refine ⟨hπ, funext fun t => ?_⟩
  rw [h.2.2 t, hπ, sub_self, smul_zero, add_zero]

/-- Cochrane (2023), (16.19), p. 371 ("In equilibrium `π_t = π*_t`, so there is no variation on
the right-hand side with which to measure `φ`"): the selection term vanishes identically. -/
theorem king_selection_zero {φ : ℝ} (hφ : 1 < |φ|) {istar pistar π i : ℕ → Ω → ℝ}
    (hc : TargetsConsistent 𝔼 istar pistar) (hbs : BoundedProc pistar)
    (h : KingEq 𝔼 φ istar pistar π i) (hb : BoundedProc π) (t : ℕ) :
    φ • (π t - pistar t) = 0 := by
  rw [(king_bounded_eq 𝔼 hφ hc hbs h hb).1, sub_self, smul_zero]

/-- Cochrane (2023), (16.19), p. 371 (NI-4): for `|φ| > 1` the set of bounded equilibria is
exactly `{(π*, i*)}`. -/
theorem king_eq_set {φ : ℝ} (hφ : 1 < |φ|) {istar pistar : ℕ → Ω → ℝ}
    (hc : TargetsConsistent 𝔼 istar pistar) (hbs : BoundedProc pistar) :
    {p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) | KingEq 𝔼 φ istar pistar p.1 p.2 ∧ BoundedProc p.1} =
      {(pistar, istar)} := by
  ext ⟨π, i⟩
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨h, hb⟩
    exact king_bounded_eq 𝔼 hφ hc hbs h hb
  · rintro ⟨rfl, rfl⟩
    exact ⟨king_target_eq 𝔼 φ hc, hbs⟩

/-- Cochrane (2023), (16.19), p. 371 (NI-4): the set of bounded equilibria is the same for
every pair of values `|φ₁|, |φ₂| > 1`; `φ` is not identified. -/
theorem king_eq_set_indep {φ₁ φ₂ : ℝ} (h₁ : 1 < |φ₁|) (h₂ : 1 < |φ₂|)
    {istar pistar : ℕ → Ω → ℝ} (hc : TargetsConsistent 𝔼 istar pistar)
    (hbs : BoundedProc pistar) :
    {p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) | KingEq 𝔼 φ₁ istar pistar p.1 p.2 ∧ BoundedProc p.1} =
      {p | KingEq 𝔼 φ₂ istar pistar p.1 p.2 ∧ BoundedProc p.1} := by
  rw [king_eq_set 𝔼 h₁ hc hbs, king_eq_set 𝔼 h₂ hc hbs]

/-! ### §16.9 Identification patches -/

/-- Cochrane (2023), p. 382: equilibrium with the rule `i_t = θπ*_t + φ(π_t − π*_t) + u_t`. -/
def ThetaEq (θ φ : ℝ) (u pistar π i : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted π ∧ (∀ t, i t = 𝔼.E t (π (t + 1))) ∧
    ∀ t, i t = θ • pistar t + φ • (π t - pistar t) + u t

/-- Cochrane (2023), p. 382: the interest-rate policy `i*_t = θπ*_t + u_t` respects
`i*_t = E_t π*_{t+1}`. -/
def ThetaConsistent (θ : ℝ) (u pistar : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted pistar ∧ ∀ t, 𝔼.E t (pistar (t + 1)) = θ • pistar t + u t

/-- Cochrane (2023), pp. 367, 382: the θ-rule is the King rule with `i*_t = θπ*_t + u_t`. -/
theorem thetaEq_iff_king (θ φ : ℝ) (u pistar π i : ℕ → Ω → ℝ) :
    ThetaEq 𝔼 θ φ u pistar π i ↔
      KingEq 𝔼 φ (fun t => θ • pistar t + u t) pistar π i := by
  unfold ThetaEq KingEq
  refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun t => ?_
  rw [add_right_comm]

/-- Cochrane (2023), p. 382: for every `φ` the target is an equilibrium of the θ-rule. -/
theorem thetaEq_target (φ : ℝ) {θ : ℝ} {u pistar : ℕ → Ω → ℝ}
    (hc : ThetaConsistent 𝔼 θ u pistar) :
    ThetaEq 𝔼 θ φ u pistar pistar (fun t => θ • pistar t + u t) :=
  (thetaEq_iff_king 𝔼 _ _ _ _ _ _).mpr
    (king_target_eq 𝔼 φ ⟨hc.1, fun t => (hc.2 t).symm⟩)

/-- Cochrane (2023), p. 382: for `|φ| > 1` the bounded equilibrium of the θ-rule is `π = π*`
and the observed data obey `i_t = θ π_t + u_t`; `φ` does not appear. -/
theorem thetaRule_eq_obs {θ φ : ℝ} (hφ : 1 < |φ|) {u pistar π i : ℕ → Ω → ℝ}
    (hc : ThetaConsistent 𝔼 θ u pistar) (hbs : BoundedProc pistar)
    (h : ThetaEq 𝔼 θ φ u pistar π i) (hb : BoundedProc π) :
    π = pistar ∧ ∀ t, i t = θ • π t + u t := by
  obtain ⟨hπ, hi⟩ := king_bounded_eq 𝔼 hφ ⟨hc.1, fun t => (hc.2 t).symm⟩ hbs
    ((thetaEq_iff_king 𝔼 _ _ _ _ _ _).mp h) hb
  exact ⟨hπ, fun t => by rw [hi, hπ]⟩

/-- Cochrane (2023), p. 382 ("the identifying assumptions that let us measure `φ` start with
`θ = φ`"): in the bounded equilibrium of the θ-rule, an instrument `z` orthogonal to `u` in the
sample (`∑ z u = 0`, `∑ z π ≠ 0`) measures `θ`; it measures `φ` if and only if `θ = φ`. -/
theorem iv_identifies_iff {θ φ : ℝ} (hφ : 1 < |φ|) {u pistar π i : ℕ → Ω → ℝ}
    (hc : ThetaConsistent 𝔼 θ u pistar) (hbs : BoundedProc pistar)
    (h : ThetaEq 𝔼 θ φ u pistar π i) (hb : BoundedProc π) (ω : Ω) (z : ℕ → ℝ) {T : ℕ}
    (hzu : ∑ t ∈ Finset.range T, z t * u t ω = 0)
    (hzx : ∑ t ∈ Finset.range T, z t * π t ω ≠ 0) :
    ivEst z (fun t => π t ω) (fun t => i t ω) T = θ ∧
      (ivEst z (fun t => π t ω) (fun t => i t ω) T = φ ↔ θ = φ) := by
  have hi := (thetaRule_eq_obs 𝔼 hφ hc hbs h hb).2
  have e := ivEst_eq_add (z := z) (x := fun t => π t ω) (y := fun t => i t ω)
    (e := fun t => u t ω) (b := θ) (fun t _ => by
    simp only [hi t, Pi.add_apply, Pi.smul_apply, smul_eq_mul]) hzx
  rw [hzu, zero_div, add_zero] at e
  exact ⟨e, by rw [e]⟩

/-- Cochrane (2023), p. 382 ("φ is also identified if there is no disturbance … and if there
are shocks to other equations"): in the simplest model, with `θ = φ`, `u = 0` and `|φ| > 1`, the
only bounded target is `π* = 0`; the equilibrium data are identically zero, so identification
needs shocks from other equations. -/
theorem theta_eq_phi_no_shock_zero {φ : ℝ} (hφ : 1 < |φ|) {pistar : ℕ → Ω → ℝ}
    (hc : ThetaConsistent 𝔼 φ 0 pistar) (hbs : BoundedProc pistar) : pistar = 0 :=
  eq164_unique 𝔼 hφ (u := 0) (fun t => hc.2 t) (fun t => by simp) hbs
    ⟨0, fun _ _ => by simp⟩

/-- Cochrane (2023), p. 382: an equilibrium of the model with a real-rate shock in the Fisher
equation, `i_t = r_t + E_t π_{t+1}`, and the rule `i_t = φ π_t + u_t`. -/
def RREq (φ : ℝ) (r u π i : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted π ∧ (∀ t, i t = r t + 𝔼.E t (π (t + 1))) ∧ ∀ t, i t = φ • π t + u t

/-- Cochrane (2023), p. 382: in any equilibrium of the real-rate model, the IV estimate with
instrument `z` is `φ + ∑ z u / ∑ z π`. -/
theorem rr_iv_eq_phi_add {φ : ℝ} {r u π i : ℕ → Ω → ℝ} (h : RREq 𝔼 φ r u π i) (ω : Ω)
    (z : ℕ → ℝ) {T : ℕ} (hzx : ∑ t ∈ Finset.range T, z t * π t ω ≠ 0) :
    ivEst z (fun t => π t ω) (fun t => i t ω) T =
      φ + (∑ t ∈ Finset.range T, z t * u t ω) / ∑ t ∈ Finset.range T, z t * π t ω :=
  ivEst_eq_add (fun t _ => by simp only [h.2.2 t, Pi.add_apply, Pi.smul_apply, smul_eq_mul])
    hzx

/-- Cochrane (2023), p. 382 ("We might try to assume that monetary-policy disturbances are
orthogonal to disturbances to the other equations"): the IV estimate equals `φ` iff the
instrument is orthogonal to `u` in the sample; if the bank responds to the other shocks
(`∑ z u ≠ 0`) it does not measure `φ`. -/
theorem rr_iv_eq_phi_iff {φ : ℝ} {r u π i : ℕ → Ω → ℝ} (h : RREq 𝔼 φ r u π i) (ω : Ω)
    (z : ℕ → ℝ) {T : ℕ} (hzx : ∑ t ∈ Finset.range T, z t * π t ω ≠ 0) :
    ivEst z (fun t => π t ω) (fun t => i t ω) T = φ ↔
      ∑ t ∈ Finset.range T, z t * u t ω = 0 := by
  rw [rr_iv_eq_phi_add 𝔼 h ω z hzx]
  constructor
  · intro e
    have : (∑ t ∈ Finset.range T, z t * u t ω) / ∑ t ∈ Finset.range T, z t * π t ω = 0 := by
      linarith
    rcases div_eq_zero_iff.mp this with h0 | h0
    · exact h0
    · exact absurd h0 hzx
  · intro e
    rw [e, zero_div, add_zero]

/-- Cochrane (2023), p. 382: in the real-rate model with `|φ| > 1`, the equilibrium is the
unique bounded solution of `E_t π_{t+1} = φ π_t + u_t − r_t`. -/
theorem rr_unique {φ : ℝ} (hφ : 1 < |φ|) {r u π₁ π₂ i₁ i₂ : ℕ → Ω → ℝ}
    (h₁ : RREq 𝔼 φ r u π₁ i₁) (h₂ : RREq 𝔼 φ r u π₂ i₂) (hb₁ : BoundedProc π₁)
    (hb₂ : BoundedProc π₂) : π₁ = π₂ := by
  have key : ∀ π i, RREq 𝔼 φ r u π i → Eq164 𝔼 φ (fun t => u t - r t) π := by
    intro π i h t
    have e1 := h.2.1 t
    have e2 := h.2.2 t
    rw [e2] at e1
    rw [show 𝔼.E t (π (t + 1)) = φ • π t + u t - r t by rw [e1]; abel]
    abel_nf
  exact eq164_unique 𝔼 hφ (key _ _ h₁) (key _ _ h₂) hb₁ hb₂

/-- Cochrane (2023), p. 382: a non-vacuous identified example under perfect foresight. With
`φ = 2`, a constant real-rate shock `r = 1` and no disturbance, `π = 1`, `i = 2` is the unique
bounded equilibrium, and the IV estimate with instrument `r` on any nonempty sample is `φ = 2`. -/
theorem rr_example (T : ℕ) (hT : 0 < T) :
    RREq perfectForesight 2 (fun _ _ => 1) 0 (fun _ _ => 1) (fun _ _ => 2) ∧
      (∀ π i, RREq perfectForesight 2 (fun _ _ => 1) 0 π i → BoundedProc π →
        π = fun _ _ => 1) ∧
      ivEst (fun _ => 1) (fun t => (fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) t ())
        (fun t => (fun (_ : ℕ) (_ : Unit) => (2 : ℝ)) t ()) T = 2 := by
  have h : RREq perfectForesight 2 (fun _ _ => 1) 0 (fun _ _ => 1) (fun _ _ => 2) := by
    refine ⟨fun t => rfl, fun t => ?_, fun t => ?_⟩
    · funext ω
      change (2 : ℝ) = 1 + 1
      norm_num
    · funext ω
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
      norm_num
  refine ⟨h, fun π i h' hb => rr_unique perfectForesight (by norm_num) h' h hb
    ⟨1, fun _ _ => by simp⟩, ?_⟩
  have hs : ∑ t ∈ Finset.range T, (1 : ℝ) * 1 ≠ 0 := by
    simp only [mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact_mod_cast hT.ne'
  exact ivEst_eq (η := 2) (fun t _ => by norm_num) hs

/-! ### §16.10.7: the on-equilibrium parameter θ of the fiscal-theory model is identified -/

/-- Cochrane (2023), (2.20)–(2.22), p. 40: an equilibrium of the simple fiscal-theory model,
`i_t = E_t π_{t+1}`, `ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}`, `i_t = θ π_t + u_t`. -/
def FTPLEq (θ : ℝ) (u εs π i : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted π ∧ (∀ t, i t = 𝔼.E t (π (t + 1))) ∧
    (∀ t, innov 𝔼 t (π (t + 1)) = -εs (t + 1)) ∧
    ∀ t, i t = θ • π t + u t

/-- Cochrane (2023), §16.10.7, p. 394: the class of fiscal-theory specifications
`(θ, ε_Σs, π)` with no monetary disturbance whose inflation is not identically zero. -/
def ftplClass : Set (ℝ × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ)) :=
  {m | FTPLEq 𝔼 m.1 0 m.2.1 m.2.2 (fisherRate 𝔼 m.2.2) ∧ ∃ t ω, m.2.2 t ω ≠ 0}

/-- Cochrane (2023), §16.10.7, p. 394 ("In the passive-money active-fiscal equilibrium, `θ` …
is identified"): in an equilibrium with `u = 0`, `θ = i_t/π_t` at any date and state with
`π_t ≠ 0`. -/
theorem ftpl_theta_eq {θ : ℝ} {εs π i : ℕ → Ω → ℝ} (h : FTPLEq 𝔼 θ 0 εs π i) {t : ℕ} {ω : Ω}
    (hπ : π t ω ≠ 0) : θ = i t ω / π t ω := by
  have e := congrFun (h.2.2.2 t) ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, add_zero] at e
  rw [e, mul_div_assoc, div_self hπ, mul_one]

/-- Cochrane (2023), §16.10.7, p. 394: `θ` is identified on the fiscal-theory class. -/
theorem ftpl_theta_identified : IdentifiedOn (ftplClass 𝔼) (nkObs 𝔼) Prod.fst := by
  rintro ⟨θ₁, ε₁, π₁⟩ ⟨h₁, t, ω, hπ⟩ ⟨θ₂, ε₂, π₂⟩ ⟨h₂, -⟩ he
  simp only [nkObs, Prod.mk.injEq] at he
  obtain ⟨rfl, -⟩ := he
  exact (ftpl_theta_eq 𝔼 h₁ hπ).trans (ftpl_theta_eq 𝔼 h₂ hπ).symm

/-- Cochrane (2023), §16.10.7, p. 394 ("identified, and hence measurable by econometricians and
learnable to agents"): a learning rule recovers `θ` from the observables. -/
theorem ftpl_theta_learnable :
    ∃ L : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) → ℝ, ∀ m ∈ ftplClass 𝔼, L (nkObs 𝔼 m) = m.1 :=
  (identified_iff_learnable _ _ _).mp (ftpl_theta_identified 𝔼)

end Cochrane.NewKeynesianSelection.Identification
