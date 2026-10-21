/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.Identification
import NewKeynesianSelection.ExpectationsFiniteTree

/-!
# Observational equivalence of new-Keynesian and fiscal-theory equilibria

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 16, §16.6 "Observational
equivalence" (pp. 372–374), with the simple fiscal-theory model (2.20)–(2.25) of §2.6
(p. 40) and the `*`-notation fiscal rule of §5.4–5.5 ((5.29)–(5.38), pp. 137–139).

All statements hold for an arbitrary `ExpectationSystem` and are pathwise equalities of
processes.

## Main results

* (2.25): `ftpl_eq_225`, `ftpl_unique`, `ftpl_exists` — given `π_0` and the exogenous
  processes, the fiscal-theory equilibrium exists and is unique (for every `θ`); the path is
  the canonical `FTPLSimple.ruleSol`, and the implied fiscal shock `ε_Σs = −ΔEπ` is the
  canonical `FTPLSimple.passiveShock`.
* NI-5 (p. 372): `nk_is_ftpl` — the selected new-Keynesian AR(1) equilibrium `(φ, η, ε_i)` is
  the fiscal-theory equilibrium with `θ = η`, `u = 0`, `ε_Σs = ε_i/(φ − η)`;
  `nk_eq_ftpl_path` (equality with the fiscal-theory path), `passive_surplus_eq_active`, and
  equal impulse responses `obs_irf`, `nk_irf`, `ftpl_irf`, `nk_irf_eq_ftpl_irf`.
* "Any new-Keynesian model can be written as a fiscal theory model" (p. 373):
  `nk_to_ftpl` (every equilibrium, with any `θ`, in particular a time-varying peg),
  `ftpl_to_nk`, and the two-way set equalities `nkObsSet_eq_ftplObsSet`,
  `selectedObsSet_eq_boundedFtplObsSet`.
* The unified model (16.20)–(16.22): `MonetaryBlock`, `FiscalBlock`, `TVC`, `UnifiedEq`;
  deviation dynamics `e_dyn` (`ρ e_{t+1} = e_t − (ΔEπ − ΔEπ*)`, free of `γ`), `vs_dyn`,
  `v_dyn`; `tendsto_tvc` (`ρ^T E_t v_{t+T} → (α − γ)/α · (v_t − v*_t)`), `tvc_iff`.
* Regimes (p. 373) and survey error E6: `passive_of_eq` (`γ = α`: the TVC holds for every
  inflation path), `not_passive_of_ne`, `passive_iff` (fiscal policy is passive iff `γ = α`;
  the printed "`γ > 0`" and the conjectured "`0 < γ < 2`" are wrong), the concrete coin-flip
  counterexample `e6_counterexample`; `af_regime` (active fiscal: `ΔEπ = ΔEπ*`,
  `π_t − π*_t = φᵗ(π_0 − π*_0)`), `af_regime_phi_zero`, `am_regime`.
* NI-6 (16.23)–(16.24): `ObsFiscal`, `unifiedEq_obs` (every equilibrium of every regime
  satisfies (16.23)–(16.24)), `obs_unifiedEq` (every solution of (16.23)–(16.24) is an
  equilibrium of every regime), `eqObs_eq`, `eqObs_nonempty`,
  `regimes_observationally_equivalent`, `gamma_phi_not_identified`, `gamma_phi_not_learnable`
  (§16.10.7: "the argument admittedly cuts both ways").
* Survey error E6 resolved: with (16.21) as printed (the actual surplus `s_{t+1}` in both debt
  equations) passivity holds iff `γ = α`, not for all `γ > 0` and not for all `0 < γ < 2`
  (`0 < γ < 2` is the passivity range of the surplus rule `s_{t+1} = γ v_t + u_{s,t+1}` of
  (5.36)–(5.37), which is (16.20) with `γ = α`).
-/

namespace Cochrane.NewKeynesianSelection.ObservationalEquivalence

open Filter Topology Cochrane.NewKeynesianSelection.Identification
open Innovation (innov IsShock innov_eq_sub_E E_innov_zero_of_le innov_known_next isShock_smul
  isShock_neg coinShock_adapted)
open SimplestModel (ar1Pi ar1Pi_adapted)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The simple fiscal-theory model (2.20)–(2.25) -/

/-- Cochrane (2023), (2.25), p. 40: in a fiscal-theory equilibrium
`π_{t+1} = θ π_t + u_t − ε_{Σs,t+1}`. -/
theorem ftpl_eq_225 {θ : ℝ} {u εs π i : ℕ → Ω → ℝ} (h : FTPLEq 𝔼 θ u εs π i) (t : ℕ) :
    π (t + 1) = θ • π t + u t - εs (t + 1) := by
  have e := h.2.2.1 t
  rw [innov_eq_sub_E 𝔼 (h.1 (t + 1)), ← h.2.1 t, h.2.2.2 t] at e
  rw [show π (t + 1) = π (t + 1) - (θ • π t + u t) + (θ • π t + u t) by abel, e]
  abel

/-- Cochrane (2023), (2.20)–(2.25), p. 40: given the date-0 inflation and the exogenous
processes, the fiscal-theory equilibrium is unique (for every `θ`; no boundedness needed). -/
theorem ftpl_unique {θ : ℝ} {u εs π₁ π₂ i₁ i₂ : ℕ → Ω → ℝ} (h₁ : FTPLEq 𝔼 θ u εs π₁ i₁)
    (h₂ : FTPLEq 𝔼 θ u εs π₂ i₂) (h0 : π₁ 0 = π₂ 0) : π₁ = π₂ ∧ i₁ = i₂ := by
  have hπ : π₁ = π₂ := by
    funext t
    induction t with
    | zero => exact h0
    | succ t ih => rw [ftpl_eq_225 𝔼 h₁ t, ftpl_eq_225 𝔼 h₂ t, ih]
  refine ⟨hπ, funext fun t => ?_⟩
  rw [h₁.2.2.2 t, h₂.2.2.2 t, hπ]

/-- Cochrane (2023), (2.20)–(2.25), p. 40: for adapted `u`, a fiscal shock `ε_Σs` and a
date-0 inflation known at date 0, the path (2.25) (`FTPLSimple.ruleSol`) is a fiscal-theory
equilibrium. -/
theorem ftpl_exists (θ : ℝ) {u εs : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (hu : 𝔼.Adapted u)
    (hε : IsShock 𝔼 εs) (h0 : 𝔼.E 0 π0 = π0) :
    FTPLEq 𝔼 θ u εs (FTPLSimple.ruleSol θ u εs π0)
      (fisherRate 𝔼 (FTPLSimple.ruleSol θ u εs π0)) := by
  have ha := FTPLSimple.ruleSol_adapted 𝔼 (θ := θ) h0 hu hε
  have h224 := (FTPLSimple.eq224_iff 𝔼 ha hu hε).mpr fun t => rfl
  exact ⟨ha, fun _ => rfl, fun t => (h224 t).2, fun t => (h224 t).1⟩

/-! ### NI-5: the new-Keynesian equilibrium is a fiscal-theory equilibrium (p. 372) -/

/-- Cochrane (2023), p. 372: the selected AR(1) new-Keynesian equilibrium (16.10) with
`(φ, η, ε_i)` is a fiscal-theory equilibrium (2.20)–(2.22) with `θ = η`, no monetary
disturbance and fiscal shock `ε_Σs = ε_i/(φ − η)`. -/
theorem nk_is_ftpl (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) :
    FTPLEq 𝔼 η 0 (fun t => (φ - η)⁻¹ • ε t) (ar1Pi φ η u) (fisherRate 𝔼 (ar1Pi φ η u)) := by
  refine ⟨fun s => by simp only [ar1Pi, map_smul, h.1 s], fun _ => rfl, fun t => ?_,
    fun t => ?_⟩
  · rw [eq_16_16_innov 𝔼 φ h t, neg_smul]
  · rw [(eq_16_15 𝔼 φ h t).1, Pi.zero_apply, add_zero]

/-- Cochrane (2023), p. 372 ("the fiscal theory model produces exactly the same time series"):
the fiscal-theory path with `θ = η`, `u = 0`, `ε_Σs = ε_i/(φ − η)` and `π_0 = −u_0/(φ − η)` IS
the new-Keynesian selected path. -/
theorem nk_eq_ftpl_path (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) :
    FTPLSimple.ruleSol η 0 (fun t => (φ - η)⁻¹ • ε t) (ar1Pi φ η u 0) = ar1Pi φ η u := by
  have hε : IsShock 𝔼 (fun t => (φ - η)⁻¹ • ε t) := isShock_smul 𝔼 h.2.1 _
  have h0 : 𝔼.E 0 (ar1Pi φ η u 0) = ar1Pi φ η u 0 := ar1Pi_adapted 𝔼 φ η h.1 0
  exact (ftpl_unique 𝔼 (ftpl_exists 𝔼 η (fun t => by simp) hε h0) (nk_is_ftpl 𝔼 φ h)
    rfl).1

/-- Cochrane (2023), p. 372 ("fiscal policy passively raises surpluses by
`ε_Σs,t+1 = −ΔE_{t+1}π_{t+1} = ε_{i,t+1}/(φ − η)`. This value is exactly the same as the fiscal
theory model's active fiscal shock"). -/
theorem passive_surplus_eq_active (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε)
    (t : ℕ) : -innov 𝔼 t (ar1Pi φ η u (t + 1)) = (fun s => (φ - η)⁻¹ • ε s) (t + 1) :=
  (eq_16_18 𝔼 φ h t).2

/-- Cochrane (2023), (16.16), p. 371: impulse responses of the observable system,
`E_{t+1} π_{t+1+k} − E_t π_{t+1+k} = ηᵏ ε_{π,t+1}`. -/
theorem obs_irf {η : ℝ} {π i επ : ℕ → Ω → ℝ} (h : ObsAR1 𝔼 η π i επ) (t k : ℕ) :
    𝔼.E (t + 1) (π (t + 1 + k)) - 𝔼.E t (π (t + 1 + k)) = η ^ k • επ (t + 1) := by
  have har : 𝔼.IsAR1 η π := ⟨h.1, fun s => by
    rw [h.2.2.1 s, map_add, map_smul, h.1 s, h.2.1.2 s, add_zero]⟩
  rw [𝔼.ar1_iterate har, show t + 1 + k = t + (k + 1) by omega, 𝔼.ar1_iterate har,
    h.2.2.1 t, smul_add, pow_succ, ← smul_smul]
  abel

/-- Cochrane (2023), (16.10), p. 365 and Figure 16.1: the new-Keynesian response to a
monetary-policy shock, `ΔE_{t+1} π_{t+1+k} = −ηᵏ ε_{i,t+1}/(φ − η)`. -/
theorem nk_irf (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (t k : ℕ) :
    𝔼.E (t + 1) (ar1Pi φ η u (t + 1 + k)) - 𝔼.E t (ar1Pi φ η u (t + 1 + k)) =
      (-(η ^ k * (φ - η)⁻¹)) • ε (t + 1) := by
  rw [obs_irf 𝔼 (ar1_obs 𝔼 φ h) t k, smul_smul]
  congr 1
  ring

/-- Cochrane (2023), (2.25), p. 40 and Figure 2.2: the fiscal-theory response to a fiscal shock
with `u = 0`, `ΔE_{t+1} π_{t+1+k} = −θᵏ ε_{Σs,t+1}`. -/
theorem ftpl_irf {θ : ℝ} {εs π i : ℕ → Ω → ℝ} (h : FTPLEq 𝔼 θ 0 εs π i) (hε : IsShock 𝔼 εs)
    (t k : ℕ) :
    𝔼.E (t + 1) (π (t + 1 + k)) - 𝔼.E t (π (t + 1 + k)) = (-θ ^ k) • εs (t + 1) := by
  have hobs : ObsAR1 𝔼 θ π i (fun s => -εs s) :=
    ⟨h.1, isShock_neg 𝔼 hε,
      fun s => by rw [ftpl_eq_225 𝔼 h s, Pi.zero_apply, add_zero, sub_eq_add_neg],
      fun s => by rw [h.2.2.2 s, Pi.zero_apply, add_zero]⟩
  rw [obs_irf 𝔼 hobs t k, smul_neg, neg_smul]

/-- Cochrane (2023), p. 372 ("The new-Keynesian inflation response to a monetary policy shock
of Figure 16.1 is exactly the same as the fiscal-theory inflation response to a fiscal
shock"): with `θ = η` and `ε_Σs = ε_i/(φ − η)` the two impulse responses coincide. -/
theorem nk_irf_eq_ftpl_irf (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (t k : ℕ) :
    𝔼.E (t + 1) (ar1Pi φ η u (t + 1 + k)) - 𝔼.E t (ar1Pi φ η u (t + 1 + k)) =
      (-η ^ k) • (fun s => (φ - η)⁻¹ • ε s) (t + 1) := by
  rw [nk_irf 𝔼 φ h, smul_smul]
  congr 1
  ring

/-! ### Any new-Keynesian equilibrium is a fiscal-theory equilibrium, and conversely -/

/-- Cochrane (2023), p. 373 ("Any new-Keynesian model can be written as a fiscal theory
model"): every equilibrium of (16.1)–(16.2), for any `φ` and `u` (selected or not), is, for
EVERY `θ`, a fiscal-theory equilibrium with monetary disturbance `u^F = i − θπ` and active
fiscal shock `ε_Σs = −ΔEπ`; it is the unique such equilibrium with its date-0 inflation. -/
theorem nk_to_ftpl {φ : ℝ} {u π i : ℕ → Ω → ℝ} (h : NKEq 𝔼 φ u π i) (θ : ℝ) :
    FTPLEq 𝔼 θ (fun t => i t - θ • π t) (FTPLSimple.passiveShock 𝔼 π) π i ∧
      ∀ π' i', FTPLEq 𝔼 θ (fun t => i t - θ • π t) (FTPLSimple.passiveShock 𝔼 π) π' i' →
        π' 0 = π 0 → π' = π ∧ i' = i := by
  have hF : FTPLEq 𝔼 θ (fun t => i t - θ • π t) (FTPLSimple.passiveShock 𝔼 π) π i :=
    ⟨h.1, h.2.1, fun t => by simp only [FTPLSimple.passiveShock, neg_neg],
      fun t => (add_sub_cancel (θ • π t) (i t)).symm⟩
  exact ⟨hF, fun π' i' h' h0 => ftpl_unique 𝔼 h' hF h0⟩

/-- Cochrane (2023), pp. 367, 373: the special case of a time-varying interest-rate peg
`i_t = i*_t` (`θ = 0`, `u^F = i`). -/
theorem nk_to_peg {φ : ℝ} {u π i : ℕ → Ω → ℝ} (h : NKEq 𝔼 φ u π i) :
    FTPLEq 𝔼 0 i (FTPLSimple.passiveShock 𝔼 π) π i := by
  have := (nk_to_ftpl 𝔼 h 0).1
  simpa only [zero_smul, sub_zero] using this

/-- Cochrane (2023), p. 373 ("Observational equivalence goes both ways"): every bounded
fiscal-theory equilibrium is, for every `φ` with `|φ| > 1`, the new-Keynesian selected
equilibrium with `u = i − φπ`. -/
theorem ftpl_to_nk {θ : ℝ} {u εs π i : ℕ → Ω → ℝ} (h : FTPLEq 𝔼 θ u εs π i)
    (hb : BoundedProc π) {φ : ℝ} (hφ : 1 < |φ|) :
    NKEq 𝔼 φ (fun t => i t - φ • π t) π i ∧ Selected 𝔼 φ (fun t => i t - φ • π t) π :=
  every_eq_selected 𝔼 ⟨h.1, h.2.1, h.2.2.2⟩ hb hφ

/-- Cochrane (2023), p. 373: the observables of new-Keynesian equilibria. -/
def nkObsSet : Set ((ℕ → Ω → ℝ) × (ℕ → Ω → ℝ)) := {o | ∃ φ u, NKEq 𝔼 φ u o.1 o.2}

/-- Cochrane (2023), p. 373: the observables of fiscal-theory equilibria. -/
def ftplObsSet : Set ((ℕ → Ω → ℝ) × (ℕ → Ω → ℝ)) := {o | ∃ θ u εs, FTPLEq 𝔼 θ u εs o.1 o.2}

/-- Cochrane (2023), p. 373 ("You can always fit the data at least as well with a fiscal theory
model as you can with an active-money model"): the two sets of observable equilibrium
processes are equal. -/
theorem nkObsSet_eq_ftplObsSet : nkObsSet 𝔼 = ftplObsSet 𝔼 := by
  ext ⟨π, i⟩
  constructor
  · rintro ⟨φ, u, h⟩
    exact ⟨φ, _, _, (nk_to_ftpl 𝔼 h φ).1⟩
  · rintro ⟨θ, u, εs, h⟩
    exact ⟨θ, u, h.1, h.2.1, h.2.2.2⟩

/-- Cochrane (2023), pp. 372–373: the observables of new-Keynesian SELECTED equilibria
(`|φ| > 1`, unique bounded solution). -/
def selectedObsSet : Set ((ℕ → Ω → ℝ) × (ℕ → Ω → ℝ)) :=
  {o | ∃ φ u, 1 < |φ| ∧ Selected 𝔼 φ u o.1 ∧ o.2 = fisherRate 𝔼 o.1}

/-- Cochrane (2023), pp. 372–373: the observables of bounded fiscal-theory equilibria. -/
def boundedFtplObsSet : Set ((ℕ → Ω → ℝ) × (ℕ → Ω → ℝ)) :=
  {o | (∃ θ u εs, FTPLEq 𝔼 θ u εs o.1 o.2) ∧ BoundedProc o.1}

/-- Cochrane (2023), pp. 372–373 (observational equivalence, both directions): the
new-Keynesian selected equilibria and the bounded fiscal-theory equilibria produce exactly
the same set of observable processes. -/
theorem selectedObsSet_eq_boundedFtplObsSet : selectedObsSet 𝔼 = boundedFtplObsSet 𝔼 := by
  ext ⟨π, i⟩
  constructor
  · rintro ⟨φ, u, -, hs, hi⟩
    simp only at hs hi
    subst hi
    have hN : NKEq 𝔼 φ u π (fisherRate 𝔼 π) :=
      (nkEq_iff 𝔼 _ _ _ _).mpr ⟨hs.2.1, hs.2.2.1, rfl⟩
    exact ⟨⟨φ, _, _, (nk_to_ftpl 𝔼 hN φ).1⟩, hs.1⟩
  · rintro ⟨⟨θ, u, εs, h⟩, hb⟩
    have h2 : 1 < |(2 : ℝ)| := by norm_num
    obtain ⟨hN, hs⟩ := ftpl_to_nk 𝔼 h hb h2
    exact ⟨2, _, h2, hs, ((nkEq_iff 𝔼 _ _ _ _).mp hN).2.2⟩

/-! ### The unified model (16.20)–(16.22) -/

/-- Cochrane (2023), (16.20), p. 373, monetary block: `i_t = E_t π_{t+1}`,
`i_t = i*_t + φ(π_t − π*_t)`, with consistent targets `i*_t = E_t π*_{t+1}`. -/
def MonetaryBlock (φ : ℝ) (istar pistar π i : ℕ → Ω → ℝ) : Prop :=
  KingEq 𝔼 φ istar pistar π i ∧ TargetsConsistent 𝔼 istar pistar

/-- Cochrane (2023), (16.20)–(16.22), p. 373, fiscal block: the surplus rule
`s_{t+1} = α v*_t + γ(v_t − v*_t) + u_{s,t+1}`, the target-debt evolution (16.21)
`ρ v*_{t+1} = v*_t − ΔE_{t+1} π*_{t+1} − s_{t+1}`, the debt evolution (16.22)
`ρ v_{t+1} = v_t − ΔE_{t+1} π_{t+1} − s_{t+1}`, with `v`, `v*` adapted and the initial
condition `v_0 = v*_0` (the target debt starts at the actual debt). -/
def FiscalBlock (ρ α γ : ℝ) (us pistar π s v vs : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted v ∧ 𝔼.Adapted vs ∧ v 0 = vs 0 ∧
    (∀ t, s (t + 1) = α • vs t + γ • (v t - vs t) + us (t + 1)) ∧
    (∀ t, ρ • vs (t + 1) = vs t - innov 𝔼 t (pistar (t + 1)) - s (t + 1)) ∧
    ∀ t, ρ • v (t + 1) = v t - innov 𝔼 t (π (t + 1)) - s (t + 1)

/-- Cochrane (2023), p. 137 and p. 369: the transversality condition on the value of debt,
`ρ^T E_t v_{t+T} → 0` for every date and state. -/
def TVC (ρ : ℝ) (v : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Tendsto (fun T : ℕ => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 0)

/-- Cochrane (2023), (16.20)–(16.22), p. 373: an equilibrium of the unified model. -/
def UnifiedEq (ρ α γ φ : ℝ) (us istar pistar π i s v vs : ℕ → Ω → ℝ) : Prop :=
  MonetaryBlock 𝔼 φ istar pistar π i ∧ FiscalBlock 𝔼 ρ α γ us pistar π s v vs ∧ TVC 𝔼 ρ v

/-- Cochrane (2023), (5.35), p. 137, for (16.21)–(16.22): the debt gap `e = v − v*` obeys
`ρ e_{t+1} = e_t − (ΔE_{t+1} π_{t+1} − ΔE_{t+1} π*_{t+1})`; the surplus, hence `γ`, cancels. -/
theorem e_dyn {ρ α γ : ℝ} {us pistar π s v vs : ℕ → Ω → ℝ}
    (h : FiscalBlock 𝔼 ρ α γ us pistar π s v vs) (t : ℕ) :
    ρ • (v (t + 1) - vs (t + 1)) =
      (v t - vs t) - (innov 𝔼 t (π (t + 1)) - innov 𝔼 t (pistar (t + 1))) := by
  rw [smul_sub, h.2.2.2.2.2 t, h.2.2.2.2.1 t]
  abel

/-- Cochrane (2023), p. 138: substituting the surplus rule into (16.21),
`ρ v*_{t+1} = (1 − α) v*_t − γ(v_t − v*_t) − ΔE_{t+1} π*_{t+1} − u_{s,t+1}`. -/
theorem vs_dyn {ρ α γ : ℝ} {us pistar π s v vs : ℕ → Ω → ℝ}
    (h : FiscalBlock 𝔼 ρ α γ us pistar π s v vs) (t : ℕ) :
    ρ • vs (t + 1) =
      (1 - α) • vs t - γ • (v t - vs t) - innov 𝔼 t (pistar (t + 1)) - us (t + 1) := by
  rw [h.2.2.2.2.1 t, h.2.2.2.1 t, sub_smul, one_smul]
  abel

/-- Cochrane (2023), p. 138: substituting the surplus rule into (16.22),
`ρ v_{t+1} = (1 − γ) v_t − (α − γ) v*_t − ΔE_{t+1} π_{t+1} − u_{s,t+1}`; with `γ = α` this is
the passive rule (5.37) `ρ v_{t+1} = (1 − α) v_t − ΔE π_{t+1} − u_{s,t+1}`. -/
theorem v_dyn {ρ α γ : ℝ} {us pistar π s v vs : ℕ → Ω → ℝ}
    (h : FiscalBlock 𝔼 ρ α γ us pistar π s v vs) (t : ℕ) :
    ρ • v (t + 1) = (1 - γ) • v t - (α - γ) • vs t - innov 𝔼 t (π (t + 1)) - us (t + 1) := by
  rw [h.2.2.2.2.2 t, h.2.2.2.1 t, sub_smul, sub_smul, one_smul, smul_sub]
  abel

/-- Cochrane (2023), p. 137: the expected debt gap grows at rate `1/ρ`,
`ρ^k E_t e_{t+k} = e_t`. -/
theorem E_gap {ρ α γ : ℝ} {us pistar π s v vs : ℕ → Ω → ℝ}
    (h : FiscalBlock 𝔼 ρ α γ us pistar π s v vs) (t k : ℕ) (ω : Ω) :
    ρ ^ k * 𝔼.E t (v (t + k) - vs (t + k)) ω = v t ω - vs t ω := by
  induction k with
  | zero =>
    simp only [pow_zero, one_mul, add_zero, map_sub, h.1 t, h.2.1 t, Pi.sub_apply]
  | succ k ih =>
    have e := congrArg (fun x => 𝔼.E t x ω) (e_dyn 𝔼 h (t + k))
    simp only [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      E_innov_zero_of_le 𝔼 (Nat.le_add_right t k), Pi.zero_apply, sub_zero] at e
    rw [← add_assoc, pow_succ, mul_assoc, map_sub, Pi.sub_apply, e, ← ih, map_sub,
      Pi.sub_apply]

/-- Cochrane (2023), p. 138 (a linear recursion with converging forcing; general lemma not in
the core): if `W_{k+1} = q W_k + c_k` with `|q| < 1` and `c_k → L`, then
`W_k → L/(1 − q)`. -/
theorem rec_limit {q : ℝ} (hq : |q| < 1) {W c : ℕ → ℝ} {L : ℝ}
    (hW : ∀ k, W (k + 1) = q * W k + c k) (hc : Tendsto c atTop (𝓝 L)) :
    Tendsto W atTop (𝓝 (L / (1 - q))) := by
  have hq1 : 0 < 1 - |q| := by linarith
  have hq0 : 1 - q ≠ 0 := by
    intro h0
    have : q = 1 := by linarith
    rw [this, abs_one] at hq
    exact lt_irrefl _ hq
  set Z : ℕ → ℝ := fun k => W k - L / (1 - q) with hZ
  have hZs : ∀ k, Z (k + 1) = q * Z k + (c k - L) := by
    intro k
    simp only [hZ, hW k]
    field_simp
    ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hc' := (Metric.tendsto_atTop.mp hc) (ε * (1 - |q|) / 2) (by positivity)
  obtain ⟨N1, hN1⟩ := hc'
  have hbound : ∀ j, |Z (N1 + j)| ≤ |q| ^ j * |Z N1| + ε / 2 := by
    intro j
    induction j with
    | zero => simp only [add_zero, pow_zero, one_mul]; linarith
    | succ j ih =>
      rw [← add_assoc, hZs, ← Real.dist_eq]
      have hd := hN1 (N1 + j) (Nat.le_add_right _ _)
      calc |q * Z (N1 + j) + (c (N1 + j) - L)|
          ≤ |q * Z (N1 + j)| + |c (N1 + j) - L| := abs_add_le _ _
        _ ≤ |q| * (|q| ^ j * |Z N1| + ε / 2) + ε * (1 - |q|) / 2 := by
            rw [abs_mul]
            rw [Real.dist_eq] at hd
            gcongr
        _ = |q| ^ (j + 1) * |Z N1| + ε / 2 := by ring
  have hgeo : Tendsto (fun j : ℕ => |q| ^ j * |Z N1|) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg q) hq).mul_const |Z N1|
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.mp hgeo) (ε / 2) (by positivity)
  refine ⟨N1 + J, fun n hn => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hbJ := hbound (J + j)
  have h2 := hJ (J + j) (Nat.le_add_right _ _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h2
  rw [dist_zero_right, Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
  change |Z (N1 + J + j)| < ε
  rw [add_assoc]
  linarith

/-- Cochrane (2023), (16.21)–(16.22), p. 373, and pp. 137–138: for `0 < ρ < 1`, `0 < α < 2`
and a bounded surplus disturbance, `ρ^T E_t v_{t+T} → ((α − γ)/α) (v_t − v*_t)`. -/
theorem tendsto_tvc {ρ α γ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α) (hα2 : α < 2)
    {us pistar π s v vs : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M)
    (h : FiscalBlock 𝔼 ρ α γ us pistar π s v vs) (t : ℕ) (ω : Ω) :
    Tendsto (fun T : ℕ => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop
      (𝓝 ((α - γ) / α * (v t ω - vs t ω))) := by
  set e := v t ω - vs t ω with he
  set W : ℕ → ℝ := fun k => ρ ^ k * 𝔼.E t (vs (t + k)) ω with hWdef
  set g : ℕ → ℝ := fun k => 𝔼.E t (us (t + k + 1)) ω with hg
  have hW : ∀ k, W (k + 1) = (1 - α) * W k + (-γ * e - ρ ^ k * g k) := by
    intro k
    have e1 := congrArg (fun x => 𝔼.E t x ω) (vs_dyn 𝔼 h (t + k))
    simp only [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      E_innov_zero_of_le 𝔼 (Nat.le_add_right t k), sub_zero] at e1
    have hgap := E_gap 𝔼 h t k ω
    rw [map_sub, Pi.sub_apply] at hgap
    simp only [hWdef, hg, ← add_assoc, pow_succ]
    rw [mul_assoc, e1]
    linear_combination (-γ) * hgap + γ * he
  have hgb : ∀ k, |g k| ≤ M := fun k => 𝔼.abs_E_le (hus _) t ω
  have hc : Tendsto (fun k => -γ * e - ρ ^ k * g k) atTop (𝓝 (-γ * e)) := by
    have h0 : Tendsto (fun k => ρ ^ k * g k) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
        (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).mul_const M)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hρ0 k)]
      exact mul_le_mul_of_nonneg_left (hgb k) (pow_pos hρ0 k).le
    simpa using tendsto_const_nhds.sub h0
  have hq : |1 - α| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hWlim := rec_limit hq hW hc
  have hsplit : ∀ T : ℕ, ρ ^ T * 𝔼.E t (v (t + T)) ω = W T + e := by
    intro T
    have hgap := E_gap 𝔼 h t T ω
    rw [map_sub, Pi.sub_apply] at hgap
    simp only [hWdef]
    linear_combination hgap - he
  simp only [hsplit]
  have hα : α ≠ 0 := hα0.ne'
  rw [show (1 : ℝ) - (1 - α) = α by ring] at hWlim
  convert hWlim.add_const e using 2
  field_simp
  ring

/-- Cochrane (2023), (16.21)–(16.22), p. 373: given the fiscal block, the transversality
condition holds iff `(α − γ)(v_t − v*_t) = 0` at every date and state. -/
theorem tvc_iff {ρ α γ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α) (hα2 : α < 2)
    {us pistar π s v vs : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M)
    (h : FiscalBlock 𝔼 ρ α γ us pistar π s v vs) :
    TVC 𝔼 ρ v ↔ ∀ t ω, (α - γ) * (v t ω - vs t ω) = 0 := by
  constructor
  · intro htvc t ω
    have e := tendsto_nhds_unique (tendsto_tvc 𝔼 hρ0 hρ1 hα0 hα2 hus h t ω) (htvc t ω)
    rw [div_mul_eq_mul_div, div_eq_zero_iff] at e
    rcases e with e | e
    · exact e
    · exact absurd e hα0.ne'
  · intro h0 t ω
    have := tendsto_tvc 𝔼 hρ0 hρ1 hα0 hα2 hus h t ω
    rwa [div_mul_eq_mul_div, h0 t ω, zero_div] at this

/-- Cochrane (2023), p. 137: with `v_0 = v*_0`, the debt gap vanishes at every date iff
unexpected inflation equals the target's unexpected inflation at every date. -/
theorem gap_zero_iff {ρ α γ : ℝ} (hρ : ρ ≠ 0) {us pistar π s v vs : ℕ → Ω → ℝ}
    (h : FiscalBlock 𝔼 ρ α γ us pistar π s v vs) :
    (∀ t, v t = vs t) ↔ ∀ t, innov 𝔼 t (π (t + 1)) = innov 𝔼 t (pistar (t + 1)) := by
  constructor
  · intro hv t
    have e := e_dyn 𝔼 h t
    rw [hv t, hv (t + 1), sub_self, sub_self, smul_zero, zero_sub, eq_comm, neg_eq_zero,
      sub_eq_zero] at e
    exact e
  · intro hd t
    induction t with
    | zero => exact h.2.2.1
    | succ t ih =>
      have e := e_dyn 𝔼 h t
      rw [ih, hd t, sub_self, sub_self, sub_zero] at e
      have := (smul_eq_zero.mp e).resolve_left hρ
      exact sub_eq_zero.mp this

/-! ### Regimes, passivity, and survey error E6 -/

/-- Cochrane (2023), p. 138 ("for `γ > 1 − ρ` … any unexpected inflation is an equilibrium"):
fiscal policy is passive if the transversality condition holds along every inflation path,
i.e. for every solution of the fiscal block. -/
def FiscalPassive (ρ α γ : ℝ) (us : ℕ → Ω → ℝ) : Prop :=
  ∀ pistar π s v vs : ℕ → Ω → ℝ, FiscalBlock 𝔼 ρ α γ us pistar π s v vs → TVC 𝔼 ρ v

/-- Cochrane (2023), p. 373 ("most simply `γ = α > 0`"): with `γ = α` fiscal policy is passive. -/
theorem passive_of_eq {ρ α M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α) (hα2 : α < 2)
    {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) : FiscalPassive 𝔼 ρ α α us :=
  fun _ _ _ _ _ h => (tvc_iff 𝔼 hρ0 hρ1 hα0 hα2 hus h).mpr fun t ω => by ring

/-- Cochrane (2023), (16.20)–(16.22), p. 373: the fiscal block has a solution for any inflation
and target paths: the pair `(v, v*)` defined by the recursions. -/
noncomputable def fiscalPath (ρ α γ : ℝ) (us pistar π : ℕ → Ω → ℝ) (v0 : Ω → ℝ) :
    ℕ → (Ω → ℝ) × (Ω → ℝ)
  | 0 => (v0, v0)
  | t + 1 =>
    (ρ⁻¹ • ((fiscalPath ρ α γ us pistar π v0 t).1 - innov 𝔼 t (π (t + 1)) -
        (α • (fiscalPath ρ α γ us pistar π v0 t).2 +
          γ • ((fiscalPath ρ α γ us pistar π v0 t).1 - (fiscalPath ρ α γ us pistar π v0 t).2) +
          us (t + 1))),
      ρ⁻¹ • ((fiscalPath ρ α γ us pistar π v0 t).2 - innov 𝔼 t (pistar (t + 1)) -
        (α • (fiscalPath ρ α γ us pistar π v0 t).2 +
          γ • ((fiscalPath ρ α γ us pistar π v0 t).1 - (fiscalPath ρ α γ us pistar π v0 t).2) +
          us (t + 1))))

/-- Cochrane (2023), (16.20), p. 373: the surplus along `fiscalPath` (zero at date 0, which
the fiscal block does not constrain). -/
noncomputable def fiscalSurplus (ρ α γ : ℝ) (us pistar π : ℕ → Ω → ℝ) (v0 : Ω → ℝ) :
    ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => α • (fiscalPath 𝔼 ρ α γ us pistar π v0 t).2 +
      γ • ((fiscalPath 𝔼 ρ α γ us pistar π v0 t).1 - (fiscalPath 𝔼 ρ α γ us pistar π v0 t).2) +
      us (t + 1)

/-- Cochrane (2023), (16.20)–(16.22), p. 373: for `ρ ≠ 0`, adapted `u_s` and `v_0` known at
date 0, `fiscalPath` solves the fiscal block. -/
theorem fiscalPath_block {ρ : ℝ} (hρ : ρ ≠ 0) (α γ : ℝ) {us pistar π : ℕ → Ω → ℝ}
    {v0 : Ω → ℝ} (hus : 𝔼.Adapted us) (hv0 : 𝔼.E 0 v0 = v0) :
    FiscalBlock 𝔼 ρ α γ us pistar π (fiscalSurplus 𝔼 ρ α γ us pistar π v0)
      (fun t => (fiscalPath 𝔼 ρ α γ us pistar π v0 t).1)
      (fun t => (fiscalPath 𝔼 ρ α γ us pistar π v0 t).2) := by
  have had : ∀ t, 𝔼.E t (fiscalPath 𝔼 ρ α γ us pistar π v0 t).1 =
      (fiscalPath 𝔼 ρ α γ us pistar π v0 t).1 ∧
      𝔼.E t (fiscalPath 𝔼 ρ α γ us pistar π v0 t).2 =
        (fiscalPath 𝔼 ρ α γ us pistar π v0 t).2 := by
    intro t
    induction t with
    | zero => exact ⟨hv0, hv0⟩
    | succ t ih =>
      have k1 := ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih.1
      have k2 := ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih.2
      constructor <;>
        simp only [fiscalPath, map_smul, map_sub, map_add, k1, k2, innov_known_next, hus (t + 1)]
  refine ⟨fun t => (had t).1, fun t => (had t).2, rfl, fun t => rfl, fun t => ?_, fun t => ?_⟩
  · simp only [fiscalPath, fiscalSurplus, smul_smul, mul_inv_cancel₀ hρ, one_smul]
  · simp only [fiscalPath, fiscalSurplus, smul_smul, mul_inv_cancel₀ hρ, one_smul]

/-- Cochrane (2023), p. 373 and survey error E6: if `γ ≠ α` and some inflation path has
unexpected inflation different from the target's, fiscal policy is NOT passive: along that
path the transversality condition fails. -/
theorem not_passive_of_ne {ρ α γ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α)
    (hα2 : α < 2) (hγ : γ ≠ α) {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M)
    (husa : 𝔼.Adapted us) {pistar π : ℕ → Ω → ℝ} {t₀ : ℕ}
    (hne : innov 𝔼 t₀ (π (t₀ + 1)) ≠ innov 𝔼 t₀ (pistar (t₀ + 1))) :
    ¬ FiscalPassive 𝔼 ρ α γ us := by
  intro hP
  have hb := fiscalPath_block 𝔼 hρ0.ne' α γ (pistar := pistar) (π := π) (v0 := 0) husa
    (by simp)
  have htvc := hP _ _ _ _ _ hb
  rw [tvc_iff 𝔼 hρ0 hρ1 hα0 hα2 hus hb] at htvc
  have hgap : ∀ t, (fiscalPath 𝔼 ρ α γ us pistar π 0 t).1 =
      (fiscalPath 𝔼 ρ α γ us pistar π 0 t).2 := fun t => funext fun ω => by
    have := htvc t ω
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (sub_eq_zero.mp h0).symm hγ
    · exact sub_eq_zero.mp h0
  exact hne ((gap_zero_iff 𝔼 hρ0.ne' hb).mp hgap t₀)

/-- Cochrane (2023), p. 373 (corrected; survey error E6): on any expectation system with a
nonzero innovation, fiscal policy (16.20)–(16.22) is passive if and only if `γ = α`. The
printed "active-monetary passive-fiscal policy with `φ > 1`, `γ > 0`" is passive only for
`γ = α`; every `γ ≠ α` makes the fiscal rule active as well. -/
theorem passive_iff {ρ α γ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α) (hα2 : α < 2)
    {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) (husa : 𝔼.Adapted us)
    (hnt : ∃ (x : ℕ → Ω → ℝ) (t : ℕ), innov 𝔼 t (x (t + 1)) ≠ 0) :
    FiscalPassive 𝔼 ρ α γ us ↔ γ = α := by
  constructor
  · intro hP
    by_contra hγ
    obtain ⟨x, t, hx⟩ := hnt
    have hne : innov 𝔼 t (x (t + 1)) ≠ innov 𝔼 t ((0 : ℕ → Ω → ℝ) (t + 1)) := by
      simpa [Innovation.innov] using hx
    exact not_passive_of_ne 𝔼 hρ0 hρ1 hα0 hα2 hγ hus husa hne hP
  · rintro rfl
    exact passive_of_eq 𝔼 hρ0 hρ1 hα0 hα2 hus

/-- Cochrane (2023), (16.20), p. 373: under the monetary block, the inflation gap
`x = π − π*` obeys `x_{t+1} = φ x_t + (ΔE_{t+1} π_{t+1} − ΔE_{t+1} π*_{t+1})`. -/
theorem gap_succ {φ : ℝ} {istar pistar π i : ℕ → Ω → ℝ}
    (h : MonetaryBlock 𝔼 φ istar pistar π i) (t : ℕ) :
    π (t + 1) - pistar (t + 1) =
      φ • (π t - pistar t) + (innov 𝔼 t (π (t + 1)) - innov 𝔼 t (pistar (t + 1))) := by
  rw [innov_eq_sub_E 𝔼 (h.1.1 (t + 1)), innov_eq_sub_E 𝔼 (h.2.1 (t + 1)), ← h.1.2.1 t,
    ← h.2.2 t,
    h.1.2.2 t]
  abel

/-- Cochrane (2023), p. 373 (active fiscal, passive money): if `γ ≠ α`, every equilibrium has
`ΔE π = ΔE π*` and `v = v*` (for EVERY `φ`), and the inflation gap is `φᵗ(π_0 − π*_0)`; so
`π = π*` exactly when the date-0 inflation is on target. -/
theorem af_regime {ρ α γ φ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α) (hα2 : α < 2)
    (hγ : γ ≠ α) {us istar pistar π i s v vs : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M)
    (h : UnifiedEq 𝔼 ρ α γ φ us istar pistar π i s v vs) :
    (∀ t, innov 𝔼 t (π (t + 1)) = innov 𝔼 t (pistar (t + 1))) ∧ (∀ t, v t = vs t) ∧
      (∀ t, π t - pistar t = φ ^ t • (π 0 - pistar 0)) ∧
      (π 0 = pistar 0 → π = pistar ∧ i = istar) := by
  obtain ⟨hm, hf, htvc⟩ := h
  rw [tvc_iff 𝔼 hρ0 hρ1 hα0 hα2 hus hf] at htvc
  have hv : ∀ t, v t = vs t := fun t => funext fun ω => by
    rcases mul_eq_zero.mp (htvc t ω) with h0 | h0
    · exact absurd (sub_eq_zero.mp h0).symm hγ
    · exact sub_eq_zero.mp h0
  have hd := (gap_zero_iff 𝔼 hρ0.ne' hf).mp hv
  have hx : ∀ t, π t - pistar t = φ ^ t • (π 0 - pistar 0) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [gap_succ 𝔼 hm t, hd t, sub_self, add_zero, ih, smul_smul, pow_succ,
        mul_comm]
  refine ⟨hd, hv, hx, fun h0 => ?_⟩
  have hπ : π = pistar := funext fun t => by
    have := hx t
    rw [h0, sub_self, smul_zero] at this
    exact sub_eq_zero.mp this
  refine ⟨hπ, funext fun t => ?_⟩
  rw [hm.1.2.2 t, hπ, sub_self, smul_zero, add_zero]

/-- Cochrane (2023), p. 373 ("most simply `φ = 0`"): in the active-fiscal regime with `φ = 0`,
inflation equals its target from date 1 on, with no initial condition. -/
theorem af_regime_phi_zero {ρ α γ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α)
    (hα2 : α < 2) (hγ : γ ≠ α) {us istar pistar π i s v vs : ℕ → Ω → ℝ}
    (hus : ∀ t ω, |us t ω| ≤ M) (h : UnifiedEq 𝔼 ρ α γ 0 us istar pistar π i s v vs)
    (t : ℕ) : π (t + 1) = pistar (t + 1) := by
  have := (af_regime 𝔼 hρ0 hρ1 hα0 hα2 hγ hus h).2.2.1 (t + 1)
  rw [zero_pow (Nat.succ_ne_zero t), zero_smul] at this
  exact sub_eq_zero.mp this

/-- Cochrane (2023), p. 373 (active money): if `|φ| > 1` and the targets are bounded, every
equilibrium with bounded inflation has `π = π*`, `i = i*` and `v = v*` (for EVERY `γ`). -/
theorem am_regime {ρ α γ φ : ℝ} (hρ0 : 0 < ρ) (hφ : 1 < |φ|)
    {us istar pistar π i s v vs : ℕ → Ω → ℝ}
    (h : UnifiedEq 𝔼 ρ α γ φ us istar pistar π i s v vs) (hbs : BoundedProc pistar)
    (hb : BoundedProc π) : π = pistar ∧ i = istar ∧ ∀ t, v t = vs t := by
  obtain ⟨hπ, hi⟩ := king_bounded_eq 𝔼 hφ h.1.2 hbs h.1.1 hb
  refine ⟨hπ, hi, (gap_zero_iff 𝔼 hρ0.ne' h.2.1).mpr fun t => by rw [hπ]⟩

/-! ### NI-6: (16.23)–(16.24) -/

/-- Cochrane (2023), (16.23)–(16.24), p. 373: the observable system `i_t = E_t π_{t+1}`,
`s_{t+1} = α v_t + u_{s,t+1}`, `ρ v_{t+1} = v_t − ΔE_{t+1} π_{t+1} − s_{t+1}`, with `π`, `v`
adapted. -/
def ObsFiscal (ρ α : ℝ) (us π i s v : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted π ∧ 𝔼.Adapted v ∧ (∀ t, i t = 𝔼.E t (π (t + 1))) ∧
    (∀ t, s (t + 1) = α • v t + us (t + 1)) ∧
    ∀ t, ρ • v (t + 1) = v t - innov 𝔼 t (π (t + 1)) - s (t + 1)

/-- Cochrane (2023), (16.23)–(16.24), p. 373 (NI-6): in every regime (every `φ`, every `γ`),
the observables of every equilibrium satisfy (16.23)–(16.24), in which neither `φ` nor `γ`
appears. -/
theorem unifiedEq_obs {ρ α γ φ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α) (hα2 : α < 2)
    {us istar pistar π i s v vs : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M)
    (h : UnifiedEq 𝔼 ρ α γ φ us istar pistar π i s v vs) : ObsFiscal 𝔼 ρ α us π i s v := by
  obtain ⟨hm, hf, htvc⟩ := h
  rw [tvc_iff 𝔼 hρ0 hρ1 hα0 hα2 hus hf] at htvc
  refine ⟨hm.1.1, hf.1, hm.1.2.1, fun t => ?_, hf.2.2.2.2.2⟩
  rw [hf.2.2.2.1 t]
  by_cases hγ : γ = α
  · subst hγ
    rw [smul_sub, add_sub_cancel]
  · have hv : v t = vs t := funext fun ω => by
      rcases mul_eq_zero.mp (htvc t ω) with h0 | h0
      · exact absurd (sub_eq_zero.mp h0).symm hγ
      · exact sub_eq_zero.mp h0
    rw [hv, sub_self, smul_zero, add_zero]

/-- Cochrane (2023), (16.23)–(16.24), p. 373 (NI-6, converse): every solution of the observable
system is an equilibrium of EVERY regime `(φ, γ)`, with targets `i* = i`, `π* = π`, `v* = v`. -/
theorem obs_unifiedEq {ρ α M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α) (hα2 : α < 2)
    {us π i s v : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) (h : ObsFiscal 𝔼 ρ α us π i s v)
    (γ φ : ℝ) : UnifiedEq 𝔼 ρ α γ φ us i π π i s v v := by
  have hf : FiscalBlock 𝔼 ρ α γ us π π s v v :=
    ⟨h.2.1, h.2.1, rfl, fun t => by rw [h.2.2.2.1 t, sub_self, smul_zero, add_zero],
      h.2.2.2.2, h.2.2.2.2⟩
  refine ⟨⟨⟨h.1, h.2.2.1, fun t => by rw [sub_self, smul_zero, add_zero]⟩,
    ⟨h.1, h.2.2.1⟩⟩, hf, ?_⟩
  exact (tvc_iff 𝔼 hρ0 hρ1 hα0 hα2 hus hf).mpr fun t ω => by simp

/-- Cochrane (2023), p. 373: the observable processes `(π, i, s, v)` of the equilibria of the
regime `(φ, γ)`. -/
def eqObs (ρ α γ φ : ℝ) (us : ℕ → Ω → ℝ) :
    Set ((ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ)) :=
  {o | ∃ istar pistar vs, UnifiedEq 𝔼 ρ α γ φ us istar pistar o.1 o.2.1 o.2.2.1 o.2.2.2 vs}

/-- Cochrane (2023), (16.23)–(16.24), p. 373 (NI-6): for every regime, the set of observable
equilibrium processes is exactly the solution set of (16.23)–(16.24). -/
theorem eqObs_eq {ρ α M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α) (hα2 : α < 2)
    {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) (γ φ : ℝ) :
    eqObs 𝔼 ρ α γ φ us = {o | ObsFiscal 𝔼 ρ α us o.1 o.2.1 o.2.2.1 o.2.2.2} := by
  ext ⟨π, i, s, v⟩
  constructor
  · rintro ⟨istar, pistar, vs, h⟩
    exact unifiedEq_obs 𝔼 hρ0 hρ1 hα0 hα2 hus h
  · intro h
    exact ⟨i, π, v, obs_unifiedEq 𝔼 hρ0 hρ1 hα0 hα2 hus h γ φ⟩

/-- Cochrane (2023), p. 373 ("the regimes are observationally equivalent"): the
active-fiscal regime (`φ = 0`, `γ = 0`) and the active-money regime (`φ > 1`, `γ = α`), and
indeed any two regimes, have the same observable equilibrium processes. -/
theorem regimes_observationally_equivalent {ρ α M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hα0 : 0 < α) (hα2 : α < 2) {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M)
    (γ₁ φ₁ γ₂ φ₂ : ℝ) : eqObs 𝔼 ρ α γ₁ φ₁ us = eqObs 𝔼 ρ α γ₂ φ₂ us := by
  rw [eqObs_eq 𝔼 hρ0 hρ1 hα0 hα2 hus, eqObs_eq 𝔼 hρ0 hρ1 hα0 hα2 hus]

/-- Cochrane (2023), p. 373 ("The fiscal parameter `γ` is just as unidentified as the monetary
parameter `φ`"): whenever an observed process is an equilibrium of one regime, it is an
equilibrium of every other regime. -/
theorem gamma_phi_not_identified {ρ α M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α)
    (hα2 : α < 2) {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) {γ₁ φ₁ : ℝ}
    {o : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ)}
    (ho : o ∈ eqObs 𝔼 ρ α γ₁ φ₁ us) (γ₂ φ₂ : ℝ) : o ∈ eqObs 𝔼 ρ α γ₂ φ₂ us := by
  rwa [regimes_observationally_equivalent 𝔼 hρ0 hρ1 hα0 hα2 hus γ₁ φ₁ γ₂ φ₂] at ho

/-- Cochrane (2023), (16.23)–(16.24), p. 373: for an adapted bounded surplus disturbance the
observable equilibrium set of every regime is nonempty (zero inflation and interest rate, with
the debt and surplus paths that (16.24) implies from `v_0 = 0`). -/
theorem eqObs_nonempty {ρ α M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α) (hα2 : α < 2)
    {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) (husa : 𝔼.Adapted us) (γ φ : ℝ) :
    (eqObs 𝔼 ρ α γ φ us).Nonempty := by
  have hb := fiscalPath_block 𝔼 hρ0.ne' α α (us := us) (pistar := 0) (π := 0) (v0 := 0) husa
    (map_zero _)
  have hgap := (gap_zero_iff 𝔼 hρ0.ne' hb).mpr fun _ => rfl
  refine ⟨(0, 0, fiscalSurplus 𝔼 ρ α α us 0 0 0, fun t => (fiscalPath 𝔼 ρ α α us 0 0 0 t).1),
    ?_⟩
  rw [eqObs_eq 𝔼 hρ0 hρ1 hα0 hα2 hus γ φ]
  refine ⟨fun t => map_zero _, hb.1, fun t => (map_zero _).symm, fun t => ?_, hb.2.2.2.2.2⟩
  dsimp only
  rw [hb.2.2.2.1 t]
  dsimp only
  rw [hgap t, sub_self, smul_zero, add_zero]

/-- Cochrane (2023), p. 373 and §16.10.7, p. 394: the class of unified-model specifications
`(γ, φ, observation)` whose observation is an equilibrium of the regime `(φ, γ)`. -/
def unifiedClass (ρ α : ℝ) (us : ℕ → Ω → ℝ) :
    Set (ℝ × ℝ × ((ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ))) :=
  {m | m.2.2 ∈ eqObs 𝔼 ρ α m.1 m.2.1 us}

/-- Cochrane (2023), p. 373 ("The fiscal parameter `γ` is just as unidentified as the monetary
parameter `φ`") and §16.10.7, p. 394 ("The argument admittedly cuts both ways"): neither `γ`
nor `φ` is identified, hence neither is learnable from equilibrium time series. -/
theorem gamma_phi_not_learnable {ρ α M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α)
    (hα2 : α < 2) {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) (husa : 𝔼.Adapted us) :
    ¬ IdentifiedOn (unifiedClass 𝔼 ρ α us) (fun m => m.2.2) Prod.fst ∧
      ¬ IdentifiedOn (unifiedClass 𝔼 ρ α us) (fun m => m.2.2) (fun m => m.2.1) := by
  obtain ⟨o, ho⟩ := eqObs_nonempty 𝔼 hρ0 hρ1 hα0 hα2 hus husa 0 0
  have hmem : ∀ γ φ : ℝ, ((γ, φ, o) : ℝ × ℝ × _) ∈ unifiedClass 𝔼 ρ α us := fun γ φ =>
    gamma_phi_not_identified 𝔼 hρ0 hρ1 hα0 hα2 hus ho γ φ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h _ (hmem 0 0) _ (hmem 1 0) rfl
    norm_num at this
  · have := h _ (hmem 0 0) _ (hmem 0 1) rfl
    norm_num at this

/-! ### Survey error E6 on a genuine coin-flip tree -/

/-- Cochrane (2023), p. 364 (uncertainty example for E6): the coin-flip tree has a nonzero
innovation, `ΔE_1 ε_1 = ±1`. -/
theorem coin_innov_ne_zero :
    innov ExpectationsFiniteTree.coinSystem 0 (ExpectationsFiniteTree.coinShock 1) ≠ 0 := by
  intro h
  have e := congrFun h (true, true)
  rw [Innovation.innov, coinShock_adapted 1, ExpectationsFiniteTree.coinShock_mean_zero 0] at e
  simp [ExpectationsFiniteTree.coinShock] at e

/-- Cochrane (2023), p. 373 (survey error E6): on the coin-flip tree, fiscal policy
(16.20)–(16.22) is passive iff `γ = α`. -/
theorem coin_passive_iff {ρ α γ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α)
    (hα2 : α < 2) {us : ℕ → Bool × Bool → ℝ} (hus : ∀ t ω, |us t ω| ≤ M)
    (husa : ExpectationsFiniteTree.coinSystem.Adapted us) :
    FiscalPassive ExpectationsFiniteTree.coinSystem ρ α γ us ↔ γ = α :=
  passive_iff _ hρ0 hρ1 hα0 hα2 hus husa ⟨_, 0, coin_innov_ne_zero⟩

/-- Cochrane (2023), p. 373 (survey error E6): the printed active-money/passive-fiscal regime
"`γ > 0`" is not passive in general. With `ρ = α = 1/2` and `γ = 1` (so `γ > 0`, and also
`0 < γ < 2`) fiscal policy on the coin-flip tree is not passive. -/
theorem e6_printed_fails :
    ¬ FiscalPassive ExpectationsFiniteTree.coinSystem (1 / 2) (1 / 2) 1 0 := by
  rw [coin_passive_iff (M := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ _ => by simp) (fun t => by simp)]
  norm_num

/-- Cochrane (2023), p. 373 (survey error E6): the off-target sunspot path
`π_{t+1} = φ π_t + ε_{t+1}`, `π_0 = 0`, on the coin-flip tree, with targets `π* = i* = 0`. -/
noncomputable def coinSunspot (φ : ℝ) : ℕ → Bool × Bool → ℝ :=
  ForwardSolution.sunspotFamily φ⁻¹ 0 ExpectationsFiniteTree.coinShock 0

/-- Cochrane (2023), p. 373 (survey error E6): for every `φ ≠ 0` the sunspot path solves the
monetary block with targets zero: it is a legitimate off-target monetary path. -/
theorem coinSunspot_monetary {φ : ℝ} (hφ : φ ≠ 0) :
    MonetaryBlock ExpectationsFiniteTree.coinSystem φ 0 0 (coinSunspot φ)
      (fisherRate ExpectationsFiniteTree.coinSystem (coinSunspot φ)) := by
  have hz0 : ExpectationsFiniteTree.coinSystem.E 0 (0 : Bool × Bool → ℝ) = 0 := map_zero _
  have hua : ExpectationsFiniteTree.coinSystem.Adapted (0 : ℕ → Bool × Bool → ℝ) :=
    fun t => map_zero _
  have hsol := ForwardSolution.sunspotFamily_solves ExpectationsFiniteTree.coinSystem
    (inv_ne_zero hφ) hz0 hua coinShock_adapted ExpectationsFiniteTree.coinShock_mean_zero
  have had := ForwardSolution.sunspotFamily_adapted ExpectationsFiniteTree.coinSystem
    (a := φ⁻¹) hz0 hua coinShock_adapted
  refine ⟨⟨had, fun _ => rfl, fun t => ?_⟩, ⟨fun t => map_zero _, fun t => (map_zero _).symm⟩⟩
  have e := hsol t
  simp only [Pi.zero_apply, add_zero] at e
  simp only [fisherRate, coinSunspot, Pi.zero_apply, zero_add, sub_zero]
  conv_rhs => rw [e]
  rw [smul_smul, mul_inv_cancel₀ hφ, one_smul]

/-- Cochrane (2023), p. 373 (survey error E6): for every `φ ≠ 0` and every `γ ≠ α`, the
off-target sunspot path, with the debt and surplus it implies through (16.20)–(16.22),
violates the transversality condition. So with `γ ≠ α` the fiscal rule itself rules out
off-target paths: it is not passive. -/
theorem e6_counterexample {ρ α γ φ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α)
    (hα2 : α < 2) (hγ : γ ≠ α) (hφ : φ ≠ 0) :
    MonetaryBlock ExpectationsFiniteTree.coinSystem φ 0 0 (coinSunspot φ)
        (fisherRate ExpectationsFiniteTree.coinSystem (coinSunspot φ)) ∧
      FiscalBlock ExpectationsFiniteTree.coinSystem ρ α γ 0 0 (coinSunspot φ)
        (fiscalSurplus ExpectationsFiniteTree.coinSystem ρ α γ 0 0 (coinSunspot φ) 0)
        (fun t => (fiscalPath ExpectationsFiniteTree.coinSystem ρ α γ 0 0 (coinSunspot φ) 0 t).1)
        (fun t => (fiscalPath ExpectationsFiniteTree.coinSystem ρ α γ 0 0 (coinSunspot φ) 0 t).2)
        ∧ ¬ TVC ExpectationsFiniteTree.coinSystem ρ (fun t =>
          (fiscalPath ExpectationsFiniteTree.coinSystem ρ α γ 0 0 (coinSunspot φ) 0 t).1) := by
  have hb := fiscalPath_block ExpectationsFiniteTree.coinSystem hρ0.ne' α γ
    (us := 0) (pistar := 0) (π := coinSunspot φ) (v0 := 0) (fun t => by simp) (map_zero _)
  refine ⟨coinSunspot_monetary hφ, hb, fun htvc => ?_⟩
  rw [tvc_iff _ (M := 0) hρ0 hρ1 hα0 hα2 (fun _ _ => by simp) hb] at htvc
  have hgap : ∀ t, (fiscalPath ExpectationsFiniteTree.coinSystem ρ α γ 0 0 (coinSunspot φ) 0 t).1
      = (fiscalPath ExpectationsFiniteTree.coinSystem ρ α γ 0 0 (coinSunspot φ) 0 t).2 :=
    fun t => funext fun ω => by
      rcases mul_eq_zero.mp (htvc t ω) with h0 | h0
      · exact absurd (sub_eq_zero.mp h0).symm hγ
      · exact sub_eq_zero.mp h0
  have hd := (gap_zero_iff _ hρ0.ne' hb).mp hgap 0
  have h1 : coinSunspot φ 1 = ExpectationsFiniteTree.coinShock 1 := by
    funext ω
    simp [coinSunspot, ForwardSolution.sunspotFamily]
  have hz : innov ExpectationsFiniteTree.coinSystem 0 ((0 : ℕ → Bool × Bool → ℝ) (0 + 1)) = 0 :=
    by simp [Innovation.innov]
  rw [hz, h1] at hd
  exact coin_innov_ne_zero hd

end Cochrane.NewKeynesianSelection.ObservationalEquivalence
