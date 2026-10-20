/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.Responses
import NewKeynesianSelection.SelectionPatches
import NewKeynesianSelection.SimsTinyFiscal

/-!
# Links between the Chapter 16 modules

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 16, pp. 363–396, with §2.6
(p. 40). The chapter was formalised in three concurrent chains, and several book objects appear
in more than one of them with different (but equivalent) definitions. This module proves the
equivalences and the cross-chain connections. Two statements of Woodford (2003) are restated
here (not imported) to connect Cochrane's claims to them.

## Main results

* The §16.1 model (pp. 363–365): `nkEq_iff_nkModel` (`Identification.NKEq` is
  `SimplestModel.NKModel` plus adaptedness), `selected_iff_eq_fwdSol` (the new-Keynesian
  selection `Identification.Selected` is the forward solution (16.6) `SimplestModel.fwdSol`),
  `ar1_selected_eq_fwdSol` ((16.9) in both forms).
* NI-5 and the fiscal-theory rule equilibrium (pp. 40, 364, 372): `ftplEq_iff_ruleModel`,
  `ftplEq_eq_ruleSol`, `nk3Eq_iff_ruleModel` ((16.1)–(16.3) is the model (2.20)–(2.22) with
  `θ = φ`), `nk_is_ruleModel` (NI-5 in the `FTPLSimple` form); `ruleModel_eq164`,
  `rule_expected_path_of_eq164` (§16.4 and Chapter 12, P6, p. 327).
* NI-4 and the King form (pp. 366–367, 371): `king_disturbance_eq_toU`, `kingEq_iff_kingRule`,
  `king_bounded_eq_of_kingForm`.
* The Wicksellian rule (16.8), p. 365, and Woodford (2003) Ch. 2, eq. (1.36) and
  Proposition 2.3 (pp. 81–82): `WoodfordReduced`, `woodfordReduced_iff_eq164`,
  `wicksellModel_iff_woodford`, `woodford_prop_2_3_linear`, `woodford_determinate_iff`.
* E6 (p. 373) and Woodford (2003) Ch. 4, (4.5) and Proposition 4.11 (pp. 312–314):
  `WoodfordDebt45`, `fiscalBlock_debt45`, `e6_passive_iff_woodford45`, `woodford_ricardian_iff`,
  `passive_of_ricardian`, `passive_not_ricardian`.
* §16.3 and §16.8 (pp. 368, 377–379, (16.30)): `isEquilibrium_hyper` (an equilibrium of the full
  model of §16.8 satisfies the §16.3 fiscal block), `passive_tvc_of_gamma`.
* Transversality conditions: `tvc_pf_iff` (the expectation-system TVC of (16.20)–(16.22) under
  perfect foresight is the §16.3 TVC), `stoch_tvc_obs`.
-/

namespace Cochrane.NewKeynesianSelection.Links

open Filter Topology
open Innovation (innov IsShock)
open SimplestModel (Eq164 ar1Pi)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The §16.1 model and its selected solution -/

/-- Cochrane (2023), (16.1)–(16.2), p. 364: `Identification.NKEq` is `SimplestModel.NKModel`
together with adaptedness of inflation. -/
theorem nkEq_iff_nkModel (φ : ℝ) (u π i : ℕ → Ω → ℝ) :
    Identification.NKEq 𝔼 φ u π i ↔ 𝔼.Adapted π ∧ SimplestModel.NKModel 𝔼 φ u i π :=
  ⟨fun h => ⟨h.1, fun t => ⟨h.2.1 t, h.2.2 t⟩⟩,
    fun h => ⟨h.1, fun t => (h.2 t).1, fun t => (h.2 t).2⟩⟩

/-- Cochrane (2023), (16.6), p. 364: for `|φ| > 1` and a bounded adapted disturbance, the
new-Keynesian selection of the identification chain (`Identification.Selected`: the unique
bounded adapted solution of (16.4)) is exactly the forward solution `SimplestModel.fwdSol`. -/
theorem selected_iff_eq_fwdSol {φ M : ℝ} (hφ : 1 < |φ|) {u π : ℕ → Ω → ℝ}
    (hM : ∀ t ω, |u t ω| ≤ M) (hu : 𝔼.Adapted u) :
    Identification.Selected 𝔼 φ u π ↔ π = SimplestModel.fwdSol 𝔼 φ u := by
  obtain ⟨hs, hb, ha, huniq⟩ := SimplestModel.fwdSol_existsUnique 𝔼 hφ hM hu
  constructor
  · intro h
    exact huniq π h.2.2.1 h.1
  · rintro rfl
    exact Identification.selected_of 𝔼 hφ hb ha hs

/-- Cochrane (2023), (16.9), p. 365: the two forms of the AR(1) result agree. For `|φ| > 1`,
`φ ≠ η` and a bounded AR(1) disturbance, the forward solution (16.6) is `π = −u/(φ − η)`, and it
is the selected equilibrium. -/
theorem ar1_selected_eq_fwdSol {φ η M : ℝ} (hφ : 1 < |φ|) (hφη : φ ≠ η) {u ε : ℕ → Ω → ℝ}
    (h : Identification.AR1 𝔼 η u ε) (hM : ∀ t ω, |u t ω| ≤ M) :
    SimplestModel.fwdSol 𝔼 φ u = ar1Pi φ η u ∧
      Identification.Selected 𝔼 φ u (SimplestModel.fwdSol 𝔼 φ u) := by
  have e := SimplestModel.ar1_solution 𝔼 hφ hφη hM (h.isAR1 𝔼)
  refine ⟨e, ?_⟩
  rw [e]
  exact Identification.ar1_selected 𝔼 hφ hφη h ⟨M, hM⟩

/-! ### NI-5 and the fiscal-theory rule equilibrium -/

/-- Cochrane (2023), (2.20)–(2.22), p. 40: the fiscal-theory equilibrium of the identification
chain (`Identification.FTPLEq`) is the rule model `FTPLSimple.RuleModel` with adapted inflation. -/
theorem ftplEq_iff_ruleModel (θ : ℝ) (u εs π i : ℕ → Ω → ℝ) :
    Identification.FTPLEq 𝔼 θ u εs π i ↔ 𝔼.Adapted π ∧ FTPLSimple.RuleModel 𝔼 θ i u εs π :=
  ⟨fun h => ⟨h.1, fun t => ⟨h.2.1 t, h.2.2.1 t, h.2.2.2 t⟩⟩,
    fun h => ⟨h.1, fun t => (h.2 t).1, fun t => (h.2 t).2.1, fun t => (h.2 t).2.2⟩⟩

/-- Cochrane (2023), (2.25), p. 40: given the fiscal shock, every fiscal-theory equilibrium is the
path `FTPLSimple.ruleSol` from its own date-0 inflation (the solution of
`FTPLSimple.rule_existsUnique`). -/
theorem ftplEq_eq_ruleSol {θ : ℝ} {u εs π i : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u)
    (hε : IsShock 𝔼 εs) (h : Identification.FTPLEq 𝔼 θ u εs π i) :
    π = FTPLSimple.ruleSol θ u εs (π 0) := by
  obtain ⟨q, -, huniq⟩ := FTPLSimple.rule_existsUnique 𝔼 θ (h.1 0) hu hε
  have h1 := huniq (π, i) ⟨h.1, rfl, ((ftplEq_iff_ruleModel 𝔼 θ u εs π i).mp h).2⟩
  have hs := ObservationalEquivalence.ftpl_exists 𝔼 θ hu hε (h.1 0)
  have h2 := huniq (FTPLSimple.ruleSol θ u εs (π 0),
    Identification.fisherRate 𝔼 (FTPLSimple.ruleSol θ u εs (π 0)))
    ⟨hs.1, rfl, ((ftplEq_iff_ruleModel 𝔼 θ u εs _ _).mp hs).2⟩
  exact congrArg Prod.fst (h1.trans h2.symm)

/-- Cochrane (2023), (16.1)–(16.3), p. 364 ("the same set of equations as the simplest fiscal
theory of monetary policy model"): the full new-Keynesian model `Responses.NK3Eq` is the
fiscal-theory rule model (2.20)–(2.22) with `θ = φ`, for adapted inflation. -/
theorem nk3Eq_iff_ruleModel (φ : ℝ) (u εs π i : ℕ → Ω → ℝ) :
    Responses.NK3Eq 𝔼 φ u εs π i ↔ 𝔼.Adapted π ∧ FTPLSimple.RuleModel 𝔼 φ i u εs π := by
  constructor
  · rintro ⟨h, h3⟩
    exact ⟨h.1, fun t => ⟨h.2.1 t, h3 t, h.2.2 t⟩⟩
  · rintro ⟨ha, h⟩
    exact ⟨⟨ha, fun t => (h t).1, fun t => (h t).2.2⟩, fun t => (h t).2.1⟩

/-- Cochrane (2023), p. 372 (NI-5) in the form of §2.6: the selected AR(1) new-Keynesian
equilibrium is the fiscal-theory rule equilibrium `FTPLSimple.RuleModel` with `θ = η`, no
monetary disturbance and fiscal shock `ε_Σs = ε_i/(φ − η)`, and it is the path
`FTPLSimple.ruleSol` (2.25). -/
theorem nk_is_ruleModel (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : Identification.AR1 𝔼 η u ε) :
    FTPLSimple.RuleModel 𝔼 η (Identification.fisherRate 𝔼 (ar1Pi φ η u)) 0
        (fun t => (φ - η)⁻¹ • ε t) (ar1Pi φ η u) ∧
      FTPLSimple.ruleSol η 0 (fun t => (φ - η)⁻¹ • ε t) (ar1Pi φ η u 0) = ar1Pi φ η u :=
  ⟨((ftplEq_iff_ruleModel 𝔼 _ _ _ _ _).mp (ObservationalEquivalence.nk_is_ftpl 𝔼 φ h)).2,
    ObservationalEquivalence.nk_eq_ftpl_path 𝔼 φ h⟩

/-- Cochrane (2023), (2.20)–(2.24), p. 40, and (16.4), p. 364: every solution of the
fiscal-theory rule model satisfies (16.4) with `φ = θ`, so the §16.4 results on `E_t π_{t+j}`
(`Hyperinflation.expected_path`, `stable_of_abs_lt_one`, `unstable_of_one_lt_abs`) apply to the
Chapter 12 rule equilibria of `FTPLSimple` (`rule_expected_path`, `rule_stable`,
`rule_determinate_unstable`). -/
theorem ruleModel_eq164 {θ : ℝ} {i u ε π : ℕ → Ω → ℝ} (h : FTPLSimple.RuleModel 𝔼 θ i u ε π) :
    Eq164 𝔼 θ u π :=
  fun t => (h t).1.symm.trans (h t).2.2

/-- Cochrane (2023), p. 327 (Chapter 12, P6) and §16.4, p. 369: the expected-path result of the
fiscal-theory rule model, `E_t π_{t+j} = φʲ π_t`, re-derived from §16.4's
`Hyperinflation.expected_path` through `ruleModel_eq164`. -/
theorem rule_expected_path_of_eq164 {φ : ℝ} {i ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hm : FTPLSimple.RuleModel 𝔼 φ i 0 ε π) (t j : ℕ) : 𝔼.E t (π (t + j)) = φ ^ j • π t :=
  Hyperinflation.expected_path 𝔼 hπ (ruleModel_eq164 𝔼 hm) t j

/-! ### NI-4 and the King form -/

/-- Cochrane (2023), (16.13), pp. 366–367: with consistent targets `i*_t = E_t π*_{t+1}`, the
disturbance `u = i* − φπ*` of `Responses.king_iff_nk` is King's translation `KingForm.toU`. -/
theorem king_disturbance_eq_toU (φ : ℝ) {istar pistar : ℕ → Ω → ℝ}
    (hc : Identification.TargetsConsistent 𝔼 istar pistar) :
    (fun t => istar t - φ • pistar t) = KingForm.toU 𝔼 φ pistar := by
  funext t
  rw [KingForm.toU, hc.2 t]

/-- Cochrane (2023), (16.12), p. 366, and (16.19), p. 371: with consistent targets, the
King-form equilibrium of the identification chain (`Identification.KingEq`) is adapted inflation
with the Fisher equation and King's rule `KingForm.KingRule`. -/
theorem kingEq_iff_kingRule (φ : ℝ) {istar pistar π i : ℕ → Ω → ℝ}
    (hc : Identification.TargetsConsistent 𝔼 istar pistar) :
    Identification.KingEq 𝔼 φ istar pistar π i ↔
      𝔼.Adapted π ∧ (∀ t, i t = 𝔼.E t (π (t + 1))) ∧ KingForm.KingRule 𝔼 φ pistar i π := by
  unfold Identification.KingEq KingForm.KingRule
  refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun t => ?_
  rw [hc.2 t]

/-- Cochrane (2023), (16.14), p. 367, and NI-4 (16.19), p. 371: the identification chain's
`king_bounded_eq` follows from the King-form chain's `KingForm.eq_target_of_bounded`: for
`|φ| > 1` and bounded consistent targets every bounded King-form equilibrium is `π = π*`,
`i = i*`. -/
theorem king_bounded_eq_of_kingForm {φ : ℝ} (hφ : 1 < |φ|) {istar pistar π i : ℕ → Ω → ℝ}
    (hc : Identification.TargetsConsistent 𝔼 istar pistar) (hbs : BoundedProc pistar)
    (h : Identification.KingEq 𝔼 φ istar pistar π i) (hb : BoundedProc π) :
    π = pistar ∧ i = istar := by
  obtain ⟨-, hf, hk⟩ := (kingEq_iff_kingRule 𝔼 φ hc).mp h
  have hπ : π = pistar := KingForm.eq_target_of_bounded 𝔼 hφ hbs hc.1 hb fun t => by
    rw [map_sub, KingForm.expected_set_by_rate 𝔼 hf hk t]
    abel
  refine ⟨hπ, funext fun t => ?_⟩
  rw [h.2.2 t, hπ, sub_self, smul_zero, add_zero]

/-! ### The Wicksellian rule (16.8) and Woodford's Proposition 2.3 -/

/-- Cochrane (2023), (16.8), p. 365, and Woodford (2003), eq. (1.36), p. 81 (restated from the
Woodford Chapter 2 project): Woodford's reduced price-level equation
`(1 + φ_p) P̂_t = E_t P̂_{t+1} + r̂_t + E_t π*_{t+1} − ν_t` for the log price gap `P̂`. -/
def WoodfordReduced (φp : ℝ) (r pis ν Ph : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (1 + φp) • Ph t = 𝔼.E t (Ph (t + 1)) + r t + 𝔼.E t (pis (t + 1)) - ν t

/-- Cochrane (2023), (16.8) and (16.4), pp. 364–365: Woodford's (1.36) is Cochrane's equation
(16.4) for the price gap, `E_t P̂_{t+1} = (1 + φ_p) P̂_t + u_t`, with the disturbance
`u_t = ν_t − r̂_t − E_t π*_{t+1}`. -/
theorem woodfordReduced_iff_eq164 (φp : ℝ) (r pis ν Ph : ℕ → Ω → ℝ) :
    WoodfordReduced 𝔼 φp r pis ν Ph ↔
      Eq164 𝔼 (1 + φp) (fun t => ν t - r t - 𝔼.E t (pis (t + 1))) Ph := by
  refine forall_congr' fun t => ?_
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), eq. (16.8), p. 365: Cochrane's Wicksellian model (constant target `p*`, no
real-rate variation) is Woodford's (1.36) with `r̂ = 0`, `π* = 0`, `ν = u` for the price gap
`p − p*`, together with the rule. -/
theorem wicksellModel_iff_woodford {φp pstar : ℝ} {u i p : ℕ → Ω → ℝ} :
    SimplestModel.WicksellModel 𝔼 φp pstar u i p ↔
      (∀ t, i t = φp • (p t - fun _ => pstar) + u t) ∧
        WoodfordReduced 𝔼 φp 0 0 u (fun t => p t - fun _ => pstar) := by
  rw [SimplestModel.wicksell_iff, woodfordReduced_iff_eq164]
  refine and_congr_right fun _ => ?_
  have e : (fun t => u t - (0 : ℕ → Ω → ℝ) t - 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1))) = u := by
    funext t
    simp
  rw [e]

/-- Woodford (2003), Proposition 2.3 (linear core), pp. 81–82, restated from the Woodford
Chapter 2 project and derived from Cochrane (2023), (16.6), p. 364 (`SimplestModel.fwdSol`): for
`φ_p > 0` and bounded `{r̂, π*, ν}` with `r̂`, `ν` adapted, (1.36) has exactly one bounded
adapted solution. Cochrane's (16.8) is the case `r̂ = π* = 0`. -/
theorem woodford_prop_2_3_linear {φp : ℝ} (hφ : 0 < φp) {r pis ν : ℕ → Ω → ℝ}
    (hrb : BoundedProc r) (hpb : BoundedProc pis) (hνb : BoundedProc ν) (hra : 𝔼.Adapted r)
    (hνa : 𝔼.Adapted ν) :
    ∃! Ph, BoundedProc Ph ∧ 𝔼.Adapted Ph ∧ WoodfordReduced 𝔼 φp r pis ν Ph := by
  obtain ⟨Mr, hr⟩ := hrb
  obtain ⟨Mp, hp⟩ := hpb
  obtain ⟨Mν, hν⟩ := hνb
  have h1 : 1 < |1 + φp| := by rw [abs_of_pos (by linarith)]; linarith
  set u : ℕ → Ω → ℝ := fun t => ν t - r t - 𝔼.E t (pis (t + 1)) with hu
  have huM : ∀ t ω, |u t ω| ≤ Mν + Mr + Mp := fun t ω => by
    simp only [hu, Pi.sub_apply]
    have := 𝔼.abs_E_le (hp (t + 1)) t ω
    calc |ν t ω - r t ω - 𝔼.E t (pis (t + 1)) ω|
        ≤ |ν t ω - r t ω| + |𝔼.E t (pis (t + 1)) ω| := abs_sub _ _
      _ ≤ |ν t ω| + |r t ω| + |𝔼.E t (pis (t + 1)) ω| := by gcongr; exact abs_sub _ _
      _ ≤ Mν + Mr + Mp := by linarith [hr t ω, hν t ω]
  have hua : 𝔼.Adapted u := fun t => by
    simp only [hu, map_sub, hra t, hνa t, 𝔼.E_E_self]
  obtain ⟨hs, hb, ha, huniq⟩ := SimplestModel.fwdSol_existsUnique 𝔼 h1 huM hua
  refine ⟨SimplestModel.fwdSol 𝔼 (1 + φp) u, ⟨hb, ha, (woodfordReduced_iff_eq164 𝔼 _ _ _ _ _).mpr
    hs⟩, fun Ph hP => huniq Ph ((woodfordReduced_iff_eq164 𝔼 _ _ _ _ _).mp hP.2.2) hP.1⟩

/-- Woodford (2003), Proposition 2.3, p. 82 (restated from the Woodford Chapter 2 project:
within `φ_p ≥ 0`, the log-linear system is determinate iff `φ_p > 0`), derived from Cochrane's
corrected determinacy condition for (16.8) (`SimplestModel.wicksell_determinate_iff`, survey E4:
`φ_p > 0` or `φ_p < −2`). -/
theorem woodford_determinate_iff [Nonempty Ω] {φp : ℝ} (hφ : 0 ≤ φp) :
    (∀ r pis ν : ℕ → Ω → ℝ, BoundedProc r → BoundedProc pis → BoundedProc ν → 𝔼.Adapted r →
      𝔼.Adapted ν → ∃! Ph, BoundedProc Ph ∧ WoodfordReduced 𝔼 φp r pis ν Ph) ↔ 0 < φp := by
  have hz : BoundedProc (0 : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
  have hza : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun _ => map_zero _
  have e0 : ∀ u : ℕ → Ω → ℝ,
      (fun t => u t - (0 : ℕ → Ω → ℝ) t - 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1))) = u := fun u => by
    funext t
    simp
  constructor
  · intro h
    have hdet : ∀ u : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u →
        ∃! x, BoundedProc x ∧ Eq164 𝔼 (1 + φp) u x := by
      intro u hub hua
      obtain ⟨x, hx, hxu⟩ := h 0 0 u hz hz hub hza hua
      refine ⟨x, ⟨hx.1, ?_⟩, fun y hy => hxu y ⟨hy.1, ?_⟩⟩
      · have := (woodfordReduced_iff_eq164 𝔼 φp 0 0 u x).mp hx.2
        rwa [e0] at this
      · rw [woodfordReduced_iff_eq164, e0]
        exact hy.2
    rcases (SimplestModel.wicksell_determinate_iff 𝔼 φp).mp hdet with h1 | h1
    · exact h1
    · linarith
  · intro hφ r pis ν hrb hpb hνb hra hνa
    obtain ⟨Ph, hP, huniq⟩ := woodford_prop_2_3_linear 𝔼 hφ hrb hpb hνb hra hνa
    refine ⟨Ph, ⟨hP.1, hP.2.2⟩, fun Q hQ => ?_⟩
    have h1 : 1 < |1 + φp| := by rw [abs_of_pos (by linarith)]; linarith
    exact SimplestModel.eq164_unique 𝔼 h1 ((woodfordReduced_iff_eq164 𝔼 _ _ _ _ _).mp hQ.2)
      ((woodfordReduced_iff_eq164 𝔼 _ _ _ _ _).mp hP.2.2) hQ.1 hP.1

/-! ### E6 and Woodford's Ricardian / non-Ricardian rules (Proposition 4.11) -/

/-- Woodford (2003), eq. (4.5), p. 313 (restated from the Woodford Chapter 4 project), used for
Cochrane (2023), (16.20)–(16.22), p. 373: the law of motion of real debt under a linear tax rule,
`d_{t+1} = β⁻¹[(1 − τ_b) d_t − (b̄ + τ_π) π_t + (1 − τ_g) G_t − τ_y Y_t] + (b̄ − β⁻¹τ_i) i_t
− β⁻¹ v_t`. -/
def WoodfordDebt45 (β bb τb τg τπ τy τi : ℝ) (d π G Y i v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, d (t + 1) = β⁻¹ • ((1 - τb) • d t - (bb + τπ) • π t + (1 - τg) • G t - τy • Y t) +
    (bb - β⁻¹ * τi) • i t - β⁻¹ • v t

/-- Cochrane (2023), (16.20)–(16.22), p. 373, with `γ = α`: the debt of the unified model follows
Woodford's tax-rule debt dynamics (4.5) with `β = ρ`, `τ_b = α`, `b̄ = 0`, `τ_π = 1` applied to
unexpected inflation `ΔE_{t+1} π_{t+1}`, no other inputs, and the fiscal disturbance
`v_t = u_{s,t+1}`. -/
theorem fiscalBlock_debt45 {ρ α : ℝ} (hρ : ρ ≠ 0) {us pistar π s v vs : ℕ → Ω → ℝ}
    (h : ObservationalEquivalence.FiscalBlock 𝔼 ρ α α us pistar π s v vs) :
    WoodfordDebt45 ρ 0 α 0 1 0 0 v (fun t => innov 𝔼 t (π (t + 1))) 0 0 0
      (fun t => us (t + 1)) := by
  intro t
  have e := ObservationalEquivalence.v_dyn 𝔼 h t
  rw [sub_self, zero_smul, sub_zero] at e
  funext ω
  have e' := congrFun e ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at e' ⊢
  field_simp
  linarith

/-- Cochrane (2023), p. 373 (survey error E6, `ObservationalEquivalence.passive_iff`) in
Woodford's terms: on an expectation system with a nonzero innovation, fiscal policy
(16.20)–(16.22) is passive iff `γ = α`, and then real debt follows Woodford's (4.5) with
`τ_b = α`. -/
theorem e6_passive_iff_woodford45 {ρ α γ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα0 : 0 < α)
    (hα2 : α < 2) {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) (husa : 𝔼.Adapted us)
    (hnt : ∃ (x : ℕ → Ω → ℝ) (t : ℕ), innov 𝔼 t (x (t + 1)) ≠ 0) :
    (ObservationalEquivalence.FiscalPassive 𝔼 ρ α γ us ↔ γ = α) ∧
      ∀ pistar π s v vs : ℕ → Ω → ℝ,
        ObservationalEquivalence.FiscalBlock 𝔼 ρ α α us pistar π s v vs →
        WoodfordDebt45 ρ 0 α 0 1 0 0 v (fun t => innov 𝔼 t (π (t + 1))) 0 0 0
          (fun t => us (t + 1)) :=
  ⟨ObservationalEquivalence.passive_iff 𝔼 hρ0 hρ1 hα0 hα2 hus husa hnt,
    fun _ _ _ _ _ h => fiscalBlock_debt45 𝔼 hρ0.ne' h⟩

/-- Woodford (2003), p. 314 (restated from the Woodford Chapter 4 project), for Cochrane (2023),
p. 373: for `0 < β` and `τ_b ≤ 1`, Woodford's locally-Ricardian condition `|β⁻¹(1 − τ_b)| < 1`
(Proposition 4.11's dividing line) holds iff `τ_b > 1 − β`. -/
theorem woodford_ricardian_iff {β τb : ℝ} (hβ : 0 < β) (hτ : τb ≤ 1) :
    |β⁻¹ * (1 - τb)| < 1 ↔ 1 - β < τb := by
  rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hβ.le) (by linarith)), ← div_eq_inv_mul,
    div_lt_one hβ]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 373, and Woodford (2003), Proposition 4.11, p. 314: a surplus rule that is
locally Ricardian in Woodford's sense (`|ρ⁻¹(1 − α)| < 1`, with `γ = α`) is passive in Cochrane's
transversality sense. -/
theorem passive_of_ricardian {ρ α M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hR : |ρ⁻¹ * (1 - α)| < 1) {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) :
    ObservationalEquivalence.FiscalPassive 𝔼 ρ α α us := by
  have h1 : |1 - α| < ρ := by
    have e : |1 - α| = ρ * |ρ⁻¹ * (1 - α)| := by
      rw [abs_mul, abs_inv, abs_of_pos hρ0, ← mul_assoc, mul_inv_cancel₀ hρ0.ne', one_mul]
    rw [e]
    calc ρ * |ρ⁻¹ * (1 - α)| < ρ * 1 := mul_lt_mul_of_pos_left hR hρ0
      _ = ρ := mul_one ρ
  have h2 := abs_lt.mp h1
  exact ObservationalEquivalence.passive_of_eq 𝔼 hρ0 hρ1 (by linarith) (by linarith) hus

/-- Cochrane (2023), p. 373, and Woodford (2003), Proposition 4.11, p. 314: the converse fails —
Cochrane's passivity (the transversality condition along every path) is weaker than Woodford's
local Ricardianness (bounded debt). With `ρ = 1/2` and `γ = α = 1/4` fiscal policy is passive,
yet `|ρ⁻¹(1 − α)| = 3/2 > 1`. -/
theorem passive_not_ricardian {M : ℝ} {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) :
    ObservationalEquivalence.FiscalPassive 𝔼 (1 / 2) (1 / 4) (1 / 4) us ∧
      ¬ |(1 / 2 : ℝ)⁻¹ * (1 - 1 / 4)| < 1 := by
  refine ⟨ObservationalEquivalence.passive_of_eq 𝔼 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hus, ?_⟩
  norm_num [abs_of_pos]

/-! ### §16.3 and §16.8: the fiscal block -/

/-- Cochrane (2023), §16.8, pp. 377–379, and §16.3, p. 368: every perfect-foresight equilibrium
of the full model of §16.8 (`LowerBound.IsEquilibrium`) satisfies the fiscal block restated in
§16.3: the Fisher equation `FisherPF`, the flow condition `Flow`, the valuation equation
(16.26) `Valuation` and the transversality condition `TVC`. -/
theorem isEquilibrium_hyper {r : ℝ} (hr : 0 < 1 + r) {Φ : ℝ → ℝ} {Pm1 : ℝ} {P i s D : ℕ → ℝ}
    (h : LowerBound.IsEquilibrium r Φ Pm1 P i s D) :
    Hyperinflation.FisherPF r P i ∧ Hyperinflation.Flow P D i s ∧
      Hyperinflation.Valuation r P D s ∧ Hyperinflation.TVC r P D := by
  have hdyn := LowerBound.equilibrium_dynamics hr h
  obtain ⟨-, hP, hi, hfis, -, hflow, hval⟩ := h
  refine ⟨fun t => ?_, hflow, hval, ?_⟩
  · have e := hfis t
    have h1 : 0 < 1 + i t := by linarith [hi t]
    have h2 := (hP t).ne'
    have h3 := (hP (t + 1)).ne'
    field_simp at e ⊢
    linarith
  · unfold Hyperinflation.TVC
    simpa using hdyn.2.2.2 0

/-- Cochrane (2023), p. 379 ("a specific version of the specification `s_t = γ(B_{t−1}/P_t)` that
produces passive fiscal policy") and §16.3, p. 368: the transversality condition of
`Hyperinflation.passive_tvc` also follows from the §16.8 criterion
`LowerBound.passive_gamma_tvc_iff` with `γ = r/(1 + r) ∈ (0, 2)`. -/
theorem passive_tvc_of_gamma {r : ℝ} (hr : 0 < r) {P D i s : ℕ → ℝ} (hP : ∀ t, 0 < P t)
    (hF : Hyperinflation.FisherPF r P i) (hflow : Hyperinflation.Flow P D i s)
    (hpas : Hyperinflation.PassiveRule r P D s) : Hyperinflation.TVC r P D := by
  have h1 : 0 < 1 + r := by linarith
  have hb : ∀ t, D (t + 1) / P (t + 1) =
      (1 + r) * (D t / P t - r / (1 + r) * (D t / P t)) := fun t => by
    rw [Hyperinflation.real_debt_flow h1 hP hF hflow t, hpas t]
  exact (LowerBound.passive_gamma_tvc_iff h1).mpr (LowerBound.passive_coefficient_mem hr) _ hb

/-! ### Transversality conditions -/

/-- Cochrane (2023), p. 137, p. 368 and p. 373: the expectation-system transversality condition
of the unified model (`ObservationalEquivalence.TVC`, `ρ^T E_t v_{t+T} → 0` at every date),
under perfect foresight with `ρ = 1/(1 + r)` and `v_t = B_{t−1}/P_t`, is the §16.3 condition
`Hyperinflation.TVC` (`(1 + r)^{−T} B_{T−1}/P_T → 0`): the date-0 limit implies the limit at
every date. -/
theorem tvc_pf_iff {r : ℝ} (hr : 0 < 1 + r) (P D : ℕ → ℝ) :
    ObservationalEquivalence.TVC perfectForesight (1 + r)⁻¹ (fun t _ => D t / P t) ↔
      Hyperinflation.TVC r P D := by
  constructor
  · intro h
    unfold Hyperinflation.TVC
    simpa [perfectForesight] using h 0 ()
  · intro h t ω
    have hshift := h.comp (tendsto_add_atTop_nat t)
    have hc := hshift.const_mul ((1 + r) ^ t)
    rw [mul_zero] at hc
    refine hc.congr fun T => ?_
    change (1 + r) ^ t * ((1 + r)⁻¹ ^ (T + t) * (D (T + t) / P (T + t))) =
      (1 + r)⁻¹ ^ T * (D (t + T) / P (t + T))
    rw [add_comm T t, pow_add, ← mul_assoc, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hr.ne',
      one_pow, one_mul]

/-- Cochrane (2023), §16.3, p. 368, under uncertainty: the passive-fiscal transversality result
`Hyperinflation.stoch_tvc` is the transversality condition `ObservationalEquivalence.TVC` of the
unified model (16.20)–(16.22) for real debt with `ρ = 1/(1 + r)`. -/
theorem stoch_tvc_obs (hPO : 𝔼.PullOut) {r : ℝ} (hr : 0 < r) {P D i s : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (hk : ∀ t, 𝔼.E t (fun ω => D (t + 1) ω / P t ω) = fun ω => D (t + 1) ω / P t ω)
    (hb : 𝔼.Adapted (Hyperinflation.realDebt P D)) (hF : Hyperinflation.FisherE 𝔼 r P i)
    (hflow : Hyperinflation.FlowE P D i s)
    (hpas : ∀ t ω, s t ω = r / (1 + r) * (D t ω / P t ω)) :
    ObservationalEquivalence.TVC 𝔼 (1 + r)⁻¹ (Hyperinflation.realDebt P D) :=
  fun t ω => Hyperinflation.stoch_tvc 𝔼 hPO hr hP hi hk hb hF hflow hpas t ω

end Cochrane.NewKeynesianSelection.Links
