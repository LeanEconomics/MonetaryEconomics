/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.Money
import NeoWicksellianFramework.Learning
import NeoWicksellianFramework.ThreeByThree
import NeoWicksellianFramework.InflationDeterminants
import NeoWicksellianFramework.TargetingRules

/-!
# Links between the chapters' modules

Woodford (2003), *Interest and Prices*, Chapter 4 (with the Chapter 3 Phillips curve it uses).
Several modules state as a hypothesis, or prove in a different formulation, a result that
another module establishes. This module connects them.

* **(3.14) from the Calvo model.** `Money.as314_of_mc` takes the Chapter 3 Phillips curve
  `π = ξ ŝ + β E π′` in real marginal cost as a hypothesis. `as314_of_pricing` derives it from
  the Calvo pricing condition through the Chapter 3 derivation restated in `BasicModel`
  (`BasicModel.prop35`, with the marginal-cost term `ŝ/(1 + ωθ)`), so (3.14) holds whenever
  firms price as in Chapter 3 and marginal cost obeys (3.11)–(3.13). `kappa314_eq_kappa`: the
  slope of (3.14) is the slope `κ` of (1.10) with `ζ = ε_mc/(1 + ωθ)`.
* **Propositions 4.8 and 4.9.** Both rest on `Determinacy2Learning.prop_4_8` (E-stability of the
  temporary-equilibrium matrix `B` iff (2.7)). `eStable_dT_iff_eStable`: regression learning
  on a stationary state is E-stable iff sample-mean learning is; `eStable_dT_iff_determinate`:
  iff the equilibrium under (1.14) is determinate (Proposition 4.3).
* **Proposition 4.4.** `prop44_iff_inertialTaylorPrinciple`: the determinacy theorem
  `ThreeByThree.prop44` is the condition `InflationDeterminants.InertialTaylorPrinciple` (2.9)
  together with some feedback; `inert_decomp_of_determinate44`: whenever the inertial rule
  (2.8) is determinate, the decomposition behind the solution formula of p. 277 exists
  (`InflationDeterminants.inert_BK`); `inertial_existsUnique_of_determinate44`: the
  determinacy of `ThreeByThree` then gives the unique equilibrium of
  `InflationDeterminants.inertial_equilibrium_existsUnique` (bounded random initial condition).
* **Two notions of determinacy for (1.14).** `forwardDeterminate_iff_modelDeterminate`: the
  uniqueness notion of `InflationDeterminants` and the existence-and-uniqueness notion of
  `Determinacy2` coincide under the Taylor rule (both are (2.7)).
* **The reaction function (2.44).** `rule244_forward_determinate`: the forward-looking rule
  (2.10) with the coefficients of (2.44) is determinate (Proposition 4.5), as p. 294 asserts.
* **The natural rate (1.15) in Preston's gap form.** `gapIS_of_rational_rnHat`: the natural
  rate of interest of (1.15) (`BasicModel.rnHat`) satisfies the hypothesis of
  `Learning.Preston.gapIS_of_rational`, so under rational expectations the output form of
  aggregate demand implies (2.29) with that natural rate.
-/

namespace Woodford.NeoWicksellianFramework.Links

open Determinacy2 Determinacy2Learning

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (3.14) from the Chapter 3 Calvo derivation -/

omit 𝔼 in
/-- Woodford (2003), (3.14), p. 304, and (1.10), p. 245: the slope
`κ = ξ ε_mc = (1 − α)(1 − αβ)ε_mc/(α(1 + ωθ))` of (3.14) is the slope `κ = (1 − α)(1 − αβ)ζ/α`
of the New Keynesian Phillips curve with `ζ = ε_mc/(1 + ωθ)`. -/
theorem kappa314_eq_kappa (α β ω θ εmc : ℝ) :
    Money.kappa314 α β ω θ εmc = BasicModel.kappa α β (εmc / (1 + ω * θ)) := by
  unfold Money.kappa314 BasicModel.kappa
  ring

/-- Woodford (2003), (3.14), p. 304, from Chapter 3, Proposition 3.5 (p. 187) and (2.6): if
the price index is predetermined with bounded inflation, real marginal cost `ŝ` is adapted and
bounded, (2.5) holds, firms set prices by the Calvo condition (2.6) with marginal-cost term
`ŝ/(1 + ωθ)`, and marginal cost obeys `ŝ = ε_mc(x + ϕ(î − îᵐ))` ((3.11)–(3.13)), then the
aggregate-supply relation (3.14) holds with `κ = (1 − α)(1 − αβ)ε_mc/(α(1 + ωθ))`. The
Phillips-curve hypothesis of `Money.as314_of_mc` is thus derived, not assumed. -/
theorem as314_of_pricing {α β ω θ εmc ϕ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) {P pstar s x i im : ℕ → Ω → ℝ} (hPa : ∀ t, 𝔼.E t (P t) = P t)
    (hpre : ∀ t, 𝔼.E t (P (t + 1)) = P (t + 1)) (hπ : BasicModel.BoundedIncr P)
    (hsa : 𝔼.Adapted s) (hsb : BoundedProc s) (h25 : BasicModel.Eq25 α P pstar)
    (h26 : BasicModel.Eq26 𝔼 α β P pstar (fun T z => (1 + ω * θ)⁻¹ * s T z))
    (hs : ∀ t, s t = εmc • (x t + ϕ • (i t - im t))) :
    Money.AS314 𝔼 (Money.kappa314 α β ω θ εmc) ϕ β x (BasicModel.infl P) i im := by
  have h := (BasicModel.prop35 𝔼 (ζ := (1 + ω * θ)⁻¹) hα0 hα1 hβ0 hβ1 hPa hpre hπ hsa hsb
    h25).mp h26
  refine Money.as314_of_mc 𝔼 (fun t => ?_) hs
  rw [h t]
  congr 2
  unfold BasicModel.kappa
  ring

/-! ### Propositions 4.8 and 4.9 -/

/-- Woodford (2003), Propositions 4.8 (p. 266) and 4.9 (p. 271): with a stationary state
(every eigenvalue of `C` inside the unit circle), the regression r.e.e. is E-stable under
least-squares learning, `DT = blockdiag(B, C′ ⊗ B)`, iff the s.c.e. is E-stable under
sample-mean learning (`DT = B`): both are the Taylor principle (2.7). -/
theorem eStable_dT_iff_eStable {S : Type*} [Fintype S] [DecidableEq S] {β σ κ φπ φx : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (C : Matrix S S ℝ) (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ‖ρ‖ < 1) :
    EStable (Learning.Regression.dT (taylorB β σ κ φπ φx) C) ↔ EStable (taylorB β σ κ φπ φx) := by
  rw [Learning.BullardMitra.prop_4_9 hβ0 hβ1 hκ hσ hφπ hφx C hC,
    prop_4_8 hβ0 hβ1 hσ hκ hφπ hφx]

/-- Woodford (2003), Proposition 4.9 (p. 271) with Proposition 4.3 (p. 254) and p. 272: with a
stationary state, the regression r.e.e. under (1.14) is E-stable iff equilibrium is
determinate. -/
theorem eStable_dT_iff_determinate [Nonempty Ω] {S : Type*} [Fintype S] [DecidableEq S]
    {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ) (hφπ : 0 ≤ φπ)
    (hφx : 0 ≤ φx) (πbar : ℝ) (C : Matrix S S ℝ)
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ‖ρ‖ < 1) :
    EStable (Learning.Regression.dT (taylorB β σ κ φπ φx) C) ↔
      ModelDeterminate 𝔼 (TaylorEqm 𝔼 β σ κ φπ φx πbar) := by
  rw [Learning.BullardMitra.prop_4_9 hβ0 hβ1 hκ hσ hφπ hφx C hC,
    prop_4_3 𝔼 hβ0 hβ1 hσ hκ hφπ hφx πbar]

/-! ### Proposition 4.4 -/

/-- Woodford (2003), Proposition 4.4 (p. 255) in the notation of §2.4 (p. 277): the inertial
rule (2.8) is determinate (`ThreeByThree.Determinate44`) iff the condition (2.9),
`InflationDeterminants.InertialTaylorPrinciple`, holds and the rule responds to inflation or
the output gap (the corrected statement `ThreeByThree.prop44`). -/
theorem prop44_iff_inertialTaylorPrinciple [Nonempty Ω] {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    ThreeByThree.Determinate44 𝔼 β κ σ ρ φπ φx ↔
      InflationDeterminants.InertialTaylorPrinciple β κ ρ φπ φx ∧ (0 < φπ ∨ 0 < φx) := by
  rw [ThreeByThree.prop44 𝔼 hβ0 hβ1 hκ hσ hρ hφπ hφx, InflationDeterminants.InertialTaylorPrinciple,
    ← taylorLHS_eq]
  rfl

/-- Woodford (2003), Proposition 4.4 (p. 255) and p. 277: whenever the inertial rule (2.8) is
determinate, the decomposition `z = ω s + ẑ` with a stable root `0 ≤ λ < 1` and a stable
forward block, on which the solution formula of p. 277 rests
(`InflationDeterminants.inertial_equilibrium_formula`), exists. -/
theorem inert_decomp_of_determinate44 [Nonempty Ω] {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (h : ThreeByThree.Determinate44 𝔼 β κ σ ρ φπ φx) :
    ∃ lam, 0 ≤ lam ∧ lam < 1 ∧
      InflationDeterminants.Decomp (InflationDeterminants.inertP κ)
        (InflationDeterminants.predN β σ) 0 (a25 σ) (InflationDeterminants.inertPhi φπ φx) ρ lam
        (InflationDeterminants.inertOmega β σ κ lam) ∧
      det2 (InflationDeterminants.resM (InflationDeterminants.inertP κ)
        (InflationDeterminants.predN β σ) (a25 σ) (InflationDeterminants.inertPhi φπ φx)
        (InflationDeterminants.inertOmega β σ κ lam)) ≠ 0 ∧
      SchurStable (tr2 (BlanchardKahn.solveMN (InflationDeterminants.resM
          (InflationDeterminants.inertP κ) (InflationDeterminants.predN β σ) (a25 σ)
          (InflationDeterminants.inertPhi φπ φx) (InflationDeterminants.inertOmega β σ κ lam))
          (InflationDeterminants.predN β σ)))
        (det2 (BlanchardKahn.solveMN (InflationDeterminants.resM
          (InflationDeterminants.inertP κ) (InflationDeterminants.predN β σ) (a25 σ)
          (InflationDeterminants.inertPhi φπ φx) (InflationDeterminants.inertOmega β σ κ lam))
          (InflationDeterminants.predN β σ))) := by
  obtain ⟨hTP, hφ⟩ := (prop44_iff_inertialTaylorPrinciple 𝔼 hβ0 hβ1 hκ hσ hρ hφπ hφx).mp h
  exact InflationDeterminants.inert_BK hβ0 hβ1 hκ hσ hρ hφπ hφx hφ hTP

/-- Woodford (2003), Proposition 4.4 (p. 255) and p. 277: if the inertial rule (2.8) is
determinate in the sense of `ThreeByThree.Determinate44` (deterministic initial interest rate),
then for every bounded adapted gap `r̂ⁿ − ī + π̄` and every bounded initial `î_{−1} − ī_{−1}`
known at date 0 (possibly random) the model (1.12), (1.13), (2.8) has exactly one equilibrium
with `π`, `x`, `î − ī` bounded and `π`, `x`, `î` adapted
(`InflationDeterminants.inertial_equilibrium_existsUnique`). -/
theorem inertial_existsUnique_of_determinate44 [Nonempty Ω] {β κ σ ρ φπ φx πbar : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφπ : 0 ≤ φπ)
    (hφx : 0 ≤ φx) (h : ThreeByThree.Determinate44 𝔼 β κ σ ρ φπ φx) {rn ibar : ℕ → Ω → ℝ}
    {Mg : ℝ} (hg : ∀ t z, |InflationDeterminants.gapForcing πbar rn ibar t z| ≤ Mg)
    (hga : 𝔼.Adapted (InflationDeterminants.gapForcing πbar rn ibar)) (hiba : 𝔼.Adapted ibar)
    {s0 : Ω → ℝ} {B : ℝ} (hs0 : 𝔼.E 0 s0 = s0) (hs0b : ∀ z, |s0 z| ≤ B) :
    ∃! p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      BasicModel.NKPCurve 𝔼 β κ p.1 p.2.1 ∧ BasicModel.IS112 𝔼 σ p.2.1 p.2.2 p.1 rn ∧
        InflationDeterminants.InertialRule β κ ρ φπ φx πbar s0 p.1 p.2.1 p.2.2 ibar ∧
          𝔼.Adapted p.1 ∧ 𝔼.Adapted p.2.1 ∧ 𝔼.Adapted p.2.2 ∧ BoundedProc p.1 ∧
            BoundedProc p.2.1 ∧ BoundedProc (p.2.2 - ibar) := by
  obtain ⟨lam, hl0, hl1, hD, hd, hG⟩ :=
    inert_decomp_of_determinate44 𝔼 hβ0 hβ1 hκ hσ hρ hφπ hφx h
  exact InflationDeterminants.inertial_equilibrium_existsUnique 𝔼 hκ.ne' hD
    (abs_lt.mpr ⟨by linarith, hl1⟩) hd hG hg hga hiba hs0 hs0b

/-! ### Determinacy of the Taylor rule in two formulations -/

/-- Woodford (2003), Proposition 4.3 (p. 254), in the two formulations of this project: the
system `E_t z_{t+1} = A z_t + a e_t` of (C.19) has at most one bounded adapted solution for
every forcing (`InflationDeterminants.ForwardDeterminate`) iff the model (1.12)–(1.14) has
exactly one bounded adapted equilibrium for all bounded adapted disturbances
(`Determinacy2.ModelDeterminate`). -/
theorem forwardDeterminate_iff_modelDeterminate [Nonempty Ω] {β σ κ φπ φx : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (πbar : ℝ) :
    InflationDeterminants.ForwardDeterminate 𝔼 (taylorA β σ κ φπ φx) (a25 σ) ↔
      ModelDeterminate 𝔼 (TaylorEqm 𝔼 β σ κ φπ φx πbar) := by
  rw [InflationDeterminants.taylor_determinate_iff 𝔼 hβ0 hκ hσ hφπ hφx hβ1,
    prop_4_3 𝔼 hβ0 hβ1 hσ hκ hφπ hφx πbar, InflationDeterminants.TaylorPrinciple, taylorLHS_eq]

/-! ### The reaction function (2.44) and Proposition 4.5 -/

/-- Woodford (2003), p. 294, with Proposition 4.5 (p. 257): the forward-looking rule (2.10)
with the coefficients `φ_π = 1 + β/(κσ)`, `φ_x = 4/σ` of the reaction function (2.44)
(`TargetingRules.rule244_coefficients`: they satisfy (2.7) and (2.11)) is determinate, for all
`0 < β < 1`, `κ, σ > 0`. -/
theorem rule244_forward_determinate [Nonempty Ω] {β σ κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hκ : 0 < κ) (πbar : ℝ) :
    ModelDeterminate 𝔼 (Determinacy2Forward.FwdEqm 𝔼 β σ κ (TargetingRules.rule244_phiPi β σ κ)
      (TargetingRules.rule244_phiX σ) πbar) := by
  obtain ⟨hTP, h211⟩ := TargetingRules.rule244_coefficients hβ0 hκ hσ
  refine (Determinacy2Forward.prop_4_5 𝔼 hβ0 hβ1 hσ hκ
    (div_pos four_pos hσ).le πbar).mpr ⟨?_, h211⟩
  rw [taylorLHS_eq]
  exact hTP

/-! ### The natural rate (1.15) in Preston's gap form (2.29) -/

/-- Woodford (2003), (1.15), p. 246, and p. 273: for `σ ≠ 0` the natural rate of interest
`r̂ⁿ = σ⁻¹[(g − Ŷⁿ) − E_t(g′ − Ŷⁿ′)]` of `BasicModel.rnHat` satisfies the relation
`σ r̂ⁿ_t = h_t − E_t h_{t+1}`, `h = g − Ŷⁿ`, assumed in `Learning.Preston`. -/
theorem smul_rnHat {σ : ℝ} (hσ : σ ≠ 0) (g Yn : ℕ → Ω → ℝ) (t : ℕ) :
    σ • BasicModel.rnHat 𝔼 σ g Yn t = (g t - Yn t) - 𝔼.E t (g (t + 1) - Yn (t + 1)) := by
  rw [BasicModel.rnHat, smul_smul, mul_inv_cancel₀ hσ, one_smul]

/-- Woodford (2003), (1.15), p. 246, and (2.29), p. 273: under rational expectations, with
bounded disturbances and `σ ≠ 0`, the output form of aggregate demand implies Preston's gap
form (2.29) with the natural rate of interest `r̂ⁿ` of (1.15) (`BasicModel.rnHat`). -/
theorem gapIS_of_rational_rnHat {β σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : σ ≠ 0)
    {Y g Yn i infl : ℕ → Ω → ℝ} (hY : BoundedProc Y) (hg : BoundedProc g) (hYn : BoundedProc Yn)
    (hi : BoundedProc i) (hπ : BoundedProc infl)
    (hout : Learning.Preston.OutputIS 𝔼.E β σ Y g i infl)
    (hYa : ∀ t, 𝔼.E t (Y t - g t) = Y t - g t) (ha : 𝔼.Adapted fun t => g t - Yn t) :
    Learning.Preston.PrestonIS 𝔼.E β σ (fun t => Y t - Yn t) infl i
      (BasicModel.rnHat 𝔼 σ g Yn) := by
  obtain ⟨Mg, hMg⟩ := hg
  obtain ⟨Mn, hMn⟩ := hYn
  have hb : ∀ t z, |g t z - Yn t z| ≤ Mg + Mn := fun t z =>
    (abs_sub _ _).trans (add_le_add (hMg t z) (hMn t z))
  have hr : BoundedProc (BasicModel.rnHat 𝔼 σ g Yn) := by
    refine ⟨|σ⁻¹| * ((Mg + Mn) + (Mg + Mn)), fun t z => ?_⟩
    have hE := 𝔼.abs_E_le (x := g (t + 1) - Yn (t + 1)) (fun z => hb (t + 1) z) t z
    simp only [BasicModel.rnHat, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hb t z) hE))
      (abs_nonneg _)
  exact Learning.Preston.gapIS_of_rational 𝔼 hβ0 hβ1 hY ⟨Mg, hMg⟩ ⟨Mn, hMn⟩ hi hπ hr hout
    hYa ha (smul_rnHat 𝔼 hσ g Yn)

end Woodford.NeoWicksellianFramework.Links
