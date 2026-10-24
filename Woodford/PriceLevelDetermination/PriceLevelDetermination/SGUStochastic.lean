/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.SchmittGroheUribe
import PriceLevelDetermination.LocalIFTStochastic

/-!
# The Schmitt-Grohé–Uribe example under uncertainty

Woodford (2003), *Interest and Prices*, Chapter 2, §4.3, p. 137, and Appendix A.17, pp. 653–655.
After excluding self-fulfilling inflations and deflations under perfect foresight (module
`SchmittGroheUribe`, with the E5 hypothesis `β + θΠ*(1 − φ_π) > 0`), the book claims (p. 137) that
"using similar arguments, one can show that it is the unique rational-expectations equilibrium,
even allowing for stochastic equilibria of arbitrary form". This module tests the claim.

The stochastic model (`StochPath`): positive adapted `Π` with `A(Π_t) = E_t[B(Π_{t+1})]`,
`A = λ(φ)/(1 + φ)`, `B = βλ(φ)/Π` — the Euler equation (4.3) (`stochPath_iff_eq43`, under the
pull-out property). It is linear in `B(Π_{t+1})`, so the "no successor beyond `Π̄`" step passes
through `E_t` by monotonicity alone (no Jensen term); the transversality condition (1.24) is
imposed at every date and state (`StochTVC`), with liabilities growing at `μ̄`.

## Main results

* `stoch_le_pibar`, `stoch_no_hyperinflation`: on **every** expectation system, every stochastic
  equilibrium has `Π_t ≤ Π*` in every state (no boundedness assumed).
* `stoch_target_equilibrium`: `Π ≡ Π*` is a stochastic equilibrium; it satisfies the TVC iff
  `βμ̄ < Π*`.
* `stoch_unique_of_resolved`: on any informationally closed expectation system on which
  information is eventually resolved, `Π ≡ Π*` is the **unique** stochastic equilibrium satisfying
  the TVC. `finiteTree_eventuallyResolved` and `sgu_finiteTree_unique`: this covers every finite
  event tree (`ExpectationsFiniteTree`), so no finite-tree sunspot equilibrium exists.
* **Correction** (`sgu_sunspot_refutation`): with perpetual uncertainty the claim is false. In
  a geometric switching-date model (`geomE`, a genuine conditional expectation on bounded
  variables: `geomE_const`, `geomE_add`, `geomE_smul`, `geomE_mono`, `geomE_known`,
  `geomE_tower`) with `θ = Ȳ = 1`, `β = 1/2`, `Π* = 1`, `φ_π = 5/4` (all hypotheses, E5 included)
  and any `1 < μ̄ < 2`, the sunspot equilibrium "zero-interest deflation `Π = 1/3` until a switch
  that occurs with probability `2/3` each period, `Π* ` afterwards" satisfies (4.5), the TVC and
  (4.4) at every date and state, but `Π₀ ≠ Π*`.
-/

namespace Woodford.PriceLevelDetermination.SGUStochastic

open Filter Topology
open Woodford.PriceLevelDetermination.GlobalDynamics (IsPath45)
open Woodford.PriceLevelDetermination.MoneyTargetingDynamics (tvcValue target_tvc_iff)
open Woodford.PriceLevelDetermination.SchmittGroheUribe (sguA sguB sguC sguPibar ellSGU phiSGU
  lamSGU sguAB_formula sguB_gt sguB_strictAntiOn sguA_lt_B_above sguAB_continuousAt
  sguPibar_spec eq45_iff_AB sgu_unique_pf_equilibrium phiSGU_target lamSGU_phi_pos
  phiSGU_nonneg)
open Woodford.PriceLevelDetermination.LocalIFTStochastic.Ops (InfoClosed CellConst Indist
  cellConst_of_known)

/-! ## The functions `A` and `B` -/

/-- Woodford (2003), p. 655: `A(Π) = 1/(Ȳ M) + θ/Ȳ` with `M = max(1, ℓ(Π)) = 1 + φ(Π)`. -/
theorem sguA_eq {θ Y β Pis φπ x : ℝ} (hY : 0 < Y) :
    sguA θ Y β Pis φπ x = 1 / (Y * max 1 (ellSGU β Pis φπ x)) + θ / Y := by
  rw [(sguAB_formula θ Y β Pis φπ x).1]
  have hM : 0 < max 1 (ellSGU β Pis φπ x) := lt_of_lt_of_le one_pos (le_max_left _ _)
  field_simp

/-- Woodford (2003), p. 655: on the range where the rule is linear (`ℓ ≥ 1`), `A` is strictly
decreasing (for `φ_π > 0`). -/
theorem sguA_lt_of_lt {θ Y β Pis φπ a b : ℝ} (hY : 0 < Y) (hβ : 0 < β) (hφπ : 0 < φπ)
    (ha : 1 ≤ ellSGU β Pis φπ a) (hab : a < b) : sguA θ Y β Pis φπ b < sguA θ Y β Pis φπ a := by
  have hl : ellSGU β Pis φπ a < ellSGU β Pis φπ b := by
    unfold ellSGU
    exact div_lt_div_of_pos_right (by nlinarith) hβ
  have hMa : max 1 (ellSGU β Pis φπ a) = ellSGU β Pis φπ a := max_eq_right ha
  have hMb : max 1 (ellSGU β Pis φπ b) = ellSGU β Pis φπ b := max_eq_right (by linarith)
  rw [sguA_eq hY, sguA_eq hY, hMa, hMb]
  have h1 : 0 < ellSGU β Pis φπ a := by linarith
  have h2 : 1 / (Y * ellSGU β Pis φπ b) < 1 / (Y * ellSGU β Pis φπ a) :=
    one_div_lt_one_div_of_lt (by positivity) (mul_lt_mul_of_pos_left hl hY)
  linarith

/-- Woodford (2003), p. 655: `A(Π) = A(Π*)` only at `Π = Π*` (for `φ_π ≠ 0`, `Π* > β`). -/
theorem sguA_eq_target {θ Y β Pis φπ x : ℝ} (hY : 0 < Y) (hβ : 0 < β) (hφπ : φπ ≠ 0)
    (hPis : β < Pis) (h : sguA θ Y β Pis φπ x = sguA θ Y β Pis φπ Pis) : x = Pis := by
  rw [sguA_eq hY, sguA_eq hY] at h
  have hlP : ellSGU β Pis φπ Pis = Pis / β := by unfold ellSGU; ring
  have hlP1 : 1 < Pis / β := (one_lt_div hβ).mpr hPis
  have hMP : max 1 (ellSGU β Pis φπ Pis) = Pis / β := by rw [hlP]; exact max_eq_right hlP1.le
  rw [hMP] at h
  have hMx : 0 < max 1 (ellSGU β Pis φπ x) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hM : max 1 (ellSGU β Pis φπ x) = Pis / β := by
    have h' : 1 / (Y * max 1 (ellSGU β Pis φπ x)) = 1 / (Y * (Pis / β)) := by linarith
    have hne1 : Y * max 1 (ellSGU β Pis φπ x) ≠ 0 := by positivity
    have hne2 : Y * (Pis / β) ≠ 0 := by positivity
    rw [div_eq_div_iff hne1 hne2, one_mul, one_mul] at h'
    exact mul_left_cancel₀ hY.ne' h'.symm
  have hl : ellSGU β Pis φπ x = Pis / β := by
    rcases le_total 1 (ellSGU β Pis φπ x) with h1 | h1
    · rwa [max_eq_right h1] at hM
    · rw [max_eq_left h1] at hM
      linarith
  unfold ellSGU at hl
  field_simp at hl
  have : φπ * (x - Pis) = 0 := by linarith
  rcases mul_eq_zero.mp this with h2 | h2
  · exact absurd h2 hφπ
  · linarith

/-- Woodford (2003), p. 655: `A(Π*) = B(Π*)` (the target is a steady state of (4.5)) when
`Π* > β`. -/
theorem sguA_target_eq_B {θ Y β Pis φπ : ℝ} (hY : 0 < Y) (hβ : 0 < β) (hPis : β < Pis) :
    sguA θ Y β Pis φπ Pis = sguB θ Y β Pis φπ Pis := by
  rw [(sguAB_formula θ Y β Pis φπ Pis).1, (sguAB_formula θ Y β Pis φπ Pis).2]
  have hlP : ellSGU β Pis φπ Pis = Pis / β := by unfold ellSGU; ring
  have hlP1 : 1 < Pis / β := (one_lt_div hβ).mpr hPis
  rw [hlP, max_eq_right hlP1.le]
  have hP : 0 < Pis := by linarith
  field_simp

/-- Woodford (2003), p. 655, with E5: under `φ_π > 1`, `Π* > β` and `β + θΠ*(1 − φ_π) > 0`,
`ℓ(Π̄) ≥ 1`, so `A` is strictly decreasing beyond `Π̄`. -/
theorem one_le_ell_pibar {θ Y β Pis φπ : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hβ : 0 < β)
    (hφπ : 1 < φπ) (hPis : β < Pis) (hc : 0 < sguC θ β Pis φπ) :
    1 ≤ ellSGU β Pis φπ (sguPibar θ β Pis φπ) := by
  rw [(sguPibar_spec (Y := Y) hθ hY hβ hφπ hPis hc).2.1]
  have hk : 0 < θ * (φπ - 1) := by nlinarith
  have hkP : θ * (φπ - 1) * Pis < β := by unfold sguC at hc; nlinarith
  rw [le_div_iff₀ hk, one_mul]
  nlinarith

/-! ## The stochastic model -/

variable {Ω : Type*}

/-- Woodford (2003), (4.3) with (4.1), pp. 124–125, under uncertainty, in the form of A.17: an
inflation process `Π` (positive, adapted) with `A(Π_t) = E_t[B(Π_{t+1})]` at every date —
`λ(φ(Π_t))/(1 + φ(Π_t)) = β E_t[λ(φ(Π_{t+1}))/Π_{t+1}]`, the Euler equation (1.21) with the
truncated linear Taylor rule (A.56) and `λ(i) = (1 + θ(1 + i))/Ȳ` (`stochPath_iff_eq43` derives
it from (4.3)). Only `A`, `B` and the linear `E_t` enter, so no Jensen-type term arises. -/
def StochPath (𝔼 : ExpectationSystem Ω) (θ Y β Pis φπ : ℝ) (Pi_ : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, 0 < Pi_ t ω) ∧ (∀ t, 𝔼.E t (Pi_ t) = Pi_ t) ∧
    ∀ t, 𝔼.E t (fun ω => sguB θ Y β Pis φπ (Pi_ (t + 1) ω)) =
      fun ω => sguA θ Y β Pis φπ (Pi_ t ω)

/-- Woodford (2003), (1.24), p. 72, under uncertainty: the transversality condition
`lim_T β^T E_t[λ_T D_T/P_T] = 0` at every date and in every state, with deterministic
nominal liabilities `D`. -/
def StochTVC (𝔼 : ExpectationSystem Ω) (θ Y β Pis φπ : ℝ) (Pi_ P : ℕ → Ω → ℝ) (D : ℕ → ℝ) :
    Prop :=
  ∀ t ω, Tendsto (fun T => 𝔼.E t (fun ω' =>
    tvcValue β (lamSGU θ Y) (phiSGU β Pis φπ) (fun s => Pi_ s ω') (fun s => P s ω') D T) ω)
    atTop (𝓝 0)

/-- Woodford (2003), (4.3), p. 124, under uncertainty: with the pull-out property and
informational closure (so that `λ(φ(Π_t))` is known at `t`), the Fisher equation
`β(1 + φ(Π_t)) E_t[λ_{t+1}/(λ_t Π_{t+1})] = 1` at every date is the stochastic (4.5),
`E_t[B(Π_{t+1})] = A(Π_t)`. -/
theorem stochPath_iff_eq43 (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) (hcl : InfoClosed 𝔼)
    {θ Y β Pis φπ : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hβ : 0 < β) {Pi_ : ℕ → Ω → ℝ}
    (hpos : ∀ t ω, 0 < Pi_ t ω) (had : ∀ t, 𝔼.E t (Pi_ t) = Pi_ t) (t : ℕ) :
    𝔼.E t (fun ω => β * (1 + phiSGU β Pis φπ (Pi_ t ω)) *
        (lamSGU θ Y (phiSGU β Pis φπ (Pi_ (t + 1) ω)) /
          (lamSGU θ Y (phiSGU β Pis φπ (Pi_ t ω)) * Pi_ (t + 1) ω))) = (fun _ => 1) ↔
      𝔼.E t (fun ω => sguB θ Y β Pis φπ (Pi_ (t + 1) ω)) =
        fun ω => sguA θ Y β Pis φπ (Pi_ t ω) := by
  set k : Ω → ℝ := fun ω => (1 + phiSGU β Pis φπ (Pi_ t ω)) /
    lamSGU θ Y (phiSGU β Pis φπ (Pi_ t ω)) with hk
  have hkk : 𝔼.E t k = k := by
    refine hcl t k (fun ω ω' h => ?_)
    have h1 := cellConst_of_known 𝔼 (had t) ω ω' h
    simp only [hk, h1]
  have hkpos : ∀ ω, 0 < k ω := fun ω => by
    have := lamSGU_phi_pos (β := β) (Pis := Pis) (φπ := φπ) (x := Pi_ t ω) hθ hY
    have := phiSGU_nonneg β Pis φπ (Pi_ t ω)
    simp only [hk]
    positivity
  have hfun : (fun ω => β * (1 + phiSGU β Pis φπ (Pi_ t ω)) *
      (lamSGU θ Y (phiSGU β Pis φπ (Pi_ (t + 1) ω)) /
        (lamSGU θ Y (phiSGU β Pis φπ (Pi_ t ω)) * Pi_ (t + 1) ω))) =
      k * fun ω => sguB θ Y β Pis φπ (Pi_ (t + 1) ω) := by
    funext ω
    have h1 := lamSGU_phi_pos (β := β) (Pis := Pis) (φπ := φπ) (x := Pi_ t ω) hθ hY
    have h2 := hpos (t + 1) ω
    simp only [Pi.mul_apply, hk, sguB]
    field_simp
  rw [hfun, hpo t k _ hkk]
  constructor
  · intro h
    funext ω
    have h1 := congrFun h ω
    simp only [Pi.mul_apply] at h1
    have h2 := lamSGU_phi_pos (β := β) (Pis := Pis) (φπ := φπ) (x := Pi_ t ω) hθ hY
    have h3 : 0 < 1 + phiSGU β Pis φπ (Pi_ t ω) := by
      linarith [phiSGU_nonneg β Pis φπ (Pi_ t ω)]
    rw [hk] at h1
    simp only at h1
    unfold sguA
    field_simp at h1 ⊢
    linarith
  · intro h
    funext ω
    simp only [Pi.mul_apply, h, hk]
    have h2 := lamSGU_phi_pos (β := β) (Pis := Pis) (φπ := φπ) (x := Pi_ t ω) hθ hY
    have h3 : 0 < 1 + phiSGU β Pis φπ (Pi_ t ω) := by
      linarith [phiSGU_nonneg β Pis φπ (Pi_ t ω)]
    unfold sguA
    field_simp

/-! ## No self-fulfilling inflation under uncertainty (every expectation system) -/

/-- Woodford (2003), p. 655 ("there is no value for `Π_{t+1}`…"), **under uncertainty**: with
the E5 hypothesis, every stochastic equilibrium has `Π_t ≤ Π̄` in every state: `A(Π_t) =
E_t[B(Π_{t+1})] ≥ θφ_π/Ȳ = A(Π̄)` by monotonicity of `E_t` and `B > θφ_π/Ȳ`. -/
theorem stoch_le_pibar (𝔼 : ExpectationSystem Ω) {θ Y β Pis φπ : ℝ} (hθ : 0 < θ) (hY : 0 < Y)
    (hβ : 0 < β) (hφπ : 1 < φπ) (hPis : β < Pis) (hc : 0 < sguC θ β Pis φπ)
    {Pi_ : ℕ → Ω → ℝ} (hpath : StochPath 𝔼 θ Y β Pis φπ Pi_) (t : ℕ) (ω : Ω) :
    Pi_ t ω ≤ sguPibar θ β Pis φπ := by
  have hge : θ * φπ / Y ≤ sguA θ Y β Pis φπ (Pi_ t ω) := by
    have hm := 𝔼.mono t (x := fun _ => θ * φπ / Y)
      (y := fun ω' => sguB θ Y β Pis φπ (Pi_ (t + 1) ω'))
      (fun ω' => (sguB_gt hθ hY hβ (hpath.1 (t + 1) ω') hc).le) ω
    rw [𝔼.const, hpath.2.2 t] at hm
    exact hm
  by_contra hlt
  push Not at hlt
  have h1 := sguA_lt_of_lt (θ := θ) hY hβ (by linarith)
    (one_le_ell_pibar hθ hY hβ hφπ hPis hc) hlt
  rw [(sguPibar_spec hθ hY hβ hφπ hPis hc).2.2] at h1
  linarith

/-- Woodford (2003), p. 137 and p. 655, **no self-fulfilling inflation under uncertainty**: under
`φ_π > 1`, `Π* > β` and the E5 hypothesis `β + θΠ*(1 − φ_π) > 0`, **every stochastic equilibrium
on any expectation system has `Π_t ≤ Π*` at every date and in every state** (no boundedness
assumed). Proof: `S = sup Π_t(ω) ≤ Π̄`; if `S > Π*`, then `A(Π_t) = E_t[B(Π_{t+1})] ≥ B(S) > A(S)`
everywhere, contradicting continuity of `A` at `S`. -/
theorem stoch_no_hyperinflation (𝔼 : ExpectationSystem Ω) {θ Y β Pis φπ : ℝ} (hθ : 0 < θ)
    (hY : 0 < Y) (hβ : 0 < β) (hφπ : 1 < φπ) (hPis : β < Pis) (hc : 0 < sguC θ β Pis φπ)
    {Pi_ : ℕ → Ω → ℝ} (hpath : StochPath 𝔼 θ Y β Pis φπ Pi_) (t : ℕ) (ω : Ω) :
    Pi_ t ω ≤ Pis := by
  set V : Set ℝ := Set.range (fun q : ℕ × Ω => Pi_ q.1 q.2) with hV
  have hne : V.Nonempty := ⟨Pi_ t ω, ⟨(t, ω), rfl⟩⟩
  have hbdd : BddAbove V := ⟨sguPibar θ β Pis φπ, by
    rintro _ ⟨q, rfl⟩
    exact stoch_le_pibar 𝔼 hθ hY hβ hφπ hPis hc hpath q.1 q.2⟩
  set S := sSup V with hS
  have hle : ∀ s ω', Pi_ s ω' ≤ S := fun s ω' => le_csSup hbdd ⟨(s, ω'), rfl⟩
  by_contra hgt
  push Not at hgt
  have hSP : Pis < S := lt_of_lt_of_le hgt (hle t ω)
  have hS0 : 0 < S := by linarith
  have hsa := sguB_strictAntiOn (Y := Y) hθ hY hβ hc
  have hlow : ∀ s ω', sguB θ Y β Pis φπ S ≤ sguA θ Y β Pis φπ (Pi_ s ω') := by
    intro s ω'
    have hm := 𝔼.mono s (x := fun _ => sguB θ Y β Pis φπ S)
      (y := fun ω'' => sguB θ Y β Pis φπ (Pi_ (s + 1) ω''))
      (fun ω'' => hsa.antitoneOn (hpath.1 (s + 1) ω'') hS0 (hle (s + 1) ω'')) ω'
    rw [𝔼.const, hpath.2.2 s] at hm
    exact hm
  have hAB := sguA_lt_B_above hθ hY hβ hφπ (by linarith) hSP (Y := Y)
  have hcont := (sguAB_continuousAt (θ := θ) (β := β) (Pis := Pis) (φπ := φπ) hY hS0).1
  have hev : ∀ᶠ x in 𝓝 S, sguA θ Y β Pis φπ x < sguB θ Y β Pis φπ S :=
    hcont.eventually (gt_mem_nhds hAB)
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨v, ⟨q, rfl⟩, hv⟩ := exists_lt_of_lt_csSup hne (by linarith : S - δ < S)
  have hd : dist (Pi_ q.1 q.2) S < δ := by
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith, by linarith [hle q.1 q.2]⟩
  have := hδP hd
  linarith [hlow q.1 q.2]

/-! ## Uniqueness when information stops arriving (all finite event trees) -/

/-- Woodford (2003), p. 137 (setting of the uniqueness claim): information is **eventually
resolved** when `E_t` no longer changes after some date `T₀` — true on every finite event tree
(`finiteTree_eventuallyResolved`), false for perpetual sunspots. -/
def EventuallyResolved (𝔼 : ExpectationSystem Ω) : Prop :=
  ∃ T0, ∀ t, T0 ≤ t → ∀ y, 𝔼.E t y = 𝔼.E T0 y

/-- Woodford (2003), p. 137 and p. 655, **Π* is the unique rational-expectations equilibrium on
any informationally closed, eventually resolved expectation system** (in particular on every
finite event tree, `sgu_finiteTree_unique`): under `φ_π > 1`, `Π* > β`, the E5 hypothesis and
liabilities growing at `1 < μ̄ < Π*/β`, every stochastic equilibrium (positive adapted `Π`, prices
`P_{t+1} = Π_{t+1} P_t`, stochastic (4.5)) satisfying the stochastic transversality condition is
`Π ≡ Π*`. (After `T₀` every path is a perfect-foresight path, which is `Π*` by
`SchmittGroheUribe.sgu_unique_pf_equilibrium`; backwards, `A(Π_t) = E_t[B(Π*)] = A(Π*)` forces
`Π_t = Π*`.) -/
theorem stoch_unique_of_resolved (𝔼 : ExpectationSystem Ω) (hcl : InfoClosed 𝔼)
    (hres : EventuallyResolved 𝔼) {θ Y β Pis φπ μ : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hβ : 0 < β)
    (hφπ : 1 < φπ) (hPis : β < Pis) (hc : 0 < sguC θ β Pis φπ) (hμ : 1 < μ)
    (hμPis : β * μ < Pis) {Pi_ P : ℕ → Ω → ℝ} {D : ℕ → ℝ}
    (hpath : StochPath 𝔼 θ Y β Pis φπ Pi_) (hP : ∀ t ω, 0 < P t ω)
    (hPrec : ∀ t ω, P (t + 1) ω = Pi_ (t + 1) ω * P t ω) (hPad : ∀ t, 𝔼.E t (P t) = P t)
    (hD : ∀ t, D (t + 1) = μ * D t) (hDpos : ∀ t, 0 < D t)
    (htvc : StochTVC 𝔼 θ Y β Pis φπ Pi_ P D) : ∀ t ω, Pi_ t ω = Pis := by
  obtain ⟨T0, hT0⟩ := hres
  -- variables dated after `T₀` are known at `T₀`
  have hknownPi : ∀ s, T0 ≤ s → 𝔼.E T0 (Pi_ s) = Pi_ s := fun s hs => by
    rw [← hT0 s hs]; exact hpath.2.1 s
  have hknownP : ∀ s, T0 ≤ s → 𝔼.E T0 (P s) = P s := fun s hs => by
    rw [← hT0 s hs]; exact hPad s
  -- after `T₀` the equation holds state by state
  have hpf : ∀ s, T0 ≤ s → ∀ ω, sguB θ Y β Pis φπ (Pi_ (s + 1) ω) =
      sguA θ Y β Pis φπ (Pi_ s ω) := by
    intro s hs ω
    have h1 : 𝔼.E T0 (fun ω => sguB θ Y β Pis φπ (Pi_ (s + 1) ω)) =
        fun ω => sguB θ Y β Pis φπ (Pi_ (s + 1) ω) := by
      refine hcl T0 _ (fun a b h => ?_)
      simp only [cellConst_of_known 𝔼 (hknownPi (s + 1) (by omega)) a b h]
    have h2 := hpath.2.2 s
    rw [hT0 s hs, h1] at h2
    exact congrFun h2 ω
  -- the TVC at `T₀` holds state by state
  have htvc' : ∀ ω, Tendsto (fun T => tvcValue β (lamSGU θ Y) (phiSGU β Pis φπ)
      (fun s => Pi_ s ω) (fun s => P s ω) D T) atTop (𝓝 0) := by
    intro ω
    refine (htvc T0 ω).congr' ?_
    filter_upwards [eventually_ge_atTop T0] with T hT
    have h1 : 𝔼.E T0 (fun ω' => tvcValue β (lamSGU θ Y) (phiSGU β Pis φπ)
        (fun s => Pi_ s ω') (fun s => P s ω') D T) = fun ω' => tvcValue β (lamSGU θ Y)
        (phiSGU β Pis φπ) (fun s => Pi_ s ω') (fun s => P s ω') D T := by
      refine hcl T0 _ (fun a b h => ?_)
      have e1 := cellConst_of_known 𝔼 (hknownPi T hT) a b h
      have e2 := cellConst_of_known 𝔼 (hknownP T hT) a b h
      simp only [tvcValue, e1, e2]
    exact congrFun h1 ω
  -- after `T₀`: the perfect-foresight theorem
  have hlate : ∀ s ω, Pi_ (T0 + s) ω = Pis := by
    intro s ω
    have hpath' : IsPath45 β (lamSGU θ Y) (phiSGU β Pis φπ) (fun s => Pi_ (T0 + s) ω) := by
      refine ⟨fun s => hpath.1 _ ω, fun s => ?_⟩
      have h := hpf (T0 + s) (by omega) ω
      exact (eq45_iff_AB hθ hY (hpath.1 _ ω)).mpr h
    have hres := (sgu_unique_pf_equilibrium (P := fun s => P (T0 + s) ω)
      (D := fun s => D (T0 + s)) hθ hY hβ hφπ hPis hc hμ hμPis hpath' (fun s => hP _ ω)
      (fun s => hPrec (T0 + s) ω) (fun s => hD (T0 + s)) (fun s => hDpos _)).2
    have hval : ∀ T, tvcValue β (lamSGU θ Y) (phiSGU β Pis φπ) (fun s => Pi_ (T0 + s) ω)
        (fun s => P (T0 + s) ω) (fun s => D (T0 + s)) T =
        (β ^ T0)⁻¹ * tvcValue β (lamSGU θ Y) (phiSGU β Pis φπ) (fun s => Pi_ s ω)
          (fun s => P s ω) D (T + T0) := by
      intro T
      simp only [tvcValue, pow_add]
      rw [add_comm T T0]
      field_simp
    have hlim : Tendsto (fun T => tvcValue β (lamSGU θ Y) (phiSGU β Pis φπ)
        (fun s => Pi_ (T0 + s) ω) (fun s => P (T0 + s) ω) (fun s => D (T0 + s)) T) atTop
        (𝓝 0) := by
      simp only [hval]
      have h := ((htvc' ω).comp (tendsto_add_atTop_nat T0)).const_mul (β ^ T0)⁻¹
      rw [mul_zero] at h
      exact h
    exact hres.mp hlim s
  -- backwards from `T₀`
  have hback : ∀ s, (∀ ω, Pi_ (s + 1) ω = Pis) → ∀ ω, Pi_ s ω = Pis := by
    intro s hs ω
    have h := congrFun (hpath.2.2 s) ω
    have hc' : (fun ω => sguB θ Y β Pis φπ (Pi_ (s + 1) ω)) =
        fun _ => sguB θ Y β Pis φπ Pis := by
      funext ω'
      rw [hs ω']
    rw [hc', 𝔼.const, ← sguA_target_eq_B hY hβ hPis] at h
    exact sguA_eq_target hY hβ (by linarith) hPis h.symm
  have hkey : ∀ k t, t + k = T0 → ∀ ω, Pi_ t ω = Pis := by
    intro k
    induction k with
    | zero =>
      intro t ht ω
      rw [add_zero] at ht
      subst ht
      simpa using hlate 0 ω
    | succ k ih =>
      intro t ht
      exact hback t (ih (t + 1) (by omega))
  intro t ω
  rcases le_total T0 t with h | h
  · have := hlate (t - T0) ω
    rwa [show T0 + (t - T0) = t by omega] at this
  · exact hkey (T0 - t) t (by omega) ω

/-- Woodford (2003), p. 137: **existence** — on every expectation system the target path
`Π ≡ Π*`, with deterministic prices `P_t = P₀ Π*^t`, is a stochastic equilibrium, and it satisfies
the stochastic transversality condition (for `D` growing at `μ̄ > 0`) iff `βμ̄ < Π*`. -/
theorem stoch_target_equilibrium [Nonempty Ω] (𝔼 : ExpectationSystem Ω) {θ Y β Pis φπ μ P0 : ℝ}
    (hθ : 0 < θ) (hY : 0 < Y) (hβ : 0 < β) (hPis : β < Pis) (hμ : 0 < μ) (hP0 : 0 < P0)
    {D : ℕ → ℝ} (hD : ∀ t, D (t + 1) = μ * D t) (hDpos : ∀ t, 0 < D t) :
    StochPath 𝔼 θ Y β Pis φπ (fun _ _ => Pis) ∧
      (StochTVC 𝔼 θ Y β Pis φπ (fun _ _ => Pis) (fun t _ => P0 * Pis ^ t) D ↔
        β * μ < Pis) := by
  have hP : 0 < Pis := by linarith
  refine ⟨⟨fun _ _ => hP, fun t => 𝔼.const t Pis, fun t => ?_⟩, ?_⟩
  · rw [𝔼.const]
    funext ω
    exact (sguA_target_eq_B hY hβ hPis).symm
  have htarget : 1 + phiSGU β Pis φπ Pis = Pis / β := by
    rw [phiSGU_target hβ hPis.le]; ring
  have hiff := target_tvc_iff (P := fun t => P0 * Pis ^ t) hβ hμ hP htarget
    (lamSGU_phi_pos hθ hY) (fun t => by positivity) (fun t => by ring) hD hDpos
  constructor
  · intro h
    obtain ⟨ω⟩ := (inferInstance : Nonempty Ω)
    refine hiff.mp ?_
    have h1 := h 0 ω
    simp only [𝔼.const] at h1
    exact h1
  · intro h t ω
    simp only [𝔼.const]
    exact hiff.mpr h

/-- Woodford (2003), p. 137: **every finite event tree is eventually resolved** (a refining
sequence of partitions of a finite set is eventually constant). -/
theorem finiteTree_eventuallyResolved {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') : EventuallyResolved T.toExpectationSystem := by
  classical
  set R : ℕ → Finset (Ω' × Ω') := fun t => Finset.univ.filter (fun q => T.info t q.1 q.2)
    with hR
  have hanti : ∀ s t, s ≤ t → R t ⊆ R s := fun s t h q hq => by
    simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact T.refines h _ _ hq
  obtain ⟨T0, hT0⟩ : ∃ T0, ∀ t, (R T0).card ≤ (R t).card := by
    obtain ⟨T0, hT0⟩ := Nat.sInf_mem (Set.range_nonempty fun t => (R t).card)
    change (R T0).card = _ at hT0
    exact ⟨T0, fun t => by rw [hT0]; exact Nat.sInf_le ⟨t, rfl⟩⟩
  refine ⟨T0, fun t ht y => ?_⟩
  have heq : R t = R T0 := Finset.eq_of_subset_of_card_le (hanti T0 t ht) (hT0 t)
  have hinfo : T.info t = T.info T0 := by
    refine Setoid.ext fun a b => ?_
    have : (a, b) ∈ R t ↔ (a, b) ∈ R T0 := by rw [heq]
    simpa [hR] using this
  rw [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E,
    ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  funext ω
  simp only [ExpectationsFiniteTree.FiniteTree.condE, ExpectationsFiniteTree.FiniteTree.num,
    ExpectationsFiniteTree.FiniteTree.mass]
  rw [hinfo]

/-- Woodford (2003), p. 137 and A.17, p. 655, **the claim holds on every finite event tree**:
under `φ_π > 1`, `Π* > β`, the E5 hypothesis `β + θΠ*(1 − φ_π) > 0` and nominal liabilities
growing at `1 < μ̄ < Π*/β`, the target path `Π ≡ Π*` (with `P_t = P₀Π*^t`) is a stochastic
equilibrium satisfying the stochastic transversality condition, and it is the **only** stochastic
equilibrium (positive adapted `Π`, adapted prices `P_{t+1} = Π_{t+1}P_t`) satisfying it — no
sunspot equilibrium exists. -/
theorem sgu_finiteTree_unique {Ω' : Type*} [Fintype Ω'] [Nonempty Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') {θ Y β Pis φπ μ P0 : ℝ} (hθ : 0 < θ) (hY : 0 < Y)
    (hβ : 0 < β) (hφπ : 1 < φπ) (hPis : β < Pis) (hc : 0 < sguC θ β Pis φπ) (hμ : 1 < μ)
    (hμPis : β * μ < Pis) (hP0 : 0 < P0) {D : ℕ → ℝ} (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) :
    (StochPath T.toExpectationSystem θ Y β Pis φπ (fun _ _ => Pis) ∧
      StochTVC T.toExpectationSystem θ Y β Pis φπ (fun _ _ => Pis) (fun t _ => P0 * Pis ^ t) D) ∧
    ∀ Pi_ P : ℕ → Ω' → ℝ, StochPath T.toExpectationSystem θ Y β Pis φπ Pi_ →
      (∀ t ω, 0 < P t ω) → (∀ t ω, P (t + 1) ω = Pi_ (t + 1) ω * P t ω) →
      (∀ t, T.toExpectationSystem.E t (P t) = P t) →
      StochTVC T.toExpectationSystem θ Y β Pis φπ Pi_ P D → ∀ t ω, Pi_ t ω = Pis := by
  obtain ⟨h1, h2⟩ := stoch_target_equilibrium T.toExpectationSystem (φπ := φπ) hθ hY hβ hPis
    (by linarith) hP0 hD hDpos
  refine ⟨⟨h1, h2.mpr hμPis⟩, fun Pi_ P hpath hP hPrec hPad htvc => ?_⟩
  exact stoch_unique_of_resolved T.toExpectationSystem
    (LocalIFTStochastic.finiteTree_infoClosed T) (finiteTree_eventuallyResolved T) hθ hY hβ hφπ
    hPis hc hμ hμPis hpath hP hPrec hPad hD hDpos htvc

/-! ## A perpetual sunspot: the claim fails for infinite-horizon uncertainty

The switching-date model: a state `n ∈ ℕ` with `P(n) = p(1 − p)ⁿ`, `0 < p < 1`; at date `t` one
knows `n` if `n < t` and otherwise only that `n ≥ t` (memoryless: `P(n = t + k | n ≥ t) = p(1 −
p)^k`). `geomE` is the corresponding conditional expectation of bounded random variables (proved
linear, monotone, constant-preserving, with the tower property). It cannot be an
`ExpectationSystem` (whose `E_t` is defined on *all* functions; positive linear functionals on
all of `ℝ^ℕ` are finitely supported, so such systems cannot carry this perpetual uncertainty). -/

/-- Woodford (2003), p. 137 (counterexample): bounded random variables on the switching-date
space. -/
def Bdd (y : ℕ → ℝ) : Prop := ∃ C, ∀ n, |y n| ≤ C

/-- Woodford (2003), p. 137 (counterexample): the conditional expectation at date `t` of the
switching-date model, `E_t y(n) = y(n)` if `n < t`, `= ∑_k p(1 − p)^k y(t + k)` if `n ≥ t`. -/
noncomputable def geomE (p : ℝ) (t : ℕ) (y : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n < t then y n else ∑' k, p * (1 - p) ^ k * y (t + k)

variable {p : ℝ}

/-- Woodford (2003), p. 137 (counterexample): the conditional weights are summable against a
bounded variable. -/
theorem summable_geom (hp0 : 0 < p) (hp1 : p < 1) {y : ℕ → ℝ} (hy : Bdd y) (t : ℕ) :
    Summable (fun k => p * (1 - p) ^ k * y (t + k)) := by
  obtain ⟨C, hC⟩ := hy
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (by linarith) (by linarith : 1 - p < 1)).mul_left (p * C))
    (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hp0, abs_pow, abs_of_pos (by linarith)]
  have := hC (t + k)
  have h1 : 0 ≤ p * (1 - p) ^ k := by positivity
  nlinarith

/-- Woodford (2003), p. 137 (counterexample): the conditional weights sum to one. -/
theorem tsum_geom_weights (hp0 : 0 < p) (hp1 : p < 1) : ∑' k : ℕ, p * (1 - p) ^ k = 1 := by
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by linarith) (by linarith), sub_sub_cancel,
    mul_inv_cancel₀ hp0.ne']

/-- Woodford (2003), p. 137 (counterexample): constants are known. -/
theorem geomE_const (hp0 : 0 < p) (hp1 : p < 1) (t : ℕ) (c : ℝ) (n : ℕ) :
    geomE p t (fun _ => c) n = c := by
  unfold geomE
  split_ifs
  · rfl
  · rw [tsum_mul_right, tsum_geom_weights hp0 hp1, one_mul]

/-- Woodford (2003), p. 137 (counterexample): `E_t` is bounded by the bound of its argument. -/
theorem abs_geomE_le (hp0 : 0 < p) (hp1 : p < 1) {y : ℕ → ℝ} {C : ℝ} (hC : ∀ n, |y n| ≤ C)
    (t n : ℕ) : |geomE p t y n| ≤ C := by
  unfold geomE
  split_ifs
  · exact hC n
  · have hs := summable_geom hp0 hp1 ⟨C, hC⟩ t
    have hw : Summable (fun k : ℕ => p * (1 - p) ^ k * C) :=
      ((summable_geometric_of_lt_one (by linarith) (by linarith : 1 - p < 1)).mul_left p).mul_right
        C
    have hval : ∑' k : ℕ, p * (1 - p) ^ k * C = C := by
      rw [tsum_mul_right, tsum_geom_weights hp0 hp1, one_mul]
    rw [abs_le]
    constructor
    · rw [← hval, ← tsum_neg]
      refine Summable.tsum_le_tsum (fun k => ?_) hw.neg hs
      have h1 : 0 ≤ p * (1 - p) ^ k := by positivity
      have := neg_abs_le (y (t + k))
      have := hC (t + k)
      nlinarith
    · rw [← hval]
      refine Summable.tsum_le_tsum (fun k => ?_) hs hw
      have h1 : 0 ≤ p * (1 - p) ^ k := by positivity
      have := le_abs_self (y (t + k))
      have := hC (t + k)
      nlinarith

/-- Woodford (2003), p. 137 (counterexample): `E_t` of a bounded variable is bounded. -/
theorem bdd_geomE (hp0 : 0 < p) (hp1 : p < 1) {y : ℕ → ℝ} (hy : Bdd y) (t : ℕ) :
    Bdd (geomE p t y) := by
  obtain ⟨C, hC⟩ := hy
  exact ⟨C, abs_geomE_le hp0 hp1 hC t⟩

/-- Woodford (2003), p. 137 (counterexample): `E_t` is additive on bounded variables. -/
theorem geomE_add (hp0 : 0 < p) (hp1 : p < 1) {y z : ℕ → ℝ} (hy : Bdd y) (hz : Bdd z)
    (t n : ℕ) : geomE p t (y + z) n = geomE p t y n + geomE p t z n := by
  unfold geomE
  split_ifs
  · rfl
  · rw [← (summable_geom hp0 hp1 hy t).tsum_add (summable_geom hp0 hp1 hz t)]
    exact tsum_congr fun k => by simp only [Pi.add_apply]; ring

/-- Woodford (2003), p. 137 (counterexample): `E_t` is homogeneous. -/
theorem geomE_smul (c : ℝ) (y : ℕ → ℝ) (t n : ℕ) :
    geomE p t (c • y) n = c * geomE p t y n := by
  unfold geomE
  split_ifs
  · rfl
  · rw [← tsum_mul_left]
    exact tsum_congr fun k => by simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- Woodford (2003), p. 137 (counterexample): `E_t` is monotone on bounded variables. -/
theorem geomE_mono (hp0 : 0 < p) (hp1 : p < 1) {y z : ℕ → ℝ} (hy : Bdd y) (hz : Bdd z)
    (h : y ≤ z) (t n : ℕ) : geomE p t y n ≤ geomE p t z n := by
  unfold geomE
  split_ifs
  · exact h n
  · refine Summable.tsum_le_tsum (fun k => ?_) (summable_geom hp0 hp1 hy t)
      (summable_geom hp0 hp1 hz t)
    have h1 : 0 ≤ p * (1 - p) ^ k := by positivity
    exact mul_le_mul_of_nonneg_left (h (t + k)) h1

/-- Woodford (2003), p. 137 (counterexample): above date `t` the forecast is the same in every
state of the cell `n ≥ t`. -/
theorem geomE_of_le (y : ℕ → ℝ) {t n : ℕ} (h : t ≤ n) :
    geomE p t y n = ∑' k, p * (1 - p) ^ k * y (t + k) := by
  unfold geomE
  simp only [show ¬ n < t by omega, ↓reduceIte]

/-- Woodford (2003), p. 137 (counterexample): earlier forecasts are known later,
`E_t E_s = E_s` for `s ≤ t`. -/
theorem geomE_known (hp0 : 0 < p) (hp1 : p < 1) {s t : ℕ} (hst : s ≤ t) (y : ℕ → ℝ) (n : ℕ) :
    geomE p t (geomE p s y) n = geomE p s y n := by
  by_cases hn : n < t
  · unfold geomE
    simp only [hn, ↓reduceIte]
  · rw [geomE_of_le _ (by omega), geomE_of_le _ (by omega : s ≤ n)]
    have hc : ∀ k, geomE p s y (t + k) = ∑' j, p * (1 - p) ^ j * y (s + j) := fun k =>
      geomE_of_le y (by omega)
    simp only [hc]
    rw [tsum_mul_right, tsum_geom_weights hp0 hp1, one_mul]

/-- Woodford (2003), p. 137 (counterexample): **the law of iterated expectations**,
`E_s E_t = E_s` for `s ≤ t`, on bounded variables. -/
theorem geomE_tower (hp0 : 0 < p) (hp1 : p < 1) {s t : ℕ} (hst : s ≤ t) {y : ℕ → ℝ}
    (hy : Bdd y) (n : ℕ) : geomE p s (geomE p t y) n = geomE p s y n := by
  by_cases hn : n < s
  · unfold geomE
    simp only [hn, show n < t by omega, ↓reduceIte]
  rw [geomE_of_le _ (by omega), geomE_of_le _ (by omega)]
  set d := t - s with hd
  set c := ∑' j, p * (1 - p) ^ j * y (t + j) with hc
  have hL := (summable_geom hp0 hp1 (bdd_geomE hp0 hp1 hy t) s).sum_add_tsum_nat_add d
  have hR := (summable_geom hp0 hp1 hy s).sum_add_tsum_nat_add d
  rw [← hL, ← hR]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    unfold geomE
    simp only [show s + k < t by omega, ↓reduceIte]
  · have h1 : ∀ j, p * (1 - p) ^ (j + d) * geomE p t y (s + (j + d)) =
        (1 - p) ^ d * (p * (1 - p) ^ j * c) := fun j => by
      rw [geomE_of_le y (by omega), pow_add]
      ring
    have h2 : ∀ j, p * (1 - p) ^ (j + d) * y (s + (j + d)) =
        (1 - p) ^ d * (p * (1 - p) ^ j * y (t + j)) := fun j => by
      rw [pow_add, show s + (j + d) = t + j by omega]
      ring
    simp only [h1, h2]
    rw [tsum_mul_left, tsum_mul_left, tsum_mul_right, tsum_geom_weights hp0 hp1, one_mul]

/-! ### The sunspot equilibrium -/

/-- Woodford (2003), A.17 (counterexample): inflation `Π_t(n) = Π* = 1` once the sunspot has
switched (`n < t`), and `Π_low = 1/3` (a zero-interest deflation) before. -/
noncomputable def sunPi (t n : ℕ) : ℝ := if n < t then 1 else 1 / 3

/-- Woodford (2003), A.17 (counterexample): the price level `P_t(n) = (1/3)^{min(t, n)}`
(`P₀ = 1`). -/
noncomputable def sunP (t n : ℕ) : ℝ := (1 / 3) ^ min t n

/-- Woodford (2003), A.17 (counterexample): the values `A(1) = 3/2`, `A(1/3) = 2`, `B(1) = 3/2`,
`B(1/3) = 3` for `θ = 1, Ȳ = 1, β = 1/2, Π* = 1, φ_π = 5/4`. -/
theorem sun_AB :
    sguA 1 1 (1 / 2) 1 (5 / 4) 1 = 3 / 2 ∧ sguA 1 1 (1 / 2) 1 (5 / 4) (1 / 3) = 2 ∧
      sguB 1 1 (1 / 2) 1 (5 / 4) 1 = 3 / 2 ∧ sguB 1 1 (1 / 2) 1 (5 / 4) (1 / 3) = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [(sguAB_formula _ _ _ _ _ _).1, (sguAB_formula _ _ _ _ _ _).2, ellSGU] <;> norm_num

/-- Woodford (2003), A.17 (counterexample): `λ(φ(1)) = 3` and `λ(φ(1/3)) = 2`. -/
theorem sun_lam :
    lamSGU 1 1 (phiSGU (1 / 2) 1 (5 / 4) 1) = 3 ∧
      lamSGU 1 1 (phiSGU (1 / 2) 1 (5 / 4) (1 / 3)) = 2 := by
  refine ⟨?_, ?_⟩ <;> simp only [lamSGU, phiSGU, ellSGU] <;> norm_num

/-- Woodford (2003), A.17 (counterexample): `Π_t` is positive. -/
theorem sunPi_pos (t n : ℕ) : 0 < sunPi t n := by
  unfold sunPi
  split_ifs <;> norm_num

/-- Woodford (2003), A.17 (counterexample): `Π_t` takes the values `1` or `1/3`. -/
theorem sunPi_bdd (t : ℕ) : Bdd (sunPi t) :=
  ⟨1, fun n => by unfold sunPi; split_ifs <;> norm_num⟩

/-- Woodford (2003), A.17 (counterexample): `λ_t = λ(φ(Π_t)) ≤ 3` and positive. -/
theorem sun_lam_bounds (T n : ℕ) :
    0 < lamSGU 1 1 (phiSGU (1 / 2) 1 (5 / 4) (sunPi T n)) ∧
      lamSGU 1 1 (phiSGU (1 / 2) 1 (5 / 4) (sunPi T n)) ≤ 3 := by
  unfold sunPi
  split_ifs
  · rw [sun_lam.1]; norm_num
  · rw [sun_lam.2]; norm_num

/-- Woodford (2003), A.17 (counterexample): `B(Π_t)` is bounded. -/
theorem sunB_bdd (t : ℕ) : Bdd (fun n => sguB 1 1 (1 / 2) 1 (5 / 4) (sunPi t n)) :=
  ⟨3, fun n => by
    change |sguB 1 1 (1 / 2) 1 (5 / 4) (sunPi t n)| ≤ 3
    unfold sunPi
    split_ifs
    · rw [sun_AB.2.2.1]; norm_num
    · rw [sun_AB.2.2.2]; norm_num⟩

/-- Woodford (2003), (4.5) under uncertainty (counterexample): **the sunspot process solves
`A(Π_t) = E_t[B(Π_{t+1})]`** — after the switch `A(1) = B(1)`; before it
`p B(1) + (1 − p) B(1/3) = (2/3)(3/2) + (1/3)·3 = 2 = A(1/3)`. -/
theorem sun_eq45 (t : ℕ) :
    geomE (2 / 3) t (fun n => sguB 1 1 (1 / 2) 1 (5 / 4) (sunPi (t + 1) n)) =
      fun n => sguA 1 1 (1 / 2) 1 (5 / 4) (sunPi t n) := by
  funext n
  by_cases hn : n < t
  · unfold geomE sunPi
    simp only [hn, show n < t + 1 by omega, ↓reduceIte]
    rw [sun_AB.1, sun_AB.2.2.1]
  · rw [geomE_of_le _ (by omega)]
    have hs : sunPi t n = 1 / 3 := by unfold sunPi; simp only [hn, ↓reduceIte]
    rw [hs, sun_AB.2.1,
      (summable_geom (by norm_num) (by norm_num) (sunB_bdd (t + 1)) t).tsum_eq_zero_add]
    have h0 : sunPi (t + 1) (t + 0) = 1 := by
      unfold sunPi; simp only [show t + 0 < t + 1 by omega, ↓reduceIte]
    have h1 : ∀ k, (2 / 3 : ℝ) * (1 - 2 / 3) ^ (k + 1) *
        sguB 1 1 (1 / 2) 1 (5 / 4) (sunPi (t + 1) (t + (k + 1))) =
        2 / 3 * (1 - 2 / 3) ^ k * 1 := fun k => by
      have : sunPi (t + 1) (t + (k + 1)) = 1 / 3 := by
        unfold sunPi; simp only [show ¬ t + (k + 1) < t + 1 by omega, ↓reduceIte]
      rw [this, sun_AB.2.2.2, pow_succ]
      ring
    simp only [h0, h1]
    rw [tsum_mul_right, tsum_geom_weights (by norm_num) (by norm_num), sun_AB.2.2.1]
    norm_num

/-- Woodford (2003), A.17 (counterexample): the sunspot inflation process is adapted. -/
theorem sunPi_adapted (t : ℕ) : geomE (2 / 3) t (sunPi t) = sunPi t := by
  funext n
  by_cases hn : n < t
  · unfold geomE
    simp only [hn, ↓reduceIte]
  · rw [geomE_of_le _ (by omega)]
    have h : ∀ k, sunPi t (t + k) = 1 / 3 := fun k => by
      unfold sunPi; simp only [show ¬ t + k < t by omega, ↓reduceIte]
    simp only [h]
    rw [tsum_mul_right, tsum_geom_weights (by norm_num) (by norm_num), one_mul]
    unfold sunPi
    simp only [hn, ↓reduceIte]

/-- Woodford (2003), A.17 (counterexample): prices are positive. -/
theorem sunP_pos (t n : ℕ) : 0 < sunP t n := by
  unfold sunP
  positivity

/-- Woodford (2003), A.17 (counterexample): `P_{t+1} = Π_{t+1} P_t`. -/
theorem sunP_succ (t n : ℕ) : sunP (t + 1) n = sunPi (t + 1) n * sunP t n := by
  unfold sunP sunPi
  by_cases hn : n < t + 1
  · simp only [hn, ↓reduceIte, one_mul]
    rw [min_eq_right (by omega), min_eq_right (by omega)]
  · simp only [hn, ↓reduceIte]
    rw [min_eq_left (by omega), min_eq_left (by omega), pow_succ]
    ring

/-- Woodford (2003), A.17 (counterexample): the price process is adapted. -/
theorem sunP_adapted (t : ℕ) : geomE (2 / 3) t (sunP t) = sunP t := by
  funext n
  by_cases hn : n < t
  · unfold geomE
    simp only [hn, ↓reduceIte]
  · rw [geomE_of_le _ (by omega)]
    have h : ∀ k, sunP t (t + k) = (1 / 3) ^ t := fun k => by
      unfold sunP; rw [min_eq_left (by omega)]
    simp only [h]
    rw [tsum_mul_right, tsum_geom_weights (by norm_num) (by norm_num), one_mul]
    unfold sunP
    rw [min_eq_left (by omega)]

/-- Woodford (2003), A.17 (counterexample): the transversality value
`β^T λ_T D_T/P_T` along state `n`, with `D_T = μ^T`. -/
noncomputable def sunV (μ : ℝ) (T n : ℕ) : ℝ :=
  tvcValue (1 / 2) (lamSGU 1 1) (phiSGU (1 / 2) 1 (5 / 4)) (fun s => sunPi s n)
    (fun s => sunP s n) (fun s => μ ^ s) T

/-- Woodford (2003), A.17 (counterexample): `0 ≤ β^T λ_T D_T/P_T ≤ 3 (μ/2)^T 3^{min(T, n)}`. -/
theorem sunV_bounds {μ : ℝ} (hμ : 0 < μ) (T n : ℕ) :
    0 ≤ sunV μ T n ∧ sunV μ T n ≤ 3 * (μ / 2) ^ T * 3 ^ min T n := by
  obtain ⟨hl0, hl3⟩ := sun_lam_bounds T n
  have hv : sunV μ T n = (μ / 2) ^ T * lamSGU 1 1 (phiSGU (1 / 2) 1 (5 / 4) (sunPi T n)) *
      3 ^ min T n := by
    unfold sunV tvcValue sunP
    beta_reduce
    field_simp
    have h3 : (1 / 3 : ℝ) ^ min T n * 3 ^ min T n = 1 := by rw [← mul_pow]; norm_num
    have h2 : (1 / 2 : ℝ) ^ T * μ ^ T = (μ / 2) ^ T := by rw [← mul_pow]; ring_nf
    rw [h2]
    linear_combination (-(μ / 2) ^ T) * h3
  rw [hv]
  refine ⟨by positivity, ?_⟩
  have h1 : 0 ≤ (μ / 2) ^ T := by positivity
  have h2 : (0 : ℝ) ≤ 3 ^ min T n := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hl3 h1]

/-- Woodford (2003), A.17 (counterexample): for `1 ≤ r ≤ 3`,
`(1/3)^k 3^{min(T, t+k)} ≤ 3^t r^T (1/r)^k`. -/
theorem key_pow_bound {r : ℝ} (hr1 : 1 ≤ r) (hr3 : r ≤ 3) (t T k : ℕ) :
    (1 / 3 : ℝ) ^ k * 3 ^ min T (t + k) ≤ 3 ^ t * r ^ T * (1 / r) ^ k := by
  have hr0 : 0 < r := by linarith
  have h3k : (0 : ℝ) < 3 ^ k := by positivity
  have hrk : (0 : ℝ) < r ^ k := by positivity
  suffices h : (3 : ℝ) ^ min T (t + k) * r ^ k ≤ 3 ^ t * r ^ T * 3 ^ k by
    rw [one_div_pow, one_div_pow, div_mul_eq_mul_div, one_mul, mul_one_div,
      div_le_div_iff₀ h3k hrk]
    nlinarith
  rcases le_total (t + k) T with h | h
  · rw [min_eq_right h, pow_add]
    have := pow_le_pow_right₀ hr1 (show k ≤ T by omega)
    have h3t : (0 : ℝ) < 3 ^ t := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this (le_of_lt (mul_pos h3t h3k))]
  · rw [min_eq_left h]
    rcases le_total k T with hk | hk
    · have e1 := pow_le_pow_right₀ hr1 hk
      have e2 : (3 : ℝ) ^ T ≤ 3 ^ t * 3 ^ k := by
        rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) h
      have h3T : (0 : ℝ) < 3 ^ T := by positivity
      calc (3 : ℝ) ^ T * r ^ k ≤ (3 ^ t * 3 ^ k) * r ^ T :=
            mul_le_mul e2 e1 hrk.le (by positivity)
        _ = 3 ^ t * r ^ T * 3 ^ k := by ring
    · have e1 : r ^ k ≤ r ^ T * 3 ^ (k - T) := by
        rw [show r ^ k = r ^ T * r ^ (k - T) by rw [← pow_add]; congr 1; omega]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0.le hr3 _) (by positivity)
      have e2 : (3 : ℝ) ^ T * 3 ^ (k - T) = 3 ^ k := by rw [← pow_add]; congr 1; omega
      have h3t : (1 : ℝ) ≤ 3 ^ t := one_le_pow₀ (by norm_num)
      calc (3 : ℝ) ^ T * r ^ k ≤ 3 ^ T * (r ^ T * 3 ^ (k - T)) :=
            mul_le_mul_of_nonneg_left e1 (by positivity)
        _ = 3 ^ k * r ^ T := by rw [← e2]; ring
        _ ≤ 3 ^ t * r ^ T * 3 ^ k := by
          have h' := mul_le_mul_of_nonneg_right h3t (le_of_lt (mul_pos (pow_pos hr0 T) h3k))
          linarith [h']

/-- Woodford (2003), (1.24) under uncertainty (counterexample): **the sunspot equilibrium
satisfies the stochastic transversality condition** `lim_T β^T E_t[λ_T D_T/P_T] = 0` at every
date and in every state, for every growth rate `1 < μ̄ < 2 = Π*/β` of nominal liabilities. -/
theorem sun_tvc {μ : ℝ} (hμ1 : 1 < μ) (hμ2 : μ < 2) (t n : ℕ) :
    Tendsto (fun T => geomE (2 / 3) t (sunV μ T) n) atTop (𝓝 0) := by
  have hμ0 : 0 < μ := by linarith
  have hq : μ / 2 < 1 := by linarith
  by_cases hn : n < t
  · have he : ∀ T, geomE (2 / 3) t (sunV μ T) n = sunV μ T n := fun T => by
      unfold geomE; simp only [hn, ↓reduceIte]
    simp only [he]
    refine squeeze_zero (fun T => (sunV_bounds hμ0 T n).1) (fun T => ?_)
      (g := fun T => 3 * 3 ^ n * (μ / 2) ^ T) ?_
    · have h := (sunV_bounds hμ0 T n).2
      have h3 : (3 : ℝ) ^ min T n ≤ 3 ^ n := pow_le_pow_right₀ (by norm_num) (min_le_right _ _)
      have h4 : 0 ≤ (μ / 2) ^ T := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h3 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) h4)]
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hq).const_mul
        (3 * 3 ^ n)
  · set r := (2 + μ) / (2 * μ) with hr
    have hr1 : 1 < r := by rw [hr, one_lt_div (by positivity)]; linarith
    have hr3 : r ≤ 3 := by rw [hr, div_le_iff₀ (by positivity)]; linarith
    have hmr : μ * r / 2 < 1 := by
      rw [hr]; field_simp; linarith
    have hmr0 : 0 ≤ μ * r / 2 := by positivity
    have hinv : 1 / r < 1 := by rw [div_lt_one (by linarith)]; exact hr1
    have hbdd : ∀ T, Bdd (sunV μ T) := fun T => ⟨3 * (μ / 2) ^ T * 3 ^ T, fun m => by
      obtain ⟨h0, h1⟩ := sunV_bounds hμ0 T m
      rw [abs_of_nonneg h0]
      have h3 : (3 : ℝ) ^ min T m ≤ 3 ^ T := pow_le_pow_right₀ (by norm_num) (min_le_left _ _)
      have h4 : 0 ≤ 3 * (μ / 2) ^ T := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h3 h4]⟩
    set K := 2 * 3 ^ t * (∑' k : ℕ, (1 / r) ^ k) with hK
    refine squeeze_zero (fun T => ?_) (fun T => ?_) (g := fun T => K * (μ * r / 2) ^ T) ?_
    · have := geomE_mono (p := 2 / 3) (by norm_num) (by norm_num) (y := fun _ => 0)
        ⟨0, fun _ => by simp⟩ (hbdd T) (fun m => (sunV_bounds hμ0 T m).1) t n
      rwa [geomE_const (by norm_num) (by norm_num)] at this
    · rw [geomE_of_le _ (by omega)]
      have hs := summable_geom (p := 2 / 3) (by norm_num) (by norm_num) (hbdd T) t
      have hg : Summable (fun k : ℕ => 2 * 3 ^ t * (μ * r / 2) ^ T * (1 / r) ^ k) :=
        (summable_geometric_of_lt_one (by positivity) hinv).mul_left _
      calc ∑' k, 2 / 3 * (1 - 2 / 3) ^ k * sunV μ T (t + k)
          ≤ ∑' k : ℕ, 2 * 3 ^ t * (μ * r / 2) ^ T * (1 / r) ^ k := by
            refine Summable.tsum_le_tsum (fun k => ?_) hs hg
            have hb := (sunV_bounds hμ0 T (t + k)).2
            have hk := key_pow_bound hr1.le hr3 t T k
            have hw : (2 / 3 : ℝ) * (1 - 2 / 3) ^ k = 2 / 3 * (1 / 3) ^ k := by norm_num
            rw [hw]
            have hpos : (0 : ℝ) ≤ 2 / 3 * (1 / 3) ^ k := by positivity
            have hm : (μ * r / 2) ^ T = (μ / 2) ^ T * r ^ T := by
              rw [← mul_pow]; ring_nf
            rw [hm]
            have hq0 : (0 : ℝ) ≤ (μ / 2) ^ T := by positivity
            calc 2 / 3 * (1 / 3) ^ k * sunV μ T (t + k)
                ≤ 2 / 3 * (1 / 3) ^ k * (3 * (μ / 2) ^ T * 3 ^ min T (t + k)) :=
                  mul_le_mul_of_nonneg_left hb hpos
              _ = 2 * (μ / 2) ^ T * ((1 / 3) ^ k * 3 ^ min T (t + k)) := by ring
              _ ≤ 2 * (μ / 2) ^ T * (3 ^ t * r ^ T * (1 / r) ^ k) :=
                  mul_le_mul_of_nonneg_left hk (by positivity)
              _ = 2 * 3 ^ t * ((μ / 2) ^ T * r ^ T) * (1 / r) ^ k := by ring
        _ = K * (μ * r / 2) ^ T := by
            rw [tsum_mul_left, hK]
            ring
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hmr0 hmr).const_mul K

/-- Woodford (2003), (4.4)/(1.23), p. 124, under uncertainty (counterexample): the sunspot
equilibrium satisfies the bound `∑_T β^T E_t[λ_T (Ȳ + i_T/(1 + i_T) L(Ȳ, i_T))] < ∞` at every
date and state (the integrand is between `0` and `6`). -/
theorem sun_bound44 (t n : ℕ) :
    Summable (fun T : ℕ => (1 / 2 : ℝ) ^ T * geomE (2 / 3) t (fun m =>
      lamSGU 1 1 (phiSGU (1 / 2) 1 (5 / 4) (sunPi T m)) *
        (1 + phiSGU (1 / 2) 1 (5 / 4) (sunPi T m) / (1 + phiSGU (1 / 2) 1 (5 / 4) (sunPi T m)) *
          SchmittGroheUribe.LSGU 1 1 (phiSGU (1 / 2) 1 (5 / 4) (sunPi T m)))) n) := by
  have hw : ∀ T m, |lamSGU 1 1 (phiSGU (1 / 2) 1 (5 / 4) (sunPi T m)) *
      (1 + phiSGU (1 / 2) 1 (5 / 4) (sunPi T m) / (1 + phiSGU (1 / 2) 1 (5 / 4) (sunPi T m)) *
        SchmittGroheUribe.LSGU 1 1 (phiSGU (1 / 2) 1 (5 / 4) (sunPi T m)))| ≤ 6 := by
    intro T m
    obtain ⟨hl0, hl3⟩ := sun_lam_bounds T m
    set i := phiSGU (1 / 2) 1 (5 / 4) (sunPi T m) with hi
    have hi0 : 0 ≤ i := phiSGU_nonneg _ _ _ _
    have hq0 : 0 ≤ i / (1 + i) := by positivity
    have hq1 : i / (1 + i) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have hL0 : 0 ≤ SchmittGroheUribe.LSGU 1 1 i := by
      unfold SchmittGroheUribe.LSGU; positivity
    have hL1 : SchmittGroheUribe.LSGU 1 1 i ≤ 1 := by
      unfold SchmittGroheUribe.LSGU; rw [div_le_one (by linarith)]; linarith
    have hprod : i / (1 + i) * SchmittGroheUribe.LSGU 1 1 i ≤ 1 := by nlinarith
    have hin : 0 ≤ 1 + i / (1 + i) * SchmittGroheUribe.LSGU 1 1 i := by positivity
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)).mul_left 6)
    (fun T => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity), mul_comm 6]
  exact mul_le_mul_of_nonneg_left (abs_geomE_le (by norm_num) (by norm_num) (hw T) t n)
    (by positivity)

/-- Woodford (2003), p. 137 ("one can show that it is the unique rational-expectations
equilibrium, even allowing for stochastic equilibria of arbitrary form") and A.17, **the claim is
false for infinite-horizon sunspots**: take `θ = 1`, `Ȳ = 1`, `β = 1/2`, `Π* = 1`, `φ_π = 5/4` (so
`φ_π > 1`, `Π* > β` and the E5 hypothesis `β + θΠ*(1 − φ_π) = 1/4 > 0` hold) and nominal
liabilities `D_T = μ̄^T` with any `1 < μ̄ < Π*/β = 2`. In the switching-date model with switch
probability `p = 2/3` per period, inflation `Π_t = 1/3` (zero interest rate) until the sunspot
switches and `Π_t = Π*` afterwards, with `P_t = (1/3)^{min(t, n)}`, is positive and adapted,
satisfies the stochastic (4.5) `A(Π_t) = E_t[B(Π_{t+1})]` at every date, the stochastic
transversality condition (1.24) at every date and state (the bound (4.4) is `sun_bound44`)
— and yet
`Π₀ = 1/3 ≠ Π*` in every state. So the corrected statement is the finite-tree theorem
`sgu_finiteTree_unique` (and `stoch_unique_of_resolved`); no-hyperinflation
(`stoch_no_hyperinflation`) survives in general (here `Π_t ≤ Π*`). -/
theorem sgu_sunspot_refutation {μ : ℝ} (hμ1 : 1 < μ) (hμ2 : μ < 2) :
    ((1 : ℝ) < 5 / 4 ∧ (1 / 2 : ℝ) < 1 ∧ 0 < sguC 1 (1 / 2) 1 (5 / 4) ∧ 1 / 2 * μ < 1) ∧
    (∀ t n, 0 < sunPi t n) ∧ (∀ t, geomE (2 / 3) t (sunPi t) = sunPi t) ∧
    (∀ t, geomE (2 / 3) t (fun n => sguB 1 1 (1 / 2) 1 (5 / 4) (sunPi (t + 1) n)) =
      fun n => sguA 1 1 (1 / 2) 1 (5 / 4) (sunPi t n)) ∧
    (∀ t n, 0 < sunP t n) ∧ (∀ t n, sunP (t + 1) n = sunPi (t + 1) n * sunP t n) ∧
    (∀ t, geomE (2 / 3) t (sunP t) = sunP t) ∧
    (∀ t n, Tendsto (fun T => geomE (2 / 3) t (fun m =>
      tvcValue (1 / 2) (lamSGU 1 1) (phiSGU (1 / 2) 1 (5 / 4)) (fun s => sunPi s m)
        (fun s => sunP s m) (fun s => μ ^ s) T) n) atTop (𝓝 0)) ∧
    (∀ t n, sunPi t n ≤ 1) ∧ (∀ n, sunPi 0 n ≠ 1) := by
  refine ⟨⟨by norm_num, by norm_num, by unfold sguC; norm_num, by linarith⟩, sunPi_pos,
    sunPi_adapted, sun_eq45, sunP_pos, sunP_succ, sunP_adapted, fun t n => sun_tvc hμ1 hμ2 t n,
    fun t n => ?_, fun n => ?_⟩
  · unfold sunPi; split_ifs <;> norm_num
  · unfold sunPi; simp

end Woodford.PriceLevelDetermination.SGUStochastic
