/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.TidyR6StochasticLowerBound
import NewKeynesianSelection.SelectionPatches

/-!
# The selection patches of §16.10 under uncertainty

Cochrane (2023), Chapter 16, §§16.10.2–16.10.6, pp. 386–394. The module SelectionPatches proves the
nonlinear claims under perfect foresight. Here they are proved for an arbitrary
`ExpectationSystem`: sunspot equilibria are allowed, and the patches must remove them too. The
growth lemma `TidyR6StochasticLowerBound.growth_zero` replaces the monotone-orbit arguments.

## Main results

* ACK (§16.10.2, p. 389): `StochACK`, `firstInd`, `stoch_ack_inconsistent`,
  `stoch_ack_bounded` (with `ExpectationSystem.PullOut` and the first-exceedance event known at its
  date —
  `firstInd_known_tree` proves this on every finite tree), `stoch_ack_prunes_inflation` (no
  equilibrium, sunspots included, has `Π_t > Π*` in any state), `linRule_gap_above`,
  `const_stochACK` and `stoch_ack_keeps_deflation` (the deflationary paths remain).
* Stopping an inflation (§16.10.2, p. 386): `StochStab`, `const_stochStab`,
  `stoch_stop_not_rule_out`.
* Bassetto (§16.10.4, p. 391): `stoch_bassetto` (with the zero bound, no equilibrium has
  `Π_t < Π*` in any state), `linRule_gap_below`, `linRule_lo`, `stoch_bassetto_linear`.
* V-shaped rules (§16.10.5, p. 392): `stoch_v_rule` (the only bounded equilibrium is `Π*`),
  `vRule_gap`, `stoch_vRule`.
* BSGU (§16.10.3, p. 390): `stoch_bsgu_tvc_violated`; Woodford's `μ̄` rule:
  `stoch_mubar_tvc_violated`.
* (16.31)–(16.32) (§16.10.6, p. 393): `stochEq1632_of_bond` (the stochastic (16.32)
  `E_t[k(Π_{t+1})/Π_{t+1}] = k(Π_t)/Φ(Π_t)`), `boundedRule_h_ge` and
  `stoch_bounded_rule_explosion` (in the bounded-rule model no random `Π_{t+1}` exists for
  `Π_t ∈ (1, 3/2)`).
* Sims (1994) (§16.10.6, p. 394): `stoch_sims_tvc_violated`.
-/

namespace Cochrane.NewKeynesianSelection.TidyR6StochasticPatches

open Filter Topology TidyR6StochasticLowerBound

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ## Bond pricing with the rule -/

/-- Cochrane (2023), eqs. (16.25), (16.27), p. 378: where the rule holds, the
bond-pricing equation gives `E_t(1/Π_{t+1}) = 1/Φ(Π_t)` in that state. -/
theorem E_inv_of_rule {r : ℝ} (hr : 0 < 1 + r) {Φ : ℝ → ℝ} {infl i : ℕ → Ω → ℝ}
    (hbp : LowerBound.BondPricing 𝔼 r i infl) {t : ℕ} {ω : Ω}
    (hrule : 1 + i t ω = (1 + r) * Φ (infl t ω)) :
    𝔼.E t (fun ω => 1 / infl (t + 1) ω) ω = 1 / Φ (infl t ω) := by
  have e := congrFun (hbp t) ω
  simp only [Pi.smul_apply, smul_eq_mul] at e
  rw [hrule, one_div, mul_inv] at e
  rw [one_div]
  exact (mul_left_cancel₀ (inv_ne_zero hr.ne') e).symm

/-- Cochrane (2023), p. 378: under the rule with `i_t ≥ 0`, `Φ(Π_t) > 0` (`1 + r > 0`). -/
theorem phi_pos_of_rule {r : ℝ} (hr : 0 < 1 + r) {Φ : ℝ → ℝ} {x i : ℝ} (hi : 0 ≤ i)
    (hrule : 1 + i = (1 + r) * Φ x) : 0 < Φ x := by
  by_contra h
  push Not at h
  nlinarith

/-! ## Atkeson–Chari–Kehoe under uncertainty -/

/-- Cochrane (2023), §16.10.2, p. 389, under uncertainty: the ACK regime state by state — the
Taylor rule until and including the first date at which `Π_t > Π_U` in that state, the
money-growth rule `Π_{t+1} = μ` (constant velocity) from then on, with (16.25) and the zero
bound. -/
def StochACK (r : ℝ) (Φ : ℝ → ℝ) (PiU μ : ℝ) (infl i : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, 0 < infl t ω) ∧ LowerBound.BondPricing 𝔼 r i infl ∧ (∀ t ω, 0 ≤ i t ω) ∧
    (∀ t ω, (∀ s < t, infl s ω ≤ PiU) → 1 + i t ω = (1 + r) * Φ (infl t ω)) ∧
    ∀ t ω, (∃ s ≤ t, PiU < infl s ω) → infl (t + 1) ω = μ

open Classical in
/-- Cochrane (2023), §16.10.2, p. 389: the indicator of the event "`t` is the first date with
`Π_t > Π_U`". -/
noncomputable def firstInd (infl : ℕ → Ω → ℝ) (PiU : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  if PiU < infl t ω ∧ ∀ s < t, infl s ω ≤ PiU then 1 else 0

/-- Cochrane (2023), §16.10.2, p. 389, "an equilibrium cannot form at period `T`", under
uncertainty: with the pull-out property and the first-exceedance event known at its date, in
every state where `T` is the first date with `Π_T > Π_U`, an equilibrium needs `Φ(Π_T) = μ`. -/
theorem stoch_ack_inconsistent (hPO : 𝔼.PullOut) {r : ℝ} (hr : 0 < 1 + r) {Φ : ℝ → ℝ}
    {PiU μ : ℝ} {infl i : ℕ → Ω → ℝ} (h : StochACK 𝔼 r Φ PiU μ infl i)
    (hk : ∀ t, 𝔼.E t (firstInd infl PiU t) = firstInd infl PiU t) {T : ℕ} {ω : Ω}
    (hT : PiU < infl T ω) (hbefore : ∀ s < T, infl s ω ≤ PiU) : Φ (infl T ω) = μ := by
  obtain ⟨hpos, hbp, hi, htay, hmon⟩ := h
  set a := firstInd infl PiU T with ha
  have hrule := htay T ω hbefore
  have hE := E_inv_of_rule 𝔼 hr hbp hrule
  have hΦ := phi_pos_of_rule hr (hi T ω) hrule
  have hμ : 0 < μ := by rw [← hmon T ω ⟨T, le_rfl, hT⟩]; exact hpos _ _
  have hprod : a * (fun ω => 1 / infl (T + 1) ω) = (1 / μ) • a := by
    funext ω'
    simp only [ha, firstInd, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs with hc
    · rw [hmon T ω' ⟨T, le_rfl, hc.1⟩]; ring
    · ring
  have h1 := congrFun (hPO T a (fun ω => 1 / infl (T + 1) ω) (hk T)) ω
  rw [hprod, map_smul, hk T] at h1
  simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, hE] at h1
  have hev : PiU < infl T ω ∧ ∀ s < T, infl s ω ≤ PiU := ⟨hT, hbefore⟩
  have haω : a ω = 1 := by
    rw [ha]
    unfold firstInd
    split_ifs
    rfl
  have h2 : 1 / μ = 1 / Φ (infl T ω) := by
    have haω' : firstInd infl PiU T ω = 1 := haω
    simpa [haω, haω'] using h1
  rw [one_div, one_div, inv_inj] at h2
  exact h2.symm

/-- Cochrane (2023), §16.10.2, p. 389, "the inflationary path leading to `T` is not an
equilibrium", under uncertainty: if `Φ(Π) ≠ μ` above `Π_U`, no equilibrium exceeds `Π_U` in any
state at any date. -/
theorem stoch_ack_bounded (hPO : 𝔼.PullOut) {r : ℝ} (hr : 0 < 1 + r) {Φ : ℝ → ℝ}
    {PiU μ : ℝ} {infl i : ℕ → Ω → ℝ} (hΦμ : ∀ x, PiU < x → Φ x ≠ μ)
    (h : StochACK 𝔼 r Φ PiU μ infl i)
    (hk : ∀ t, 𝔼.E t (firstInd infl PiU t) = firstInd infl PiU t) :
    ∀ t ω, infl t ω ≤ PiU := by
  intro t ω
  by_contra hcon
  push Not at hcon
  classical
  have hex : ∃ T, PiU < infl T ω := ⟨t, hcon⟩
  let T := Nat.find hex
  have hT : PiU < infl T ω := Nat.find_spec hex
  have hbefore : ∀ s < T, infl s ω ≤ PiU := fun s hs => not_lt.mp (Nat.find_min hex hs)
  exact hΦμ _ hT (stoch_ack_inconsistent 𝔼 hPO hr h hk hT hbefore)

/-- Cochrane (2023), §16.10.2, p. 389: on a finite event tree, if inflation is known at each
date (constant on the information cells), the first-exceedance indicator is known at its
date, so the hypothesis `hk` of `stoch_ack_bounded` holds. -/
theorem firstInd_known_tree {Ω' : Type*} [Fintype Ω'] (T : ExpectationsFiniteTree.FiniteTree Ω')
    {infl : ℕ → Ω' → ℝ} (had : ∀ s ω ω', T.info s ω' ω → infl s ω' = infl s ω) (PiU : ℝ)
    (t : ℕ) : T.toExpectationSystem.E t (firstInd infl PiU t) = firstInd infl PiU t := by
  funext ω
  rw [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  refine T.condE_of_const_on_cell fun ω' h => ?_
  have hs : ∀ s ≤ t, infl s ω' = infl s ω := fun s hs => had s ω ω' (T.refines hs ω' ω h)
  unfold firstInd
  rw [hs t le_rfl]
  have : (∀ s < t, infl s ω' ≤ PiU) ↔ ∀ s < t, infl s ω ≤ PiU :=
    forall_congr' fun s => imp_congr_right fun hst => by rw [hs s hst.le]
  simp only [this]

/-- Cochrane (2023), §16.10.2, p. 389: a rule that pushes inverse inflation away from the target
at rate `c` in the inflation region: `c(1/Π* − 1/Π) ≤ 1/Π* − 1/Φ(Π)` for `Π ∈ [Π*, Π_U]`. -/
def GapAbove (Φ : ℝ → ℝ) (Pis PiU c : ℝ) : Prop :=
  ∀ x, Pis ≤ x → x ≤ PiU → c * (1 / Pis - 1 / x) ≤ 1 / Pis - 1 / Φ x

/-- Cochrane (2023), §16.10.2, p. 389, "the ACK regime prunes the inflationary equilibria",
under uncertainty: with `Φ(Π) ≠ μ` above `Π_U ≥ Π*` and a rule satisfying `GapAbove` with
`c > 1`, no equilibrium — sunspot equilibria included — has `Π_t > Π*` in any state at any
date. -/
theorem stoch_ack_prunes_inflation (hPO : 𝔼.PullOut) {r : ℝ} (hr : 0 < 1 + r) {Φ : ℝ → ℝ}
    {Pis PiU μ c : ℝ} (hPis : 0 < Pis) (hc : 1 < c) (hgap : GapAbove Φ Pis PiU c)
    {infl i : ℕ → Ω → ℝ} (hΦμ : ∀ x, PiU < x → Φ x ≠ μ) (h : StochACK 𝔼 r Φ PiU μ infl i)
    (hk : ∀ t, 𝔼.E t (firstInd infl PiU t) = firstInd infl PiU t) :
    ∀ t ω, infl t ω ≤ Pis := by
  have hbd := stoch_ack_bounded 𝔼 hPO hr hΦμ h hk
  obtain ⟨hpos, hbp, hi, htay, -⟩ := h
  set D : ℕ → Ω → ℝ := fun t ω => max (1 / Pis - 1 / infl t ω) 0 with hD
  have hDB : ∀ t ω, D t ω ≤ 1 / Pis := fun t ω => by
    have := one_div_pos.mpr (hpos t ω)
    have := one_div_pos.mpr hPis
    exact max_le (by linarith) this.le
  have hg : ∀ t ω, c * D t ω ≤ 𝔼.E t (D (t + 1)) ω := by
    intro t ω
    have hnn : 0 ≤ 𝔼.E t (D (t + 1)) ω := by
      have := 𝔼.mono t (fun ω' => le_max_right _ _ : (fun _ => (0 : ℝ)) ≤ D (t + 1)) ω
      rwa [𝔼.const] at this
    by_cases hx : infl t ω ≤ Pis
    · have : D t ω = 0 := by
        simp only [hD]
        apply max_eq_right
        have := hpos t ω
        rw [sub_nonpos]
        exact one_div_le_one_div_of_le this hx
      rw [this, mul_zero]
      exact hnn
    · push Not at hx
      have hrule := htay t ω fun s _ => hbd s ω
      have hE := E_inv_of_rule 𝔼 hr hbp hrule
      have hgp := hgap _ hx.le (hbd t ω)
      have hDt : D t ω = 1 / Pis - 1 / infl t ω := by
        simp only [hD]
        apply max_eq_left
        rw [sub_nonneg]
        exact one_div_le_one_div_of_le hPis hx.le
      have hm : (fun ω' => 1 / Pis - 1 / infl (t + 1) ω') ≤ D (t + 1) := fun ω' =>
        le_max_left _ _
      have h2 := 𝔼.mono t hm ω
      have e : (fun ω' => 1 / Pis - 1 / infl (t + 1) ω') =
          (fun _ => 1 / Pis) - fun ω' => 1 / infl (t + 1) ω' := rfl
      rw [e, map_sub, 𝔼.const] at h2
      simp only [Pi.sub_apply, hE] at h2
      rw [hDt]
      linarith
  have hz := growth_zero 𝔼 hc (fun t ω => le_max_right _ _) hDB hg
  intro t ω
  have h0 : max (1 / Pis - 1 / infl t ω) 0 = 0 := hz t ω
  have hle : 1 / Pis - 1 / infl t ω ≤ 0 := by rw [← h0]; exact le_max_left _ _
  have := hpos t ω
  by_contra hcon
  push Not at hcon
  have : 1 / infl t ω < 1 / Pis := one_div_lt_one_div_of_lt hPis hcon
  linarith

/-- Cochrane (2023), §16.10.2, p. 389, and §16.10.4, p. 391: the linear rule
`Φ(Π) = Π* + φ(Π − Π*)` with `φ > 1` satisfies `GapAbove` on `[Π*, Π_U]` with
`c = φΠ_U/(Π* + φ(Π_U − Π*)) > 1`. -/
theorem linRule_gap_above {Pis PiU φ : ℝ} (hPis : 0 < Pis) (hφ : 1 < φ) (hU : Pis ≤ PiU) :
    1 < φ * PiU / (Pis + φ * (PiU - Pis)) ∧
      GapAbove (SelectionPatches.linRule Pis φ) Pis PiU (φ * PiU / (Pis + φ * (PiU - Pis))) := by
  have hden : 0 < Pis + φ * (PiU - Pis) := by nlinarith
  refine ⟨by rw [one_lt_div hden]; nlinarith, fun x hx1 hx2 => ?_⟩
  unfold SelectionPatches.linRule
  have hx0 : 0 < x := by linarith
  have hΦ : 0 < Pis + φ * (x - Pis) := by nlinarith
  rcases hx1.lt_or_eq with hlt | heq
  · rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    have e1 : 1 / Pis - 1 / x = (x - Pis) / (Pis * x) := by field_simp
    have e2 : 1 / Pis - 1 / (Pis + φ * (x - Pis)) =
        φ * (x - Pis) / (Pis * (Pis + φ * (x - Pis))) := by field_simp; ring
    rw [e1, e2]
    rw [show φ * PiU * ((x - Pis) / (Pis * x)) = (x - Pis) / Pis * (φ * PiU / x) by
      field_simp]
    rw [show φ * (x - Pis) / (Pis * (Pis + φ * (x - Pis))) * (Pis + φ * (PiU - Pis)) =
      (x - Pis) / Pis * (φ * (Pis + φ * (PiU - Pis)) / (Pis + φ * (x - Pis))) by
      field_simp]
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (by linarith) hPis.le)
    rw [div_le_div_iff₀ hx0 hΦ]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hx2) (by linarith : (0 : ℝ) ≤ φ - 1))
      (mul_pos (by linarith : (0 : ℝ) < φ) hPis).le]
  · subst heq
    simp

/-- Cochrane (2023), §16.10.2, p. 389, under uncertainty: a perfect-foresight ACK equilibrium is
an equilibrium of every expectation system (`Ω` nonempty). -/
theorem const_stochACK {r : ℝ} (hr : 0 < 1 + r) {Φ : ℝ → ℝ} {PiU μ : ℝ} {p j : ℕ → ℝ}
    (h : SelectionPatches.ACKEq r Φ PiU μ p j) :
    StochACK 𝔼 r Φ PiU μ (fun t _ => p t) (fun t _ => j t) := by
  obtain ⟨hpos, hi, hfis, htay, hmon⟩ := h
  refine ⟨fun t _ => hpos t, fun t => ?_, fun t _ => hi t, fun t _ hs => htay t hs,
    fun t _ hs => hmon t hs⟩
  funext ω
  change 1 / (1 + j t) = (1 + r)⁻¹ * 𝔼.E t (fun _ => 1 / p (t + 1)) ω
  rw [𝔼.const]
  have h1 : 0 < 1 + j t := by linarith [hi t]
  rw [hfis t]
  field_simp

/-- Cochrane (2023), §16.10.2, p. 389, "the ACK regime does not prune the deflationary paths",
for every expectation system: under the hypotheses of `SelectionPatches.ack_keeps_deflation`,
every `Π₀ ∈ (0, Π*]` starts an equilibrium of `StochACK`. -/
theorem stoch_ack_keeps_deflation {r : ℝ} {Φ : ℝ → ℝ} {Pis PiU μ Pi0 : ℝ} (hr : 0 < 1 + r)
    (hmono : MonotoneOn Φ (Set.Ioc 0 Pis)) (hfix : Φ Pis = Pis)
    (hbd : ∀ x ∈ Set.Ioc 0 Pis, (1 + r)⁻¹ ≤ Φ x) (hPiU : Pis ≤ PiU) (h0 : Pi0 ∈ Set.Ioc 0 Pis) :
    StochACK 𝔼 r Φ PiU μ (fun t _ => Φ^[t] Pi0) (fun t _ => (1 + r) * Φ (Φ^[t] Pi0) - 1) :=
  const_stochACK 𝔼 hr (SelectionPatches.ack_keeps_deflation hr hmono hfix hbd hPiU h0)

/-! ## Stopping an inflation does not rule it out -/

/-- Cochrane (2023), §16.10.2, p. 387, under uncertainty: the separated regime — the Taylor rule
while `Π_s ≤ Π_U` for all `s ≤ t` (in that state), the money rule `Π_{t+1} = μ` from the first
exceedance on — with (16.25) and the zero bound. -/
def StochStab (r : ℝ) (Φ : ℝ → ℝ) (PiU μ : ℝ) (infl i : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, 0 < infl t ω) ∧ LowerBound.BondPricing 𝔼 r i infl ∧ (∀ t ω, 0 ≤ i t ω) ∧
    (∀ t ω, (∀ s ≤ t, infl s ω ≤ PiU) → 1 + i t ω = (1 + r) * Φ (infl t ω)) ∧
    ∀ t ω, (∃ s ≤ t, PiU < infl s ω) → infl (t + 1) ω = μ

/-- Cochrane (2023), §16.10.2, p. 387: a perfect-foresight equilibrium of the separated regime
is an equilibrium of every expectation system. -/
theorem const_stochStab {r : ℝ} (hr : 0 < 1 + r) {Φ : ℝ → ℝ} {PiU μ : ℝ} {p j : ℕ → ℝ}
    (h : SelectionPatches.StabEq r Φ PiU μ p j) :
    StochStab 𝔼 r Φ PiU μ (fun t _ => p t) (fun t _ => j t) := by
  obtain ⟨hpos, hi, hfis, htay, hmon⟩ := h
  refine ⟨fun t _ => hpos t, fun t => ?_, fun t _ => hi t, fun t _ hs => htay t hs,
    fun t _ hs => hmon t hs⟩
  funext ω
  change 1 / (1 + j t) = (1 + r)⁻¹ * 𝔼.E t (fun _ => 1 / p (t + 1)) ω
  rw [𝔼.const]
  have h1 : 0 < 1 + j t := by linarith [hi t]
  rw [hfis t]
  field_simp

/-- Cochrane (2023), §16.10.2, p. 386, "if the government successfully stops the inflation …
then the inflation and its end remain an equilibrium path", for every expectation system: under
the hypotheses of `SelectionPatches.stop_not_rule_out`, every `Π₀ > 0` starts an equilibrium of
the separated regime, which follows the Taylor orbit until it exceeds `Π_U`. -/
theorem stoch_stop_not_rule_out {r : ℝ} {Φ : ℝ → ℝ} {PiU μ Pi0 : ℝ} (hr : 0 < 1 + r)
    (hΦ : ∀ x, 0 < x → (1 + r)⁻¹ ≤ Φ x) (hμ : (1 + r)⁻¹ ≤ μ) (hPi0 : 0 < Pi0) :
    ∃ p j : ℕ → ℝ, StochStab 𝔼 r Φ PiU μ (fun t _ => p t) (fun t _ => j t) ∧ p 0 = Pi0 := by
  obtain ⟨⟨p, j, h, h0⟩, -⟩ := SelectionPatches.stop_not_rule_out hr hΦ hμ hPi0
  exact ⟨p, j, const_stochStab 𝔼 hr h, h0⟩

/-! ## Bassetto under uncertainty -/

/-- Cochrane (2023), §16.10.4, p. 391: a rule that pushes inverse inflation away from the target
at rate `c` below the target wherever it respects the zero bound:
`c(1/Π − 1/Π*) ≤ 1/Φ(Π) − 1/Π*` for `0 < Π ≤ Π*` with `Φ(Π) ≥ β`. -/
def GapBelow (Φ : ℝ → ℝ) (β Pis c : ℝ) : Prop :=
  ∀ x, 0 < x → x ≤ Pis → β ≤ Φ x → c * (1 / x - 1 / Pis) ≤ 1 / Φ x - 1 / Pis

/-- Cochrane (2023), §16.10.4, pp. 391–392, "such a `Φ(Π)` function cleanly rules out
deflationary equilibria", under uncertainty: if the rule satisfies `GapBelow` with `c > 1`, and
respecting the zero bound forces `Π ≥ lo > 0`, then every equilibrium (sunspot equilibria
included) has `Π_t ≥ Π*` in every state at every date. -/
theorem stoch_bassetto {r : ℝ} (hr : 0 < 1 + r) {Φ : ℝ → ℝ} {Pis c lo : ℝ} (hPis : 0 < Pis)
    (hlo : 0 < lo) (hc : 1 < c) (hgap : GapBelow Φ (1 + r)⁻¹ Pis c)
    (hloB : ∀ x, 0 < x → (1 + r)⁻¹ ≤ Φ x → lo ≤ x) {infl i : ℕ → Ω → ℝ}
    (h : StochEq 𝔼 r Φ infl i) : ∀ t ω, Pis ≤ infl t ω := by
  have hpos := h.1
  have hzb : ∀ t ω, (1 + r)⁻¹ ≤ Φ (infl t ω) := fun t ω =>
    ((zero_bound_iff_stoch 𝔼 hr h t ω).1).mp (h.2.2.2.2 t ω)
  have hdyn := stochEq_dyn 𝔼 hr h
  set D : ℕ → Ω → ℝ := fun t ω => max (1 / infl t ω - 1 / Pis) 0 with hD
  have hDB : ∀ t ω, D t ω ≤ 1 / lo := fun t ω => by
    have h1 := hloB _ (hpos t ω) (hzb t ω)
    have h2 : 1 / infl t ω ≤ 1 / lo := one_div_le_one_div_of_le hlo h1
    have := one_div_pos.mpr hPis
    exact max_le (by linarith) (one_div_pos.mpr hlo).le
  have hg : ∀ t ω, c * D t ω ≤ 𝔼.E t (D (t + 1)) ω := by
    intro t ω
    have hnn : 0 ≤ 𝔼.E t (D (t + 1)) ω := by
      have := 𝔼.mono t (fun ω' => le_max_right _ _ : (fun _ => (0 : ℝ)) ≤ D (t + 1)) ω
      rwa [𝔼.const] at this
    by_cases hx : Pis ≤ infl t ω
    · have : D t ω = 0 := by
        simp only [hD]
        apply max_eq_right
        rw [sub_nonpos]
        exact one_div_le_one_div_of_le hPis hx
      rw [this, mul_zero]
      exact hnn
    · push Not at hx
      have hgp := hgap _ (hpos t ω) hx.le (hzb t ω)
      have hDt : D t ω = 1 / infl t ω - 1 / Pis := by
        simp only [hD]
        apply max_eq_left
        rw [sub_nonneg]
        exact one_div_le_one_div_of_le (hpos t ω) hx.le
      have hm : (fun ω' => 1 / infl (t + 1) ω' - 1 / Pis) ≤ D (t + 1) := fun ω' =>
        le_max_left _ _
      have h2 := 𝔼.mono t hm ω
      have e : (fun ω' => 1 / infl (t + 1) ω' - 1 / Pis) =
          (fun ω' => 1 / infl (t + 1) ω') - fun _ => 1 / Pis := rfl
      rw [e, map_sub, 𝔼.const, hdyn t] at h2
      simp only [Pi.sub_apply] at h2
      rw [hDt]
      linarith
  have hz := growth_zero 𝔼 hc (fun t ω => le_max_right _ _) hDB hg
  intro t ω
  have h0 : max (1 / infl t ω - 1 / Pis) 0 = 0 := hz t ω
  have hle : 1 / infl t ω - 1 / Pis ≤ 0 := by rw [← h0]; exact le_max_left _ _
  have := hpos t ω
  by_contra hcon
  push Not at hcon
  have : 1 / Pis < 1 / infl t ω := one_div_lt_one_div_of_lt this hcon
  linarith

/-- Cochrane (2023), §16.10.4, p. 391: the linear rule `Φ(Π) = Π* + φ(Π − Π*)`, `φ ≥ 1`,
satisfies `GapBelow` with `c = φ` (for `β > 0`). -/
theorem linRule_gap_below {β Pis φ : ℝ} (hβ : 0 < β) (hPis : 0 < Pis) (hφ : 1 ≤ φ) :
    GapBelow (SelectionPatches.linRule Pis φ) β Pis φ := by
  intro x hx0 hx hb
  unfold SelectionPatches.linRule at hb ⊢
  have hΦ : 0 < Pis + φ * (x - Pis) := lt_of_lt_of_le hβ hb
  have hΦx : Pis + φ * (x - Pis) ≤ x := by nlinarith
  have e1 : 1 / x - 1 / Pis = (Pis - x) / (x * Pis) := by field_simp
  have e2 : 1 / (Pis + φ * (x - Pis)) - 1 / Pis =
      φ * (Pis - x) / ((Pis + φ * (x - Pis)) * Pis) := by field_simp; ring
  rw [e1, e2, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have hd : 0 ≤ φ * (Pis - x) := mul_nonneg (by linarith) (by linarith)
  have : φ * (Pis - x) * ((Pis + φ * (x - Pis)) * Pis) ≤ φ * (Pis - x) * (x * Pis) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΦx hPis.le) hd
  linarith

/-- Cochrane (2023), §16.10.4, p. 391: under the linear rule (`φ ≥ 1`, `0 < β < Π*`), the zero
bound `Φ(Π) ≥ β` forces `Π ≥ Π* − (Π* − β)/φ > 0`. -/
theorem linRule_lo {β Pis φ : ℝ} (hβ : 0 < β) (hβPis : β < Pis) (hφ : 1 ≤ φ) :
    0 < Pis - (Pis - β) / φ ∧
      ∀ x, β ≤ SelectionPatches.linRule Pis φ x → Pis - (Pis - β) / φ ≤ x := by
  have hφ0 : 0 < φ := by linarith
  refine ⟨?_, fun x hx => ?_⟩
  · rw [sub_pos, div_lt_iff₀ hφ0]; nlinarith
  · unfold SelectionPatches.linRule at hx
    have : Pis - x ≤ (Pis - β) / φ := by rw [le_div_iff₀ hφ0]; nlinarith
    linarith

/-- Cochrane (2023), §16.10.4, pp. 391–392, under uncertainty: with the linear rule `φ > 1`
ignoring the zero bound (`0 < β < Π*`), no equilibrium — sunspot equilibria included — ever has
`Π_t < Π*` in any state. -/
theorem stoch_bassetto_linear {r Pis φ : ℝ} (hr : 0 < 1 + r) (hβPis : (1 + r)⁻¹ < Pis)
    (hφ : 1 < φ) {infl i : ℕ → Ω → ℝ}
    (h : StochEq 𝔼 r (SelectionPatches.linRule Pis φ) infl i) : ∀ t ω, Pis ≤ infl t ω := by
  have hβ : 0 < (1 + r)⁻¹ := inv_pos.mpr hr
  have hPis : 0 < Pis := lt_trans hβ hβPis
  obtain ⟨hlo, hloB⟩ := linRule_lo hβ hβPis hφ.le
  exact stoch_bassetto 𝔼 hr hPis hlo hφ (linRule_gap_below hβ hPis hφ.le)
    (fun x _ hx => hloB x hx) h

/-! ## V-shaped rules under uncertainty -/

/-- Cochrane (2023), §16.10.2 and §16.10.5: if `E_t(1/Π_{t+1}) = 1/Φ(Π_t)`, the process stays
below `Π_U` and the rule satisfies `GapAbove` with `c > 1`, then `Π_t ≤ Π*` in every state. -/
theorem le_of_gapAbove {Φ : ℝ → ℝ} {Pis PiU c : ℝ} (hPis : 0 < Pis) (hc : 1 < c)
    (hgap : GapAbove Φ Pis PiU c) {infl : ℕ → Ω → ℝ} (hpos : ∀ t ω, 0 < infl t ω)
    (hbd : ∀ t ω, infl t ω ≤ PiU)
    (hdyn : ∀ t, 𝔼.E t (fun ω => 1 / infl (t + 1) ω) = fun ω => 1 / Φ (infl t ω)) :
    ∀ t ω, infl t ω ≤ Pis := by
  set D : ℕ → Ω → ℝ := fun t ω => max (1 / Pis - 1 / infl t ω) 0 with hD
  have hDB : ∀ t ω, D t ω ≤ 1 / Pis := fun t ω => by
    have := one_div_pos.mpr (hpos t ω)
    have := one_div_pos.mpr hPis
    exact max_le (by linarith) this.le
  have hg : ∀ t ω, c * D t ω ≤ 𝔼.E t (D (t + 1)) ω := by
    intro t ω
    have hnn : 0 ≤ 𝔼.E t (D (t + 1)) ω := by
      have := 𝔼.mono t (fun ω' => le_max_right _ _ : (fun _ => (0 : ℝ)) ≤ D (t + 1)) ω
      rwa [𝔼.const] at this
    by_cases hx : infl t ω ≤ Pis
    · have : D t ω = 0 := by
        simp only [hD]
        apply max_eq_right
        rw [sub_nonpos]
        exact one_div_le_one_div_of_le (hpos t ω) hx
      rw [this, mul_zero]
      exact hnn
    · push Not at hx
      have hgp := hgap _ hx.le (hbd t ω)
      have hDt : D t ω = 1 / Pis - 1 / infl t ω := by
        simp only [hD]
        apply max_eq_left
        rw [sub_nonneg]
        exact one_div_le_one_div_of_le hPis hx.le
      have hm : (fun ω' => 1 / Pis - 1 / infl (t + 1) ω') ≤ D (t + 1) := fun ω' =>
        le_max_left _ _
      have h2 := 𝔼.mono t hm ω
      have e : (fun ω' => 1 / Pis - 1 / infl (t + 1) ω') =
          (fun _ => 1 / Pis) - fun ω' => 1 / infl (t + 1) ω' := rfl
      rw [e, map_sub, 𝔼.const, hdyn t] at h2
      simp only [Pi.sub_apply] at h2
      rw [hDt]
      linarith
  have hz := growth_zero 𝔼 hc (fun t ω => le_max_right _ _) hDB hg
  intro t ω
  have h0 : max (1 / Pis - 1 / infl t ω) 0 = 0 := hz t ω
  have hle : 1 / Pis - 1 / infl t ω ≤ 0 := by rw [← h0]; exact le_max_left _ _
  have := hpos t ω
  by_contra hcon
  push Not at hcon
  have : 1 / infl t ω < 1 / Pis := one_div_lt_one_div_of_lt hPis hcon
  linarith

/-- Cochrane (2023), §16.10.5, p. 392 (Alstadheim and Henderson), under uncertainty: if the rule
sends every `Π ≠ Π*` above `Π*` and satisfies `GapAbove` on `[Π*, Π_max]` with `c > 1`, the
only equilibrium bounded by `Π_max` — sunspot equilibria included — is `Π_t ≡ Π*`. -/
theorem stoch_v_rule {Φ : ℝ → ℝ} {Pis Pmax c : ℝ} (hPis : 0 < Pis) (hc : 1 < c)
    (hgap : GapAbove Φ Pis Pmax c) (hjump : ∀ x, 0 < x → x ≠ Pis → Pis < Φ x)
    {infl : ℕ → Ω → ℝ} (hpos : ∀ t ω, 0 < infl t ω) (hbd : ∀ t ω, infl t ω ≤ Pmax)
    (hdyn : ∀ t, 𝔼.E t (fun ω => 1 / infl (t + 1) ω) = fun ω => 1 / Φ (infl t ω)) :
    ∀ t ω, infl t ω = Pis := by
  have hle := le_of_gapAbove 𝔼 hPis hc hgap hpos hbd hdyn
  intro t ω
  by_contra hne
  have hΦ := hjump _ (hpos t ω) hne
  have hm : (fun _ => 1 / Pis) ≤ fun ω' => 1 / infl (t + 1) ω' := fun ω' =>
    one_div_le_one_div_of_le (hpos _ _) (hle _ _)
  have h2 := 𝔼.mono t hm ω
  rw [𝔼.const, hdyn t] at h2
  have : 1 / Φ (infl t ω) < 1 / Pis := one_div_lt_one_div_of_lt hPis hΦ
  linarith

/-- Cochrane (2023), §16.10.5, p. 392: the V-shaped rule `Φ(Π) = Π* + 2|Π − Π*|` satisfies
`GapAbove` on `[Π*, Π_max]` with `c = 2Π_max/(2Π_max − Π*) > 1`, and sends every `Π ≠ Π*` above
`Π*`. -/
theorem vRule_gap {Pis Pmax : ℝ} (hPis : 0 < Pis) (hmax : Pis ≤ Pmax) :
    1 < 2 * Pmax / (2 * Pmax - Pis) ∧
      GapAbove (SelectionPatches.vRule Pis) Pis Pmax (2 * Pmax / (2 * Pmax - Pis)) ∧
      ∀ x, x ≠ Pis → Pis < SelectionPatches.vRule Pis x := by
  have hden : 0 < 2 * Pmax - Pis := by linarith
  refine ⟨by rw [one_lt_div hden]; linarith, fun x hx1 hx2 => ?_, fun x hx => ?_⟩
  · unfold SelectionPatches.vRule
    rw [abs_of_nonneg (by linarith)]
    have hx0 : 0 < x := by linarith
    have hΦ : 0 < Pis + 2 * (x - Pis) := by linarith
    have h2x : 0 < 2 * x - Pis := by linarith
    have hq : 0 ≤ (x - Pis) / Pis := div_nonneg (by linarith) hPis.le
    have e1 : 1 / Pis - 1 / x = (1 / x) * ((x - Pis) / Pis) := by field_simp
    have e2 : 1 / Pis - 1 / (Pis + 2 * (x - Pis)) = (2 / (2 * x - Pis)) * ((x - Pis) / Pis) := by
      rw [show Pis + 2 * (x - Pis) = 2 * x - Pis by ring]
      field_simp
      ring
    have hc : 2 * Pmax / (2 * Pmax - Pis) * (1 / x) ≤ 2 / (2 * x - Pis) := by
      rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) h2x]
      nlinarith
    rw [e1, e2, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hc hq
  · unfold SelectionPatches.vRule
    have : 0 < |x - Pis| := abs_pos.mpr (sub_ne_zero.mpr hx)
    linarith

/-- Cochrane (2023), §16.10.5, p. 392, under uncertainty: with the V-shaped rule, `Π*` is the
only equilibrium bounded above, sunspot equilibria included, for every expectation system. -/
theorem stoch_vRule {Pis Pmax : ℝ} (hPis : 0 < Pis) (hmax : Pis ≤ Pmax) {infl : ℕ → Ω → ℝ}
    (hpos : ∀ t ω, 0 < infl t ω) (hbd : ∀ t ω, infl t ω ≤ Pmax)
    (hdyn : ∀ t, 𝔼.E t (fun ω => 1 / infl (t + 1) ω) =
      fun ω => 1 / SelectionPatches.vRule Pis (infl t ω)) : ∀ t ω, infl t ω = Pis := by
  obtain ⟨hc, hgap, hjump⟩ := vRule_gap hPis hmax
  exact stoch_v_rule 𝔼 hPis hc hgap (fun x _ hx => hjump x hx) hpos hbd hdyn

/-! ## Fiscal trimming under uncertainty -/

/-- Cochrane (2023), §16.10.3, p. 390 (Benhabib, Schmitt-Grohé and Uribe), under uncertainty:
let real debt follow the flow `b_{t+1} = (1 + i_t)(1 − θ(Π_t))b_t/Π_{t+1}` (surpluses
`s_t = θ(Π_t)b_t`), with (16.25), `1 + i_t > 0`, `b ≥ 0`, the factor `(1 + i_t)(1 − θ(Π_t))b_t`
known at `t` and the pull-out property. If from date `T` on `θ(Π_t) ≤ θ̄ < 0` in every state,
then `E_tb_{t+1} = (1 + r)(1 − θ(Π_t))b_t` and the discounted expected debt `βᵗE_0b_t`
diverges whenever `E_0b_T > 0`: the transversality condition fails. -/
theorem stoch_bsgu_tvc_violated (hPO : 𝔼.PullOut) {r : ℝ} (hr : 0 < 1 + r) {θ : ℝ → ℝ}
    {θbar : ℝ} (hθbar : θbar < 0) {T : ℕ} {infl i b : ℕ → Ω → ℝ}
    (hbp : LowerBound.BondPricing 𝔼 r i infl) (hi : ∀ t ω, 0 < 1 + i t ω)
    (hflow : ∀ t ω, b (t + 1) ω = (1 + i t ω) * (1 - θ (infl t ω)) * b t ω / infl (t + 1) ω)
    (hk : ∀ t, 𝔼.E t (fun ω => (1 + i t ω) * (1 - θ (infl t ω)) * b t ω) =
      fun ω => (1 + i t ω) * (1 - θ (infl t ω)) * b t ω)
    (hb : ∀ t ω, 0 ≤ b t ω) (hθ : ∀ t, T ≤ t → ∀ ω, θ (infl t ω) ≤ θbar) (ω : Ω)
    (hT : 0 < 𝔼.E 0 (b T) ω) :
    Tendsto (fun t => ((1 + r)⁻¹) ^ t * 𝔼.E 0 (b t) ω) atTop atTop := by
  have hEb : ∀ t, 𝔼.E t (b (t + 1)) = (1 + r) • fun ω => (1 - θ (infl t ω)) * b t ω := by
    intro t
    have e : b (t + 1) = (fun ω => (1 + i t ω) * (1 - θ (infl t ω)) * b t ω) *
        fun ω => 1 / infl (t + 1) ω := by
      funext ω; rw [hflow]; simp only [Pi.mul_apply]; ring
    rw [e, hPO t _ _ (hk t)]
    funext ω
    have hbpω := congrFun (hbp t) ω
    simp only [Pi.smul_apply, smul_eq_mul] at hbpω
    have hE : 𝔼.E t (fun ω => 1 / infl (t + 1) ω) ω = (1 + r) / (1 + i t ω) := by
      have h1 := hi t ω
      field_simp at hbpω ⊢
      linarith
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hE]
    have h1 := (hi t ω).ne'
    field_simp
  have hstep : ∀ t, T ≤ t → (1 - θbar) * (((1 + r)⁻¹) ^ t * 𝔼.E 0 (b t) ω) ≤
      ((1 + r)⁻¹) ^ (t + 1) * 𝔼.E 0 (b (t + 1)) ω := by
    intro t ht
    have h1 : 𝔼.E 0 (b (t + 1)) ω = (1 + r) * 𝔼.E 0 (fun ω => (1 - θ (infl t ω)) * b t ω) ω := by
      rw [← 𝔼.tower (Nat.zero_le t), hEb t, map_smul]
      rfl
    have h2 : (1 - θbar) • b t ≤ fun ω => (1 - θ (infl t ω)) * b t ω := fun ω' => by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by linarith [hθ t ht ω']) (hb t ω')
    have h3 := 𝔼.mono 0 h2 ω
    rw [map_smul] at h3
    simp only [Pi.smul_apply, smul_eq_mul] at h3
    rw [h1, pow_succ]
    have hβ : 0 < ((1 + r)⁻¹) ^ t := pow_pos (inv_pos.mpr hr) t
    calc (1 - θbar) * (((1 + r)⁻¹) ^ t * 𝔼.E 0 (b t) ω)
        = ((1 + r)⁻¹) ^ t * ((1 - θbar) * 𝔼.E 0 (b t) ω) := by ring
      _ ≤ ((1 + r)⁻¹) ^ t * 𝔼.E 0 (fun ω => (1 - θ (infl t ω)) * b t ω) ω :=
          mul_le_mul_of_nonneg_left h3 hβ.le
      _ = ((1 + r)⁻¹) ^ t * (1 + r)⁻¹ * ((1 + r) * 𝔼.E 0 (fun ω => (1 - θ (infl t ω)) *
          b t ω) ω) := by field_simp
  have hgrow : ∀ n, (1 - θbar) ^ n * (((1 + r)⁻¹) ^ T * 𝔼.E 0 (b T) ω) ≤
      ((1 + r)⁻¹) ^ (T + n) * 𝔼.E 0 (b (T + n)) ω := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc (1 - θbar) ^ (n + 1) * (((1 + r)⁻¹) ^ T * 𝔼.E 0 (b T) ω)
          = (1 - θbar) * ((1 - θbar) ^ n * (((1 + r)⁻¹) ^ T * 𝔼.E 0 (b T) ω)) := by ring
        _ ≤ (1 - θbar) * (((1 + r)⁻¹) ^ (T + n) * 𝔼.E 0 (b (T + n)) ω) :=
            mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ _ := hstep (T + n) (Nat.le_add_right T n)
  have hpos0 : 0 < ((1 + r)⁻¹) ^ T * 𝔼.E 0 (b T) ω := mul_pos (pow_pos (inv_pos.mpr hr) T) hT
  have hlim : Tendsto (fun n => (1 - θbar) ^ n * (((1 + r)⁻¹) ^ T * 𝔼.E 0 (b T) ω)) atTop
      atTop := Tendsto.atTop_mul_const hpos0 (tendsto_pow_atTop_atTop_of_one_lt (by linarith))
  have hlim' : Tendsto (fun n => ((1 + r)⁻¹) ^ (T + n) * 𝔼.E 0 (b (T + n)) ω) atTop atTop :=
    tendsto_atTop_mono hgrow hlim
  rw [← tendsto_add_atTop_iff_nat T]
  exact hlim'.congr fun n => by rw [Nat.add_comm T n]

/-- Cochrane (2023), §16.10.3, p. 390, Woodford's `μ̄` rule under uncertainty: with nominal
liabilities `D_{t+1} = μ̄D_t`, prices `P_{t+1} = Π_{t+1}P_t`, real liabilities `v_t = D_t/P_t ≥ 0`
known at `t`, the pull-out property and `E_t(1/Π_{t+1}) = 1/Φ(Π_t)`: if from date `T` on
`0 < Φ(Π_t) ≤ βμ̄` in every state, the discounted expected real liabilities `βᵗE_0v_t` are
nondecreasing from `T`, so they do not tend to zero when `E_0v_T > 0`: the transversality
condition fails. -/
theorem stoch_mubar_tvc_violated (hPO : 𝔼.PullOut) {r μ : ℝ} (hr : 0 < 1 + r)
    {Φ : ℝ → ℝ} {T : ℕ} {infl P D : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω)
    (hPs : ∀ t ω, P (t + 1) ω = infl (t + 1) ω * P t ω) (hD : ∀ t ω, D (t + 1) ω = μ * D t ω)
    (hv : ∀ t ω, 0 ≤ D t ω)
    (hk : ∀ t, 𝔼.E t (fun ω => D t ω / P t ω) = fun ω => D t ω / P t ω)
    (hdyn : ∀ t, 𝔼.E t (fun ω => 1 / infl (t + 1) ω) = fun ω => 1 / Φ (infl t ω))
    (hle : ∀ t, T ≤ t → ∀ ω, 0 < Φ (infl t ω) ∧ Φ (infl t ω) ≤ (1 + r)⁻¹ * μ) (ω : Ω)
    (hT : 0 < 𝔼.E 0 (fun ω => D T ω / P T ω) ω) :
    ¬ Tendsto (fun t => ((1 + r)⁻¹) ^ t * 𝔼.E 0 (fun ω => D t ω / P t ω) ω) atTop (𝓝 0) := by
  have hinfl : ∀ t ω, 0 < infl (t + 1) ω := fun t ω => by
    have h1 := hPs t ω
    have h2 := hP (t + 1) ω
    have h3 := hP t ω
    by_contra hc
    push Not at hc
    nlinarith
  have hstep : ∀ t, T ≤ t → ((1 + r)⁻¹) ^ t * 𝔼.E 0 (fun ω => D t ω / P t ω) ω ≤
      ((1 + r)⁻¹) ^ (t + 1) * 𝔼.E 0 (fun ω => D (t + 1) ω / P (t + 1) ω) ω := by
    intro t ht
    have e : (fun ω => D (t + 1) ω / P (t + 1) ω) =
        (fun ω => D t ω / P t ω) * fun ω => μ * (1 / infl (t + 1) ω) := by
      funext ω'
      rw [hD, hPs]
      simp only [Pi.mul_apply]
      have := (hP t ω').ne'
      have := (hinfl t ω').ne'
      field_simp
    have hE : 𝔼.E t (fun ω => D (t + 1) ω / P (t + 1) ω) =
        fun ω => D t ω / P t ω * (μ * (1 / Φ (infl t ω))) := by
      rw [e, hPO t _ _ (hk t)]
      have e2 : (fun ω => μ * (1 / infl (t + 1) ω)) = μ • fun ω => 1 / infl (t + 1) ω := rfl
      rw [e2, map_smul, hdyn t]
      rfl
    have h2 : (fun ω => (1 + r) * (D t ω / P t ω)) ≤
        fun ω => D t ω / P t ω * (μ * (1 / Φ (infl t ω))) := fun ω' => by
      obtain ⟨h1, h2⟩ := hle t ht ω'
      have hvv : 0 ≤ D t ω' / P t ω' := div_nonneg (hv t ω') (hP t ω').le
      have : 1 + r ≤ μ * (1 / Φ (infl t ω')) := by
        rw [mul_one_div, le_div_iff₀ h1]
        have := mul_le_mul_of_nonneg_left h2 hr.le
        rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at this
        exact this
      nlinarith
    have h3 := 𝔼.mono 0 h2 ω
    rw [← hE, 𝔼.tower (Nat.zero_le t)] at h3
    have e3 : (fun ω => (1 + r) * (D t ω / P t ω)) = (1 + r) • fun ω => D t ω / P t ω := rfl
    rw [e3, map_smul] at h3
    simp only [Pi.smul_apply, smul_eq_mul] at h3
    rw [pow_succ]
    have hβ : 0 < ((1 + r)⁻¹) ^ t := pow_pos (inv_pos.mpr hr) t
    calc ((1 + r)⁻¹) ^ t * 𝔼.E 0 (fun ω => D t ω / P t ω) ω
        = ((1 + r)⁻¹) ^ t * (1 + r)⁻¹ * ((1 + r) * 𝔼.E 0 (fun ω => D t ω / P t ω) ω) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
  intro hlim
  have hmono : ∀ n, ((1 + r)⁻¹) ^ T * 𝔼.E 0 (fun ω => D T ω / P T ω) ω ≤
      ((1 + r)⁻¹) ^ (T + n) * 𝔼.E 0 (fun ω => D (T + n) ω / P (T + n) ω) ω := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => exact ih.trans (hstep (T + n) (Nat.le_add_right T n))
  have hpos0 : 0 < ((1 + r)⁻¹) ^ T * 𝔼.E 0 (fun ω => D T ω / P T ω) ω :=
    mul_pos (pow_pos (inv_pos.mpr hr) T) hT
  have h2 := (tendsto_add_atTop_iff_nat T).mpr hlim
  have := ge_of_tendsto h2 (Eventually.of_forall fun n => by
    simpa only [Nat.add_comm n T] using hmono n)
  linarith

/-! ## Sims (1994) under uncertainty -/

/-- Cochrane (2023), §16.10.6, p. 394 (Sims 1994), under uncertainty: with nominal money
`M_t ≥ M̲ > 0`, prices `P_{t+1} = Π_{t+1}P_t > 0` with `1/P_t` known at `t`, the pull-out
property, and the zero bound reached from date `T` on in every state (`i_t = 0`, so
`E_t(1/Π_{t+1}) = 1 + r`), the discounted expected real money `βᵗE_0[M_t/P_t]` does not tend to
zero when `E_0(1/P_T) > 0`: the transversality condition fails. -/
theorem stoch_sims_tvc_violated (hPO : 𝔼.PullOut) {r Mlow : ℝ} (hr : 0 < 1 + r)
    (hM0 : 0 < Mlow) {T : ℕ} {infl P M : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω)
    (hPs : ∀ t ω, P (t + 1) ω = infl (t + 1) ω * P t ω) (hM : ∀ t ω, Mlow ≤ M t ω)
    (hk : ∀ t, 𝔼.E t (fun ω => 1 / P t ω) = fun ω => 1 / P t ω)
    (hzb : ∀ t, T ≤ t → 𝔼.E t (fun ω => 1 / infl (t + 1) ω) = fun _ => 1 + r) (ω : Ω)
    (hT : 0 < 𝔼.E 0 (fun ω => 1 / P T ω) ω) :
    ¬ Tendsto (fun t => ((1 + r)⁻¹) ^ t * 𝔼.E 0 (fun ω => M t ω / P t ω) ω) atTop (𝓝 0) := by
  have hstep : ∀ t, T ≤ t → ((1 + r)⁻¹) ^ (t + 1) * 𝔼.E 0 (fun ω => 1 / P (t + 1) ω) ω =
      ((1 + r)⁻¹) ^ t * 𝔼.E 0 (fun ω => 1 / P t ω) ω := by
    intro t ht
    have e : (fun ω => 1 / P (t + 1) ω) = (fun ω => 1 / P t ω) * fun ω => 1 / infl (t + 1) ω := by
      funext ω'
      rw [hPs]
      simp only [Pi.mul_apply]
      rw [one_div_mul_one_div, mul_comm]
    have h1 : 𝔼.E 0 (fun ω => 1 / P (t + 1) ω) ω = (1 + r) * 𝔼.E 0 (fun ω => 1 / P t ω) ω := by
      rw [← 𝔼.tower (Nat.zero_le t), e, hPO t _ _ (hk t), hzb t ht]
      have e2 : ((fun ω => 1 / P t ω) * fun _ => 1 + r) = (1 + r) • fun ω => 1 / P t ω := by
        funext ω'; simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [e2, map_smul]
      rfl
    rw [h1, pow_succ]
    field_simp
  have hconst : ∀ n, ((1 + r)⁻¹) ^ (T + n) * 𝔼.E 0 (fun ω => 1 / P (T + n) ω) ω =
      ((1 + r)⁻¹) ^ T * 𝔼.E 0 (fun ω => 1 / P T ω) ω := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [← add_assoc, hstep (T + n) (Nat.le_add_right T n), ih]
  have hlow : ∀ t, Mlow * (((1 + r)⁻¹) ^ t * 𝔼.E 0 (fun ω => 1 / P t ω) ω) ≤
      ((1 + r)⁻¹) ^ t * 𝔼.E 0 (fun ω => M t ω / P t ω) ω := by
    intro t
    have h2 : Mlow • (fun ω => 1 / P t ω) ≤ fun ω => M t ω / P t ω := fun ω' => by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right (hM t ω') (hP t ω').le
    have h3 := 𝔼.mono 0 h2 ω
    rw [map_smul] at h3
    simp only [Pi.smul_apply, smul_eq_mul] at h3
    have hβ : 0 ≤ ((1 + r)⁻¹) ^ t := (pow_pos (inv_pos.mpr hr) t).le
    calc Mlow * (((1 + r)⁻¹) ^ t * 𝔼.E 0 (fun ω => 1 / P t ω) ω)
        = ((1 + r)⁻¹) ^ t * (Mlow * 𝔼.E 0 (fun ω => 1 / P t ω) ω) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 hβ
  intro hlim
  have hpos0 : 0 < Mlow * (((1 + r)⁻¹) ^ T * 𝔼.E 0 (fun ω => 1 / P T ω) ω) :=
    mul_pos hM0 (mul_pos (pow_pos (inv_pos.mpr hr) T) hT)
  have h2 := (tendsto_add_atTop_iff_nat T).mpr hlim
  have := ge_of_tendsto h2 (Eventually.of_forall fun n => by
    have := hlow (T + n)
    rw [hconst n] at this
    simpa only [Nat.add_comm n T] using this)
  linarith

/-! ## (16.31)–(16.32) under uncertainty -/

/-- Cochrane (2023), eq. (16.32), p. 393, under uncertainty:
`E_t[k(Π_{t+1})/Π_{t+1}] = k(Π_t)/Φ(Π_t)` with `k(Π) = u_c(y, L(Φ(Π)/β − 1))`. -/
def StochEq1632 (Φ k : ℝ → ℝ) (infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, 𝔼.E t (fun ω => k (infl (t + 1) ω) / infl (t + 1) ω) = fun ω => k (infl t ω) / Φ (infl t ω)

/-- Cochrane (2023), eqs. (16.31)–(16.32), p. 393, under uncertainty: the stochastic (16.31)
`1/(1 + i_t) = βE_t[(k(Π_{t+1})/k(Π_t))/Π_{t+1}]` (with `u_c = k(Π)`, the form derived from
optimisation in `TidyR6Household16_31.bond_1631`) and the rule `1 + i_t = Φ(Π_t)/β`, with the
pull-out property and `1/k(Π_t)` known at `t`, give the stochastic (16.32). -/
theorem stochEq1632_of_bond (hPO : 𝔼.PullOut) {β : ℝ} (hβ : 0 < β) {Φ k : ℝ → ℝ}
    {infl i : ℕ → Ω → ℝ} (hk0 : ∀ t ω, 0 < k (infl t ω)) (hΦ0 : ∀ t ω, 0 < Φ (infl t ω))
    (hbond : ∀ t, (fun ω => 1 / (1 + i t ω)) =
      β • 𝔼.E t (fun ω => k (infl (t + 1) ω) / k (infl t ω) / infl (t + 1) ω))
    (hrule : ∀ t ω, 1 + i t ω = Φ (infl t ω) / β)
    (hkn : ∀ t, 𝔼.E t (fun ω => 1 / k (infl t ω)) = fun ω => 1 / k (infl t ω)) :
    StochEq1632 𝔼 Φ k infl := by
  intro t
  have e : (fun ω => k (infl (t + 1) ω) / k (infl t ω) / infl (t + 1) ω) =
      (fun ω => 1 / k (infl t ω)) * fun ω => k (infl (t + 1) ω) / infl (t + 1) ω := by
    funext ω; simp only [Pi.mul_apply]; ring
  have h := hbond t
  rw [e, hPO t _ _ (hkn t)] at h
  funext ω
  have hω := congrFun h ω
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, hrule] at hω
  have hk := (hk0 t ω).ne'
  have hΦ := (hΦ0 t ω).ne'
  field_simp at hω
  field_simp
  linarith

/-- Cochrane (2023), (16.32), p. 393: in the bounded-rule model of
`SelectionPatches.bounded_rule_explosion` (`β = 1/2`, `Φ = boundedRule`, `L(i) = 5 − i`,
`u_c = 1/m`), `k(Π) = u_c(L(i(Π)))` satisfies `k(Π)/Π ≥ 1/4` at every `Π > 0` with positive
money demand. -/
theorem boundedRule_h_ge {x : ℝ} (hx : 0 < x)
    (hm : 0 < SelectionPatches.moneyDemand (SelectionPatches.boundedRate x)) :
    1 / 4 ≤ SelectionPatches.ucMoney (SelectionPatches.moneyDemand
      (SelectionPatches.boundedRate x)) / x := by
  simp only [SelectionPatches.ucMoney, SelectionPatches.moneyDemand,
    SelectionPatches.boundedRate, SelectionPatches.boundedRule] at hm ⊢
  rw [div_div, div_le_div_iff₀ (by norm_num) (mul_pos hm hx), one_mul]
  rcases le_total (2 * x - 1) 3 with h3 | h3
  · rw [min_eq_left h3] at hm ⊢
    rcases le_total (1 / 2 : ℝ) (2 * x - 1) with h2 | h2
    · rw [max_eq_right h2]
      nlinarith [sq_nonneg (x - 1)]
    · rw [max_eq_left h2]
      nlinarith
  · rw [min_eq_right h3, max_eq_right (by norm_num)] at hm
    norm_num at hm

/-- Cochrane (2023), (16.32), p. 393, "may rise to require `Π_{t+1} = ∞` … even if the policy
rule for nominal interest rates … remains bounded", under uncertainty: in the bounded-rule model,
for every expectation system, if `Π_t ∈ (1, 3/2)` in a state there is no random `Π_{t+1}`
(positive, with positive money demand in every state) satisfying the stochastic (16.32) there:
sunspots cannot rescue the economy from the finite-time explosion. -/
theorem stoch_bounded_rule_explosion {infl : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (hx : infl t ω ∈ Set.Ioo (1 : ℝ) (3 / 2))
    (hpos : ∀ ω', 0 < infl (t + 1) ω' ∧
      0 < SelectionPatches.moneyDemand (SelectionPatches.boundedRate (infl (t + 1) ω'))) :
    𝔼.E t (fun ω' => SelectionPatches.ucMoney (SelectionPatches.moneyDemand
        (SelectionPatches.boundedRate (infl (t + 1) ω'))) / infl (t + 1) ω') ω ≠
      SelectionPatches.ucMoney (SelectionPatches.moneyDemand
        (SelectionPatches.boundedRate (infl t ω))) / SelectionPatches.boundedRule (infl t ω) := by
  have hge : (fun _ => (1 / 4 : ℝ)) ≤ fun ω' => SelectionPatches.ucMoney
      (SelectionPatches.moneyDemand (SelectionPatches.boundedRate (infl (t + 1) ω'))) /
        infl (t + 1) ω' := fun ω' => boundedRule_h_ge (hpos ω').1 (hpos ω').2
  have h1 := 𝔼.mono t hge ω
  rw [𝔼.const] at h1
  obtain ⟨hx1, hx2⟩ := hx
  set x := infl t ω
  have hrule : SelectionPatches.boundedRule x = 2 * x - 1 := by
    unfold SelectionPatches.boundedRule
    rw [min_eq_left (by linarith), max_eq_right (by linarith)]
  have hrhs : SelectionPatches.ucMoney (SelectionPatches.moneyDemand
      (SelectionPatches.boundedRate x)) / SelectionPatches.boundedRule x < 1 / 4 := by
    simp only [SelectionPatches.ucMoney, SelectionPatches.moneyDemand,
      SelectionPatches.boundedRate]
    rw [hrule, div_div, div_lt_div_iff₀ (by nlinarith) (by norm_num), one_mul]
    nlinarith
  intro he
  rw [he] at h1
  linarith

end Cochrane.NewKeynesianSelection.TidyR6StochasticPatches
