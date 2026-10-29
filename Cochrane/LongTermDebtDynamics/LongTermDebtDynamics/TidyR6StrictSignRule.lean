/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR5FutureSalesRandom

/-!
# The strict sign rule for expected future sales with random debt

Cochrane (2023), Online Appendix §A1.14.2, p. 592 (last bullet), equations (1.65)–(1.66).

`TidyR5FutureSalesRandom.x0R_strictMono` proves the strict sign rule only under uniform positive
lower bounds, on the grounds that an abstract `ExpectationSystem` need not be strictly positive.
That rationale is wrong: monotonicity on *all* functions `Ω → ℝ`, unbounded ones included,
already forces strict positivity.

* `E_pos_iff`: **for every expectation system and every `f ≥ 0`,
  `E_t f > 0` at `ω` if and only if `E_t 1_{f>0} > 0` at `ω`**: `E_t` is strictly positive
  exactly on events of positive conditional probability. The proof uses the unbounded "level
  index" `levelIdx f` (the least `n` with `f > 1/(n+1)`) in one direction and
  `f ≤ M 1_{f>0} + f²/M` in the other. `E_pos_of_pos`: `f > 0` everywhere gives `E_t f > 0`
  everywhere, with no uniform bound.
* `x0R_strict_iff`: **the exact strict sign rule.** Under the book's sign conditions alone
  (`A₁ > A₂`, `B_0^{(2)} > 0`, `s_2 > 0`, larger sales `G ≥ 0`, `B_{−1}^{(0)} > 0`), larger
  future sales strictly lower `P_0` in state `ω` if and only if `E_0 1_{G>0} > 0` there.
  Otherwise there is no effect at all (`x0R_eq_of_null`).
* `x0R_strictMono_pos`: if the sale is larger in every state (`G > 0`), the rule is strict in
  every state for every expectation system, **with no uniform bounds**.
* `nullSys`, `null_counterexample`, `null_counterexample_eqm`: **the exact counterexample.**
  Under an expectation system whose date-0 forecast puts all weight on one state, a larger sale
  only in the other state satisfies every sign condition, yet leaves `P_0` unchanged in every
  equilibrium. So the condition `E_0 1_{G>0} > 0` cannot be dropped. What is needed is *not* a
  uniform bound but positive conditional probability of a larger sale, exactly as on a
  probability space (module TidyR6StrictSignMeasure).
-/

namespace Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule

open MaturityStructure TidyR5FutureSalesRandom

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), Online Appendix p. 592: the indicator `1_{f>0}` of the event on which `f` is
positive (for `f = G`, the event on which future sales are larger). -/
noncomputable def posEvent (f : Ω → ℝ) : Ω → ℝ := fun ω => if 0 < f ω then 1 else 0

/-- Cochrane (2023), Online Appendix p. 592 (proof device): the indicator of `f > 1/(N+1)`. -/
noncomputable def levelInd (f : Ω → ℝ) (N : ℕ) : Ω → ℝ :=
  fun ω => if 1 / ((N : ℝ) + 1) < f ω then 1 else 0

/-- Cochrane (2023), Online Appendix p. 592 (proof device): the level index of `f`, the least
`n` with `1/(n+1) < f ω` where `f ω > 0`, and `0` elsewhere. It is unbounded in general. -/
noncomputable def levelIdx (f : Ω → ℝ) : Ω → ℝ := fun ω =>
  if h : 0 < f ω then ((Nat.find (exists_nat_one_div_lt h) : ℕ) : ℝ) else 0

/-- Cochrane (2023), Online Appendix p. 592 (proof device): `1_{f > 1/(N+1)} ≤ (N+1) f` for
`f ≥ 0`. -/
theorem levelInd_le {f : Ω → ℝ} (hf : 0 ≤ f) (N : ℕ) :
    levelInd f N ≤ ((N : ℝ) + 1) • f := fun ω => by
  simp only [levelInd, Pi.smul_apply, smul_eq_mul]
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  split_ifs with h
  · rw [div_lt_iff₀ hN] at h; linarith
  · exact mul_nonneg hN.le (hf ω)

/-- Cochrane (2023), Online Appendix p. 592 (proof device): the level index dominates
`N (1_{f>0} − 1_{f > 1/(N+1)})`. -/
theorem levelIdx_ge (f : Ω → ℝ) (N : ℕ) :
    (N : ℝ) • (posEvent f - levelInd f N) ≤ levelIdx f := fun ω => by
  simp only [posEvent, levelInd, levelIdx, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  by_cases h : 0 < f ω
  · simp only [h, ↓reduceIte, ↓reduceDIte]
    split_ifs with h2
    · simp
    · have hge : N < Nat.find (exists_nat_one_div_lt h) := by
        by_contra hlt
        push Not at hlt
        have hs := Nat.find_spec (exists_nat_one_div_lt h)
        have hmono : 1 / ((N : ℝ) + 1) ≤ 1 / ((Nat.find (exists_nat_one_div_lt h) : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast Nat.add_le_add_right hlt 1
        exact h2 (lt_of_le_of_lt hmono hs)
      have : (N : ℝ) ≤ (Nat.find (exists_nat_one_div_lt h) : ℝ) := by exact_mod_cast hge.le
      linarith
  · have h2 : ¬ 1 / ((N : ℝ) + 1) < f ω := by
      intro h2; exact h ((by positivity : (0 : ℝ) < 1 / ((N : ℝ) + 1)).trans h2)
    simp only [h, h2, ↓reduceIte, ↓reduceDIte, sub_self, mul_zero, le_refl]

/-- Cochrane (2023), Online Appendix p. 592: for `f ≥ 0`, if the event `{f > 0}` has positive
conditional probability at `ω`, then `E_t f > 0` at `ω`. -/
theorem E_pos_of_E_posEvent_pos {f : Ω → ℝ} (hf : 0 ≤ f) {t : ℕ} {ω : Ω}
    (h : 0 < 𝔼.E t (posEvent f) ω) : 0 < 𝔼.E t f ω := by
  by_contra hle
  push Not at hle
  have hlev : ∀ N : ℕ, 𝔼.E t (levelInd f N) ω ≤ 0 := fun N => by
    have h1 := 𝔼.mono t (levelInd_le hf N) ω
    rw [map_smul, Pi.smul_apply, smul_eq_mul] at h1
    nlinarith [(by positivity : (0 : ℝ) < (N : ℝ) + 1)]
  have hbig : ∀ N : ℕ, (N : ℝ) * 𝔼.E t (posEvent f) ω ≤ 𝔼.E t (levelIdx f) ω := fun N => by
    have h1 := 𝔼.mono t (levelIdx_ge f N) ω
    rw [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h1
    nlinarith [hlev N, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  obtain ⟨N, hN⟩ := exists_nat_gt (𝔼.E t (levelIdx f) ω / 𝔼.E t (posEvent f) ω)
  rw [div_lt_iff₀ h] at hN
  linarith [hbig N]

/-- Cochrane (2023), Online Appendix p. 592: for `f ≥ 0`, `E_t f > 0` at `ω` forces the event
`{f > 0}` to have positive conditional probability at `ω`. -/
theorem E_posEvent_pos_of_E_pos {f : Ω → ℝ} (hf : 0 ≤ f) {t : ℕ} {ω : Ω}
    (h : 0 < 𝔼.E t f ω) : 0 < 𝔼.E t (posEvent f) ω := by
  have hp0 : 0 ≤ 𝔼.E t (posEvent f) ω := by
    have := 𝔼.mono t (show (fun _ => (0 : ℝ)) ≤ posEvent f from fun ω' => by
      simp only [posEvent]; split_ifs <;> norm_num) ω
    rwa [𝔼.const] at this
  by_contra hle
  push Not at hle
  have hp : 𝔼.E t (posEvent f) ω = 0 := le_antisymm hle hp0
  set Q := 𝔼.E t (f * f) ω with hQ
  have hQ0 : 0 ≤ Q := by
    have := 𝔼.mono t (show (fun _ => (0 : ℝ)) ≤ f * f from fun ω' => mul_self_nonneg (f ω')) ω
    rwa [𝔼.const] at this
  set a := 𝔼.E t f ω with ha
  have hM : ∀ M : ℝ, 0 < M → a * M ≤ Q := fun M hM => by
    have hle : f ≤ M • posEvent f + M⁻¹ • (f * f) := fun ω' => by
      simp only [posEvent, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
      have hf' := hf ω'
      have hsq : 0 ≤ M⁻¹ * (f ω' * f ω') :=
        mul_nonneg (inv_nonneg.mpr hM.le) (mul_self_nonneg _)
      by_cases hfM : f ω' ≤ M
      · split_ifs with hpos
        · linarith
        · have : f ω' = 0 := le_antisymm (not_lt.mp hpos) hf'
          rw [this]; simp
      · push Not at hfM
        have hpos : 0 < f ω' := hM.trans hfM
        simp only [hpos, ↓reduceIte, mul_one]
        have : f ω' ≤ M⁻¹ * (f ω' * f ω') := by
          rw [← div_eq_inv_mul, le_div_iff₀ hM]; nlinarith
        linarith
    have h1 := 𝔼.mono t hle ω
    rw [map_add, map_smul, map_smul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul, hp, mul_zero, zero_add] at h1
    rw [← ha] at h1
    have := mul_le_mul_of_nonneg_right h1 hM.le
    rw [mul_assoc, mul_comm Q M, ← mul_assoc, inv_mul_cancel₀ hM.ne', one_mul] at this
    exact this
  have := hM (2 * (Q + 1) / a) (by positivity)
  have key : a * (2 * (Q + 1) / a) = 2 * (Q + 1) := by field_simp
  rw [key] at this
  linarith

/-- Cochrane (2023), Online Appendix p. 592: **expectations are strictly positive exactly on
events of positive conditional probability**: for every expectation system and every `f ≥ 0`,
`0 < E_t f` at `ω` if and only if `0 < E_t 1_{f>0}` at `ω`. -/
theorem E_pos_iff {f : Ω → ℝ} (hf : 0 ≤ f) (t : ℕ) (ω : Ω) :
    0 < 𝔼.E t f ω ↔ 0 < 𝔼.E t (posEvent f) ω :=
  ⟨E_posEvent_pos_of_E_pos 𝔼 hf, E_pos_of_E_posEvent_pos 𝔼 hf⟩

/-- Cochrane (2023), Online Appendix p. 592: **a strictly positive random variable has a strictly
positive expectation in every state, under every expectation system**, with no uniform lower
bound. -/
theorem E_pos_of_pos {f : Ω → ℝ} (hf : ∀ ω, 0 < f ω) (t : ℕ) (ω : Ω) : 0 < 𝔼.E t f ω := by
  have h1 : posEvent f = fun _ => 1 := funext fun ω' => by simp [posEvent, hf ω']
  rw [E_pos_iff 𝔼 (fun ω' => (hf ω').le), h1, 𝔼.const]
  norm_num

/-- Cochrane (2023), Online Appendix p. 592: the change in `B_{−1}^{(0)}/P_0` from `ε` to `ε'`
is `E_0` of the dilution difference `kCoef/B_1^{(2)}(ε') − kCoef/B_1^{(2)}(ε)`. -/
noncomputable def dilDiff (β : ℝ) (D : ℕ → ℕ → Ω → ℝ) (G : Ω → ℝ) (s : ℕ → Ω → ℝ)
    (ε ε' : ℝ) : Ω → ℝ :=
  kCoef β D s / (D 2 2 + ε' • G) - kCoef β D s / (D 2 2 + ε • G)

/-- Cochrane (2023), Online Appendix p. 592: the dilution difference in closed form,
`β² s_2 B_0^{(2)} (A₁ − A₂)(ε' − ε) G / (B_1^{(2)}(ε) B_1^{(2)}(ε'))`. -/
theorem dilDiff_eq {β ε ε' : ℝ} {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ}
    (h12 : ∀ ω, D 1 2 ω ≠ 0) (hpos : ∀ ω, D 2 2 ω + ε * G ω ≠ 0)
    (hpos' : ∀ ω, D 2 2 ω + ε' * G ω ≠ 0) (ω : Ω) :
    dilDiff β D G s ε ε' ω = β ^ 2 * s 2 ω * D 1 2 ω * (fracA D 1 ω - fracA D 2 ω) *
      ((ε' - ε) * G ω) / ((D 2 2 ω + ε * G ω) * (D 2 2 ω + ε' * G ω)) := by
  rw [dilDiff, kCoef_eq h12]
  have h1 := hpos ω
  have h2 := hpos' ω
  simp only [Pi.sub_apply, Pi.div_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
  rw [div_sub_div _ _ h2 h1, div_eq_div_iff (mul_ne_zero h2 h1) (mul_ne_zero h1 h2)]
  ring

/-- Cochrane (2023), Online Appendix p. 592: under the book's sign conditions the dilution
difference is nonnegative and positive exactly where the sale is larger, `1_{dilDiff>0} =
1_{G>0}`. -/
theorem dilDiff_sign {β ε ε' : ℝ} (hβ : β ≠ 0) {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ}
    {s : ℕ → Ω → ℝ} (hG0 : ∀ ω, 0 ≤ G ω) (hs2 : ∀ ω, 0 < s 2 ω) (h12 : ∀ ω, 0 < D 1 2 ω)
    (hA : ∀ ω, fracA D 2 ω < fracA D 1 ω) (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω)
    (hεε : ε < ε') :
    0 ≤ dilDiff β D G s ε ε' ∧ posEvent (dilDiff β D G s ε ε') = posEvent G := by
  have hpos' : ∀ ω, 0 < D 2 2 ω + ε' * G ω := fun ω => by nlinarith [hpos ω, hG0 ω]
  have hform := dilDiff_eq (β := β) (s := s) (fun ω => (h12 ω).ne') (fun ω => (hpos ω).ne')
    (fun ω => (hpos' ω).ne')
  have hq : ∀ ω, 0 < β ^ 2 * s 2 ω * D 1 2 ω * (fracA D 1 ω - fracA D 2 ω) := fun ω => by
    have := sub_pos.mpr (hA ω)
    have := hs2 ω
    have := h12 ω
    positivity
  have hden : ∀ ω, 0 < (D 2 2 ω + ε * G ω) * (D 2 2 ω + ε' * G ω) := fun ω =>
    mul_pos (hpos ω) (hpos' ω)
  have hd : 0 < ε' - ε := sub_pos.mpr hεε
  refine ⟨fun ω => ?_, funext fun ω => ?_⟩
  · rw [Pi.zero_apply, hform]
    have := hG0 ω
    have := hq ω
    have := hden ω
    positivity
  · simp only [posEvent]
    rw [hform]
    rcases (hG0 ω).lt_or_eq with hG | hG
    · have : 0 < β ^ 2 * s 2 ω * D 1 2 ω * (fracA D 1 ω - fracA D 2 ω) * ((ε' - ε) * G ω) /
          ((D 2 2 ω + ε * G ω) * (D 2 2 ω + ε' * G ω)) := by
        have := hq ω
        have := hden ω
        positivity
      simp [this, hG]
    · rw [← hG]; simp

/-- Cochrane (2023), Online Appendix eq. (1.66), p. 591:
`x0R ε' − x0R ε = E_0(dilDiff)/B_{−1}^{(0)}` whenever `B_1^{(2)}(ε)`, `B_1^{(2)}(ε')` are nonzero
in every state. -/
theorem x0R_sub (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼) {β ε ε' : ℝ}
    {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D)
    (hne : ∀ ω, D 2 2 ω + ε * G ω ≠ 0) (hne' : ∀ ω, D 2 2 ω + ε' * G ω ≠ 0) (ω : Ω) :
    x0R 𝔼 β D G s ε' ω - x0R 𝔼 β D G s ε ω = 𝔼.E 0 (dilDiff β D G s ε ε') ω / D 0 0 ω := by
  rw [x0R_pull 𝔼 hpo hdc hD hne, x0R_pull 𝔼 hpo hdc hD hne', dilDiff, map_sub]
  simp only [Pi.div_apply, Pi.add_apply, Pi.sub_apply]
  ring

/-- Cochrane (2023), Online Appendix p. 592 (last bullet), with random debt: **the exact strict
sign rule.** Under the book's sign conditions alone (`A₁ > A₂`, `B_0^{(2)} > 0`, `s_2 > 0`,
`β ≠ 0`, `B_{−1}^{(0)} > 0`, a larger sale `G ≥ 0`, `ε < ε'`), larger state-contingent future
sales strictly lower `P_0` in state `ω` if and only if the larger sale has positive conditional
probability, `E_0 1_{G>0} > 0`, at `ω`. No uniform bound is assumed. -/
theorem x0R_strict_iff (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼) {β ε ε' : ℝ}
    (hβ : β ≠ 0) {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D)
    (hG0 : ∀ ω, 0 ≤ G ω) (hs2 : ∀ ω, 0 < s 2 ω) (h12 : ∀ ω, 0 < D 1 2 ω)
    (hA : ∀ ω, fracA D 2 ω < fracA D 1 ω) (hD00 : ∀ ω, 0 < D 0 0 ω)
    (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hεε : ε < ε') (ω : Ω) :
    x0R 𝔼 β D G s ε ω < x0R 𝔼 β D G s ε' ω ↔ 0 < 𝔼.E 0 (posEvent G) ω := by
  have hpos' : ∀ ω, 0 < D 2 2 ω + ε' * G ω := fun ω => by nlinarith [hpos ω, hG0 ω]
  have hsub := x0R_sub 𝔼 (β := β) (s := s) hpo hdc hD (fun ω => (hpos ω).ne')
    (fun ω => (hpos' ω).ne') ω
  obtain ⟨hnn, hev⟩ := dilDiff_sign hβ hG0 hs2 h12 hA hpos hεε
  rw [← sub_pos, hsub, div_pos_iff_of_pos_right (hD00 ω), E_pos_iff 𝔼 hnn, hev]

/-- Cochrane (2023), Online Appendix p. 592: where the larger sale has zero conditional
probability (`E_0 1_{G>0} = 0`), expected future sales have no effect on `P_0` at all. -/
theorem x0R_eq_of_null (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼) {β ε ε' : ℝ}
    (hβ : β ≠ 0) {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D)
    (hG0 : ∀ ω, 0 ≤ G ω) (hs2 : ∀ ω, 0 < s 2 ω) (h12 : ∀ ω, 0 < D 1 2 ω)
    (hA : ∀ ω, fracA D 2 ω < fracA D 1 ω)
    (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hεε : ε < ε') {ω : Ω}
    (hnull : 𝔼.E 0 (posEvent G) ω = 0) :
    x0R 𝔼 β D G s ε' ω = x0R 𝔼 β D G s ε ω := by
  have hpos' : ∀ ω, 0 < D 2 2 ω + ε' * G ω := fun ω => by nlinarith [hpos ω, hG0 ω]
  have hsub := x0R_sub 𝔼 (β := β) (s := s) hpo hdc hD (fun ω => (hpos ω).ne')
    (fun ω => (hpos' ω).ne') ω
  obtain ⟨hnn, hev⟩ := dilDiff_sign hβ hG0 hs2 h12 hA hpos hεε
  have h0 : 𝔼.E 0 (dilDiff β D G s ε ε') ω ≤ 0 := by
    by_contra hlt
    push Not at hlt
    have := (E_pos_iff 𝔼 hnn 0 ω).1 hlt
    rw [hev, hnull] at this
    exact lt_irrefl _ this
  have h0' : 0 ≤ 𝔼.E 0 (dilDiff β D G s ε ε') ω := by
    have := 𝔼.mono 0 hnn ω
    rwa [show (0 : Ω → ℝ) = fun _ => 0 from rfl, 𝔼.const] at this
  have : 𝔼.E 0 (dilDiff β D G s ε ε') ω = 0 := le_antisymm h0 h0'
  rw [this, zero_div, sub_eq_zero] at hsub
  exact hsub

/-- Cochrane (2023), Online Appendix p. 592 (last bullet), with random debt: **if the sale is
larger in every state (`G > 0`), larger future sales strictly lower `P_0` in every state, for
every expectation system, under the book's sign conditions alone** (no uniform bounds, unlike
`TidyR5FutureSalesRandom.x0R_strictMono`). -/
theorem x0R_strictMono_pos (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼)
    {β ε ε' : ℝ} (hβ : β ≠ 0) {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (hG0 : ∀ ω, 0 < G ω) (hs2 : ∀ ω, 0 < s 2 ω)
    (h12 : ∀ ω, 0 < D 1 2 ω) (hA : ∀ ω, fracA D 2 ω < fracA D 1 ω) (hD00 : ∀ ω, 0 < D 0 0 ω)
    (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hεε : ε < ε') (ω : Ω) :
    x0R 𝔼 β D G s ε ω < x0R 𝔼 β D G s ε' ω := by
  rw [x0R_strict_iff 𝔼 hpo hdc hβ hD (fun ω => (hG0 ω).le) hs2 h12 hA hD00 hpos hεε]
  exact E_pos_of_pos 𝔼 (fun ω' => by simp [posEvent, hG0 ω']) 0 ω

/-! ### The exact counterexample: a larger sale only in a zero-weight state -/

/-- Cochrane (2023), Online Appendix §A1.14 (counterexample): the date-0 forecast that puts all
weight on the state `true`, `E_0 f = f(true)`; full information from date 1 on. -/
noncomputable def nullE (t : ℕ) : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ) :=
  if t = 0 then LinearMap.pi (fun _ => LinearMap.proj true) else LinearMap.id

/-- Cochrane (2023), Online Appendix §A1.14 (counterexample): `nullE` at date 0. -/
theorem nullE_zero (f : Bool → ℝ) : nullE 0 f = fun _ => f true := by
  simp [nullE]; rfl

/-- Cochrane (2023), Online Appendix §A1.14 (counterexample): `nullE` from date 1 on. -/
theorem nullE_succ (t : ℕ) (f : Bool → ℝ) : nullE (t + 1) f = f := by
  simp [nullE]

/-- Cochrane (2023), Online Appendix §A1.14 (counterexample): `nullE` is an expectation system:
the state `false` has date-0 probability zero and is revealed at date 1. -/
noncomputable def nullSys : ExpectationSystem Bool where
  E := nullE
  const := fun t c => by
    rcases t with _ | t
    · rw [nullE_zero]
    · rw [nullE_succ]
  mono := fun t x y h => by
    rcases t with _ | t
    · rw [nullE_zero, nullE_zero]; exact fun _ => h true
    · rw [nullE_succ, nullE_succ]; exact h
  tower := fun {s t} hst x => by
    rcases s with _ | s
    · rcases t with _ | t
      · rw [nullE_zero, nullE_zero]
      · rw [nullE_succ]
    · obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      simp only [nullE_succ]
  known := fun {s t} hst x => by
    rcases s with _ | s
    · rcases t with _ | t
      · rw [nullE_zero, nullE_zero]
      · rw [nullE_zero, nullE_succ]
    · obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      rw [nullE_succ, nullE_succ]

/-- Cochrane (2023), Online Appendix §A1.14 (counterexample): `nullSys` has the pull-out
property. -/
theorem nullSys_pullOut : nullSys.PullOut := by
  intro t a y ha
  rcases t with _ | t
  · change nullE 0 a = a at ha
    change nullE 0 (a * y) = a * nullE 0 y
    rw [nullE_zero] at ha ⊢
    rw [nullE_zero]
    funext ω
    have := congrFun ha ω
    simp only [Pi.mul_apply] at this ⊢
    rw [← this]
  · change nullE (t + 1) (a * y) = a * nullE (t + 1) y
    rw [nullE_succ, nullE_succ]

/-- Cochrane (2023), Online Appendix §A1.14 (counterexample): `nullSys` is closed under
quotients of known variables. -/
theorem nullSys_divClosed : PolicyConstraints.DivClosed nullSys := by
  intro t f g hf hg
  rcases t with _ | t
  · change nullE 0 f = f at hf
    change nullE 0 g = g at hg
    change nullE 0 (f / g) = f / g
    rw [nullE_zero] at hf hg ⊢
    funext ω
    have h1 := congrFun hf ω
    have h2 := congrFun hg ω
    simp only [Pi.div_apply] at h1 h2 ⊢
    rw [← h1, ← h2]
  · change nullE (t + 1) (f / g) = f / g
    rw [nullE_succ]

/-- Cochrane (2023), Online Appendix §A1.14 (counterexample): the debt positions, all known at
date 0: `B_{−1}^{(0)} = 1`, `B_{−1}^{(1)} = 0`, `B_0^{(1)} = 1`, `B_{−1}^{(2)} = B_0^{(2)} =
B_1^{(2)} = 1`, nothing longer. So `A₁ = 1 > 0 = A₂`. -/
noncomputable def nullD : ℕ → ℕ → Bool → ℝ := fun t m _ =>
  if m = 0 ∧ t = 0 then 1 else if m = 1 ∧ t = 1 then 1 else if m = 2 then 1 else 0

/-- Cochrane (2023), Online Appendix §A1.14 (counterexample): the larger sale, `G = 1` in the
zero-probability state `false` only. -/
noncomputable def nullG : Bool → ℝ := fun ω => if ω then 0 else 1

/-- Cochrane (2023), Online Appendix §A1.14 (counterexample): **the book's sign conditions hold,
the sale is larger in some state, but `P_0` does not move.** Under `nullSys` (pull-out and
closed under quotients), with the debt `nullD`, surpluses `s ≡ 1`, `β = 1/2` and the direction
`nullG` (nonnegative, known at date 1, positive in the state `false`): `A₁ > A₂`,
`B_0^{(2)} > 0`, `s_2 > 0`, `B_{−1}^{(0)} > 0`, yet `x0R 0 = x0R 1` in every state, because
`E_0 1_{G>0} = 0`. -/
theorem null_counterexample :
    Predetermined nullSys nullD ∧ nullSys.E 1 nullG = nullG ∧ (∀ ω, 0 ≤ nullG ω) ∧
      nullG false = 1 ∧ (∀ ω, fracA nullD 2 ω < fracA nullD 1 ω) ∧ (∀ ω, 0 < nullD 1 2 ω) ∧
      (∀ ω, 0 < nullD 0 0 ω) ∧ (∀ ω, 0 < nullD 2 2 ω + 0 * nullG ω) ∧
      (∀ ω, nullSys.E 0 (posEvent nullG) ω = 0) ∧
      ∀ ω, x0R nullSys (1 / 2) nullD nullG (fun _ _ => 1) 1 ω =
        x0R nullSys (1 / 2) nullD nullG (fun _ _ => 1) 0 ω := by
  have hconst : ∀ u t m, nullSys.E u (nullD t m) = nullD t m := fun u t m => by
    have : nullD t m = fun _ => nullD t m true := funext fun _ => rfl
    rw [this, nullSys.const]
  have hnull : ∀ ω, nullSys.E 0 (posEvent nullG) ω = 0 := fun ω => by
    change nullE 0 (posEvent nullG) ω = 0
    rw [nullE_zero]; simp [posEvent, nullG]
  have hA : ∀ ω, fracA nullD 2 ω < fracA nullD 1 ω := fun ω => by
    simp [fracA, nullD]
  have hpred : Predetermined nullSys nullD :=
    ⟨fun m => hconst 0 0 m, fun t m => hconst t (t + 1) m⟩
  refine ⟨hpred, ?_, fun ω => by cases ω <;> simp [nullG], by simp [nullG], hA,
    fun ω => by simp [nullD], fun ω => by simp [nullD], fun ω => by simp [nullD], hnull,
    fun ω => ?_⟩
  · change nullE 1 nullG = nullG
    exact nullE_succ 0 nullG
  · exact x0R_eq_of_null nullSys nullSys_pullOut nullSys_divClosed (by norm_num) hpred
      (fun ω => by cases ω <;> simp [nullG]) (fun _ => one_pos) (fun ω => by simp [nullD]) hA
      (fun ω => by simp [nullD]) zero_lt_one (hnull ω)

/-- Cochrane (2023), Online Appendix eqs. (1.63)–(1.66) (counterexample, in equilibrium): in the
economy of `null_counterexample`, **every** equilibrium with the larger sale (`ε = 1`) has the same
`1/P_0` as every equilibrium without it (`ε = 0`): the flow conditions (7.1) at dates 0, 1, 2
pin `1/P_0 = x0R ε` (`TidyR5FutureSalesRandom.x0_eq_x0R`), and `x0R 1 = x0R 0`. -/
theorem null_counterexample_eqm {x x' : ℕ → Bool → ℝ}
    (h0 : RealFlow nullSys (1 / 2) (pertD nullD nullG 1) x (fun _ _ => 1) 0)
    (h1 : RealFlow nullSys (1 / 2) (pertD nullD nullG 1) x (fun _ _ => 1) 1)
    (h2 : RealFlow nullSys (1 / 2) (pertD nullD nullG 1) x (fun _ _ => 1) 2)
    (h0' : RealFlow nullSys (1 / 2) (pertD nullD nullG 0) x' (fun _ _ => 1) 0)
    (h1' : RealFlow nullSys (1 / 2) (pertD nullD nullG 0) x' (fun _ _ => 1) 1)
    (h2' : RealFlow nullSys (1 / 2) (pertD nullD nullG 0) x' (fun _ _ => 1) 2) :
    x 0 = x' 0 := by
  obtain ⟨hpred, hG1, hG0, -, -, -, -, -, -, heq⟩ := null_counterexample
  have hD3 : ∀ t j, nullD t (j + 3) = 0 := fun t j => by
    funext ω; simp [nullD]
  have hD11 : ∀ ω, nullD 1 1 ω ≠ 0 := fun ω => by simp [nullD]
  have hD00 : ∀ ω, nullD 0 0 ω ≠ 0 := fun ω => by simp [nullD]
  have hne : ∀ ε : ℝ, 0 ≤ ε → ∀ ω, nullD 2 2 ω + ε * nullG ω ≠ 0 := fun ε hε ω => by
    have : nullD 2 2 ω = 1 := by simp [nullD]
    rw [this]
    have := mul_nonneg hε (hG0 ω)
    linarith
  rw [x0_eq_x0R nullSys nullSys_pullOut hpred hG1 hD3 h0 h1 h2 (hne 1 zero_le_one) hD11 hD00,
    x0_eq_x0R nullSys nullSys_pullOut hpred hG1 hD3 h0' h1' h2' (hne 0 le_rfl) hD11 hD00]
  exact funext heq

end Cochrane.LongTermDebtDynamics.TidyR6StrictSignRule
