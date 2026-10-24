/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MonetaryPolicyDesign.Ex4_4
import MonetaryPolicyDesign.MoneyRuleDeterminacy

/-!
# Exercise 4.4(c): the money supply rule implements the optimum uniquely

Galí (2015), Chapter 4, Exercise 4.4(c), p. 123. Under the money supply rule
`m_t = p* + yⁿ_t − η rⁿ_t`, the optimal outcome `ỹ = π = 0`, `p = p*`, `i = rⁿ` is an equilibrium
(`Ex4_4.moneyRule_equilibrium`). This module proves that it is the ONLY bounded equilibrium,
the claim recorded (and deferred) as `Ex4_4.MoneyRuleUniqueness`.

## The reduction to (34)

With real balances measured from target, `l̂_{t−1} = p* − p_{t−1}` (`realBal`, so `l̂_{−1} = 0`),
money demand and the rule give `η (i_t − rⁿ_t) = ỹ_t − l̂_t`, and the IS equation, the Phillips
curve and the price-level identity become EXACTLY the Chapter 3 system (34) with all shocks set
to zero (`system34_of_moneyRule`): the natural-rate and natural-output terms cancel. The
Chapter 3 determinacy theorem (`MoneyRuleDeterminacy.system34_existsUnique`, restated in this
project) then says the bounded equilibrium of (34) with `l̂_{−1} = 0` is unique; the zero path is
one, so `ỹ = π = 0`.

## Main results

* `system34_of_moneyRule`: every equilibrium under the money rule solves (34) with zero shocks.
* `moneyRule_gap_infl_zero`, `moneyRuleUniqueness_holds`: **`Ex4_4.MoneyRuleUniqueness`
  holds** for `σ > 0`, `η ≥ 0`, `κ > 0`, `0 < β ≤ 1`, for any expectation system (the boundedness
  of `rⁿ`, `yⁿ` is not even needed).
* `moneyRule_unique_outcome`, `moneyRule_implements_uniquely`: every bounded equilibrium under the
  rule has `ỹ = π = 0`, `p_t = p*`, `i_t = rⁿ_t`, and this outcome is an equilibrium.
-/

namespace Gali.MonetaryPolicyDesign.Ex4_4Determinacy

open Ex4_4 MoneyRuleSystem MoneyRuleDeterminacy

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Ex. 4.4(c), p. 123: real balances measured from target,
`l̂_{t−1} = p* − p_{t−1}` (so `l̂_{−1} = 0` and `l̂_t = p* − p_t`). -/
def realBal (pstar : ℝ) (p : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => (fun _ => pstar) - lagP pstar p t

omit 𝔼 in
/-- Galí (2015), Ex. 4.4(c): `l̂_{−1} = 0`. -/
theorem realBal_zero (pstar : ℝ) (p : ℕ → Ω → ℝ) : realBal pstar p 0 = fun _ => 0 := by
  funext ω
  simp [realBal, lagP]

/-- Galí (2015), Ex. 4.4: the lagged price level `p_{t−1}` is adapted when `p` is. -/
theorem lagP_adapted {pstar : ℝ} {p : ℕ → Ω → ℝ} (hp : 𝔼.Adapted p) :
    𝔼.Adapted (lagP pstar p) := by
  intro t
  cases t with
  | zero => exact 𝔼.const 0 pstar
  | succ t =>
    change 𝔼.E (t + 1) (p t) = p t
    calc 𝔼.E (t + 1) (p t) = 𝔼.E (t + 1) (𝔼.E t (p t)) := by rw [hp t]
      _ = 𝔼.E t (p t) := 𝔼.known (Nat.le_succ t) _
      _ = p t := hp t

omit 𝔼 in
/-- Galí (2015), Ex. 4.4: the lagged price level is bounded when `p` is. -/
theorem lagP_bounded {pstar : ℝ} {p : ℕ → Ω → ℝ} (hp : BoundedProc p) :
    BoundedProc (lagP pstar p) := by
  obtain ⟨M, hM⟩ := hp
  refine ⟨max M |pstar|, fun t ω => ?_⟩
  cases t with
  | zero => exact le_max_right _ _
  | succ t => exact (hM t ω).trans (le_max_left _ _)

/-- Galí (2015), Ex. 4.4(c): real balances `l̂_t = p* − p_t` are known at `t` (predetermined). -/
theorem realBal_pred {pstar : ℝ} {p : ℕ → Ω → ℝ} (hp : 𝔼.Adapted p) :
    Predetermined 𝔼 (realBal pstar p) := by
  intro t
  change 𝔼.E t ((fun _ => pstar) - p t) = (fun _ => pstar) - p t
  rw [map_sub, 𝔼.const, hp t]

/-- Galí (2015), Ex. 4.4(c): real balances are adapted. -/
theorem realBal_adapted {pstar : ℝ} {p : ℕ → Ω → ℝ} (hp : 𝔼.Adapted p) :
    𝔼.Adapted (realBal pstar p) := by
  intro t
  change 𝔼.E t ((fun _ => pstar) - lagP pstar p t) = (fun _ => pstar) - lagP pstar p t
  rw [map_sub, 𝔼.const, lagP_adapted 𝔼 hp t]

omit 𝔼 in
/-- Galí (2015), Ex. 4.4(c): real balances are bounded. -/
theorem realBal_bounded {pstar : ℝ} {p : ℕ → Ω → ℝ} (hp : BoundedProc p) :
    BoundedProc (realBal pstar p) := by
  obtain ⟨M, hM⟩ := lagP_bounded (pstar := pstar) hp
  refine ⟨|pstar| + M, fun t ω => ?_⟩
  change |pstar - lagP pstar p t ω| ≤ _
  exact (abs_sub _ _).trans (add_le_add le_rfl (hM t ω))

/-- Galí (2015), Ex. 4.4: inflation `π_t = p_t − p_{t−1}` is adapted when `p` is. -/
theorem infl_adapted {pstar : ℝ} {p infl : ℕ → Ω → ℝ} (hpl : PriceLevel pstar p infl)
    (hp : 𝔼.Adapted p) : 𝔼.Adapted infl := by
  intro t
  rw [hpl t, map_sub, hp t, lagP_adapted 𝔼 hp t]

omit 𝔼 in
/-- Galí (2015), Ex. 4.4: inflation is bounded when `p` is. -/
theorem infl_bounded {pstar : ℝ} {p infl : ℕ → Ω → ℝ} (hpl : PriceLevel pstar p infl)
    (hp : BoundedProc p) : BoundedProc infl := by
  obtain ⟨M, hM⟩ := hp
  obtain ⟨M', hM'⟩ := lagP_bounded (pstar := pstar) ⟨M, hM⟩
  refine ⟨M + M', fun t ω => ?_⟩
  rw [hpl t, Pi.sub_apply]
  exact (abs_sub _ _).trans (add_le_add (hM t ω) (hM' t ω))

/-- **Galí (2015), Ex. 4.4(c), p. 123 (reduction)**: every equilibrium under the money rule
`m_t = p* + yⁿ_t − η rⁿ_t` (with an adapted price level and `σ ≠ 0`) solves the Chapter 3 system
(34) for `(ỹ_t, π_t, l̂_{t−1} = p* − p_{t−1})` with ALL shocks equal to zero. -/
theorem system34_of_moneyRule {β σ κ η pstar : ℝ} (hσ : σ ≠ 0)
    {rn yn ygap infl p m i : ℕ → Ω → ℝ}
    (h : FullEquilibrium 𝔼 β σ κ η pstar rn yn ygap infl p m i)
    (hm : Ex4_4.MoneyRule η pstar rn yn m) (hp : 𝔼.Adapted p) :
    System34 𝔼 σ η β κ ygap infl (realBal pstar p) 0 0 0 := by
  obtain ⟨⟨hD, hN⟩, hPL, hMD⟩ := h
  intro t ω
  have hd := congrFun (hD t) ω
  have hn := congrFun (hN t) ω
  have hpl := congrFun (hPL t) ω
  have hmd := congrFun (hMD t) ω
  have hr := congrFun (hm t) ω
  have hEL : 𝔼.E t (realBal pstar p (t + 1)) ω = pstar - p t ω := by
    rw [realBal_pred 𝔼 hp t]
    rfl
  have hRt : realBal pstar p t ω = pstar - lagP pstar p t ω := rfl
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hd hn hpl hmd hr
  have hd' : σ * ygap t ω = σ * 𝔼.E t (ygap (t + 1)) ω -
      (i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) := by
    rw [hd, mul_sub, ← mul_assoc, mul_inv_cancel₀ hσ, one_mul]
  funext j
  fin_cases j
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
      shockVec]
    linear_combination η * hd' - hmd + hr - hEL
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
      shockVec]
    linarith
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
      shockVec]
    linarith

/-- Galí (2015), Ex. 4.4(c): the zero path solves (34) with zero shocks and `l̂_{−1} = 0`. -/
theorem equil34_zero (σ η β κ : ℝ) :
    Equil34 𝔼 σ η β κ 0 0 0 0 (0 : ℕ → Ω → ℝ) 0 0 := by
  have hza : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => map_zero (𝔼.E t)
  have hzb : BoundedProc (0 : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
  refine ⟨?_, fun t => map_zero (𝔼.E t), rfl, hza, hza, hza, hzb, hzb, hzb⟩
  intro t ω
  funext j
  fin_cases j <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, stateVec, expVec, shockVec]

/-- **Galí (2015), Ex. 4.4(c), p. 123 — uniqueness**: for `σ > 0`, `η ≥ 0`, `κ > 0`,
`0 < β ≤ 1` and any expectation system, under the money rule `m_t = p* + yⁿ_t − η rⁿ_t` every
equilibrium with bounded adapted output gap and price level has `ỹ = π = 0` (for ANY shocks
`rⁿ`, `yⁿ`: they cancel from the reduced system). -/
theorem moneyRule_gap_infl_zero {β σ κ η pstar : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) {rn yn ygap infl p m i : ℕ → Ω → ℝ}
    (h : FullEquilibrium 𝔼 β σ κ η pstar rn yn ygap infl p m i)
    (hm : Ex4_4.MoneyRule η pstar rn yn m) (hag : 𝔼.Adapted ygap) (hap : 𝔼.Adapted p)
    (hbg : BoundedProc ygap) (hbp : BoundedProc p) :
    ygap = (fun _ => 0) ∧ infl = (fun _ => 0) := by
  have hza : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => map_zero (𝔼.E t)
  have hzb : BoundedProc (0 : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
  obtain ⟨v, -, huniq⟩ := system34_existsUnique 𝔼 hσ hη hκ hβ0 hβ1 hzb hzb hzb hza hza hza 0
  have hpl := h.2.1
  have e1 := huniq (ygap, infl, realBal pstar p)
    ⟨system34_of_moneyRule 𝔼 hσ.ne' h hm hap, realBal_pred 𝔼 hap, realBal_zero pstar p, hag,
      infl_adapted 𝔼 hpl hap, realBal_adapted 𝔼 hap, hbg, infl_bounded hpl hbp,
      realBal_bounded hbp⟩
  have e0 := huniq (0, 0, 0) (equil34_zero 𝔼 σ η β κ)
  have e := e1.trans e0.symm
  simp only [Prod.mk.injEq] at e
  exact ⟨e.1, e.2.1⟩

/-- **Galí (2015), Ex. 4.4(c), p. 123 — uniqueness, PROVED**: for `σ > 0`, `η ≥ 0`, `κ > 0`,
`0 < β ≤ 1` and any expectation system, the claim `Ex4_4.MoneyRuleUniqueness` (recorded without
proof in `Ex4_4`) holds. -/
theorem moneyRuleUniqueness_holds {β σ κ η pstar : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) : MoneyRuleUniqueness 𝔼 β σ κ η pstar :=
  fun _ _ _ _ _ _ _ _ _ _ _ h hm hag hap hbg hbp =>
    moneyRule_gap_infl_zero 𝔼 hσ hη hκ hβ0 hβ1 h hm hag hap hbg hbp

/-- **Galí (2015), Ex. 4.4(c), p. 123**: every bounded equilibrium under the money rule attains
the optimum: `ỹ = π = 0`, the price level stays at `p*`, and `i_t = rⁿ_t`. -/
theorem moneyRule_unique_outcome {β σ κ η pstar : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) {rn yn ygap infl p m i : ℕ → Ω → ℝ}
    (h : FullEquilibrium 𝔼 β σ κ η pstar rn yn ygap infl p m i)
    (hm : Ex4_4.MoneyRule η pstar rn yn m) (hag : 𝔼.Adapted ygap) (hap : 𝔼.Adapted p)
    (hbg : BoundedProc ygap) (hbp : BoundedProc p) :
    ygap = (fun _ => 0) ∧ infl = (fun _ => 0) ∧ (∀ t, p t = fun _ => pstar) ∧ i = rn := by
  obtain ⟨hg, hi⟩ := moneyRule_gap_infl_zero 𝔼 hσ hη hκ hβ0 hβ1 h hm hag hap hbg hbp
  subst hg hi
  exact ⟨rfl, rfl, price_level_const h.2.1, (zero_equilibrium_iff 𝔼 hσ.ne' rn i).mp h.1⟩

/-- **Galí (2015), Ex. 4.4(c), p. 123: the money rule implements the optimum UNIQUELY**: for
`σ > 0`, `η ≥ 0`, `κ > 0`, `0 < β ≤ 1`, under `m_t = p* + yⁿ_t − η rⁿ_t` the optimal outcome
(`ỹ = π = 0`, `p = p*`, `i = rⁿ`) is an equilibrium, and every equilibrium with bounded adapted
output gap and price level is that outcome. -/
theorem moneyRule_implements_uniquely {β σ κ η pstar : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η)
    (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (rn yn : ℕ → Ω → ℝ) :
    FullEquilibrium 𝔼 β σ κ η pstar rn yn (fun _ => 0) (fun _ => 0) (fun _ _ => pstar)
        (fun t => (fun _ => pstar) + yn t - η • rn t) rn ∧
      ∀ ygap infl p m i : ℕ → Ω → ℝ,
        FullEquilibrium 𝔼 β σ κ η pstar rn yn ygap infl p m i →
        Ex4_4.MoneyRule η pstar rn yn m → 𝔼.Adapted ygap → 𝔼.Adapted p →
        BoundedProc ygap → BoundedProc p →
        ygap = (fun _ => 0) ∧ infl = (fun _ => 0) ∧ (∀ t, p t = fun _ => pstar) ∧ i = rn :=
  ⟨(moneyRule_equilibrium 𝔼 hσ.ne' rn yn).1, fun _ _ _ _ _ h hm hag hap hbg hbp =>
    moneyRule_unique_outcome 𝔼 hσ hη hκ hβ0 hβ1 h hm hag hap hbg hbp⟩

end Gali.MonetaryPolicyDesign.Ex4_4Determinacy
