/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR6ActiveFiscalMeasureExist

/-!
# A mean-zero debt bubble: coordination is not necessary under the unconditional TVC

Cochrane (2023), *The Fiscal Theory of the Price Level*, Ch. 19, §19.5, pp. 448–454, and the
transversality condition (19.28), p. 449. `TidyR6ActiveFiscalMeasure.MeasMonetaryEq` imposes the
transversality condition only in unconditional expectation, `E[β^Tx_T] → 0`.
`TidyR6ActiveFiscalMeasureExist.meas_std_exists_iff` characterises existence of the standard
equilibrium within equilibria with bounded real liabilities. This module shows that the bound
cannot be dropped: in an uncoordinated economy a standard-price `MeasMonetaryEq` exists whose
real debt explodes along every path while its discounted mean tends to zero.

## The economy

The coin-flip tree as a probability space (`ExpectationsMeasure.TreeBridge.treeSystem`),
`y = V = 1`, constant money `M = 1`, so `P = MV/y = 1` and `q = β`. Surplus `s_0 = s̄`,
`s_t = s̄ + σ·1{first coin heads}` for `t ≥ 1` (`TidyR6ActiveFiscalTree.shockSurplus`),
`s̄ ≥ 0`, `σ > 0`. Real liabilities `x_0 = βx̄_1 + s̄ + 1 − β`,
`x_{t+1} = x*(ω) + β^{−t}(x̄_1 − x*(ω))` with `x* = (s̄ + 1 − β + σh)/(1 − β)` the state's
valuation and `x̄_1 = E[x*]` (`bubbleW`); bonds `B_t = x_t − 1`.

## Main results

* `bubble_eq`: this is a `MeasMonetaryEq` with the standard price level.
* Inside `bubble_eq`, `E[β^{t+1}x_{t+1}] = β^{t+1}x̄_1 → 0` (the unconditional TVC holds),
  while `bubble_path`: `β^{t+1}x_{t+1} − β(x̄_1 − x*) = β^{t+1}x* → 0` with
  `x̄_1 − x* = ±σ/(2(1 − β))`
  on every path (the discounted debt does not vanish: a mean-zero bubble).
* `bubble_unbounded`: real liabilities are unbounded.
* `bubble_not_coordinated`: the surplus is NOT coordinated with money (`CoordinatedM` fails),
  though a standard-price `MeasMonetaryEq` exists. So coordination is necessary only for
  equilibria with bounded real debt (or with the conditional TVCs of
  `TidyR6ActiveFiscalTree.StochMonetaryEq`), as in `meas_std_exists_iff`.
-/

namespace Cochrane.Monetarism.TidyR6ActiveFiscalBubble

open MeasureTheory Filter Topology
open Cochrane.Monetarism.ExpectationsMeasure
open Cochrane.Monetarism.ExpectationsFiniteTree (coinTree firstHeads coinObs)
open Cochrane.Monetarism.TidyR6ActiveFiscalTree (stdPrice wealth shockSurplus)
open Cochrane.Monetarism.TidyR6ActiveFiscalMeasure
open Cochrane.Monetarism.TidyR6ActiveFiscalMeasureExist

/-- Cochrane (2023), p. 449 (the probability space): the coin-flip tree as a measure-theoretic
expectation system. -/
noncomputable def bubbleS : MeasExpectationSystem (Bool × Bool) := TreeBridge.treeSystem coinTree

/-- Cochrane (2023), (19.35), p. 450: the valuation of surpluses plus seigniorage once the
first coin is known, `x* = (s̄ + 1 − β + σh)/(1 − β)`. -/
noncomputable def wStar (β sbar σ : ℝ) (ω : Bool × Bool) : ℝ :=
  (sbar + (1 - β) + σ * firstHeads ω) / (1 - β)

/-- Cochrane (2023), (19.35), p. 450: the date-1 real liabilities, the mean of `x*`. -/
noncomputable def wBar (β sbar σ : ℝ) : ℝ := (sbar + (1 - β) + σ / 2) / (1 - β)

/-- Cochrane (2023), (19.28), p. 449: real liabilities of the bubble equilibrium,
`x_0 = βx̄_1 + s̄ + 1 − β`, `x_{t+1} = x* + β^{−t}(x̄_1 − x*)`. -/
noncomputable def bubbleW (β sbar σ : ℝ) (t : ℕ) (ω : Bool × Bool) : ℝ :=
  if t = 0 then β * wBar β sbar σ + (sbar + (1 - β))
  else wStar β sbar σ ω + (β ^ (t - 1))⁻¹ * (wBar β sbar σ - wStar β sbar σ ω)

/-- Cochrane (2023), (19.27), p. 449: the bonds of the bubble equilibrium, `B_{t−1} = x_t − 1`
(`P = M = 1`). -/
noncomputable def bubbleB (β sbar σ : ℝ) (t : ℕ) (ω : Bool × Bool) : ℝ := bubbleW β sbar σ t ω - 1

/-- Cochrane (2023), p. 449: on the coin tree, a function of the first coin is known from
date 1 on.
Probability-space version of `TidyR6ActiveFiscalTree.firstHeads_known`. -/
theorem firstCoin_meas {t : ℕ} (ht : 1 ≤ t) {f : Bool × Bool → ℝ}
    (hf : ∀ ω ω', ω.1 = ω'.1 → f ω = f ω') : StronglyMeasurable[bubbleS.𝓕 t] f := by
  have e : f = coinTree.condE t f := by
    funext ω
    refine (coinTree.condE_of_const_on_cell fun ω' h => ?_).symm
    change Setoid.ker (coinObs t) ω' ω at h
    rw [Setoid.ker_def] at h
    simp only [coinObs, Prod.mk.injEq, ht, ↓reduceIte] at h
    exact hf ω' ω h.1
  rw [e]
  exact TreeBridge.stronglyMeasurable_condE coinTree t f

/-- Cochrane (2023), p. 449: the bubble liabilities depend on the state only through the first
coin. -/
theorem bubbleW_dep (β sbar σ : ℝ) (t : ℕ) {ω ω' : Bool × Bool} (h : ω.1 = ω'.1) :
    bubbleW β sbar σ t ω = bubbleW β sbar σ t ω' := by
  have hf : firstHeads ω = firstHeads ω' := by simp [firstHeads, h]
  simp only [bubbleW, wStar, hf]

/-- **Cochrane (2023), (19.27)–(19.28), pp. 449–450: the bubble is a standard-price
equilibrium.** With `0 < β < 1`, `s̄ ≥ 0`, `σ > 0`, the price level `P = MV/y = 1`, bonds
`bubbleB` and the surplus `shockSurplus s̄ σ` form a `MeasMonetaryEq` on the coin tree. -/
theorem bubble_eq {β sbar σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    MeasMonetaryEq bubbleS β 1 1 (stdPrice 1 1 fun _ _ => 1) (bubbleB β sbar σ)
      (fun _ _ => 1) (shockSurplus sbar σ) := by
  have hP : stdPrice 1 1 (fun (_ : ℕ) (_ : Bool × Bool) => (1 : ℝ)) = fun _ _ => 1 := by
    funext t ω; simp [stdPrice]
  have hQ : ∀ t, bondPriceM bubbleS β (fun _ _ => (1 : ℝ)) t = fun _ => β := by
    intro t
    unfold bondPriceM
    have e : (fun _ : Bool × Bool => β * (1 : ℝ) / 1) = fun _ => β := by funext; ring
    rw [e, bubbleS.E_const]
  have h1β : (1 - β) ≠ 0 := by linarith
  rw [hP]
  refine ⟨fun _ _ => one_pos, fun _ => stronglyMeasurable_const, fun t => ?_,
    fun _ => stronglyMeasurable_const, fun _ => Integrable.of_finite,
    fun _ => Integrable.of_finite, fun _ => Integrable.of_finite,
    fun _ => ae_of_all _ fun _ => by norm_num, fun t => ae_of_all _ fun ω => ?_,
    fun t => ae_of_all _ fun ω => ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht
      have e : bubbleB β sbar σ (0 + 1) = fun _ => wBar β sbar σ - 1 := by
        funext ω; simp [bubbleB, bubbleW]
      rw [e]; exact stronglyMeasurable_const
    · exact firstCoin_meas ht fun ω ω' h => by
        simp only [bubbleB, bubbleW_dep β sbar σ (t + 1) h]
  · rw [hQ t]
    exact ⟨hβ1.le, fun _ => by norm_num⟩
  · rw [hQ t]
    simp only [bubbleB]
    rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht
      have e0 : bubbleW β sbar σ 0 ω = β * wBar β sbar σ + (sbar + (1 - β)) := by
        simp [bubbleW]
      have e1 : bubbleW β sbar σ (0 + 1) ω = wBar β sbar σ := by simp [bubbleW]
      rw [e0, e1]
      simp only [shockSurplus, ↓reduceIte]
      ring
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt ht
      simp only [bubbleW, shockSurplus, wStar, show 0 + k + 1 ≠ 0 by omega,
        show 0 + k + 1 + 1 ≠ 0 by omega, ↓reduceIte, show 0 + k + 1 + 1 - 1 = k + 1 by omega,
        show 0 + k + 1 - 1 = k by omega, pow_succ]
      have := (pow_pos hβ0 k).ne'
      field_simp
      ring
  · -- the unconditional transversality condition
    have hint : ∀ t, ∫ ω, β ^ (t + 1) * wealth (fun _ _ => 1) (bubbleB β sbar σ)
        (fun _ _ => 1) (t + 1) ω ∂bubbleS.μ = β ^ (t + 1) * wBar β sbar σ := by
      intro t
      have := TreeBridge.integral_treeProb coinTree
        (fun ω => β ^ (t + 1) * wealth (fun _ _ => 1) (bubbleB β sbar σ) (fun _ _ => 1)
          (t + 1) ω)
      change _ = _ at this
      rw [show bubbleS.μ = (TreeBridge.treeProb coinTree : Measure (Bool × Bool)) from rfl,
        this]
      simp only [Fintype.sum_prod_type, Fintype.univ_bool, Finset.sum_insert,
        Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true, Finset.sum_singleton,
        wealth, bubbleB, bubbleW, wStar, wBar, firstHeads, coinTree, ↓reduceIte,
        show t + 1 ≠ 0 by omega, show t + 1 - 1 = t by omega, Bool.false_eq_true]
      have := (pow_pos hβ0 t).ne'
      field_simp
      ring
    have hlim : Tendsto (fun t => β ^ (t + 1) * wBar β sbar σ) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).comp
        (tendsto_add_atTop_nat 1)).mul_const (wBar β sbar σ)
      simpa using this
    rw [← tendsto_add_atTop_iff_nat 1]
    exact hlim.congr fun t => (hint t).symm

/-- **Cochrane (2023), (19.28), p. 449: the discounted debt does not vanish on any path.**
`β^{t+1}x_{t+1} = β^{t+1}x* + β(x̄_1 − x*)`, and `x̄_1 − x* = σ(1/2 − h)/(1 − β) ≠ 0`. -/
theorem bubble_path (β sbar σ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (t : ℕ)
    (ω : Bool × Bool) :
    β ^ (t + 1) * bubbleW β sbar σ (t + 1) ω =
        β ^ (t + 1) * wStar β sbar σ ω + β * (wBar β sbar σ - wStar β sbar σ ω) ∧
      wBar β sbar σ - wStar β sbar σ ω ≠ 0 := by
  have h1β : (1 - β) ≠ 0 := by linarith
  refine ⟨?_, ?_⟩
  · simp only [bubbleW, show t + 1 ≠ 0 by omega, ↓reduceIte, show t + 1 - 1 = t by omega]
    have := (pow_pos hβ0 t).ne'
    rw [pow_succ]
    field_simp
  · simp only [wBar, wStar, firstHeads]
    split_ifs
    · rw [ne_eq, div_sub_div_same, div_eq_zero_iff]; push Not
      exact ⟨by linarith, h1β⟩
    · rw [ne_eq, div_sub_div_same, div_eq_zero_iff]; push Not
      exact ⟨by linarith, h1β⟩

/-- **Cochrane (2023), (19.28), p. 449: the mean-zero bubble's real debt is unbounded.** -/
theorem bubble_unbounded {β sbar σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) :
    ¬ bubbleS.BddProc fun t => wealth (fun _ _ => 1) (bubbleB β sbar σ) (fun _ _ => 1) t := by
  rintro ⟨M, hM⟩
  set ω0 : Bool × Bool := (true, true)
  have hfull := TreeBridge.treeSystem_fullSupport coinTree
  have hpt : ∀ t, |bubbleW β sbar σ (t + 1) ω0| ≤ M := by
    intro t
    have h := bubbleS.le_of_ae_le hfull (f := fun ω => |wealth (fun _ _ => 1)
      (bubbleB β sbar σ) (fun _ _ => 1) (t + 1) ω|) (g := fun _ => M) (hM (t + 1))
    have := h ω0
    simpa [wealth, bubbleB] using this
  obtain ⟨hpath, hd⟩ := bubble_path β sbar σ hβ0 hβ1 hσ 0 ω0
  set d := wBar β sbar σ - wStar β sbar σ ω0
  set a := wStar β sbar σ ω0
  have hbd : ∀ t, β * |d| ≤ β ^ (t + 1) * (M + |a|) := by
    intro t
    have hp := (bubble_path β sbar σ hβ0 hβ1 hσ t ω0).1
    have hb : |β ^ (t + 1) * bubbleW β sbar σ (t + 1) ω0| ≤ β ^ (t + 1) * M := by
      rw [abs_mul, abs_of_pos (pow_pos hβ0 _)]
      exact mul_le_mul_of_nonneg_left (hpt t) (pow_pos hβ0 _).le
    have e : β * d = β ^ (t + 1) * bubbleW β sbar σ (t + 1) ω0 - β ^ (t + 1) * a := by
      rw [hp]; ring
    have h2 : β * |d| = |β * d| := by rw [abs_mul, abs_of_pos hβ0]
    rw [h2, e]
    have h3 : |β ^ (t + 1) * a| = β ^ (t + 1) * |a| := by
      rw [abs_mul, abs_of_pos (pow_pos hβ0 _)]
    calc |β ^ (t + 1) * bubbleW β sbar σ (t + 1) ω0 - β ^ (t + 1) * a|
        ≤ |β ^ (t + 1) * bubbleW β sbar σ (t + 1) ω0| + |β ^ (t + 1) * a| := abs_sub _ _
      _ ≤ β ^ (t + 1) * M + β ^ (t + 1) * |a| := by rw [h3]; linarith
      _ = β ^ (t + 1) * (M + |a|) := by ring
  have hlim : Tendsto (fun t => β ^ (t + 1) * (M + |a|)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).comp
      (tendsto_add_atTop_nat 1)).mul_const (M + |a|)
    simpa using this
  have hle : β * |d| ≤ 0 := ge_of_tendsto' hlim hbd
  have : 0 < β * |d| := mul_pos hβ0 (abs_pos.mpr hd)
  linarith

/-- **Cochrane (2023), pp. 453–454: coordination is not necessary under the unconditional
TVC (counterexample).** With `0 < β < 1`, `s̄ ≥ 0`, `σ > 0`, the surplus `shockSurplus s̄ σ` is
not coordinated with money (`CoordinatedM` fails), yet `bubble_eq` is a standard-price
`MeasMonetaryEq`, with unbounded real debt (`bubble_unbounded`). -/
theorem bubble_not_coordinated {β sbar σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs0 : 0 ≤ sbar)
    (hσ : 0 < σ) :
    MeasMonetaryEq bubbleS β 1 1 (stdPrice 1 1 fun _ _ => 1) (bubbleB β sbar σ)
        (fun _ _ => 1) (shockSurplus sbar σ) ∧
      ¬ CoordinatedM bubbleS β 1 1 (bubbleB β sbar σ 0) (fun _ _ => 1) (shockSurplus sbar σ) := by
  have h := bubble_eq (sbar := sbar) (σ := σ) hβ0 hβ1
  refine ⟨h, fun hc => ?_⟩
  have hsa : StronglyAdapted bubbleS.𝓕 (shockSurplus sbar σ) := by
    intro t
    rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht
      have e : shockSurplus sbar σ 0 = fun _ => sbar := by funext ω; simp [shockSurplus]
      rw [e]; exact stronglyMeasurable_const
    · exact firstCoin_meas ht fun ω ω' hh => by
        simp [shockSurplus, firstHeads, hh]
  have hsb : ∀ t, ∀ᵐ ω ∂bubbleS.μ, |shockSurplus sbar σ t ω| ≤ |sbar| + |σ| := fun t =>
    ae_of_all _ fun ω => by
      simp only [shockSurplus]
      split_ifs
      · linarith [abs_nonneg σ]
      · refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [abs_mul]
        have : |firstHeads ω| ≤ 1 := by simp only [firstHeads]; split_ifs <;> norm_num
        nlinarith [abs_nonneg σ]
  obtain ⟨Bs, hB0, hstd, hbdd⟩ :=
    (meas_std_exists_iff (S := bubbleS) (s := shockSurplus sbar σ) hβ0 hβ1 one_pos one_pos
      (fun _ _ => one_pos) (fun _ => stronglyMeasurable_const)
      (fun _ => Integrable.of_finite) (fun _ => Integrable.of_finite) hsa hsb
      (bubbleB β sbar σ 0)).2 hc
  have hw0 : 0 < bubbleW β sbar σ 0 (true, true) := by
    simp only [bubbleW, ↓reduceIte, wBar]
    have : 0 < (sbar + (1 - β) + σ / 2) / (1 - β) := div_pos (by linarith) (by linarith)
    nlinarith
  have hbu := meas_bonds_unique hβ0 one_pos one_pos h hstd (fun _ => Integrable.of_finite)
    hB0.symm (ae_of_all _ fun ω => by
      simp only [bubbleB, bubbleW, ↓reduceIte] at hw0 ⊢; linarith)
    (ae_of_all _ fun ω => Or.inr (by
      unfold stdBondPriceM
      have e : (fun _ : Bool × Bool => β * (1 : ℝ) / 1) = fun _ => β := by funext; ring
      rw [e, bubbleS.E_const]; exact hβ1))
  refine bubble_unbounded (sbar := sbar) (σ := σ) hβ0 hβ1 hσ ?_
  obtain ⟨M, hM⟩ := hbdd
  refine ⟨M, fun t => ?_⟩
  filter_upwards [hM t, hbu t] with ω h1 h2
  simpa [wealth, stdPrice, h2] using h1

end Cochrane.Monetarism.TidyR6ActiveFiscalBubble
