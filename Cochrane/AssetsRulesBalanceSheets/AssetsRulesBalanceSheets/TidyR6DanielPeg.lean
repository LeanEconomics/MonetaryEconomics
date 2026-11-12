/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.BigOperators.Field

/-!
# Daniel (2001a): the collapse of a peg with long-term debt

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 24, §24.3, p. 527 (Daniel
(2001a), "A Fiscal Theory of Currency Crises"), with the long-term-debt valuation equation of
Chapter 7 (eq. (7.2), p. 213, and Online Appendix §1.2.1, pp. 559–561). The book quotes Daniel:
without long-term government bonds the exchange-rate collapse must be instantaneous; with
long-term bonds the collapse can be delayed at the discretion of the monetary authority; fiscal
policy makes the crisis inevitable, monetary policy determines its timing and the size of the
depreciation.

## The model

A small open economy under perfect foresight with purchasing-power parity and foreign price level
`1`, so the price level `P_j` is the exchange rate. At date `0` the government owes nominal
zero-coupon debt `B_j ≥ 0` due at date `j` (bounded), and the present value of real primary
surpluses is `𝒮 > 0` (fiscal policy). With the real rate `1/β − 1` and the expectations hypothesis
the date-0 price of the bond due at `j` is `Q^{(j)} = βʲ P_0/P_j`, so the valuation equation (7.3)
is (7.2), `∑ⱼ βʲ B_j/P_j = 𝒮` (`Eqm`). Monetary policy chooses the price path among the
solutions (an interest-rate path, `1 + i_t = P_{t+1}/(β P_t)`, `rate`). The peg is `P_j = S̄`.

## Main results

* `peg_forever_iff`: the peg can be held forever iff `A/S̄ = 𝒮`, with `A = ∑ βʲ B_j`.
* `collapse_inevitable` (**fiscal policy makes the crisis inevitable**): if `A/S̄ > 𝒮`, every
  equilibrium depreciates above the peg at some date; `max_delay` (**within a finite window**):
  there is a date `T*` before which every equilibrium abandons the peg.
* `short_debt_instant` (**no long-term bonds: the collapse is instantaneous**): with one-period
  debt only, every equilibrium has `P_0 = B_0/𝒮 > S̄`.
* `peg_at_zero_iff` (**long-term bonds make delay possible**): an equilibrium holding the peg at
  date `0` exists iff either there is long-term debt and `B_0 < S̄ 𝒮`, or there is none and
  `B_0 = S̄ 𝒮`.
* `delayed_eqm`, `delayed_unique` (**monetary policy chooses the timing**): for every `T ≥ 1` with
  `∑_{j<T} βʲ B_j < S̄ 𝒮` and long-term debt outstanding past `T`, holding the peg through `T − 1`
  and devaluing once to `S_T = N_T/(𝒮 − H_T/S̄)` (`H_T`, `N_T` the discounted debt due before and
  from `T`) is an equilibrium, and the only one of this form; `devalue_gt_iff`: `S_T > S̄` iff the
  peg is unsupported; `rate_path`: the interest rate stays at the world rate except at `T − 1`.
* `devalue_mono` (**and the magnitude**): a later collapse means a larger devaluation,
  `S_T ≤ S_{T+1}`.
-/

namespace Cochrane.AssetsRulesBalanceSheets.TidyR6DanielPeg

open Filter Topology

/-- Cochrane (2023), eq. (7.2), p. 213, and §24.3, p. 527 (Daniel (2001a)): an equilibrium price
(exchange-rate) path — positive, and satisfying the valuation equation
`∑ⱼ βʲ B_j/P_j = 𝒮` with the date-0 maturity structure `B` and surplus present value `𝒮`. -/
def Eqm (β sv : ℝ) (B P : ℕ → ℝ) : Prop := (∀ j, 0 < P j) ∧ HasSum (fun j => β ^ j * B j / P j) sv

/-- Cochrane (2023), §24.3, p. 527: the discounted debt due before date `T`,
`H_T = ∑_{j<T} βʲ B_j`. -/
noncomputable def head (β : ℝ) (B : ℕ → ℝ) (T : ℕ) : ℝ := ∑ j ∈ Finset.range T, β ^ j * B j

/-- Cochrane (2023), §24.3, p. 527: the discounted debt due from date `T` on,
`N_T = ∑_{j ≥ T} βʲ B_j`. -/
noncomputable def tail (β : ℝ) (B : ℕ → ℝ) (T : ℕ) : ℝ := ∑' j, β ^ (j + T) * B (j + T)

/-- Cochrane (2023), §24.3, p. 527: the path that holds the peg `S̄` before `T` and is `S_T`
from `T` on. -/
noncomputable def pegPath (Sb ST : ℝ) (T j : ℕ) : ℝ := if j < T then Sb else ST

/-- Cochrane (2023), §24.3, p. 527: the devalued exchange rate `S_T = N_T/(𝒮 − H_T/S̄)`. -/
noncomputable def devalue (β sv Sb : ℝ) (B : ℕ → ℝ) (T : ℕ) : ℝ :=
  tail β B T / (sv - head β B T / Sb)

/-- Cochrane (2023), Chapter 7, p. 212 (`Q^{(t+1)}_t = β E_t(P_t/P_{t+1})`): the nominal interest
rate implied by the price path under perfect foresight, `1 + i_t = P_{t+1}/(β P_t)`. -/
noncomputable def rate (β : ℝ) (P : ℕ → ℝ) (t : ℕ) : ℝ := P (t + 1) / (β * P t) - 1

variable {β : ℝ} {B : ℕ → ℝ}

/-- Cochrane (2023), §24.3, p. 527: with `0 < β < 1` and `0 ≤ B_j ≤ K`, the discounted debt
`∑ βʲ B_j` converges. -/
theorem summable_debt (hβ0 : 0 < β) (hβ1 : β < 1) (hB0 : ∀ j, 0 ≤ B j) {K : ℝ}
    (hBK : ∀ j, B j ≤ K) : Summable (fun j => β ^ j * B j) :=
  ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right K).of_nonneg_of_le
    (fun j => mul_nonneg (pow_nonneg hβ0.le j) (hB0 j))
    fun j => mul_le_mul_of_nonneg_left (hBK j) (pow_nonneg hβ0.le j)

/-- Cochrane (2023), §24.3, p. 527: `A = H_T + N_T`. -/
theorem head_add_tail (hs : Summable (fun j => β ^ j * B j)) (T : ℕ) :
    head β B T + tail β B T = ∑' j, β ^ j * B j :=
  hs.sum_add_tsum_nat_add T

/-- Cochrane (2023), §24.3, p. 527: the tail is nonnegative and `N_{T+1} = N_T − β^T B_T`. -/
theorem tail_succ (hβ0 : 0 < β) (hB0 : ∀ j, 0 ≤ B j) (hs : Summable (fun j => β ^ j * B j))
    (T : ℕ) : 0 ≤ tail β B T ∧ tail β B (T + 1) = tail β B T - β ^ T * B T := by
  have h1 := head_add_tail hs T
  have h2 := head_add_tail hs (T + 1)
  refine ⟨tsum_nonneg fun j => mul_nonneg (pow_nonneg hβ0.le _) (hB0 _), ?_⟩
  simp only [head, Finset.sum_range_succ] at h1 h2
  linarith

/-- Cochrane (2023), §24.3, p. 527 (**a permanent peg**): the peg `P ≡ S̄ > 0` is an equilibrium iff
`A/S̄ = 𝒮`: the surpluses exactly support the debt at the pegged exchange rate. -/
theorem peg_forever_iff {sv Sb : ℝ} (hSb : 0 < Sb) (hs : Summable (fun j => β ^ j * B j)) :
    Eqm β sv B (fun _ => Sb) ↔ (∑' j, β ^ j * B j) / Sb = sv := by
  have h := hs.hasSum.div_const Sb
  constructor
  · rintro ⟨-, hE⟩
    exact h.unique hE
  · intro he
    exact ⟨fun _ => hSb, he ▸ h⟩

/-- Cochrane (2023), §24.3, p. 527 (**fiscal policy makes the crisis inevitable**): if the peg is
unsupported, `𝒮 < A/S̄`, then in every equilibrium the exchange rate exceeds the peg at some
date. -/
theorem collapse_inevitable {sv Sb : ℝ} (hβ0 : 0 < β) (hB0 : ∀ j, 0 ≤ B j)
    (hs : Summable (fun j => β ^ j * B j)) (hgap : sv < (∑' j, β ^ j * B j) / Sb) {P : ℕ → ℝ}
    (hE : Eqm β sv B P) : ∃ j, Sb < P j := by
  by_contra hcon
  push Not at hcon
  have hle : ∀ j, β ^ j * B j / Sb ≤ β ^ j * B j / P j := fun j =>
    div_le_div_of_nonneg_left (mul_nonneg (pow_nonneg hβ0.le j) (hB0 j)) (hE.1 j) (hcon j)
  have := hasSum_le hle (hs.hasSum.div_const Sb) hE.2
  linarith

/-- Cochrane (2023), §24.3, p. 527 (**the window is finite**): if the peg is unsupported,
`𝒮 < A/S̄`, there is a date `T*` such that every equilibrium leaves the peg before `T*`. -/
theorem max_delay {sv Sb : ℝ} (hβ0 : 0 < β) (hB0 : ∀ j, 0 ≤ B j)
    (hs : Summable (fun j => β ^ j * B j)) (hgap : sv < (∑' j, β ^ j * B j) / Sb) :
    ∃ Tstar : ℕ, ∀ P, Eqm β sv B P → ∃ j < Tstar, P j ≠ Sb := by
  have hlim : Tendsto (fun T => head β B T / Sb) atTop (𝓝 ((∑' j, β ^ j * B j) / Sb)) :=
    hs.hasSum.tendsto_sum_nat.div_const Sb
  obtain ⟨Tstar, hT⟩ := (hlim.eventually (lt_mem_nhds hgap)).exists
  refine ⟨Tstar, fun P hE => ?_⟩
  by_contra hcon
  push Not at hcon
  have hnn : ∀ j, 0 ≤ β ^ j * B j / P j := fun j =>
    div_nonneg (mul_nonneg (pow_nonneg hβ0.le j) (hB0 j)) (hE.1 j).le
  have h1 := sum_le_hasSum (Finset.range Tstar) (fun j _ => hnn j) hE.2
  have h2 : ∑ j ∈ Finset.range Tstar, β ^ j * B j / P j = head β B Tstar / Sb := by
    rw [head, Finset.sum_div]
    exact Finset.sum_congr rfl fun j hj => by rw [hcon j (Finset.mem_range.1 hj)]
  rw [h2] at h1
  linarith

/-- Cochrane (2023), §24.3, p. 527 (**without long-term bonds the collapse is instantaneous**): if
all debt is one-period (`B_j = 0` for `j ≥ 1`) and `B_0 > 0`, every equilibrium has
`P_0 = B_0/𝒮`; if the peg is unsupported (`𝒮 < B_0/S̄`), then `P_0 > S̄`: the peg breaks at
once. -/
theorem short_debt_instant {sv Sb : ℝ} (hSb : 0 < Sb) (hB1 : ∀ j, 1 ≤ j → B j = 0)
    (hBpos : 0 < B 0) (hsv : 0 < sv) (hgap : sv < B 0 / Sb) {P : ℕ → ℝ} (hE : Eqm β sv B P) :
    P 0 = B 0 / sv ∧ Sb < P 0 := by
  have hsum : HasSum (fun j => β ^ j * B j / P j) (B 0 / P 0) := by
    have := hasSum_ite_eq 0 (B 0 / P 0)
    convert this using 1
    funext j
    rcases j with _ | j
    · simp
    · simp [hB1 (j + 1) (by omega)]
  have he := hsum.unique hE.2
  have hP0 := hE.1 0
  have h1 : P 0 = B 0 / sv := by
    rw [← he]
    field_simp
  refine ⟨h1, ?_⟩
  rw [h1, lt_div_iff₀ hsv]
  rw [lt_div_iff₀ hSb] at hgap
  linarith

/-- Cochrane (2023), §24.3, p. 527 (**long-term bonds make delay possible**): with
`0 ≤ B_j ≤ K`, an equilibrium holding the peg at date `0` (`P_0 = S̄`) exists iff either there is
long-term debt (`N_1 > 0`) and `B_0 < S̄ 𝒮`, or there is none (`N_1 = 0`) and `B_0 = S̄ 𝒮`. -/
theorem peg_at_zero_iff {sv Sb K : ℝ} (hSb : 0 < Sb) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB0 : ∀ j, 0 ≤ B j) (hBK : ∀ j, B j ≤ K) :
    (∃ P, Eqm β sv B P ∧ P 0 = Sb) ↔
      (0 < tail β B 1 ∧ B 0 < Sb * sv) ∨ (tail β B 1 = 0 ∧ B 0 = Sb * sv) := by
  have hs := summable_debt hβ0 hβ1 hB0 hBK
  have hs1 : HasSum (fun j => β ^ (j + 1) * B (j + 1)) (tail β B 1) :=
    ((summable_nat_add_iff 1).2 hs).hasSum
  have hN0 := (tail_succ hβ0 hB0 hs 1).1
  constructor
  · rintro ⟨P, ⟨hP, hE⟩, hP0⟩
    have hsplit := (hasSum_nat_add_iff' 1).2 hE
    simp only [Finset.sum_range_one, pow_zero, one_mul, hP0] at hsplit
    have hnn : ∀ j, 0 ≤ β ^ (j + 1) * B (j + 1) / P (j + 1) := fun j =>
      div_nonneg (mul_nonneg (pow_nonneg hβ0.le _) (hB0 _)) (hP _).le
    rcases hN0.lt_or_eq with hN | hN
    · left
      refine ⟨hN, ?_⟩
      -- some term of the tail is positive, so the tail value is positive
      have hex : ∃ j, 0 < β ^ (j + 1) * B (j + 1) := by
        by_contra hc
        push Not at hc
        have : tail β B 1 ≤ 0 := hasSum_le (fun j => hc j) hs1 hasSum_zero
        linarith
      obtain ⟨j, hj⟩ := hex
      have hpos : 0 < sv - B 0 / Sb := by
        have h1 := le_hasSum hsplit j fun i _ => hnn i
        have h2 : 0 < β ^ (j + 1) * B (j + 1) / P (j + 1) := div_pos hj (hP _)
        linarith
      rw [sub_pos, div_lt_iff₀ hSb] at hpos
      linarith
    · right
      refine ⟨hN.symm, ?_⟩
      have hz : ∀ j, β ^ (j + 1) * B (j + 1) = 0 := by
        have := (hasSum_zero_iff_of_nonneg fun j => mul_nonneg (pow_nonneg hβ0.le (j + 1))
          (hB0 (j + 1))).1 (hN ▸ hs1)
        exact fun j => congrFun this j
      have hz' : (fun j => β ^ (j + 1) * B (j + 1) / P (j + 1)) = fun _ => 0 := by
        funext j
        rw [hz j, zero_div]
      rw [hz'] at hsplit
      have := hasSum_zero.unique hsplit
      field_simp at this
      linarith
  · rintro (⟨hN, hB⟩ | ⟨hN, hB⟩)
    · -- hold the peg at date 0, then a constant price
      set c := tail β B 1 / (sv - B 0 / Sb) with hc
      have hden : 0 < sv - B 0 / Sb := by
        rw [sub_pos, div_lt_iff₀ hSb]
        linarith
      have hc0 : 0 < c := div_pos hN hden
      refine ⟨fun j => if j = 0 then Sb else c,
        ⟨fun j => by dsimp only; split_ifs <;> assumption, ?_⟩, by simp⟩
      rw [← hasSum_nat_add_iff' 1]
      simp only [Finset.sum_range_one, pow_zero, one_mul, ↓reduceIte, Nat.add_one_ne_zero]
      have : sv - B 0 / Sb = tail β B 1 / c := by
        rw [hc]
        field_simp
      rw [this]
      exact hs1.div_const c
    · refine ⟨fun _ => Sb, ⟨fun _ => hSb, ?_⟩, rfl⟩
      rw [← hasSum_nat_add_iff' 1]
      simp only [Finset.sum_range_one, pow_zero, one_mul]
      have hz : ∀ j, β ^ (j + 1) * B (j + 1) = 0 := by
        have := (hasSum_zero_iff_of_nonneg fun j => mul_nonneg (pow_nonneg hβ0.le (j + 1))
          (hB0 (j + 1))).1 (hN ▸ hs1)
        exact fun j => congrFun this j
      have e : (fun j => β ^ (j + 1) * B (j + 1) / Sb) = fun _ => 0 := by
        funext j
        rw [hz j, zero_div]
      rw [e, hB, mul_div_cancel_left₀ sv hSb.ne', sub_self]
      exact hasSum_zero

/-- Cochrane (2023), §24.3, p. 527 (**the delayed collapse**): for `T`, if
`H_T = ∑_{j<T} βʲ B_j < S̄ 𝒮` and long-term debt is outstanding past `T` (`N_T > 0`), the path
holding the peg `S̄` before `T` and equal to `S_T = N_T/(𝒮 − H_T/S̄)` from `T` on is an
equilibrium. -/
theorem delayed_eqm {sv Sb : ℝ} (hSb : 0 < Sb) (hs : Summable (fun j => β ^ j * B j)) {T : ℕ}
    (hH : head β B T < Sb * sv) (hN : 0 < tail β B T) :
    Eqm β sv B (pegPath Sb (devalue β sv Sb B T) T) := by
  have hden : 0 < sv - head β B T / Sb := by
    rw [sub_pos, div_lt_iff₀ hSb]
    linarith
  have hST : 0 < devalue β sv Sb B T := div_pos hN hden
  refine ⟨fun j => by unfold pegPath; split_ifs <;> assumption, ?_⟩
  rw [← hasSum_nat_add_iff' T]
  have e1 : ∑ i ∈ Finset.range T, β ^ i * B i / pegPath Sb (devalue β sv Sb B T) T i =
      head β B T / Sb := by
    rw [head, Finset.sum_div]
    exact Finset.sum_congr rfl fun i hi => by
      simp [pegPath, Finset.mem_range.1 hi]
  have e2 : (fun n => β ^ (n + T) * B (n + T) / pegPath Sb (devalue β sv Sb B T) T (n + T)) =
      fun n => β ^ (n + T) * B (n + T) / devalue β sv Sb B T := by
    funext n
    have : ¬ n + T < T := by omega
    simp [pegPath, this]
  rw [e1, e2]
  have e3 : sv - head β B T / Sb = tail β B T / devalue β sv Sb B T := by
    unfold devalue
    field_simp
  rw [e3]
  exact ((summable_nat_add_iff T).2 hs).hasSum.div_const _

/-- Cochrane (2023), §24.3, p. 527 (**the size of the devaluation is determined by the timing**):
if a path holding the peg before `T` and constant at `c` from `T` on is an equilibrium and
`N_T > 0`, then `c = S_T`. -/
theorem delayed_unique {sv Sb c : ℝ} (hs : Summable (fun j => β ^ j * B j)) {T : ℕ}
    (hN : 0 < tail β B T) (hE : Eqm β sv B (pegPath Sb c T)) : c = devalue β sv Sb B T := by
  have hc : 0 < c := by
    have := hE.1 T
    simpa [pegPath] using this
  have h := (hasSum_nat_add_iff' T).2 hE.2
  have e1 : ∑ i ∈ Finset.range T, β ^ i * B i / pegPath Sb c T i = head β B T / Sb := by
    rw [head, Finset.sum_div]
    exact Finset.sum_congr rfl fun i hi => by
      simp [pegPath, Finset.mem_range.1 hi]
  have e2 : (fun n => β ^ (n + T) * B (n + T) / pegPath Sb c T (n + T)) =
      fun n => β ^ (n + T) * B (n + T) / c := by
    funext n
    have : ¬ n + T < T := by omega
    simp [pegPath, this]
  rw [e1, e2] at h
  have h2 := ((summable_nat_add_iff T).2 hs).hasSum.div_const c
  have he : tail β B T / c = sv - head β B T / Sb := h2.unique h
  have hden : sv - head β B T / Sb ≠ 0 := by
    rw [← he]
    exact (div_pos hN hc).ne'
  unfold devalue
  rw [← he]
  field_simp

/-- Cochrane (2023), §24.3, p. 527: the delayed devaluation exceeds the peg, `S_T > S̄`, iff the
peg is unsupported, `S̄ 𝒮 < A` (given `H_T < S̄ 𝒮`). -/
theorem devalue_gt_iff {sv Sb : ℝ} (hSb : 0 < Sb) (hs : Summable (fun j => β ^ j * B j))
    {T : ℕ} (hH : head β B T < Sb * sv) :
    Sb < devalue β sv Sb B T ↔ Sb * sv < ∑' j, β ^ j * B j := by
  have hA := head_add_tail hs T
  have hden : 0 < sv - head β B T / Sb := by
    rw [sub_pos, div_lt_iff₀ hSb]
    linarith
  unfold devalue
  rw [lt_div_iff₀ hden]
  have e : Sb * (sv - head β B T / Sb) = Sb * sv - head β B T := by
    field_simp
  rw [e]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §24.3, p. 527 (**a later collapse means a larger devaluation**): if the peg
is unsupported (`S̄ 𝒮 < A`) and `H_{T+1} < S̄ 𝒮` (so both collapse dates are feasible), then
`S_T ≤ S_{T+1}`. -/
theorem devalue_mono {sv Sb : ℝ} (hSb : 0 < Sb) (hβ0 : 0 < β) (hB0 : ∀ j, 0 ≤ B j)
    (hs : Summable (fun j => β ^ j * B j)) (hgap : Sb * sv < ∑' j, β ^ j * B j) {T : ℕ}
    (hH : head β B (T + 1) < Sb * sv) :
    devalue β sv Sb B T ≤ devalue β sv Sb B (T + 1) := by
  set A := ∑' j, β ^ j * B j with hAdef
  set G := A - Sb * sv with hG
  have hG0 : 0 < G := by linarith
  have hA0 := head_add_tail hs T
  have hA1 := head_add_tail hs (T + 1)
  obtain ⟨-, hts⟩ := tail_succ hβ0 hB0 hs T
  have hbT : 0 ≤ β ^ T * B T := mul_nonneg (pow_nonneg hβ0.le T) (hB0 T)
  -- `S_T = S̄ N_T/(N_T − G)` with `N_T > G`
  have hform : ∀ k, head β B k < Sb * sv →
      devalue β sv Sb B k = Sb * tail β B k / (tail β B k - G) := fun k hk => by
    have hk' := head_add_tail hs k
    unfold devalue
    have h1 : sv - head β B k / Sb = (tail β B k - G) / Sb := by
      rw [hG]
      field_simp
      linarith
    rw [h1]
    have : tail β B k - G ≠ 0 := by
      have : tail β B k - G = Sb * sv - head β B k := by rw [hG]; linarith
      rw [this]
      linarith
    field_simp
  have hH0 : head β B T < Sb * sv := by
    have : head β B (T + 1) = head β B T + β ^ T * B T := by
      simp [head, Finset.sum_range_succ]
    linarith
  rw [hform T hH0, hform (T + 1) hH]
  have hd1 : 0 < tail β B (T + 1) - G := by linarith
  have hd0 : 0 < tail β B T - G := by linarith
  rw [div_le_div_iff₀ hd0 hd1]
  have key : Sb * G * tail β B (T + 1) = Sb * G * tail β B T - Sb * G * (β ^ T * B T) := by
    rw [hts]
    ring
  nlinarith [key, mul_nonneg (mul_nonneg hSb.le hG0.le) hbT]

/-- Cochrane (2023), Chapter 7, p. 212, and §24.3, p. 527: along the delayed-collapse path the
nominal interest rate equals the world rate `1/β − 1` at every date except `T − 1`, where it is
`S_T/(β S̄) − 1` (uncovered interest parity: the expected devaluation is priced one period
ahead). -/
theorem rate_path {Sb ST : ℝ} (hβ0 : 0 < β) (hSb : 0 < Sb) (hST : 0 < ST) {T : ℕ} (t : ℕ) :
    rate β (pegPath Sb ST T) t =
      if t + 1 = T then ST / (β * Sb) - 1 else 1 / β - 1 := by
  unfold rate pegPath
  by_cases h1 : t + 1 = T
  · subst h1
    simp
  · simp only [h1, ↓reduceIte]
    by_cases h2 : t + 1 < T
    · have h3 : t < T := by omega
      simp only [h2, h3, ↓reduceIte]
      field_simp
    · have h3 : ¬ t < T := by omega
      simp only [h2, h3, ↓reduceIte]
      field_simp

end Cochrane.AssetsRulesBalanceSheets.TidyR6DanielPeg
