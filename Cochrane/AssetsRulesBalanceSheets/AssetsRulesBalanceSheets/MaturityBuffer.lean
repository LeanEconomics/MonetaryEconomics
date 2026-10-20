/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.ExpectationsFiniteTree
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Long versus short debt: the maturity buffer

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 8, §8.4 (pp. 249–254),
eq. (8.4) and the continuous-time present-value relation on p. 250.

## Main results

* `identity_84`: the weighted unexpected-inflation identity (8.4) is derived from the
  linearised identities (3.20) (with no growth term) and (3.21), which are taken as the model
  equations (they are approximations derived in Chapter 3). The real-rate terms in (8.4) are the
  news `ΔE_{t+1} r_{t+1+j}`, `j ≥ 1`, as in (3.22); (8.4) prints `r_{t+j}` (an index slip).
* `short_debt_identity` (`ω = 0`: the whole revision of the surplus present value is met by
  immediate inflation), `short_debt_constant_rates`, `matched_maturity_identity` (`ω = ρ`:
  real-rate news drops out), `rate_weights_antitone` (the weights `ρʲ − ωʲ` shrink as the
  maturity `ω` lengthens towards `ρ`).
* Continuous time, perfect foresight (p. 250): `matching_cancels` (if the real value of debt
  maturing at each date matches the surplus at that date, the present-value relation holds for
  every real-rate path) and `price_insulated` (the price level is then the same for every real
  rate path).
* The converse, in discrete time: `matching_necessary`, `price_insulated_only_if_matching`: if
  the price level is the same for every real-rate path (rates bounded below by some `r̲ > 0`),
  then debt maturity must match surpluses exactly.
* Survey E8.3: `matching_fails_under_uncertainty` — with stochastic real rates correlated with
  the price level, matching `B^{(t+τ)} E_t(1/P_{t+τ}) = s_{t+τ}` does not cancel the rates.
-/

namespace Cochrane.AssetsRulesBalanceSheets.MaturityBuffer

open Filter Topology MeasureTheory

/-! ### The identity (8.4) and its corollaries -/

/-- Cochrane (2023), eq. (3.20), p. 65, with no growth term, as used for (8.4), p. 250: the news
at `t + 1` in inflation `πN j = ΔE_{t+1} π_{t+1+j}`, surpluses `sN j = ΔE_{t+1} s_{t+1+j}`, real
returns `rN j = ΔE_{t+1} r_{t+1+j}` and the nominal bond return `rn = ΔE_{t+1} rⁿ_{t+1}` satisfy
`πN₀ − rn = −∑ ρʲ sN_j + ∑_{j ≥ 1} ρʲ rN_j`. -/
def Identity320 (ρ : ℝ) (πN sN rN : ℕ → ℝ) (rn : ℝ) : Prop :=
  πN 0 - rn = -(∑' j, ρ ^ j * sN j) + ∑' j, ρ ^ (j + 1) * rN (j + 1)

/-- Cochrane (2023), eq. (3.21), p. 65, as used for (8.4), p. 250: with geometric maturity `w`
(the book's `ω`), `rn = −∑_{j ≥ 1} wʲ (rN_j + πN_j)`. -/
def Identity321 (w : ℝ) (πN rN : ℕ → ℝ) (rn : ℝ) : Prop :=
  rn = -(∑' j, w ^ (j + 1) * (rN (j + 1) + πN (j + 1)))

/-- Cochrane (2023), eq. (8.4), p. 250 (derived from (3.20)–(3.21)):
`∑ wʲ ΔE π_{t+1+j} = −∑ ρʲ ΔE s_{t+1+j} + ∑_{j ≥ 1} (ρʲ − wʲ) ΔE r_{t+1+j}`, assuming the
real-rate and inflation news series weighted by `wʲ` and `ρʲ` are summable. -/
theorem identity_84 {ρ w rn : ℝ} {πN sN rN : ℕ → ℝ}
    (hs1 : Summable (fun j => w ^ (j + 1) * rN (j + 1)))
    (hs2 : Summable (fun j => w ^ (j + 1) * πN (j + 1)))
    (hs3 : Summable (fun j => ρ ^ (j + 1) * rN (j + 1)))
    (h320 : Identity320 ρ πN sN rN rn) (h321 : Identity321 w πN rN rn) :
    ∑' j, w ^ j * πN j =
      -(∑' j, ρ ^ j * sN j) + ∑' j, (ρ ^ (j + 1) - w ^ (j + 1)) * rN (j + 1) := by
  have hsum0 : Summable (fun j => w ^ j * πN j) :=
    (summable_nat_add_iff (f := fun j => w ^ j * πN j) 1).mp hs2
  have e1 : ∑' j, w ^ j * πN j = πN 0 + ∑' j, w ^ (j + 1) * πN (j + 1) := by
    rw [hsum0.tsum_eq_zero_add]
    simp
  have e2 : ∑' j, w ^ (j + 1) * (rN (j + 1) + πN (j + 1)) =
      ∑' j, w ^ (j + 1) * rN (j + 1) + ∑' j, w ^ (j + 1) * πN (j + 1) := by
    rw [← hs1.tsum_add hs2]
    exact tsum_congr fun j => by ring
  have e3 : ∑' j, (ρ ^ (j + 1) - w ^ (j + 1)) * rN (j + 1) =
      ∑' j, ρ ^ (j + 1) * rN (j + 1) - ∑' j, w ^ (j + 1) * rN (j + 1) := by
    rw [← hs3.tsum_sub hs1]
    exact tsum_congr fun j => by ring
  unfold Identity320 at h320
  unfold Identity321 at h321
  rw [e1, e3]
  rw [e2] at h321
  linarith

/-- Cochrane (2023), §8.4, p. 250: "If `ω = 0`, short-term debt, then the entire revision in the
present value of surpluses must be met by immediate inflation":
`ΔE π_{t+1} = −∑ ρʲ ΔE s_{t+1+j} + ∑_{j ≥ 1} ρʲ ΔE r_{t+1+j}`. -/
theorem short_debt_identity {ρ rn : ℝ} {πN sN rN : ℕ → ℝ} (h320 : Identity320 ρ πN sN rN rn)
    (h321 : Identity321 0 πN rN rn) :
    πN 0 = -(∑' j, ρ ^ j * sN j) + ∑' j, ρ ^ (j + 1) * rN (j + 1) := by
  unfold Identity321 at h321
  simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
    zero_pow, zero_mul, tsum_zero, neg_zero] at h321
  unfold Identity320 at h320
  rw [h321, sub_zero] at h320
  exact h320

/-- Cochrane (2023), §8.4, p. 250: with short-term debt and no real-rate news, unexpected
inflation is exactly minus the revision of the present value of surpluses. -/
theorem short_debt_constant_rates {ρ rn : ℝ} {πN sN : ℕ → ℝ}
    (h320 : Identity320 ρ πN sN (fun _ => 0) rn) (h321 : Identity321 0 πN (fun _ => 0) rn) :
    πN 0 = -(∑' j, ρ ^ j * sN j) := by
  have h := short_debt_identity h320 h321
  simpa using h

/-- Cochrane (2023), §8.4, p. 250: "In the limit `ω = ρ`, a real-rate increase has no
inflationary effect": with `w = ρ` the real-rate news drops out of (8.4),
`∑ ρʲ ΔE π_{t+1+j} = −∑ ρʲ ΔE s_{t+1+j}`. -/
theorem matched_maturity_identity {ρ rn : ℝ} {πN sN rN : ℕ → ℝ}
    (hs1 : Summable (fun j => ρ ^ (j + 1) * rN (j + 1)))
    (hs2 : Summable (fun j => ρ ^ (j + 1) * πN (j + 1)))
    (h320 : Identity320 ρ πN sN rN rn) (h321 : Identity321 ρ πN rN rn) :
    ∑' j, ρ ^ j * πN j = -(∑' j, ρ ^ j * sN j) := by
  rw [identity_84 hs1 hs2 hs1 h320 h321]
  simp

/-- Cochrane (2023), §8.4, p. 250: "The larger `ω`, the smaller the weights `ρʲ − ωʲ`": for
`0 ≤ w ≤ w' ≤ ρ` the real-rate weights satisfy `0 ≤ ρʲ − w'ʲ ≤ ρʲ − wʲ`. -/
theorem rate_weights_antitone {ρ w w' : ℝ} (hw : 0 ≤ w) (hww : w ≤ w') (hw'ρ : w' ≤ ρ)
    (j : ℕ) : 0 ≤ ρ ^ j - w' ^ j ∧ ρ ^ j - w' ^ j ≤ ρ ^ j - w ^ j := by
  have h1 : w' ^ j ≤ ρ ^ j := pow_le_pow_left₀ (hw.trans hww) hw'ρ j
  have h2 : w ^ j ≤ w' ^ j := pow_le_pow_left₀ hw hww j
  constructor <;> linarith

/-! ### Continuous-time matching (perfect foresight) -/

/-- Cochrane (2023), §8.4, p. 250: the continuous-time discount factor
`exp(−∫₀^τ r_{t+j} dj)` along a perfect-foresight real-rate path `r`. -/
noncomputable def cdisc (r : ℝ → ℝ) (τ : ℝ) : ℝ := Real.exp (-∫ u in (0 : ℝ)..τ, r u)

/-- Cochrane (2023), §8.4, p. 250: if the real value of the debt maturing at each date, `x(τ)`,
matches the surplus at that date, `s(τ)`, for all `τ ≥ 0`, then the present-value relation
`∫₀^∞ e^{−∫r} x = ∫₀^∞ e^{−∫r} s` holds for every real-rate path `r`: real rates cancel. -/
theorem matching_cancels {x s : ℝ → ℝ} (hm : ∀ τ, 0 ≤ τ → x τ = s τ) (r : ℝ → ℝ) :
    ∫ τ in Set.Ioi 0, cdisc r τ * x τ = ∫ τ in Set.Ioi 0, cdisc r τ * s τ := by
  refine setIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
  rw [hm τ (le_of_lt hτ)]

/-- Cochrane (2023), §8.4, p. 250 (price-level form): with nominal debt `B(τ)` maturing at
`t + τ`, the price path `P_{t+τ} = P_t Π(τ)` (relative path `Π` set by monetary policy), and
matching `B(τ)/Π(τ) = κ s(τ)` for `τ ≥ 0`, the valuation
`(1/P_t) ∫ e^{−∫r} B/Π = ∫ e^{−∫r} s` holds iff `P_t = κ`, for every real-rate path with
`∫ e^{−∫r} s ≠ 0`: the price level is insulated from real rates. -/
theorem price_insulated {Bm Pi s : ℝ → ℝ} {κ : ℝ} (hm : ∀ τ, 0 ≤ τ → Bm τ / Pi τ = κ * s τ)
    (r : ℝ → ℝ) (hS : ∫ τ in Set.Ioi 0, cdisc r τ * s τ ≠ 0) {P0 : ℝ} (hP0 : P0 ≠ 0) :
    (∫ τ in Set.Ioi 0, cdisc r τ * (Bm τ / Pi τ)) / P0 = ∫ τ in Set.Ioi 0, cdisc r τ * s τ ↔
      P0 = κ := by
  have hX : ∫ τ in Set.Ioi 0, cdisc r τ * (Bm τ / Pi τ) =
      κ * ∫ τ in Set.Ioi 0, cdisc r τ * s τ := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
    rw [hm τ (le_of_lt hτ)]
    ring
  rw [hX, div_eq_iff hP0]
  constructor
  · intro h
    have h2 : (κ - P0) * ∫ τ in Set.Ioi 0, cdisc r τ * s τ = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · exact absurd h3 hS
  · intro h
    rw [h]
    ring

/-! ### The converse in discrete time -/

/-- Cochrane (2023), §8.4, p. 250 (discrete-time analogue): the discount factor
`∏_{j<τ} (1 + r_j)⁻¹` along a real-rate path `r`. -/
noncomputable def ddisc (r : ℕ → ℝ) (τ : ℕ) : ℝ := ∏ j ∈ Finset.range τ, (1 + r j)⁻¹

/-- Cochrane (2023), §8.4, p. 250: along the constant path `r_j = r̲` the discount factor is
`(1 + r̲)⁻ᵗ`. -/
theorem ddisc_const (rl : ℝ) (τ : ℕ) : ddisc (fun _ => rl) τ = ((1 + rl)⁻¹) ^ τ := by
  simp [ddisc]

/-- Cochrane (2023), §8.4, p. 250: raising the rate of a single period `k` from `r̲` to `2r̲`
multiplies every later discount factor by `c = (1 + r̲)/(1 + 2r̲)`. -/
theorem ddisc_bump {rl : ℝ} (hrl : 0 < rl) (k τ : ℕ) :
    ddisc (fun j => if j = k then 2 * rl else rl) τ =
      ((1 + rl)⁻¹) ^ τ * (if k < τ then (1 + rl) / (1 + 2 * rl) else 1) := by
  have h1 : (1 + rl) ≠ 0 := by linarith
  have h2 : (1 + 2 * rl) ≠ 0 := by linarith
  induction τ with
  | zero => simp [ddisc]
  | succ τ ih =>
    rw [ddisc, Finset.prod_range_succ, ← ddisc, ih, pow_succ]
    by_cases hτk : τ = k
    · subst hτk
      simp only [lt_self_iff_false, ↓reduceIte, lt_add_iff_pos_right, Nat.lt_one_iff,
        mul_one]
      field_simp
    · simp only [hτk, ↓reduceIte]
      by_cases hk : k < τ
      · have hk' : k < τ + 1 := by omega
        simp only [hk, ↓reduceIte, hk']
        ring
      · have hk' : ¬ k < τ + 1 := by omega
        simp only [hk, ↓reduceIte, hk', mul_one]

/-- Cochrane (2023), §8.4, pp. 250–251 ("otherwise, the mismatch ... determines how the price
level reacts to real interest rates"), the converse of `matching_cancels` in discrete time: if a
bounded mismatch stream `y` has zero present value along every real-rate path with rates at
least `r̲ > 0`, then `y = 0`. -/
theorem matching_necessary {rl M : ℝ} (hrl : 0 < rl) {y : ℕ → ℝ} (hy : ∀ τ, |y τ| ≤ M)
    (h : ∀ r : ℕ → ℝ, (∀ j, rl ≤ r j) → ∑' τ, ddisc r τ * y τ = 0) : ∀ τ, y τ = 0 := by
  set q : ℝ := (1 + rl)⁻¹ with hq
  set c : ℝ := (1 + rl) / (1 + 2 * rl) with hc
  have hq0 : 0 < q := inv_pos.mpr (by linarith)
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hc0 : 0 ≤ c := div_nonneg (by linarith) (by linarith)
  have hc1 : c < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hgeo : Summable (fun τ : ℕ => q ^ τ * M) :=
    (summable_geometric_of_lt_one hq0.le hq1).mul_right M
  have hsum0 : Summable (fun τ => q ^ τ * y τ) :=
    Summable.of_norm_bounded hgeo fun τ => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hq0]
      exact mul_le_mul_of_nonneg_left (hy τ) (pow_nonneg hq0.le τ)
  -- base path
  have hbase : ∑' τ, q ^ τ * y τ = 0 := by
    have := h (fun _ => rl) (fun _ => le_rfl)
    simpa [ddisc_const, hq] using this
  -- head and tail decomposition
  set H : ℕ → ℝ := fun k => ∑ τ ∈ Finset.range (k + 1), q ^ τ * y τ with hH
  set T : ℕ → ℝ := fun k => ∑' τ, q ^ (τ + (k + 1)) * y (τ + (k + 1)) with hT
  have hHT : ∀ k, H k + T k = 0 := by
    intro k
    rw [← hbase]
    exact hsum0.sum_add_tsum_nat_add (k + 1)
  have hbumpH : ∀ k, H k + c * T k = 0 := by
    intro k
    have hk := h (fun j => if j = k then 2 * rl else rl) (fun j => by
      by_cases hj : j = k
      · simp only [hj, ↓reduceIte]; linarith
      · simp only [hj, ↓reduceIte, le_refl])
    have hform : (fun τ => ddisc (fun j => if j = k then 2 * rl else rl) τ * y τ) =
        fun τ => q ^ τ * y τ * (if k < τ then c else 1) := by
      funext τ
      rw [ddisc_bump hrl k τ]
      ring
    rw [hform] at hk
    have hsumk : Summable (fun τ => q ^ τ * y τ * (if k < τ then c else 1)) :=
      Summable.of_norm_bounded hgeo fun τ => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos hq0]
        have hif : |(if k < τ then c else 1)| ≤ 1 := by
          split_ifs
          · rw [abs_of_nonneg hc0]; exact hc1.le
          · simp
        calc q ^ τ * |y τ| * |(if k < τ then c else 1)| ≤ q ^ τ * M * 1 := by
              apply mul_le_mul (mul_le_mul_of_nonneg_left (hy τ) (pow_nonneg hq0.le τ)) hif
                (abs_nonneg _)
              exact mul_nonneg (pow_nonneg hq0.le τ) ((abs_nonneg _).trans (hy τ))
          _ = q ^ τ * M := mul_one _
    have hsplit := hsumk.sum_add_tsum_nat_add (k + 1)
    rw [hk] at hsplit
    have hhead : ∑ τ ∈ Finset.range (k + 1), q ^ τ * y τ * (if k < τ then c else 1) = H k := by
      refine Finset.sum_congr rfl fun τ hτ => ?_
      have : ¬ k < τ := by
        have := Finset.mem_range.mp hτ
        omega
      simp [this]
    have htail : ∑' τ, q ^ (τ + (k + 1)) * y (τ + (k + 1)) *
        (if k < τ + (k + 1) then c else 1) = c * T k := by
      rw [hT, ← tsum_mul_left]
      refine tsum_congr fun τ => ?_
      have : k < τ + (k + 1) := by omega
      simp only [this, ↓reduceIte]
      ring
    rw [hhead, htail] at hsplit
    exact hsplit
  have hHzero : ∀ k, H k = 0 := by
    intro k
    have h1 := hHT k
    have h2 := hbumpH k
    have hT0 : T k = 0 := by
      have : (1 - c) * T k = 0 := by linarith
      rcases mul_eq_zero.mp this with h3 | h3
      · linarith
      · exact h3
    linarith
  intro τ
  cases τ with
  | zero =>
    have := hHzero 0
    simpa [hH] using this
  | succ n =>
    have h1 := hHzero (n + 1)
    have h0 := hHzero n
    simp only [hH] at h1 h0
    rw [Finset.sum_range_succ, h0, zero_add] at h1
    rcases mul_eq_zero.mp h1 with h3 | h3
    · exact absurd h3 (pow_ne_zero _ hq0.ne')
    · exact h3

/-- Cochrane (2023), §8.4, pp. 250–251 (price-level form of the converse): with bounded debt
payoffs `x` (real value of debt maturing at `τ` per unit of the current price level) and
surpluses `s`, if the valuation `∑ d_τ x_τ / κ = ∑ d_τ s_τ` gives the same price level `κ ≠ 0`
along every real-rate path with rates at least `r̲ > 0`, then the maturity structure matches
the surpluses exactly, `x_τ = κ s_τ`. -/
theorem price_insulated_only_if_matching {rl Mx Ms κ : ℝ} (hrl : 0 < rl) (hκ : κ ≠ 0)
    {x s : ℕ → ℝ} (hx : ∀ τ, |x τ| ≤ Mx) (hs : ∀ τ, |s τ| ≤ Ms)
    (h : ∀ r : ℕ → ℝ, (∀ j, rl ≤ r j) →
      (∑' τ, ddisc r τ * x τ) / κ = ∑' τ, ddisc r τ * s τ) :
    ∀ τ, x τ = κ * s τ := by
  have hd : ∀ r : ℕ → ℝ, (∀ j, rl ≤ r j) → ∀ τ, 0 < ddisc r τ ∧ ddisc r τ ≤ 1 := by
    intro r hr τ
    constructor
    · exact Finset.prod_pos fun j _ => inv_pos.mpr (by linarith [hr j])
    · exact Finset.prod_le_one₀ (fun j _ => (inv_pos.mpr (by linarith [hr j])).le)
        fun j _ => inv_le_one_of_one_le₀ (by linarith [hr j])
  have hzero := matching_necessary hrl (y := fun τ => x τ - κ * s τ) (M := Mx + |κ| * Ms)
    (fun τ => by
      calc |x τ - κ * s τ| ≤ |x τ| + |κ * s τ| := abs_sub _ _
        _ ≤ Mx + |κ| * Ms := by
          rw [abs_mul]
          exact add_le_add (hx τ) (mul_le_mul_of_nonneg_left (hs τ) (abs_nonneg κ)))
    (fun r hr => by
      have hq1 : (1 + rl)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
      have hq0 : 0 ≤ (1 + rl)⁻¹ := (inv_pos.mpr (by linarith)).le
      have hdle : ∀ τ, ddisc r τ ≤ ((1 + rl)⁻¹) ^ τ := by
        intro τ
        have hc : ((1 + rl)⁻¹) ^ τ = ∏ j ∈ Finset.range τ, (1 + rl)⁻¹ := by simp
        rw [ddisc, hc]
        exact Finset.prod_le_prod₀ (fun j _ => (inv_pos.mpr (by linarith [hr j])).le)
          fun j _ => inv_anti₀ (by linarith) (by linarith [hr j])
      have hsx : Summable (fun τ => ddisc r τ * x τ) :=
        Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0 hq1).mul_right Mx)
          fun τ => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hd r hr τ).1]
            exact mul_le_mul (hdle τ) (hx τ) (abs_nonneg _) (pow_nonneg hq0 τ)
      have hss : Summable (fun τ => ddisc r τ * s τ) :=
        Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0 hq1).mul_right Ms)
          fun τ => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hd r hr τ).1]
            exact mul_le_mul (hdle τ) (hs τ) (abs_nonneg _) (pow_nonneg hq0 τ)
      have hval := h r hr
      rw [div_eq_iff hκ] at hval
      have e : (fun τ => ddisc r τ * (x τ - κ * s τ)) =
          fun τ => ddisc r τ * x τ - κ * (ddisc r τ * s τ) := by
        funext τ
        ring
      rw [e, hsx.tsum_sub (hss.mul_left κ), tsum_mul_left, hval]
      ring)
  intro τ
  have := hzero τ
  linarith

/-! ### Survey E8.3: matching is not enough under uncertainty -/

/-- Cochrane (2023), §8.4, p. 250 (survey E8.3): with stochastic real rates correlated with the
price level, matching the expected real payoff of maturing debt to the surplus does not cancel
the rates. In the coin-flip tree, a unit of debt maturing at `τ` with `E₀(1/P_τ) = 1 = s_τ`
(matching) and a positive discount factor `D` correlated with `1/P_τ` give
`E₀[D/P_τ] = 1 ≠ 3/4 = E₀[D s_τ]`. -/
theorem matching_fails_under_uncertainty :
    ∃ (D X : Bool × Bool → ℝ) (s : ℝ), (∀ ω, 0 < D ω) ∧
      ExpectationsFiniteTree.coinSystem.E 0 X = (fun _ => s) ∧
      ExpectationsFiniteTree.coinSystem.E 0 (D * X) ≠
        ExpectationsFiniteTree.coinSystem.E 0 (fun ω => D ω * s) := by
  set fh := ExpectationsFiniteTree.firstHeads with hfh
  set 𝔼 := ExpectationsFiniteTree.coinSystem with h𝔼
  have hE : ∀ ω, 𝔼.E 0 fh ω = 1 / 2 := ExpectationsFiniteTree.coinSystem_E0_firstHeads
  have hfh2 : ∀ ω, fh ω * fh ω = fh ω := by
    intro ω
    simp only [hfh, ExpectationsFiniteTree.firstHeads]
    split_ifs <;> norm_num
  refine ⟨fun ω => 1 / 2 + 1 / 2 * fh ω, (2 : ℝ) • fh, 1, fun ω => ?_, ?_, ?_⟩
  · have : 0 ≤ fh ω := by
      simp only [hfh, ExpectationsFiniteTree.firstHeads]
      split_ifs <;> norm_num
    linarith
  · funext ω
    rw [map_smul, Pi.smul_apply, hE ω, smul_eq_mul]
    norm_num
  · intro h
    have h1 : (fun ω => 1 / 2 + 1 / 2 * fh ω) * (2 : ℝ) • fh = (2 : ℝ) • fh := by
      funext ω
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      have := hfh2 ω
      linear_combination this
    have h2 : (fun ω => (1 / 2 + 1 / 2 * fh ω) * 1) =
        (fun _ => (1 / 2 : ℝ)) + (1 / 2 : ℝ) • fh := by
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [h1, h2, map_add, map_smul, map_smul, 𝔼.const] at h
    have h3 := congrFun h (true, true)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hE] at h3
    norm_num at h3

end Cochrane.AssetsRulesBalanceSheets.MaturityBuffer
