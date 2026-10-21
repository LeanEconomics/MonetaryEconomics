/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.MaturityStructure
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Forward guidance and bond-price targets

Cochrane (2023), §7.1, pp. 213–215 (equation (7.3) and the bond-price display on p. 214) and
Online Appendix §A1.2.1, pp. 559–561 (the geometric-maturity forward-guidance formulas behind
Figure 7.1, discrete and continuous time, and the steady-state sales).

At date 0 the government announces that the one-period rate, `r` until now, rises to `i` from
date `T` on. Bonds maturing at `j ≤ T` keep their prices `(1+r)^{-j}`, bonds maturing at `T + j`
are priced `((1+r)^T (1+i)^j)^{-1}`. With surpluses unchanged, the valuation equation (7.3)
`(∑_j Q_0^{(j)} B_{−1}^{(j)}) / P_0 = E_0 ∑_j β^j s_j` determines `P_0`.

## Main results

* `fgPrice_of_le`, `fgPrice_add`, `inv_pow_lt_fgPrice`, `fgPrice_lt`: the bond-price display on
  p. 214, including `Q_0^{(T+j)} > (1+i)^{-(T+j)}`.
* `fgPrice_mono`: the bond prices rise with the announcement horizon `T`.
* `fgPath_unique`, `fgPath_eq_of_le`, `fgPath_jump`, `fgPrice_eq_path`: perfect-foresight price
  path; the price level is flat until `T`, there is no second jump at `T`, and inflation starts
  only after the rate rises; the bond prices are `β^j P_0/P_j`.
* `valuation_iff`: (7.3) pins down `P_0` from bond prices (or bond-price targets).
* `priceLevel_fg_of_le`: forward guidance beyond the longest maturity `k` (`T ≥ k`, sharper than
  the book's `T > k`) leaves `P_0` unchanged; `priceLevel_fg_lt` shows `T ≥ k` is sharp.
* `priceLevel_mono`, `priceLevel_immediate_le`: forward guidance has a smaller effect than the
  same immediate rise, and the effect falls with the horizon.
* `hasSum_fg_geometric`, `fg_jump_geometric`: Online Appendix p. 560, the discrete geometric
  forward-guidance formula `P_0/P − 1 = (ω/(1+r))^T [(1+i)(1+r−ω)/((1+r)(1+i−ω)) − 1]`;
  `fg_jump_immediate` is (1.16), `perpetuity_ratio_bounds` corrects the "25%" of p. 560.
* `fgJump_*`: the jump is negative, shrinks with `T`, tends to zero, and grows with `ω`.
* `integral_cfg`, `cfg_jump`, `cfgJump_*`: the continuous-time formula
  `P_0/P − 1 = e^{−(r+ϖ)T}((r+ϖ)/(i+ϖ) − 1)` (p. 561) with its comparative statics.
* `steady_sales`: the sales that maintain a geometric maturity structure (p. 561).
-/

namespace Cochrane.LongTermDebtDynamics.ForwardGuidance

open Filter Topology MeasureTheory

/-! ### Bond prices under forward guidance -/

/-- Cochrane (2023), §7.1, p. 214: the date-0 price of a zero-coupon bond maturing at `j` when the
one-period rate is `r` before date `T` and `i` from `T` on:
`Q_0^{(j)} = ((1+r)^{min(j,T)} (1+i)^{j−T})^{-1}`. -/
noncomputable def fgPrice (r i : ℝ) (T j : ℕ) : ℝ := ((1 + r) ^ min j T * (1 + i) ^ (j - T))⁻¹

/-- Cochrane (2023), §7.1, p. 214: bonds maturing at `j ≤ T` are unaffected by the announcement,
`Q_0^{(j)} = (1+r)^{-j}`. -/
theorem fgPrice_of_le (r i : ℝ) {T j : ℕ} (hj : j ≤ T) : fgPrice r i T j = ((1 + r) ^ j)⁻¹ := by
  rw [fgPrice, min_eq_left hj, Nat.sub_eq_zero_of_le hj, pow_zero, mul_one]

/-- Cochrane (2023), §7.1, p. 214: `Q_0^{(T+j)} = ((1+r)^T (1+i)^j)^{-1}`. -/
theorem fgPrice_add (r i : ℝ) (T j : ℕ) :
    fgPrice r i T (T + j) = ((1 + r) ^ T * (1 + i) ^ j)⁻¹ := by
  rw [fgPrice, min_eq_right (Nat.le_add_right T j), Nat.add_sub_cancel_left]

/-- Cochrane (2023), §7.1, p. 214: with no rate change the forward-guidance price is the
steady-state price `(1+r)^{-j}`. -/
theorem fgPrice_same (r : ℝ) (T j : ℕ) : fgPrice r r T j = ((1 + r) ^ j)⁻¹ := by
  rw [fgPrice, ← pow_add]
  congr 2
  omega

/-- Cochrane (2023), §7.1, p. 214: for `−1 < r < i` and `T ≥ 1`, the forward-guidance price
exceeds the price under an immediate rise, `Q_0^{(T+j)} > (1+i)^{-(T+j)}`. -/
theorem inv_pow_lt_fgPrice {r i : ℝ} (hr : -1 < r) (hri : r < i) {T : ℕ} (hT : 1 ≤ T)
    (j : ℕ) : ((1 + i) ^ (T + j))⁻¹ < fgPrice r i T (T + j) := by
  rw [fgPrice_add, pow_add]
  have h1 : 0 < 1 + r := by linarith
  have h2 : 0 < 1 + i := by linarith
  apply inv_strictAnti₀ (mul_pos (pow_pos h1 _) (pow_pos h2 _))
  have : (1 + r) ^ T < (1 + i) ^ T := pow_lt_pow_left₀ (by linarith) h1.le (by omega)
  exact mul_lt_mul_of_pos_right this (by positivity)

/-- Cochrane (2023), §7.1, p. 214: bonds maturing after `T` fall in price,
`Q_0^{(j)} < (1+r)^{-j}` for `j > T` and `−1 < r < i`. -/
theorem fgPrice_lt {r i : ℝ} (hr : -1 < r) (hri : r < i) {T j : ℕ} (hj : T < j) :
    fgPrice r i T j < ((1 + r) ^ j)⁻¹ := by
  obtain ⟨k, rfl⟩ : ∃ k, j = T + (k + 1) := ⟨j - T - 1, by omega⟩
  rw [fgPrice_add, show (1 + r) ^ (T + (k + 1)) = (1 + r) ^ T * (1 + r) ^ (k + 1) from
    pow_add _ _ _]
  have h1 : 0 < 1 + r := by linarith
  have h2 : 0 < 1 + i := by linarith
  apply inv_strictAnti₀ (mul_pos (pow_pos h1 _) (pow_pos h1 _))
  have : (1 + r) ^ (k + 1) < (1 + i) ^ (k + 1) := pow_lt_pow_left₀ (by linarith) h1.le (by omega)
  exact mul_lt_mul_of_pos_left this (by positivity)

/-- Cochrane (2023), §7.1, p. 213: bond prices rise with the announcement horizon:
`T ↦ Q_0^{(j)}(T)` is monotone for `−1 < r ≤ i`. -/
theorem fgPrice_mono {r i : ℝ} (hr : -1 < r) (hri : r ≤ i) (j : ℕ) :
    Monotone (fun T => fgPrice r i T j) := by
  have h1 : 0 < 1 + r := by linarith
  have h2 : 0 < 1 + i := by linarith
  refine monotone_nat_of_le_succ fun T => ?_
  change fgPrice r i T j ≤ fgPrice r i (T + 1) j
  rcases le_or_gt j T with hj | hj
  · rw [fgPrice_of_le r i hj, fgPrice_of_le r i (Nat.le_succ_of_le hj)]
  · obtain ⟨k, rfl⟩ : ∃ k, j = T + 1 + k := ⟨j - T - 1, by omega⟩
    rw [fgPrice_add, show T + 1 + k = T + (k + 1) by omega, fgPrice_add]
    apply inv_anti₀ (mul_pos (pow_pos h1 _) (pow_pos h2 _))
    rw [pow_succ, pow_succ]
    have : (1 + r) ^ T * (1 + i) ^ k * (1 + r) ≤ (1 + r) ^ T * (1 + i) ^ k * (1 + i) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_pos (pow_pos h1 _) (pow_pos h2 _)).le
    linarith [this]

/-! ### The perfect-foresight price path -/

/-- Cochrane (2023), §7.1, p. 213: the announced one-period rate path, `r` before `T`, `i` from
`T` on. -/
noncomputable def fgRate (r i : ℝ) (T t : ℕ) : ℝ := if t < T then r else i

/-- Cochrane (2023), §7.1, pp. 214–215: the price path after the announcement,
`P_t = P_0 ((1+i)/(1+r))^{t−T}` (flat until `T`, inflation `i − r` thereafter). -/
noncomputable def fgPath (P0 r i : ℝ) (T t : ℕ) : ℝ := P0 * ((1 + i) / (1 + r)) ^ (t - T)

/-- Cochrane (2023), §7.1, p. 215: the path satisfies the Fisher relation of the constant real
rate model, `P_{t+1} = P_t (1 + i_t)/(1 + r)` (i.e. `1 + i_t = β^{-1} P_{t+1}/P_t`). -/
theorem fgPath_succ (P0 r i : ℝ) (hr : -1 < r) (T t : ℕ) :
    fgPath P0 r i T (t + 1) = fgPath P0 r i T t * (1 + fgRate r i T t) / (1 + r) := by
  have h1 : (1 + r) ≠ 0 := by linarith
  unfold fgPath fgRate
  by_cases ht : t < T
  · simp only [ht, ↓reduceIte, Nat.sub_eq_zero_of_le (show t + 1 ≤ T by omega),
      Nat.sub_eq_zero_of_le ht.le]
    field_simp
  · simp only [ht, ↓reduceIte, show t + 1 - T = t - T + 1 by omega, pow_succ]
    field_simp

/-- Cochrane (2023), §7.1, p. 215: under perfect foresight, the Fisher relation and `P_0` determine
the whole path: any path with `P_{t+1} = P_t(1+i_t)/(1+r)` is `fgPath`. -/
theorem fgPath_unique {P : ℕ → ℝ} {r i : ℝ} (hr : -1 < r) {T : ℕ}
    (hP : ∀ t, P (t + 1) = P t * (1 + fgRate r i T t) / (1 + r)) (t : ℕ) :
    P t = fgPath (P 0) r i T t := by
  induction t with
  | zero => simp [fgPath]
  | succ t ih => rw [hP t, ih, fgPath_succ (P 0) r i hr]

/-- Cochrane (2023), §7.1, pp. 214–215: the price level stays at its new level `P_0` up to and
including the date `T` at which the rate rises: there is no second jump. -/
theorem fgPath_eq_of_le (P0 r i : ℝ) {T t : ℕ} (ht : t ≤ T) : fgPath P0 r i T t = P0 := by
  simp [fgPath, Nat.sub_eq_zero_of_le ht]

/-- Cochrane (2023), §7.1, p. 215: inflation starts when the interest rate actually rises,
`P_{T+1} = P_T (1+i)/(1+r) > P_T` for `P_0 > 0` and `−1 < r < i`. -/
theorem fgPath_jump {P0 r i : ℝ} (hP0 : 0 < P0) (hr : -1 < r) (hri : r < i) (T : ℕ) :
    fgPath P0 r i T T < fgPath P0 r i T (T + 1) := by
  have h1 : 0 < 1 + r := by linarith
  simp only [fgPath, Nat.sub_self, pow_zero, mul_one, show T + 1 - T = 1 by omega, pow_one]
  rw [lt_mul_iff_one_lt_right hP0, one_lt_div h1]
  linarith

/-- Cochrane (2023), §7.1, p. 214: the forward-guidance bond prices are the perfect-foresight
prices `Q_0^{(j)} = β^j P_0/P_j` with `β = 1/(1+r)` along the path `fgPath`. -/
theorem fgPrice_eq_path {P0 r i : ℝ} (hP0 : P0 ≠ 0) (hr : -1 < r) (hi : -1 < i) (T j : ℕ) :
    fgPrice r i T j = ((1 + r)⁻¹) ^ j * (P0 / fgPath P0 r i T j) := by
  have h1 : (1 + r) ≠ 0 := by linarith
  have h2 : (1 + i) ≠ 0 := by linarith
  have hj : (1 + r) ^ j = (1 + r) ^ min j T * (1 + r) ^ (j - T) := by
    rw [← pow_add]; congr 1; omega
  rw [fgPrice, fgPath, div_mul_cancel_left₀ hP0, div_pow, inv_div, inv_pow, hj]
  have h3 : (1 + r) ^ (j - T) ≠ 0 := pow_ne_zero _ h1
  have h4 : (1 + r) ^ min j T ≠ 0 := pow_ne_zero _ h1
  have h5 : (1 + i) ^ (j - T) ≠ 0 := pow_ne_zero _ h2
  field_simp

/-! ### The valuation equation (7.3) -/

/-- Cochrane (2023), eq. (7.3), p. 214: the price level implied by the valuation equation with
bond prices `Q`, outstanding debt `B_{−1}^{(j)}` (maturities `j ≤ k`) and present value of
surpluses `S`: `P_0 = (∑_{j ≤ k} Q_0^{(j)} B_{−1}^{(j)}) / S`. -/
noncomputable def priceLevel (Q B : ℕ → ℝ) (k : ℕ) (S : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (k + 1), Q j * B j) / S

/-- Cochrane (2023), eq. (7.3), p. 214 and p. 215: the valuation equation determines the price
level from bond prices (or from bond-price targets): `(∑ Q B)/P_0 = S` iff `P_0 = priceLevel`. -/
theorem valuation_iff (Q B : ℕ → ℝ) (k : ℕ) {S P0 : ℝ} (hS : 0 < S) (hP0 : 0 < P0) :
    (∑ j ∈ Finset.range (k + 1), Q j * B j) / P0 = S ↔ P0 = priceLevel Q B k S := by
  rw [priceLevel, div_eq_iff hP0.ne', eq_div_iff hS.ne']
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §7.1, p. 214: if the announcement horizon reaches the longest outstanding
maturity, `T ≥ k`, the price level does not move. (The book says `T > k`; `T ≥ k` suffices.) -/
theorem priceLevel_fg_of_le (r i : ℝ) (B : ℕ → ℝ) {k T : ℕ} (hkT : k ≤ T) (S : ℝ) :
    priceLevel (fgPrice r i T) B k S = priceLevel (fgPrice r r T) B k S := by
  unfold priceLevel
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ T := by have := Finset.mem_range.mp hj; omega
  rw [fgPrice_of_le r i hj', fgPrice_same]

/-- Cochrane (2023), §7.1, p. 214: `T ≥ k` is sharp: if some maturity `j` with `T < j ≤ k` is
outstanding (`B_{−1}^{(j)} > 0`, all positions nonnegative), forward guidance lowers `P_0`. -/
theorem priceLevel_fg_lt {r i : ℝ} (hr : -1 < r) (hri : r < i) {B : ℕ → ℝ}
    (hB : ∀ j, 0 ≤ B j) {k T j₀ : ℕ} (hTj : T < j₀) (hjk : j₀ ≤ k) (hBj : 0 < B j₀)
    {S : ℝ} (hS : 0 < S) :
    priceLevel (fgPrice r i T) B k S < priceLevel (fgPrice r r T) B k S := by
  unfold priceLevel
  apply div_lt_div_of_pos_right _ hS
  apply Finset.sum_lt_sum
  · intro j _
    rw [fgPrice_same]
    rcases le_or_gt j T with h | h
    · rw [fgPrice_of_le r i h]
    · exact mul_le_mul_of_nonneg_right (fgPrice_lt hr hri h).le (hB j)
  · refine ⟨j₀, Finset.mem_range.mpr (by omega), ?_⟩
    rw [fgPrice_same]
    exact mul_lt_mul_of_pos_right (fgPrice_lt hr hri hTj) hBj

/-- Cochrane (2023), §7.1, p. 213: the effect of forward guidance falls with the announcement
horizon: with nonnegative positions `P_0(T)` is monotone in `T`. -/
theorem priceLevel_mono {r i : ℝ} (hr : -1 < r) (hri : r ≤ i) {B : ℕ → ℝ} (hB : ∀ j, 0 ≤ B j)
    (k : ℕ) {S : ℝ} (hS : 0 < S) : Monotone (fun T => priceLevel (fgPrice r i T) B k S) := by
  intro T T' hTT'
  unfold priceLevel
  apply div_le_div_of_nonneg_right _ hS.le
  exact Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_right (fgPrice_mono hr hri j hTT') (hB j)

/-- Cochrane (2023), §7.1, p. 213 (first bullet): forward guidance has less effect than the same
immediate rise: the immediate rise (`T = 0`) gives the lowest price level. -/
theorem priceLevel_immediate_le {r i : ℝ} (hr : -1 < r) (hri : r ≤ i) {B : ℕ → ℝ}
    (hB : ∀ j, 0 ≤ B j) (k T : ℕ) {S : ℝ} (hS : 0 < S) :
    priceLevel (fgPrice r i 0) B k S ≤ priceLevel (fgPrice r i T) B k S :=
  priceLevel_mono hr hri hB k hS (Nat.zero_le T)

/-! ### Geometric maturity structure, discrete time (Online Appendix A1.2.1) -/

/-- Cochrane (2023), Online Appendix p. 560: the valuation sum `∑_j Q_0^{(j)} ω^j` under forward
guidance with a geometric maturity structure, in closed form with `a = ω/(1+r)`, `b = ω/(1+i)`. -/
noncomputable def fgSum (r i ω : ℝ) (T : ℕ) : ℝ :=
  (1 - (ω / (1 + r)) ^ (T + 1)) / (1 - ω / (1 + r)) +
    (ω / (1 + r)) ^ T * ((ω / (1 + i)) / (1 - ω / (1 + i)))

/-- Cochrane (2023), Online Appendix p. 560: `∑_j Q_0^{(j)} ω^j = fgSum` as a genuine convergent
series, for `0 ≤ ω < 1 + r`, `−1 < r ≤ i`. -/
theorem hasSum_fg_geometric {r i ω : ℝ} (hr : -1 < r) (hri : r ≤ i) (hω0 : 0 ≤ ω)
    (hω1 : ω < 1 + r) (T : ℕ) :
    HasSum (fun j => fgPrice r i T j * ω ^ j) (fgSum r i ω T) := by
  have h1 : 0 < 1 + r := by linarith
  have h2 : 0 < 1 + i := by linarith
  have h1' : 1 + r ≠ 0 := h1.ne'
  have h2' : 1 + i ≠ 0 := h2.ne'
  set a := ω / (1 + r) with ha
  set b := ω / (1 + i) with hb
  have ha1 : a < 1 := by rw [ha, div_lt_one h1]; exact hω1
  have hb0 : 0 ≤ b := div_nonneg hω0 h2.le
  have hb1 : b < 1 := by rw [hb, div_lt_one h2]; linarith
  have hfin : ∑ j ∈ Finset.range (T + 1), fgPrice r i T j * ω ^ j =
      (1 - a ^ (T + 1)) / (1 - a) := by
    have : ∀ j ∈ Finset.range (T + 1), fgPrice r i T j * ω ^ j = a ^ j := by
      intro j hj
      rw [fgPrice_of_le r i (by have := Finset.mem_range.mp hj; omega), ha, div_pow]
      field_simp
    rw [Finset.sum_congr rfl this, geom_sum_eq ha1.ne]
    have : a - 1 ≠ 0 := by linarith
    have : 1 - a ≠ 0 := by linarith
    field_simp
    ring
  rw [← hasSum_nat_add_iff' (T + 1), hfin]
  have htail : HasSum (fun n : ℕ => a ^ T * b * b ^ n) (a ^ T * b * (1 - b)⁻¹) :=
    (hasSum_geometric_of_lt_one hb0 hb1).mul_left (a ^ T * b)
  convert htail using 1
  · funext n
    rw [show n + (T + 1) = T + (n + 1) by omega, fgPrice_add, ha, hb, div_pow, div_pow]
    field_simp
    ring
  · rw [fgSum]
    ring

/-- Cochrane (2023), Online Appendix eq. (1.15), p. 559: without a rate change the valuation sum
is `(1+r)/(1+r−ω) = 1/(1−a)`. -/
theorem fgSum_same {r ω : ℝ} (hr : -1 < r) (hω1 : ω < 1 + r) (T : ℕ) :
    fgSum r r ω T = 1 / (1 - ω / (1 + r)) := by
  have h1 : 0 < 1 + r := by linarith
  have ha1 : ω / (1 + r) < 1 := by rw [div_lt_one h1]; exact hω1
  rw [fgSum]
  generalize ω / (1 + r) = a at *
  have : 1 - a ≠ 0 := by linarith
  field_simp
  ring

/-- Cochrane (2023), Online Appendix p. 560: the forward-guidance price-level jump with a
geometric maturity structure, `J_T = (ω/(1+r))^T [(1+i)(1+r−ω)/((1+r)(1+i−ω)) − 1]`. -/
noncomputable def fgJump (r i ω : ℝ) (T : ℕ) : ℝ :=
  (ω / (1 + r)) ^ T * ((1 + i) * (1 + r - ω) / ((1 + r) * (1 + i - ω)) - 1)

/-- Cochrane (2023), Online Appendix p. 560: **the discrete forward-guidance formula.** Starting
from the steady state `(B/P) ∑ (ω/(1+r))^j = PV`, an announcement at 0 of a rise from `r` to `i`
at `T`, with the same debt `B` and surpluses, gives `P_0/P − 1 = J_T`. -/
theorem fg_jump_geometric {r i ω B P P0 PV : ℝ} (hr : -1 < r) (hri : r ≤ i)
    (hω1 : ω < 1 + r) (hP : 0 < P) (hP0 : 0 < P0) (T : ℕ)
    (hss : B / P * fgSum r r ω T = PV) (hfg : B / P0 * fgSum r i ω T = PV) (hPV : PV ≠ 0) :
    P0 / P - 1 = fgJump r i ω T := by
  have h1 : 0 < 1 + r := by linarith
  have h2 : 0 < 1 + i := by linarith
  have ha1 : ω / (1 + r) < 1 := by rw [div_lt_one h1]; exact hω1
  have hb1 : ω / (1 + i) < 1 := by rw [div_lt_one h2]; linarith
  have hu : 1 - ω / (1 + r) ≠ 0 := by linarith
  rw [fgSum_same hr hω1, div_mul_div_comm, mul_one, div_eq_iff (mul_ne_zero hP.ne' hu)] at hss
  rw [div_mul_eq_mul_div, div_eq_iff hP0.ne'] at hfg
  have hratio : P0 / P = fgSum r i ω T * (1 - ω / (1 + r)) := by
    rw [div_eq_iff hP.ne']
    apply mul_left_cancel₀ hPV
    rw [← hfg, hss]
    ring
  have hfac : (1 + i) * (1 + r - ω) / ((1 + r) * (1 + i - ω)) =
      (1 - ω / (1 + r)) / (1 - ω / (1 + i)) := by
    have : 1 + i - ω ≠ 0 := by linarith
    have : 1 + r ≠ 0 := h1.ne'
    have : 1 + i ≠ 0 := h2.ne'
    field_simp
  rw [hratio, fgSum, fgJump, hfac]
  generalize ω / (1 + r) = a at *
  generalize ω / (1 + i) = b at *
  have : 1 - a ≠ 0 := by linarith
  have : 1 - b ≠ 0 := by linarith
  field_simp
  ring

/-- Cochrane (2023), Online Appendix eq. (1.16), p. 559: an immediate permanent rise (`T = 0`)
gives `P_0/P = (1+i)(1+r−ω)/((1+r)(1+i−ω))`. -/
theorem fg_jump_immediate (r i ω : ℝ) :
    fgJump r i ω 0 + 1 = (1 + i) * (1 + r - ω) / ((1 + r) * (1 + i - ω)) := by
  simp [fgJump]

/-- Cochrane (2023), Online Appendix p. 560: the jump in closed form,
`J_T = −(ω/(1+r))^T ω (i − r)/((1+r)(1+i−ω))`. -/
theorem fgJump_eq {r i ω : ℝ} (hr : -1 < r) (hiω : ω < 1 + i) (T : ℕ) :
    fgJump r i ω T = -((ω / (1 + r)) ^ T * (ω * (i - r) / ((1 + r) * (1 + i - ω)))) := by
  have h1 : 1 + r ≠ 0 := by linarith
  have h2 : 1 + i - ω ≠ 0 := by linarith
  rw [fgJump]
  field_simp
  ring

/-- Cochrane (2023), Online Appendix p. 560: the price level jumps down,
`J_T < 0`, for `0 < ω < 1 + r` and `−1 < r < i`. -/
theorem fgJump_neg {r i ω : ℝ} (hr : -1 < r) (hri : r < i) (hω0 : 0 < ω) (hω1 : ω < 1 + r)
    (T : ℕ) : fgJump r i ω T < 0 := by
  have h1 : 0 < 1 + r := by linarith
  rw [fgJump_eq hr (by linarith) T, neg_lt_zero]
  have : 0 < 1 + i - ω := by linarith
  have : 0 < i - r := by linarith
  positivity

/-- Cochrane (2023), Online Appendix p. 561: a longer horizon gives a smaller jump,
`J_{T+1} = (ω/(1+r)) J_T`, so `|J_{T+1}| < |J_T|` for `0 < ω < 1 + r`. -/
theorem fgJump_succ (r i ω : ℝ) (T : ℕ) :
    fgJump r i ω (T + 1) = ω / (1 + r) * fgJump r i ω T := by
  rw [fgJump, fgJump, pow_succ]
  ring

/-- Cochrane (2023), Online Appendix p. 561: the jump shrinks strictly with the horizon. -/
theorem fgJump_abs_lt {r i ω : ℝ} (hr : -1 < r) (hri : r < i) (hω0 : 0 < ω) (hω1 : ω < 1 + r)
    (T : ℕ) : |fgJump r i ω (T + 1)| < |fgJump r i ω T| := by
  have h1 : 0 < 1 + r := by linarith
  have hJ := fgJump_neg hr hri hω0 hω1 T
  rw [fgJump_succ, abs_mul, abs_of_pos (div_pos hω0 h1)]
  have ha1 : ω / (1 + r) < 1 := by rw [div_lt_one h1]; exact hω1
  have : 0 < |fgJump r i ω T| := abs_pos.mpr hJ.ne
  nlinarith

/-- Cochrane (2023), Online Appendix p. 561: as `T → ∞` the downward jump goes to zero. -/
theorem fgJump_tendsto {r i ω : ℝ} (hr : -1 < r) (hω0 : 0 ≤ ω) (hω1 : ω < 1 + r) :
    Tendsto (fun T => fgJump r i ω T) atTop (𝓝 0) := by
  have h1 : 0 < 1 + r := by linarith
  have ha1 : ω / (1 + r) < 1 := by rw [div_lt_one h1]; exact hω1
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hω0 h1.le) ha1).mul_const
    ((1 + i) * (1 + r - ω) / ((1 + r) * (1 + i - ω)) - 1)
  simpa [fgJump] using this

/-- Cochrane (2023), Online Appendix p. 561: shorter maturity structures (lower `ω`) give a
smaller jump: `|J_T|` is monotone in `ω` on `[0, 1 + r)`. -/
theorem fgJump_abs_mono_omega {r i ω ω' : ℝ} (hr : -1 < r) (hri : r ≤ i) (hω0 : 0 ≤ ω)
    (hωω' : ω ≤ ω') (hω'1 : ω' < 1 + r) (T : ℕ) :
    |fgJump r i ω T| ≤ |fgJump r i ω' T| := by
  have h1 : 0 < 1 + r := by linarith
  rw [fgJump_eq hr (by linarith) T, fgJump_eq hr (by linarith) T, abs_neg, abs_neg]
  have hd : 0 < 1 + i - ω' := by linarith
  have hir : 0 ≤ i - r := by linarith
  have nn : ∀ v, 0 ≤ v → v < 1 + i →
      0 ≤ (v / (1 + r)) ^ T * (v * (i - r) / ((1 + r) * (1 + i - v))) := fun v hv0 hv1 =>
    mul_nonneg (pow_nonneg (div_nonneg hv0 h1.le) T)
      (div_nonneg (mul_nonneg hv0 hir) (mul_pos h1 (by linarith)).le)
  rw [abs_of_nonneg (nn ω hω0 (by linarith)), abs_of_nonneg (nn ω' (by linarith) (by linarith))]
  have hp : (ω / (1 + r)) ^ T ≤ (ω' / (1 + r)) ^ T :=
    pow_le_pow_left₀ (div_nonneg hω0 h1.le) (div_le_div_of_nonneg_right hωω' h1.le) T
  have hq : ω * (i - r) / ((1 + r) * (1 + i - ω)) ≤ ω' * (i - r) / ((1 + r) * (1 + i - ω')) :=
    div_le_div₀ (mul_nonneg (by linarith) hir) (mul_le_mul_of_nonneg_right hωω' hir)
      (mul_pos h1 hd) (mul_le_mul_of_nonneg_left (by linarith) h1.le)
  exact mul_le_mul hp hq (div_nonneg (mul_nonneg hω0 hir) (mul_pos h1 (by linarith)).le)
    (pow_nonneg (div_nonneg (by linarith) h1.le) T)

/-- Cochrane (2023), Online Appendix p. 560, Figure 7.1 calibration (`ω = 0.8`, `r = 2%`,
`i = 3%`): the immediate rise lowers the price level by 3.41%, forward guidance with `T = 3` by
1.65% (the book reports 3.5% and 1.6%). -/
theorem fgJump_calibration :
    -0.035 < fgJump 0.02 0.03 0.8 0 ∧ fgJump 0.02 0.03 0.8 0 < -0.034 ∧
      -0.017 < fgJump 0.02 0.03 0.8 3 ∧ fgJump 0.02 0.03 0.8 3 < -0.016 := by
  simp only [fgJump]
  norm_num

/-- Cochrane (2023), Online Appendix eq. (1.19), p. 560: for a discrete perpetuity (`ω = 1`) a rise
from 3% to 4% gives `P_0/P = (1+i) r/((1+r) i) ≈ 0.757`, a 24.3% drop; the "25%" quoted on p. 560
is the continuous-time ratio `r/i` of (1.20). -/
theorem perpetuity_ratio_bounds :
    fgJump 0.03 0.04 1 0 + 1 = (1 + 0.04) * 0.03 / ((1 + 0.03) * 0.04) ∧
      0.757 < fgJump 0.03 0.04 1 0 + 1 ∧ fgJump 0.03 0.04 1 0 + 1 < 0.758 := by
  simp only [fgJump]
  norm_num

/-! ### Continuous time (Online Appendix p. 561) -/

/-- Cochrane (2023), Online Appendix p. 561: the continuous-time valuation integrand: maturity
density `ϖ e^{−ϖ j}` times the bond price `exp(−(r min(j,T) + i max(j−T,0)))`. -/
noncomputable def cfgIntegrand (r i ϖ T j : ℝ) : ℝ :=
  ϖ * Real.exp (-ϖ * j) * Real.exp (-(r * min j T + i * max (j - T) 0))

/-- Cochrane (2023), Online Appendix p. 561: the valuation integral in closed form,
`ϖ[(1 − e^{−(r+ϖ)T})/(r+ϖ) + e^{−(r+ϖ)T}/(i+ϖ)]`. -/
noncomputable def cfgValue (r i ϖ T : ℝ) : ℝ :=
  ϖ * ((1 - Real.exp (-(r + ϖ) * T)) / (r + ϖ) + Real.exp (-(r + ϖ) * T) / (i + ϖ))

/-- Cochrane (2023), Online Appendix p. 561: `∫_0^∞ ϖ e^{−ϖj} Q_0(j) dj = cfgValue`, a genuine
improper integral, for `r + ϖ > 0`, `i + ϖ > 0`, `T ≥ 0`. -/
theorem integral_cfg {r i ϖ T : ℝ} (hrv : 0 < r + ϖ) (hiv : 0 < i + ϖ) (hT : 0 ≤ T) :
    ∫ j in Set.Ioi (0 : ℝ), cfgIntegrand r i ϖ T j = cfgValue r i ϖ T := by
  set g : ℝ → ℝ := fun j => ϖ * Real.exp (-(r + ϖ) * j) with hg
  set h : ℝ → ℝ := fun j => ϖ * Real.exp ((i - r) * T) * Real.exp (-(i + ϖ) * j) with hh
  have hgi : ∀ c, IntegrableOn g (Set.Ioi c) := fun c =>
    (integrableOn_exp_mul_Ioi (by linarith) c).const_mul ϖ
  have hhi : IntegrableOn h (Set.Ioi T) :=
    (integrableOn_exp_mul_Ioi (by linarith) T).const_mul _
  have hgI : ∀ c, ∫ j in Set.Ioi c, g j = ϖ * (Real.exp (-(r + ϖ) * c) / (r + ϖ)) := by
    intro c
    rw [hg, integral_const_mul, integral_exp_mul_Ioi (by linarith)]
    field_simp
  have hhI : ∫ j in Set.Ioi T, h j = ϖ * (Real.exp (-(r + ϖ) * T) / (i + ϖ)) := by
    have hE : Real.exp (-(r + ϖ) * T) = Real.exp ((i - r) * T) * Real.exp (-(i + ϖ) * T) := by
      rw [← Real.exp_add]; congr 1; ring
    have hne : i + ϖ ≠ 0 := hiv.ne'
    rw [hh, integral_const_mul, integral_exp_mul_Ioi (by linarith), hE]
    field_simp
  have hEg : Set.EqOn (cfgIntegrand r i ϖ T) g (Set.Ioc 0 T) := by
    intro j hj
    simp only [cfgIntegrand, hg, min_eq_left hj.2, max_eq_right (by linarith [hj.2] : j - T ≤ 0),
      mul_zero, add_zero, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hEh : Set.EqOn (cfgIntegrand r i ϖ T) h (Set.Ioi T) := by
    intro j hj
    have hj' : T < j := hj
    simp only [cfgIntegrand, hh, min_eq_right hj'.le, max_eq_left (by linarith : 0 ≤ j - T),
      mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hfs : IntegrableOn (cfgIntegrand r i ϖ T) (Set.Ioc 0 T) :=
    ((hgi 0).mono_set Set.Ioc_subset_Ioi_self).congr_fun hEg.symm measurableSet_Ioc
  have hft : IntegrableOn (cfgIntegrand r i ϖ T) (Set.Ioi T) :=
    hhi.congr_fun hEh.symm measurableSet_Ioi
  rw [← Set.Ioc_union_Ioi_eq_Ioi hT, setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
    hfs hft, setIntegral_congr_fun measurableSet_Ioc hEg,
    setIntegral_congr_fun measurableSet_Ioi hEh, hhI]
  have hsplit := setIntegral_union (Set.Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := T))
    measurableSet_Ioi ((hgi 0).mono_set Set.Ioc_subset_Ioi_self) (hgi T)
  rw [Set.Ioc_union_Ioi_eq_Ioi hT, hgI 0, hgI T] at hsplit
  have hgIoc : ∫ j in Set.Ioc 0 T, g j =
      ϖ * (Real.exp (-(r + ϖ) * 0) / (r + ϖ)) - ϖ * (Real.exp (-(r + ϖ) * T) / (r + ϖ)) := by
    linarith
  rw [hgIoc, cfgValue, mul_zero, Real.exp_zero]
  ring

/-- Cochrane (2023), Online Appendix eq. (1.17), p. 560: with no rate change the valuation
integral is `ϖ/(r+ϖ)`. -/
theorem cfgValue_same (r ϖ T : ℝ) (hrv : 0 < r + ϖ) : cfgValue r r ϖ T = ϖ / (r + ϖ) := by
  rw [cfgValue]
  field_simp
  ring

/-- Cochrane (2023), Online Appendix p. 561: the continuous-time forward-guidance jump
`e^{−(r+ϖ)T}((r+ϖ)/(i+ϖ) − 1)`. -/
noncomputable def cfgJump (r i ϖ T : ℝ) : ℝ := Real.exp (-(r + ϖ) * T) * ((r + ϖ) / (i + ϖ) - 1)

/-- Cochrane (2023), Online Appendix p. 561: **the continuous forward-guidance formula.** From
the steady state `(B/P)·ϖ/(r+ϖ) = PV`, the announcement gives `P_0/P − 1 = cfgJump`. -/
theorem cfg_jump {r i ϖ T B P P0 PV : ℝ} (hrv : 0 < r + ϖ) (hiv : 0 < i + ϖ) (hϖ : 0 < ϖ)
    (hP : 0 < P) (hP0 : 0 < P0) (hss : B / P * cfgValue r r ϖ T = PV)
    (hfg : B / P0 * cfgValue r i ϖ T = PV) (hPV : PV ≠ 0) :
    P0 / P - 1 = cfgJump r i ϖ T := by
  rw [cfgValue_same r ϖ T hrv, div_mul_div_comm, div_eq_iff (mul_ne_zero hP.ne' hrv.ne')] at hss
  rw [div_mul_eq_mul_div, div_eq_iff hP0.ne'] at hfg
  have hP0eq : P0 = P * cfgValue r i ϖ T * (r + ϖ) / ϖ := by
    rw [eq_div_iff hϖ.ne']
    apply mul_left_cancel₀ hPV
    linear_combination (cfgValue r i ϖ T) * hss - ϖ * hfg
  rw [hP0eq, cfgValue, cfgJump]
  have : i + ϖ ≠ 0 := hiv.ne'
  have : r + ϖ ≠ 0 := hrv.ne'
  have : ϖ ≠ 0 := hϖ.ne'
  have : P ≠ 0 := hP.ne'
  field_simp
  ring

/-- Cochrane (2023), Online Appendix eq. (1.18), p. 560: the immediate rise (`T = 0`) gives
`P_0/P = (r+ϖ)/(i+ϖ)`, and for the perpetuity (`ϖ = 0`) eq. (1.20) `P_0/P = r/i`. -/
theorem cfgJump_zero (r i ϖ : ℝ) : cfgJump r i ϖ 0 + 1 = (r + ϖ) / (i + ϖ) := by
  simp [cfgJump]

/-- Cochrane (2023), Online Appendix p. 561: the continuous-time jump is negative for `r < i`. -/
theorem cfgJump_neg {r i ϖ : ℝ} (hrv : 0 < r + ϖ) (hri : r < i) (T : ℝ) : cfgJump r i ϖ T < 0 := by
  rw [cfgJump]
  apply mul_neg_of_pos_of_neg (Real.exp_pos _)
  rw [sub_neg, div_lt_one (by linarith)]
  linarith

/-- Cochrane (2023), Online Appendix p. 561: a longer horizon gives a smaller jump. -/
theorem cfgJump_abs_anti {r i ϖ : ℝ} (hrv : 0 < r + ϖ) (hri : r < i) {T T' : ℝ} (hTT' : T < T') :
    |cfgJump r i ϖ T'| < |cfgJump r i ϖ T| := by
  rw [abs_of_neg (cfgJump_neg hrv hri T'), abs_of_neg (cfgJump_neg hrv hri T), neg_lt_neg_iff,
    cfgJump, cfgJump]
  have hc : (r + ϖ) / (i + ϖ) - 1 < 0 := by
    rw [sub_neg, div_lt_one (by linarith)]; linarith
  apply mul_lt_mul_of_neg_right _ hc
  exact Real.exp_lt_exp.mpr (by nlinarith)

/-- Cochrane (2023), Online Appendix p. 561: as `T → ∞` the continuous-time jump vanishes. -/
theorem cfgJump_tendsto {r i ϖ : ℝ} (hrv : 0 < r + ϖ) :
    Tendsto (fun T => cfgJump r i ϖ T) atTop (𝓝 0) := by
  have h : Tendsto (fun T : ℝ => -(r + ϖ) * T) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (by linarith)
  have := (Real.tendsto_exp_atBot.comp h).mul_const ((r + ϖ) / (i + ϖ) - 1)
  simpa [cfgJump, Function.comp_def] using this

/-- Cochrane (2023), Online Appendix p. 561: a shorter maturity structure (larger `ϖ`) gives a
smaller jump: `|cfgJump|` is antitone in `ϖ` for `T ≥ 0`, `r < i`. -/
theorem cfgJump_abs_anti_varpi {r i ϖ ϖ' T : ℝ} (hrv : 0 < r + ϖ) (hri : r < i) (hT : 0 ≤ T)
    (hϖ : ϖ ≤ ϖ') : |cfgJump r i ϖ' T| ≤ |cfgJump r i ϖ T| := by
  have hrv' : 0 < r + ϖ' := by linarith
  rw [abs_of_neg (cfgJump_neg hrv' hri T), abs_of_neg (cfgJump_neg hrv hri T), neg_le_neg_iff,
    cfgJump, cfgJump]
  have e1 : (r + ϖ) / (i + ϖ) - 1 = -((i - r) / (i + ϖ)) := by
    rw [div_sub_one (by linarith), neg_div', neg_sub]; congr 1; ring
  have e2 : (r + ϖ') / (i + ϖ') - 1 = -((i - r) / (i + ϖ')) := by
    rw [div_sub_one (by linarith), neg_div', neg_sub]; congr 1; ring
  rw [e1, e2, mul_neg, mul_neg, neg_le_neg_iff]
  have hexp : Real.exp (-(r + ϖ') * T) ≤ Real.exp (-(r + ϖ) * T) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hfrac : (i - r) / (i + ϖ') ≤ (i - r) / (i + ϖ) :=
    div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
  exact mul_le_mul hexp hfrac (div_nonneg (by linarith) (by linarith)) (Real.exp_pos _).le

/-! ### Steady-state sales (Online Appendix p. 561) -/

/-- Cochrane (2023), Online Appendix p. 561: to keep the geometric structure
`B_{t−1}^{(t+j)} = ω^j B` the government sells, of each maturity `t + (j + 1)`, the amount
`B_t^{(t+j+1)} − B_{t−1}^{(t+j+1)} = ω^j B − ω^{j+1} B = ω^j(1−ω)B = ((1−ω)/ω) B_{t−1}^{(t+j+1)}`
every period. -/
theorem steady_sales {ω B : ℝ} (hω : ω ≠ 0) (j : ℕ) :
    ω ^ j * B - ω ^ (j + 1) * B = ω ^ j * (1 - ω) * B ∧
      ω ^ j * B - ω ^ (j + 1) * B = (1 - ω) / ω * (ω ^ (j + 1) * B) := by
  constructor
  · ring
  · field_simp
    ring

end Cochrane.LongTermDebtDynamics.ForwardGuidance
