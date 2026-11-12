/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.ForwardGuidance

/-!
# Forward guidance under uncertainty

Cochrane (2023), §7.1, pp. 213–215 (equation (7.3) and the bond-price display on p. 214), and
Online Appendix §A1.2.1, pp. 559–561 (the discrete geometric formula).

The book's forward-guidance analysis is deterministic. Here surpluses and price levels are
random (an arbitrary `ExpectationSystem` with the pull-out property), and the central bank
announces at date 0 a *known* path for the one-period nominal rate, `r` before `T` and `i` from
`T` on, implemented through the Fisher relation under uncertainty
`Q_t^{(t+1)} = β E_t(P_t/P_{t+1}) = 1/(1 + i_t)` (`FisherPath`), with `β = 1/(1+r)`.

* `bondPrice_eq_prod`, `stoch_fgPrice`: **bond prices are exactly the book's display**,
  `Q_0^{(j)} = ((1+r)^{min(j,T)}(1+i)^{j−T})^{-1}`, whatever the surplus uncertainty (the
  risk-neutral expectations hypothesis with a known rate path).
* `stoch_E0_path`: **the expected path**: `E_0(1/P_j) = 1/fgPath(P_0)`; the book's path is the
  path of expected values of `1/P_j`.
* `stoch_expected_inflation`, `stoch_no_expected_jump`, `stoch_expected_inflation_after`: the
  innovation form of "no second jump": before and at the rate rise the expected price ratio is
  one, `E_t(P_t/P_{t+1}) = 1` for `t < T`; from `T` on it is `(1+r)/(1+i) < 1`. Realised price
  levels move only with unforecastable news.
* `stoch_valuation`, `stoch_priceLevel`: the valuation equation (7.3) under uncertainty,
  `P_0 = (∑_j Q_0^{(j)} B_{−1}^{(j)}) / E_0 ∑ β^j s_j`, state by state.
* `stoch_fg_no_effect`, `stoch_fg_lowers`, `stoch_fg_mono`: the §7.1 claims under uncertainty:
  guidance beyond the longest maturity (`T ≥ k`) has no effect on `P_0`; otherwise, with some
  maturity `T < j₀ ≤ k` outstanding, nonnegative positions and `r < i`, it lowers `P_0`; the
  effect falls with the horizon (and the immediate rise has the largest effect).
* `stoch_geometric_value`, `stoch_fg_jump`: §A1.2.1 under uncertainty: with geometric
  maturities, the proportional jump `P_0/P − 1` (guidance versus no guidance, same surpluses) is
  the deterministic `ForwardGuidance.fgJump`, state by state.

The continuous-time formula of p. 561 is not restated: under the project's conventions continuous
time is deterministic (no stochastic calculus).
-/

namespace Cochrane.LongTermDebtDynamics.TidyR5GuidanceUncertainty

open Filter Topology MaturityStructure ForwardGuidance

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §7.1, p. 213 (under uncertainty): the announced, known path of one-period
nominal rates `i_t` is implemented: `Q_t^{(t+1)} = β E_t(P_t/P_{t+1}) = 1/(1 + i_t)` at every
date and state. -/
def FisherPath (β : ℝ) (P x : ℕ → Ω → ℝ) (i : ℕ → ℝ) : Prop :=
  ∀ t, bondPrice 𝔼 β P x t 1 = fun _ => (1 + i t)⁻¹

/-- Cochrane (2023), §7.1, p. 214 (under uncertainty): **the expectations hypothesis with a known
rate path.** If the announced rates `i_t` are implemented, every zero-coupon bond price is
deterministic, `Q_t^{(t+j)} = ∏_{u<j} (1 + i_{t+u})^{-1}`, however uncertain the price level. -/
theorem bondPrice_eq_prod (hpo : 𝔼.PullOut) {β : ℝ} {P x : ℕ → Ω → ℝ} {i : ℕ → ℝ}
    (hP : 𝔼.Adapted P) (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hF : FisherPath 𝔼 β P x i) (j : ℕ) :
    ∀ t, bondPrice 𝔼 β P x t j = fun _ => ∏ u ∈ Finset.range j, (1 + i (t + u))⁻¹ := by
  induction j with
  | zero =>
    intro t
    have h1 : P t * x (t + 0) = fun _ => (1 : ℝ) := funext fun ω => by simpa using hPx t ω
    simp only [bondPrice, pow_zero, one_smul, h1, 𝔼.const, Finset.range_zero, Finset.prod_empty]
  | succ j ih =>
    intro t
    have hsplit : P t * x (t + (j + 1)) = (P t * x (t + 1)) * (P (t + 1) * x (t + 1 + j)) := by
      funext ω
      simp only [Pi.mul_apply]
      rw [show t + 1 + j = t + (j + 1) by omega]
      have := hPx (t + 1) ω
      calc P t ω * x (t + (j + 1)) ω =
          P t ω * x (t + (j + 1)) ω * (P (t + 1) ω * x (t + 1) ω) := by rw [this, mul_one]
        _ = _ := by ring
    have hknown : 𝔼.E (t + 1) (P t * x (t + 1)) = P t * x (t + 1) := by
      rw [hpo _ _ _ (ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hP t)), hx (t + 1)]
    have ih' : β ^ j • 𝔼.E (t + 1) (P (t + 1) * x (t + 1 + j)) =
        fun _ => ∏ u ∈ Finset.range j, (1 + i (t + 1 + u))⁻¹ := ih (t + 1)
    have hF' : β • 𝔼.E t (P t * x (t + 1)) = fun _ => (1 + i t)⁻¹ := by
      have := hF t
      simpa [bondPrice] using this
    have e1 : β ^ (j + 1) • 𝔼.E t (P t * x (t + (j + 1))) = β • 𝔼.E t ((P t * x (t + 1)) *
        (β ^ j • 𝔼.E (t + 1) (P (t + 1) * x (t + 1 + j)))) := by
      rw [hsplit, ← 𝔼.tower (Nat.le_succ t) ((P t * x (t + 1)) * (P (t + 1) * x (t + 1 + j))),
        hpo _ _ _ hknown, mul_smul_comm, map_smul, smul_smul, ← pow_succ']
    change β ^ (j + 1) • 𝔼.E t (P t * x (t + (j + 1))) = _
    rw [e1, ih']
    set c : ℝ := ∏ u ∈ Finset.range j, (1 + i (t + 1 + u))⁻¹ with hc
    have h2 : (P t * x (t + 1)) * (fun _ => c) = c • (P t * x (t + 1)) := by
      funext ω; simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [h2, map_smul, smul_comm, hF']
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.prod_range_succ', hc, add_zero]
    congr 1
    refine Finset.prod_congr rfl fun u _ => ?_
    rw [show t + (u + 1) = t + 1 + u by omega]

/-- Cochrane (2023), §7.1, p. 214: the product of one-period discount factors along the announced
path is the forward-guidance bond price, `∏_{u<j}(1 + i_u)^{-1} = fgPrice r i T j`. -/
theorem prod_fgRate {r i : ℝ} (hr : -1 < r) (hi : -1 < i) (T j : ℕ) :
    ∏ u ∈ Finset.range j, (1 + fgRate r i T (0 + u))⁻¹ = fgPrice r i T j := by
  have h1 : (1 + r) ≠ 0 := by linarith
  have h2 : (1 + i) ≠ 0 := by linarith
  induction j with
  | zero => simp [fgPrice]
  | succ j ih =>
    rw [Finset.prod_range_succ, ih, zero_add]
    unfold fgPrice fgRate
    by_cases hj : j < T
    · simp only [hj, ↓reduceIte, min_eq_left (show j + 1 ≤ T by omega), min_eq_left hj.le,
        Nat.sub_eq_zero_of_le (show j + 1 ≤ T by omega), Nat.sub_eq_zero_of_le hj.le, pow_succ]
      field_simp
    · simp only [hj, ↓reduceIte, min_eq_right (show T ≤ j + 1 by omega),
        min_eq_right (show T ≤ j by omega), show j + 1 - T = j - T + 1 by omega, pow_succ]
      field_simp

/-- Cochrane (2023), §7.1, p. 214 (under uncertainty): **the bond-price display holds under
uncertainty**: with the announced path (`r` before `T`, `i` from `T` on) implemented and
`β = 1/(1+r)`, `Q_0^{(j)} = β^j E_0(P_0/P_j) = ((1+r)^{min(j,T)}(1+i)^{j−T})^{-1}` in every
state. -/
theorem stoch_fgPrice (hpo : 𝔼.PullOut) {r i : ℝ} (hr : -1 < r) (hi : -1 < i) {T : ℕ}
    {P x : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P) (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hF : FisherPath 𝔼 (1 + r)⁻¹ P x (fgRate r i T)) (j : ℕ) :
    bondPrice 𝔼 (1 + r)⁻¹ P x 0 j = fun _ => fgPrice r i T j := by
  rw [bondPrice_eq_prod 𝔼 hpo hP hx hPx hF j 0, prod_fgRate hr hi T j]

/-- Cochrane (2023), §7.1, pp. 214–215 (under uncertainty): **the expected path.** The book's
price path is the path of expected values of `1/P`: `E_0(1/P_j) = 1/fgPath(P_0)_j`, so `E_0(1/P_j)`
is flat until `T` and falls at the rate `(1+r)/(1+i)` afterwards. -/
theorem stoch_E0_path (hpo : 𝔼.PullOut) {r i : ℝ} (hr : -1 < r) (hi : -1 < i) {T : ℕ}
    {P x : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P) (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hF : FisherPath 𝔼 (1 + r)⁻¹ P x (fgRate r i T)) (j : ℕ) (ω : Ω) :
    𝔼.E 0 (x j) ω = (fgPath (P 0 ω) r i T j)⁻¹ := by
  have hP0 : P 0 ω ≠ 0 := fun h => by have := hPx 0 ω; rw [h, zero_mul] at this; simp at this
  have h1 : (1 + r) ≠ 0 := by linarith
  have hb := congrFun (stoch_fgPrice 𝔼 hpo hr hi hP hx hPx hF j) ω
  rw [bondPrice_eq 𝔼 hpo hP, fgPrice_eq_path hP0 hr hi] at hb
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, zero_add] at hb
  have hβ : ((1 + r)⁻¹) ^ j ≠ 0 := pow_ne_zero _ (inv_ne_zero h1)
  have := mul_left_cancel₀ hβ hb
  rw [div_eq_mul_inv] at this
  exact mul_left_cancel₀ hP0 this

/-- Cochrane (2023), §7.1, p. 215 (under uncertainty): the Fisher relation with the announced path,
`E_t(P_t/P_{t+1}) = (1 + r)/(1 + i_t)`. -/
theorem stoch_expected_inflation {r i : ℝ} (hr : -1 < r) {T : ℕ} {P x : ℕ → Ω → ℝ}
    (hF : FisherPath 𝔼 (1 + r)⁻¹ P x (fgRate r i T)) (t : ℕ) :
    𝔼.E t (P t * x (t + 1)) = fun _ => (1 + r) / (1 + fgRate r i T t) := by
  have h1 : (1 + r) ≠ 0 := by linarith
  have := hF t
  simp only [bondPrice, pow_one] at this
  funext ω
  have hω := congrFun this ω
  simp only [Pi.smul_apply, smul_eq_mul] at hω
  rw [div_eq_mul_inv, ← hω]
  field_simp

/-- Cochrane (2023), §7.1, p. 215 (under uncertainty): **no predictable second jump**: up to and
including the date of the rate rise there is no expected price change,
`E_t(P_t/P_{t+1}) = 1` for every `t < T`; any change in the price level at `T` is news. -/
theorem stoch_no_expected_jump {r i : ℝ} (hr : -1 < r) {T : ℕ} {P x : ℕ → Ω → ℝ}
    (hF : FisherPath 𝔼 (1 + r)⁻¹ P x (fgRate r i T)) {t : ℕ} (ht : t < T) :
    𝔼.E t (P t * x (t + 1)) = fun _ => 1 := by
  have h1 : (1 + r) ≠ 0 := by linarith
  rw [stoch_expected_inflation 𝔼 hr hF t]
  funext ω
  simp [fgRate, ht, div_self h1]

/-- Cochrane (2023), §7.1, p. 215 (under uncertainty): **expected inflation starts when the rate
rises**: for `t ≥ T`, `E_t(P_t/P_{t+1}) = (1+r)/(1+i) < 1` when `−1 < r < i`. -/
theorem stoch_expected_inflation_after {r i : ℝ} (hr : -1 < r) (hri : r < i) {T : ℕ}
    {P x : ℕ → Ω → ℝ} (hF : FisherPath 𝔼 (1 + r)⁻¹ P x (fgRate r i T)) {t : ℕ} (ht : T ≤ t)
    (ω : Ω) : 𝔼.E t (P t * x (t + 1)) ω = (1 + r) / (1 + i) ∧ (1 + r) / (1 + i) < 1 := by
  have hrate : fgRate r i T t = i := by simp [fgRate, show ¬ t < T by omega]
  rw [stoch_expected_inflation 𝔼 hr hF t, hrate]
  exact ⟨rfl, (div_lt_one (by linarith)).mpr (by linarith)⟩

/-- Cochrane (2023), eq. (7.3), p. 214 (under uncertainty): **the valuation equation.** With
deterministic outstanding debt `B_{−1}^{(j)} = B_j` (none beyond maturity `k`) and the announced
path implemented, the date-0 present-value relation reads, state by state,
`(∑_{j≤k} Q_0^{(j)} B_{−1}^{(j)})/P_0 = E_0 ∑_j β^j s_j` with the book's bond prices. -/
theorem stoch_valuation (hpo : 𝔼.PullOut) {r i : ℝ} (hr : -1 < r) (hi : -1 < i) {T k : ℕ}
    {B : ℕ → ℝ} (hBk : ∀ j, k < j → B j = 0) {P x s : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P)
    (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hF : FisherPath 𝔼 (1 + r)⁻¹ P x (fgRate r i T))
    (hpv : PresentValue 𝔼 (1 + r)⁻¹ (fun _ j _ => B j) x s 0) (ω : Ω) :
    (∑ j ∈ Finset.range (k + 1), fgPrice r i T j * B j) / P 0 ω =
      pvSurplus 𝔼 (1 + r)⁻¹ s 0 ω := by
  have hterm : ∀ j, debtTerm 𝔼 (1 + r)⁻¹ (fun _ j _ => B j) x 0 j ω =
      x 0 ω * (fgPrice r i T j * B j) := by
    intro j
    have hb := congrFun (stoch_fgPrice 𝔼 hpo hr hi hP hx hPx hF j) ω
    rw [bondPrice_eq 𝔼 hpo hP] at hb
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, zero_add] at hb
    simp only [debtTerm, zero_add]
    rw [← hb]
    have := hPx 0 ω
    linear_combination (-(B j * (1 + r)⁻¹ ^ j * 𝔼.E 0 (x j) ω)) * this
  have hfin : HasSum (fun j => debtTerm 𝔼 (1 + r)⁻¹ (fun _ j _ => B j) x 0 j ω)
      (∑ j ∈ Finset.range (k + 1), x 0 ω * (fgPrice r i T j * B j)) := by
    simp only [hterm]
    exact hasSum_sum_of_ne_finset_zero fun j hj => by
      rw [hBk j (by simpa using hj), mul_zero, mul_zero]
  have := (hpv ω).2.unique hfin
  rw [this, ← Finset.mul_sum, div_eq_mul_inv, mul_comm]
  congr 1
  exact inv_eq_of_mul_eq_one_right (hPx 0 ω)

/-- Cochrane (2023), eq. (7.3), p. 214 (under uncertainty): with a positive present value of
surpluses, `P_0 = priceLevel (fgPrice r i T) B k (E_0 ∑ β^j s_j)` state by state. -/
theorem stoch_priceLevel (hpo : 𝔼.PullOut) {r i : ℝ} (hr : -1 < r) (hi : -1 < i) {T k : ℕ}
    {B : ℕ → ℝ} (hBk : ∀ j, k < j → B j = 0) {P x s : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P)
    (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1) (hP0 : ∀ ω, 0 < P 0 ω)
    (hF : FisherPath 𝔼 (1 + r)⁻¹ P x (fgRate r i T))
    (hpv : PresentValue 𝔼 (1 + r)⁻¹ (fun _ j _ => B j) x s 0) (ω : Ω)
    (hS : 0 < pvSurplus 𝔼 (1 + r)⁻¹ s 0 ω) :
    P 0 ω = priceLevel (fgPrice r i T) B k (pvSurplus 𝔼 (1 + r)⁻¹ s 0 ω) :=
  (valuation_iff _ B k hS (hP0 ω)).mp (stoch_valuation 𝔼 hpo hr hi hBk hP hx hPx hF hpv ω)

/-- Cochrane (2023), §7.1, p. 214 (under uncertainty): **guidance beyond the longest maturity
has no effect**: if `T ≥ k`, the equilibrium `P_0` with guidance equals the one without any rate
change, in every state (same surpluses and outstanding debt). -/
theorem stoch_fg_no_effect (hpo : 𝔼.PullOut) {r i : ℝ} (hr : -1 < r) (hi : -1 < i) {T k : ℕ}
    (hkT : k ≤ T) {B : ℕ → ℝ} (hBk : ∀ j, k < j → B j = 0) {P x P' x' s : ℕ → Ω → ℝ}
    (hP : 𝔼.Adapted P) (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hP0 : ∀ ω, 0 < P 0 ω) (hF : FisherPath 𝔼 (1 + r)⁻¹ P x (fgRate r i T))
    (hpv : PresentValue 𝔼 (1 + r)⁻¹ (fun _ j _ => B j) x s 0)
    (hP' : 𝔼.Adapted P') (hx' : 𝔼.Adapted x') (hPx' : ∀ t ω, P' t ω * x' t ω = 1)
    (hP0' : ∀ ω, 0 < P' 0 ω) (hF' : FisherPath 𝔼 (1 + r)⁻¹ P' x' (fgRate r r T))
    (hpv' : PresentValue 𝔼 (1 + r)⁻¹ (fun _ j _ => B j) x' s 0) (ω : Ω)
    (hS : 0 < pvSurplus 𝔼 (1 + r)⁻¹ s 0 ω) : P 0 ω = P' 0 ω := by
  rw [stoch_priceLevel 𝔼 hpo hr hi hBk hP hx hPx hP0 hF hpv ω hS,
    stoch_priceLevel 𝔼 hpo hr hr hBk hP' hx' hPx' hP0' hF' hpv' ω hS]
  exact priceLevel_fg_of_le r i B hkT _

/-- Cochrane (2023), §7.1, pp. 213–214 (under uncertainty): **guidance within the
maturity structure lowers `P_0`**: if some maturity `j₀` with `T < j₀ ≤ k` is outstanding
(nonnegative positions, `r < i`), `P_0` with guidance is strictly below `P_0` without, in every
state. -/
theorem stoch_fg_lowers (hpo : 𝔼.PullOut) {r i : ℝ} (hr : -1 < r) (hri : r < i) {T k j₀ : ℕ}
    (hTj : T < j₀) (hjk : j₀ ≤ k) {B : ℕ → ℝ} (hB : ∀ j, 0 ≤ B j) (hBj : 0 < B j₀)
    (hBk : ∀ j, k < j → B j = 0) {P x P' x' s : ℕ → Ω → ℝ}
    (hP : 𝔼.Adapted P) (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hP0 : ∀ ω, 0 < P 0 ω) (hF : FisherPath 𝔼 (1 + r)⁻¹ P x (fgRate r i T))
    (hpv : PresentValue 𝔼 (1 + r)⁻¹ (fun _ j _ => B j) x s 0)
    (hP' : 𝔼.Adapted P') (hx' : 𝔼.Adapted x') (hPx' : ∀ t ω, P' t ω * x' t ω = 1)
    (hP0' : ∀ ω, 0 < P' 0 ω) (hF' : FisherPath 𝔼 (1 + r)⁻¹ P' x' (fgRate r r T))
    (hpv' : PresentValue 𝔼 (1 + r)⁻¹ (fun _ j _ => B j) x' s 0) (ω : Ω)
    (hS : 0 < pvSurplus 𝔼 (1 + r)⁻¹ s 0 ω) : P 0 ω < P' 0 ω := by
  rw [stoch_priceLevel 𝔼 hpo hr (by linarith) hBk hP hx hPx hP0 hF hpv ω hS,
    stoch_priceLevel 𝔼 hpo hr hr hBk hP' hx' hPx' hP0' hF' hpv' ω hS]
  exact priceLevel_fg_lt hr hri hB hTj hjk hBj hS

/-- Cochrane (2023), §7.1, p. 213 (under uncertainty): **the effect of guidance falls with the
horizon**: with nonnegative positions, `P_0` under horizon `T` is at most `P_0` under horizon
`T' ≥ T`, in every state (`T = 0` is the immediate rise, the largest effect). -/
theorem stoch_fg_mono (hpo : 𝔼.PullOut) {r i : ℝ} (hr : -1 < r) (hri : r ≤ i) {T T' k : ℕ}
    (hTT' : T ≤ T') {B : ℕ → ℝ} (hB : ∀ j, 0 ≤ B j) (hBk : ∀ j, k < j → B j = 0)
    {P x P' x' s : ℕ → Ω → ℝ}
    (hP : 𝔼.Adapted P) (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hP0 : ∀ ω, 0 < P 0 ω) (hF : FisherPath 𝔼 (1 + r)⁻¹ P x (fgRate r i T))
    (hpv : PresentValue 𝔼 (1 + r)⁻¹ (fun _ j _ => B j) x s 0)
    (hP' : 𝔼.Adapted P') (hx' : 𝔼.Adapted x') (hPx' : ∀ t ω, P' t ω * x' t ω = 1)
    (hP0' : ∀ ω, 0 < P' 0 ω) (hF' : FisherPath 𝔼 (1 + r)⁻¹ P' x' (fgRate r i T'))
    (hpv' : PresentValue 𝔼 (1 + r)⁻¹ (fun _ j _ => B j) x' s 0) (ω : Ω)
    (hS : 0 < pvSurplus 𝔼 (1 + r)⁻¹ s 0 ω) : P 0 ω ≤ P' 0 ω := by
  have hi : -1 < i := by linarith
  rw [stoch_priceLevel 𝔼 hpo hr hi hBk hP hx hPx hP0 hF hpv ω hS,
    stoch_priceLevel 𝔼 hpo hr hi hBk hP' hx' hPx' hP0' hF' hpv' ω hS]
  exact priceLevel_mono hr hri hB k hS hTT'

/-! ### Geometric maturity structure (Online Appendix A1.2.1) under uncertainty -/

/-- Cochrane (2023), Online Appendix p. 560 (under uncertainty): with a geometric
maturity structure `B_{−1}^{(j)} = ϖ^j B` (`0 ≤ ϖ < 1 + r`, `r ≤ i`) and the announced path
implemented,
the date-0 present-value relation reads `B (1/P_0) fgSum = E_0 ∑ β^j s_j`, state by state. -/
theorem stoch_geometric_value (hpo : 𝔼.PullOut) {r i om B : ℝ} (hr : -1 < r) (hri : r ≤ i)
    (hom0 : 0 ≤ om) (hom1 : om < 1 + r) {T : ℕ} {P x s : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P)
    (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hF : FisherPath 𝔼 (1 + r)⁻¹ P x (fgRate r i T))
    (hpv : PresentValue 𝔼 (1 + r)⁻¹ (fun _ j _ => om ^ j * B) x s 0) (ω : Ω) :
    B * x 0 ω * fgSum r i om T = pvSurplus 𝔼 (1 + r)⁻¹ s 0 ω := by
  have hi : -1 < i := by linarith
  have hterm : ∀ j, debtTerm 𝔼 (1 + r)⁻¹ (fun _ j _ => om ^ j * B) x 0 j ω =
      B * x 0 ω * (fgPrice r i T j * om ^ j) := by
    intro j
    have hb := congrFun (stoch_fgPrice 𝔼 hpo hr hi hP hx hPx hF j) ω
    rw [bondPrice_eq 𝔼 hpo hP] at hb
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, zero_add] at hb
    simp only [debtTerm, zero_add]
    rw [← hb]
    have := hPx 0 ω
    linear_combination (-(om ^ j * B * (1 + r)⁻¹ ^ j * 𝔼.E 0 (x j) ω)) * this
  have hs := (hasSum_fg_geometric hr hri hom0 hom1 T).mul_left (B * x 0 ω)
  simp only [← hterm] at hs
  exact hs.unique (hpv ω).2

/-- Cochrane (2023), Online Appendix p. 560 (under uncertainty): **the discrete
forward-guidance formula holds state by state.** Compare the equilibrium with guidance (rate `i`
from `T`) with the one without any rate change, same surpluses and geometric debt. Then in every
state `P_0/P − 1 = J_T = fgJump r i ϖ T`, the book's deterministic number. -/
theorem stoch_fg_jump (hpo : 𝔼.PullOut) {r i om B : ℝ} (hr : -1 < r) (hri : r ≤ i)
    (hom0 : 0 ≤ om) (hom1 : om < 1 + r) {T : ℕ} {P x P' x' s : ℕ → Ω → ℝ}
    (hP : 𝔼.Adapted P) (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hP0 : ∀ ω, 0 < P 0 ω) (hF : FisherPath 𝔼 (1 + r)⁻¹ P x (fgRate r i T))
    (hpv : PresentValue 𝔼 (1 + r)⁻¹ (fun _ j _ => om ^ j * B) x s 0)
    (hP' : 𝔼.Adapted P') (hx' : 𝔼.Adapted x') (hPx' : ∀ t ω, P' t ω * x' t ω = 1)
    (hP0' : ∀ ω, 0 < P' 0 ω) (hF' : FisherPath 𝔼 (1 + r)⁻¹ P' x' (fgRate r r T))
    (hpv' : PresentValue 𝔼 (1 + r)⁻¹ (fun _ j _ => om ^ j * B) x' s 0) (ω : Ω)
    (hS : pvSurplus 𝔼 (1 + r)⁻¹ s 0 ω ≠ 0) :
    P 0 ω / P' 0 ω - 1 = fgJump r i om T := by
  have hx0 : ∀ {P x : ℕ → Ω → ℝ}, (∀ t ω, P t ω * x t ω = 1) → (∀ ω, 0 < P 0 ω) →
      x 0 ω = 1 / P 0 ω := fun hPx hP0 => by
    rw [eq_div_iff (hP0 ω).ne', mul_comm]; exact hPx 0 ω
  have hfg := stoch_geometric_value 𝔼 hpo hr hri hom0 hom1 hP hx hPx hF hpv ω
  have hss := stoch_geometric_value 𝔼 hpo hr le_rfl hom0 hom1 hP' hx' hPx' hF' hpv' ω
  rw [hx0 hPx hP0, mul_one_div] at hfg
  rw [hx0 hPx' hP0', mul_one_div] at hss
  exact fg_jump_geometric hr hri hom1 (hP0' ω) (hP0 ω) T hss hfg hS

end Cochrane.LongTermDebtDynamics.TidyR5GuidanceUncertainty
