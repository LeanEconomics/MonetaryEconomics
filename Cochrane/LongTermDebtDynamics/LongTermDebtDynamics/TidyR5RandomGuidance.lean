/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR5GuidanceUncertainty
import LongTermDebtDynamics.ExpectationsFiniteTree

/-!
# Forward guidance with a state-contingent rate path

Cochrane (2023), §7.1, pp. 213–215 (equation (7.3) and the bond-price display on p. 214).

The module TidyR5GuidanceUncertainty treats an announced rate path known at date 0. Here the
announced one-period rate `i_t` may be random (known at `t`, state-contingent guidance),
implemented through
`Q_t^{(t+1)} = β E_t(P_t/P_{t+1}) = 1/(1 + i_t)` (`RFisher`).

* `bondPrice_succ_eq`, `bondPrice_cov`, `bondPrice_cov_rate`: **the bond-price recursion with the
  covariance term explicit**:
  `Q_t^{(t+j+1)} = (1 + i_t)^{-1} E_t Q_{t+1}^{(t+j+1)} + Cov_t(β P_t/P_{t+1}, Q_{t+1}^{(t+j+1)})`.
  With a known rate path the covariance vanishes and the book's display follows
  (`TidyR5GuidanceUncertainty.bondPrice_eq_prod`); with random rates the bond price also differs
  from `E_t ∏ (1 + i)^{-1}` by convexity.
* `random_valuation`: (7.3) under uncertainty with random bond prices,
  `(∑_j Q_0^{(j)} B_{−1}^{(j)})/P_0 = E_0 ∑ β^j s_j`.
* **What survives.** `bondPrice_prefix`, `random_fg_no_effect`: if the rates before `T` are
  unchanged (`i_t = r`), bonds maturing by `T` keep their prices and guidance beyond the longest
  maturity (`T ≥ k`) has no effect on `P_0`, however random the later rates.
  `random_expected_ratio`, `random_no_expected_jump`: `E_t(P_t/P_{t+1}) = (1+r)/(1+i_t)` state by
  state; there is no expected jump where the rate is unchanged.
* **What fails.** `cg_counterexample`: "an announced rate rise lowers `P_0`" is false for
  state-contingent guidance. In a coin-flip economy the announced rate at date 1 is `2` or
  `1/5` (mean `11/10`, above `r = 1`) and `r` at every other date; with the same debt and
  surpluses the price level is `P_0 = 7/48` against `1/8` with no announcement: guidance with a
  higher expected rate path *raises* `P_0`. The bond price `Q_0^{(2)} = 7/24` exceeds `1/4`:
  `E_0 (1+i_1)^{-1} > (1 + E_0 i_1)^{-1}` (Jensen). The comparative statics of §7.1
  (`ForwardGuidance.priceLevel_fg_lt`, `ForwardGuidance.priceLevel_mono`,
  `ForwardGuidance.priceLevel_immediate_le`) are statements about the rate *path*; they extend to
  known paths (module TidyR5GuidanceUncertainty) but not to the expected path of random rates.

As in the book's §7.1 analysis, an equilibrium here means the Fisher relations at every date and
the date-0 valuation equation (7.3) (`MaturityStructure.PresentValue` at date 0).
-/

namespace Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance

open Filter Topology MaturityStructure ForwardGuidance

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §7.1 (under uncertainty): the conditional covariance
`Cov_t(a, b) = E_t(ab) − E_t a E_t b`. -/
noncomputable def condCov (t : ℕ) (a b : Ω → ℝ) : Ω → ℝ :=
  𝔼.E t (a * b) - 𝔼.E t a * 𝔼.E t b

/-- Cochrane (2023), §7.1, p. 213 (under uncertainty): a state-contingent announced rate path
`i_t` (known at `t`) is implemented: `Q_t^{(t+1)} = β E_t(P_t/P_{t+1}) = 1/(1 + i_t)`. -/
def RFisher (β : ℝ) (P x : ℕ → Ω → ℝ) (i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, bondPrice 𝔼 β P x t 1 = fun ω => (1 + i t ω)⁻¹

/-- Cochrane (2023), §7.1, p. 214 (under uncertainty): the bond-price recursion
`Q_t^{(t+j+1)} = E_t[(β P_t/P_{t+1}) Q_{t+1}^{(t+j+1)}]`. -/
theorem bondPrice_succ_eq (hpo : 𝔼.PullOut) {β : ℝ} {P x : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P)
    (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1) (t j : ℕ) :
    bondPrice 𝔼 β P x t (j + 1) =
      𝔼.E t ((β • (P t * x (t + 1))) * bondPrice 𝔼 β P x (t + 1) j) := by
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
  change β ^ (j + 1) • 𝔼.E t (P t * x (t + (j + 1))) =
    𝔼.E t ((β • (P t * x (t + 1))) * (β ^ j • 𝔼.E (t + 1) (P (t + 1) * x (t + 1 + j))))
  rw [hsplit, ← 𝔼.tower (Nat.le_succ t) ((P t * x (t + 1)) * (P (t + 1) * x (t + 1 + j))),
    hpo _ _ _ hknown, smul_mul_assoc, mul_smul_comm, map_smul, map_smul, smul_smul, ← pow_succ']

/-- Cochrane (2023), §7.1, p. 214 (under uncertainty): **the covariance decomposition**,
`Q_t^{(t+j+1)} = Q_t^{(t+1)} E_t Q_{t+1}^{(t+j+1)} + Cov_t(β P_t/P_{t+1}, Q_{t+1}^{(t+j+1)})`. -/
theorem bondPrice_cov (hpo : 𝔼.PullOut) {β : ℝ} {P x : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P)
    (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1) (t j : ℕ) :
    bondPrice 𝔼 β P x t (j + 1) = bondPrice 𝔼 β P x t 1 * 𝔼.E t (bondPrice 𝔼 β P x (t + 1) j) +
      condCov 𝔼 t (β • (P t * x (t + 1))) (bondPrice 𝔼 β P x (t + 1) j) := by
  rw [bondPrice_succ_eq 𝔼 hpo hP hx hPx, condCov]
  have h1 : bondPrice 𝔼 β P x t 1 = 𝔼.E t (β • (P t * x (t + 1))) := by
    rw [map_smul]; simp [bondPrice]
  rw [h1]
  ring

/-- Cochrane (2023), §7.1, p. 214 (under uncertainty): with a state-contingent rate path,
`Q_t^{(t+j+1)} = (1 + i_t)^{-1} E_t Q_{t+1}^{(t+j+1)} + Cov_t(β P_t/P_{t+1}, Q_{t+1}^{(t+j+1)})`. -/
theorem bondPrice_cov_rate (hpo : 𝔼.PullOut) {β : ℝ} {P x : ℕ → Ω → ℝ} {i : ℕ → Ω → ℝ}
    (hP : 𝔼.Adapted P) (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hF : RFisher 𝔼 β P x i) (t j : ℕ) :
    bondPrice 𝔼 β P x t (j + 1) = (fun ω => (1 + i t ω)⁻¹) *
      𝔼.E t (bondPrice 𝔼 β P x (t + 1) j) +
      condCov 𝔼 t (β • (P t * x (t + 1))) (bondPrice 𝔼 β P x (t + 1) j) := by
  rw [bondPrice_cov 𝔼 hpo hP hx hPx, hF t]

/-- Cochrane (2023), §7.1, p. 214 (under uncertainty): **bonds maturing by `T` are unaffected**:
if the rate is the known `r` at every date before `T`, then
`Q_t^{(t+j)} = (1+r)^{-j}` whenever `t + j ≤ T`, whatever the rates from `T` on. -/
theorem bondPrice_prefix (hpo : 𝔼.PullOut) {β r : ℝ} {P x : ℕ → Ω → ℝ} {T : ℕ}
    (hP : 𝔼.Adapted P) (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hF : ∀ t, t < T → bondPrice 𝔼 β P x t 1 = fun _ => (1 + r)⁻¹) (j : ℕ) :
    ∀ t, t + j ≤ T → bondPrice 𝔼 β P x t j = fun _ => ((1 + r)⁻¹) ^ j := by
  induction j with
  | zero =>
    intro t _
    have h1 : P t * x (t + 0) = fun _ => (1 : ℝ) := funext fun ω => by simpa using hPx t ω
    simp only [bondPrice, pow_zero, one_smul, h1, 𝔼.const]
  | succ j ih =>
    intro t ht
    rw [bondPrice_succ_eq 𝔼 hpo hP hx hPx, ih (t + 1) (by omega)]
    have h2 : (β • (P t * x (t + 1))) * (fun _ => ((1 + r)⁻¹) ^ j) =
        ((1 + r)⁻¹) ^ j • (β • (P t * x (t + 1))) := by
      funext ω; simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; ring
    have h3 : 𝔼.E t (β • (P t * x (t + 1))) = fun _ => (1 + r)⁻¹ := by
      rw [map_smul]
      have := hF t (by omega)
      simpa [bondPrice] using this
    rw [h2, map_smul, h3]
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- Cochrane (2023), eq. (7.3), p. 214 (under uncertainty): **the valuation equation with random
bond prices.** With deterministic outstanding debt `B_j` (none beyond `k`), in every state
`(∑_{j≤k} Q_0^{(j)} B_j)/P_0 = E_0 ∑ β^j s_j`. -/
theorem random_valuation (hpo : 𝔼.PullOut) {β : ℝ} {k : ℕ} {B : ℕ → ℝ}
    (hBk : ∀ j, k < j → B j = 0) {P x s : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P)
    (hPx : ∀ t ω, P t ω * x t ω = 1) (hpv : PresentValue 𝔼 β (fun _ j _ => B j) x s 0)
    (ω : Ω) :
    (∑ j ∈ Finset.range (k + 1), bondPrice 𝔼 β P x 0 j ω * B j) / P 0 ω =
      pvSurplus 𝔼 β s 0 ω := by
  have hterm : ∀ j, debtTerm 𝔼 β (fun _ j _ => B j) x 0 j ω =
      x 0 ω * (bondPrice 𝔼 β P x 0 j ω * B j) := by
    intro j
    rw [bondPrice_eq 𝔼 hpo hP]
    simp only [debtTerm, zero_add, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    have := hPx 0 ω
    linear_combination (-(B j * β ^ j * 𝔼.E 0 (x j) ω)) * this
  have hfin : HasSum (fun j => debtTerm 𝔼 β (fun _ j _ => B j) x 0 j ω)
      (∑ j ∈ Finset.range (k + 1), x 0 ω * (bondPrice 𝔼 β P x 0 j ω * B j)) := by
    simp only [hterm]
    exact hasSum_sum_of_ne_finset_zero fun j hj => by
      rw [hBk j (by simpa using hj), mul_zero, mul_zero]
  rw [(hpv ω).2.unique hfin, ← Finset.mul_sum, div_eq_mul_inv, mul_comm]
  congr 1
  exact inv_eq_of_mul_eq_one_right (hPx 0 ω)

/-- Cochrane (2023), §7.1, p. 214 (under uncertainty): **guidance beyond the longest maturity has
no effect, even when it is state-contingent**: if the rates before `T ≥ k` are the known `r` in
both equilibria (rates from `T` on arbitrary and random in the first), `P_0` is the same in every
state with a nonzero present value of surpluses. -/
theorem random_fg_no_effect (hpo : 𝔼.PullOut) {β r : ℝ} {T k : ℕ} (hkT : k ≤ T) {B : ℕ → ℝ}
    (hBk : ∀ j, k < j → B j = 0) {P x P' x' s : ℕ → Ω → ℝ}
    (hP : 𝔼.Adapted P) (hx : 𝔼.Adapted x) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hF : ∀ t, t < T → bondPrice 𝔼 β P x t 1 = fun _ => (1 + r)⁻¹)
    (hpv : PresentValue 𝔼 β (fun _ j _ => B j) x s 0)
    (hP' : 𝔼.Adapted P') (hx' : 𝔼.Adapted x') (hPx' : ∀ t ω, P' t ω * x' t ω = 1)
    (hF' : ∀ t, t < T → bondPrice 𝔼 β P' x' t 1 = fun _ => (1 + r)⁻¹)
    (hpv' : PresentValue 𝔼 β (fun _ j _ => B j) x' s 0) (ω : Ω)
    (hS : pvSurplus 𝔼 β s 0 ω ≠ 0) : P 0 ω = P' 0 ω := by
  have h1 := random_valuation 𝔼 hpo hBk hP hPx hpv ω
  have h2 := random_valuation 𝔼 hpo hBk hP' hPx' hpv' ω
  have hsame : ∑ j ∈ Finset.range (k + 1), bondPrice 𝔼 β P x 0 j ω * B j =
      ∑ j ∈ Finset.range (k + 1), bondPrice 𝔼 β P' x' 0 j ω * B j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjT : 0 + j ≤ T := by have := Finset.mem_range.mp hj; omega
    rw [bondPrice_prefix 𝔼 hpo hP hx hPx hF j 0 hjT,
      bondPrice_prefix 𝔼 hpo hP' hx' hPx' hF' j 0 hjT]
  rw [hsame] at h1
  have hA : ∑ j ∈ Finset.range (k + 1), bondPrice 𝔼 β P' x' 0 j ω * B j ≠ 0 := by
    intro h0; rw [h0, zero_div] at h2; exact hS h2.symm
  have hP0 : P 0 ω ≠ 0 := fun h => by have := hPx 0 ω; rw [h, zero_mul] at this; simp at this
  have hP0' : P' 0 ω ≠ 0 := fun h => by
    have := hPx' 0 ω; rw [h, zero_mul] at this; simp at this
  have h3 := h1.trans h2.symm
  rw [div_eq_div_iff hP0 hP0'] at h3
  exact (mul_left_cancel₀ hA h3).symm

/-- Cochrane (2023), §7.1, p. 215 (under uncertainty): with a state-contingent rate path and
`β = 1/(1+r)`, `E_t(P_t/P_{t+1}) = (1 + r)/(1 + i_t)` in every state. -/
theorem random_expected_ratio {r : ℝ} (hr : -1 < r) {P x : ℕ → Ω → ℝ} {i : ℕ → Ω → ℝ}
    (hF : RFisher 𝔼 (1 + r)⁻¹ P x i) (t : ℕ) (ω : Ω) :
    𝔼.E t (P t * x (t + 1)) ω = (1 + r) / (1 + i t ω) := by
  have h1 : (1 + r) ≠ 0 := by linarith
  have := congrFun (hF t) ω
  simp only [bondPrice, pow_one, Pi.smul_apply, smul_eq_mul] at this
  rw [div_eq_mul_inv, ← this]
  field_simp

/-- Cochrane (2023), §7.1, p. 215 (under uncertainty): **no expected jump where the rate is
unchanged**: if `i_t = r` in state `ω`, then `E_t(P_t/P_{t+1}) = 1` there. -/
theorem random_no_expected_jump {r : ℝ} (hr : -1 < r) {P x : ℕ → Ω → ℝ} {i : ℕ → Ω → ℝ}
    (hF : RFisher 𝔼 (1 + r)⁻¹ P x i) {t : ℕ} {ω : Ω} (hi : i t ω = r) :
    𝔼.E t (P t * x (t + 1)) ω = 1 := by
  rw [random_expected_ratio 𝔼 hr hF t ω, hi, div_self (by linarith)]

/-! ### The counterexample: state-contingent guidance can raise `P_0` -/

/-- Cochrane (2023), §7.1 (counterexample): the announced rates, `r = 1` at every date except
date 1, where the rate is `2` after heads and `1/5` after tails (mean `11/10`). -/
noncomputable def cgRate : ℕ → Bool × Bool → ℝ :=
  fun t ω => if t = 1 then (if ω.1 then 2 else 1 / 5) else 1

/-- Cochrane (2023), §7.1 (counterexample): `1/P_t`: `48/7` at dates 0 and 1, then `32/7` after
heads and `80/7` after tails. -/
noncomputable def cgX : ℕ → Bool × Bool → ℝ :=
  fun t ω => if t ≤ 1 then 48 / 7 else (if ω.1 then 32 / 7 else 80 / 7)

/-- Cochrane (2023), §7.1 (counterexample): the price level `P_t = 1/cgX`. -/
noncomputable def cgP : ℕ → Bool × Bool → ℝ := fun t ω => (cgX t ω)⁻¹

/-- Cochrane (2023), §7.1 (counterexample): `1/P'_t = 8`, the path with no announcement. -/
noncomputable def cgX' : ℕ → Bool × Bool → ℝ := fun _ _ => 8

/-- Cochrane (2023), §7.1 (counterexample): `P'_t = 1/8`. -/
noncomputable def cgP' : ℕ → Bool × Bool → ℝ := fun _ _ => 1 / 8

/-- Cochrane (2023), §7.1 (counterexample): one unit of debt due at date 2, nothing else. -/
noncomputable def cgB : ℕ → ℝ := fun j => if j = 2 then 1 else 0

/-- Cochrane (2023), §7.1 (counterexample): in the coin-flip tree, `E_0` averages the four
states. -/
theorem coin_E0 (f : Bool × Bool → ℝ) (ω : Bool × Bool) :
    ExpectationsFiniteTree.coinSystem.E 0 f ω =
      (f (true, true) + f (true, false) + f (false, true) + f (false, false)) / 4 := by
  have htriv : ∀ a b, ExpectationsFiniteTree.coinTree.info 0 a b := fun a b => by
    change Setoid.ker (ExpectationsFiniteTree.coinObs 0) a b
    rw [Setoid.ker_def]
    simp [ExpectationsFiniteTree.coinObs]
  rw [ExpectationsFiniteTree.coinSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E,
    ExpectationsFiniteTree.coinTree.condE_of_trivial htriv]
  simp [ExpectationsFiniteTree.coinTree, Fintype.sum_prod_type]
  ring

/-- Cochrane (2023), §7.1 (counterexample): from date 1 on, a variable that depends only on the
first flip is known. -/
theorem coin_known {f : Bool × Bool → ℝ} (hf : ∀ ω ω', ω.1 = ω'.1 → f ω = f ω') {t : ℕ}
    (ht : 1 ≤ t) : ExpectationsFiniteTree.coinSystem.E t f = f := by
  funext ω
  rw [ExpectationsFiniteTree.coinSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  refine ExpectationsFiniteTree.coinTree.condE_of_const_on_cell fun ω' h => hf _ _ ?_
  change Setoid.ker (ExpectationsFiniteTree.coinObs t) ω' ω at h
  rw [Setoid.ker_def] at h
  simp only [ExpectationsFiniteTree.coinObs, Prod.mk.injEq, ht, ↓reduceIte] at h
  exact h.1

/-- Cochrane (2023), §7.1 (counterexample): the guidance path is adapted. -/
theorem cg_adapted : ExpectationsFiniteTree.coinSystem.Adapted cgX := by
  intro t
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have : cgX 0 = fun _ => 48 / 7 := by funext ω; simp [cgX]
    rw [this, ExpectationsFiniteTree.coinSystem.const]
  · exact coin_known (fun ω ω' h => by simp only [cgX, h]) ht

/-- Cochrane (2023), §7.1 (counterexample): the guidance price level is adapted. -/
theorem cgP_adapted : ExpectationsFiniteTree.coinSystem.Adapted cgP := by
  intro t
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have : cgP 0 = fun _ => 7 / 48 := by funext ω; simp [cgP, cgX]
    rw [this, ExpectationsFiniteTree.coinSystem.const]
  · exact coin_known (fun ω ω' h => by simp only [cgP, cgX, h]) ht

/-- Cochrane (2023), §7.1 (counterexample): **the guidance path implements the state-contingent
rates**: `Q_t^{(t+1)} = (1/2) E_t(P_t/P_{t+1}) = 1/(1 + i_t)` at every date (`r = 1`, `β = 1/2`). -/
theorem cg_fisher : RFisher ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ cgP cgX cgRate := by
  intro t
  rcases Nat.lt_or_ge t 1 with h0 | h1
  · obtain rfl : t = 0 := by omega
    have : cgP 0 * cgX (0 + 1) = fun _ => 1 := by funext ω; simp [cgP, cgX]
    simp only [bondPrice, pow_one, this, ExpectationsFiniteTree.coinSystem.const]
    funext ω; simp [cgRate]
  · rcases Nat.lt_or_ge t 2 with h2 | h2
    · obtain rfl : t = 1 := by omega
      have hk : ExpectationsFiniteTree.coinSystem.E 1 (cgP 1 * cgX (1 + 1)) =
          cgP 1 * cgX (1 + 1) :=
        coin_known (fun ω ω' h => by simp only [Pi.mul_apply, cgP, cgX, h]) le_rfl
      simp only [bondPrice, pow_one, hk]
      funext ω
      rcases ω with ⟨_ | _, _⟩ <;> simp [cgP, cgX, cgRate] <;> norm_num
    · have : cgP t * cgX (t + 1) = fun _ => 1 := by
        funext ω
        simp only [Pi.mul_apply, cgP, cgX, show ¬ (t ≤ 1) by omega,
          show ¬ (t + 1 ≤ 1) by omega, ↓reduceIte]
        split_ifs <;> norm_num
      simp only [bondPrice, pow_one, this, ExpectationsFiniteTree.coinSystem.const]
      funext ω
      simp [cgRate, show t ≠ 1 by omega]

/-- Cochrane (2023), §7.1 (counterexample): the no-announcement path implements the constant rate
`r = 1`. -/
theorem cg_fisher' : RFisher ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ cgP' cgX'
    (fun _ _ => 1) := by
  intro t
  have : cgP' t * cgX' (t + 1) = fun _ => 1 := by funext ω; simp [cgP', cgX']
  simp only [bondPrice, pow_one, this, ExpectationsFiniteTree.coinSystem.const]
  funext ω; norm_num

/-- Cochrane (2023), §7.1 (counterexample): the surpluses `s_t = 1` have present value `2`
(`β = 1/2`). -/
theorem cg_pv (ω : Bool × Bool) :
    HasSum (fun k => surplusTerm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (fun _ _ => 1) 0 k ω)
      2 := by
  have h := hasSum_geometric_of_lt_one (r := ((1 : ℝ) + 1)⁻¹) (by norm_num) (by norm_num)
  have e : (1 - ((1 : ℝ) + 1)⁻¹)⁻¹ = 2 := by norm_num
  rw [e] at h
  refine h.congr_fun fun k => ?_
  simp [surplusTerm, ExpectationsFiniteTree.coinSystem.const]

/-- Cochrane (2023), §7.1 (counterexample): the guidance path satisfies the date-0 valuation
equation (7.3) with debt `B_{−1}^{(2)} = 1` and surpluses `s_t = 1`: `β² E_0(1/P_2) = 2`. -/
theorem cg_presentValue : PresentValue ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹
    (fun _ j _ => cgB j) cgX (fun _ _ => 1) 0 := by
  intro ω
  refine ⟨(cg_pv ω).summable, ?_⟩
  rw [pvSurplus, (cg_pv ω).tsum_eq]
  have h := hasSum_single (f := fun j => debtTerm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹
    (fun _ j _ => cgB j) cgX 0 j ω) 2 fun j hj => by simp [debtTerm, cgB, hj]
  convert h using 1
  simp only [debtTerm, cgB, ↓reduceIte, one_mul, zero_add, coin_E0, cgX]
  norm_num

/-- Cochrane (2023), §7.1 (counterexample): the no-announcement path satisfies the same date-0
valuation equation: `β² · 8 = 2`. -/
theorem cg_presentValue' : PresentValue ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹
    (fun _ j _ => cgB j) cgX' (fun _ _ => 1) 0 := by
  intro ω
  refine ⟨(cg_pv ω).summable, ?_⟩
  rw [pvSurplus, (cg_pv ω).tsum_eq]
  have h := hasSum_single (f := fun j => debtTerm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹
    (fun _ j _ => cgB j) cgX' 0 j ω) 2 fun j hj => by simp [debtTerm, cgB, hj]
  convert h using 1
  simp only [debtTerm, cgB, ↓reduceIte, one_mul, zero_add]
  rw [show cgX' 2 = fun _ => (8 : ℝ) from rfl, ExpectationsFiniteTree.coinSystem.const]
  norm_num

/-- Cochrane (2023), §7.1, pp. 213–214 (state-contingent guidance): **an announced rise in
the expected rate path can raise `P_0`.** In the coin-flip economy with debt `B_{−1}^{(2)} = 1`,
surpluses `s_t = 1`, `r = 1`: both paths are adapted, positive, implement their rate paths
(`cg_fisher`, `cg_fisher'`) and satisfy (7.3) (`cg_presentValue`, `cg_presentValue'`); the
guidance rates equal `r` except at date 1, where their mean is `11/10 > r`; yet
`P_0 = 7/48 > 1/8 = P'_0` in every state, and `Q_0^{(2)} = 7/24 > 1/4 = (1+r)^{-2}`. -/
theorem cg_counterexample (ω : Bool × Bool) :
    ExpectationsFiniteTree.coinSystem.E 0 (cgRate 1) ω = 11 / 10 ∧ (∀ t, t ≠ 1 → cgRate t ω = 1) ∧
      cgP 0 ω = 7 / 48 ∧ cgP' 0 ω = 1 / 8 ∧ cgP' 0 ω < cgP 0 ω ∧
      bondPrice ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ cgP cgX 0 2 ω = 7 / 24 ∧
      ((1 : ℝ) + 1)⁻¹ ^ 2 <
        bondPrice ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ cgP cgX 0 2 ω := by
  have hQ : bondPrice ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ cgP cgX 0 2 ω = 7 / 24 := by
    rw [bondPrice_eq ExpectationsFiniteTree.coinSystem
      (ExpectationsFiniteTree.finiteTree_pullOut ExpectationsFiniteTree.coinTree) cgP_adapted]
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, zero_add, coin_E0, cgP, cgX]
    norm_num
  refine ⟨?_, fun t ht => by simp [cgRate, ht], by simp [cgP, cgX], rfl,
    by simp [cgP, cgP', cgX]; norm_num, hQ, by rw [hQ]; norm_num⟩
  rw [coin_E0]
  simp [cgRate]
  norm_num

end Cochrane.LongTermDebtDynamics.TidyR5RandomGuidance
