/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.AssetPricing

/-!
# The intertemporal budget constraint (Proposition 2.1)

Woodford (2003), *Interest and Prices*, Chapter 2, §1.1, pp. 67–70, eqs. (1.7), (1.9)–(1.13),
(1.18)–(1.19), and Appendix A.1, pp. 627–628.

Write `X_t = P_tC_t + Δ_tM_t` (spending, including the opportunity cost of money) and
`Z_t = P_tY_t − T_t` (after-tax nonfinancial income). The flow constraint (1.7) is
`X_t + E_t[Q_{t,t+1}W_{t+1}] ≤ W_t + Z_t`, the borrowing limit (1.9) is
`W_{t+1} ≥ −∑_{n ≥ 0} E_{t+1}[Q_{t+1,t+1+n} Z_{t+1+n}]`, and the intertemporal constraint (1.13)
at date `t` is `∑_n E_t[Q_{t,t+n}X_{t+n}] ≤ W_t + ∑_n E_t[Q_{t,t+n}Z_{t+n}]`.

## Hypotheses made explicit (survey error E20)

The book's (1.10), `∑ E_tQ_{t,T}(P_TY_T − T_T) < ∞`, bounds a possibly signed series, and its
proof interchanges `E_t` with infinite sums. Here the income stream is assumed
*absolutely* summable in the sense `IncomeSummable`: `∑_n E_t[Q_{t,t+n}|Z_{t+n}|] < ∞` at every
date and state; and `E_t` satisfies conditional monotone convergence (`MonotoneConvergence`,
true for perfect foresight and every finite tree). For the sufficiency half the spending series
`∑_n E_t[Q_{t,t+n}X_{t+n}]` must converge at every date and state, not only at date 0: in the
abstract framework (as with genuine conditional expectations, where it holds only almost surely)
this does not follow from the date-0 constraint. The necessity half proves it, so the
equivalence `prop_2_1_iff` is exact.

## Main results

* `telescope`: the exact finite-horizon identity behind A.1.
* `ibc_of_flow` (necessity, (1.13) at every date) and `exists_wealth_of_ibc` (sufficiency, the
  A.1 construction `W_t := ∑E_tQ X − ∑E_tQ Z` written out in full).
* `prop_2_1_iff`, `prop_2_1`: Proposition 2.1, both directions.
* `flow_eq_and_tvc_of_ibc_eq`, `ibc_eq_of_flow_eq_and_tvc`, `ibc_eq_iff_flow_eq_and_tvc`:
  (1.13) with equality ⟺ the flow constraint with equality plus the transversality condition
  (1.18) `lim_T E_t[Q_{t,T}W_T] = 0`; (1.19) is the summability of the spending series.
-/

namespace Woodford.PriceLevelDetermination.IntertemporalBudget

open Filter Topology AssetPricing

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), eq. (1.7), p. 67: the flow budget constraint
`X_t + E_t[Q_{t,t+1}W_{t+1}] ≤ W_t + Z_t` at every date. -/
def FlowConstraint (q X Z W : ℕ → Ω → ℝ) : Prop :=
  ∀ t, X t + 𝔼.E t (q t * W (t + 1)) ≤ W t + Z t

/-- Woodford (2003), p. 70: the flow budget constraint holds with equality at every date. -/
def FlowEq (q X Z W : ℕ → Ω → ℝ) : Prop :=
  ∀ t, X t + 𝔼.E t (q t * W (t + 1)) = W t + Z t

/-- Woodford (2003), eq. (1.9), p. 67: the borrowing limit
`W_{t+1} ≥ −∑_{T ≥ t+1} E_{t+1}[Q_{t+1,T}(P_TY_T − T_T)]` in every state. -/
def BorrowingLimit (q Z W : ℕ → Ω → ℝ) : Prop :=
  ∀ t, -pv 𝔼 q Z (t + 1) ≤ W (t + 1)

/-- Woodford (2003), eq. (1.10), p. 68, in the absolute form needed by the proof (survey E20):
`∑_n E_t[Q_{t,t+n}|Z_{t+n}|] < ∞` at every date and in every state. -/
def IncomeSummable (q Z : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Summable fun n => 𝔼.E t (sdf q t n * fun ω' => |Z (t + n) ω'|) ω

/-- Woodford (2003), eq. (1.19), p. 70: the spending series `∑_n E_t[Q_{t,t+n}X_{t+n}]`
converges at every date and in every state. -/
def SpendingSummable (q X : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Summable fun n => 𝔼.E t (sdf q t n * X (t + n)) ω

/-- Woodford (2003), eq. (1.18), p. 70: the transversality condition
`lim_{T→∞} E_t[Q_{t,T}W_T] = 0` looking forward from date `t`. -/
def TVC (q W : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, Tendsto (fun N => 𝔼.E t (sdf q t N * W (t + N)) ω) atTop (𝓝 0)

/-- Woodford (2003), eq. (1.7), p. 67: the slack in the date-`t` flow constraint,
`W_t + Z_t − X_t − E_t[Q_{t,t+1}W_{t+1}]`. -/
def slack (q X Z W : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  W t + Z t - X t - 𝔼.E t (q t * W (t + 1))

/-! ### Finite-horizon telescoping -/

/-- Woodford (2003), p. 627 (first display of A.1), as an exact identity: for adapted wealth,
`W_t + ∑_{n<N} E_t[Q Z] − ∑_{n<N} E_t[Q X] − E_t[Q_{t,t+N}W_{t+N}]` equals the discounted sum
of flow-constraint slacks `∑_{n<N} E_t[Q_{t,t+n} s_{t+n}]`. -/
theorem telescope (hP : 𝔼.PullOut) {q X Z W : ℕ → Ω → ℝ}
    (hq : ∀ s, 𝔼.E (s + 1) (q s) = q s) {t : ℕ} (hW : 𝔼.E t (W t) = W t) (N : ℕ) (ω : Ω) :
    W t ω + ∑ n ∈ Finset.range N, 𝔼.E t (sdf q t n * Z (t + n)) ω
      - ∑ n ∈ Finset.range N, 𝔼.E t (sdf q t n * X (t + n)) ω
      - 𝔼.E t (sdf q t N * W (t + N)) ω
      = ∑ n ∈ Finset.range N, 𝔼.E t (sdf q t n * slack 𝔼 q X Z W (t + n)) ω := by
  induction N with
  | zero => simp [hW]
  | succ N ih =>
    have key : 𝔼.E t (sdf q t N * slack 𝔼 q X Z W (t + N)) =
        𝔼.E t (sdf q t N * W (t + N)) + 𝔼.E t (sdf q t N * Z (t + N)) -
          𝔼.E t (sdf q t N * X (t + N)) - 𝔼.E t (sdf q t (N + 1) * W (t + (N + 1))) := by
      simp only [slack, mul_sub, mul_add, map_sub, map_add]
      rw [E_sdf_mul_E 𝔼 hP hq, ← mul_assoc, ← sdf_succ, add_assoc]
    have k := congrFun key ω
    simp only [Pi.add_apply, Pi.sub_apply] at k
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ← ih, k]
    ring

/-! ### Positive and negative parts of income -/

/-- Woodford (2003), p. 628 (survey E20): the positive part `max Z 0` of income. -/
def posPart (Z : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun s ω => max (Z s ω) 0

/-- Woodford (2003), p. 628 (survey E20): the negative part `max (−Z) 0` of income. -/
def negPart (Z : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun s ω => max (-Z s ω) 0

/-- Woodford (2003), p. 628: `Z = Z⁺ − Z⁻`. -/
theorem posPart_sub_negPart (Z : ℕ → Ω → ℝ) (s : ℕ) : posPart Z s - negPart Z s = Z s := by
  funext ω
  simp [posPart, negPart, max_zero_sub_max_neg_zero_eq_self]

/-- Woodford (2003), p. 628: absolutely summable income has summable positive-part present
values at every date and state. -/
theorem summable_posPart {q Z : ℕ → Ω → ℝ} (hq0 : ∀ s ω, 0 ≤ q s ω)
    (hZ : IncomeSummable 𝔼 q Z) (t : ℕ) (ω : Ω) :
    Summable fun n => 𝔼.E t (sdf q t n * posPart Z (t + n)) ω := by
  refine Summable.of_nonneg_of_le (fun n => E_nonneg 𝔼 (fun ω' => mul_nonneg
    (sdf_nonneg hq0 t n ω') (le_max_right _ _)) ω) (fun n => ?_) (hZ t ω)
  refine 𝔼.mono t (fun ω' => ?_) ω
  simp only [Pi.mul_apply, posPart]
  exact mul_le_mul_of_nonneg_left (max_le (le_abs_self _) (abs_nonneg _))
    (sdf_nonneg hq0 t n ω')

/-- Woodford (2003), p. 628: absolutely summable income has summable negative-part present
values at every date and state. -/
theorem summable_negPart {q Z : ℕ → Ω → ℝ} (hq0 : ∀ s ω, 0 ≤ q s ω)
    (hZ : IncomeSummable 𝔼 q Z) (t : ℕ) (ω : Ω) :
    Summable fun n => 𝔼.E t (sdf q t n * negPart Z (t + n)) ω := by
  refine Summable.of_nonneg_of_le (fun n => E_nonneg 𝔼 (fun ω' => mul_nonneg
    (sdf_nonneg hq0 t n ω') (le_max_right _ _)) ω) (fun n => ?_) (hZ t ω)
  refine 𝔼.mono t (fun ω' => ?_) ω
  simp only [Pi.mul_apply, negPart]
  exact mul_le_mul_of_nonneg_left (max_le (neg_le_abs _) (abs_nonneg _))
    (sdf_nonneg hq0 t n ω')

/-- Woodford (2003), p. 628: the present-value terms of `Z` split as those of `Z⁺` minus
those of `Z⁻`. -/
theorem E_sdf_mul_split (q Z : ℕ → Ω → ℝ) (t n : ℕ) :
    𝔼.E t (sdf q t n * Z (t + n)) =
      𝔼.E t (sdf q t n * posPart Z (t + n)) - 𝔼.E t (sdf q t n * negPart Z (t + n)) := by
  rw [← map_sub, ← mul_sub, posPart_sub_negPart]

/-- Woodford (2003), eq. (1.10), p. 68: absolutely summable income has a summable present-value
series at every date and state. -/
theorem summable_income {q Z : ℕ → Ω → ℝ} (hq0 : ∀ s ω, 0 ≤ q s ω)
    (hZ : IncomeSummable 𝔼 q Z) (t : ℕ) (ω : Ω) :
    Summable fun n => 𝔼.E t (sdf q t n * Z (t + n)) ω := by
  have h := (summable_posPart 𝔼 hq0 hZ t ω).sub (summable_negPart 𝔼 hq0 hZ t ω)
  refine h.congr fun n => ?_
  rw [E_sdf_mul_split 𝔼 q Z t n]
  rfl

/-- Woodford (2003), p. 627 (the borrowing limit combined with the tower property), for signed
income under `IncomeSummable`:
`E_t[Q_{t,t+N} ∑_n E_{t+N}[Q_{t+N,t+N+n}Z_{t+N+n}]] = ∑_m E_t[Q_{t,t+N+m}Z_{t+N+m}]`. -/
theorem hasSum_E_sdf_mul_pv_income (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut)
    {q Z : ℕ → Ω → ℝ} (hq : ∀ s, 𝔼.E (s + 1) (q s) = q s) (hq0 : ∀ s ω, 0 ≤ q s ω)
    (hZ : IncomeSummable 𝔼 q Z) (t N : ℕ) (ω : Ω) :
    HasSum (fun m => 𝔼.E t (sdf q t (m + N) * Z (t + (m + N))) ω)
      (𝔼.E t (sdf q t N * pv 𝔼 q Z (t + N)) ω) := by
  have hp := hasSum_E_sdf_mul_pv 𝔼 hMC hP hq hq0 (Y := posPart Z)
    (fun _ _ => le_max_right _ _) t N (summable_posPart 𝔼 hq0 hZ (t + N)) ω
  have hn := hasSum_E_sdf_mul_pv 𝔼 hMC hP hq hq0 (Y := negPart Z)
    (fun _ _ => le_max_right _ _) t N (summable_negPart 𝔼 hq0 hZ (t + N)) ω
  have hpv : pv 𝔼 q Z (t + N) = pv 𝔼 q (posPart Z) (t + N) - pv 𝔼 q (negPart Z) (t + N) := by
    funext ω'
    simp only [pv, Pi.sub_apply]
    rw [← (summable_posPart 𝔼 hq0 hZ (t + N) ω').tsum_sub
      (summable_negPart 𝔼 hq0 hZ (t + N) ω')]
    refine tsum_congr fun n => ?_
    rw [E_sdf_mul_split 𝔼 q Z (t + N) n]
    rfl
  rw [hpv, mul_sub, map_sub]
  convert hp.sub hn using 1
  funext m
  rw [E_sdf_mul_split 𝔼 q Z t (m + N)]
  rfl

/-- Woodford (2003), p. 628 (A.1 construction): a present value computed with date-`t`
expectations is itself known at `t`, for a nonnegative stream summable at `t`. -/
theorem E_pv_self (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut) {q Y : ℕ → Ω → ℝ}
    (hq : ∀ s, 𝔼.E (s + 1) (q s) = q s) (hq0 : ∀ s ω, 0 ≤ q s ω) (hY : ∀ s ω, 0 ≤ Y s ω)
    (t : ℕ) (hs : ∀ ω, Summable fun n => 𝔼.E t (sdf q t n * Y (t + n)) ω) :
    𝔼.E t (pv 𝔼 q Y t) = pv 𝔼 q Y t := by
  funext ω
  have h := hasSum_E_sdf_mul_pv 𝔼 hMC hP hq hq0 hY t 0 hs ω
  simp only [sdf_zero, one_mul, add_zero] at h
  exact h.tsum_eq.symm

/-- Woodford (2003), p. 628: the present value of signed income is known at `t`. -/
theorem E_pv_income_self (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut) {q Z : ℕ → Ω → ℝ}
    (hq : ∀ s, 𝔼.E (s + 1) (q s) = q s) (hq0 : ∀ s ω, 0 ≤ q s ω)
    (hZ : IncomeSummable 𝔼 q Z) (t : ℕ) : 𝔼.E t (pv 𝔼 q Z t) = pv 𝔼 q Z t := by
  funext ω
  have h := hasSum_E_sdf_mul_pv_income 𝔼 hMC hP hq hq0 hZ t 0 ω
  simp only [sdf_zero, one_mul, add_zero] at h
  exact h.tsum_eq.symm

/-! ### Necessity: the flow constraints and borrowing limits imply (1.13) -/

/-- Woodford (2003), Proposition 2.1 (necessity) and eq. (1.13), pp. 68–69, proof A.1,
pp. 627–628: if wealth is adapted and satisfies the flow constraints (1.7) and the borrowing
limits (1.9), spending is nonnegative and income absolutely summable, then at every date `t` and
in every state the spending series converges and
`∑_n E_t[Q_{t,t+n}X_{t+n}] ≤ W_t + ∑_n E_t[Q_{t,t+n}Z_{t+n}]`. -/
theorem ibc_of_flow (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut) {q X Z W : ℕ → Ω → ℝ}
    (hq : ∀ s, 𝔼.E (s + 1) (q s) = q s) (hq0 : ∀ s ω, 0 ≤ q s ω) (hX0 : ∀ s ω, 0 ≤ X s ω)
    (hZ : IncomeSummable 𝔼 q Z) (hW : 𝔼.Adapted W) (hflow : FlowConstraint 𝔼 q X Z W)
    (hbl : BorrowingLimit 𝔼 q Z W) (t : ℕ) (ω : Ω) :
    Summable (fun n => 𝔼.E t (sdf q t n * X (t + n)) ω) ∧
      pv 𝔼 q X t ω ≤ W t ω + pv 𝔼 q Z t ω := by
  set x : ℕ → ℝ := fun n => 𝔼.E t (sdf q t n * X (t + n)) ω with hx
  set z : ℕ → ℝ := fun n => 𝔼.E t (sdf q t n * Z (t + n)) ω with hz
  have hx0 : ∀ n, 0 ≤ x n := fun n =>
    E_nonneg 𝔼 (fun ω' => mul_nonneg (sdf_nonneg hq0 t n ω') (hX0 _ ω')) ω
  have hzs : Summable z := summable_income 𝔼 hq0 hZ t ω
  -- the bound for horizons `N + 1`
  have hbound : ∀ N, ∑ n ∈ Finset.range (N + 1), x n ≤ W t ω + ∑' n, z n := by
    intro N
    have htel := telescope 𝔼 hP (X := X) (Z := Z) hq (hW t) (N + 1) ω
    have hsl : 0 ≤ ∑ n ∈ Finset.range (N + 1),
        𝔼.E t (sdf q t n * slack 𝔼 q X Z W (t + n)) ω := by
      refine Finset.sum_nonneg fun n _ => E_nonneg 𝔼 (fun ω' => mul_nonneg
        (sdf_nonneg hq0 t n ω') ?_) ω
      have := hflow (t + n) ω'
      simp only [slack, Pi.add_apply, Pi.sub_apply] at this ⊢
      linarith
    have hWlow : -𝔼.E t (sdf q t (N + 1) * pv 𝔼 q Z (t + (N + 1))) ω ≤
        𝔼.E t (sdf q t (N + 1) * W (t + (N + 1))) ω := by
      have hle : sdf q t (N + 1) * (-pv 𝔼 q Z (t + (N + 1))) ≤
          sdf q t (N + 1) * W (t + (N + 1)) := fun ω' => by
        have := hbl (t + N) ω'
        rw [show t + N + 1 = t + (N + 1) by omega] at this
        exact mul_le_mul_of_nonneg_left this (sdf_nonneg hq0 t (N + 1) ω')
      have := 𝔼.mono t hle ω
      rwa [mul_neg, map_neg, Pi.neg_apply] at this
    have htail := (hasSum_E_sdf_mul_pv_income 𝔼 hMC hP hq hq0 hZ t (N + 1) ω).tsum_eq
    have hsplit := hzs.sum_add_tsum_nat_add (N + 1)
    have hzz : ∑' m, z (m + (N + 1)) =
        𝔼.E t (sdf q t (N + 1) * pv 𝔼 q Z (t + (N + 1))) ω := by
      rw [← htail]
    rw [← hsplit, hzz]
    simp only [hx, hz] at htel ⊢
    linarith
  have hbound' : ∀ N, ∑ n ∈ Finset.range N, x n ≤ W t ω + ∑' n, z n := fun N =>
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (Nat.le_succ N))
      (fun n _ _ => hx0 n)).trans (hbound N)
  have hxs : Summable x := summable_of_sum_range_le hx0 hbound'
  exact ⟨hxs, hxs.tsum_le_of_sum_range_le hbound'⟩

/-! ### Sufficiency: the A.1 construction -/

/-- Woodford (2003), p. 628 (A.1 construction): the wealth plan that makes (1.13) hold with
equality at every date `t ≥ 1`, `W_t = ∑E_tQ X − ∑E_tQ Z`, with given initial wealth `W_0`. -/
noncomputable def wealthPlan (q X Z : ℕ → Ω → ℝ) (W0 : Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => if t = 0 then W0 else pv 𝔼 q X t - pv 𝔼 q Z t

/-- Woodford (2003), p. 628: `E_t[Q_{t,t+1}(∑E_{t+1}Q X − ∑E_{t+1}Q Z)]
= (∑E_tQ X − X_t) − (∑E_tQ Z − Z_t)` for adapted `X`, `Z`. -/
theorem E_q_mul_wealthPlan (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut)
    {q X Z : ℕ → Ω → ℝ} (hq : ∀ s, 𝔼.E (s + 1) (q s) = q s) (hq0 : ∀ s ω, 0 ≤ q s ω)
    (hX0 : ∀ s ω, 0 ≤ X s ω) (hXad : 𝔼.Adapted X) (hZad : 𝔼.Adapted Z)
    (hZ : IncomeSummable 𝔼 q Z) (hXs : SpendingSummable 𝔼 q X) (W0 : Ω → ℝ) (t : ℕ)
    (ω : Ω) :
    𝔼.E t (q t * wealthPlan 𝔼 q X Z W0 (t + 1)) ω =
      (pv 𝔼 q X t ω - X t ω) - (pv 𝔼 q Z t ω - Z t ω) := by
  have hX1 := hasSum_E_sdf_mul_pv 𝔼 hMC hP hq hq0 hX0 t 1 (hXs (t + 1)) ω
  have hZ1 := hasSum_E_sdf_mul_pv_income 𝔼 hMC hP hq hq0 hZ t 1 ω
  rw [sdf_one] at hX1 hZ1
  have hW1 : wealthPlan 𝔼 q X Z W0 (t + 1) = pv 𝔼 q X (t + 1) - pv 𝔼 q Z (t + 1) := by
    simp [wealthPlan]
  rw [hW1, mul_sub, map_sub, Pi.sub_apply, ← hX1.tsum_eq, ← hZ1.tsum_eq]
  have ex := (hXs t ω).tsum_eq_zero_add
  have ez := (summable_income 𝔼 hq0 hZ t ω).tsum_eq_zero_add
  simp only [sdf_zero, one_mul, add_zero, hXad t, hZad t] at ex ez
  simp only [pv]
  rw [ex, ez]
  ring

/-- Woodford (2003), Proposition 2.1 (sufficiency), proof A.1, p. 628, written out in full:
given adapted nonnegative spending whose present value converges at every date and state,
absolutely summable adapted income, and initial wealth `W_0` known at date 0 satisfying the
date-0 intertemporal constraint (1.12), the wealth plan `wealthPlan` starts at `W_0`, is
adapted, satisfies every flow constraint (1.7) (with equality from date 1 on) and every
borrowing limit (1.9). -/
theorem exists_wealth_of_ibc (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut)
    {q X Z : ℕ → Ω → ℝ} (hq : ∀ s, 𝔼.E (s + 1) (q s) = q s) (hq0 : ∀ s ω, 0 ≤ q s ω)
    (hX0 : ∀ s ω, 0 ≤ X s ω) (hXad : 𝔼.Adapted X) (hZad : 𝔼.Adapted Z)
    (hZ : IncomeSummable 𝔼 q Z) (hXs : SpendingSummable 𝔼 q X) {W0 : Ω → ℝ}
    (hW0 : 𝔼.E 0 W0 = W0) (hibc : ∀ ω, pv 𝔼 q X 0 ω ≤ W0 ω + pv 𝔼 q Z 0 ω) :
    let W := wealthPlan 𝔼 q X Z W0
    W 0 = W0 ∧ 𝔼.Adapted W ∧ FlowConstraint 𝔼 q X Z W ∧ BorrowingLimit 𝔼 q Z W ∧
      ∀ t, X (t + 1) + 𝔼.E (t + 1) (q (t + 1) * W (t + 2)) = W (t + 1) + Z (t + 1) := by
  intro W
  have hWs : ∀ t, W (t + 1) = pv 𝔼 q X (t + 1) - pv 𝔼 q Z (t + 1) := fun t => by
    simp [W, wealthPlan]
  have hW0' : W 0 = W0 := by simp [W, wealthPlan]
  refine ⟨hW0', ?_, ?_, ?_, ?_⟩
  · intro t
    cases t with
    | zero => rw [hW0', hW0]
    | succ t =>
      rw [hWs t, map_sub, E_pv_self 𝔼 hMC hP hq hq0 hX0 (t + 1) (hXs (t + 1)),
        E_pv_income_self 𝔼 hMC hP hq hq0 hZ (t + 1)]
  · intro t ω
    have h := E_q_mul_wealthPlan 𝔼 hMC hP hq hq0 hX0 hXad hZad hZ hXs W0 t ω
    simp only [Pi.add_apply]
    rw [h]
    cases t with
    | zero =>
      rw [hW0']
      have := hibc ω
      linarith
    | succ t =>
      rw [hWs t, Pi.sub_apply]
      linarith
  · intro t ω
    rw [hWs t, Pi.sub_apply, Pi.neg_apply]
    have : 0 ≤ pv 𝔼 q X (t + 1) ω := tsum_nonneg fun n =>
      E_nonneg 𝔼 (fun ω' => mul_nonneg (sdf_nonneg hq0 _ n ω') (hX0 _ ω')) ω
    linarith
  · intro t
    funext ω
    have h := E_q_mul_wealthPlan 𝔼 hMC hP hq hq0 hX0 hXad hZad hZ hXs W0 (t + 1) ω
    simp only [Pi.add_apply]
    rw [h, hWs t, Pi.sub_apply]
    ring

/-- Woodford (2003), Proposition 2.1, pp. 68–69, with proof A.1, pp. 627–628, both directions,
under the explicit hypotheses of survey E20: a portfolio (wealth) plan starting from `W_0` and
satisfying every flow constraint (1.7) and every borrowing limit (1.9) exists iff the spending
series converges at every date and state and the date-0 intertemporal constraint (1.12) holds. -/
theorem prop_2_1_iff (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut)
    {q X Z : ℕ → Ω → ℝ} (hq : ∀ s, 𝔼.E (s + 1) (q s) = q s) (hq0 : ∀ s ω, 0 ≤ q s ω)
    (hX0 : ∀ s ω, 0 ≤ X s ω) (hXad : 𝔼.Adapted X) (hZad : 𝔼.Adapted Z)
    (hZ : IncomeSummable 𝔼 q Z) {W0 : Ω → ℝ} (hW0 : 𝔼.E 0 W0 = W0) :
    (∃ W : ℕ → Ω → ℝ, W 0 = W0 ∧ 𝔼.Adapted W ∧ FlowConstraint 𝔼 q X Z W ∧
        BorrowingLimit 𝔼 q Z W) ↔
      SpendingSummable 𝔼 q X ∧ ∀ ω, pv 𝔼 q X 0 ω ≤ W0 ω + pv 𝔼 q Z 0 ω := by
  constructor
  · rintro ⟨W, h0, hW, hflow, hbl⟩
    refine ⟨fun t ω => (ibc_of_flow 𝔼 hMC hP hq hq0 hX0 hZ hW hflow hbl t ω).1, fun ω => ?_⟩
    have := (ibc_of_flow 𝔼 hMC hP hq hq0 hX0 hZ hW hflow hbl 0 ω).2
    rwa [h0] at this
  · rintro ⟨hXs, hibc⟩
    obtain ⟨h0, hW, hflow, hbl, -⟩ :=
      exists_wealth_of_ibc 𝔼 hMC hP hq hq0 hX0 hXad hZad hZ hXs hW0 hibc
    exact ⟨_, h0, hW, hflow, hbl⟩

/-- Woodford (2003), Proposition 2.1, pp. 68–69, in the book's variables: with
`X_t = P_tC_t + Δ_tM_t` and `Z_t = P_tY_t − T_t`, where `P ≥ 0`, `C, M ≥ 0`, `1 + i_t > 0` and
`i_t ≥ i^m_t` (1.11), a feasible portfolio plan (flow constraints (1.7) and borrowing limits
(1.9)) exists iff (1.12) holds and the spending series converges at every date and state. -/
theorem prop_2_1 (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut)
    {q P C M Y Tx i im : ℕ → Ω → ℝ} (hq : ∀ s, 𝔼.E (s + 1) (q s) = q s)
    (hq0 : ∀ s ω, 0 ≤ q s ω) (hP0 : ∀ s ω, 0 ≤ P s ω) (hC0 : ∀ s ω, 0 ≤ C s ω)
    (hM0 : ∀ s ω, 0 ≤ M s ω) (hi : ∀ s ω, 0 < 1 + i s ω) (h111 : ∀ s ω, im s ω ≤ i s ω)
    (hXad : 𝔼.Adapted fun s => P s * C s + delta i im s * M s)
    (hZad : 𝔼.Adapted fun s => P s * Y s - Tx s)
    (hZ : IncomeSummable 𝔼 q fun s => P s * Y s - Tx s) {W0 : Ω → ℝ}
    (hW0 : 𝔼.E 0 W0 = W0) :
    (∃ W : ℕ → Ω → ℝ, W 0 = W0 ∧ 𝔼.Adapted W ∧
        FlowConstraint 𝔼 q (fun s => P s * C s + delta i im s * M s)
          (fun s => P s * Y s - Tx s) W ∧
        BorrowingLimit 𝔼 q (fun s => P s * Y s - Tx s) W) ↔
      SpendingSummable 𝔼 q (fun s => P s * C s + delta i im s * M s) ∧
        ∀ ω, pv 𝔼 q (fun s => P s * C s + delta i im s * M s) 0 ω ≤
          W0 ω + pv 𝔼 q (fun s => P s * Y s - Tx s) 0 ω := by
  have hX0 : ∀ s ω, 0 ≤ (fun s => P s * C s + delta i im s * M s) s ω := fun s ω => by
    simp only [Pi.add_apply, Pi.mul_apply]
    exact add_nonneg (mul_nonneg (hP0 s ω) (hC0 s ω))
      (mul_nonneg ((delta_nonneg_iff (hi s ω)).mpr (h111 s ω)) (hM0 s ω))
  exact prop_2_1_iff 𝔼 hMC hP hq hq0 hX0 hXad hZad hZ hW0

/-! ### (1.13) with equality, the flow constraint with equality, and the TVC (1.18) -/

/-- Woodford (2003), p. 70 ((1.13) with equality ⟹ (1.18) and the flow constraint with
equality): if the date-`t` constraint (1.13) holds with equality in every state, then the flow
constraint holds with equality at `t`, every later slack has zero discounted expectation
`E_t[Q_{t,t+n}s_{t+n}] = 0` (the flow constraint binds almost surely), and the transversality
condition (1.18) holds. -/
theorem flow_eq_and_tvc_of_ibc_eq (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut)
    {q X Z W : ℕ → Ω → ℝ} (hq : ∀ s, 𝔼.E (s + 1) (q s) = q s) (hq0 : ∀ s ω, 0 ≤ q s ω)
    (hX0 : ∀ s ω, 0 ≤ X s ω) (hXad : 𝔼.Adapted X) (hZad : 𝔼.Adapted Z)
    (hZ : IncomeSummable 𝔼 q Z) (hW : 𝔼.Adapted W) (hflow : FlowConstraint 𝔼 q X Z W)
    (hbl : BorrowingLimit 𝔼 q Z W) {t : ℕ}
    (heq : ∀ ω, pv 𝔼 q X t ω = W t ω + pv 𝔼 q Z t ω) :
    slack 𝔼 q X Z W t = 0 ∧
      (∀ n ω, 𝔼.E t (sdf q t n * slack 𝔼 q X Z W (t + n)) ω = 0) ∧ TVC 𝔼 q W t := by
  -- the core estimate, state by state
  have core : ∀ ω, (∀ n, 𝔼.E t (sdf q t n * slack 𝔼 q X Z W (t + n)) ω = 0) ∧
      Tendsto (fun N => 𝔼.E t (sdf q t N * W (t + N)) ω) atTop (𝓝 0) := by
    intro ω
    set x : ℕ → ℝ := fun n => 𝔼.E t (sdf q t n * X (t + n)) ω with hx
    set z : ℕ → ℝ := fun n => 𝔼.E t (sdf q t n * Z (t + n)) ω with hz
    set e : ℕ → ℝ := fun n => 𝔼.E t (sdf q t n * slack 𝔼 q X Z W (t + n)) ω with he
    set w : ℕ → ℝ := fun N => 𝔼.E t (sdf q t N * W (t + N)) ω with hw
    have hxs : Summable x := (ibc_of_flow 𝔼 hMC hP hq hq0 hX0 hZ hW hflow hbl t ω).1
    have hzs : Summable z := summable_income 𝔼 hq0 hZ t ω
    have he0 : ∀ n, 0 ≤ e n := fun n => E_nonneg 𝔼 (fun ω' => mul_nonneg
      (sdf_nonneg hq0 t n ω') (by
        have := hflow (t + n) ω'
        simp only [slack, Pi.add_apply, Pi.sub_apply] at this ⊢
        linarith)) ω
    -- g_N := w_N + tail_N(z) ≥ 0
    have hg0 : ∀ N, 0 ≤ w N + ∑' m, z (m + N) := by
      intro N
      cases N with
      | zero =>
        simp only [hw, hz, sdf_zero, one_mul, add_zero, hW t]
        have := heq ω
        have hpx : 0 ≤ pv 𝔼 q X t ω := tsum_nonneg fun n =>
          E_nonneg 𝔼 (fun ω' => mul_nonneg (sdf_nonneg hq0 _ n ω') (hX0 _ ω')) ω
        simp only [pv] at this hpx
        linarith
      | succ N =>
        have htail := (hasSum_E_sdf_mul_pv_income 𝔼 hMC hP hq hq0 hZ t (N + 1) ω).tsum_eq
        have hle : sdf q t (N + 1) * (-pv 𝔼 q Z (t + (N + 1))) ≤
            sdf q t (N + 1) * W (t + (N + 1)) := fun ω' => by
          have := hbl (t + N) ω'
          rw [show t + N + 1 = t + (N + 1) by omega] at this
          exact mul_le_mul_of_nonneg_left this (sdf_nonneg hq0 t (N + 1) ω')
        have := 𝔼.mono t hle ω
        rw [mul_neg, map_neg, Pi.neg_apply] at this
        simp only [hw, hz]
        rw [htail]
        linarith
    -- the identity ∑_{n<N} e_n + g_N = tail_N(x)
    have hid : ∀ N, ∑ n ∈ Finset.range N, e n + (w N + ∑' m, z (m + N)) = ∑' m, x (m + N) := by
      intro N
      have htel := telescope 𝔼 hP (X := X) (Z := Z) hq (hW t) N ω
      have hsx := hxs.sum_add_tsum_nat_add N
      have hsz := hzs.sum_add_tsum_nat_add N
      have h := heq ω
      simp only [pv] at h
      simp only [hx, hz, he, hw] at htel hsx hsz ⊢
      linarith
    have htx : Tendsto (fun N => ∑' m, x (m + N)) atTop (𝓝 0) := tendsto_sum_nat_add x
    have htz : Tendsto (fun N => ∑' m, z (m + N)) atTop (𝓝 0) := tendsto_sum_nat_add z
    have hezero : ∀ n, e n = 0 := by
      intro n
      have hle : ∀ N, n < N → e n ≤ ∑' m, x (m + N) := by
        intro N hN
        rw [← hid N]
        have h1 : e n ≤ ∑ k ∈ Finset.range N, e k :=
          Finset.single_le_sum (fun k _ => he0 k) (Finset.mem_range.mpr hN)
        linarith [hg0 N]
      have : e n ≤ 0 := ge_of_tendsto htx
        (Filter.eventually_atTop.mpr ⟨n + 1, fun N hN => hle N (by omega)⟩)
      exact le_antisymm this (he0 n)
    refine ⟨hezero, ?_⟩
    have hw_eq : w = fun N => ∑' m, x (m + N) - ∑' m, z (m + N) := by
      funext N
      have := hid N
      rw [Finset.sum_eq_zero fun n _ => hezero n] at this
      linarith
    rw [hw_eq]
    simpa using htx.sub htz
  refine ⟨?_, fun n ω => (core ω).1 n, fun ω => (core ω).2⟩
  funext ω
  have h0 := (core ω).1 0
  simp only [sdf_zero, one_mul, add_zero] at h0
  have had : 𝔼.E t (slack 𝔼 q X Z W t) = slack 𝔼 q X Z W t := by
    simp only [slack, map_sub, map_add, hW t, hZad t, hXad t, ExpectationSystem.E_E_self]
  rw [had] at h0
  exact h0

/-- Woodford (2003), p. 70 (the converse): if the flow constraint holds with equality at every
date from `t` on and the transversality condition (1.18) holds at `t`, then the spending series
converges at `t` ((1.19)) and (1.13) holds with equality at `t` in every state. -/
theorem ibc_eq_of_flow_eq_and_tvc (hP : 𝔼.PullOut) {q X Z W : ℕ → Ω → ℝ}
    (hq : ∀ s, 𝔼.E (s + 1) (q s) = q s) (hq0 : ∀ s ω, 0 ≤ q s ω) (hX0 : ∀ s ω, 0 ≤ X s ω)
    (hZ : IncomeSummable 𝔼 q Z) {t : ℕ} (hW : 𝔼.E t (W t) = W t)
    (hfeq : ∀ n, slack 𝔼 q X Z W (t + n) = 0) (htvc : TVC 𝔼 q W t) (ω : Ω) :
    Summable (fun n => 𝔼.E t (sdf q t n * X (t + n)) ω) ∧
      pv 𝔼 q X t ω = W t ω + pv 𝔼 q Z t ω := by
  set x : ℕ → ℝ := fun n => 𝔼.E t (sdf q t n * X (t + n)) ω with hx
  set z : ℕ → ℝ := fun n => 𝔼.E t (sdf q t n * Z (t + n)) ω with hz
  have hzs : Summable z := summable_income 𝔼 hq0 hZ t ω
  have hx0 : ∀ n, 0 ≤ x n := fun n =>
    E_nonneg 𝔼 (fun ω' => mul_nonneg (sdf_nonneg hq0 t n ω') (hX0 _ ω')) ω
  have hpart : ∀ N, ∑ n ∈ Finset.range N, x n =
      W t ω + ∑ n ∈ Finset.range N, z n - 𝔼.E t (sdf q t N * W (t + N)) ω := by
    intro N
    have htel := telescope 𝔼 hP (X := X) (Z := Z) hq hW N ω
    simp only [hfeq, mul_zero, map_zero, Pi.zero_apply, Finset.sum_const_zero] at htel
    simp only [hx, hz]
    linarith
  have hlim : Tendsto (fun N => ∑ n ∈ Finset.range N, x n) atTop
      (𝓝 (W t ω + ∑' n, z n - 0)) := by
    simp_rw [hpart]
    exact (tendsto_const_nhds.add hzs.hasSum.tendsto_sum_nat).sub (htvc ω)
  rw [sub_zero] at hlim
  have hhs : HasSum x (W t ω + ∑' n, z n) := (hasSum_iff_tendsto_nat_of_nonneg hx0 _).mpr hlim
  exact ⟨hhs.summable, hhs.tsum_eq⟩

/-- Woodford (2003), p. 70: (1.13) holds with equality at every date iff the flow constraint
holds with equality at every date and the transversality condition (1.18) holds at every date
(for an adapted wealth plan satisfying the flow constraints (1.7) and borrowing limits (1.9)). -/
theorem ibc_eq_iff_flow_eq_and_tvc (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut)
    {q X Z W : ℕ → Ω → ℝ} (hq : ∀ s, 𝔼.E (s + 1) (q s) = q s) (hq0 : ∀ s ω, 0 ≤ q s ω)
    (hX0 : ∀ s ω, 0 ≤ X s ω) (hXad : 𝔼.Adapted X) (hZad : 𝔼.Adapted Z)
    (hZ : IncomeSummable 𝔼 q Z) (hW : 𝔼.Adapted W) (hflow : FlowConstraint 𝔼 q X Z W)
    (hbl : BorrowingLimit 𝔼 q Z W) :
    (∀ t ω, pv 𝔼 q X t ω = W t ω + pv 𝔼 q Z t ω) ↔ FlowEq 𝔼 q X Z W ∧ ∀ t, TVC 𝔼 q W t := by
  have hslack : ∀ t, slack 𝔼 q X Z W t = 0 ↔
      X t + 𝔼.E t (q t * W (t + 1)) = W t + Z t := by
    intro t
    constructor
    · intro h
      funext ω
      have := congrFun h ω
      simp only [slack, Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at this ⊢
      linarith
    · intro h
      funext ω
      have := congrFun h ω
      simp only [slack, Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at this ⊢
      linarith
  constructor
  · intro heq
    refine ⟨fun t => (hslack t).mp ?_, fun t => ?_⟩
    · exact (flow_eq_and_tvc_of_ibc_eq 𝔼 hMC hP hq hq0 hX0 hXad hZad hZ hW hflow hbl
        (heq t)).1
    · exact (flow_eq_and_tvc_of_ibc_eq 𝔼 hMC hP hq hq0 hX0 hXad hZad hZ hW hflow hbl
        (heq t)).2.2
  · rintro ⟨hfeq, htvc⟩ t ω
    exact (ibc_eq_of_flow_eq_and_tvc 𝔼 hP hq hq0 hX0 hZ (hW t)
      (fun n => (hslack (t + n)).mpr (hfeq (t + n))) (htvc t) ω).2

end Woodford.PriceLevelDetermination.IntertemporalBudget
