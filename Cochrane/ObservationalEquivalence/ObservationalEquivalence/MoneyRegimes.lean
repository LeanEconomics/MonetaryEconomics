/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.LeeperRegions

/-!
# Observational equivalence of money-supply regimes

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.1, pp. 495–496 (the
simplest monetary-control model of §19.1), and §22.7, p. 508 ("if monetary policy fixes `M` and
fiscal policy fixes surpluses at an inconsistent value, no equilibrium can form").

With money paying interest (or surpluses responding one-for-one to seigniorage) the model is
`M_t V_t = P_t y_t` and `(B_{t−1} + M_{t−1})/P_t = ∑_{j ≥ 0} βʲ s_{t+j}` (perfect foresight). We
write `W_t = B_{t−1} + M_{t−1}` for the nominal liabilities carried into date `t`; velocity `V`
and output `y` are exogenous and positive, surpluses are bounded and `0 ≤ β < 1`, so the present
value is a genuine (absolutely convergent) infinite sum.

## Main results (OE-2)

* `pv_succ`, `flow_of_valuation`: the valuation equation at every date implies the flow
  constraint `W_t = P_t s_t + Q_t W_{t+1}` with bond price `Q_t = β P_t/P_{t+1}`.
* Active money: `activeMoney_price` (the money supply determines the price level) and
  `activeMoney_exists` (for every positive money supply and every nominal debt path with bounded
  real value, passive surpluses complete an equilibrium).
* Active fiscal: `activeFiscal_unique` and `activeFiscal_exists` (surpluses and nominal debt
  determine the price level, `P_t = W_t / PV_t`, and money follows passively).
* `oe2`: an equilibrium path is, at the same time, the unique equilibrium of the active-money
  regime given its `M` and the unique equilibrium of the active-fiscal regime given its `(W, s)` —
  "any time series produced by [one] regime can be produced by [the other] and vice versa".
* `inconsistent_iff`, `halve_money_no_eqm`: with `M`, `s` and `W` all fixed, an equilibrium exists
  iff `W_t y_t/(M_t V_t) = PV_t` at every date; cutting the money supply in half while holding
  surpluses fixed leaves no equilibrium.
-/

namespace Cochrane.ObservationalEquivalence.MoneyRegimes

open Filter Topology
open Cochrane.ObservationalEquivalence.ExpectationTools (summable_pow_mul_of_bounded
  tendsto_pow_mul_of_bounded)

/-- Cochrane (2023), §22.1, p. 496: the present value of surpluses `∑_{j ≥ 0} βʲ s_{t+j}`. -/
noncomputable def pv (β : ℝ) (s : ℕ → ℝ) (t : ℕ) : ℝ := ∑' j, β ^ j * s (t + j)

/-- Cochrane (2023), §22.1, pp. 495–496: an equilibrium of the money model — a positive price
level, the quantity equation `M_t V_t = P_t y_t` and the valuation equation
`W_t / P_t = ∑ βʲ s_{t+j}` at every date. -/
def Eqm (β : ℝ) (V y P M W s : ℕ → ℝ) : Prop :=
  ∀ t, 0 < P t ∧ M t * V t = P t * y t ∧ W t / P t = pv β s t

/-- Cochrane (2023), §22.1, p. 496: bounded surpluses have an absolutely summable present value
for `0 ≤ β < 1`. -/
theorem pv_summable {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → ℝ} (hs : ∀ t, |s t| ≤ K)
    (t : ℕ) : Summable (fun j => β ^ j * s (t + j)) :=
  summable_pow_mul_of_bounded (by rw [abs_of_nonneg hβ0]; exact hβ1) (x := fun j => s (t + j))
    fun j => hs (t + j)

/-- Cochrane (2023), §22.1, p. 496: `PV_t = s_t + β PV_{t+1}`. -/
theorem pv_succ {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → ℝ} (hs : ∀ t, |s t| ≤ K)
    (t : ℕ) : pv β s t = s t + β * pv β s (t + 1) := by
  rw [pv, (pv_summable hβ0 hβ1 hs t).tsum_eq_zero_add, pv, ← tsum_mul_left]
  simp only [pow_zero, one_mul, add_zero]
  congr 1
  refine tsum_congr fun j => ?_
  rw [show t + (j + 1) = t + 1 + j by omega, pow_succ]
  ring

/-- Cochrane (2023), §22.1, p. 496 (the valuation equation implies the flow constraint): with the
valuation equation at `t` and `t + 1`, `W_t = P_t s_t + Q_t W_{t+1}`, `Q_t = β P_t/P_{t+1}`. -/
theorem flow_of_valuation {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {V y P M W s : ℕ → ℝ}
    (hs : ∀ t, |s t| ≤ K) (h : Eqm β V y P M W s) (t : ℕ) :
    W t = P t * s t + (β * P t / P (t + 1)) * W (t + 1) := by
  obtain ⟨hP, -, hv⟩ := h t
  obtain ⟨hP1, -, hv1⟩ := h (t + 1)
  have e := pv_succ hβ0 hβ1 hs t
  rw [← hv, ← hv1] at e
  field_simp at e ⊢
  linear_combination e

/-! ### Active money -/

/-- Cochrane (2023), §22.1, p. 496 ("in an active-money passive-fiscal regime, the quantity of
money `M` determines the price level `P`"): `P_t = M_t V_t / y_t`. -/
theorem activeMoney_price {V y P M : ℕ → ℝ} (hy : ∀ t, 0 < y t)
    (h : ∀ t, M t * V t = P t * y t) : P = fun t => M t * V t / y t := by
  funext t
  rw [h t, mul_div_cancel_right₀ _ (hy t).ne']

/-- Cochrane (2023), §22.1, p. 496 ("surpluses `s` follow"): for every positive money supply and
every nominal-liability path whose real value `W_t y_t/(M_t V_t)` is bounded, the passive
surpluses `s_t = W_t/P_t − β W_{t+1}/P_{t+1}` complete an equilibrium with `P = MV/y`. -/
theorem activeMoney_exists {β X : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {V y M W : ℕ → ℝ}
    (hV : ∀ t, 0 < V t) (hy : ∀ t, 0 < y t) (hM : ∀ t, 0 < M t)
    (hX : ∀ t, |W t / (M t * V t / y t)| ≤ X) :
    Eqm β V y (fun t => M t * V t / y t) M W
      (fun t => W t / (M t * V t / y t) -
        β * (W (t + 1) / (M (t + 1) * V (t + 1) / y (t + 1)))) := by
  set x : ℕ → ℝ := fun t => W t / (M t * V t / y t) with hx
  have hsb : ∀ t, |x t - β * x (t + 1)| ≤ X + β * X := fun t => by
    refine (abs_sub _ _).trans (add_le_add (hX t) ?_)
    rw [abs_mul, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (hX (t + 1)) hβ0
  intro t
  refine ⟨div_pos (mul_pos (hM t) (hV t)) (hy t), by field_simp [(hy t).ne'], ?_⟩
  have hpart : ∀ T, ∑ j ∈ Finset.range T, β ^ j * (x (t + j) - β * x (t + j + 1)) =
      x t - β ^ T * x (t + T) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [Finset.sum_range_succ, ih, pow_succ, show t + (T + 1) = t + T + 1 by omega]
      ring
  have hlim : Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ j * (x (t + j) - β * x (t + j + 1)))
      atTop (𝓝 (x t)) := by
    simp_rw [hpart]
    have h0 : Tendsto (fun T : ℕ => β ^ T * x (t + T)) atTop (𝓝 0) :=
      tendsto_pow_mul_of_bounded (by rw [abs_of_nonneg hβ0]; exact hβ1)
        (x := fun T => x (t + T)) fun T => hX (t + T)
    simpa using (tendsto_const_nhds (x := x t)).sub h0
  have hsum := pv_summable hβ0 hβ1 (s := fun t => x t - β * x (t + 1)) hsb t
  exact (tendsto_nhds_unique hlim hsum.hasSum.tendsto_sum_nat)

/-! ### Active fiscal -/

/-- Cochrane (2023), §22.1, p. 496 ("in an active-fiscal passive-money regime, fiscal surprises
control unexpected inflation, and then the central bank provides the needed money passively"):
given surpluses and nominal liabilities with `W_t ≠ 0`, the price level `P_t = W_t / PV_t` and
money `M_t = P_t y_t / V_t` are unique. -/
theorem activeFiscal_unique {β : ℝ} {V y P M P' M' W s : ℕ → ℝ} (hV : ∀ t, 0 < V t)
    (hW : ∀ t, W t ≠ 0) (h : Eqm β V y P M W s) (h' : Eqm β V y P' M' W s) :
    P = P' ∧ M = M' := by
  have hP : P = P' := by
    funext t
    obtain ⟨hp, -, hv⟩ := h t
    obtain ⟨hp', -, hv'⟩ := h' t
    have e : W t / P t = W t / P' t := hv.trans hv'.symm
    rw [div_eq_div_iff hp.ne' hp'.ne'] at e
    exact (mul_left_cancel₀ (hW t) e).symm
  refine ⟨hP, funext fun t => ?_⟩
  have e1 := (h t).2.1
  have e2 := (h' t).2.1
  rw [hP] at e1
  exact mul_right_cancel₀ (hV t).ne' (e1.trans e2.symm)

/-- Cochrane (2023), §22.1, p. 496 (active fiscal, existence): if `W_t` and `PV_t` are positive at
every date, `P_t = W_t / PV_t` and `M_t = P_t y_t / V_t` form an equilibrium. -/
theorem activeFiscal_exists {β : ℝ} {V y W s : ℕ → ℝ} (hV : ∀ t, 0 < V t)
    (hW : ∀ t, 0 < W t) (hpv : ∀ t, 0 < pv β s t) :
    Eqm β V y (fun t => W t / pv β s t) (fun t => W t / pv β s t * y t / V t) W s := by
  intro t
  refine ⟨div_pos (hW t) (hpv t), ?_, ?_⟩
  · field_simp [(hV t).ne']
  · field_simp [(hW t).ne', (hpv t).ne']

/-! ### OE-2 -/

/-- Cochrane (2023), §22.1, p. 496 (OE-2: "the equilibrium conditions are the same in each regime.
Any time series produced by an active-money/passive fiscal regime can be produced by an
active-fiscal/passive-money regime and vice versa"): an equilibrium path `(P, M, W, s)` is the
unique price path of the active-money regime given `M`, and the unique `(P, M)` of the
active-fiscal regime given `(W, s)`. -/
theorem oe2 {β : ℝ} {V y P M W s : ℕ → ℝ} (hV : ∀ t, 0 < V t) (hy : ∀ t, 0 < y t)
    (hW : ∀ t, W t ≠ 0) (h : Eqm β V y P M W s) :
    (∀ P' : ℕ → ℝ, (∀ t, M t * V t = P' t * y t) → P' = P) ∧
      ∀ P' M' : ℕ → ℝ, Eqm β V y P' M' W s → P' = P ∧ M' = M := by
  refine ⟨fun P' hP' => ?_, fun P' M' h' => ?_⟩
  · rw [activeMoney_price hy hP', activeMoney_price hy (fun t => (h t).2.1)]
  · obtain ⟨e1, e2⟩ := activeFiscal_unique hV hW h h'
    exact ⟨e1.symm, e2.symm⟩

/-! ### Inconsistent money and fiscal policy (§22.7) -/

/-- Cochrane (2023), §22.7, p. 508 ("if monetary policy fixes `M` and fiscal policy fixes surpluses
at an inconsistent value, no equilibrium can form"): with `M`, `s` and `W` all fixed, an
equilibrium exists iff `W_t y_t / (M_t V_t) = PV_t` at every date. -/
theorem inconsistent_iff {β : ℝ} {V y M W s : ℕ → ℝ} (hV : ∀ t, 0 < V t) (hy : ∀ t, 0 < y t)
    (hM : ∀ t, 0 < M t) :
    (∃ P, Eqm β V y P M W s) ↔ ∀ t, W t / (M t * V t / y t) = pv β s t := by
  constructor
  · rintro ⟨P, hP⟩ t
    have e := activeMoney_price hy (fun t => (hP t).2.1)
    rw [← (hP t).2.2, e]
  · intro h
    refine ⟨fun t => M t * V t / y t, fun t => ⟨div_pos (mul_pos (hM t) (hV t)) (hy t), ?_,
      h t⟩⟩
    field_simp [(hy t).ne']

/-- Cochrane (2023), §22.7, p. 508 ("suppose that the central bank cuts the money supply in half
and leaves it there … that would double the value of government debt"): if `(M, s, W)` admits an
equilibrium and `W_0 ≠ 0`, then `(M/2, s, W)` — surpluses unchanged — admits none. -/
theorem halve_money_no_eqm {β : ℝ} {V y M W s : ℕ → ℝ} (hV : ∀ t, 0 < V t) (hy : ∀ t, 0 < y t)
    (hM : ∀ t, 0 < M t) (hW : W 0 ≠ 0) (h : ∃ P, Eqm β V y P M W s) :
    ¬ ∃ P, Eqm β V y P (fun t => M t / 2) W s := by
  intro h2
  have e1 := (inconsistent_iff hV hy hM).mp h 0
  have e2 := (inconsistent_iff hV hy (fun t => half_pos (hM t))).mp h2 0
  have hm := (hM 0).ne'
  have hv := (hV 0).ne'
  have hyy := (hy 0).ne'
  rw [← e1] at e2
  field_simp at e2
  apply hW
  linarith

end Cochrane.ObservationalEquivalence.MoneyRegimes
