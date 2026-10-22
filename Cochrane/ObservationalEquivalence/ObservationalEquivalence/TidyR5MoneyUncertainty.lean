/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.MoneyRegimes

/-!
# Observational equivalence of money-supply regimes under uncertainty

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.1, pp. 495–496 (the
simplest monetary-control model of §19.1, `M_t V_t = P_t y_t` and
`(B_{t−1} + M_{t−1})/P_t = E_t ∑_{j ≥ 0} βʲ s_{t+j}`), and §22.7, p. 508.

The module `MoneyRegimes` proves OE-2 under perfect foresight. The book writes the valuation
equation with `E_t`. Here the model is stated for an arbitrary `ExpectationSystem`, so every
result holds under perfect foresight, on every finite event tree and under any other expectation
system. `W_t = B_{t−1} + M_{t−1}`; velocity `V`, output `y` and money `M` are positive random
processes; surpluses are bounded and `0 ≤ β < 1`, so the ex-post present value is an absolutely
convergent series in every state and `E_t` passes through it.

## Main results

* `pvE_succ`: `E_t PV_t = s_t + β E_t E_{t+1} PV_{t+1}` for adapted surpluses;
  `flow_of_valuation`: `W_t = P_t s_t + β P_t E_t[W_{t+1}/P_{t+1}]`; `flow_bond_price`: with the
  pull-out property and `W_{t+1}` chosen at `t`, `W_t = P_t s_t + Q_t W_{t+1}` with the nominal
  bond price `Q_t = β P_t E_t[1/P_{t+1}]`.
* Active money: `activeMoney_price`, `activeMoney_exists` (any positive money supply and any
  nominal debt whose real value is bounded and adapted; surpluses
  `s_t = x_t − β E_t x_{t+1}` follow passively).
* Active fiscal: `activeFiscal_unique`, `activeFiscal_exists`, `activeFiscal_adapted`
  (`P_t = W_t / E_t PV_t` is known at `t` under the pull-out property).
* `oe2`: an equilibrium path is the unique equilibrium of the active-money regime given its `M`
  and the unique equilibrium of the active-fiscal regime given its `(W, s)`.
* `unexpected_price_level`: in every equilibrium the surprise in `1/P_{t+1}` equals the fiscal
  news `ΔE_{t+1} PV_{t+1} / W_{t+1}` and the money news `ΔE_{t+1}(y/(MV))_{t+1}` ("fiscal
  surprises control unexpected inflation", p. 496).
* `inconsistent_iff`, `halve_money_no_eqm`: §22.7 under uncertainty.
* `eqm_perfectForesight_iff`: under perfect foresight the definition is `MoneyRegimes.Eqm`.
* `coin_random_eqm`: on the coin-flip tree there is an equilibrium whose date-1 price level is not
  known at date 0.
-/

namespace Cochrane.ObservationalEquivalence.TidyR5MoneyUncertainty

open Filter Topology
open Cochrane.ObservationalEquivalence.ExpectationTools (tendsto_pow_mul_of_bounded)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §22.1, p. 496: the ex-post present value of surpluses
`∑_{j ≥ 0} βʲ s_{t+j}`, state by state. -/
noncomputable def pvS (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j, β ^ j * s (t + j) ω

/-- Cochrane (2023), §22.1, p. 496: the present value `E_t ∑_{j ≥ 0} βʲ s_{t+j}`. -/
noncomputable def pvE (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  𝔼.E t (pvS β s t)

/-- Cochrane (2023), §22.1, pp. 495–496, under uncertainty: an equilibrium of the money model — a
positive price level, the quantity equation `M_t V_t = P_t y_t` and the valuation equation
`W_t / P_t = E_t ∑ βʲ s_{t+j}` at every date and in every state. -/
def Eqm (β : ℝ) (V y P M W s : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (∀ ω, 0 < P t ω) ∧ M t * V t = P t * y t ∧ W t / P t = pvE 𝔼 β s t

omit 𝔼 in
/-- Cochrane (2023), §22.1, p. 496: state by state the ex-post present value is the perfect
foresight present value `MoneyRegimes.pv` of that state's surplus path. -/
theorem pvS_apply (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    pvS β s t ω = MoneyRegimes.pv β (fun k => s k ω) t := rfl

/-- Cochrane (2023), §22.1, p. 496: for `0 ≤ β < 1` and bounded surpluses, `E_t` passes through
the present value, `E_t PV_t = ∑_j βʲ E_t s_{t+j}`. -/
theorem pvE_eq_tsum {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ K) (t : ℕ) (ω : Ω) :
    pvE 𝔼 β s t ω = ∑' j, β ^ j * 𝔼.E t (s (t + j)) ω := by
  have h := 𝔼.E_tsum hβ0 hβ1 (f := fun j ω => β ^ j * s (t + j) ω) (M := K) (fun j ω => by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 j)]
    exact mul_le_mul_of_nonneg_left (hs _ ω) (pow_nonneg hβ0 j)) t ω
  refine h.trans (tsum_congr fun j => ?_)
  have e : (fun ω => β ^ j * s (t + j) ω) = (β ^ j) • s (t + j) := by
    funext ω; simp [smul_eq_mul]
  rw [e, map_smul]
  rfl

/-- Cochrane (2023), §22.1, p. 496: with adapted bounded surpluses,
`E_t PV_t = s_t + β E_t (E_{t+1} PV_{t+1})`. -/
theorem pvE_succ {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ K) (hsa : 𝔼.Adapted s) (t : ℕ) :
    pvE 𝔼 β s t = s t + β • 𝔼.E t (pvE 𝔼 β s (t + 1)) := by
  have hp : pvS β s t = s t + β • pvS β s (t + 1) := by
    funext ω
    have := MoneyRegimes.pv_succ hβ0 hβ1 (s := fun k => s k ω) (fun k => hs k ω) t
    simpa [pvS_apply, smul_eq_mul] using this
  rw [pvE, hp, map_add, map_smul, hsa t, pvE, 𝔼.tower (Nat.le_succ t)]

/-- Cochrane (2023), §22.1, p. 496 (the valuation equation implies the flow constraint, under
uncertainty): `W_t = P_t s_t + β P_t E_t[W_{t+1}/P_{t+1}]`. -/
theorem flow_of_valuation {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {V y P M W s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ K) (hsa : 𝔼.Adapted s) (h : Eqm 𝔼 β V y P M W s) (t : ℕ) :
    W t = P t * s t + β • (P t * 𝔼.E t (W (t + 1) / P (t + 1))) := by
  obtain ⟨hP, -, hv⟩ := h t
  obtain ⟨-, -, hv1⟩ := h (t + 1)
  have e := pvE_succ 𝔼 hβ0 hβ1 hs hsa t
  rw [← hv, ← hv1] at e
  funext ω
  have e' := congrFun e ω
  simp only [Pi.div_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply] at e' ⊢
  have hp := (hP ω).ne'
  field_simp at e'
  linear_combination e'

/-- Cochrane (2023), §22.1, p. 496 (the flow constraint with the nominal bond price): with the
pull-out property and `W_{t+1}` chosen at `t`, `W_t = P_t s_t + Q_t W_{t+1}`, where
`Q_t = β P_t E_t[1/P_{t+1}]` is the price of a one-period nominal bond. -/
theorem flow_bond_price {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {V y P M W s : ℕ → Ω → ℝ}
    (hpo : 𝔼.PullOut) (hs : ∀ t ω, |s t ω| ≤ K) (hsa : 𝔼.Adapted s)
    (h : Eqm 𝔼 β V y P M W s) (t : ℕ) (hW : 𝔼.E t (W (t + 1)) = W (t + 1)) :
    W t = P t * s t + (β • (P t * 𝔼.E t (fun ω => 1 / P (t + 1) ω))) * W (t + 1) := by
  rw [flow_of_valuation 𝔼 hβ0 hβ1 hs hsa h t]
  have e : W (t + 1) / P (t + 1) = W (t + 1) * fun ω => 1 / P (t + 1) ω := by
    funext ω; simp [div_eq_mul_inv]
  rw [e, hpo t _ _ hW]
  funext ω
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### Active money -/

omit 𝔼 in
/-- Cochrane (2023), §22.1, p. 496 ("in an active-money passive-fiscal regime, the quantity of
money `M` determines the price level `P`"), under uncertainty: `P_t = M_t V_t / y_t` in every
state. -/
theorem activeMoney_price {V y P M : ℕ → Ω → ℝ} (hy : ∀ t ω, 0 < y t ω)
    (h : ∀ t, M t * V t = P t * y t) : P = fun t => M t * V t / y t := by
  funext t ω
  have e := congrFun (h t) ω
  simp only [Pi.mul_apply, Pi.div_apply] at e ⊢
  rw [e, mul_div_cancel_right₀ _ (hy t ω).ne']

/-- Cochrane (2023), §22.1, p. 496 ("surpluses `s` follow"), under uncertainty: for every positive
money supply and every nominal-liability path whose real value `x_t = W_t y_t/(M_t V_t)` is
bounded and adapted, the passive surpluses `s_t = x_t − β E_t x_{t+1}` complete an equilibrium
with `P = MV/y`. -/
theorem activeMoney_exists {β X : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {V y M W : ℕ → Ω → ℝ}
    (hV : ∀ t ω, 0 < V t ω) (hy : ∀ t ω, 0 < y t ω) (hM : ∀ t ω, 0 < M t ω)
    (hX : ∀ t ω, |(W t / (M t * V t / y t)) ω| ≤ X)
    (hxa : 𝔼.Adapted fun t => W t / (M t * V t / y t)) :
    Eqm 𝔼 β V y (fun t => M t * V t / y t) M W
      (fun t => W t / (M t * V t / y t) -
        β • 𝔼.E t (W (t + 1) / (M (t + 1) * V (t + 1) / y (t + 1)))) := by
  set x : ℕ → Ω → ℝ := fun t => W t / (M t * V t / y t) with hx
  have hEx : ∀ t ω, |𝔼.E t (x (t + 1)) ω| ≤ X := fun t ω => 𝔼.abs_E_le (hX (t + 1)) t ω
  have hsb : ∀ t ω, |(x t - β • 𝔼.E t (x (t + 1))) ω| ≤ X + β * X := fun t ω => by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add (hX t ω) ?_)
    rw [abs_mul, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (hEx t ω) hβ0
  intro t
  refine ⟨fun ω => div_pos (mul_pos (hM t ω) (hV t ω)) (hy t ω), ?_, ?_⟩
  · funext ω
    simp only [Pi.mul_apply, Pi.div_apply]
    field_simp [(hy t ω).ne']
  · change x t = _
    funext ω
    rw [pvE_eq_tsum 𝔼 hβ0 hβ1 hsb t ω]
    set a : ℕ → ℝ := fun j => 𝔼.E t (x (t + j)) ω with ha
    have hterm : ∀ j, 𝔼.E t ((fun t => x t - β • 𝔼.E t (x (t + 1))) (t + j)) ω =
        a j - β * a (j + 1) := fun j => by
      simp only [ha, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [𝔼.tower (Nat.le_add_right t j), show t + j + 1 = t + (j + 1) by omega]
    simp_rw [hterm]
    have hpart : ∀ T, ∑ j ∈ Finset.range T, β ^ j * (a j - β * a (j + 1)) =
        a 0 - β ^ T * a T := by
      intro T
      induction T with
      | zero => simp
      | succ T ih =>
        rw [Finset.sum_range_succ, ih, pow_succ]
        ring
    have ha0 : a 0 = x t ω := by simp only [ha, add_zero]; rw [hxa t]
    have hsum : Summable fun j => β ^ j * (a j - β * a (j + 1)) := by
      refine ExpectationTools.summable_pow_mul_of_bounded (K := X + β * X)
        (by rw [abs_of_nonneg hβ0]; exact hβ1) fun j => ?_
      refine (abs_sub _ _).trans (add_le_add (𝔼.abs_E_le (hX _) t ω) ?_)
      rw [abs_mul, abs_of_nonneg hβ0]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hX _) t ω) hβ0
    have hlim : Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ j * (a j - β * a (j + 1))) atTop
        (𝓝 (a 0)) := by
      simp_rw [hpart]
      have h0 : Tendsto (fun T : ℕ => β ^ T * a T) atTop (𝓝 0) :=
        tendsto_pow_mul_of_bounded (by rw [abs_of_nonneg hβ0]; exact hβ1)
          fun T => 𝔼.abs_E_le (hX _) t ω
      simpa using (tendsto_const_nhds (x := a 0)).sub h0
    rw [← ha0]
    exact tendsto_nhds_unique hlim hsum.hasSum.tendsto_sum_nat

/-! ### Active fiscal -/

omit 𝔼 in
/-- Cochrane (2023), §22.1, p. 496 ("in an active-fiscal passive-money regime, fiscal surprises
control unexpected inflation, and then the central bank provides the needed money passively"),
under uncertainty: given surpluses and nominal liabilities with `W_t ≠ 0` in every state, the
price level `P_t = W_t / E_t PV_t` and money `M_t = P_t y_t / V_t` are unique. -/
theorem activeFiscal_unique {β : ℝ} {𝔼 : ExpectationSystem Ω} {V y P M P' M' W s : ℕ → Ω → ℝ}
    (hV : ∀ t ω, 0 < V t ω) (hW : ∀ t ω, W t ω ≠ 0) (h : Eqm 𝔼 β V y P M W s)
    (h' : Eqm 𝔼 β V y P' M' W s) : P = P' ∧ M = M' := by
  have hP : P = P' := by
    funext t ω
    obtain ⟨hp, -, hv⟩ := h t
    obtain ⟨hp', -, hv'⟩ := h' t
    have e : W t ω / P t ω = W t ω / P' t ω := by
      have := congrFun (hv.trans hv'.symm) ω
      simpa using this
    rw [div_eq_div_iff (hp ω).ne' (hp' ω).ne'] at e
    exact (mul_left_cancel₀ (hW t ω) e).symm
  refine ⟨hP, funext fun t => funext fun ω => ?_⟩
  have e1 := congrFun (h t).2.1 ω
  have e2 := congrFun (h' t).2.1 ω
  rw [hP] at e1
  simp only [Pi.mul_apply] at e1 e2
  exact mul_right_cancel₀ (hV t ω).ne' (e1.trans e2.symm)

/-- Cochrane (2023), §22.1, p. 496 (active fiscal, existence, under uncertainty): if `W_t` and
`E_t PV_t` are positive in every state, `P_t = W_t / E_t PV_t` and `M_t = P_t y_t / V_t` form an
equilibrium. -/
theorem activeFiscal_exists {β : ℝ} {V y W s : ℕ → Ω → ℝ} (hV : ∀ t ω, 0 < V t ω)
    (hW : ∀ t ω, 0 < W t ω) (hpv : ∀ t ω, 0 < pvE 𝔼 β s t ω) :
    Eqm 𝔼 β V y (fun t => W t / pvE 𝔼 β s t) (fun t => W t / pvE 𝔼 β s t * y t / V t) W s := by
  intro t
  refine ⟨fun ω => div_pos (hW t ω) (hpv t ω), ?_, ?_⟩
  · funext ω
    simp only [Pi.mul_apply, Pi.div_apply]
    field_simp [(hV t ω).ne']
  · funext ω
    simp only [Pi.div_apply]
    field_simp [(hW t ω).ne', (hpv t ω).ne']

/-- Cochrane (2023), §22.1, p. 496 (tool): under the pull-out property, the reciprocal of a
variable known at `t` and nonzero in every state is known at `t`. -/
theorem E_inv_of_known (hpo : 𝔼.PullOut) {t : ℕ} {b : Ω → ℝ} (hb : 𝔼.E t b = b)
    (hb0 : ∀ ω, b ω ≠ 0) : 𝔼.E t (fun ω => (b ω)⁻¹) = fun ω => (b ω)⁻¹ := by
  have h1 : b * (fun ω => (b ω)⁻¹) = fun _ => (1 : ℝ) := by
    funext ω; simp [hb0 ω]
  have h := hpo t b (fun ω => (b ω)⁻¹) hb
  rw [h1, 𝔼.const] at h
  funext ω
  have e := congrFun h ω
  simp only [Pi.mul_apply] at e
  exact eq_inv_of_mul_eq_one_right e.symm

/-- Cochrane (2023), §22.1, p. 496 (active fiscal: the price level is known at `t`): with the
pull-out property and nominal liabilities known at `t`, `P_t = W_t / E_t PV_t` is adapted. -/
theorem activeFiscal_adapted (hpo : 𝔼.PullOut) {β : ℝ} {W s : ℕ → Ω → ℝ} (hWa : 𝔼.Adapted W)
    (hpv : ∀ t ω, pvE 𝔼 β s t ω ≠ 0) : 𝔼.Adapted fun t => W t / pvE 𝔼 β s t := fun t => by
  change 𝔼.E t (W t / pvE 𝔼 β s t) = W t / pvE 𝔼 β s t
  have e : W t / pvE 𝔼 β s t = W t * fun ω => (pvE 𝔼 β s t ω)⁻¹ := by
    funext ω; simp [div_eq_mul_inv]
  rw [e, hpo t _ _ (hWa t), E_inv_of_known 𝔼 hpo (b := pvE 𝔼 β s t) (𝔼.E_E_self t _) (hpv t)]

/-! ### OE-2 under uncertainty -/

/-- Cochrane (2023), §22.1, p. 496 (OE-2 under uncertainty: "the equilibrium conditions are the
same in each regime. Any time series produced by an active-money/passive fiscal regime can be
produced by an active-fiscal/passive-money regime and vice versa"): an equilibrium path
`(P, M, W, s)` is the unique price path of the active-money regime given `M`, and the unique
`(P, M)` of the active-fiscal regime given `(W, s)`. -/
theorem oe2 {β : ℝ} {V y P M W s : ℕ → Ω → ℝ} (hV : ∀ t ω, 0 < V t ω) (hy : ∀ t ω, 0 < y t ω)
    (hW : ∀ t ω, W t ω ≠ 0) (h : Eqm 𝔼 β V y P M W s) :
    (∀ P' : ℕ → Ω → ℝ, (∀ t, M t * V t = P' t * y t) → P' = P) ∧
      ∀ P' M' : ℕ → Ω → ℝ, Eqm 𝔼 β V y P' M' W s → P' = P ∧ M' = M := by
  refine ⟨fun P' hP' => ?_, fun P' M' h' => ?_⟩
  · rw [activeMoney_price hy hP', activeMoney_price hy (fun t => (h t).2.1)]
  · obtain ⟨e1, e2⟩ := activeFiscal_unique hV hW h h'
    exact ⟨e1.symm, e2.symm⟩

/-- Cochrane (2023), §22.1, p. 496 ("fiscal surprises control unexpected inflation"; under active
money the money supply does): with the pull-out property and `W_{t+1}` chosen at `t`, in every
equilibrium the surprise in the inverse price level equals both the fiscal news
`(PV_{t+1} − E_t PV_{t+1})/W_{t+1}` and the money news
`y_{t+1}/(M_{t+1}V_{t+1}) − E_t[y_{t+1}/(M_{t+1}V_{t+1})]`. -/
theorem unexpected_price_level (hpo : 𝔼.PullOut) {β : ℝ} {V y P M W s : ℕ → Ω → ℝ}
    (hy : ∀ t ω, 0 < y t ω) (h : Eqm 𝔼 β V y P M W s) (t : ℕ)
    (hW : 𝔼.E t (W (t + 1)) = W (t + 1)) (hW0 : ∀ ω, W (t + 1) ω ≠ 0) :
    ((fun ω => 1 / P (t + 1) ω) - 𝔼.E t (fun ω => 1 / P (t + 1) ω) =
      fun ω => (pvE 𝔼 β s (t + 1) ω - 𝔼.E t (pvE 𝔼 β s (t + 1)) ω) / W (t + 1) ω) ∧
    ((fun ω => 1 / P (t + 1) ω) - 𝔼.E t (fun ω => 1 / P (t + 1) ω) =
      (fun ω => y (t + 1) ω / (M (t + 1) ω * V (t + 1) ω)) -
        𝔼.E t (fun ω => y (t + 1) ω / (M (t + 1) ω * V (t + 1) ω))) := by
  obtain ⟨hP, hq, hv⟩ := h (t + 1)
  have hinvP : (fun ω => 1 / P (t + 1) ω) =
      (fun ω => (W (t + 1) ω)⁻¹) * pvE 𝔼 β s (t + 1) := by
    funext ω
    have e := congrFun hv ω
    simp only [Pi.div_apply] at e
    simp only [Pi.mul_apply, ← e]
    field_simp [hW0 ω, (hP ω).ne']
  have hWi := E_inv_of_known 𝔼 hpo hW hW0
  have hmon : (fun ω => 1 / P (t + 1) ω) =
      fun ω => y (t + 1) ω / (M (t + 1) ω * V (t + 1) ω) := by
    funext ω
    have e := congrFun hq ω
    simp only [Pi.mul_apply] at e
    have hMV : M (t + 1) ω * V (t + 1) ω ≠ 0 := by
      rw [e]; exact (mul_pos (hP ω) (hy (t + 1) ω)).ne'
    rw [e]
    field_simp [(hy (t + 1) ω).ne', (hP ω).ne']
  refine ⟨?_, by rw [hmon]⟩
  rw [hinvP, hpo t _ _ hWi]
  funext ω
  simp only [Pi.sub_apply, Pi.mul_apply]
  field_simp [hW0 ω]

/-! ### Inconsistent money and fiscal policy (§22.7) -/

omit 𝔼 in
/-- Cochrane (2023), §22.7, p. 508 ("if monetary policy fixes `M` and fiscal policy fixes surpluses
at an inconsistent value, no equilibrium can form"), under uncertainty: with `M`, `s` and `W` all
fixed, an equilibrium exists iff `W_t y_t / (M_t V_t) = E_t PV_t` at every date and state. -/
theorem inconsistent_iff {β : ℝ} {𝔼 : ExpectationSystem Ω} {V y M W s : ℕ → Ω → ℝ}
    (hV : ∀ t ω, 0 < V t ω) (hy : ∀ t ω, 0 < y t ω) (hM : ∀ t ω, 0 < M t ω) :
    (∃ P, Eqm 𝔼 β V y P M W s) ↔ ∀ t, W t / (M t * V t / y t) = pvE 𝔼 β s t := by
  constructor
  · rintro ⟨P, hP⟩ t
    have e := activeMoney_price hy (fun t => (hP t).2.1)
    rw [← (hP t).2.2, e]
  · intro h
    refine ⟨fun t => M t * V t / y t, fun t => ⟨fun ω => div_pos (mul_pos (hM t ω) (hV t ω))
      (hy t ω), ?_, h t⟩⟩
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply]
    field_simp [(hy t ω).ne']

omit 𝔼 in
/-- Cochrane (2023), §22.7, p. 508 ("suppose that the central bank cuts the money supply in half
and leaves it there"), under uncertainty: if `(M, s, W)` admits an equilibrium and `W_0 ≠ 0` in
some state, then `(M/2, s, W)` — surpluses unchanged — admits none. -/
theorem halve_money_no_eqm {β : ℝ} {𝔼 : ExpectationSystem Ω} {V y M W s : ℕ → Ω → ℝ}
    (hV : ∀ t ω, 0 < V t ω) (hy : ∀ t ω, 0 < y t ω) (hM : ∀ t ω, 0 < M t ω) {ω : Ω}
    (hW : W 0 ω ≠ 0) (h : ∃ P, Eqm 𝔼 β V y P M W s) :
    ¬ ∃ P, Eqm 𝔼 β V y P (fun t => M t / 2) W s := by
  intro h2
  have e1 := congrFun ((inconsistent_iff hV hy hM).mp h 0) ω
  have e2 := congrFun ((inconsistent_iff hV hy (fun t ω => half_pos (hM t ω))).mp h2 0) ω
  simp only [Pi.div_apply, Pi.mul_apply] at e1 e2
  have hm := (hM 0 ω).ne'
  have hv := (hV 0 ω).ne'
  have hyy := (hy 0 ω).ne'
  rw [← e1] at e2
  field_simp at e2
  apply hW
  linarith

/-! ### Perfect foresight and a genuinely random equilibrium -/

/-- Cochrane (2023), §22.1, pp. 495–496: under perfect foresight the stochastic definition is the
perfect-foresight one of `MoneyRegimes`. -/
theorem eqm_perfectForesight_iff {β : ℝ} {V y P M W s : ℕ → Unit → ℝ} :
    Eqm perfectForesight β V y P M W s ↔
      MoneyRegimes.Eqm β (fun t => V t ()) (fun t => y t ()) (fun t => P t ())
        (fun t => M t ()) (fun t => W t ()) (fun t => s t ()) := by
  refine forall_congr' fun t => ?_
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1 (), congrFun h2 (), congrFun h3 ()⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun _ => h1, funext fun _ => h2, funext fun _ => h3⟩

/-- Cochrane (2023), §22.1, p. 496, on the coin-flip tree: the money supply
`M_t = 2 + ε_t` (`ε` the coin shock), `V = y = 1` and `W = M` with surpluses
`s_t = 1 − β E_t 1` form an equilibrium whose date-1 price level `P_1 = 2 ± 1` is not known at
date 0 — the stochastic model is not perfect foresight in disguise. -/
theorem coin_random_eqm {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Eqm ExpectationsFiniteTree.coinSystem β 1 1
      (fun t ω => 2 + ExpectationsFiniteTree.coinShock t ω)
      (fun t ω => 2 + ExpectationsFiniteTree.coinShock t ω)
      (fun t ω => 2 + ExpectationsFiniteTree.coinShock t ω)
      (fun _ _ => 1 - β) ∧
    ExpectationsFiniteTree.coinSystem.E 0 (fun ω => 2 + ExpectationsFiniteTree.coinShock 1 ω) ≠
      fun ω => 2 + ExpectationsFiniteTree.coinShock 1 ω := by
  set 𝔼c := ExpectationsFiniteTree.coinSystem
  set M : ℕ → Bool × Bool → ℝ := fun t ω => 2 + ExpectationsFiniteTree.coinShock t ω with hMdef
  have hM : ∀ t ω, 0 < M t ω := fun t ω => by
    obtain ⟨K, hK⟩ := Equivalence.coinShock_bounded
    have h1 : |ExpectationsFiniteTree.coinShock t ω| ≤ 1 := by
      unfold ExpectationsFiniteTree.coinShock
      split_ifs <;> norm_num
    simp only [hMdef]
    linarith [(abs_le.1 h1).1]
  have hx : (fun t => M t / (M t * (1 : ℕ → Bool × Bool → ℝ) t / (1 : ℕ → Bool × Bool → ℝ) t)) =
      fun _ _ => (1 : ℝ) := by
    funext t ω
    simp only [Pi.div_apply, Pi.one_apply, mul_one, div_one]
    exact div_self (hM t ω).ne'
  have hx' : ∀ t, M t / (M t * (1 : ℕ → Bool × Bool → ℝ) t / (1 : ℕ → Bool × Bool → ℝ) t) =
      fun _ => (1 : ℝ) := fun t => congrFun hx t
  have h := activeMoney_exists 𝔼c hβ0 hβ1 (V := 1) (y := 1) (M := M) (W := M)
    (fun _ _ => one_pos) (fun _ _ => one_pos) hM (X := 1)
    (fun t ω => by rw [hx' t]; simp) (fun t => by
      change 𝔼c.E t (M t / (M t * (1 : ℕ → Bool × Bool → ℝ) t / (1 : ℕ → Bool × Bool → ℝ) t)) =
        M t / (M t * (1 : ℕ → Bool × Bool → ℝ) t / (1 : ℕ → Bool × Bool → ℝ) t)
      rw [hx' t]; exact 𝔼c.const t 1)
  have hP : (fun t => M t * (1 : ℕ → Bool × Bool → ℝ) t / (1 : ℕ → Bool × Bool → ℝ) t) = M := by
    funext t ω; simp
  have hs : (fun t => M t / (M t * (1 : ℕ → Bool × Bool → ℝ) t / (1 : ℕ → Bool × Bool → ℝ) t) -
      β • 𝔼c.E t (M (t + 1) / (M (t + 1) * (1 : ℕ → Bool × Bool → ℝ) (t + 1) /
        (1 : ℕ → Bool × Bool → ℝ) (t + 1)))) = fun _ _ => 1 - β := by
    funext t ω
    have e1 : M t / (M t * (1 : ℕ → Bool × Bool → ℝ) t / (1 : ℕ → Bool × Bool → ℝ) t) =
        fun _ => (1 : ℝ) := congrFun hx t
    have e2 : M (t + 1) / (M (t + 1) * (1 : ℕ → Bool × Bool → ℝ) (t + 1) /
        (1 : ℕ → Bool × Bool → ℝ) (t + 1)) = fun _ => (1 : ℝ) := congrFun hx (t + 1)
    rw [e1, e2, 𝔼c.const]
    simp
  rw [hP, hs] at h
  refine ⟨h, fun he => ?_⟩
  have hE : 𝔼c.E 0 (fun ω => 2 + ExpectationsFiniteTree.coinShock 1 ω) = fun _ => 2 := by
    have e : (fun ω => 2 + ExpectationsFiniteTree.coinShock 1 ω) =
        (fun _ => (2 : ℝ)) + ExpectationsFiniteTree.coinShock (0 + 1) := by
      funext ω; simp
    rw [e, map_add, 𝔼c.const, ExpectationsFiniteTree.coinShock_mean_zero 0]
    funext ω; simp
  rw [hE] at he
  have := congrFun he (true, true)
  norm_num [ExpectationsFiniteTree.coinShock] at this

end Cochrane.ObservationalEquivalence.TidyR5MoneyUncertainty
