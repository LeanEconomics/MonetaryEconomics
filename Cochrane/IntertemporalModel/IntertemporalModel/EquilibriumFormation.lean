/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.Valuation
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Order.LeftRightNhds

/-!
# Dynamic intuition and equilibrium formation

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.2 "Dynamic intuition",
pp. 23–26, eq. (2.9), and §2.3 "Equilibrium formation", pp. 26–29, eqs. (2.10)–(2.11) and the
display on p. 28.

Notation as in `Environment` and `Valuation`: `Bm t = B_{t−1}`, real debt
`x_t = B_{t−1}/P_t`, present value `pv_t = ∑_j β^j E_t s_{t+j}`.

## Main results

* `realRevenue_hasSum`, `eqm_realRevenue` ((2.9), (2.11)): debt sales raise real revenue
  `Q_t B_t/P_t = ∑_{j ≥ 1} β^j E_t s_{t+j}`; `pv_eq_s_add_fwd`:
  `pv_t = s_t + ∑_{j≥1} β^j E_t s_{t+j}`.
* `deficit_financed_by_debt` (p. 24), `soak_up_retired` (the p. 24 formula `Q_tB_t = βE_ts_{t+1}`
  holds, in real terms, exactly when the debt is retired at `t + 1`), `no_rollover` (p. 24–25).
* `passive_every_price_eqm` (p. 24): under a "passive" surplus rule the valuation equation holds
  for every price level.
* `no_initial_debt_pv_zero`, `no_initial_debt_P0_free`, `no_initial_debt_not_unique`
  (pp. 25–26): with `B_{−1} = 0`, `P_0` is not determined.
* `money_overhang_iff`, `money_zero_iff`, `money_negative_iff` (p. 27, (2.10)–(2.11)):
  money is left overnight iff the price level is below its equilibrium value.
* `iterate_with_terminal`, `iterate_with_terminal_limit` (p. 28, with the terminal exponent
  `T + 1`), `printed_p28_false` (the printed `β^T`, survey E4).
* `tooHigh_explodes_down`, `tooHigh_violates_nonneg_debt` (p. 28): a too-high price level pushes
  debt negative, ruled out by `B ≥ 0`.
-/

namespace Cochrane.IntertemporalModel.EquilibriumFormation

open Filter Topology Environment Valuation ExpectationTools

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Debt sales and the present value of following surpluses (2.9), (2.11) -/

/-- Cochrane (2023), eq. (2.7) split at its first term, p. 24: `pv_t = s_t + ∑_{j ≥ 1} β^j E_t
s_{t+j}`, for adapted absolutely summable surpluses. -/
theorem pv_eq_s_add_fwd {β : ℝ} (hβ : 0 ≤ β) {s : ℕ → Ω → ℝ} (hs : AbsSummable 𝔼 β s)
    (hsad : 𝔼.Adapted s) (t : ℕ) (ω : Ω) :
    pv 𝔼 β s t ω = s t ω + ∑' j : ℕ, β ^ (j + 1) * 𝔼.E t (s (t + 1 + j)) ω := by
  have h0 := (summable_terms 𝔼 hβ hs t ω).tsum_eq_zero_add
  simp only [pv_apply]
  rw [h0, pow_zero, one_mul, add_zero, hsad t]
  congr 1
  exact tsum_congr fun j => by rw [show t + (j + 1) = t + 1 + j by omega]

/-- Cochrane (2023), eqs. (2.9) and (2.11), pp. 24 and 27: with the bond price (2.3), a positive
price level known at `t`, debt `B_t` known at `t`, pull-out, conditional monotone convergence,
and the valuation equation at `t + 1`, debt sales raise real revenue equal to the present value
of the following surpluses, `Q_t B_t/P_t = ∑_{j ≥ 1} β^j E_t s_{t+j}` (a convergent series). -/
theorem realRevenue_hasSum (hPO : 𝔼.PullOut) (hMC : MonotoneConvergence 𝔼) {β : ℝ}
    (hβ : 0 ≤ β) {Bm P s Q : ℕ → Ω → ℝ} (hs : AbsSummable 𝔼 β s) {t : ℕ}
    (hPpos : ∀ ω, 0 < P t ω) (hPad : 𝔼.E t (P t) = P t)
    (hB : 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (h23 : Q t = β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω))
    (hval : (fun ω => Bm (t + 1) ω / P (t + 1) ω) = pv 𝔼 β s (t + 1)) (ω : Ω) :
    HasSum (fun j : ℕ => β ^ (j + 1) * 𝔼.E t (s (t + 1 + j)) ω)
      (Q t ω * Bm (t + 1) ω / P t ω) := by
  have hsplit : (fun ω => P t ω / P (t + 1) ω) = P t * fun ω => (P (t + 1) ω)⁻¹ := by
    funext ω; simp [div_eq_mul_inv]
  have hQ : Q t ω = β * (P t ω * 𝔼.E t (fun ω => (P (t + 1) ω)⁻¹) ω) := by
    rw [h23, hsplit, hPO t _ _ hPad]
    rfl
  have hx := congrFun (flow_real_x 𝔼 hPO (β := β) (P := P) hB) ω
  simp only [Pi.smul_apply, smul_eq_mul] at hx
  have hrev : Q t ω * Bm (t + 1) ω / P t ω = β * 𝔼.E t (pv 𝔼 β s (t + 1)) ω := by
    rw [← hval, ← hx, hQ]
    have := (hPpos ω).ne'
    field_simp
  rw [hrev]
  have h1 := (hasSum_E_pv 𝔼 hMC hβ hs t 1 ω).mul_left β
  refine h1.congr_fun fun j => ?_
  rw [pow_succ]
  ring

/-- Cochrane (2023), eq. (2.11), p. 27, in every equilibrium:
`Q_tB_t/P_t = E_t∑_{j≥1}β^js_{t+j}`. -/
theorem eqm_realRevenue (hPO : 𝔼.PullOut) (hMC : MonotoneConvergence 𝔼) {β : ℝ}
    (hβ : 0 ≤ β) {Bm s P Q : ℕ → Ω → ℝ} (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s)
    (hB1 : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1)) (h : IsEqm 𝔼 β Bm s P Q) (t : ℕ) (ω : Ω) :
    HasSum (fun j : ℕ => β ^ (j + 1) * 𝔼.E t (s (t + 1 + j)) ω)
      (Q t ω * Bm (t + 1) ω / P t ω) :=
  realRevenue_hasSum 𝔼 hPO hMC hβ hs (h.1 t) (h.2.1 t) (hB1 t) (h.2.2.1 t)
    (eqm_realDebt_eq_pv 𝔼 hPO hMC hβ hs hsad hB1 h (t + 1)) ω

/-- Cochrane (2023), eq. (2.9), p. 24, "If the government needs to finance a war ... it will
want to run a deficit ... the government can soak up those dollars by debt sales": with a
deficit `s_t < 0` and `P_t > 0`, debt sales `Q_tB_t` exceed the maturing debt `B_{t−1}`. -/
theorem deficit_financed_by_debt {Bm P s Q : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (h24 : Bm t ω = P t ω * s t ω + Q t ω * Bm (t + 1) ω) (hP : 0 < P t ω)
    (hs : s t ω < 0) : Bm t ω < Q t ω * Bm (t + 1) ω := by
  have : P t ω * s t ω < 0 := mul_neg_of_pos_of_neg hP hs
  linarith

/-- Cochrane (2023), p. 24, "the government can soak up those dollars by debt sales
`Q_tB_t = βE_ts_{t+1}`": the formula is exact (in real terms, `Q_tB_t/P_t = βE_ts_{t+1}`) when
the debt is retired at `t + 1` (`B_{t+1} = 0`); in general the revenue is the whole present
value (2.11) (`realRevenue_hasSum`). -/
theorem soak_up_retired (hPO : 𝔼.PullOut) {β : ℝ} {Bm P s Q : ℕ → Ω → ℝ} {t : ℕ}
    (hPpos : ∀ ω, 0 < P t ω) (hPpos1 : ∀ ω, 0 < P (t + 1) ω) (hPad : 𝔼.E t (P t) = P t)
    (hB : 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (h23 : Q t = β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω))
    (h24 : ∀ ω, Bm (t + 1) ω = P (t + 1) ω * s (t + 1) ω + Q (t + 1) ω * Bm (t + 2) ω)
    (hret : ∀ ω, Bm (t + 2) ω = 0) (ω : Ω) :
    Q t ω * Bm (t + 1) ω / P t ω = β * 𝔼.E t (s (t + 1)) ω := by
  have hx1 : (fun ω => Bm (t + 1) ω / P (t + 1) ω) = s (t + 1) := by
    funext ω
    rw [h24 ω, hret ω, mul_zero, add_zero]
    have := (hPpos1 ω).ne'
    field_simp
  have hsplit : (fun ω => P t ω / P (t + 1) ω) = P t * fun ω => (P (t + 1) ω)⁻¹ := by
    funext ω; simp [div_eq_mul_inv]
  have hQ : Q t ω = β * (P t ω * 𝔼.E t (fun ω => (P (t + 1) ω)⁻¹) ω) := by
    rw [h23, hsplit, hPO t _ _ hPad]
    rfl
  have hx := congrFun (flow_real_x 𝔼 hPO (β := β) (P := P) hB) ω
  simp only [Pi.smul_apply, smul_eq_mul] at hx
  rw [← hx1, ← hx, hQ]
  have := (hPpos ω).ne'
  field_simp

/-- Cochrane (2023), pp. 24–25, "If the roll-over fails, or if the government retires the debt,
not selling new debt, we have `B_{t−1}/P_t = s_t` only as in the one-period model": with
`B_t = 0`, (2.4) gives `B_{t−1}/P_t = s_t`. -/
theorem no_rollover {Bm P s Q : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (h24 : Bm t ω = P t ω * s t ω + Q t ω * Bm (t + 1) ω) (hP : P t ω ≠ 0)
    (hB : Bm (t + 1) ω = 0) : Bm t ω / P t ω = s t ω := by
  rw [h24, hB, mul_zero, add_zero]
  field_simp

/-- Cochrane (2023), p. 25 (the flow equation `B_{t−1}/P_t = s_t + Q_tB_t/P_t`): for `P_t ≠ 0`,
(2.4) is equivalent to its real form. -/
theorem flow_div_iff {Bm P s Q : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω} (hP : P t ω ≠ 0) :
    Bm t ω = P t ω * s t ω + Q t ω * Bm (t + 1) ω ↔
      Bm t ω / P t ω = s t ω + Q t ω * Bm (t + 1) ω / P t ω := by
  constructor
  · intro h
    rw [h]
    field_simp
  · intro h
    have : Bm t ω = P t ω * (Bm t ω / P t ω) := by field_simp
    rw [this, h]
    field_simp

/-! ### Passive fiscal policy (p. 24) -/

/-- Cochrane (2023), p. 24: a "passive" surplus rule, which sets surpluses so that the real
flow condition holds at whatever price level obtains, `s_t = x_t − β E_t x_{t+1}` with
`x_t = B_{t−1}/P_t`. -/
noncomputable def passiveSurplus (β : ℝ) (Bm P : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (fun ω => Bm t ω / P t ω) - β • 𝔼.E t (fun ω => Bm (t + 1) ω / P (t + 1) ω)

/-- Cochrane (2023), p. 24, "We only have to rule out or treat separately the special case of
'passive' policy, that the present value of surpluses reacts exactly one-for-one to changes in
the value of nominal debt brought about by changes in the price level, so that equation (2.7)
holds for any price level": with `0 ≤ β < 1`, debt known when sold and pull-out, every positive
adapted price level with bounded real debt is an equilibrium under the passive rule. -/
theorem passive_every_price_eqm (hPO : 𝔼.PullOut) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {Bm P : ℕ → Ω → ℝ} (hB1 : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (hPpos : ∀ t ω, 0 < P t ω) (hPad : 𝔼.Adapted P)
    (hbdd : ∃ M, ∀ t ω, |Bm t ω / P t ω| ≤ M) :
    IsEqm 𝔼 β Bm (passiveSurplus 𝔼 β Bm P) P
      (fun t => β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω)) := by
  refine ⟨hPpos, hPad, fun t => rfl, fun t => ?_, fun t ω => ?_⟩
  · refine (flow_iff_real_x 𝔼 hPO (Q := fun t => β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω))
      (hPpos t) (hPad t) (hB1 t) rfl).mpr ?_
    simp [passiveSurplus]
  · obtain ⟨M, hM⟩ := hbdd
    have hb : ∀ N : ℕ, |β ^ N * 𝔼.E t (fun ω => Bm (t + N) ω / P (t + N) ω) ω| ≤
        β ^ N * M := fun N => by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 N)]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (fun ω => hM (t + N) ω) t ω)
        (pow_nonneg hβ0 N)
    have hlim : Tendsto (fun N : ℕ => β ^ N * M) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const M
    exact squeeze_zero_norm (fun N => by rw [Real.norm_eq_abs]; exact hb N) hlim

/-! ### No initial debt (pp. 25–26) -/

/-- Cochrane (2023), pp. 25–26, "If we start with `B_{−1} = 0`": in every equilibrium the date-0
valuation equation reads `0 = pv_0`, a restriction on surpluses that does not involve `P_0`. -/
theorem no_initial_debt_pv_zero (hPO : 𝔼.PullOut) (hMC : MonotoneConvergence 𝔼) {β : ℝ}
    (hβ : 0 ≤ β) {Bm s P Q : ℕ → Ω → ℝ} (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s)
    (hB1 : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1)) (h : IsEqm 𝔼 β Bm s P Q)
    (hB0 : ∀ ω, Bm 0 ω = 0) : pv 𝔼 β s 0 = 0 := by
  rw [← eqm_realDebt_eq_pv 𝔼 hPO hMC hβ hs hsad hB1 h 0]
  funext ω
  simp [hB0 ω]

/-- Cochrane (2023), pp. 25–26, "If we start with `B_{−1} = 0`, then the price level `P_0` must
be determined by other means": replacing `P_0` in any equilibrium by an arbitrary positive
date-0 variable `P₀'` (and `Q_0` by the corresponding bond price) gives another equilibrium. -/
theorem no_initial_debt_P0_free (hPO : 𝔼.PullOut) {β : ℝ} {Bm s P Q : ℕ → Ω → ℝ}
    (hB1 : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1)) (h : IsEqm 𝔼 β Bm s P Q)
    (hB0 : ∀ ω, Bm 0 ω = 0) {P₀' : Ω → ℝ} (hP0pos : ∀ ω, 0 < P₀' ω)
    (hP0ad : 𝔼.E 0 P₀' = P₀') :
    IsEqm 𝔼 β Bm s (fun t => if t = 0 then P₀' else P t)
      (fun t => if t = 0 then β • 𝔼.E 0 (fun ω => P₀' ω / P 1 ω) else Q t) := by
  obtain ⟨hPpos, hPad, h23, h24, htvc⟩ := h
  set P' : ℕ → Ω → ℝ := fun t => if t = 0 then P₀' else P t with hP'
  set Q' : ℕ → Ω → ℝ :=
    fun t => if t = 0 then β • 𝔼.E 0 (fun ω => P₀' ω / P 1 ω) else Q t with hQ'
  have hP'0 : P' 0 = P₀' := rfl
  have hP'succ : ∀ t, P' (t + 1) = P (t + 1) := fun t => rfl
  have hP'pos : ∀ t ω, 0 < P' t ω := fun t ω => by
    cases t with
    | zero => exact hP0pos ω
    | succ t => exact hPpos (t + 1) ω
  have hP'ad : 𝔼.Adapted P' := fun t => by
    cases t with
    | zero => exact hP0ad
    | succ t => exact hPad (t + 1)
  have h23' : ∀ t, Q' t = β • 𝔼.E t (fun ω => P' t ω / P' (t + 1) ω) := fun t => by
    cases t with
    | zero => rfl
    | succ t => exact h23 (t + 1)
  have hx : (fun t ω => Bm t ω / P' t ω) = fun t ω => Bm t ω / P t ω := by
    funext t ω
    cases t with
    | zero => simp [hB0 ω]
    | succ t => rfl
  refine ⟨hP'pos, hP'ad, h23', fun t => ?_, fun t => by rw [hx]; exact htvc t⟩
  cases t with
  | zero =>
    have hr := (flow_iff_real_x 𝔼 hPO (hPpos 0) (hPad 0) (hB1 0) (h23 0)).mp (h24 0)
    refine (flow_iff_real_x 𝔼 hPO (hP'pos 0) (hP'ad 0) (hB1 0) (h23' 0)).mpr ?_
    have e0 := congrFun hx 0
    have e1 := congrFun hx 1
    rw [e0, e1]
    exact hr
  | succ t => exact h24 (t + 1)

/-- Cochrane (2023), pp. 25–26: with `B_{−1} = 0` the equilibrium price level is not unique:
next to any equilibrium there is another with `P_0` doubled. -/
theorem no_initial_debt_not_unique [Nonempty Ω] (hPO : 𝔼.PullOut) {β : ℝ}
    {Bm s P Q : ℕ → Ω → ℝ} (hB1 : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (h : IsEqm 𝔼 β Bm s P Q) (hB0 : ∀ ω, Bm 0 ω = 0) :
    ∃ P' Q', IsEqm 𝔼 β Bm s P' Q' ∧ P' ≠ P := by
  have hpos : ∀ ω, 0 < (2 : ℝ) • P 0 ω := fun ω => by
    have := h.1 0 ω
    simp only [smul_eq_mul]
    linarith
  have had : 𝔼.E 0 ((2 : ℝ) • P 0) = (2 : ℝ) • P 0 := by rw [map_smul, h.2.1 0]
  refine ⟨_, _, no_initial_debt_P0_free 𝔼 hPO hB1 h hB0 (P₀' := (2 : ℝ) • P 0)
    (fun ω => by simpa using hpos ω) had, fun heq => ?_⟩
  have := congrFun (congrFun heq 0) (Classical.arbitrary Ω)
  have hp := h.1 0 (Classical.arbitrary Ω)
  simp only [↓reduceIte, Pi.smul_apply, smul_eq_mul] at this
  linarith

/-! ### Money left overnight (2.10)–(2.11) -/

/-- Cochrane (2023), eqs. (2.10)–(2.11), p. 27, "if the price level `P_t` is too low, the current
surplus and the revenue from bond sales in (2.10) do not soak up all the money printed to redeem
bonds. Money `M_t` is left overnight": with `B_{t−1} = P_ts_t + Q_tB_t + M_t`, debt-sale revenue
`Q_tB_t/P_t = ∑_{j≥1}β^jE_ts_{t+j}`, `P_t > 0` and a positive present value, `M_t > 0` iff
`P_t < B_{t−1}/pv_t`. -/
theorem money_overhang_iff {β : ℝ} (hβ : 0 ≤ β) {Bm P s Q M : ℕ → Ω → ℝ}
    (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s) {t : ℕ} {ω : Ω}
    (h210 : Bm t ω = P t ω * s t ω + Q t ω * Bm (t + 1) ω + M t ω)
    (h211 : HasSum (fun j : ℕ => β ^ (j + 1) * 𝔼.E t (s (t + 1 + j)) ω)
      (Q t ω * Bm (t + 1) ω / P t ω))
    (hP : 0 < P t ω) (hpv : 0 < pv 𝔼 β s t ω) :
    0 < M t ω ↔ P t ω < Bm t ω / pv 𝔼 β s t ω := by
  have hpv' := pv_eq_s_add_fwd 𝔼 hβ hs hsad t ω
  rw [h211.tsum_eq] at hpv'
  -- `M_t / P_t = B_{t−1}/P_t − pv_t`
  have hM : M t ω = Bm t ω - P t ω * pv 𝔼 β s t ω := by
    rw [hpv']
    have := hP.ne'
    field_simp
    linarith
  rw [lt_div_iff₀ hpv, hM]
  constructor <;> intro h <;> nlinarith

/-- Cochrane (2023), p. 27: under (2.10)–(2.11), no money is left overnight iff the price level
is exactly `B_{t−1}/pv_t`. -/
theorem money_zero_iff {β : ℝ} (hβ : 0 ≤ β) {Bm P s Q M : ℕ → Ω → ℝ}
    (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s) {t : ℕ} {ω : Ω}
    (h210 : Bm t ω = P t ω * s t ω + Q t ω * Bm (t + 1) ω + M t ω)
    (h211 : HasSum (fun j : ℕ => β ^ (j + 1) * 𝔼.E t (s (t + 1 + j)) ω)
      (Q t ω * Bm (t + 1) ω / P t ω))
    (hP : 0 < P t ω) (hpv : 0 < pv 𝔼 β s t ω) :
    M t ω = 0 ↔ P t ω = Bm t ω / pv 𝔼 β s t ω := by
  have hpv' := pv_eq_s_add_fwd 𝔼 hβ hs hsad t ω
  rw [h211.tsum_eq] at hpv'
  have hM : M t ω = Bm t ω - P t ω * pv 𝔼 β s t ω := by
    rw [hpv']
    have := hP.ne'
    field_simp
    linarith
  rw [eq_div_iff hpv.ne', hM]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 27, "If you're bothered by negative money in the opposite direction":
under (2.10)–(2.11), the money balance is negative iff the price level is above
`B_{t−1}/pv_t`. -/
theorem money_negative_iff {β : ℝ} (hβ : 0 ≤ β) {Bm P s Q M : ℕ → Ω → ℝ}
    (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s) {t : ℕ} {ω : Ω}
    (h210 : Bm t ω = P t ω * s t ω + Q t ω * Bm (t + 1) ω + M t ω)
    (h211 : HasSum (fun j : ℕ => β ^ (j + 1) * 𝔼.E t (s (t + 1 + j)) ω)
      (Q t ω * Bm (t + 1) ω / P t ω))
    (hP : 0 < P t ω) (hpv : 0 < pv 𝔼 β s t ω) :
    M t ω < 0 ↔ Bm t ω / pv 𝔼 β s t ω < P t ω := by
  have hpv' := pv_eq_s_add_fwd 𝔼 hβ hs hsad t ω
  rw [h211.tsum_eq] at hpv'
  have hM : M t ω = Bm t ω - P t ω * pv 𝔼 β s t ω := by
    rw [hpv']
    have := hP.ne'
    field_simp
    linarith
  rw [div_lt_iff₀ hpv, hM]
  constructor <;> intro h <;> nlinarith

/-! ### The terminal term (p. 28) -/

/-- Cochrane (2023), p. 28 (display), as an exact finite-horizon identity: if the flow condition
holds at every date (adapted surpluses), then
`B_{t−1}/P_t = s_t + ∑_{j=1}^{T} β^j E_t s_{t+j} + β^{T+1} E_t B_{t+T}/P_{t+T+1}`. The printed
terminal weight is `β^T` (survey E4); `printed_p28_false` refutes it. -/
theorem iterate_with_terminal {β : ℝ} {x s : ℕ → Ω → ℝ} (hsad : 𝔼.Adapted s)
    (h : FlowX 𝔼 β x s) (t T : ℕ) :
    x t = s t + (∑ j ∈ Finset.range T, β ^ (j + 1) • 𝔼.E t (s (t + 1 + j))) +
      β ^ (T + 1) • 𝔼.E t (x (t + T + 1)) := by
  rw [hh_iterate 𝔼 hsad h t T, Finset.sum_range_succ', pow_zero, one_smul, add_zero, hsad t]
  have : ∑ j ∈ Finset.range T, β ^ (j + 1) • 𝔼.E t (s (t + (j + 1))) =
      ∑ j ∈ Finset.range T, β ^ (j + 1) • 𝔼.E t (s (t + 1 + j)) :=
    Finset.sum_congr rfl fun j _ => by rw [show t + (j + 1) = t + 1 + j by omega]
  rw [this]
  abel

/-- Cochrane (2023), p. 28 (display, limit form): if the terminal term
`β^N E_t x_{t+N}` converges to `L`, then `x_t = s_t + ∑_{j ≥ 1} β^j E_t s_{t+j} + L`. -/
theorem iterate_with_terminal_limit {β : ℝ} (hβ : 0 ≤ β) {x s : ℕ → Ω → ℝ}
    (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s) (h : FlowX 𝔼 β x s) {t : ℕ} {ω : Ω}
    {L : ℝ} (hL : Tendsto (fun N : ℕ => β ^ N * 𝔼.E t (x (t + N)) ω) atTop (𝓝 L)) :
    x t ω = s t ω + (∑' j : ℕ, β ^ (j + 1) * 𝔼.E t (s (t + 1 + j)) ω) + L := by
  have hxt := adapted_of_flow 𝔼 hsad h t
  have hpart : ∀ N, ∑ j ∈ Finset.range N, β ^ j * 𝔼.E t (s (t + j)) ω =
      x t ω - β ^ N * 𝔼.E t (x (t + N)) ω := by
    intro N
    have := congrFun (telescope 𝔼 h hxt N) ω
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  have hlim : Tendsto (fun N => ∑ j ∈ Finset.range N, β ^ j * 𝔼.E t (s (t + j)) ω) atTop
      (𝓝 (x t ω - L)) := by
    simp_rw [hpart]
    exact tendsto_const_nhds.sub hL
  have hS := summable_terms 𝔼 hβ hs t ω
  have hpv : pv 𝔼 β s t ω = x t ω - L :=
    tendsto_nhds_unique hS.hasSum.tendsto_sum_nat hlim
  have := pv_eq_s_add_fwd 𝔼 hβ hs hsad t ω
  linarith

/-- Cochrane (2023), p. 28 (survey E4): the printed terminal weight `β^T` is wrong. Under perfect
foresight with `β = 1/2`, `s ≡ 0` and `x_t = 2^t` (so the flow condition holds),
`x_0 ≠ s_0 + ∑_{j=1}^{1} β^j s_j + β^1 x_2`. -/
theorem printed_p28_false :
    FlowX perfectForesight (1 / 2 : ℝ) (fun t _ => (2 : ℝ) ^ t) (fun _ _ => 0) ∧
      (2 : ℝ) ^ 0 ≠ 0 + (1 / 2 : ℝ) ^ 1 * 0 + (1 / 2 : ℝ) ^ 1 * 2 ^ (0 + 1 + 1) := by
  refine ⟨(printed_A1_2_false).1, by norm_num⟩

/-! ### A too-high price level (p. 28) -/

/-- Cochrane (2023), p. 28, "a too-high price level pushes debt to negative values": with constant
surpluses `s`, `0 < β < 1`, and real debt below the equilibrium value `x_t < s/(1−β)` in state
`ω`, expected real debt `E_t x_{t+n}` tends to `−∞`. -/
theorem tooHigh_explodes_down {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {x : ℕ → Ω → ℝ}
    (h : FlowX 𝔼 β x fun _ _ => s) {t : ℕ} {ω : Ω} (hlow : x t ω < s / (1 - β)) :
    Tendsto (fun n : ℕ => 𝔼.E t (x (t + n)) ω) atTop atBot := by
  have hform : ∀ n : ℕ, 𝔼.E t (x (t + n)) ω =
      (β⁻¹) ^ n * (x t ω - s / (1 - β)) + s / (1 - β) := by
    intro n
    have := congrFun (const_explodes 𝔼 hβ0 hβ1 h t n) ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [inv_pow]
    linarith
  simp_rw [hform]
  have hpow : Tendsto (fun n : ℕ => (β⁻¹) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (one_lt_inv₀ hβ0 |>.mpr hβ1)
  have hneg : Tendsto (fun n : ℕ => (β⁻¹) ^ n * (x t ω - s / (1 - β))) atTop atBot := by
    have := hpow.const_mul_atTop_of_neg (r := x t ω - s / (1 - β)) (by linarith)
    simpa [mul_comm] using this
  exact hneg.atBot_add tendsto_const_nhds

/-- Cochrane (2023), p. 28, "a too-high price level pushes debt to negative values, which is ruled
out by budget constraint": under the hypotheses of `tooHigh_explodes_down`, with positive prices,
nominal debt cannot stay nonnegative at all later dates and states. -/
theorem tooHigh_violates_nonneg_debt {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {Bm P : ℕ → Ω → ℝ} (hPpos : ∀ t ω, 0 < P t ω)
    (h : FlowX 𝔼 β (fun t ω => Bm t ω / P t ω) fun _ _ => s) {t : ℕ} {ω : Ω}
    (hlow : Bm t ω / P t ω < s / (1 - β)) : ¬ ∀ n ω', 0 ≤ Bm (t + n) ω' := by
  intro hnn
  have hlim := tooHigh_explodes_down 𝔼 hβ0 hβ1 h hlow
  obtain ⟨n, hn⟩ := (hlim.eventually (eventually_lt_atBot 0)).exists
  have : 0 ≤ 𝔼.E t (fun ω' => Bm (t + n) ω' / P (t + n) ω') ω :=
    E_nonneg 𝔼 (fun ω' => div_nonneg (hnn n ω') (hPpos _ ω').le) ω
  linarith

end Cochrane.IntertemporalModel.EquilibriumFormation
