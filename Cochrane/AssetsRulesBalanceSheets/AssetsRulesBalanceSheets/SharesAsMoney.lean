/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.RealDebt

/-!
# Shares as money

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 10, §10.1.3 (pp. 295–297),
eq. (10.7).

A potato farm with `N` shares sells `s_t` potatoes a day for its own shares and pays the shares
back out as dividends; `P_t` is the number of shares per potato. Then the farm's indexed
perpetuities, or one-period indexed bonds, are used as the numeraire.

## Main results

* `ShareFlow`, `shareFlow_iff_solves`, `pv_smul`, `share_valuation_iff` (a share that pays only
  shares is worth `(1/N) E_t ∑ βʲ s_{t+j}` potatoes), `potato_price_level`
  (`N/P_t = E_t ∑ βʲ s_{t+j}`; uniqueness is `PresentValue.valuation_price_unique`).
* (10.7): `pv_one`, `perpetuity_real_value` (`E_t ∑ βʲ P_{t+j}/P_{t+j} = 1/(1 − β)`),
  `one_sub_beta_inv` (`= (1 + r)/r`), `perpetuity_price_level`,
  `perpetuity_price_level_process` (`P_t = (1 + y) r/((1 + r) y)`), and survey E10.1: the printed
  `P_t = (1 + r) y/((1 + y) r)` is the reciprocal (`printed_reciprocal`), equal only when `y = r`
  (`printed_eq_iff`, `printed_counterexample`); `price_level_one_iff` (`P_t = 1` iff `y = r`,
  the book's conclusion is unaffected); `potato_perpetuity_unit`.
* `pv_sub_const`, `perpetuity_backing_bound`: positive equity bounds the perpetuities by the
  present value of potato sales.
* One-period indexed bonds as numeraire (survey E10.2): `oneperiod_real_value` (worth `β` goods),
  `oneperiod_price_level` (`P_t = 1/β`, so each maturing bond is redeemed for `1/β` new bonds),
  `printed_beta_wrong` (the printed `P_t = β` is wrong for `0 < β < 1`),
  `numeraire_one_plus_y`; survey E10.4: `bond_value_le`, `bond_value_no_default` (no default
  needs only `M_t ≤ s_{t+1}`, weak inequality).
-/

namespace Cochrane.AssetsRulesBalanceSheets.SharesAsMoney

open Filter Topology RealDebt PresentValue

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Potato-farm shares as money -/

/-- Cochrane (2023), §10.1.3, p. 295: the real value `v_t` of a share that pays `P_t s_t/N`
shares as its date-`t` dividend, each share being worth `1/P_t` potatoes:
`v_t = (P_t s_t/N)/P_t + β E_t v_{t+1}`. -/
def ShareFlow (β N : ℝ) (P s v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, v t = (fun ω => P t ω * s t ω / N / P t ω) + β • 𝔼.E t (v (t + 1))

/-- Cochrane (2023), §10.1.3, p. 295: "the value of shares is the same as if dividends delivered
potatoes": with a nowhere-zero price level the share flow is `v_t = s_t/N + β E_t v_{t+1}`. -/
theorem shareFlow_iff_solves {β N : ℝ} {P s v : ℕ → Ω → ℝ} (hN : N ≠ 0)
    (hP : ∀ t ω, P t ω ≠ 0) :
    ShareFlow 𝔼 β N P s v ↔ ForwardSolution.Solves 𝔼 β (fun t => N⁻¹ • s t) v := by
  have e : ∀ t, (fun ω => P t ω * s t ω / N / P t ω) = N⁻¹ • s t := by
    intro t
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [hP t ω]
  simp only [ShareFlow, ForwardSolution.Solves, e]
  constructor <;> intro h t <;> rw [h t, add_comm]

/-- Cochrane (2023), §10.1.3, p. 295: the present value is linear in a constant scale factor,
`E_t ∑ βʲ (c s_{t+j}) = c E_t ∑ βʲ s_{t+j}`. -/
theorem pv_smul (β c : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) :
    pv 𝔼 β (fun t => c • s t) t = c • pv 𝔼 β s t := by
  have h : epv β (fun t => c • s t) t = c • epv β s t := by
    funext ω
    simp only [epv, Pi.smul_apply, smul_eq_mul]
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by ring
  rw [pv, h, map_smul, pv]

/-- Cochrane (2023), §10.1.3, p. 295: for bounded adapted potato sales and `0 ≤ β < 1`, the share
flow plus the transversality condition is equivalent to the share value
`v_t = (1/N) E_t ∑ βʲ s_{t+j}`. -/
theorem share_valuation_iff {β M N : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hN : N ≠ 0)
    {P s v : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s)
    (hP : ∀ t ω, P t ω ≠ 0) :
    (ShareFlow 𝔼 β N P s v ∧ TVC 𝔼 β v) ↔ ∀ t, v t = N⁻¹ • pv 𝔼 β s t := by
  have hs' : ∀ t ω, |(fun t => N⁻¹ • s t) t ω| ≤ |N⁻¹| * M := by
    intro t ω
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hs t ω) (abs_nonneg _)
  have hsa' : 𝔼.Adapted (fun t => N⁻¹ • s t) := fun t => by
    simp only [map_smul, hsa t]
  rw [shareFlow_iff_solves 𝔼 hN hP, flow_tvc_iff_pv 𝔼 hβ0 hβ1 hs' hsa', funext_iff]
  simp only [pv_smul]

/-- Cochrane (2023), §10.1.3, p. 295: "The real value of a share in the goods market must be the
same as the real value of a share in the asset market": with share value `1/P_t`,
`N/P_t = E_t ∑ βʲ s_{t+j}`. -/
theorem potato_price_level {β N : ℝ} (hN : N ≠ 0) {P s v : ℕ → Ω → ℝ}
    (hval : ∀ t, v t = N⁻¹ • pv 𝔼 β s t) (hgoods : ∀ t, v t = (P t)⁻¹) (t : ℕ) (ω : Ω) :
    N / P t ω = pv 𝔼 β s t ω := by
  have h1 := congrFun (hval t) ω
  have h2 := congrFun (hgoods t) ω
  simp only [Pi.smul_apply, smul_eq_mul, Pi.inv_apply] at h1 h2
  rw [div_eq_mul_inv, ← h2, h1]
  field_simp

/-! ### Indexed perpetuities as numeraire: (10.7) -/

/-- Cochrane (2023), eq. (10.7), p. 296: a claim to one good every period is worth
`∑ βʲ = 1/(1 − β)` at every date, `0 ≤ β < 1`. -/
theorem pv_one {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (t : ℕ) :
    pv 𝔼 β (fun (_ : ℕ) (_ : Ω) => (1 : ℝ)) t = fun _ => (1 - β)⁻¹ := by
  have h : epv β (fun (_ : ℕ) (_ : Ω) => (1 : ℝ)) t = fun _ => (1 - β)⁻¹ := by
    funext ω
    simp only [epv, mul_one]
    exact tsum_geometric_of_lt_one hβ0 hβ1
  rw [pv, h, 𝔼.const]

/-- Cochrane (2023), eq. (10.7), p. 296: the perpetuity pays `P_{t+j}` dollars, i.e. one potato,
every period, so its real value is `E_t ∑ βʲ P_{t+j}/P_{t+j} = 1/(1 − β)` (nowhere-zero `P`). -/
theorem perpetuity_real_value {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {P : ℕ → Ω → ℝ}
    (hP : ∀ t ω, P t ω ≠ 0) (t : ℕ) :
    pv 𝔼 β (fun t ω => P t ω / P t ω) t = fun _ => (1 - β)⁻¹ := by
  have h : (fun t ω => P t ω / P t ω) = fun (_ : ℕ) (_ : Ω) => (1 : ℝ) := by
    funext t ω
    exact div_self (hP t ω)
  rw [h, pv_one 𝔼 hβ0 hβ1]

/-- Cochrane (2023), eq. (10.7), p. 296: with `β = 1/(1 + r)`, `r > 0`,
`1/(1 − β) = (1 + r)/r`. -/
theorem one_sub_beta_inv {r : ℝ} (hr : 0 < r) : (1 - 1 / (1 + r))⁻¹ = (1 + r) / r := by
  have h1 : (1 + r) ≠ 0 := by linarith
  have h3 : (1 : ℝ) - 1 / (1 + r) = r / (1 + r) := by
    rw [eq_div_iff h1, sub_mul, one_div, inv_mul_cancel₀ h1]
    ring
  rw [h3, inv_div]

/-- Cochrane (2023), eq. (10.7), p. 296 (survey E10.1, corrected): the dollar is `y/(1 + y)`
perpetuities, so a perpetuity is worth `(1 + y)/y` dollars; `((1 + y)/y)/P_t = (1 + r)/r` holds
iff `P_t = (1 + y) r/((1 + r) y)`. -/
theorem perpetuity_price_level {y r P : ℝ} (hy : 0 < y) (hr : 0 < r) (hP : P ≠ 0) :
    (1 + y) / y / P = (1 + r) / r ↔ P = (1 + y) * r / ((1 + r) * y) := by
  have h1 : (1 + r) ≠ 0 := by linarith
  rw [div_eq_div_iff hP hr.ne', eq_div_iff (mul_ne_zero h1 hy.ne')]
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    field_simp
    linarith

/-- Cochrane (2023), eq. (10.7), p. 296 (survey E10.1): if (10.7) holds at every date and state
(`β = 1/(1 + r)`), the price level is the constant `(1 + y) r/((1 + r) y)`. -/
theorem perpetuity_price_level_process {y r : ℝ} (hy : 0 < y) (hr : 0 < r) {P : ℕ → Ω → ℝ}
    (hP : ∀ t ω, P t ω ≠ 0)
    (h107 : ∀ t ω, (1 + y) / y / P t ω = pv 𝔼 (1 / (1 + r)) (fun t ω => P t ω / P t ω) t ω)
    (t : ℕ) (ω : Ω) : P t ω = (1 + y) * r / ((1 + r) * y) := by
  have hβ0 : 0 ≤ 1 / (1 + r) := by positivity
  have hβ1 : 1 / (1 + r) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h := h107 t ω
  rw [perpetuity_real_value 𝔼 hβ0 hβ1 hP t, one_sub_beta_inv hr] at h
  exact (perpetuity_price_level hy hr (hP t ω)).mp h

/-- Cochrane (2023), p. 296 (survey E10.1): the printed formula `(1 + r) y/((1 + y) r)` is the
reciprocal of the correct price level. -/
theorem printed_reciprocal (y r : ℝ) :
    (1 + r) * y / ((1 + y) * r) = ((1 + y) * r / ((1 + r) * y))⁻¹ := by
  rw [inv_div]

/-- Cochrane (2023), p. 296 (survey E10.1): the printed and the correct price levels agree iff
`y = r` (for `y, r > 0`). -/
theorem printed_eq_iff {y r : ℝ} (hy : 0 < y) (hr : 0 < r) :
    (1 + r) * y / ((1 + y) * r) = (1 + y) * r / ((1 + r) * y) ↔ y = r := by
  have ha : 0 < (1 + r) * y := by positivity
  have hb : 0 < (1 + y) * r := by positivity
  rw [div_eq_div_iff hb.ne' ha.ne']
  constructor
  · intro h
    have h2 : ((1 + r) * y - (1 + y) * r) * ((1 + r) * y + (1 + y) * r) = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · linarith
  · intro h
    rw [h]

/-- Cochrane (2023), p. 296 (survey E10.1): at `r = 0.04`, `y = 0.05` the correct price level is
`21/26 ≈ 0.808` while the printed formula gives `26/21 ≈ 1.238`. -/
theorem printed_counterexample :
    (1 + (0.05 : ℝ)) * 0.04 / ((1 + 0.04) * 0.05) = 21 / 26 ∧
      (1 + (0.04 : ℝ)) * 0.05 / ((1 + 0.05) * 0.04) = 26 / 21 := by
  constructor <;> norm_num

/-- Cochrane (2023), p. 296: "it is convenient to define `y = r` so `P_t = 1`": the corrected
price level equals one iff `y = r` (so the book's conclusion stands). -/
theorem price_level_one_iff {y r : ℝ} (hy : 0 < y) (hr : 0 < r) :
    (1 + y) * r / ((1 + r) * y) = 1 ↔ y = r := by
  rw [div_eq_one_iff_eq (by positivity)]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 296: defining the dollar as `r/(1 + r)` perpetuities each paying one
potato a year gives a dollar worth `(r/(1 + r)) (1 + r)/r = 1` potato, a unit price level. -/
theorem potato_perpetuity_unit {r : ℝ} (hr : 0 < r) : r / (1 + r) * ((1 + r) / r) = 1 := by
  have h1 : (1 + r) ≠ 0 := by linarith
  field_simp

/-- Cochrane (2023), p. 296: for bounded surpluses, subtracting a constant payment `c` every period
lowers the present value by `c/(1 − β)`. -/
theorem pv_sub_const {β M c : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (t : ℕ) :
    pv 𝔼 β (fun t ω => s t ω - c) t = pv 𝔼 β s t - fun _ => c * (1 - β)⁻¹ := by
  have hgeo : Summable (fun j : ℕ => β ^ j) := summable_geometric_of_lt_one hβ0 hβ1
  have h : epv β (fun t ω => s t ω - c) t = epv β s t - fun _ => c * (1 - β)⁻¹ := by
    funext ω
    have hsum : Summable (fun j => β ^ j * s (t + j) ω) :=
      Summable.of_norm_bounded (hgeo.mul_right M) fun j => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
        exact mul_le_mul_of_nonneg_left (hs (t + j) ω) (pow_nonneg hβ0 j)
    simp only [epv, Pi.sub_apply]
    rw [← tsum_geometric_of_lt_one hβ0 hβ1, ← tsum_mul_left, ← hsum.tsum_sub (hgeo.mul_left c)]
    exact tsum_congr fun j => by ring
  rw [pv, h, map_sub, 𝔼.const, pv]

/-- Cochrane (2023), p. 296: "the value of equity must be positive, so the value of the perpetuity
is limited by the present value of potato sales": if the stockholders' claim
`E_t ∑ βʲ (s_{t+j} − M)` is nonnegative, then `M/(1 − β) ≤ E_t ∑ βʲ s_{t+j}`. -/
theorem perpetuity_backing_bound {β Ms M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ Ms) {t : ℕ} {ω : Ω}
    (heq : 0 ≤ pv 𝔼 β (fun t ω => s t ω - M) t ω) : M * (1 - β)⁻¹ ≤ pv 𝔼 β s t ω := by
  rw [pv_sub_const 𝔼 hβ0 hβ1 hs t] at heq
  simp only [Pi.sub_apply] at heq
  linarith

/-! ### One-period indexed bonds as numeraire -/

/-- Cochrane (2023), p. 296: a one-period indexed bond pays `P_{t+1}` dollars, i.e. one potato, at
`t + 1`; its real value at `t` is `β E_t(P_{t+1}/P_{t+1}) = β`. -/
theorem oneperiod_real_value {β : ℝ} {P : ℕ → Ω → ℝ} (hP : ∀ t ω, P t ω ≠ 0) (t : ℕ) :
    β • 𝔼.E t (fun ω => P (t + 1) ω / P (t + 1) ω) = fun _ => β := by
  have h : (fun ω => P (t + 1) ω / P (t + 1) ω) = fun _ => (1 : ℝ) := by
    funext ω
    exact div_self (hP (t + 1) ω)
  rw [h, 𝔼.const]
  funext ω
  simp

/-- Cochrane (2023), p. 296 (survey E10.2, corrected): if the bond is the numeraire, a unit of
numeraire is worth `β` goods, so the price level (numeraire per good) is `P_t = 1/β`, and each
maturing bond (worth one good) is redeemed for `P_t = 1/β` new bonds. -/
theorem oneperiod_price_level {β P : ℝ} : 1 / P = β ↔ P = 1 / β := by
  constructor
  · intro h
    rw [← h, one_div_one_div]
  · intro h
    rw [h, one_div_one_div]

/-- Cochrane (2023), p. 296 (survey E10.2): the printed `P_t = β` is not the price level, since
`β ≠ 1/β` for `0 < β < 1`. -/
theorem printed_beta_wrong {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : β ≠ 1 / β := by
  intro h
  rw [eq_div_iff hβ0.ne'] at h
  nlinarith

/-- Cochrane (2023), pp. 296–297: defining the numeraire as `1 + y` one-period indexed bonds
(`β = 1/(1 + r)`) gives `P_t = (1 + r)/(1 + y)`, equal to one iff `y = r`. -/
theorem numeraire_one_plus_y {y r P : ℝ} (hy : 0 < 1 + y) (hr : 0 < 1 + r) (hP : P ≠ 0)
    (h : 1 / P = (1 + y) * (1 / (1 + r))) : P = (1 + r) / (1 + y) ∧ (P = 1 ↔ y = r) := by
  have hP' : P = (1 + r) / (1 + y) := by
    field_simp at h
    rw [eq_div_iff hy.ne']
    linarith
  refine ⟨hP', ?_⟩
  rw [hP', div_eq_one_iff_eq hy.ne']
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 296: bondholders receive `min(M_t, s_{t+1})` potatoes when stockholder
payments must be nonnegative, so the bonds are worth at most `β M_t`. -/
theorem bond_value_le {β M : ℝ} (hβ : 0 ≤ β) {s : ℕ → Ω → ℝ} (t : ℕ) :
    β • 𝔼.E t (fun ω => min M (s (t + 1) ω)) ≤ fun _ => β * M := by
  intro ω
  have h1 : 𝔼.E t (fun ω => min M (s (t + 1) ω)) ≤ 𝔼.E t (fun _ => M) :=
    𝔼.mono t fun ω => min_le_left _ _
  rw [𝔼.const] at h1
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (h1 ω) hβ

/-- Cochrane (2023), p. 296 (survey E10.4): there is no default, and the bonds are worth exactly
`β M_t`, as soon as `M_t ≤ s_{t+1}` in every state (the book's strict `M_t < min s_{t+1}` is not
needed). -/
theorem bond_value_no_default {β M : ℝ} {s : ℕ → Ω → ℝ} {t : ℕ} (hM : ∀ ω, M ≤ s (t + 1) ω) :
    β • 𝔼.E t (fun ω => min M (s (t + 1) ω)) = fun _ => β * M := by
  have h : (fun ω => min M (s (t + 1) ω)) = fun _ => M := by
    funext ω
    exact min_eq_left (hM ω)
  rw [h, 𝔼.const]
  funext ω
  simp

end Cochrane.AssetsRulesBalanceSheets.SharesAsMoney
