/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.MaturityStructure

/-!
# Maturing debt, the long-term-debt buffer, and roll-over runs

Cochrane (2023), §7.2.1 (pp. 216–218, equation (7.6)) and §7.2.2 (pp. 218–220, equation (7.7) and
the backward-induction display on p. 219).

## Main results

* `debt_eq_initial`, `price_eq_maturing` — (7.6): with no sales or repurchases after the
  inherited structure, `B_{−1}^{(t)}/P_t = B_{t−1}^{(t)}/P_t = s_t` at every date.
* `noSales_solution`: conversely `x_t = s_t / B_{−1}^{(t)}` solves every flow condition.
* `noSales_presentValue`: the present-value relation still holds, term by term.
* `noSales_E_price`, `noSales_bondPrice`: news about `s_{t+j}` moves `E_t(1/P_{t+j})` and the bond
  price `Q_t^{(t+j)} = β^j P_t E_t(s_{t+j})/B^{(t+j)}`.
* `noSales_price_news`, `noSales_bond_news`, `noSales_price_indep`: the buffer: unexpected
  inflation at `t` reflects only news about `s_t`; news about later surpluses shows up in bond
  prices only.
* `oneperiod_flow_iff` — (7.7): with one-period debt only, `B_{t−1}^{(t)}/P_t =
  s_t + β B_t^{(t+1)} E_t(1/P_{t+1})`, and `oneperiod_flow_E` the form with `E_t` outside.
* `oneperiod_backward`, `oneperiod_two_period` — the backward-induction ("run") recursion of
  p. 219: with the debt retired at `T`, `B_{t−1}^{(t)}/P_t = ∑_{k ≤ T−t} β^k E_t s_{t+k}`.
* `oneperiod_fear`: lower expected far-future surpluses raise today's price level.
-/

namespace Cochrane.LongTermDebtDynamics.MaturingDebt

open MaturityStructure

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §7.2.1, p. 216: the government neither sells nor repurchases debt after it
inherits the maturity structure: `B_t^{(t+j)} = B_{t−1}^{(t+j)}` for every `t` and `j ≥ 1`. -/
def NoSales (D : ℕ → ℕ → Ω → ℝ) : Prop := ∀ t j, D (t + 1) (t + (j + 1)) = D t (t + (j + 1))

/-- Cochrane (2023), §7.2.1, p. 216: with no sales, the bond outstanding at 0 becomes the bond
maturing at `t`: `B_{t−1}^{(t+k)} = B_{−1}^{(t+k)}`. -/
theorem debt_eq_initial {D : ℕ → ℕ → Ω → ℝ} (h : NoSales D) (t k : ℕ) :
    D t (t + k) = D 0 (t + k) := by
  induction t generalizing k with
  | zero => rfl
  | succ t ih =>
    rw [show t + 1 + k = t + (k + 1) by omega, h t k, ih]

/-- Cochrane (2023), eq. (7.6), p. 217: with no sales, the flow condition at `t` reads
`B_{−1}^{(t)}/P_t = B_{t−1}^{(t)}/P_t = s_t`. -/
theorem price_eq_maturing {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (h : NoSales D)
    {t : ℕ} (hflow : RealFlow 𝔼 β D x s t) (ω : Ω) : D 0 t ω * x t ω = s t ω := by
  have hz : (fun j : ℕ => β ^ (j + 1) * (sales D t (t + (j + 1)) ω *
      𝔼.E t (x (t + (j + 1))) ω)) = fun _ => 0 := by
    funext j
    simp [sales, h t j]
  have h0 := hflow ω
  rw [hz] at h0
  have := h0.unique hasSum_zero
  have hD := debt_eq_initial h t 0
  rw [add_zero] at hD
  rw [← hD]
  linarith

/-- Cochrane (2023), eq. (7.6), p. 217: conversely, with no sales and `B_{−1}^{(t)} ≠ 0`, the
price levels `x_t = 1/P_t = s_t / B_{−1}^{(t)}` satisfy every flow condition. -/
theorem noSales_solution {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (h : NoSales D)
    (hD : ∀ t ω, D 0 t ω ≠ 0) (hx : ∀ t ω, x t ω = s t ω / D 0 t ω) (t : ℕ) :
    RealFlow 𝔼 β D x s t := by
  intro ω
  have hz : (fun j : ℕ => β ^ (j + 1) * (sales D t (t + (j + 1)) ω *
      𝔼.E t (x (t + (j + 1))) ω)) = fun _ => 0 := by
    funext j
    simp [sales, h t j]
  rw [hz]
  have hD0 := debt_eq_initial h t 0
  rw [add_zero] at hD0
  rw [hD0, hx t ω, mul_div_cancel₀ _ (hD t ω), sub_self]
  exact hasSum_zero

/-- Cochrane (2023), §7.2.1, p. 217: with no sales, `B^{(t+j)} E_t(1/P_{t+j}) = E_t s_{t+j}`, so
news about the surplus `s_{t+j}` moves `E_t(1/P_{t+j})` one for one. -/
theorem noSales_E_price (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (h : NoSales D) (hflow : ∀ t, RealFlow 𝔼 β D x s t) (t j : ℕ) :
    D 0 (t + j) * 𝔼.E t (x (t + j)) = 𝔼.E t (s (t + j)) := by
  have hm : D 0 (t + j) * x (t + j) = s (t + j) := by
    funext ω; exact price_eq_maturing 𝔼 h (hflow (t + j)) ω
  rw [← hpo t _ _ (Predetermined.known 𝔼 hD (Nat.zero_le t) _), hm]

/-- Cochrane (2023), §7.2.1, p. 217: with no sales the bond price is
`Q_t^{(t+j)} B^{(t+j)} = β^j P_t E_t s_{t+j}`: bad news about `s_{t+j}` lowers the bond price. -/
theorem noSales_bondPrice (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {P x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (h : NoSales D) (hP : 𝔼.Adapted P)
    (hflow : ∀ t, RealFlow 𝔼 β D x s t) (t j : ℕ) :
    D 0 (t + j) * bondPrice 𝔼 β P x t j = β ^ j • (P t * 𝔼.E t (s (t + j))) := by
  rw [bondPrice_eq 𝔼 hpo hP, ← noSales_E_price 𝔼 hpo hD h hflow t j]
  funext ω
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), §7.2.1, p. 217: with no sales and bounded surpluses, the present-value
relation (7.2) still holds at every date, term by term. -/
theorem noSales_presentValue (hpo : 𝔼.PullOut) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (h : NoSales D)
    (hsb : ∀ t ω, |s t ω| ≤ M) (hflow : ∀ t, RealFlow 𝔼 β D x s t) (t : ℕ) :
    PresentValue 𝔼 β D x s t := by
  intro ω
  refine ⟨summable_surplusTerm 𝔼 hβ0 hβ1 hsb t ω, ?_⟩
  have heq : (fun j => debtTerm 𝔼 β D x t j ω) = fun j => surplusTerm 𝔼 β s t j ω := by
    funext j
    rw [debtTerm, surplusTerm, debt_eq_initial h t j]
    congr 1
    exact congrFun (noSales_E_price 𝔼 hpo hD h hflow t j) ω
  rw [heq]
  exact (summable_surplusTerm 𝔼 hβ0 hβ1 hsb t ω).hasSum

/-- Cochrane (2023), §7.2.1, p. 217 (the buffer): with no sales, the unexpected price level at
`t + 1` reflects only news about the current surplus,
`B^{(t+1)} (1/P_{t+1} − E_t(1/P_{t+1})) = s_{t+1} − E_t s_{t+1}`. -/
theorem noSales_price_news (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (h : NoSales D) (hflow : ∀ t, RealFlow 𝔼 β D x s t) (t : ℕ) :
    D 0 (t + 1) * (x (t + 1) - 𝔼.E t (x (t + 1))) = s (t + 1) - 𝔼.E t (s (t + 1)) := by
  have hm : D 0 (t + 1) * x (t + 1) = s (t + 1) := by
    funext ω; exact price_eq_maturing 𝔼 h (hflow (t + 1)) ω
  rw [mul_sub, hm, noSales_E_price 𝔼 hpo hD h hflow t 1]

/-- Cochrane (2023), §7.2.1, p. 217 (the buffer): news at `t + 1` about a later surplus
`s_{t+1+j}` moves the expected future price level (and hence bond prices) one for one,
`B^{(t+1+j)} (E_{t+1} − E_t)(1/P_{t+1+j}) = (E_{t+1} − E_t) s_{t+1+j}`. -/
theorem noSales_bond_news (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (h : NoSales D) (hflow : ∀ t, RealFlow 𝔼 β D x s t) (t j : ℕ) :
    D 0 (t + 1 + j) * (𝔼.E (t + 1) (x (t + 1 + j)) - 𝔼.E t (x (t + 1 + j))) =
      𝔼.E (t + 1) (s (t + 1 + j)) - 𝔼.E t (s (t + 1 + j)) := by
  have h1 := noSales_E_price 𝔼 hpo hD h hflow (t + 1) j
  have h2 := noSales_E_price 𝔼 hpo hD h hflow t (1 + j)
  rw [← add_assoc] at h2
  rw [mul_sub, h1, h2]

/-- Cochrane (2023), §7.2.1, pp. 216–217: with no sales, two surplus paths that agree at `t`
(differing only in later surpluses) give the same price level at `t`. -/
theorem noSales_price_indep {β β' : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x x' s s' : ℕ → Ω → ℝ}
    (h : NoSales D) {t : ℕ} (hD : ∀ ω, D 0 t ω ≠ 0) (hflow : RealFlow 𝔼 β D x s t)
    (hflow' : RealFlow 𝔼 β' D x' s' t) (hs : s t = s' t) : x t = x' t := by
  funext ω
  have h1 := price_eq_maturing 𝔼 h hflow ω
  have h2 := price_eq_maturing 𝔼 h hflow' ω
  rw [congrFun hs ω] at h1
  exact mul_left_cancel₀ (hD ω) (h1.trans h2.symm)

/-! ### One-period debt and the roll-over run (§7.2.2) -/

/-- Cochrane (2023), §7.2.2, p. 219: only one-period debt is ever outstanding:
`B_{t−1}^{(t+j)} = 0` for `j ≥ 1` at every date. -/
def OnePeriod (D : ℕ → ℕ → Ω → ℝ) : Prop := ∀ t j, D t (t + (j + 1)) = 0

/-- Cochrane (2023), eq. (7.7), p. 219: with one-period debt the flow condition (7.1) is
`B_{t−1}^{(t)}/P_t = s_t + β B_t^{(t+1)} E_t(1/P_{t+1})`. -/
theorem oneperiod_flow_iff {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (h : OnePeriod D)
    (t : ℕ) :
    RealFlow 𝔼 β D x s t ↔
      D t t * x t = s t + β • (D (t + 1) (t + 1) * 𝔼.E t (x (t + 1))) := by
  have hterms : ∀ ω, (fun j : ℕ => β ^ (j + 1) * (sales D t (t + (j + 1)) ω *
      𝔼.E t (x (t + (j + 1))) ω)) = Pi.single 0
        (β * (D (t + 1) (t + 1) ω * 𝔼.E t (x (t + 1)) ω)) := by
    intro ω
    funext j
    rcases j with _ | j
    · simp [sales, h t 0]
    · have h1 := h (t + 1) j
      rw [show t + 1 + (j + 1) = t + (j + 1 + 1) by omega] at h1
      simp [sales, h1, h t (j + 1)]
  constructor
  · intro hf
    funext ω
    have := (hf ω).unique (by rw [hterms ω]; exact hasSum_pi_single 0 _)
    simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  · intro he ω
    rw [hterms ω]
    have := congrFun he ω
    simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    convert hasSum_pi_single 0 _ using 1
    linarith

/-- Cochrane (2023), eq. (7.7), p. 219: the same condition with the expectation outside,
`B_{t−1}^{(t)}/P_t = s_t + E_t(β B_t^{(t+1)}/P_{t+1})` (pull-out of the known `B_t^{(t+1)}`). -/
theorem oneperiod_flow_E (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (h : OnePeriod D) (t : ℕ) :
    RealFlow 𝔼 β D x s t ↔
      D t t * x t = s t + 𝔼.E t (β • (D (t + 1) (t + 1) * x (t + 1))) := by
  rw [oneperiod_flow_iff 𝔼 h, map_smul, hpo t _ _ (hD.2 t _)]

/-- Cochrane (2023), §7.2.2, p. 219 (backward induction): with one-period debt that is retired at
`T` (`B_T^{(T+1)} = 0`), the real value of maturing debt at `t ≤ T` is the finite present value
`B_{t−1}^{(t)}/P_t = ∑_{k ≤ T−t} β^k E_t s_{t+k}`. -/
theorem oneperiod_backward (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (h : OnePeriod D) (hs : 𝔼.Adapted s) {T : ℕ}
    (hT : D (T + 1) (T + 1) = 0) (hflow : ∀ t, RealFlow 𝔼 β D x s t) {t : ℕ} (htT : t ≤ T) :
    D t t * x t = ∑ k ∈ Finset.range (T - t + 1), β ^ k • 𝔼.E t (s (t + k)) := by
  have hf : ∀ t, D t t * x t = s t + 𝔼.E t (β • (D (t + 1) (t + 1) * x (t + 1))) :=
    fun t => (oneperiod_flow_E 𝔼 hpo hD h t).mp (hflow t)
  -- prove for `t = T - n` with `n ≤ T`, by induction on `n`
  have key : ∀ n, n ≤ T → D (T - n) (T - n) * x (T - n) =
      ∑ k ∈ Finset.range (n + 1), β ^ k • 𝔼.E (T - n) (s (T - n + k)) := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [Nat.sub_zero, hf T, hT]
      simp [hs T]
    | succ n ih =>
      intro hn
      have ht : T - n = T - (n + 1) + 1 := by omega
      rw [hf (T - (n + 1)), ← ht, ih (by omega)]
      conv_rhs => rw [Finset.sum_range_succ']
      rw [map_smul, map_sum, Finset.smul_sum, add_comm]
      congr 1
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smul, 𝔼.tower (by omega : T - (n + 1) ≤ T - n), smul_smul, ← pow_succ',
          show T - n + k = T - (n + 1) + (k + 1) by omega]
      · simp [hs (T - (n + 1))]
  have := key (T - t) (Nat.sub_le T t)
  rwa [Nat.sub_sub_self htT] at this

/-- Cochrane (2023), §7.2.2, p. 219: the last two steps of the backward induction,
`B_{T−2}^{(T−1)}/P_{T−1} = s_{T−1} + E_{T−1}(β s_T)` when the debt is retired at `T` (here with
last payment date `T + 1`). -/
theorem oneperiod_two_period (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ}
    {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (h : OnePeriod D) (hs : 𝔼.Adapted s) {T : ℕ}
    (hT : D (T + 1 + 1) (T + 1 + 1) = 0) (hflow : ∀ t, RealFlow 𝔼 β D x s t) :
    D T T * x T = s T + 𝔼.E T (β • s (T + 1)) := by
  have := oneperiod_backward 𝔼 hpo hD h hs hT hflow (t := T) (by omega)
  rw [show T + 1 - T + 1 = 2 by omega] at this
  rw [this, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, one_smul, pow_one, add_zero,
    hs, map_smul]

/-- Cochrane (2023), §7.2.2, pp. 219–220: fear of low surpluses far in the future raises today's
price level: with one-period debt retired at `T`, positive maturing debt, and two surplus
processes with `s' ≤ s`, the price levels satisfy `1/P'_t ≤ 1/P_t` at every `t ≤ T`. -/
theorem oneperiod_fear (hpo : 𝔼.PullOut) {β : ℝ} (hβ : 0 ≤ β) {D : ℕ → ℕ → Ω → ℝ}
    {x x' s s' : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (h : OnePeriod D) (hs : 𝔼.Adapted s)
    (hs' : 𝔼.Adapted s') {T : ℕ} (hT : D (T + 1) (T + 1) = 0) (hpos : ∀ t ω, 0 < D t t ω)
    (hflow : ∀ t, RealFlow 𝔼 β D x s t) (hflow' : ∀ t, RealFlow 𝔼 β D x' s' t)
    (hss : ∀ t, s' t ≤ s t) {t : ℕ} (htT : t ≤ T) (ω : Ω) : x' t ω ≤ x t ω := by
  have h1 := congrFun (oneperiod_backward 𝔼 hpo hD h hs hT hflow htT) ω
  have h2 := congrFun (oneperiod_backward 𝔼 hpo hD h hs' hT hflow' htT) ω
  simp only [Pi.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  have hle : D t t ω * x' t ω ≤ D t t ω * x t ω := by
    rw [h1, h2]
    exact Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left (𝔼.mono _ (hss _) ω) (pow_nonneg hβ k)
  exact le_of_mul_le_mul_left hle (hpos _ ω)

end Cochrane.LongTermDebtDynamics.MaturingDebt
