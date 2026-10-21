/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.SpreadTarget

/-!
# Debt sales with a spread target

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.4.2
"Debt sales with a spread target", eq. (9.27), pp. 278–280.

The end-of-period valuation equation (9.27) is `β b_t + β B_t E_t(1/P_{t+1}) = W` with
`W = E_t ∑_{j≥1} βʲ s_{t+j}` held fixed. Write `e = E_t(1/P_{t+1})`. The government sold `b₀` real
and
`B₀` nominal bonds and then swaps `P*` nominal bonds for each real bond,
`−(B_t − B₀) = (b_t − b₀) P*`.

## Main results

* `eq_9_27`: `Q_t B_t/P_t = β B_t E_t(1/P_{t+1})` (pull-out property); `end_of_period_valuation`.
* `market_price_irrelevant`: swaps at the market rate `e₀` leave `E_t(1/P_{t+1})` unchanged.
* `swap_valuation_iff`, `hasDerivAt_eSwap`: after a swap at `P*`, `e(B) = (W/β − b₀ + (B −
B₀)/P*)/B`
  and `de/dB = −(e − 1/P*)/B` (the book's differential, p. 280).
* **The hyperbola (error E9.8)**: `eSwap_sub_target`: `e(B) − 1/P* = C/B` with
  `C = W/β − b₀ − B₀/P* = B₀(e₀ − 1/P*)`; `swap_reaches_target_iff`: free exchange at `P*` reaches
  `E_t(1/P_{t+1}) = 1/P*` at some finite `B` iff the gap was zero to begin with — the book's bullet
  "offering to freely exchange real debt for nominal debt at the rate `P*` … drives the expected
  price level to `E_t(1/P_{t+1}) = 1/P*`" does not follow; `real_debt_exhausted`: when the public's
  real debt is exhausted the gap is still `C/(B₀ + P* b₀)`; `numeric_example` (gap `7/30 → 35/222`).
* `eSwap_strictAntiOn`, `eSwap_gt_target`: the book's qualitative direction is right — with
  `1/P* < e₀` the expected inverse price level falls as nominal debt rises, but stays above `1/P*`.
* `swap_invariant`, `passive_supply` (the corrected statement): swaps at `P*` leave `b + B/P*`
  unchanged, and the target is reached iff `β(b + B/P*) = W`; a passive supply of nominal debt
  (sold for goods, as with an interest-rate peg) reaches it at the unique `B = P*(W/β − b)`.
-/

namespace Cochrane.AssetsRulesBalanceSheets.SpreadSwap

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), eq. (9.27), p. 279: with the nominal bond price `Q_t = β E_t(P_t/P_{t+1})`, the
pull-out property and `B_t`, `P_t` known at `t`, `Q_t B_t/P_t = β B_t E_t(1/P_{t+1})`. -/
theorem eq_9_27 (h𝔼 : 𝔼.PullOut) {β : ℝ} {P B Q : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω)
    (hPa : 𝔼.Adapted P) (hQ : ∀ t, Q t = β • 𝔼.E t (P t / P (t + 1))) (t : ℕ) :
    Q t * B t / P t = β • (B t * 𝔼.E t (fun ω => 1 / P (t + 1) ω)) := by
  have hsplit : P t / P (t + 1) = P t * fun ω => 1 / P (t + 1) ω := by
    funext ω
    simp only [Pi.div_apply, Pi.mul_apply]
    ring
  rw [hQ t, hsplit, h𝔼 t _ _ (hPa t)]
  funext ω
  simp only [Pi.div_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [(hP t ω).ne']

/-- Cochrane (2023), eq. (9.27), p. 279: subtracting the date-`t` surplus from the valuation
equation `b_{t−1} + B_{t−1}/P_t = E_t ∑_{j≥0} βʲ s_{t+j} = s_t + W` and the flow condition
`b_{t−1} + B_{t−1}/P_t = s_t + β b_t + Q_t B_t/P_t` gives `β b_t + Q_t B_t/P_t = W`. -/
theorem end_of_period_valuation {bprev Bprev P s b B Q W β : ℝ}
    (hval : bprev + Bprev / P = s + W) (hflow : bprev + Bprev / P = s + β * b + Q * B / P) :
    β * b + Q * B / P = W := by
  linarith

/-- Cochrane (2023), §9.4.2, p. 279: "if it exchanges real for nominal bonds at market prices, the
left-hand side does not change" — swapping at the market rate `e₀` (`b = b₀ − (B − B₀) e₀`) leaves
`E_t(1/P_{t+1}) = e₀` as the unique solution of (9.27), for every `B ≠ 0`. -/
theorem market_price_irrelevant {β W b0 B0 e0 B e : ℝ} (hβ : β ≠ 0) (hB : B ≠ 0)
    (h0 : β * b0 + β * B0 * e0 = W) :
    β * (b0 - (B - B0) * e0) + β * B * e = W ↔ e = e0 := by
  constructor
  · intro h
    have h2 : β * B * (e - e0) = 0 := by linear_combination h - h0
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 (mul_ne_zero hβ hB)
    · linarith
  · intro h
    rw [h, ← h0]
    ring

/-- Cochrane (2023), §9.4.2, pp. 279–280: the expected inverse price level after swapping
`B − B₀` nominal bonds at `P*`, `e(B) = (W/β − b₀ + (B − B₀)/P*)/B`. -/
noncomputable def eSwap (β W b0 B0 Pstar B : ℝ) : ℝ := (W / β - b0 + (B - B0) / Pstar) / B

/-- Cochrane (2023), §9.4.2, p. 279 (the display after "Plug into (9.27)"): with real debt
`b = b₀ − (B − B₀)/P*`, the valuation (9.27) holds iff `E_t(1/P_{t+1}) = e(B)`. -/
theorem swap_valuation_iff {β W b0 B0 Pstar B e : ℝ} (hβ : β ≠ 0) (hB : B ≠ 0) :
    β * (b0 - (B - B0) / Pstar) + β * B * e = W ↔ e = eSwap β W b0 B0 Pstar B := by
  unfold eSwap
  rw [eq_div_iff hB]
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    field_simp at h
    linear_combination h

/-- Cochrane (2023), §9.4.2, p. 280 (**error E9.8**, the hyperbola): integrating the book's
differential, `e(B) − 1/P* = C/B` with `C = W/β − b₀ − B₀/P*`. -/
theorem eSwap_sub_target {β W b0 B0 Pstar B : ℝ} (hP : Pstar ≠ 0) (hB : B ≠ 0) :
    eSwap β W b0 B0 Pstar B - 1 / Pstar = (W / β - b0 - B0 / Pstar) / B := by
  unfold eSwap
  field_simp
  ring

/-- Cochrane (2023), §9.4.2, p. 280 (the book's differential): `d e/dB = −(e − 1/P*)/B`. -/
theorem hasDerivAt_eSwap {β W b0 B0 Pstar B : ℝ} (hP : Pstar ≠ 0) (hB : B ≠ 0) :
    HasDerivAt (eSwap β W b0 B0 Pstar)
      (-(eSwap β W b0 B0 Pstar B - 1 / Pstar) / B) B := by
  set C := W / β - b0 - B0 / Pstar with hC
  have h := HasDerivAt.add_const (1 / Pstar) (HasDerivAt.const_mul C (hasDerivAt_inv hB))
  have hev : eSwap β W b0 B0 Pstar =ᶠ[𝓝 B] fun B => C * B⁻¹ + 1 / Pstar := by
    filter_upwards [isOpen_ne.mem_nhds hB] with B' hB'
    have := eSwap_sub_target (β := β) (W := W) (b0 := b0) (B0 := B0) hP hB'
    rw [← hC] at this
    have e2 : C / B' = C * B'⁻¹ := div_eq_mul_inv _ _
    linarith
  refine HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq h hev) ?_
  rw [eSwap_sub_target hP hB, ← hC]
  field_simp

/-- Cochrane (2023), §9.4.2, p. 280 (E9.8): the constant of the hyperbola is the initial gap times
initial nominal debt, `C = B₀ (e₀ − 1/P*)` with `e₀ = e(B₀)` the pre-swap market value. -/
theorem gap_const {β W b0 B0 Pstar : ℝ} (hB0 : B0 ≠ 0) :
    W / β - b0 - B0 / Pstar = B0 * (eSwap β W b0 B0 Pstar B0 - 1 / Pstar) := by
  unfold eSwap
  field_simp
  ring

/-- Cochrane (2023), §9.4.2, p. 280 (**error E9.8**): free exchange at `P*` with surpluses and the
initial sales held fixed reaches `E_t(1/P_{t+1}) = 1/P*` at some finite nonzero `B` if and only if
the initial gap `e₀ − 1/P*` is already zero; otherwise the gap shrinks like `1/B` but never closes.
-/
theorem swap_reaches_target_iff {β W b0 B0 Pstar : ℝ} (hP : Pstar ≠ 0) (hB0 : B0 ≠ 0) :
    (∃ B, B ≠ 0 ∧ eSwap β W b0 B0 Pstar B = 1 / Pstar) ↔
      eSwap β W b0 B0 Pstar B0 = 1 / Pstar := by
  constructor
  · rintro ⟨B, hB, h⟩
    have h1 := eSwap_sub_target (β := β) (W := W) (b0 := b0) (B0 := B0) hP hB
    rw [h, sub_self] at h1
    have hC : W / β - b0 - B0 / Pstar = 0 := by
      have := h1.symm
      rwa [div_eq_zero_iff, or_iff_left hB] at this
    have h2 := gap_const (β := β) (W := W) (b0 := b0) (Pstar := Pstar) hB0
    rw [hC] at h2
    have := (mul_eq_zero.mp h2.symm).resolve_left hB0
    linarith
  · intro h
    exact ⟨B0, hB0, h⟩

/-- Cochrane (2023), §9.4.2, p. 280 (E9.8): the public's real debt `b₀ − (B − B₀)/P*` is exhausted
at
`B₁ = B₀ + P* b₀`, where the gap is still `C/B₁`. -/
theorem real_debt_exhausted {β W b0 B0 Pstar : ℝ} (hP : Pstar ≠ 0) (hB1 : B0 + Pstar * b0 ≠ 0) :
    b0 - ((B0 + Pstar * b0) - B0) / Pstar = 0 ∧
      eSwap β W b0 B0 Pstar (B0 + Pstar * b0) - 1 / Pstar =
        (W / β - b0 - B0 / Pstar) / (B0 + Pstar * b0) := by
  refine ⟨by field_simp; ring, eSwap_sub_target hP hB1⟩

/-- Cochrane (2023), §9.4.2, p. 280: the book's direction is right — if `1/P* < e₀` (the government
offers more nominal bonds per real bond than the market) then, for `B > 0`, `E_t(1/P_{t+1})` falls
strictly as nominal debt rises. -/
theorem eSwap_strictAntiOn {β W b0 B0 Pstar : ℝ} (hP : Pstar ≠ 0)
    (hC : 0 < W / β - b0 - B0 / Pstar) :
    StrictAntiOn (eSwap β W b0 B0 Pstar) (Set.Ioi 0) := by
  intro B₁ h₁ B₂ h₂ hlt
  simp only [Set.mem_Ioi] at h₁ h₂
  have e1 := eSwap_sub_target (β := β) (W := W) (b0 := b0) (B0 := B0) hP h₁.ne'
  have e2 := eSwap_sub_target (β := β) (W := W) (b0 := b0) (B0 := B0) hP h₂.ne'
  have : (W / β - b0 - B0 / Pstar) / B₂ < (W / β - b0 - B0 / Pstar) / B₁ :=
    div_lt_div_of_pos_left hC h₁ hlt
  linarith

/-- Cochrane (2023), §9.4.2, p. 280 (E9.8): with a positive gap the expected inverse price level
stays strictly above the target at every `B > 0`. -/
theorem eSwap_gt_target {β W b0 B0 Pstar B : ℝ} (hP : Pstar ≠ 0) (hB : 0 < B)
    (hC : 0 < W / β - b0 - B0 / Pstar) : 1 / Pstar < eSwap β W b0 B0 Pstar B := by
  have e1 := eSwap_sub_target (β := β) (W := W) (b0 := b0) (B0 := B0) hP hB.ne'
  have : 0 < (W / β - b0 - B0 / Pstar) / B := div_pos hC hB
  linarith

/-- Cochrane (2023), §9.4.2, p. 280 (E9.8), the survey's numerical example: `W = 10`, `β = 0.96`,
`b₀ = 3`, `B₀ = 5`, `P* = 0.8`. Then `C = 7/6`, the gap is `7/30 ≈ 0.233` before the swaps and
`35/222 ≈ 0.158` when the public's real debt is exhausted (`B = 7.4`). -/
theorem numeric_example :
    (10 : ℝ) / (24 / 25) - 3 - 5 / (4 / 5) = 7 / 6 ∧
      eSwap (24 / 25) 10 3 5 (4 / 5) 5 - 1 / (4 / 5) = 7 / 30 ∧
      eSwap (24 / 25) 10 3 5 (4 / 5) (5 + 4 / 5 * 3) - 1 / (4 / 5) = 35 / 222 ∧
      (3 : ℝ) - ((5 + 4 / 5 * 3) - 5) / (4 / 5) = 0 := by
  unfold eSwap
  norm_num

/-- Cochrane (2023), §9.4.2, p. 279: a swap at `P*` (`−(B − B₀) = (b − b₀)P*`) leaves `b + B/P*`
unchanged. -/
theorem swap_invariant {b b0 B B0 Pstar : ℝ} (hP : Pstar ≠ 0)
    (hswap : -(B - B0) = (b - b0) * Pstar) : b + B / Pstar = b0 + B0 / Pstar := by
  have : B = B0 - (b - b0) * Pstar := by linarith
  rw [this]
  field_simp
  ring

/-- Cochrane (2023), §9.4.2, p. 280 (the corrected statement, E9.8): the target `E_t(1/P_{t+1}) =
1/P*`
is consistent with (9.27) iff the total debt valued at the target equals the present value,
`β(b + B/P*) = W`. Swaps at `P*` cannot change `b + B/P*` (`swap_invariant`); a passive supply of
nominal debt sold for goods (as with an interest-rate peg, the book's `P* = ∞` case) reaches the
target at the unique `B = P*(W/β − b)`. -/
theorem passive_supply {β W b Pstar : ℝ} (hβ : β ≠ 0) (hP : Pstar ≠ 0) :
    (∀ B, β * b + β * B * (1 / Pstar) = W ↔ β * (b + B / Pstar) = W) ∧
      ∃! B, β * b + β * B * (1 / Pstar) = W := by
  refine ⟨fun B => by constructor <;> intro h <;> linear_combination h, ?_⟩
  refine ⟨Pstar * (W / β - b), ?_, fun B hB => ?_⟩
  · field_simp
    ring
  · field_simp at hB
    field_simp
    linear_combination hB

end Cochrane.AssetsRulesBalanceSheets.SpreadSwap
