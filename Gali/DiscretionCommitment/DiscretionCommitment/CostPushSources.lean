/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DiscretionCommitment.LossAndCostPush
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Sources of cost-push shocks

Galí (2015), Chapter 5, Appendix 5.2 (pp. 156–157). Constant returns to labour (`α = 0`) as
in the book, so `λ = (1 − θ)(1 − βθ)/θ` and `κ = λ(σ + φ)`.

## Exogenous variations in desired price markups

* `resetPrice_solves`: the optimal reset price
  `p*_t = (1 − βθ) ∑_{k ≥ 0} (βθ)ᵏ E_t{μⁿ_{t+k} + ψ_{t+k}}` (a genuine infinite sum) satisfies
  the recursion `p*_t = (1 − βθ)(μⁿ_t + ψ_t) + βθ E_t p*_{t+1}`.
* `inflation_eq_markupGap`: with the Calvo index `p_t = θ p_{t−1} + (1 − θ) p*_t`, this gives
  `π_t = β E_t π_{t+1} − λ(μ_t − μⁿ_t)` exactly.
* `nkpc_priceMarkup`: with flexible wages and a subsidy that corrects the steady-state markup,
  `μ_t − μ = −(σ + φ)(y_t − y^e_t)` and `π_t = β E_t π_{t+1} + κ(y_t − y^e_t) + u_t` with
  `u_t = λ μ̂ⁿ_t`.
* **C5-7** (the printed sums start at `k = 1`): `weights_sum_k0` (the weights
  `(1 − βθ)(βθ)ᵏ`, `k ≥ 0`, sum to one), `weights_sum_k1` (from `k = 1` they sum to `βθ ≠ 1`),
  `printedResetPrice_const` (the printed rule sets `p* = βθ (μⁿ + ψ)` in a steady state instead
  of `μⁿ + ψ`), and `printed_priceSetting_breaks_nkpc`: a perfect-foresight steady state that
  satisfies the printed price-setting rule and the Calvo index but violates the NKPC.

## Exogenous variations in wage markups

* `priceMarkup_eq`: `μ_t = p_t − (w_t − a_t) = −μ_{w,t} − (σ + φ) y_t + (1 + φ) a_t`.
* **C5-6** (sign): `printed_markup_line_iff` (the printed line `μ_t = +μ_{w,t} − …` holds iff
  `μ_{w,t} = 0`), `markupGap_wage`, `nkpc_wageMarkup` (`u_t = +λ(μ_{w,t} − μ_w)`),
  `printed_wage_costPush_contradiction` (the printed `u_t = −λ(μ_{w,t} − μ_w)` contradicts the
  derivation whenever `λ ≠ 0` and the wage markup is away from steady state), and
  `wageMarkup_costPush_pos` (a higher wage markup is inflationary).
-/

namespace Gali.DiscretionCommitment.CostPushSources

open Gali.DiscretionCommitment.LossAndCostPush

/-- Galí (2015), App. 5.2, p. 157 (with `α = 0`; ch. 3, p. 61): the slope of inflation with
respect to the markup gap, `λ = (1 − θ)(1 − βθ)/θ`. -/
noncomputable def lambdaCalvo (β θ : ℝ) : ℝ := (1 - θ) * (1 - β * θ) / θ

/-- Galí (2015), App. 5.2, p. 156: with constant returns (`α = 0`), `Θ = 1` and the general
`λ` of chapter 3 reduces to `(1 − θ)(1 − βθ)/θ`. -/
theorem lambdaNK_alpha_zero (β θ ε : ℝ) : lambdaNK β θ 0 ε = lambdaCalvo β θ := by
  unfold lambdaNK bigTheta lambdaCalvo
  simp

/-- Galí (2015), App. 5.2, p. 156: `λ > 0` for `0 < θ < 1` and `β < 1`. -/
theorem lambdaCalvo_pos {β θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ1 : β < 1) :
    0 < lambdaCalvo β θ := by
  unfold lambdaCalvo
  have h1 : 0 < 1 - β * θ := by nlinarith
  exact div_pos (mul_pos (by linarith) h1) hθ0

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Desired price markups: the price-setting rule and the Calvo index -/

/-- Galí (2015), App. 5.2, p. 156 (corrected, C5-7): the optimal reset price
`p*_t = (1 − βθ) ∑_{k ≥ 0} (βθ)ᵏ E_t{μⁿ_{t+k} + ψ_{t+k}}`, `ψ` nominal marginal cost and
`μⁿ` the desired markup. -/
noncomputable def resetPrice (β θ : ℝ) (μn ψ : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (1 - β * θ) • 𝔼.forwardSeries (β * θ) (fun s => μn s + ψ s) t

/-- Galí (2015), App. 5.2, p. 156 (C5-7): the price-setting rule **as printed**, with the sums
starting at `k = 1`: `(1 − βθ) ∑_{k ≥ 1} (βθ)ᵏ E_t{μⁿ_{t+k} + ψ_{t+k}}`. -/
noncomputable def printedResetPrice (β θ : ℝ) (μn ψ : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (1 - β * θ) * ∑' k, (β * θ) ^ (k + 1) * 𝔼.E t (μn (t + (k + 1)) + ψ (t + (k + 1))) ω

/-- Galí (2015), App. 5.2, p. 156 (and ch. 3, eq. (11), p. 57): for bounded adapted desired
markups and marginal costs and `0 ≤ βθ < 1`, the reset price (a genuine infinite sum) satisfies
the recursion `p*_t = (1 − βθ)(μⁿ_t + ψ_t) + βθ E_t p*_{t+1}`. -/
theorem resetPrice_solves {β θ M : ℝ} (h0 : 0 ≤ β * θ) (h1 : β * θ < 1) {μn ψ : ℕ → Ω → ℝ}
    (hb : ∀ t ω, |μn t ω + ψ t ω| ≤ M) (ha : 𝔼.Adapted fun s => μn s + ψ s) (t : ℕ) :
    resetPrice 𝔼 β θ μn ψ t
      = (1 - β * θ) • (μn t + ψ t) + (β * θ) • 𝔼.E t (resetPrice 𝔼 β θ μn ψ (t + 1)) := by
  unfold resetPrice
  rw [𝔼.forwardSeries_solves h0 h1 (u := fun s => μn s + ψ s) hb ha t, map_smul, smul_add,
    smul_comm (1 - β * θ) (β * θ)]
  abel

/-- Galí (2015), App. 5.2, pp. 156–157 (**the inflation equation, exact**). Let prices be
adapted, `p_{t+1} = θ p_t + (1 − θ) p*_{t+1}` (the Calvo index, log-linear), and the reset
price satisfy `p*_t = (1 − βθ)(μⁿ_t + ψ_t) + βθ E_t p*_{t+1}`. Then, with the markup
`μ_t = p_t − ψ_t` and `π_t = p_t − p_{t−1}`, at every date `t ≥ 1`
`π_t = β E_t π_{t+1} − λ(μ_t − μⁿ_t)`. -/
theorem inflation_eq_markupGap {β θ : ℝ} (hθ : θ ≠ 0) {p pstar μn ψ : ℕ → Ω → ℝ}
    (hp : 𝔼.Adapted p) (hcalvo : ∀ t, p (t + 1) = θ • p t + (1 - θ) • pstar (t + 1))
    (hreset : ∀ t, pstar t = (1 - β * θ) • (μn t + ψ t) + (β * θ) • 𝔼.E t (pstar (t + 1)))
    (t : ℕ) :
    p (t + 1) - p t = β • 𝔼.E (t + 1) (p (t + 2) - p (t + 1)) -
      lambdaCalvo β θ • ((p (t + 1) - ψ (t + 1)) - μn (t + 1)) := by
  have hE : 𝔼.E (t + 1) (p (t + 2)) =
      θ • p (t + 1) + (1 - θ) • 𝔼.E (t + 1) (pstar (t + 2)) := by
    rw [hcalvo (t + 1), map_add, map_smul, map_smul, hp (t + 1)]
  funext ω
  have c1 := congrFun (hcalvo t) ω
  have c2 := congrFun hE ω
  have r := congrFun (hreset (t + 1)) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at c1 c2 r
  rw [show t + 1 + 1 = t + 2 from rfl] at r
  simp only [map_sub, hp (t + 1), Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hl : lambdaCalvo β θ * θ = (1 - θ) * (1 - β * θ) := by
    unfold lambdaCalvo
    field_simp
  apply mul_left_cancel₀ hθ
  linear_combination c1 - θ * β * c2 + (1 - θ) * r +
    (p (t + 1) ω - ψ (t + 1) ω - μn (t + 1) ω) * hl

/-- Galí (2015), App. 5.2, p. 157: with constant returns, flexible wages `w_t − p_t = mrs_t`,
`mrs_t = σ y_t + φ n_t`, `n_t = y_t − a_t`, nominal marginal cost `ψ_t = w_t − a_t`, and
efficient output defined by the subsidy-corrected steady-state markup,
`μ = −(σ + φ) y^e_t + (1 + φ) a_t`, the markup gap is `μ_t − μ = −(σ + φ)(y_t − y^e_t)`. -/
theorem markupGap_price {σ φ μbar p w ψ y n a ye : ℝ} (hmrs : w - p = σ * y + φ * n)
    (hn : n = y - a) (hψ : ψ = w - a) (hye : μbar = -(σ + φ) * ye + (1 + φ) * a) :
    (p - ψ) - μbar = -(σ + φ) * (y - ye) := by
  subst hn hψ hye
  linear_combination -hmrs

/-- Galí (2015), App. 5.2, p. 157 (**desired price markup shocks as cost-push shocks**): under
the hypotheses of `inflation_eq_markupGap` and `markupGap_price` (at every date), inflation
satisfies `π_t = β E_t π_{t+1} + κ(y_t − y^e_t) + u_t` with `κ = λ(σ + φ)` and
`u_t = λ μ̂ⁿ_t`, `μ̂ⁿ_t = μⁿ_t − μ`. -/
theorem nkpc_priceMarkup {β θ σ φ μbar : ℝ} (hθ : θ ≠ 0) {p pstar μn ψ w y n a ye : ℕ → Ω → ℝ}
    (hp : 𝔼.Adapted p) (hcalvo : ∀ t, p (t + 1) = θ • p t + (1 - θ) • pstar (t + 1))
    (hreset : ∀ t, pstar t = (1 - β * θ) • (μn t + ψ t) + (β * θ) • 𝔼.E t (pstar (t + 1)))
    (hmrs : ∀ t ω, w t ω - p t ω = σ * y t ω + φ * n t ω) (hn : ∀ t ω, n t ω = y t ω - a t ω)
    (hψ : ∀ t ω, ψ t ω = w t ω - a t ω)
    (hye : ∀ t ω, μbar = -(σ + φ) * ye t ω + (1 + φ) * a t ω) (t : ℕ) :
    p (t + 1) - p t = β • 𝔼.E (t + 1) (p (t + 2) - p (t + 1)) +
      (lambdaCalvo β θ * (σ + φ)) • (y (t + 1) - ye (t + 1)) +
      lambdaCalvo β θ • (μn (t + 1) - fun _ => μbar) := by
  rw [inflation_eq_markupGap 𝔼 hθ hp hcalvo hreset t]
  funext ω
  have hg := markupGap_price (hmrs (t + 1) ω) (hn (t + 1) ω) (hψ (t + 1) ω) (hye (t + 1) ω)
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-lambdaCalvo β θ) * hg

/-! ### C5-7: the printed sums from `k = 1` -/

/-- Galí (2015), App. 5.2, p. 156 (corrected, C5-7): the weights `(1 − βθ)(βθ)ᵏ`, `k ≥ 0`,
sum to one. -/
theorem weights_sum_k0 {β θ : ℝ} (h0 : 0 ≤ β * θ) (h1 : β * θ < 1) :
    HasSum (fun k : ℕ => (1 - β * θ) * (β * θ) ^ k) 1 := by
  have h := (hasSum_geometric_of_lt_one h0 h1).mul_left (1 - β * θ)
  rwa [mul_inv_cancel₀ (by linarith)] at h

/-- Galí (2015), App. 5.2, p. 156 (**C5-7**): the printed weights `(1 − βθ)(βθ)ᵏ`, `k ≥ 1`,
sum to `βθ`, which is not one for `0 ≤ βθ < 1`. -/
theorem weights_sum_k1 {β θ : ℝ} (h0 : 0 ≤ β * θ) (h1 : β * θ < 1) :
    HasSum (fun k : ℕ => (1 - β * θ) * (β * θ) ^ (k + 1)) (β * θ) ∧ β * θ ≠ 1 := by
  refine ⟨?_, h1.ne⟩
  have h := ((hasSum_geometric_of_lt_one h0 h1).mul_left (1 - β * θ)).mul_left (β * θ)
  rw [mul_inv_cancel₀ (by linarith), mul_one] at h
  convert h using 1
  funext k
  ring

/-- Galí (2015), App. 5.2, p. 156: with constant `μⁿ + ψ = c` the correct rule sets the reset
price at `p* = c` (the frictionless markup over marginal cost). -/
theorem resetPrice_const {β θ c : ℝ} (h0 : 0 ≤ β * θ) (h1 : β * θ < 1) {μn ψ : ℕ → Ω → ℝ}
    (hc : ∀ t, μn t + ψ t = fun _ => c) (t : ℕ) :
    resetPrice 𝔼 β θ μn ψ t = fun _ => c := by
  funext ω
  unfold resetPrice ExpectationSystem.forwardSeries
  beta_reduce
  simp only [Pi.smul_apply, smul_eq_mul]
  have he : ∀ k, (β * θ) ^ k * 𝔼.E t (μn (t + k) + ψ (t + k)) ω = c * (β * θ) ^ k := by
    intro k
    rw [hc (t + k), 𝔼.const]
    ring
  rw [tsum_congr he, tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
  field_simp [show (1 : ℝ) - β * θ ≠ 0 by linarith]

/-- Galí (2015), App. 5.2, p. 156 (**C5-7**): with constant `μⁿ + ψ = c` the printed rule
(sums from `k = 1`) sets `p* = βθ c ≠ c` (for `c ≠ 0`): the reset price is not the
frictionless markup over marginal cost even in a steady state. -/
theorem printedResetPrice_const {β θ c : ℝ} (h0 : 0 ≤ β * θ) (h1 : β * θ < 1)
    {μn ψ : ℕ → Ω → ℝ} (hc : ∀ t, μn t + ψ t = fun _ => c) (t : ℕ) :
    printedResetPrice 𝔼 β θ μn ψ t = fun _ => β * θ * c := by
  funext ω
  unfold printedResetPrice
  have he : ∀ k : ℕ, (β * θ) ^ (k + 1) * 𝔼.E t (μn (t + (k + 1)) + ψ (t + (k + 1))) ω
      = c * (β * θ) * (β * θ) ^ k := by
    intro k
    rw [hc, 𝔼.const]
    ring
  rw [show (fun k : ℕ => (β * θ) ^ (k + 1) * 𝔼.E t (μn (t + (k + 1)) + ψ (t + (k + 1))) ω) =
      fun k => c * (β * θ) * (β * θ) ^ k from funext he, tsum_mul_left,
    tsum_geometric_of_lt_one h0 h1]
  field_simp [show (1 : ℝ) - β * θ ≠ 0 by linarith]

/-- Galí (2015), App. 5.2, pp. 156–157 (**C5-7: the printed rule does not yield the NKPC**).
For every `0 < β < 1`, `0 < θ < 1` there is a perfect-foresight path (a steady state with
price level `1`, marginal cost `1/(βθ)` and `μⁿ = 0`) that satisfies the printed price-setting
rule (sums from `k = 1`) and the Calvo index, but violates
`π_t = β E_t π_{t+1} − λ(μ_t − μⁿ_t)`. -/
theorem printed_priceSetting_breaks_nkpc {β θ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) :
    ∃ p pstar μn ψ : ℕ → Unit → ℝ,
      (∀ t, pstar t = printedResetPrice perfectForesight β θ μn ψ t) ∧
      (∀ t, p (t + 1) = θ • p t + (1 - θ) • pstar (t + 1)) ∧
      ¬ ∀ t, p (t + 1) - p t = β • perfectForesight.E (t + 1) (p (t + 2) - p (t + 1)) -
        lambdaCalvo β θ • ((p (t + 1) - ψ (t + 1)) - μn (t + 1)) := by
  have hbt0 : 0 < β * θ := mul_pos hβ0 hθ0
  have hbt1 : β * θ < 1 := by nlinarith
  refine ⟨fun _ _ => 1, fun _ _ => 1, fun _ _ => 0, fun _ _ => 1 / (β * θ), fun t => ?_,
    fun t => ?_, fun h => ?_⟩
  · rw [printedResetPrice_const perfectForesight hbt0.le hbt1 (c := 1 / (β * θ))
      (fun t => by funext ω; simp)]
    funext ω
    field_simp
  · funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · have h0 := congrFun (h 0) ()
    simp only [perfectForesight, LinearMap.id_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      sub_self, Pi.zero_apply, mul_zero, zero_sub, sub_zero] at h0
    have hl := lambdaCalvo_pos hθ0 hθ1 hβ1
    have hne : 1 - 1 / (β * θ) ≠ 0 := by
      rw [sub_ne_zero, ne_comm, ne_eq, div_eq_one_iff_eq hbt0.ne']
      exact fun h => hbt1.ne h.symm
    have : lambdaCalvo β θ * (1 - 1 / (β * θ)) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hl.ne' h1
    · exact hne h1

/-! ### Wage markups (C5-6) -/

/-- Galí (2015), App. 5.2, p. 157, first two lines (correct as printed): with `α = 0` the price
markup is `μ_t = p_t − (w_t − a_t)`; with the wage markup `μ_{w,t} = (w_t − p_t) − mrs_t`,
`mrs_t = σ y_t + φ n_t` and `n_t = y_t − a_t`,
`μ_t = −μ_{w,t} − mrs_t + a_t = −μ_{w,t} − (σ + φ) y_t + (1 + φ) a_t`. -/
theorem priceMarkup_eq {σ φ μ μw p w a mrs y n : ℝ} (hμ : μ = p - (w - a))
    (hμw : μw = (w - p) - mrs) (hmrs : mrs = σ * y + φ * n) (hn : n = y - a) :
    μ = -μw - mrs + a ∧ μ = -μw - (σ + φ) * y + (1 + φ) * a := by
  subst hμ hμw hmrs hn
  constructor <;> ring

/-- Galí (2015), App. 5.2, p. 157, third line (**C5-6**): given the definitions, the printed
line `μ_t = μ_{w,t} − (σ + φ) y_t + (1 + φ) a_t` holds iff `μ_{w,t} = 0`. It is false whenever
the wage markup is nonzero; the correct sign is `−μ_{w,t}`. -/
theorem printed_markup_line_iff {σ φ μ μw p w a mrs y n : ℝ} (hμ : μ = p - (w - a))
    (hμw : μw = (w - p) - mrs) (hmrs : mrs = σ * y + φ * n) (hn : n = y - a) :
    μ = μw - (σ + φ) * y + (1 + φ) * a ↔ μw = 0 := by
  have h := (priceMarkup_eq hμ hμw hmrs hn).2
  constructor
  · intro h'
    linarith
  · intro h'
    rw [h, h']
    ring

/-- Galí (2015), App. 5.2, p. 157 (**C5-6, corrected markup gap**): with the subsidy-corrected
steady state `μ = −μ_w − (σ + φ) y^e_t + (1 + φ) a_t` (corrected sign), the markup gap is
`μ_t − μ = −(σ + φ)(y_t − y^e_t) − (μ_{w,t} − μ_w)`. -/
theorem markupGap_wage {σ φ μ μbar μw μwbar p w a mrs y n ye : ℝ} (hμ : μ = p - (w - a))
    (hμw : μw = (w - p) - mrs) (hmrs : mrs = σ * y + φ * n) (hn : n = y - a)
    (hss : μbar = -μwbar - (σ + φ) * ye + (1 + φ) * a) :
    μ - μbar = -(σ + φ) * (y - ye) - (μw - μwbar) := by
  rw [(priceMarkup_eq hμ hμw hmrs hn).2, hss]
  ring

/-- Galí (2015), App. 5.2, p. 157 (**C5-6, wage-markup shocks as cost-push shocks,
corrected**): if `π_t = β E_t π_{t+1} − λ(μ_t − μ)` (chapter 3) with the price markup of
`priceMarkup_eq` and the steady state of `markupGap_wage` at every date, then
`π_t = β E_t π_{t+1} + κ(y_t − y^e_t) + u_t` with `κ = λ(σ + φ)` and
`u_t = +λ(μ_{w,t} − μ_w)`. -/
theorem nkpc_wageMarkup {β lam σ φ μbar μwbar : ℝ}
    {infl μ μw p w a mrs y n ye : ℕ → Ω → ℝ}
    (hpc : ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) - lam • (μ t - fun _ => μbar))
    (hμ : ∀ t ω, μ t ω = p t ω - (w t ω - a t ω))
    (hμw : ∀ t ω, μw t ω = (w t ω - p t ω) - mrs t ω)
    (hmrs : ∀ t ω, mrs t ω = σ * y t ω + φ * n t ω) (hn : ∀ t ω, n t ω = y t ω - a t ω)
    (hss : ∀ t ω, μbar = -μwbar - (σ + φ) * ye t ω + (1 + φ) * a t ω) (t : ℕ) :
    infl t = β • 𝔼.E t (infl (t + 1)) + (lam * (σ + φ)) • (y t - ye t) +
      lam • (μw t - fun _ => μwbar) := by
  rw [hpc t]
  funext ω
  have hg := markupGap_wage (hμ t ω) (hμw t ω) (hmrs t ω) (hn t ω) (hss t ω)
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-lam) * hg

/-- Galí (2015), App. 5.2, p. 157 (**C5-6: the printed sign contradicts the derivation**): if
inflation satisfied both the derived equation (`u_t = +λ(μ_{w,t} − μ_w)`) and the printed one
(`u_t = −λ(μ_{w,t} − μ_w)`) at some date and state, then `λ(μ_{w,t} − μ_w) = 0`. So for
`λ ≠ 0` the printed cost-push term is wrong whenever the wage markup is away from its steady
state. -/
theorem printed_wage_costPush_contradiction {β lam σ φ μwbar : ℝ}
    {infl μw y ye : ℕ → Ω → ℝ} (t : ℕ) (ω : Ω)
    (hder : infl t = β • 𝔼.E t (infl (t + 1)) + (lam * (σ + φ)) • (y t - ye t) +
      lam • (μw t - fun _ => μwbar))
    (hprint : infl t = β • 𝔼.E t (infl (t + 1)) + (lam * (σ + φ)) • (y t - ye t) -
      lam • (μw t - fun _ => μwbar)) (hlam : lam ≠ 0) :
    μw t ω = μwbar := by
  have h1 := congrFun hder ω
  have h2 := congrFun hprint ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  have : lam * (μw t ω - μwbar) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hlam
  · linarith

/-- Galí (2015), App. 5.2, p. 157 (C5-6): with the corrected sign a wage-markup increase is a
genuine cost-push shock: `u_t = λ(μ_{w,t} − μ_w) > 0` when `μ_{w,t} > μ_w` and `λ > 0`, whereas
the printed sign would make it disinflationary. -/
theorem wageMarkup_costPush_pos {lam μw μwbar : ℝ} (hlam : 0 < lam) (h : μwbar < μw) :
    0 < lam * (μw - μwbar) ∧ -(lam * (μw - μwbar)) < 0 := by
  have := mul_pos hlam (sub_pos.mpr h)
  exact ⟨this, by linarith⟩

end Gali.DiscretionCommitment.CostPushSources
