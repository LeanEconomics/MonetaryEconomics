/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.MarginalCost

/-!
# The New Keynesian Phillips curve

Galí (2015), Chapter 3, §3.3 (pp. 60–63), including footnote 4.

## Main results

* `eq17`: combining (8) and (16) gives `π_t = β E_t π_{t+1} − λ μ̂_t` with
  `λ = (1 − θ)(1 − βθ)Θ/θ`.
* `lam_strictAntiOn_theta`, `lam_strictAntiOn_alpha`, `lam_strictAntiOn_eps`:
  `λ` is strictly decreasing in `θ`, in `α`, and in `ε` when `α > 0`;
  `lam_const_eps`, `not_lam_strictAntiOn_eps`: at `α = 0`, `λ` does not depend on
  `ε`, so the book's claim (p. 61) fails there (correction C3-2).
* `nkpc_forward`, `nkpc_forward_unique`: `π_t = −λ ∑ₖ βᵏ E_t μ̂_{t+k}` is the unique
  bounded solution of (17).
* `fn4`: the real-marginal-cost form `π_t = β E_t π_{t+1} + λ m̂c_t`.
* `eq18`, `eq19_iff_eq20`, `eq21`: the markup–output relation, natural output
  `y^n_t = ψ_ya a_t + ψ_y` and the markup gap–output gap relation.
* `psi_y_neg`, `not_psi_y_pos`: `ψ_y < 0` (the book prints `> 0`, correction C3-1).
* `psi_y_perfect_competition`, `natural_output_lower`: `μ = 0` gives the classical
  output of chapter 2; market power lowers the level of output, not its slope.
* `eq22`: the NKPC `π_t = β E_t π_{t+1} + κ ỹ_t`, `κ = λ(σ + (φ + α)/(1 − α))`.
-/

namespace Gali.BasicNewKeynesianModel.NKPC

open MarginalCost

/-- `λ = (1 − θ)(1 − βθ)Θ/θ` (Galí (2015), p. 61). -/
noncomputable def lam (θ β α ε : ℝ) : ℝ := (1 - θ) * (1 - β * θ) * Theta α ε / θ

/-- `λ > 0` for `θ ∈ (0, 1)` and `β < 1` (Galí (2015), p. 61). -/
theorem lam_pos {θ β α ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ1 : β < 1)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 < ε) : 0 < lam θ β α ε := by
  unfold lam
  have : 0 < 1 - β * θ := by nlinarith
  have := Theta_pos hα0 hα1 hε
  positivity

/-! ### The inflation equation (17) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- **Equation (17)** (Galí (2015), p. 60), derived from (8) and (16). With
inflation `π_t = p_t − p_{t−1}`, the price-index relation (8)
`π_t = (1 − θ)(p*_t − p_{t−1})` and the reset-price recursion (16)
`p*_t = βθ E_t p*_{t+1} + (1 − βθ)(p_t − Θ μ̂_t)`, inflation satisfies
`π_t = β E_t π_{t+1} − λ μ̂_t` at every date `t ≥ 1`. -/
theorem eq17 {θ β α ε μ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {p pstar π ψ : ℕ → Ω → ℝ}
    (hpa : 𝔼.Adapted p) (hπ : ∀ t, π (t + 1) = p (t + 1) - p t)
    (h8 : ∀ t, π (t + 1) = (1 - θ) • (pstar (t + 1) - p t))
    (h16 : ∀ t, pstar t = (β * θ) • 𝔼.E t (pstar (t + 1))
      + (1 - β * θ) • (p t - Theta α ε • markupGap μ p ψ t)) (t : ℕ) :
    π (t + 1) = β • 𝔼.E (t + 1) (π (t + 2)) - lam θ β α ε • markupGap μ p ψ (t + 1) := by
  have h1θ : 1 - θ ≠ 0 := by linarith
  have hnext : pstar (t + 2) = p (t + 1) + (1 - θ)⁻¹ • π (t + 2) := by
    rw [h8 (t + 1), smul_smul, inv_mul_cancel₀ h1θ, one_smul]
    abel
  have hE : 𝔼.E (t + 1) (pstar (t + 2))
      = p (t + 1) + (1 - θ)⁻¹ • 𝔼.E (t + 1) (π (t + 2)) := by
    rw [hnext, map_add, map_smul, hpa (t + 1)]
  have h16' := h16 (t + 1)
  rw [hE] at h16'
  funext ω
  have e8 := congrFun (h8 t) ω
  have eπ := congrFun (hπ t) ω
  have e16 := congrFun h16' ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e8 eπ e16 ⊢
  unfold lam
  set G := markupGap μ p ψ (t + 1) ω
  set Epi := 𝔼.E (t + 1) (π (t + 2)) ω
  set Θ := Theta α ε
  -- `p*_{t+1} − p_{t+1} = θ/(1 − θ) π_{t+1}` and (16) give the result
  have hgap : pstar (t + 1) ω - p (t + 1) ω = θ * (1 - θ)⁻¹ * π (t + 1) ω := by
    field_simp
    linear_combination -e8 + (1 - θ) * eπ
  have hgap2 : pstar (t + 1) ω - p (t + 1) ω
      = β * θ * (1 - θ)⁻¹ * Epi - (1 - β * θ) * Θ * G := by
    rw [e16]; ring
  have hθ : θ ≠ 0 := hθ0.ne'
  have key : θ * (1 - θ)⁻¹ * π (t + 1) ω = β * θ * (1 - θ)⁻¹ * Epi - (1 - β * θ) * Θ * G := by
    rw [← hgap, hgap2]
  field_simp at key ⊢
  linear_combination key

/-! ### Comparative statics of `λ` -/

/-- **`λ` is strictly decreasing in the degree of price stickiness `θ`**
(Galí (2015), p. 61). -/
theorem lam_strictAntiOn_theta {β α ε : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hε : 0 < ε) :
    StrictAntiOn (fun θ => lam θ β α ε) (Set.Ioo 0 1) := by
  intro θ₁ h₁ θ₂ h₂ h12
  have hΘ := Theta_pos hα0 hα1 hε
  simp only [lam]
  rw [div_lt_div_iff₀ h₂.1 h₁.1]
  have hb : 0 ≤ β * (θ₂ - θ₁) := mul_nonneg hβ0 (by linarith)
  have hp1 : 0 < 1 - β * θ₂ := by nlinarith [h₂.2]
  have key : (1 - θ₂) * (1 - β * θ₂) * θ₁ < (1 - θ₁) * (1 - β * θ₁) * θ₂ := by
    have e1 : (1 - θ₂) * θ₁ < (1 - θ₁) * θ₂ := by nlinarith
    have e2 : 1 - β * θ₂ ≤ 1 - β * θ₁ := by nlinarith
    calc (1 - θ₂) * (1 - β * θ₂) * θ₁ = ((1 - θ₂) * θ₁) * (1 - β * θ₂) := by ring
      _ < ((1 - θ₁) * θ₂) * (1 - β * θ₂) := mul_lt_mul_of_pos_right e1 hp1
      _ ≤ ((1 - θ₁) * θ₂) * (1 - β * θ₁) :=
          mul_le_mul_of_nonneg_left e2 (mul_pos (by linarith [h₁.2]) h₂.1).le
      _ = (1 - θ₁) * (1 - β * θ₁) * θ₂ := by ring
  calc (1 - θ₂) * (1 - β * θ₂) * Theta α ε * θ₁
      = (1 - θ₂) * (1 - β * θ₂) * θ₁ * Theta α ε := by ring
    _ < (1 - θ₁) * (1 - β * θ₁) * θ₂ * Theta α ε := mul_lt_mul_of_pos_right key hΘ
    _ = (1 - θ₁) * (1 - β * θ₁) * Theta α ε * θ₂ := by ring

/-- `Θ` is strictly decreasing in `α` on `[0, 1)` when `ε > 0` (Galí (2015), p. 61). -/
theorem Theta_strictAntiOn_alpha {ε : ℝ} (hε : 0 < ε) :
    StrictAntiOn (fun α => Theta α ε) (Set.Ico 0 1) := by
  intro α₁ h₁ α₂ h₂ h12
  simp only [Theta]
  rw [div_lt_div_iff₀ (by nlinarith [h₂.1, h₂.2]) (by nlinarith [h₁.1, h₁.2])]
  nlinarith [mul_lt_mul_of_pos_right h12 hε]

/-- **`λ` is strictly decreasing in the measure of decreasing returns `α`**
(Galí (2015), p. 61). -/
theorem lam_strictAntiOn_alpha {θ β ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ1 : β < 1)
    (hε : 0 < ε) :
    StrictAntiOn (fun α => lam θ β α ε) (Set.Ico 0 1) := by
  intro α₁ h₁ α₂ h₂ h12
  have hc : 0 < (1 - θ) * (1 - β * θ) / θ := by
    have : 0 < 1 - β * θ := by nlinarith
    have : 0 < 1 - θ := by linarith
    positivity
  have := Theta_strictAntiOn_alpha hε h₁ h₂ h12
  simp only [lam, mul_div_right_comm _ (Theta _ _)] at this ⊢
  exact mul_lt_mul_of_pos_left this hc

/-- **`λ` is strictly decreasing in the demand elasticity `ε` when `α > 0`**
(Galí (2015), p. 61, corrected: see `not_lam_strictAntiOn_eps`). -/
theorem lam_strictAntiOn_eps {θ β α : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ1 : β < 1)
    (hα0 : 0 < α) (hα1 : α < 1) :
    StrictAntiOn (fun ε => lam θ β α ε) (Set.Ioi 0) := by
  intro ε₁ h₁ ε₂ h₂ h12
  have hc : 0 < (1 - θ) * (1 - β * θ) / θ := by
    have : 0 < 1 - β * θ := by nlinarith
    have : 0 < 1 - θ := by linarith
    positivity
  have hΘ : Theta α ε₂ < Theta α ε₁ := by
    simp only [Theta]
    have h1 : 0 < 1 - α + α * ε₁ := by nlinarith [Set.mem_Ioi.mp h₁]
    exact div_lt_div_of_pos_left (by linarith) h1 (by nlinarith)
  simp only [lam, mul_div_right_comm _ (Theta _ _)]
  exact mul_lt_mul_of_pos_left hΘ hc

/-- Under constant returns (`α = 0`), `λ` does not depend on `ε` (Galí (2015),
p. 61: `Θ = 1` when `α = 0`). -/
theorem lam_const_eps (θ β ε₁ ε₂ : ℝ) : lam θ β 0 ε₁ = lam θ β 0 ε₂ := by
  simp [lam, Theta]

/-- **Correction C3-2** (Galí (2015), p. 61): the claim that `λ` is strictly
decreasing in `ε` is false at `α = 0`, where `λ` is constant in `ε`. -/
theorem not_lam_strictAntiOn_eps (θ β : ℝ) :
    ¬ StrictAntiOn (fun ε => lam θ β 0 ε) (Set.Ioi 1) := by
  intro h
  have := h (show (2 : ℝ) ∈ Set.Ioi 1 by norm_num) (show (3 : ℝ) ∈ Set.Ioi 1 by norm_num)
    (by norm_num)
  simp only [lam_const_eps θ β 3 2, lt_self_iff_false] at this

/-! ### Forward solution of (17) -/

/-- **Forward solution of (17)** (Galí (2015), p. 61): for a bounded adapted
markup gap, `π_t = −λ ∑ₖ βᵏ E_t μ̂_{t+k}` satisfies `π_t = β E_t π_{t+1} − λ μ̂_t`
and is bounded. -/
theorem nkpc_forward {β lamv : ℝ} (hβ : |β| < 1) {μhat : ℕ → Ω → ℝ} {M : ℝ}
    (hμ : ∀ t ω, |μhat t ω| ≤ M) (hμa : 𝔼.Adapted μhat) :
    (∀ t, (-lamv) • ResetPrice.forwardSum 𝔼 β μhat t
        = β • 𝔼.E t ((-lamv) • ResetPrice.forwardSum 𝔼 β μhat (t + 1)) - lamv • μhat t) ∧
      BoundedProc fun t => (-lamv) • ResetPrice.forwardSum 𝔼 β μhat t := by
  refine ⟨fun t => ?_, ?_⟩
  · rw [ResetPrice.forwardSum_rec 𝔼 hβ hμ hμa t, 𝔼.E_smul, smul_add, smul_smul, smul_smul,
      mul_comm β (-lamv)]
    simp only [neg_smul]
    abel
  · obtain ⟨B, hB⟩ := ResetPrice.forwardSum_bounded 𝔼 hβ ⟨M, hμ⟩
    refine ⟨|lamv| * B, fun t ω => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hB t ω) (abs_nonneg _)

/-- **Uniqueness of the forward solution** (Galí (2015), p. 61): every bounded
solution of (17) equals `−λ ∑ₖ βᵏ E_t μ̂_{t+k}`. -/
theorem nkpc_forward_unique {β lamv : ℝ} (hβ : |β| < 1) {μhat : ℕ → Ω → ℝ} {M : ℝ}
    (hμ : ∀ t ω, |μhat t ω| ≤ M) (hμa : 𝔼.Adapted μhat) {π : ℕ → Ω → ℝ}
    (hπ : BoundedProc π) (h17 : ∀ t, π t = β • 𝔼.E t (π (t + 1)) - lamv • μhat t) :
    π = fun t => (-lamv) • ResetPrice.forwardSum 𝔼 β μhat t := by
  obtain ⟨hsol, hb⟩ := nkpc_forward 𝔼 (lamv := lamv) hβ hμ hμa
  refine 𝔼.forward_unique hβ (u := fun t => -(lamv • μhat t)) (fun t => ?_) (fun t => ?_) hπ hb
  · rw [h17 t, sub_eq_add_neg]
  · rw [hsol t, sub_eq_add_neg]

/-- Inflation is nonnegative when markups are expected to be at or below their
desired level at every horizon (Galí (2015), p. 61). -/
theorem inflation_nonneg_of_markups_below {β lamv : ℝ} (hβ0 : 0 ≤ β)
    (hlam : 0 ≤ lamv) {μhat : ℕ → Ω → ℝ} (t : ℕ) (ω : Ω) (hneg : ∀ k, 𝔼.E t (μhat (t + k)) ω ≤ 0) :
    0 ≤ ((-lamv) • ResetPrice.forwardSum 𝔼 β μhat t) ω := by
  simp only [Pi.smul_apply, smul_eq_mul, ResetPrice.forwardSum]
  have hs : ∑' k, β ^ k * 𝔼.E t (μhat (t + k)) ω ≤ 0 :=
    tsum_nonpos fun k => mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ0 k) (hneg k)
  nlinarith

/-- **Footnote 4** (Galí (2015), p. 61): with real marginal cost `mc_t = ψ_t − p_t =
−μ_t` and its deviation `m̂c_t = mc_t + μ = −μ̂_t`, (17) reads
`π_t = β E_t π_{t+1} + λ m̂c_t`. -/
theorem fn4 {β lamv μ : ℝ} {p ψ π : ℕ → Ω → ℝ} (t : ℕ)
    (h17 : π t = β • 𝔼.E t (π (t + 1)) - lamv • markupGap μ p ψ t) :
    π t = β • 𝔼.E t (π (t + 1)) + lamv • ((ψ t - p t) - fun _ => -μ) := by
  rw [h17, sub_eq_add_neg, ← smul_neg]
  congr 2
  funext ω
  simp [markupGap]
  ring

/-! ### Markups and output: (18)–(21) -/

/-- **Equation (18)** (Galí (2015), p. 62): with `μ_t = p_t − ψ_t`, average marginal
cost `ψ_t = w_t − (a_t − α n_t + log(1 − α))`, labour supply (2)
`w_t − p_t = σ y_t + φ n_t` (using `c_t = y_t`) and (14) `(1 − α) n_t = y_t − a_t`,
`μ_t = −(σ + (φ + α)/(1 − α)) y_t + ((1 + φ)/(1 − α)) a_t + log(1 − α)`. -/
theorem eq18 {σ φ α w p n y a ψ μt : ℝ} (hα : α < 1) (hμ : μt = p - ψ)
    (hψ : ψ = w - (a - α * n + Real.log (1 - α))) (h2 : w - p = σ * y + φ * n)
    (h14 : (1 - α) * n = y - a) :
    μt = -(σ + (φ + α) / (1 - α)) * y + (1 + φ) / (1 - α) * a + Real.log (1 - α) := by
  have h1 : 1 - α ≠ 0 := by linarith
  have hn : n = (y - a) / (1 - α) := by field_simp; linarith
  rw [hμ, hψ, hn]
  have hw : w = p + σ * y + φ * ((y - a) / (1 - α)) := by rw [← hn]; linarith
  rw [hw]
  field_simp
  ring

/-- `ψ_ya = (1 + φ)/(σ(1 − α) + φ + α)` (Galí (2015), p. 62). -/
noncomputable def psiYA (σ φ α : ℝ) : ℝ := (1 + φ) / (σ * (1 - α) + φ + α)

/-- `ψ_y = −(1 − α)(μ − log(1 − α))/(σ(1 − α) + φ + α)` (Galí (2015), p. 62). -/
noncomputable def psiY (σ φ α μ : ℝ) : ℝ :=
  -((1 - α) * (μ - Real.log (1 - α))) / (σ * (1 - α) + φ + α)

/-- The denominator `σ(1 − α) + φ + α` is positive (Galí (2015), p. 62). -/
theorem denom_pos {σ φ α : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < σ * (1 - α) + φ + α := by
  have : 0 < σ * (1 - α) := mul_pos hσ (by linarith)
  linarith

/-- **Natural output, (19) ⟺ (20)** (Galí (2015), p. 62): evaluating (18) at the
flexible-price equilibrium, where the average markup equals the desired `μ`,
`μ = −(σ + (φ + α)/(1 − α)) y^n_t + ((1 + φ)/(1 − α)) a_t + log(1 − α)` holds if and
only if `y^n_t = ψ_ya a_t + ψ_y`. -/
theorem eq19_iff_eq20 {σ φ α μ yn a : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) :
    μ = -(σ + (φ + α) / (1 - α)) * yn + (1 + φ) / (1 - α) * a + Real.log (1 - α) ↔
      yn = psiYA σ φ α * a + psiY σ φ α μ := by
  have h1 : 1 - α ≠ 0 := by linarith
  have hD := (denom_pos hσ hφ hα0 hα1).ne'
  unfold psiYA psiY
  constructor
  · intro h
    rw [h]
    field_simp
    ring
  · intro h
    rw [h]
    field_simp
    ring

/-- **Correction C3-1** (Galí (2015), p. 62): with a positive desired markup
`μ > 0` and `α ∈ [0, 1)`, `ψ_y < 0` (the book prints `ψ_y > 0`). -/
theorem psi_y_neg {σ φ α μ : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hμ : 0 < μ) : psiY σ φ α μ < 0 := by
  unfold psiY
  have hlog : Real.log (1 - α) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have : 0 < (1 - α) * (μ - Real.log (1 - α)) := mul_pos (by linarith) (by linarith)
  exact div_neg_of_neg_of_pos (by linarith) (denom_pos hσ hφ hα0 hα1)

/-- The book's sign claim `ψ_y > 0` (Galí (2015), p. 62) is false (C3-1). -/
theorem not_psi_y_pos {σ φ α μ : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hμ : 0 < μ) : ¬ 0 < psiY σ φ α μ :=
  fun h => lt_asymm h (psi_y_neg hσ hφ hα0 hα1 hμ)

/-- The log desired markup `μ = log(ε/(ε − 1))` is positive for `ε > 1`
(Galí (2015), p. 57). -/
theorem logMarkup_pos {ε : ℝ} (hε : 1 < ε) : 0 < ResetPrice.logMarkup ε :=
  Real.log_pos (ResetPrice.one_lt_markup hε)

/-- C3-1 at the book's markup: `ψ_y < 0` for `μ = log(ε/(ε − 1))`, `ε > 1`
(Galí (2015), p. 62). -/
theorem psi_y_neg_at_markup {σ φ α ε : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hε : 1 < ε) : psiY σ φ α (ResetPrice.logMarkup ε) < 0 :=
  psi_y_neg hσ hφ hα0 hα1 (logMarkup_pos hε)

/-- **Perfect competition gives the classical output** (Galí (2015), p. 62): at
`μ = 0`, `ψ_y = (1 − α) log(1 − α)/(σ(1 − α) + φ + α)`, the constant of the
classical equilibrium output of chapter 2. -/
theorem psi_y_perfect_competition (σ φ α : ℝ) :
    psiY σ φ α 0 = (1 - α) * Real.log (1 - α) / (σ * (1 - α) + φ + α) := by
  unfold psiY
  ring

/-- **Market power lowers the level of natural output, not its slope**
(Galí (2015), p. 62): `ψ_y` is strictly decreasing in `μ`, so for `μ > 0` natural
output is below its perfect-competition level at every technology level, while
the slope `ψ_ya` does not involve `μ`. -/
theorem natural_output_lower {σ φ α μ : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hμ : 0 < μ) (a : ℝ) :
    psiYA σ φ α * a + psiY σ φ α μ < psiYA σ φ α * a + psiY σ φ α 0 := by
  have hD := denom_pos hσ hφ hα0 hα1
  have : psiY σ φ α μ < psiY σ φ α 0 := by
    unfold psiY
    rw [div_lt_div_iff_of_pos_right hD]
    nlinarith
  linarith

/-- **Equation (21)** (Galí (2015), p. 62): subtracting (19) from (18),
`μ̂_t = −(σ + (φ + α)/(1 − α)) (y_t − y^n_t)`. -/
theorem eq21 {σ φ α μ μt y yn a : ℝ}
    (h18 : μt = -(σ + (φ + α) / (1 - α)) * y + (1 + φ) / (1 - α) * a + Real.log (1 - α))
    (h19 : μ = -(σ + (φ + α) / (1 - α)) * yn + (1 + φ) / (1 - α) * a + Real.log (1 - α)) :
    μt - μ = -(σ + (φ + α) / (1 - α)) * (y - yn) := by
  rw [h18, h19]; ring

/-! ### The New Keynesian Phillips curve (22) -/

/-- `κ = λ(σ + (φ + α)/(1 − α))` (Galí (2015), p. 63). -/
noncomputable def kappa (θ β α ε σ φ : ℝ) : ℝ := lam θ β α ε * (σ + (φ + α) / (1 - α))

/-- `κ > 0` (Galí (2015), p. 63). -/
theorem kappa_pos {θ β α ε σ φ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ1 : β < 1)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 < ε) (hσ : 0 < σ) (hφ : 0 ≤ φ) :
    0 < kappa θ β α ε σ φ := by
  unfold kappa
  have : 0 ≤ (φ + α) / (1 - α) := div_nonneg (by linarith) (by linarith)
  exact mul_pos (lam_pos hθ0 hθ1 hβ1 hα0 hα1 hε) (by linarith)

/-- **The New Keynesian Phillips curve (22)** (Galí (2015), p. 63): combining (17)
with (21), `π_t = β E_t π_{t+1} + κ ỹ_t`, where `ỹ_t = y_t − y^n_t`. -/
theorem eq22 {θ β α ε σ φ μ : ℝ} {p ψ π ygap : ℕ → Ω → ℝ} (t : ℕ)
    (h17 : π t = β • 𝔼.E t (π (t + 1)) - lam θ β α ε • markupGap μ p ψ t)
    (h21 : markupGap μ p ψ t = (-(σ + (φ + α) / (1 - α))) • ygap t) :
    π t = β • 𝔼.E t (π (t + 1)) + kappa θ β α ε σ φ • ygap t := by
  rw [h17, h21, smul_smul, kappa, sub_eq_add_neg, ← neg_smul]
  congr 2
  ring

/-- **The NKPC from primitives** (Galí (2015), pp. 60–63): (8), (16) and the
markup–output relations (18)–(19) at every date give
`π_t = β E_t π_{t+1} + κ ỹ_t` at every date `t ≥ 1`. -/
theorem eq22_of_primitives {θ β α ε σ φ μ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {p pstar π ψ y yn a : ℕ → Ω → ℝ} (hpa : 𝔼.Adapted p)
    (hπ : ∀ t, π (t + 1) = p (t + 1) - p t)
    (h8 : ∀ t, π (t + 1) = (1 - θ) • (pstar (t + 1) - p t))
    (h16 : ∀ t, pstar t = (β * θ) • 𝔼.E t (pstar (t + 1))
      + (1 - β * θ) • (p t - Theta α ε • markupGap μ p ψ t))
    (h18 : ∀ t ω, p t ω - ψ t ω = -(σ + (φ + α) / (1 - α)) * y t ω
      + (1 + φ) / (1 - α) * a t ω + Real.log (1 - α))
    (h19 : ∀ t ω, μ = -(σ + (φ + α) / (1 - α)) * yn t ω
      + (1 + φ) / (1 - α) * a t ω + Real.log (1 - α)) (t : ℕ) :
    π (t + 1) = β • 𝔼.E (t + 1) (π (t + 2))
      + kappa θ β α ε σ φ • (y (t + 1) - yn (t + 1)) := by
  have h17 := eq17 𝔼 hθ0 hθ1 hpa hπ h8 h16 t
  refine eq22 (σ := σ) (φ := φ) (ygap := fun s => y s - yn s) 𝔼 (t + 1) h17 ?_
  funext ω
  have := eq21 (h18 (t + 1) ω) (h19 (t + 1) ω)
  simp only [markupGap, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linarith

end Gali.BasicNewKeynesianModel.NKPC
