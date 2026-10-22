/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR5StochasticPathsMeasure

/-!
# Figure 17.6 on a genuine probability space: equilibria indexed by inflation innovations

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.4.1, eq. (17.18),
p. 408, Figure 17.6, p. 410 ("any of these jumps"), with eq. (5.5), p. 119.

The measure-theoretic version of `TidyR5StochasticPaths.innov_eqm_existsUnique`, on a
probability space with a filtration and Mathlib's conditional expectation:

* `eq1718_of_modelM`: every equilibrium of (17.15)–(17.17) (`TidyR5StochasticPathsMeasure.ModelM`)
  satisfies (17.18) almost everywhere.
* `factoredM_of_eq1718`, `eq1718_of_factoredM`: for essentially bounded processes, (17.18) holds
  a.e. iff the factored form `λ₁ E_t π_{t+1} = π_t + σκ F_t` does, with
  `F = ∑ λ₂ᵏ E_t i_{t+k}` the forward solution (`MeasExpectationSystem.forwardSol`); the `λ₂`
  factor is solved forward with `MeasExpectationSystem.forward_unique`.
* `piM`: inflation with initial value `p` and innovations `δ`,
  `π_{t+1} = λ₁^{−1}(π_t + σκF_t) + δ_{t+1}`. **`piM_equilibrium`** (existence): for every
  bounded adapted rate process, every bounded `p` known at date 0 and every bounded adapted
  innovation process `δ` with `E_t δ_{t+1} = 0` a.s., `piM` is adapted, essentially bounded, has
  innovations `δ`, and with `r = i − E π'` and `x = (π − β E π')/κ` is an equilibrium.
  **`eq_piM`** (uniqueness): every essentially bounded equilibrium with `π_0 = p` a.s. and
  innovations `δ` a.s. equals `piM` almost surely at every date.
-/

namespace Cochrane.KeynesianStickyPrices.TidyR5InnovEqmMeasure

open MeasureTheory Filter Topology FullModel TidyR5ExpectationsMeasure
open TidyR5StochasticPathsMeasure

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), eqs. (17.15)–(17.18), p. 408, on a probability space: every equilibrium
satisfies `σκ i_t = −β E_t π_{t+2} + (1 + β + σκ) E_t π_{t+1} − π_t` almost everywhere. -/
theorem eq1718_of_modelM {σ β κ : ℝ} {i r x π : ℕ → Ω → ℝ} (h : ModelM S σ β κ i r x π)
    (t : ℕ) :
    (σ * κ) • i t =ᵐ[S.μ]
      -β • S.E t (π (t + 2)) + (1 + β + σ * κ) • S.E t (π (t + 1)) - π t := by
  obtain ⟨hint, heq⟩ := h
  obtain ⟨h1, h2, h3⟩ := heq t
  obtain ⟨-, -, h3'⟩ := heq (t + 1)
  obtain ⟨-, -, ix', -⟩ := hint (t + 1)
  have iE := S.integrable_E (t + 1) (π (t + 1 + 1))
  filter_upwards [h1, h2, h3, S.E_congr h3' t, S.E_add (iE.smul β) (ix'.smul κ) t,
    S.E_smul β (S.E (t + 1) (π (t + 1 + 1))) t, S.E_smul κ (x (t + 1)) t,
    S.E_tower (Nat.le_succ t) (π (t + 1 + 1))] with ω a b c d e f g k
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b c d e f g ⊢
  have e2 : t + 2 = t + 1 + 1 := rfl
  rw [e2]
  linear_combination (σ * κ) * b + κ * a + c - (d + e + f + g + β * k)

/-- Cochrane (2023), eq. (5.5), p. 119, on a probability space: the factored form
`λ₁ E_t π_{t+1} = π_t + σκ F_t` a.e., `F` the forward solution for `λ₂` and the rates. -/
def FactoredM (σ β κ : ℝ) (i π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, lam1 σ β κ • S.E t (π (t + 1)) =ᵐ[S.μ]
    π t + (σ * κ) • S.forwardSol (lam2 σ β κ) i t

/-- Cochrane (2023), A1 §1.7, p. 570, on a probability space: the factorisation identity,
`G_t − λ₂ E_t G_{t+1} = π_t − (1 + β + σκ) E_t π_{t+1} + β E_t π_{t+2}` a.e. for
`G_t = π_t − λ₁ E_t π_{t+1}`. -/
theorem factor_identity_ae {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {π : ℕ → Ω → ℝ}
    (hπi : ∀ t, Integrable (π t) S.μ) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, (π t ω - lam1 σ β κ * S.E t (π (t + 1)) ω) -
        lam2 σ β κ * S.E t (π (t + 1) - lam1 σ β κ • S.E (t + 1) (π (t + 1 + 1))) ω =
      π t ω - (1 + β + σ * κ) * S.E t (π (t + 1)) ω + β * S.E t (π (t + 2)) ω := by
  have hs := lam_sum σ β κ
  have hp := lam_prod ha hβ
  filter_upwards [S.E_sub (hπi (t + 1)) ((S.integrable_E (t + 1) _).smul (lam1 σ β κ)) t,
    S.E_smul (lam1 σ β κ) (S.E (t + 1) (π (t + 1 + 1))) t,
    S.E_tower (Nat.le_succ t) (π (t + 1 + 1))] with ω a b c
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b
  rw [a, b, c, show t + 2 = t + 1 + 1 from rfl]
  linear_combination -(S.E t (π (t + 1)) ω) * hs + (S.E t (π (t + 1 + 1)) ω) * hp

/-- Cochrane (2023), eq. (5.5) and A1 §1.7, on a probability space: for essentially bounded
adapted rates and essentially bounded integrable inflation, (17.18) a.e. implies the factored
form a.e. -/
theorem factoredM_of_eq1718 {σ β κ M Mπ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i π : ℕ → Ω → ℝ}
    (hia : StronglyAdapted S.𝓕 i) (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ M)
    (hπi : ∀ t, Integrable (π t) S.μ) (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ)
    (h : ∀ t, (σ * κ) • i t =ᵐ[S.μ]
      -β • S.E t (π (t + 2)) + (1 + β + σ * κ) • S.E t (π (t + 1)) - π t) :
    FactoredM S σ β κ i π := by
  have h20 := (lam2_pos ha hβ).le
  have h21 := lam2_lt_one ha hβ
  have hl2 : |lam2 σ β κ| < 1 := by rw [abs_of_nonneg h20]; exact h21
  have hFs := S.forwardSol_solves hl2 hia hi
  set F := S.forwardSol (lam2 σ β κ) i with hF
  set G : ℕ → Ω → ℝ := fun t => π t - lam1 σ β κ • S.E t (π (t + 1)) with hG
  set H : ℕ → Ω → ℝ := fun t => (-(σ * κ)) • F t with hH
  have hiI : ∀ t, Integrable (i t) S.μ := fun t =>
    MeasExpectationSystem.BddRV.integrable
      ⟨((hia t).mono (S.𝓕.le t)).aestronglyMeasurable, M, hi t⟩
  have hGs : S.Solves (lam2 σ β κ) (fun t => (-(σ * κ)) • i t) G := by
    intro t
    filter_upwards [factor_identity_ae S ha hβ hπi t, h t] with ω a b
    simp only [hG, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, neg_mul] at a b ⊢
    linear_combination a + b
  have hHs : S.Solves (lam2 σ β κ) (fun t => (-(σ * κ)) • i t) H := by
    intro t
    filter_upwards [hFs t, S.E_smul (-(σ * κ)) (F (t + 1)) t] with ω a b
    simp only [hH, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at a b ⊢
    rw [b, a]
    ring
  have hGm : ∀ t, AEStronglyMeasurable (G t) S.μ := fun t =>
    (hπi t).aestronglyMeasurable.sub ((S.integrable_E t _).aestronglyMeasurable.const_smul _)
  have hHm : ∀ t, AEStronglyMeasurable (H t) S.μ := fun t =>
    (S.integrable_E t _).aestronglyMeasurable.const_smul _
  have hGb : S.BddProc G := ⟨Mπ + |lam1 σ β κ| * Mπ, fun t => by
    filter_upwards [hπ t, S.abs_E_le (hπ (t + 1)) t] with ω a b
    simp only [hG, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add a ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left b (abs_nonneg _)⟩
  have hHb : S.BddProc H := by
    obtain ⟨K, hK⟩ := S.forwardSol_bdd hl2 hi
    exact ⟨|σ * κ| * K, fun t => by
      filter_upwards [hK t] with ω a
      simp only [hH, Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left a (by positivity)⟩
  have heq := S.forward_unique hl2 hGs hHs hGm hHm hGb hHb
  intro t
  filter_upwards [heq t] with ω a
  simp only [hG, hH, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a ⊢
  linear_combination -a

/-- Cochrane (2023), eq. (5.5) and A1 §1.7, on a probability space: the factored form a.e.
implies (17.18) a.e. (adapted essentially bounded rates). -/
theorem eq1718_of_factoredM {σ β κ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i π : ℕ → Ω → ℝ}
    (hia : StronglyAdapted S.𝓕 i) (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ M)
    (hπi : ∀ t, Integrable (π t) S.μ) (h : FactoredM S σ β κ i π) (t : ℕ) :
    (σ * κ) • i t =ᵐ[S.μ]
      -β • S.E t (π (t + 2)) + (1 + β + σ * κ) • S.E t (π (t + 1)) - π t := by
  have h20 := (lam2_pos ha hβ).le
  have h21 := lam2_lt_one ha hβ
  have hl2 : |lam2 σ β κ| < 1 := by rw [abs_of_nonneg h20]; exact h21
  have hFs := S.forwardSol_solves hl2 hia hi
  have h1' : S.E t (π (t + 1) - lam1 σ β κ • S.E (t + 1) (π (t + 1 + 1))) =ᵐ[S.μ]
      S.E t ((-(σ * κ)) • S.forwardSol (lam2 σ β κ) i (t + 1)) := by
    refine S.E_congr ?_ t
    filter_upwards [h (t + 1)] with ω a
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a ⊢
    linarith
  filter_upwards [factor_identity_ae S ha hβ hπi t, h t, hFs t, h1',
    S.E_smul (-(σ * κ)) (S.forwardSol (lam2 σ β κ) i (t + 1)) t]
    with ω a b c d e
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    neg_mul] at a b c d e ⊢
  rw [d, e] at a
  linear_combination -a - b - (σ * κ) * c

/-! ### The equilibrium with given innovations -/

/-- Cochrane (2023), Fig. 17.6, p. 410, on a probability space: inflation with initial value `p`
and innovations `δ`, `π_{t+1} = λ₁^{−1}(π_t + σκF_t) + δ_{t+1}`. -/
noncomputable def piM (σ β κ : ℝ) (i : ℕ → Ω → ℝ) (p : Ω → ℝ) (δ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => p
  | t + 1 => (lam1 σ β κ)⁻¹ • (piM σ β κ i p δ t +
      (σ * κ) • S.forwardSol (lam2 σ β κ) i t) + δ (t + 1)

/-- Cochrane (2023), Fig. 17.6: `piM` is adapted. -/
theorem piM_adapted {σ β κ : ℝ} {i : ℕ → Ω → ℝ} {p : Ω → ℝ} {δ : ℕ → Ω → ℝ}
    (hp0 : StronglyMeasurable[S.𝓕 0] p) (hδa : StronglyAdapted S.𝓕 δ) :
    StronglyAdapted S.𝓕 (piM S σ β κ i p δ) := by
  intro t
  induction t with
  | zero => exact hp0
  | succ t ih =>
    have h1 := ih.mono (S.𝓕.mono (Nat.le_succ t))
    have h2 := (S.forwardSol_adapted (lam2 σ β κ) i t).mono (S.𝓕.mono (Nat.le_succ t))
    exact ((h1.add (h2.const_smul (σ * κ))).const_smul _).add (hδa (t + 1))

/-- Cochrane (2023), Fig. 17.6: `piM` is essentially bounded for essentially bounded `i`, `p`,
`δ`. -/
theorem piM_bdd {σ β κ M Mp Mδ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i : ℕ → Ω → ℝ}
    (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ M) {p : Ω → ℝ} (hp : ∀ᵐ ω ∂S.μ, |p ω| ≤ Mp)
    {δ : ℕ → Ω → ℝ} (hδ : ∀ t, ∀ᵐ ω ∂S.μ, |δ t ω| ≤ Mδ) :
    ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |piM S σ β κ i p δ t ω| ≤ K := by
  have h20 := (lam2_pos ha hβ).le
  have h21 := lam2_lt_one ha hβ
  have hl2 : |lam2 σ β κ| < 1 := by rw [abs_of_nonneg h20]; exact h21
  have hl1 := one_lt_lam1 ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans hl1
  have hc0 : 0 ≤ (lam1 σ β κ)⁻¹ := inv_nonneg.mpr hl0.le
  have hc1 : (lam1 σ β κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  obtain ⟨K0, hK0⟩ := S.forwardSol_bdd hl2 hi
  set Fc := (lam1 σ β κ)⁻¹ * (σ * κ * max K0 0) + max Mδ 0
  have hFc : 0 ≤ Fc := by positivity
  refine ⟨max Mp 0 + Fc / (1 - (lam1 σ β κ)⁻¹), ae_all_iff.mp ?_⟩
  filter_upwards [hp, ae_all_iff.mpr hK0, ae_all_iff.mpr hδ] with ω h1 h2 h3 t
  refine bounded_of_rec (x := fun t => piM S σ β κ i p δ t ω) hc0 hc1 hFc
    (h1.trans (le_max_left _ _)) (fun t => ?_) t
  simp only [piM, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hc0]
  have e1 := abs_add_le (piM S σ β κ i p δ t ω) (σ * κ * S.forwardSol (lam2 σ β κ) i t ω)
  have e2 : |σ * κ * S.forwardSol (lam2 σ β κ) i t ω| ≤ σ * κ * max K0 0 := by
    rw [abs_mul, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left ((h2 t).trans (le_max_left _ _)) ha.le
  have e3 := (h3 (t + 1)).trans (le_max_left Mδ 0)
  have e4 : (lam1 σ β κ)⁻¹ * |piM S σ β κ i p δ t ω + σ * κ *
      S.forwardSol (lam2 σ β κ) i t ω| ≤ (lam1 σ β κ)⁻¹ * (|piM S σ β κ i p δ t ω| +
      σ * κ * max K0 0) := mul_le_mul_of_nonneg_left (e1.trans (by linarith)) hc0
  simp only [Fc]
  nlinarith

/-- Cochrane (2023), Fig. 17.6, p. 410, on a probability space (**existence**): for `σκ > 0`,
`β > 0`, essentially bounded adapted rates, essentially bounded `p` known at date 0 and
essentially bounded adapted innovations `δ` with `E_t δ_{t+1} = 0` a.s., `piM` is adapted,
essentially bounded, has innovations `δ` almost surely, satisfies the factored form, and with
`r_t = i_t − E_t π_{t+1}`, `x_t = (π_t − β E_t π_{t+1})/κ` is an equilibrium. -/
theorem piM_equilibrium {σ β κ M Mp Mδ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i : ℕ → Ω → ℝ}
    (hia : StronglyAdapted S.𝓕 i) (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ M) {p : Ω → ℝ}
    (hp0 : StronglyMeasurable[S.𝓕 0] p) (hp : ∀ᵐ ω ∂S.μ, |p ω| ≤ Mp) {δ : ℕ → Ω → ℝ}
    (hδa : StronglyAdapted S.𝓕 δ) (hδ : ∀ t, ∀ᵐ ω ∂S.μ, |δ t ω| ≤ Mδ)
    (hδ0 : ∀ t, S.E t (δ (t + 1)) =ᵐ[S.μ] 0) :
    StronglyAdapted S.𝓕 (piM S σ β κ i p δ) ∧
      (∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |piM S σ β κ i p δ t ω| ≤ K) ∧
      (∀ t, piM S σ β κ i p δ (t + 1) - S.E t (piM S σ β κ i p δ (t + 1)) =ᵐ[S.μ] δ (t + 1)) ∧
      FactoredM S σ β κ i (piM S σ β κ i p δ) ∧
      ModelM S σ β κ i (fun t => i t - S.E t (piM S σ β κ i p δ (t + 1)))
        (fun t => κ⁻¹ • (piM S σ β κ i p δ t - β • S.E t (piM S σ β κ i p δ (t + 1))))
        (piM S σ β κ i p δ) := by
  have hκ : κ ≠ 0 := by rintro rfl; simp at ha
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  set P := piM S σ β κ i p δ with hP
  have had := piM_adapted S (σ := σ) (β := β) (κ := κ) (i := i) hp0 hδa
  obtain ⟨K, hK⟩ := piM_bdd S ha hβ hi hp hδ
  have hPi : ∀ t, Integrable (P t) S.μ := fun t => MeasExpectationSystem.BddRV.integrable
    ⟨((had t).mono (S.𝓕.le t)).aestronglyMeasurable, K, hK t⟩
  have hδi : ∀ t, Integrable (δ t) S.μ := fun t => MeasExpectationSystem.BddRV.integrable
    ⟨((hδa t).mono (S.𝓕.le t)).aestronglyMeasurable, Mδ, hδ t⟩
  have hiI : ∀ t, Integrable (i t) S.μ := fun t => MeasExpectationSystem.BddRV.integrable
    ⟨((hia t).mono (S.𝓕.le t)).aestronglyMeasurable, M, hi t⟩
  -- the forecast of next period's inflation
  have hE : ∀ t, S.E t (P (t + 1)) =ᵐ[S.μ]
      (lam1 σ β κ)⁻¹ • (P t + (σ * κ) • S.forwardSol (lam2 σ β κ) i t) := by
    intro t
    have hX : StronglyMeasurable[S.𝓕 t]
        ((lam1 σ β κ)⁻¹ • (P t + (σ * κ) • S.forwardSol (lam2 σ β κ) i t)) :=
      ((had t).add ((S.forwardSol_adapted _ i t).const_smul _)).const_smul _
    have hXi : Integrable ((lam1 σ β κ)⁻¹ • (P t + (σ * κ) • S.forwardSol (lam2 σ β κ) i t))
        S.μ := ((hPi t).add ((S.integrable_E _ _).smul _)).smul _
    have hEX := S.E_of_stronglyMeasurable hX hXi
    have hP1 : P (t + 1) =
        (lam1 σ β κ)⁻¹ • (P t + (σ * κ) • S.forwardSol (lam2 σ β κ) i t) + δ (t + 1) := rfl
    rw [hP1]
    filter_upwards [S.E_add hXi (hδi (t + 1)) t, hδ0 t] with ω a b
    rw [a, Pi.add_apply, hEX, b, Pi.zero_apply, add_zero]
  have hfac : FactoredM S σ β κ i P := by
    intro t
    filter_upwards [hE t] with ω a
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at a ⊢
    rw [a, ← mul_assoc, mul_inv_cancel₀ hl0, one_mul]
  have hinn : ∀ t, P (t + 1) - S.E t (P (t + 1)) =ᵐ[S.μ] δ (t + 1) := by
    intro t
    filter_upwards [hE t] with ω a
    simp only [Pi.sub_apply]
    rw [a]
    simp only [hP, piM, Pi.add_apply]
    ring
  have h18 := eq1718_of_factoredM S ha hβ hia hi hPi hfac
  refine ⟨had, ⟨K, hK⟩, hinn, hfac, fun t => ⟨hiI t, (hiI t).sub (S.integrable_E _ _),
    ((hPi t).sub ((S.integrable_E _ _).smul _)).smul _, hPi t⟩, fun t => ⟨?_, ?_, ?_⟩⟩
  · have hint : Integrable (P (t + 1) - β • S.E (t + 1) (P (t + 1 + 1))) S.μ :=
      (hPi (t + 1)).sub ((S.integrable_E _ _).smul _)
    filter_upwards [h18 t, S.E_smul κ⁻¹ (P (t + 1) - β • S.E (t + 1) (P (t + 1 + 1))) t,
      S.E_sub (hPi (t + 1)) ((S.integrable_E (t + 1) (P (t + 1 + 1))).smul β) t,
      S.E_smul β (S.E (t + 1) (P (t + 1 + 1))) t, S.E_tower (Nat.le_succ t) (P (t + 1 + 1))]
      with ω e a b c d
    have hk : κ⁻¹ * κ = 1 := inv_mul_cancel₀ hκ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e a b c ⊢
    rw [a, b, c, d]
    rw [show t + 2 = t + 1 + 1 from rfl] at e
    linear_combination κ⁻¹ * e - (σ * i t ω - σ * S.E t (P (t + 1)) ω) * hk
  · exact Eventually.of_forall fun ω => by simp
  · refine Eventually.of_forall fun ω => ?_
    have hk : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination -(P t ω - β * S.E t (P (t + 1)) ω) * hk

/-- Cochrane (2023), Fig. 17.6, p. 410, on a probability space (**uniqueness**): every
equilibrium with essentially bounded inflation, `π_0 = p` a.s. and innovations `δ` a.s. equals
`piM` almost surely at every date. -/
theorem eq_piM {σ β κ M Mπ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i : ℕ → Ω → ℝ}
    (hia : StronglyAdapted S.𝓕 i) (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ M) {p : Ω → ℝ}
    {δ : ℕ → Ω → ℝ} {r x π : ℕ → Ω → ℝ} (h : ModelM S σ β κ i r x π)
    (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) (h0 : π 0 =ᵐ[S.μ] p)
    (hin : ∀ t, π (t + 1) - S.E t (π (t + 1)) =ᵐ[S.μ] δ (t + 1)) :
    ∀ t, π t =ᵐ[S.μ] piM S σ β κ i p δ t := by
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  have hπi : ∀ t, Integrable (π t) S.μ := fun t => (h.1 t).2.2.2
  have hf := factoredM_of_eq1718 S ha hβ hia hi hπi hπ (eq1718_of_modelM S h)
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
    filter_upwards [ih, hin t, hf t] with ω a b c
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at b c
    simp only [piM, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← a]
    have hl : lam1 σ β κ * (lam1 σ β κ)⁻¹ = 1 := mul_inv_cancel₀ hl0
    linear_combination b + (lam1 σ β κ)⁻¹ * c - S.E t (π (t + 1)) ω * hl

end Cochrane.KeynesianStickyPrices.TidyR5InnovEqmMeasure
