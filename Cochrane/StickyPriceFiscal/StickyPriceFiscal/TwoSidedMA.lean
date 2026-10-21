/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.NKModel
import StickyPriceFiscal.ExpectationsFiniteTree

/-!
# Inflation as a two-sided moving average of interest rates

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.1.1, eqs. (5.5), (5.7),
(5.9), (5.10), (5.14), pp. 119–121, and §5.1.3, p. 126; Online Appendix A1, §1.7,
eq. (1.38), pp. 569–571.

The book eliminates output, factors the lag polynomial
`1 − (1 + β + σκ)L⁻¹ + βL⁻² = (1 − λ₁L⁻¹)(1 − λ₂L⁻¹)`, solves the `λ₂` factor forward and the
`λ₁` factor backward, and expands by partial fractions. Here the time index is `ℕ`, so the
backward sums are finite and the infinite past is replaced by one explicit pre-sample term
`λ₁^{−t} K` with `K` known at date 0.

## Main results

* `nk_iff_second`: (5.1)–(5.2) with `κ ≠ 0` iff `κ x_t = π_t − β E_t π_{t+1}` and
  `π_t − (1 + β + σκ) E_t π_{t+1} + β E_t π_{t+2} = −σκ i_t` (A1 p. 569).
* `factor_of_second`, `second_of_factor`, `nk_iff_factor`: for bounded processes and bounded
  adapted `i`, the second-order equation holds iff `π_t − λ₁ E_t π_{t+1} = −σκ F_t` with
  `F_t = ∑_{k≥0} λ₂ᵏ E_t i_{t+k}` (the forward-solved `λ₂` factor).
* (5.5): `piMA` (the right-hand side of (5.5)), `piMA_E_succ`, `piMA_factor`, `piMA_bounded`,
  `piMA_adapted`, `piMA_nk` (every `(K, δ)` gives a bounded equilibrium), and the
  **characterisation** `factor_iff_piMA`, `eq_5_5`: bounded `(x, π)` solve (5.1)–(5.2) iff
  `π = piMA K δ` for some date-0 `K` and bounded martingale-difference `δ`; `eq_5_5_sum` is the
  printed form with genuine sums.
* (5.7): `eq_5_7`, `eq_5_7_sum`; survey error E26 (`δ ≠ Δπ` in general): `delta_eq_innov_iff`
  and the genuine-uncertainty counterexample `e26_coin`.
* (5.14): `eq_5_14`, `eq_5_14_sum`.
* (5.9)–(5.10): `flex_iff`; §5.1.3: `flex_no_dynamics`.
* Anticipated rate rises (Fig. 5.2, p. 124, and survey error E30, p. 129):
  `anticipated_moves_before` — with sticky prices inflation cannot stay at zero up to the date
  of an announced rise; `flex_one_period_after` — with flexible prices it can.
-/

namespace Cochrane.StickyPriceFiscal.TwoSidedMA

open Filter Topology NKModel

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Eliminating output -/

/-- Cochrane (2023), A1 §1.7, p. 569: with `κ ≠ 0`, (5.1)–(5.2) hold iff output is given by the
Phillips curve and inflation solves
`π_t − (1 + β + σκ) E_t π_{t+1} + β E_t π_{t+2} = −σκ i_t`. -/
theorem nk_iff_second {σ β κ : ℝ} (hκ : κ ≠ 0) {i x π : ℕ → Ω → ℝ} :
    NK 𝔼 σ β κ i x π ↔ (∀ t, x t = κ⁻¹ • (π t - β • 𝔼.E t (π (t + 1)))) ∧
      ∀ t, π t - (1 + β + σ * κ) • 𝔼.E t (π (t + 1)) + β • 𝔼.E t (π (t + 2)) =
        -(σ * κ) • i t := by
  constructor
  · rintro ⟨his, hpc⟩
    refine ⟨fun t => ?_, fun t => ?_⟩
    · funext ω
      have h := congrFun (hpc t) ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h ⊢
      field_simp
      linarith
    · funext ω
      have h1 := congrFun (his t) ω
      have h2 := congrFun (hpc t) ω
      have h3 := congrFun (congrArg (𝔼.E t) (hpc (t + 1))) ω
      rw [map_add, map_smul, map_smul, 𝔼.tower (Nat.le_succ t)] at h3
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h1 h2 h3 ⊢
      linear_combination h2 + κ * h1 - h3
  · rintro ⟨hx, hsec⟩
    refine ⟨fun t => ?_, fun t => ?_⟩
    · funext ω
      have h := congrFun (hsec t) ω
      have hx1 := congrFun (congrArg (𝔼.E t) (hx (t + 1))) ω
      rw [map_smul, map_sub, map_smul, 𝔼.tower (Nat.le_succ t)] at hx1
      have hx0 := congrFun (hx t) ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, 
        neg_mul] at h hx1 hx0 ⊢
      rw [hx0, hx1]
      field_simp
      linear_combination h
    · funext ω
      have hx0 := congrFun (hx t) ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hx0 ⊢
      rw [hx0]
      field_simp
      ring

/-! ### Factoring the lag polynomial -/

/-- Cochrane (2023), A1 §1.7, p. 570: the forward-solved `λ₂` factor
`F_t = ∑_{k≥0} λ₂ᵏ E_t i_{t+k}` solves `F_t = λ₂ E_t F_{t+1} + i_t`. -/
theorem F_solves {σ β κ Mi : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i : ℕ → Ω → ℝ}
    (hi : 𝔼.Adapted i) (hib : ∀ t ω, |i t ω| ≤ Mi) (t : ℕ) :
    𝔼.forwardSeries (lam2 σ β κ) i t =
      lam2 σ β κ • 𝔼.E t (𝔼.forwardSeries (lam2 σ β κ) i (t + 1)) + i t :=
  𝔼.forwardSeries_solves (lam2_pos ha hβ).le (lam2_lt_one ha hβ) hib hi t

/-- Cochrane (2023), A1 §1.7, p. 570: `(1 − λ₁L⁻¹)(1 − λ₂L⁻¹)π = −σκ i` with the `λ₂` factor
solved forward: a bounded adapted solution of the second-order equation satisfies
`π_t − λ₁ E_t π_{t+1} = −σκ F_t`. -/
theorem factor_of_second {σ β κ Mi : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i π : ℕ → Ω → ℝ}
    (hi : 𝔼.Adapted i) (hib : ∀ t ω, |i t ω| ≤ Mi) (hπb : BoundedProc π)
    (hsec : ∀ t, π t - (1 + β + σ * κ) • 𝔼.E t (π (t + 1)) + β • 𝔼.E t (π (t + 2)) =
      -(σ * κ) • i t) (t : ℕ) :
    π t - lam1 σ β κ • 𝔼.E t (π (t + 1)) =
      -(σ * κ) • 𝔼.forwardSeries (lam2 σ β κ) i t := by
  set l1 := lam1 σ β κ with hl1
  set l2 := lam2 σ β κ with hl2
  set w : ℕ → Ω → ℝ := fun s => π s - l1 • 𝔼.E s (π (s + 1)) with hw
  set z : ℕ → Ω → ℝ := fun s => -(σ * κ) • 𝔼.forwardSeries l2 i s with hz
  have hsum : l1 + l2 = 1 + β + σ * κ := lam_sum σ β κ
  have hprod : l1 * l2 = β := lam_prod ha hβ
  have hl2a : |l2| < 1 := by
    rw [abs_of_pos (lam2_pos ha hβ)]; exact lam2_lt_one ha hβ
  have hwsol : ∀ s, w s = l2 • 𝔼.E s (w (s + 1)) + (-(σ * κ) • i) s := by
    intro s
    funext ω
    have h := congrFun (hsec s) ω
    have hE : 𝔼.E s (w (s + 1)) = 𝔼.E s (π (s + 1)) - l1 • 𝔼.E s (π (s + 2)) := by
      simp only [hw]
      rw [map_sub, map_smul, 𝔼.tower (Nat.le_succ s)]
    rw [hE]
    simp only [hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, neg_mul] at h ⊢
    linear_combination h - 𝔼.E s (π (s + 1)) ω * hsum + 𝔼.E s (π (s + 2)) ω * hprod
  have hzsol : ∀ s, z s = l2 • 𝔼.E s (z (s + 1)) + (-(σ * κ) • i) s := by
    intro s
    simp only [hz]
    rw [F_solves 𝔼 ha hβ hi hib s, map_smul, smul_add, smul_comm]
    rfl
  have hwb : BoundedProc w := by
    obtain ⟨M, hM⟩ := hπb
    refine ⟨M + |l1| * M, fun s ω => ?_⟩
    simp only [hw, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    calc |π s ω - l1 * 𝔼.E s (π (s + 1)) ω| ≤ |π s ω| + |l1| * |𝔼.E s (π (s + 1)) ω| := by
          rw [← abs_mul]; exact abs_sub _ _
      _ ≤ M + |l1| * M := by
          gcongr
          · exact hM s ω
          · exact 𝔼.abs_E_le (hM (s + 1)) s ω
  have hzb : BoundedProc z := by
    obtain ⟨M, hM⟩ := 𝔼.forwardSeries_bounded (lam2_pos ha hβ).le (lam2_lt_one ha hβ) hib
    refine ⟨|σ * κ| * M, fun s ω => ?_⟩
    simp only [hz, Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hM s ω) (by positivity)
  have := 𝔼.forward_unique hl2a hwsol hzsol hwb hzb
  exact congrFun this t

/-- Cochrane (2023), A1 §1.7, p. 570: conversely, `π_t − λ₁ E_t π_{t+1} = −σκ F_t` implies the
second-order equation (no boundedness needed). -/
theorem second_of_factor {σ β κ Mi : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i π : ℕ → Ω → ℝ}
    (hi : 𝔼.Adapted i) (hib : ∀ t ω, |i t ω| ≤ Mi)
    (hf : ∀ t, π t - lam1 σ β κ • 𝔼.E t (π (t + 1)) =
      -(σ * κ) • 𝔼.forwardSeries (lam2 σ β κ) i t) (t : ℕ) :
    π t - (1 + β + σ * κ) • 𝔼.E t (π (t + 1)) + β • 𝔼.E t (π (t + 2)) = -(σ * κ) • i t := by
  funext ω
  have h0 := congrFun (hf t) ω
  have h1 := congrFun (congrArg (𝔼.E t) (hf (t + 1))) ω
  rw [map_sub, map_smul, map_smul, 𝔼.tower (Nat.le_succ t)] at h1
  have hF := congrFun (F_solves 𝔼 ha hβ hi hib t) ω
  have hsum := lam_sum σ β κ
  have hprod := lam_prod ha hβ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, neg_mul] at h0 h1 hF ⊢
  linear_combination h0 - lam2 σ β κ * h1 - σ * κ * hF + 𝔼.E t (π (t + 1)) ω * hsum -
    𝔼.E t (π (t + 2)) ω * hprod

/-- Cochrane (2023), eqs. (5.1)–(5.2) and A1 §1.7: for bounded `(x, π)`, `κ > 0`, and bounded
adapted `i`, (5.1)–(5.2) hold iff `κ x_t = π_t − β E_t π_{t+1}` and
`π_t − λ₁ E_t π_{t+1} = −σκ F_t`. -/
theorem nk_iff_factor {σ β κ Mi : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    {i x π : ℕ → Ω → ℝ} (hi : 𝔼.Adapted i) (hib : ∀ t ω, |i t ω| ≤ Mi) (hπb : BoundedProc π) :
    NK 𝔼 σ β κ i x π ↔ (∀ t, x t = κ⁻¹ • (π t - β • 𝔼.E t (π (t + 1)))) ∧
      ∀ t, π t - lam1 σ β κ • 𝔼.E t (π (t + 1)) =
        -(σ * κ) • 𝔼.forwardSeries (lam2 σ β κ) i t := by
  have ha := mul_pos hσ hκ
  rw [nk_iff_second 𝔼 hκ.ne']
  constructor
  · rintro ⟨hx, hsec⟩
    exact ⟨hx, factor_of_second 𝔼 ha hβ hi hib hπb hsec⟩
  · rintro ⟨hx, hf⟩
    exact ⟨hx, second_of_factor 𝔼 ha hβ hi hib hf⟩

/-! ### The right-hand side of (5.5) -/

/-- Cochrane (2023), eq. (5.5), p. 119: the finite backward geometric sum
`bsum q u t = ∑_{j<t} qʲ u_{t−1−j}`, by its recursion. -/
def bsum (q : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => q • bsum q u t + u t

/-- Cochrane (2023), eq. (5.5), p. 119: `bsum q u (t + 1) = ∑_{j=0}^{t} qʲ u_{t−j}`. -/
theorem bsum_succ_eq_sum (q : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) :
    bsum q u (t + 1) = ∑ j ∈ Finset.range (t + 1), q ^ j • u (t - j) := by
  induction t with
  | zero => simp [bsum]
  | succ t ih =>
    rw [bsum, ih, Finset.smul_sum]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [smul_smul, pow_succ', pow_zero, one_smul, Nat.sub_zero, Nat.add_sub_add_right]

/-- Cochrane (2023), eq. (5.5), p. 119: if each `u_t` is known at `t + 1`, `bsum q u` is
adapted. -/
theorem bsum_adapted {q : ℝ} {u : ℕ → Ω → ℝ} (hu : ∀ t, 𝔼.E (t + 1) (u t) = u t) :
    𝔼.Adapted (bsum q u) := by
  intro t
  induction t with
  | zero => simp [bsum]
  | succ t ih =>
    rw [bsum, map_add, map_smul, hu t, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih]

/-- Cochrane (2023), p. 119 ("the moving averages as expressed converge"): for `0 ≤ q < 1` and
`|u| ≤ M`, `|bsum q u t| ≤ M/(1 − q)`. -/
theorem bsum_bounded {q M : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (t : ℕ) (ω : Ω) : |bsum q u t ω| ≤ M / (1 - q) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hu 0 ω)
  have h1 : 0 < 1 - q := by linarith
  induction t with
  | zero => simp only [bsum, Pi.zero_apply, abs_zero]; positivity
  | succ t ih =>
    simp only [bsum, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc |q * bsum q u t ω + u t ω| ≤ q * (M / (1 - q)) + M := by
          refine (abs_add_le _ _).trans (add_le_add ?_ (hu t ω))
          rw [abs_mul, abs_of_nonneg hq0]
          exact mul_le_mul_of_nonneg_left ih hq0
      _ = M / (1 - q) := by field_simp; ring

/-- Cochrane (2023), eq. (5.5), p. 119: the coefficient `c = σκ/(λ₁ − λ₂)`. -/
noncomputable def coef (σ β κ : ℝ) : ℝ := σ * κ / (lam1 σ β κ - lam2 σ β κ)

/-- Cochrane (2023), eq. (5.5), p. 119: `c (λ₁ − λ₂) = σκ`. -/
theorem coef_mul {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) :
    coef σ β κ * (lam1 σ β κ - lam2 σ β κ) = σ * κ := by
  unfold coef
  exact div_mul_cancel₀ _ (sub_ne_zero.mpr (lam2_lt_lam1 ha hβ).ne')

/-- Cochrane (2023), eq. (5.5), p. 119 (ℕ-indexed): the right-hand side
`c[∑_{j<t} λ₁^{−j} i_{t−1−j} + λ₂ F_t] + ∑_{j<t} λ₁^{−j} δ_{t−j} + λ₁·λ₁^{−t} K`, with
`F_t = ∑_{k≥0} λ₂ᵏ E_t i_{t+k}` and a pre-sample term `K` known at date 0. At date `t + 1` this
is (5.5) (`eq_5_5_sum`). -/
noncomputable def piMA (σ β κ : ℝ) (i δ : ℕ → Ω → ℝ) (K : Ω → ℝ) : ℕ → Ω → ℝ := fun t =>
  coef σ β κ • (bsum (lam1 σ β κ)⁻¹ i t + lam2 σ β κ • 𝔼.forwardSeries (lam2 σ β κ) i t) +
    bsum (lam1 σ β κ)⁻¹ (fun s => δ (s + 1)) t + (lam1 σ β κ * (lam1 σ β κ)⁻¹ ^ t) • K

/-- Cochrane (2023), eq. (5.5), p. 119: the one-step forecast of `piMA`,
`E_t π_{t+1} = c[λ₁⁻¹ B_t + F_t] + λ₁⁻¹ D_t + λ₁^{−t} K`. -/
theorem piMA_E_succ {σ β κ Mi : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i δ : ℕ → Ω → ℝ}
    {K : Ω → ℝ} (hi : 𝔼.Adapted i) (hib : ∀ t ω, |i t ω| ≤ Mi) (hK : 𝔼.E 0 K = K)
    (hδa : 𝔼.Adapted δ) (hδ : ∀ t, 𝔼.E t (δ (t + 1)) = 0) (t : ℕ) :
    𝔼.E t (piMA 𝔼 σ β κ i δ K (t + 1)) =
      coef σ β κ • ((lam1 σ β κ)⁻¹ • bsum (lam1 σ β κ)⁻¹ i t +
        𝔼.forwardSeries (lam2 σ β κ) i t) +
      (lam1 σ β κ)⁻¹ • bsum (lam1 σ β κ)⁻¹ (fun s => δ (s + 1)) t +
      ((lam1 σ β κ)⁻¹ ^ t) • K := by
  have hB := bsum_adapted 𝔼 (q := (lam1 σ β κ)⁻¹) (u := i)
    (fun s => ForwardSolution.E_of_known 𝔼 (Nat.le_succ s) (hi s))
  have hD := bsum_adapted 𝔼 (q := (lam1 σ β κ)⁻¹) (u := fun s => δ (s + 1)) (fun s => hδa _)
  have hKt : 𝔼.E t K = K := ForwardSolution.E_of_known 𝔼 (Nat.zero_le t) hK
  have hF := F_solves 𝔼 ha hβ hi hib t
  have hl0 : lam1 σ β κ ≠ 0 := (lam1_pos ha hβ).ne'
  unfold piMA
  simp only [bsum]
  rw [map_add, map_add, map_smul, map_add, map_add, map_smul, map_smul, map_add, map_smul,
    map_smul, hB t, hD t, hKt, hi t, hδ t, add_zero]
  have hpow : lam1 σ β κ * (lam1 σ β κ)⁻¹ ^ (t + 1) = (lam1 σ β κ)⁻¹ ^ t := by
    rw [pow_succ]; field_simp
  rw [hpow]
  conv_rhs => rw [hF]
  abel_nf

/-- Cochrane (2023), eq. (5.5) and A1 (1.38), p. 570: `piMA` solves the factored equation
`π_t − λ₁ E_t π_{t+1} = −σκ F_t` for every date-0 `K` and martingale-difference `δ`. -/
theorem piMA_factor {σ β κ Mi : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i δ : ℕ → Ω → ℝ}
    {K : Ω → ℝ} (hi : 𝔼.Adapted i) (hib : ∀ t ω, |i t ω| ≤ Mi) (hK : 𝔼.E 0 K = K)
    (hδa : 𝔼.Adapted δ) (hδ : ∀ t, 𝔼.E t (δ (t + 1)) = 0) (t : ℕ) :
    piMA 𝔼 σ β κ i δ K t - lam1 σ β κ • 𝔼.E t (piMA 𝔼 σ β κ i δ K (t + 1)) =
      -(σ * κ) • 𝔼.forwardSeries (lam2 σ β κ) i t := by
  rw [piMA_E_succ 𝔼 ha hβ hi hib hK hδa hδ t]
  have hl0 : lam1 σ β κ ≠ 0 := (lam1_pos ha hβ).ne'
  have hc := coef_mul ha hβ
  funext ω
  unfold piMA
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, neg_mul]
  rw [← hc]
  field_simp
  ring

/-- Cochrane (2023), p. 119: `piMA` is adapted. -/
theorem piMA_adapted {σ β κ Mi : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i δ : ℕ → Ω → ℝ}
    {K : Ω → ℝ} (hi : 𝔼.Adapted i) (hib : ∀ t ω, |i t ω| ≤ Mi) (hK : 𝔼.E 0 K = K)
    (hδa : 𝔼.Adapted δ) : 𝔼.Adapted (piMA 𝔼 σ β κ i δ K) := by
  have hB := bsum_adapted 𝔼 (q := (lam1 σ β κ)⁻¹) (u := i)
    (fun s => ForwardSolution.E_of_known 𝔼 (Nat.le_succ s) (hi s))
  have hD := bsum_adapted 𝔼 (q := (lam1 σ β κ)⁻¹) (u := fun s => δ (s + 1)) (fun s => hδa _)
  have hF := 𝔼.forwardSeries_adapted (lam2_pos ha hβ).le (lam2_lt_one ha hβ) hib
  intro t
  have hKt : 𝔼.E t K = K := ForwardSolution.E_of_known 𝔼 (Nat.zero_le t) hK
  unfold piMA
  rw [map_add, map_add, map_smul, map_add, map_smul, map_smul, hB t, hD t, hF t, hKt]

/-- Cochrane (2023), p. 119 ("the moving averages as expressed converge"): `piMA` is bounded
when `i`, `δ` and `K` are. -/
theorem piMA_bounded {σ β κ Mi Mδ MK : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i δ : ℕ → Ω → ℝ}
    {K : Ω → ℝ} (hib : ∀ t ω, |i t ω| ≤ Mi) (hδb : ∀ t ω, |δ t ω| ≤ Mδ)
    (hKb : ∀ ω, |K ω| ≤ MK) : BoundedProc (piMA 𝔼 σ β κ i δ K) := by
  set l1 := lam1 σ β κ
  set l2 := lam2 σ β κ
  have h1 : 1 < l1 := one_lt_lam1 ha hβ
  have hl2 : 0 < l2 := lam2_pos ha hβ
  have hl21 : l2 < 1 := lam2_lt_one ha hβ
  have hq0 : 0 ≤ l1⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : l1⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  obtain ⟨MF, hMF⟩ := 𝔼.forwardSeries_bounded hl2.le hl21 hib
  refine ⟨|coef σ β κ| * (Mi / (1 - l1⁻¹) + l2 * MF) + Mδ / (1 - l1⁻¹) + l1 * MK,
    fun t ω => ?_⟩
  have hB := bsum_bounded hq0 hq1 hib t ω
  have hD := bsum_bounded hq0 hq1 (u := fun s => δ (s + 1)) (fun s => hδb (s + 1)) t ω
  have hqt : (l1⁻¹) ^ t ≤ 1 := pow_le_one₀ hq0 hq1.le
  unfold piMA
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e1 : |coef σ β κ * (bsum l1⁻¹ i t ω + l2 * 𝔼.forwardSeries l2 i t ω)| ≤
      |coef σ β κ| * (Mi / (1 - l1⁻¹) + l2 * MF) := by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hB ?_)) (abs_nonneg _)
    rw [abs_mul, abs_of_pos hl2]
    exact mul_le_mul_of_nonneg_left (hMF t ω) hl2.le
  have e3 : |l1 * l1⁻¹ ^ t * K ω| ≤ l1 * MK := by
    rw [abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < l1), abs_of_nonneg (pow_nonneg hq0 t)]
    calc l1 * l1⁻¹ ^ t * |K ω| ≤ l1 * 1 * MK := by gcongr; exact hKb ω
      _ = l1 * MK := by ring
  calc _ ≤ |coef σ β κ * (bsum l1⁻¹ i t ω + l2 * 𝔼.forwardSeries l2 i t ω)| +
        |bsum l1⁻¹ (fun s => δ (s + 1)) t ω| + |l1 * l1⁻¹ ^ t * K ω| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add e1 hD) e3

/-- Cochrane (2023), eqs. (5.5) and (5.14), pp. 119–121: for every date-0 `K` and bounded
martingale-difference `δ`, `π = piMA K δ` with `κ x_t = π_t − β E_t π_{t+1}` is a bounded
solution of (5.1)–(5.2). -/
theorem piMA_nk {σ β κ Mi Mδ MK : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) {i δ : ℕ → Ω → ℝ}
    {K : Ω → ℝ} (hi : 𝔼.Adapted i) (hib : ∀ t ω, |i t ω| ≤ Mi) (hK : 𝔼.E 0 K = K)
    (hKb : ∀ ω, |K ω| ≤ MK) (hδa : 𝔼.Adapted δ) (hδb : ∀ t ω, |δ t ω| ≤ Mδ)
    (hδ : ∀ t, 𝔼.E t (δ (t + 1)) = 0) :
    NK 𝔼 σ β κ i (fun t => κ⁻¹ • (piMA 𝔼 σ β κ i δ K t -
      β • 𝔼.E t (piMA 𝔼 σ β κ i δ K (t + 1)))) (piMA 𝔼 σ β κ i δ K) ∧
      BoundedProc (piMA 𝔼 σ β κ i δ K) ∧
      BoundedProc (fun t => κ⁻¹ • (piMA 𝔼 σ β κ i δ K t -
        β • 𝔼.E t (piMA 𝔼 σ β κ i δ K (t + 1)))) := by
  have ha := mul_pos hσ hκ
  have hb := piMA_bounded 𝔼 ha hβ hib hδb hKb
  refine ⟨(nk_iff_factor 𝔼 hσ hκ hβ hi hib hb).mpr
    ⟨fun t => rfl, piMA_factor 𝔼 ha hβ hi hib hK hδa hδ⟩, hb, ?_⟩
  obtain ⟨M, hM⟩ := hb
  refine ⟨κ⁻¹ * (M + β * M), fun t ω => ?_⟩
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [abs_mul, abs_of_pos (inv_pos.mpr hκ)]
  refine mul_le_mul_of_nonneg_left ?_ (inv_pos.mpr hκ).le
  refine (abs_sub _ _).trans (add_le_add (hM t ω) ?_)
  rw [abs_mul, abs_of_pos hβ]
  exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hM (t + 1)) t ω) hβ.le

/-- Cochrane (2023), eq. (5.7), p. 120: the expectational shock implied by an inflation path,
`δ_{t+1} = ΔE_{t+1} π_{t+1} − c λ₂ ΔE_{t+1} F_{t+1}` (zero at date 0). -/
noncomputable def deltaOf (σ β κ : ℝ) (i π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | s + 1 => (π (s + 1) - 𝔼.E s (π (s + 1))) - (coef σ β κ * lam2 σ β κ) •
      (𝔼.forwardSeries (lam2 σ β κ) i (s + 1) -
        𝔼.E s (𝔼.forwardSeries (lam2 σ β κ) i (s + 1)))

/-- Cochrane (2023), eq. (5.5), p. 119: the pre-sample term implied by an inflation path,
`K = λ₁⁻¹(π_0 − c λ₂ F_0)`. -/
noncomputable def KOf (σ β κ : ℝ) (i π : ℕ → Ω → ℝ) : Ω → ℝ :=
  (lam1 σ β κ)⁻¹ • (π 0 - (coef σ β κ * lam2 σ β κ) • 𝔼.forwardSeries (lam2 σ β κ) i 0)

/-- Cochrane (2023), eq. (5.5), p. 119, **characterisation**: a bounded adapted `π` solves
`π_t − λ₁ E_t π_{t+1} = −σκ F_t` iff `π = piMA K δ` for some date-0 `K` and some bounded
adapted martingale-difference `δ` (`E_t δ_{t+1} = 0`). -/
theorem factor_iff_piMA {σ β κ Mi : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i π : ℕ → Ω → ℝ}
    (hi : 𝔼.Adapted i) (hib : ∀ t ω, |i t ω| ≤ Mi) (hπa : 𝔼.Adapted π)
    (hπb : BoundedProc π) :
    (∀ t, π t - lam1 σ β κ • 𝔼.E t (π (t + 1)) =
      -(σ * κ) • 𝔼.forwardSeries (lam2 σ β κ) i t) ↔
    ∃ K δ, 𝔼.E 0 K = K ∧ 𝔼.Adapted δ ∧ (∀ t, 𝔼.E t (δ (t + 1)) = 0) ∧ BoundedProc δ ∧
      π = piMA 𝔼 σ β κ i δ K := by
  have hFa : 𝔼.Adapted (𝔼.forwardSeries (lam2 σ β κ) i) :=
    𝔼.forwardSeries_adapted (lam2_pos ha hβ).le (lam2_lt_one ha hβ) hib
  have hl0 : lam1 σ β κ ≠ 0 := (lam1_pos ha hβ).ne'
  constructor
  · intro hf
    refine ⟨KOf 𝔼 σ β κ i π, deltaOf 𝔼 σ β κ i π, ?_, ?_, ?_, ?_, ?_⟩
    · unfold KOf
      rw [map_smul, map_sub, map_smul, hπa 0, hFa 0]
    · intro t
      cases t with
      | zero => simp [deltaOf]
      | succ s =>
        simp only [deltaOf]
        rw [map_sub, map_sub, map_smul, map_sub, hπa, hFa,
          ForwardSolution.E_of_known 𝔼 (Nat.le_succ s) (𝔼.E_E_self s _),
          ForwardSolution.E_of_known 𝔼 (Nat.le_succ s) (𝔼.E_E_self s _)]
    · intro t
      simp only [deltaOf]
      rw [map_sub, map_sub, map_smul, map_sub, 𝔼.E_E_self, 𝔼.E_E_self, sub_self, sub_self,
        smul_zero, sub_self]
    · obtain ⟨M, hM⟩ := hπb
      obtain ⟨MF, hMF⟩ := 𝔼.forwardSeries_bounded (lam2_pos ha hβ).le (lam2_lt_one ha hβ) hib
      refine ⟨(M + M) + |coef σ β κ * lam2 σ β κ| * (MF + MF), fun t ω => ?_⟩
      cases t with
      | zero =>
        simp only [deltaOf, Pi.zero_apply, abs_zero]
        have := (abs_nonneg (π 0 ω)).trans (hM 0 ω)
        have := (abs_nonneg (𝔼.forwardSeries (lam2 σ β κ) i 0 ω)).trans (hMF 0 ω)
        positivity
      | succ s =>
        simp only [deltaOf, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        refine (abs_sub _ _).trans (add_le_add ?_ ?_)
        · exact (abs_sub _ _).trans (add_le_add (hM _ ω) (𝔼.abs_E_le (hM (s + 1)) s ω))
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_left
            ((abs_sub _ _).trans (add_le_add (hMF _ ω) (𝔼.abs_E_le (hMF (s + 1)) s ω)))
            (abs_nonneg _)
    · funext t
      induction t with
      | zero =>
        funext ω
        simp only [piMA, bsum, KOf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
          pow_zero, mul_one, zero_add, add_zero]
        field_simp
        ring
      | succ t ih =>
        funext ω
        have e1 := congrFun (hf t) ω
        have e2 := congrFun ih ω
        have e3 := congrFun (F_solves 𝔼 ha hβ hi hib t) ω
        have hc := coef_mul ha hβ
        simp only [piMA, bsum, deltaOf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
          neg_mul] at e1 e2 e3 ⊢
        have hq : lam1 σ β κ * (lam1 σ β κ)⁻¹ = 1 := mul_inv_cancel₀ hl0
        linear_combination (-(lam1 σ β κ)⁻¹) * e1 + (lam1 σ β κ)⁻¹ * e2 + coef σ β κ * e3 -
          (𝔼.E t (π (t + 1)) ω - coef σ β κ * 𝔼.forwardSeries (lam2 σ β κ) i t ω) * hq -
          ((lam1 σ β κ)⁻¹ * 𝔼.forwardSeries (lam2 σ β κ) i t ω) * hc
  · rintro ⟨K, δ, hK, hδa, hδ, _, rfl⟩
    exact piMA_factor 𝔼 ha hβ hi hib hK hδa hδ

/-- Cochrane (2023), eq. (5.5), p. 119, and A1 §1.7, pp. 569–570 — **the characterisation**:
for `σ, κ > 0`, `0 < β < 1` and bounded adapted `i`, bounded `(x, π)` solve (5.1)–(5.2) iff
`κ x_t = π_t − β E_t π_{t+1}` and `π = piMA K δ` for some date-0 `K` and bounded
martingale-difference `δ`. -/
theorem eq_5_5 {σ β κ Mi : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) {i x π : ℕ → Ω → ℝ}
    (hi : 𝔼.Adapted i) (hib : ∀ t ω, |i t ω| ≤ Mi) (hπb : BoundedProc π) :
    NK 𝔼 σ β κ i x π ↔ (∀ t, x t = κ⁻¹ • (π t - β • 𝔼.E t (π (t + 1)))) ∧
      ∃ K δ, 𝔼.E 0 K = K ∧ 𝔼.Adapted δ ∧ (∀ t, 𝔼.E t (δ (t + 1)) = 0) ∧ BoundedProc δ ∧
        π = piMA 𝔼 σ β κ i δ K := by
  have ha := mul_pos hσ hκ
  constructor
  · intro hnk
    have hxa := is_adapted 𝔼 hi hnk.1
    have hπa : 𝔼.Adapted π := fun t => by
      conv_lhs => rw [hnk.2 t]
      rw [map_add, map_smul, map_smul, 𝔼.E_E_self, hxa t, ← hnk.2 t]
    obtain ⟨hx, hf⟩ := (nk_iff_factor 𝔼 hσ hκ hβ hi hib hπb).mp hnk
    exact ⟨hx, (factor_iff_piMA 𝔼 ha hβ hi hib hπa hπb).mp hf⟩
  · rintro ⟨hx, K, δ, hK, hδa, hδ, _, rfl⟩
    exact (nk_iff_factor 𝔼 hσ hκ hβ hi hib hπb).mpr ⟨hx, piMA_factor 𝔼 ha hβ hi hib hK hδa hδ⟩

/-- Cochrane (2023), eq. (5.5), p. 119, printed form: for `π = piMA K δ`,
`π_{t+1} = c[∑_{j=0}^{t} λ₁^{−j} i_{t−j} + ∑_{j≥1} λ₂ʲ E_{t+1} i_{t+j}]
  + ∑_{j=0}^{t} λ₁^{−j} δ_{t+1−j} + λ₁^{−t} K`, the forward series converging. -/
theorem eq_5_5_sum {σ β κ Mi : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i δ : ℕ → Ω → ℝ}
    (K : Ω → ℝ) (hib : ∀ t ω, |i t ω| ≤ Mi) (t : ℕ) (ω : Ω) :
    Summable (fun j : ℕ => lam2 σ β κ ^ (j + 1) * 𝔼.E (t + 1) (i (t + 1 + j)) ω) ∧
    piMA 𝔼 σ β κ i δ K (t + 1) ω = coef σ β κ *
      (∑ j ∈ Finset.range (t + 1), (lam1 σ β κ)⁻¹ ^ j * i (t - j) ω +
        ∑' j : ℕ, lam2 σ β κ ^ (j + 1) * 𝔼.E (t + 1) (i (t + 1 + j)) ω) +
      ∑ j ∈ Finset.range (t + 1), (lam1 σ β κ)⁻¹ ^ j * δ (t + 1 - j) ω +
      (lam1 σ β κ)⁻¹ ^ t * K ω := by
  have hl0 : lam1 σ β κ ≠ 0 := (lam1_pos ha hβ).ne'
  have hs := 𝔼.forwardSeries_summable (lam2_pos ha hβ).le (lam2_lt_one ha hβ) hib (t + 1) ω
  refine ⟨?_, ?_⟩
  · have := hs.mul_left (lam2 σ β κ)
    refine this.congr fun j => ?_
    ring
  · unfold piMA
    rw [bsum_succ_eq_sum, bsum_succ_eq_sum]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    have hF : lam2 σ β κ * 𝔼.forwardSeries (lam2 σ β κ) i (t + 1) ω =
        ∑' j : ℕ, lam2 σ β κ ^ (j + 1) * 𝔼.E (t + 1) (i (t + 1 + j)) ω := by
      unfold ExpectationSystem.forwardSeries
      rw [← tsum_mul_left]
      exact tsum_congr fun j => by ring
    have hδs : ∑ j ∈ Finset.range (t + 1), (lam1 σ β κ)⁻¹ ^ j * δ (t - j + 1) ω =
        ∑ j ∈ Finset.range (t + 1), (lam1 σ β κ)⁻¹ ^ j * δ (t + 1 - j) ω := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      congr 3
      omega
    have hpow : lam1 σ β κ * (lam1 σ β κ)⁻¹ ^ (t + 1) = (lam1 σ β κ)⁻¹ ^ t := by
      rw [pow_succ]; field_simp
    rw [hF, hδs, hpow]

/-! ### (5.7): innovations -/

/-- Cochrane (2023), eq. (5.7), p. 120: for `π = piMA K δ`,
`ΔE_{t+1} π_{t+1} = c λ₂ ΔE_{t+1} F_{t+1} + δ_{t+1}`. -/
theorem eq_5_7 {σ β κ Mi : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i δ : ℕ → Ω → ℝ}
    {K : Ω → ℝ} (hi : 𝔼.Adapted i) (hib : ∀ t ω, |i t ω| ≤ Mi) (hK : 𝔼.E 0 K = K)
    (hδa : 𝔼.Adapted δ) (hδ : ∀ t, 𝔼.E t (δ (t + 1)) = 0) (t : ℕ) :
    piMA 𝔼 σ β κ i δ K (t + 1) - 𝔼.E t (piMA 𝔼 σ β κ i δ K (t + 1)) =
      (coef σ β κ * lam2 σ β κ) • (𝔼.forwardSeries (lam2 σ β κ) i (t + 1) -
        𝔼.E t (𝔼.forwardSeries (lam2 σ β κ) i (t + 1))) + δ (t + 1) := by
  rw [piMA_E_succ 𝔼 ha hβ hi hib hK hδa hδ t]
  have hl0 : lam1 σ β κ ≠ 0 := (lam1_pos ha hβ).ne'
  funext ω
  have hFω := congrFun (F_solves 𝔼 ha hβ hi hib t) ω
  unfold piMA
  simp only [bsum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hFω ⊢
  have hpow : lam1 σ β κ * (lam1 σ β κ)⁻¹ ^ (t + 1) = (lam1 σ β κ)⁻¹ ^ t := by
    rw [pow_succ]; field_simp
  rw [hpow]
  linear_combination (-coef σ β κ) * hFω

/-- Cochrane (2023), eq. (5.7), p. 120, printed form: the rate-news term is
`λ₂ ΔE_{t+1} F_{t+1} = ∑_{j≥1} λ₂ʲ ΔE_{t+1} i_{t+j}`, a convergent series. -/
theorem eq_5_7_sum {σ β κ Mi : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i : ℕ → Ω → ℝ}
    (hib : ∀ t ω, |i t ω| ≤ Mi) (t : ℕ) (ω : Ω) :
    HasSum (fun j : ℕ => lam2 σ β κ ^ (j + 1) *
      (𝔼.E (t + 1) (i (t + 1 + j)) ω - 𝔼.E t (i (t + 1 + j)) ω))
      (lam2 σ β κ * (𝔼.forwardSeries (lam2 σ β κ) i (t + 1) ω -
        𝔼.E t (𝔼.forwardSeries (lam2 σ β κ) i (t + 1)) ω)) := by
  set l2 := lam2 σ β κ
  have h0 := (lam2_pos ha hβ).le
  have h1 := lam2_lt_one ha hβ
  have hs1 := 𝔼.forwardSeries_summable h0 h1 hib (t + 1) ω
  have hb : ∀ k ω', |l2 ^ k * 𝔼.E (t + 1) (i (t + 1 + k)) ω'| ≤ l2 ^ k * Mi := fun k ω' => by
    rw [abs_mul, abs_of_nonneg (pow_nonneg h0 k)]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hib _) _ ω') (pow_nonneg h0 k)
  have hEt : 𝔼.E t (𝔼.forwardSeries l2 i (t + 1)) ω =
      ∑' k, l2 ^ k * 𝔼.E t (i (t + 1 + k)) ω := by
    have := 𝔼.E_tsum h0 h1 hb t ω
    unfold ExpectationSystem.forwardSeries
    rw [this]
    refine tsum_congr fun k => ?_
    have : (fun ω' => l2 ^ k * 𝔼.E (t + 1) (i (t + 1 + k)) ω') =
        l2 ^ k • 𝔼.E (t + 1) (i (t + 1 + k)) := rfl
    rw [this, map_smul, 𝔼.tower (Nat.le_succ t)]
    rfl
  have hs2 : Summable (fun k => l2 ^ k * 𝔼.E t (i (t + 1 + k)) ω) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h0 h1).mul_right Mi)
      (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h0 k)]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hib _) t ω) (pow_nonneg h0 k)
  rw [hEt]
  unfold ExpectationSystem.forwardSeries
  have := ((hs1.hasSum.sub hs2.hasSum).mul_left l2)
  refine this.congr_fun fun j => ?_
  ring

/-- Cochrane (2023), p. 120, survey error E26: the printed "we no longer have
`δ_{t+1} ≠ ΔE_{t+1} π_{t+1}`" should read "=": in (5.5), `δ_{t+1} = ΔE_{t+1} π_{t+1}` holds iff
there is no news about future rates, `c λ₂ ΔE_{t+1} F_{t+1} = 0`. -/
theorem delta_eq_innov_iff {σ β κ Mi : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i δ : ℕ → Ω → ℝ}
    {K : Ω → ℝ} (hi : 𝔼.Adapted i) (hib : ∀ t ω, |i t ω| ≤ Mi) (hK : 𝔼.E 0 K = K)
    (hδa : 𝔼.Adapted δ) (hδ : ∀ t, 𝔼.E t (δ (t + 1)) = 0) (t : ℕ) :
    δ (t + 1) = piMA 𝔼 σ β κ i δ K (t + 1) - 𝔼.E t (piMA 𝔼 σ β κ i δ K (t + 1)) ↔
      (coef σ β κ * lam2 σ β κ) • (𝔼.forwardSeries (lam2 σ β κ) i (t + 1) -
        𝔼.E t (𝔼.forwardSeries (lam2 σ β κ) i (t + 1))) = 0 := by
  rw [eq_5_7 𝔼 ha hβ hi hib hK hδa hδ t]
  constructor
  · intro h
    have := congrArg (fun f => f - δ (t + 1)) h
    simpa using this.symm
  · intro h
    rw [h, zero_add]

/-- Cochrane (2023), p. 120, survey error E26, genuine uncertainty: on the two-period coin-flip
tree with i.i.d. rate shocks `i = coinAR1 0` (news about `i_1` arrives at date 1), every
representation (5.5) of an equilibrium has `δ_1 ≠ ΔE_1 π_1`. -/
theorem e26_coin {σ β κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) {δ : ℕ → Bool × Bool → ℝ}
    {K : Bool × Bool → ℝ} (hK : ExpectationsFiniteTree.coinSystem.E 0 K = K)
    (hδa : ExpectationsFiniteTree.coinSystem.Adapted δ)
    (hδ : ∀ t, ExpectationsFiniteTree.coinSystem.E t (δ (t + 1)) = 0) :
    δ 1 ≠ piMA ExpectationsFiniteTree.coinSystem σ β κ (ExpectationsFiniteTree.coinAR1 0) δ K 1
      - ExpectationsFiniteTree.coinSystem.E 0 (piMA ExpectationsFiniteTree.coinSystem σ β κ
        (ExpectationsFiniteTree.coinAR1 0) δ K 1) := by
  set 𝔼c := ExpectationsFiniteTree.coinSystem
  set i := ExpectationsFiniteTree.coinAR1 0
  have ha := mul_pos hσ hκ
  have har := ExpectationsFiniteTree.coinAR1_isAR1 0
  have hib : ∀ t ω, |i t ω| ≤ 1 := by
    intro t ω
    cases t with
    | zero => simp [i, ExpectationsFiniteTree.coinAR1]
    | succ t =>
      simp only [i, ExpectationsFiniteTree.coinAR1, zero_mul, zero_add,
        ExpectationsFiniteTree.coinShock]
      split_ifs <;> norm_num
  have hE1 : ∀ t, 𝔼c.E t (i (t + 1)) = 0 := fun t => by
    rw [har.2 t, zero_smul]
  have hF : 𝔼c.forwardSeries (lam2 σ β κ) i = i := by
    refine (𝔼c.eq_forwardSeries (lam2_pos ha hβ).le (lam2_lt_one ha hβ) hib har.1
      (fun t => ?_) ⟨1, hib⟩).symm
    rw [hE1 t, smul_zero, zero_add]
  intro h
  have h2 := (delta_eq_innov_iff 𝔼c ha hβ har.1 hib hK hδa hδ 0).mp h
  rw [hF, hE1 0, sub_zero] at h2
  have h3 := congrFun h2 (true, true)
  have hc : 0 < coef σ β κ := div_pos ha (sub_pos.mpr (lam2_lt_lam1 ha hβ))
  have hi1 : i 1 (true, true) = 1 := (ExpectationsFiniteTree.coinAR1_nondegenerate 0).1
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hi1, mul_one] at h3
  exact (mul_pos hc (lam2_pos ha hβ)).ne' h3

/-! ### (5.14): output -/

/-- Cochrane (2023), eq. (5.14), p. 121, and A1 §1.7, p. 571: for `π = piMA K δ`,
`π_t − β E_t π_{t+1} = c[(1 − βλ₁⁻¹) B_t + (1 − βλ₂⁻¹) λ₂ F_t] + (1 − βλ₁⁻¹)(D_t + λ₁·λ₁^{−t}K)`
(written with `(1 − βλ₂⁻¹)λ₂ = λ₂ − β`, `(1 − βλ₁⁻¹)λ₁ = λ₁ − β`); with (5.2) this is `κ x_t`. -/
theorem eq_5_14 {σ β κ Mi : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i δ : ℕ → Ω → ℝ}
    {K : Ω → ℝ} (hi : 𝔼.Adapted i) (hib : ∀ t ω, |i t ω| ≤ Mi) (hK : 𝔼.E 0 K = K)
    (hδa : 𝔼.Adapted δ) (hδ : ∀ t, 𝔼.E t (δ (t + 1)) = 0) (t : ℕ) :
    piMA 𝔼 σ β κ i δ K t - β • 𝔼.E t (piMA 𝔼 σ β κ i δ K (t + 1)) =
      coef σ β κ • ((1 - β * (lam1 σ β κ)⁻¹) • bsum (lam1 σ β κ)⁻¹ i t +
        (lam2 σ β κ - β) • 𝔼.forwardSeries (lam2 σ β κ) i t) +
      (1 - β * (lam1 σ β κ)⁻¹) • bsum (lam1 σ β κ)⁻¹ (fun s => δ (s + 1)) t +
      ((lam1 σ β κ - β) * (lam1 σ β κ)⁻¹ ^ t) • K := by
  rw [piMA_E_succ 𝔼 ha hβ hi hib hK hδa hδ t]
  funext ω
  unfold piMA
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  ring

/-- Cochrane (2023), eq. (5.14), p. 121, printed form: if `(x, π)` satisfy (5.2) and
`π = piMA K δ`, then `κ x_{t+1} = c[(1 − βλ₁⁻¹) ∑_{j=0}^{t} λ₁^{−j} i_{t−j}
  + (1 − βλ₂⁻¹) ∑_{j≥1} λ₂ʲ E_{t+1} i_{t+j}] + (1 − βλ₁⁻¹)[∑_{j=0}^{t} λ₁^{−j} δ_{t+1−j}
  + λ₁^{−t} K]`. -/
theorem eq_5_14_sum {σ β κ Mi : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i δ x : ℕ → Ω → ℝ}
    {K : Ω → ℝ} (hi : 𝔼.Adapted i) (hib : ∀ t ω, |i t ω| ≤ Mi) (hK : 𝔼.E 0 K = K)
    (hδa : 𝔼.Adapted δ) (hδ : ∀ t, 𝔼.E t (δ (t + 1)) = 0)
    (hpc : PC 𝔼 β κ x (piMA 𝔼 σ β κ i δ K)) (t : ℕ) (ω : Ω) :
    κ * x (t + 1) ω = coef σ β κ *
      ((1 - β * (lam1 σ β κ)⁻¹) * ∑ j ∈ Finset.range (t + 1), (lam1 σ β κ)⁻¹ ^ j * i (t - j) ω +
        (1 - β * (lam2 σ β κ)⁻¹) *
          ∑' j : ℕ, lam2 σ β κ ^ (j + 1) * 𝔼.E (t + 1) (i (t + 1 + j)) ω) +
      (1 - β * (lam1 σ β κ)⁻¹) *
        (∑ j ∈ Finset.range (t + 1), (lam1 σ β κ)⁻¹ ^ j * δ (t + 1 - j) ω +
          (lam1 σ β κ)⁻¹ ^ t * K ω) := by
  have h14 := congrFun (eq_5_14 𝔼 ha hβ hi hib hK hδa hδ (t + 1)) ω
  have hpcω := congrFun (hpc (t + 1)) ω
  obtain ⟨_, h55⟩ := eq_5_5_sum 𝔼 ha hβ (δ := δ) K hib t ω
  have hl0 : lam1 σ β κ ≠ 0 := (lam1_pos ha hβ).ne'
  have hl2 : lam2 σ β κ ≠ 0 := (lam2_pos ha hβ).ne'
  have hF : lam2 σ β κ * 𝔼.forwardSeries (lam2 σ β κ) i (t + 1) ω =
      ∑' j : ℕ, lam2 σ β κ ^ (j + 1) * 𝔼.E (t + 1) (i (t + 1 + j)) ω := by
    unfold ExpectationSystem.forwardSeries
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by ring
  have hB := bsum_succ_eq_sum (lam1 σ β κ)⁻¹ i t
  have hD := bsum_succ_eq_sum (lam1 σ β κ)⁻¹ (fun s => δ (s + 1)) t
  have hδs : ∑ j ∈ Finset.range (t + 1), (lam1 σ β κ)⁻¹ ^ j * δ (t - j + 1) ω =
      ∑ j ∈ Finset.range (t + 1), (lam1 σ β κ)⁻¹ ^ j * δ (t + 1 - j) ω := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    congr 3
    omega
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h14 hpcω
  rw [hB, hD] at h14
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h14
  rw [← hδs, ← hF]
  have hk : κ * x (t + 1) ω = piMA 𝔼 σ β κ i δ K (t + 1) ω -
      β * 𝔼.E (t + 1) (piMA 𝔼 σ β κ i δ K (t + 1 + 1)) ω := by linarith
  rw [hk, h14]
  have hq1 : lam1 σ β κ * (lam1 σ β κ)⁻¹ = 1 := mul_inv_cancel₀ hl0
  have hq2 : lam2 σ β κ * (lam2 σ β κ)⁻¹ = 1 := mul_inv_cancel₀ hl2
  linear_combination (coef σ β κ * β * 𝔼.forwardSeries (lam2 σ β κ) i (t + 1) ω) * hq2 +
    ((lam1 σ β κ)⁻¹ ^ t * K ω) * hq1

/-! ### (5.9)–(5.10): the flexible-price model and §5.1.3 -/

/-- Cochrane (2023), eqs. (5.9)–(5.10), p. 120: the flexible-price "IS" equation
`i_t = E_t π_{t+1}` holds iff `π_{t+1} = i_t + δ_{t+1}` for some `δ` with `E_t δ_{t+1} = 0`. -/
theorem flex_iff {i π : ℕ → Ω → ℝ} (hi : 𝔼.Adapted i) :
    (∀ t, i t = 𝔼.E t (π (t + 1))) ↔
      ∃ δ : ℕ → Ω → ℝ, (∀ t, 𝔼.E t (δ (t + 1)) = 0) ∧ ∀ t, π (t + 1) = i t + δ (t + 1) := by
  constructor
  · intro h
    refine ⟨fun s => π s - i (s - 1), fun t => ?_, fun t => ?_⟩
    · simp only [Nat.add_sub_cancel]
      rw [map_sub, ← h t, hi t, sub_self]
    · simp only [Nat.add_sub_cancel]
      abel
  · rintro ⟨δ, hδ, h⟩ t
    rw [h t, map_add, hi t, hδ t, add_zero]

/-- Cochrane (2023), §5.1.3, p. 126: in the flexible-price model `E_t i_{t+j} = E_t π_{t+j+1}`
for all `j` — any dynamics of inflation are those of expected interest rates. -/
theorem flex_no_dynamics {i π : ℕ → Ω → ℝ} (h : ∀ t, i t = 𝔼.E t (π (t + 1))) (t j : ℕ) :
    𝔼.E t (i (t + j)) = 𝔼.E t (π (t + j + 1)) := by
  rw [h (t + j), 𝔼.tower (Nat.le_add_right t j)]

/-! ### Anticipated rate rises (Fig. 5.2, p. 124; survey error E30, p. 129) -/

/-- Cochrane (2023), Fig. 5.2, p. 124, and survey error E30 (p. 129): for a rate rise announced
in advance (`i_t = 1` from date `S + 1` on, `0` before, known to everyone), in **every** bounded
sticky-price equilibrium inflation moves no later than the period before the rise:
`π_S` and `π_{S+1}` are not both zero. So "inflation rises one period after the interest-rate
rise" (p. 129) is false with sticky prices. -/
theorem anticipated_moves_before [Nonempty Ω] {σ β κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (S : ℕ) {x π : ℕ → Ω → ℝ} (hπb : BoundedProc π)
    (h : NK 𝔼 σ β κ (fun t _ => if S + 1 ≤ t then 1 else 0) x π) :
    ¬ (π S = 0 ∧ π (S + 1) = 0) := by
  have ha := mul_pos hσ hκ
  set i : ℕ → Ω → ℝ := fun t _ => if S + 1 ≤ t then 1 else 0 with hidef
  have hi : 𝔼.Adapted i := fun t => 𝔼.const t _
  have hib : ∀ t ω, |i t ω| ≤ 1 := fun t ω => by
    simp only [hidef]; split_ifs <;> norm_num
  obtain ⟨_, hf⟩ := (nk_iff_factor 𝔼 hσ hκ hβ hi hib hπb).mp h
  rintro ⟨h0, h1⟩
  have hS := hf S
  rw [h0, h1, map_zero, smul_zero, sub_zero] at hS
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have hFω := congrFun hS ω
  simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at hFω
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hterm : ∀ k, lam2 σ β κ ^ k * 𝔼.E S (i (S + k)) ω =
      lam2 σ β κ ^ k * (if S + 1 ≤ S + k then 1 else 0) := fun k => by
    rw [show i (S + k) = fun _ => (if S + 1 ≤ S + k then (1 : ℝ) else 0) from rfl, 𝔼.const]
  have hpos : 0 < 𝔼.forwardSeries (lam2 σ β κ) i S ω := by
    unfold ExpectationSystem.forwardSeries
    simp_rw [hterm]
    refine Summable.tsum_pos ?_ (fun k => ?_) 1 (by simp [h2])
    · refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
        (summable_geometric_of_lt_one h2.le h21)
      · split_ifs <;> simp [pow_nonneg h2.le]
      · split_ifs <;> simp [pow_nonneg h2.le]
    · split_ifs <;> simp [pow_nonneg h2.le]
  nlinarith

/-- Cochrane (2023), p. 129 (the case where the sentence is right): with flexible prices,
`i_t = E_t π_{t+1}`, the path with inflation zero through date `S + 1` and one from date `S + 2`
on — one period after the rise — is an equilibrium of the announced rise. -/
theorem flex_one_period_after (S : ℕ) :
    ∀ t, (fun t (_ : Ω) => if S + 1 ≤ t then (1 : ℝ) else 0) t =
      𝔼.E t ((fun t (_ : Ω) => if S + 2 ≤ t then (1 : ℝ) else 0) (t + 1)) := by
  intro t
  rw [𝔼.const]
  funext _
  simp only [show (S + 2 ≤ t + 1) ↔ (S + 1 ≤ t) by omega]

end Cochrane.StickyPriceFiscal.TwoSidedMA
