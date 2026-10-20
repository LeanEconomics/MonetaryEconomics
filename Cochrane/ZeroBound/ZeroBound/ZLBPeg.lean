/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.ForwardSolution
import ZeroBound.ExpectationsFiniteTree
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The new-Keynesian model at an interest-rate peg: the zero bound

Cochrane (2023), Chapter 20, §20.1, pp. 465–469.

At the zero bound the nominal rate is pegged, `i_t = ī` (`ī = 0` at the bound). The book's three
claims about the standard new-Keynesian model (5.1)–(5.2), p. 118, at a peg are made precise here
for an arbitrary `ExpectationSystem` (so under perfect foresight and under uncertainty):

* p. 467, "stable": the two roots (5.6), p. 119, straddle the unit circle, `λ₂ < 1 < λ₁`
  (`lam2_lt_one`, `one_lt_lam1`, `pegMatrix_roots`); every bounded equilibrium converges in
  expectation to the steady state `π = ī` (`peg_expected_converges`).
* p. 467, "indeterminate": the backward matrix fails Schur–Cohn (`peg_not_schurStable`), so the
  system is not determinate (`peg_not_determinate`). Exact characterisation of all bounded
  equilibria (`peg_equilibrium_iff`, `peg_equilibrium_char`): the unstable combination
  `κx_t + (λ₂ − 1)π_t` is pinned (`peg_slaving`), and `p_t = π_t − ī` is ANY bounded solution
  of `p_t = λ₁ E_t p_{t+1}` — a sunspot recursion `p_{t+1} = λ₁⁻¹p_t + δ_{t+1}` driven by an
  arbitrary bounded martingale difference `δ` (`sunspot_equilibrium`, `sunspot_innovation`);
  uncountably many equilibria (`peg_continuum`) and a genuinely random sunspot on a coin-flip
  tree (`coin_sunspot_equilibrium`).
* p. 469, "add active fiscal policy, and inflation can be stable, determinate and quiet at the
  zero bound": with the linearised valuation equation (5.13), p. 121, at a constant interest
  rate, `ΔE_{t+1} ∑ ρʲ π_{t+1+j} = −ε_{t+1}` (genuine `HasSum`), there is exactly one bounded
  equilibrium (`fiscal_selects`); its unexpected inflation is pinned by fiscal news
  (`fiscal_unexpected_inflation`), it is stable (`fiscal_stable`), quiet without fiscal news
  (`fiscal_quiet`), and a date-0 deflation requires a fiscal contraction
  (`deflation_iff_fiscal_contraction`).
-/

namespace Cochrane.ZeroBound.ZLBPeg

open Filter Topology
open Cochrane.ZeroBound

/-! ## The roots (5.6) -/

/-- Cochrane (2023), eq. (5.6), p. 119: the larger root `λ₁`; the discriminant
`(1 + β + σκ)² − 4β` is the core `discQ` of trace `1 + β + σκ` and determinant `β`. -/
noncomputable def lam1 (β σ κ : ℝ) : ℝ :=
  ((1 + β + σ * κ) + Real.sqrt (discQ (1 + β + σ * κ) β)) / 2

/-- Cochrane (2023), eq. (5.6), p. 119: the smaller root `λ₂`. -/
noncomputable def lam2 (β σ κ : ℝ) : ℝ :=
  ((1 + β + σ * κ) - Real.sqrt (discQ (1 + β + σ * κ) β)) / 2

/-- Cochrane (2023), eq. (5.6), p. 119: the discriminant `(1 + β + σκ)² − 4β` is positive
(`β > 0`, `σκ > 0`). -/
theorem disc_pos {β σ κ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) : 0 < discQ (1 + β + σ * κ) β := by
  unfold discQ
  nlinarith [sq_nonneg (1 - β), mul_pos hσκ hβ, sq_nonneg (σ * κ)]

/-- Cochrane (2023), eq. (5.6), p. 119: `λ₁ + λ₂ = 1 + β + σκ`. -/
theorem lam_add (β σ κ : ℝ) : lam1 β σ κ + lam2 β σ κ = 1 + β + σ * κ := by
  unfold lam1 lam2
  ring

/-- Cochrane (2023), eq. (5.6), p. 119: `λ₁λ₂ = β`. -/
theorem lam_mul {β σ κ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) : lam1 β σ κ * lam2 β σ κ = β := by
  have hs : Real.sqrt (discQ (1 + β + σ * κ) β) ^ 2 = (1 + β + σ * κ) ^ 2 - 4 * β :=
    Real.sq_sqrt (disc_pos hβ hσκ).le
  unfold lam1 lam2
  linear_combination (-1 / 4 : ℝ) * hs

/-- Cochrane (2023), eq. (5.6), p. 119: both roots solve `λ² − (1 + β + σκ)λ + β = 0`. -/
theorem lam_root {β σ κ lam : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ)
    (h : lam = lam1 β σ κ ∨ lam = lam2 β σ κ) : lam ^ 2 - (1 + β + σ * κ) * lam + β = 0 := by
  have ha := lam_add β σ κ
  have hm := lam_mul hβ hσκ
  rcases h with rfl | rfl
  · linear_combination lam1 β σ κ * ha - hm
  · linear_combination lam2 β σ κ * ha - hm

/-- Cochrane (2023), eq. (5.6), p. 119: `λ₂ ≤ λ₁`. -/
theorem lam2_le_lam1 (β σ κ : ℝ) : lam2 β σ κ ≤ lam1 β σ κ := by
  unfold lam1 lam2
  linarith [Real.sqrt_nonneg (discQ (1 + β + σ * κ) β)]

/-- Cochrane (2023), p. 119 ("`λ₁ > 1`"): the larger root lies outside the unit circle. -/
theorem one_lt_lam1 {β σ κ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) : 1 < lam1 β σ κ := by
  have h1 := lam_add β σ κ
  have h2 := lam_mul hβ hσκ
  have h3 := lam2_le_lam1 β σ κ
  by_contra h
  push Not at h
  nlinarith

/-- Cochrane (2023), p. 119 ("`λ₂ < 1`"): the smaller root lies inside the unit circle. -/
theorem lam2_lt_one {β σ κ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) : lam2 β σ κ < 1 := by
  have h1 := lam_add β σ κ
  have h2 := lam_mul hβ hσκ
  have h3 := one_lt_lam1 hβ hσκ
  nlinarith

/-- Cochrane (2023), eq. (5.6), p. 119: `λ₂ > 0`. -/
theorem lam2_pos {β σ κ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) : 0 < lam2 β σ κ := by
  have h2 := lam_mul hβ hσκ
  have h3 := one_lt_lam1 hβ hσκ
  nlinarith

/-! ## The matrix form and indeterminacy -/

/-- Cochrane (2023), eqs. (5.1)–(5.2), p. 118, at a peg: the backward form
`(x_t, π_t) = A E_t (x_{t+1}, π_{t+1}) + w` has `A = [[1, σ], [κ, β + σκ]]`. -/
def pegMatrix (β σ κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, σ; κ, β + σ * κ]

/-- Cochrane (2023), eqs. (5.1)–(5.2), p. 118: the constant forcing `w = (−σī, −κσī)` of the
backward form at the peg `i_t = ī`. -/
def pegForcing {Ω : Type*} (σ κ ibar : ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun _ => ![fun _ => -(σ * ibar), fun _ => -(κ * σ * ibar)]

/-- Cochrane (2023), eq. (5.6), p. 119: trace `1 + β + σκ` and determinant `β` of the peg
matrix, so its characteristic polynomial is the quadratic of (5.6). -/
theorem pegMatrix_tr_det (β σ κ : ℝ) :
    tr2 (pegMatrix β σ κ) = 1 + β + σ * κ ∧ det2 (pegMatrix β σ κ) = β := by
  simp only [tr2, det2, pegMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  constructor <;> ring

/-- Cochrane (2023), eq. (5.6), p. 119: the eigenvalues of the peg matrix are `λ₁` and `λ₂`,
and they straddle the unit circle (`‖λ₂‖ < 1 < ‖λ₁‖`), p. 467. -/
theorem pegMatrix_roots {β σ κ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) :
    root₁ (tr2 (pegMatrix β σ κ)) (det2 (pegMatrix β σ κ)) = (lam1 β σ κ : ℂ) ∧
      root₂ (tr2 (pegMatrix β σ κ)) (det2 (pegMatrix β σ κ)) = (lam2 β σ κ : ℂ) ∧
      ‖root₂ (tr2 (pegMatrix β σ κ)) (det2 (pegMatrix β σ κ))‖ < 1 ∧
      1 < ‖root₁ (tr2 (pegMatrix β σ κ)) (det2 (pegMatrix β σ κ))‖ := by
  obtain ⟨ht, hd⟩ := pegMatrix_tr_det β σ κ
  have h0 : 0 ≤ discQ (1 + β + σ * κ) β := (disc_pos hβ hσκ).le
  have e1 : root₁ (tr2 (pegMatrix β σ κ)) (det2 (pegMatrix β σ κ)) = (lam1 β σ κ : ℂ) := by
    rw [ht, hd]
    unfold root₁
    simp only [h0, ↓reduceIte, lam1]
  have e2 : root₂ (tr2 (pegMatrix β σ κ)) (det2 (pegMatrix β σ κ)) = (lam2 β σ κ : ℂ) := by
    rw [ht, hd]
    unfold root₂
    simp only [h0, ↓reduceIte, lam2]
  refine ⟨e1, e2, ?_, ?_⟩
  · rw [e2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lam2_pos hβ hσκ)]
    exact lam2_lt_one hβ hσκ
  · rw [e1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (lt_trans one_pos (one_lt_lam1 hβ hσκ))]
    exact one_lt_lam1 hβ hσκ

/-- Cochrane (2023), §20.1, p. 467: the peg matrix fails the Schur–Cohn condition. -/
theorem peg_not_schurStable {β σ κ : ℝ} (hσκ : 0 < σ * κ) :
    ¬ SchurStable (tr2 (pegMatrix β σ κ)) (det2 (pegMatrix β σ κ)) := by
  obtain ⟨ht, hd⟩ := pegMatrix_tr_det β σ κ
  rw [ht, hd]
  rintro ⟨-, h⟩
  have := le_abs_self (1 + β + σ * κ)
  linarith

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), eqs. (5.1)–(5.2), p. 118, with `i_t = ī` (§20.1, p. 467): the IS curve
`x_t = E_t x_{t+1} − σ(ī − E_t π_{t+1})` and the Phillips curve `π_t = βE_tπ_{t+1} + κx_t`, at
every date and state. -/
def PegEq (β σ κ ibar : ℝ) (x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, x t ω = 𝔼.E t (x (t + 1)) ω - σ * (ibar - 𝔼.E t (π (t + 1)) ω) ∧
    π t ω = β * 𝔼.E t (π (t + 1)) ω + κ * x t ω

/-- Cochrane (2023), (5.1)–(5.2), p. 118: `E_t` of an affine combination. -/
theorem E_affine2 (t : ℕ) (a b c : ℝ) (y z : Ω → ℝ) (ω : Ω) :
    𝔼.E t (fun ω => a * y ω + b * z ω + c) ω = a * 𝔼.E t y ω + b * 𝔼.E t z ω + c := by
  have h : (fun ω => a * y ω + b * z ω + c) = a • y + b • z + fun _ => c := by
    funext ω
    simp
  rw [h, map_add, map_add, map_smul, map_smul, 𝔼.const]
  simp

/-- Cochrane (2023), (5.1)–(5.2), p. 118: the model at a peg is the backward system
`z_t = A E_t z_{t+1} + w` of the core module with `A = pegMatrix`. -/
theorem pegEq_iff_solves (β σ κ ibar : ℝ) (x π : ℕ → Ω → ℝ) :
    PegEq 𝔼 β σ κ ibar x π ↔
      𝔼.Solves (pegMatrix β σ κ) (pegForcing σ κ ibar) (fun t => ![x t, π t]) := by
  constructor
  · intro h t i
    fin_cases i
    · funext ω
      obtain ⟨h1, -⟩ := h t ω
      simp [pegMatrix, pegForcing]
      linarith
    · funext ω
      obtain ⟨h1, h2⟩ := h t ω
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val', Matrix.cons_val_fin_one,
        Matrix.cons_val_one, pegMatrix, Matrix.of_apply, Matrix.cons_val_zero, pegForcing,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [h2, h1]
      ring
  · intro h t ω
    have h0 := congrFun (h t 0) ω
    have h1 := congrFun (h t 1) ω
    simp only [Fin.isValue, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero,
      pegMatrix, Matrix.of_apply, one_smul, Matrix.cons_val_one, pegForcing, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] at h0 h1
    refine ⟨by linarith, ?_⟩
    rw [h1, h0]
    ring

/-- Cochrane (2023), §20.1, p. 467 ("off-the-shelf new-Keynesian models predict that inflation
is indeterminate at the zero bound"): the peg system is not determinate. -/
theorem peg_not_determinate [Nonempty Ω] {β σ κ : ℝ} (hσκ : 0 < σ * κ) :
    ¬ 𝔼.Determinate (pegMatrix β σ κ) :=
  fun h => peg_not_schurStable hσκ ((𝔼.determinate_iff _).mp h)

/-- Cochrane (2023), §20.1, p. 467: the steady state at the peg, `π = ī`,
`x = (1 − β)ī/κ`. -/
theorem peg_steady {β σ κ : ℝ} (hκ : κ ≠ 0) (ibar : ℝ) :
    PegEq 𝔼 β σ κ ibar (fun _ _ => (1 - β) * ibar / κ) (fun _ _ => ibar) := by
  intro t ω
  simp only [𝔼.const]
  constructor
  · ring
  · field_simp
    ring

/-! ## All bounded equilibria at the peg -/

/-- Cochrane (2023), §20.1, p. 467: the combination `q_t = κx_t + (λ − 1)π_t + (β − λ)ī`
attached to a root `λ` of (5.6). -/
def pegQ (β κ ibar lam : ℝ) (x π : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => κ * x t ω + (lam - 1) * π t ω + (β - lam) * ibar

/-- Cochrane (2023), §20.1, p. 467, eq. (5.6): for a root `λ`, `q_t = λ E_t q_{t+1}`. -/
theorem peg_q_step {β σ κ ibar lam : ℝ} (hlam : lam ^ 2 - (1 + β + σ * κ) * lam + β = 0)
    {x π : ℕ → Ω → ℝ} (h : PegEq 𝔼 β σ κ ibar x π) (t : ℕ) :
    pegQ β κ ibar lam x π t = lam • 𝔼.E t (pegQ β κ ibar lam x π (t + 1)) := by
  funext ω
  obtain ⟨h1, h2⟩ := h t ω
  rw [show pegQ β κ ibar lam x π (t + 1) = fun ω => κ * x (t + 1) ω + (lam - 1) * π (t + 1) ω +
    (β - lam) * ibar from rfl, Pi.smul_apply, smul_eq_mul, E_affine2]
  simp only [pegQ]
  linear_combination (lam - 1) * h2 + lam * κ * h1 +
    (ibar - 𝔼.E t (π (t + 1)) ω) * hlam

/-- Cochrane (2023), §20.1, p. 467: in a bounded equilibrium the unstable combination is
pinned, `κx_t + (λ₂ − 1)π_t = (λ₂ − β)ī`. -/
theorem peg_slaving {β σ κ ibar : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) {x π : ℕ → Ω → ℝ}
    (hbx : BoundedProc x) (hbπ : BoundedProc π) (h : PegEq 𝔼 β σ κ ibar x π) (t : ℕ) (ω : Ω) :
    κ * x t ω + (lam2 β σ κ - 1) * π t ω = (lam2 β σ κ - β) * ibar := by
  set l := lam2 β σ κ
  have hl : |l| < 1 := by
    rw [abs_lt]
    constructor <;> linarith [lam2_pos hβ hσκ, lam2_lt_one hβ hσκ]
  obtain ⟨M1, hM1⟩ := hbx
  obtain ⟨M2, hM2⟩ := hbπ
  have hq : BoundedProc (pegQ β κ ibar l x π) := by
    refine ⟨|κ| * M1 + |l - 1| * M2 + |(β - l) * ibar|, fun t ω => ?_⟩
    simp only [pegQ]
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) le_rfl)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM1 t ω) (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM2 t ω) (abs_nonneg _)
  have h0 := 𝔼.forward_unique (u := 0) (z₁ := pegQ β κ ibar l x π) (z₂ := 0) hl
    (fun t => by
      rw [Pi.zero_apply, add_zero]
      exact peg_q_step 𝔼 (lam_root hβ hσκ (Or.inr rfl)) h t)
    (fun t => by simp) hq ⟨0, fun _ _ => by simp⟩
  have := congrFun (congrFun h0 t) ω
  simp only [pegQ, Pi.zero_apply] at this
  linarith

/-- Cochrane (2023), §20.1, p. 467: in a bounded equilibrium inflation deviations obey
`π_t − ī = λ₁(E_tπ_{t+1} − ī)`, i.e. `E_t(π_{t+1} − ī) = λ₁⁻¹(π_t − ī)`: stable forward. -/
theorem peg_pi_rec {β σ κ ibar : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) {x π : ℕ → Ω → ℝ}
    (hbx : BoundedProc x) (hbπ : BoundedProc π) (h : PegEq 𝔼 β σ κ ibar x π) (t : ℕ) (ω : Ω) :
    π t ω - ibar = lam1 β σ κ * (𝔼.E t (π (t + 1)) ω - ibar) := by
  have hs := peg_slaving 𝔼 hβ hσκ hbx hbπ h t ω
  obtain ⟨-, h2⟩ := h t ω
  have hm := lam_mul hβ hσκ
  have hp := lam2_pos hβ hσκ
  have key : lam2 β σ κ * ((π t ω - ibar) - lam1 β σ κ * (𝔼.E t (π (t + 1)) ω - ibar)) = 0 := by
    linear_combination h2 + hs - (𝔼.E t (π (t + 1)) ω - ibar) * hm
  rcases mul_eq_zero.mp key with h' | h'
  · linarith
  · linarith

/-- Cochrane (2023), §20.1, p. 467 (converse): the slaving relation and the stable recursion
imply the model equations (no boundedness needed). -/
theorem pegEq_of_slaving {β σ κ ibar : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) (hκ : κ ≠ 0)
    {x π : ℕ → Ω → ℝ}
    (hs : ∀ t ω, κ * x t ω + (lam2 β σ κ - 1) * π t ω = (lam2 β σ κ - β) * ibar)
    (hr : ∀ t ω, π t ω - ibar = lam1 β σ κ * (𝔼.E t (π (t + 1)) ω - ibar)) :
    PegEq 𝔼 β σ κ ibar x π := by
  intro t ω
  have hx : x (t + 1) = fun ω => (-(lam2 β σ κ - 1) / κ) * π (t + 1) ω + 0 * π (t + 1) ω +
      (lam2 β σ κ - β) * ibar / κ := by
    funext ω
    have := hs (t + 1) ω
    field_simp
    linarith
  have hEx : 𝔼.E t (x (t + 1)) ω = (-(lam2 β σ κ - 1) / κ) * 𝔼.E t (π (t + 1)) ω +
      (lam2 β σ κ - β) * ibar / κ := by
    rw [hx, E_affine2]
    ring
  have hm := lam_mul hβ hσκ
  have ha := lam_add β σ κ
  have h1 := hs t ω
  have h2 := hr t ω
  have hEx' : κ * 𝔼.E t (x (t + 1)) ω = -(lam2 β σ κ - 1) * 𝔼.E t (π (t + 1)) ω +
      (lam2 β σ κ - β) * ibar := by
    rw [hEx]
    field_simp
  constructor
  · apply mul_left_cancel₀ hκ
    linear_combination h1 - hEx' - (lam2 β σ κ - 1) * h2 +
      (𝔼.E t (π (t + 1)) ω - ibar) * (ha - hm)
  · linear_combination -h1 + lam2 β σ κ * h2 + (𝔼.E t (π (t + 1)) ω - ibar) * hm

/-- Cochrane (2023), §20.1, p. 467: a bounded pair `(x, π)` is an equilibrium at the peg iff
the unstable combination is pinned and `π − ī` follows the stable recursion. -/
theorem peg_equilibrium_iff {β σ κ ibar : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) (hκ : κ ≠ 0)
    {x π : ℕ → Ω → ℝ} (hbx : BoundedProc x) (hbπ : BoundedProc π) :
    PegEq 𝔼 β σ κ ibar x π ↔
      (∀ t ω, κ * x t ω + (lam2 β σ κ - 1) * π t ω = (lam2 β σ κ - β) * ibar) ∧
        ∀ t ω, π t ω - ibar = lam1 β σ κ * (𝔼.E t (π (t + 1)) ω - ibar) :=
  ⟨fun h => ⟨peg_slaving 𝔼 hβ hσκ hbx hbπ h, peg_pi_rec 𝔼 hβ hσκ hbx hbπ h⟩,
    fun h => pegEq_of_slaving 𝔼 hβ hσκ hκ h.1 h.2⟩

/-- Cochrane (2023), §20.1, p. 467: the inflation path `π_t = ī + p_t`. -/
def pegPi (ibar : ℝ) (p : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t ω => ibar + p t ω

/-- Cochrane (2023), §20.1, p. 467: the output path `x_t = ((1 − β)ī + (1 − λ₂)p_t)/κ`. -/
noncomputable def pegX (β σ κ ibar : ℝ) (p : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => ((1 - β) * ibar + (1 - lam2 β σ κ) * p t ω) / κ

/-- Cochrane (2023), §20.1, p. 467: `E_s π_t = ī + E_s p_t`. -/
theorem E_pegPi (s t : ℕ) (ibar : ℝ) (p : ℕ → Ω → ℝ) (ω : Ω) :
    𝔼.E s (pegPi ibar p t) ω = ibar + 𝔼.E s (p t) ω := by
  have h := E_affine2 𝔼 s 1 0 ibar (p t) (p t) ω
  have e : (fun ω => 1 * p t ω + 0 * p t ω + ibar) = pegPi ibar p t := by
    funext ω
    simp [pegPi]
    ring
  rw [e] at h
  rw [h]
  ring

/-- Cochrane (2023), §20.1, p. 467: every solution of `p_t = λ₁ E_t p_{t+1}` gives an
equilibrium at the peg. -/
theorem pegEq_of_sunspot {β σ κ ibar : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) (hκ : κ ≠ 0)
    {p : ℕ → Ω → ℝ} (hp : ForwardSolution.Solves 𝔼 (lam1 β σ κ) 0 p) :
    PegEq 𝔼 β σ κ ibar (pegX β σ κ ibar p) (pegPi ibar p) := by
  refine pegEq_of_slaving 𝔼 hβ hσκ hκ (fun t ω => ?_) (fun t ω => ?_)
  · simp only [pegX, pegPi]
    field_simp
    ring
  · rw [E_pegPi]
    have := congrFun (hp t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero] at this
    simp only [pegPi]
    rw [this]
    ring

/-- Cochrane (2023), §20.1, p. 467: every bounded equilibrium is of the form
`π = ī + p`, `x = pegX p` with `p` a bounded solution of `p_t = λ₁E_tp_{t+1}`. -/
theorem peg_equilibrium_char {β σ κ ibar : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) (hκ : κ ≠ 0)
    {x π : ℕ → Ω → ℝ} (hbx : BoundedProc x) (hbπ : BoundedProc π) (h : PegEq 𝔼 β σ κ ibar x π) :
    ∃ p, ForwardSolution.Solves 𝔼 (lam1 β σ κ) 0 p ∧ BoundedProc p ∧
      x = pegX β σ κ ibar p ∧ π = pegPi ibar p := by
  obtain ⟨M, hM⟩ := hbπ
  refine ⟨fun t ω => π t ω - ibar, fun t => ?_, ⟨M + |ibar|, fun t ω => ?_⟩, ?_, ?_⟩
  · funext ω
    have hr := peg_pi_rec 𝔼 hβ hσκ hbx ⟨M, hM⟩ h t ω
    have hE := E_affine2 𝔼 t 1 0 (-ibar) (π (t + 1)) (π (t + 1)) ω
    have e : (fun ω => 1 * π (t + 1) ω + 0 * π (t + 1) ω + -ibar) =
        fun ω => π (t + 1) ω - ibar := by
      funext ω
      ring
    rw [e] at hE
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero]
    rw [hE, hr]
    ring
  · exact (abs_sub _ _).trans (add_le_add (hM t ω) le_rfl)
  · funext t ω
    have hs := peg_slaving 𝔼 hβ hσκ hbx ⟨M, hM⟩ h t ω
    simp only [pegX]
    field_simp
    linarith
  · funext t ω
    simp [pegPi]

/-! ## Sunspots -/

/-- Cochrane (2023), §20.1, p. 467 and Figure 16.2: for any `p₀` known at date 0 and any
bounded martingale-difference sunspot `δ`, the recursion `p_{t+1} = λ₁⁻¹p_t + δ_{t+1}` (core
`sunspotFamily`) gives a bounded adapted equilibrium at the peg. -/
theorem sunspot_equilibrium {β σ κ ibar B Mδ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) (hκ : κ ≠ 0)
    {p0 : Ω → ℝ} {δ : ℕ → Ω → ℝ} (hp0 : 𝔼.E 0 p0 = p0) (hp0b : ∀ ω, |p0 ω| ≤ B)
    (hδa : 𝔼.Adapted δ) (hδb : ∀ t ω, |δ t ω| ≤ Mδ) (hδ : ∀ t, 𝔼.E t (δ (t + 1)) = 0) :
    let p := ForwardSolution.sunspotFamily (lam1 β σ κ) 0 δ p0
    PegEq 𝔼 β σ κ ibar (pegX β σ κ ibar p) (pegPi ibar p) ∧
      𝔼.Adapted (pegX β σ κ ibar p) ∧ 𝔼.Adapted (pegPi ibar p) ∧
      BoundedProc (pegX β σ κ ibar p) ∧ BoundedProc (pegPi ibar p) := by
  intro p
  have hl1 := one_lt_lam1 hβ hσκ
  have hl0 : lam1 β σ κ ≠ 0 := by linarith
  have hua : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => by simp
  have hsol : ForwardSolution.Solves 𝔼 (lam1 β σ κ) 0 p :=
    ForwardSolution.sunspotFamily_solves 𝔼 hl0 hp0 hua hδa hδ
  have hpa : 𝔼.Adapted p := ForwardSolution.sunspotFamily_adapted 𝔼 hp0 hua hδa
  obtain ⟨K, hK⟩ : BoundedProc p :=
    ForwardSolution.sunspotFamily_bounded (by rw [abs_of_pos (by linarith)]; exact hl1) hp0b
      (Mu := 0) (fun _ _ => by simp) hδb
  refine ⟨pegEq_of_sunspot 𝔼 hβ hσκ hκ hsol, fun t => ?_, fun t => ?_, ?_, ?_⟩
  · funext ω
    have e : pegX β σ κ ibar p t =
        fun ω => ((1 - lam2 β σ κ) / κ) * p t ω + 0 * p t ω + (1 - β) * ibar / κ := by
      funext ω
      simp only [pegX]
      field_simp
      ring
    rw [e, E_affine2, hpa t]
  · funext ω
    rw [E_pegPi, hpa t]
    rfl
  · refine ⟨|(1 - β) * ibar / κ| + |(1 - lam2 β σ κ) / κ| * K, fun t ω => ?_⟩
    have e : pegX β σ κ ibar p t ω = (1 - β) * ibar / κ + (1 - lam2 β σ κ) / κ * p t ω := by
      simp only [pegX]
      field_simp
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hK t ω) (abs_nonneg _)
  · exact ⟨|ibar| + K, fun t ω => (abs_add_le _ _).trans (add_le_add le_rfl (hK t ω))⟩

/-- Cochrane (2023), §20.1, p. 467: in the sunspot equilibrium the inflation surprise is the
sunspot, `π_{t+1} − E_tπ_{t+1} = δ_{t+1}`. -/
theorem sunspot_innovation {β σ κ ibar : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ)
    {p0 : Ω → ℝ} {δ : ℕ → Ω → ℝ} (hp0 : 𝔼.E 0 p0 = p0)
    (hδa : 𝔼.Adapted δ) (hδ : ∀ t, 𝔼.E t (δ (t + 1)) = 0) (t : ℕ) (ω : Ω) :
    let p := ForwardSolution.sunspotFamily (lam1 β σ κ) 0 δ p0
    pegPi ibar p (t + 1) ω - 𝔼.E t (pegPi ibar p (t + 1)) ω = δ (t + 1) ω := by
  intro p
  have hl0 : lam1 β σ κ ≠ 0 := by linarith [one_lt_lam1 hβ hσκ]
  have hua : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => by simp
  have hsol : ForwardSolution.Solves 𝔼 (lam1 β σ κ) 0 p :=
    ForwardSolution.sunspotFamily_solves 𝔼 hl0 hp0 hua hδa hδ
  have hs := congrFun (hsol t) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero] at hs
  rw [E_pegPi]
  have hsucc : p (t + 1) ω = (lam1 β σ κ)⁻¹ * (p t ω - 0) + δ (t + 1) ω := by
    simp [p, ForwardSolution.sunspotFamily_succ]
  simp only [pegPi]
  rw [hsucc, hs]
  field_simp
  ring

/-- Cochrane (2023), §20.1, p. 467 ("inflation is stable at the zero bound"): in every bounded
equilibrium, expected inflation converges to the peg, `E_s π_{s+k} → ī` as `k → ∞`. -/
theorem peg_expected_converges {β σ κ ibar : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) (hκ : κ ≠ 0)
    {x π : ℕ → Ω → ℝ} (hπa : 𝔼.Adapted π) (hbx : BoundedProc x) (hbπ : BoundedProc π)
    (h : PegEq 𝔼 β σ κ ibar x π) (s : ℕ) (ω : Ω) :
    Tendsto (fun k => 𝔼.E s (π (s + k)) ω) atTop (𝓝 ibar) := by
  obtain ⟨p, hp, -, -, hπ⟩ := peg_equilibrium_char 𝔼 hβ hσκ hκ hbx hbπ h
  have hl1 := one_lt_lam1 hβ hσκ
  have hl0 : lam1 β σ κ ≠ 0 := by linarith
  have hpa : 𝔼.Adapted p := fun t => by
    funext ω
    have := congrFun (hπa t) ω
    rw [hπ, E_pegPi] at this
    simp only [pegPi] at this
    linarith
  have har : 𝔼.IsAR1 (lam1 β σ κ)⁻¹ p := by
    refine ⟨hpa, fun t => ?_⟩
    funext ω
    have := congrFun (hp t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero] at this
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linarith
  have e : (fun k => 𝔼.E s (π (s + k)) ω) =
      fun k => ibar + (lam1 β σ κ)⁻¹ ^ k * p s ω := by
    funext k
    rw [hπ, E_pegPi, 𝔼.ar1_iterate har s k]
    rfl
  rw [e]
  have h0 : Tendsto (fun k : ℕ => (lam1 β σ κ)⁻¹ ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hl1)
  simpa using (h0.mul_const (p s ω)).const_add ibar

/-- Cochrane (2023), §20.1, p. 467 ("there are many equilibria"): the set of bounded adapted
equilibria at the peg is uncountable. -/
theorem peg_continuum [Nonempty Ω] {β σ κ ibar : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ)
    (hκ : κ ≠ 0) :
    ¬ {z : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) | PegEq 𝔼 β σ κ ibar z.1 z.2 ∧ 𝔼.Adapted z.1 ∧
      𝔼.Adapted z.2 ∧ BoundedProc z.1 ∧ BoundedProc z.2}.Countable := by
  intro hc
  set S := {z : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) | PegEq 𝔼 β σ κ ibar z.1 z.2 ∧ 𝔼.Adapted z.1 ∧
      𝔼.Adapted z.2 ∧ BoundedProc z.1 ∧ BoundedProc z.2} with hS
  let f : ℝ → (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) := fun c =>
    (pegX β σ κ ibar (ForwardSolution.sunspotFamily (lam1 β σ κ) 0 0 (fun _ => c)),
      pegPi ibar (ForwardSolution.sunspotFamily (lam1 β σ κ) 0 0 (fun _ => c)))
  have hmaps : Set.MapsTo f Set.univ S := fun c _ => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := sunspot_equilibrium 𝔼 (ibar := ibar) (B := |c|) (Mδ := 0)
      hβ hσκ hκ (p0 := fun _ => c) (δ := 0) (𝔼.const 0 c) (fun _ => le_rfl)
      (fun t => by simp) (fun _ _ => by simp) (fun t => by simp)
    exact ⟨h1, h2, h3, h4, h5⟩
  have hinj : Set.InjOn f Set.univ := by
    intro c₁ _ c₂ _ h
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun (congrArg Prod.snd h) 0) ω
    simpa [f, pegPi, ForwardSolution.sunspotFamily] using this
  exact Cardinal.not_countable_real (hmaps.countable_of_injOn hinj hc)

/-- Cochrane (2023), §20.1, p. 467 ("the economy can jump between them following sunspots"):
on the coin-flip tree there is a bounded adapted equilibrium at the peg whose date-1 inflation
differs across states, driven by a pure sunspot. -/
theorem coin_sunspot_equilibrium {β σ κ ibar : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ)
    (hκ : κ ≠ 0) :
    ∃ x π : ℕ → Bool × Bool → ℝ, PegEq ExpectationsFiniteTree.coinSystem β σ κ ibar x π ∧
      ExpectationsFiniteTree.coinSystem.Adapted x ∧
      ExpectationsFiniteTree.coinSystem.Adapted π ∧ BoundedProc x ∧ BoundedProc π ∧
      π 1 (true, true) ≠ π 1 (false, true) := by
  set δ := ExpectationsFiniteTree.coinAR1 0
  have har := ExpectationsFiniteTree.coinAR1_isAR1 0
  have hδb : ∀ t ω, |δ t ω| ≤ 1 := by
    intro t ω
    cases t with
    | zero => simp [δ, ExpectationsFiniteTree.coinAR1]
    | succ t =>
      simp only [δ, ExpectationsFiniteTree.coinAR1, zero_mul, zero_add,
        ExpectationsFiniteTree.coinShock]
      split_ifs <;> norm_num
  obtain ⟨h1, h2, h3, h4, h5⟩ := sunspot_equilibrium ExpectationsFiniteTree.coinSystem
    (ibar := ibar) (B := 0) hβ hσκ hκ (p0 := fun _ => 0) (δ := δ)
    (ExpectationsFiniteTree.coinSystem.const 0 0) (fun _ => by simp) har.1 hδb
    (fun t => by rw [har.2 t, zero_smul])
  refine ⟨_, _, h1, h2, h3, h4, h5, ?_⟩
  obtain ⟨n1, n2, -⟩ := ExpectationsFiniteTree.coinAR1_nondegenerate 0
  simp only [pegPi, ForwardSolution.sunspotFamily, Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
    sub_zero, smul_eq_mul, mul_zero, zero_add]
  rw [show δ 1 (true, true) = 1 from n1, show δ 1 (false, true) = -1 from n2]
  norm_num

/-! ## Fiscal theory at the peg -/

/-- Cochrane (2023), eq. (5.13), p. 121, with the interest rate constant at `ī` (one-period
debt): the linearised valuation equation `ΔE_{t+1}∑_{j≥0} ρʲπ_{t+1+j} = −ε_{t+1}`, where
`ε_{t+1} = ΔE_{t+1}∑ρʲs̃_{t+1+j}` is the fiscal news, as a genuine sum (`HasSum`). At date 0 the
economy starts from the steady state (date `−1` expectations `E_{−1}π_j = ī`), so the date-0
news sets `∑ρʲ(E₀π_j − ī) = −ε₀`. -/
def Valuation (ρ ibar : ℝ) (ε π : ℕ → Ω → ℝ) : Prop :=
  (∀ ω, HasSum (fun j => ρ ^ j * (𝔼.E 0 (π j) ω - ibar)) (-ε 0 ω)) ∧
    ∀ t ω, HasSum (fun j => ρ ^ j * (𝔼.E (t + 1) (π (t + 1 + j)) ω - 𝔼.E t (π (t + 1 + j)) ω))
      (-ε (t + 1) ω)

/-- Cochrane (2023), eq. (5.13), p. 121: for `p` with `E_tp_{t+1} = rp_t` and `0 ≤ ρr < 1`,
the date-0 discounted sum equals `p₀/(1 − ρr)`. -/
theorem valuation_sum0 {ρ r ibar : ℝ} (h0 : 0 ≤ ρ * r) (h1 : ρ * r < 1) {p : ℕ → Ω → ℝ}
    (hp : 𝔼.IsAR1 r p) (ω : Ω) :
    HasSum (fun j => ρ ^ j * (𝔼.E 0 (pegPi ibar p j) ω - ibar)) ((1 - ρ * r)⁻¹ * p 0 ω) := by
  have hg := (hasSum_geometric_of_lt_one h0 h1).mul_right (p 0 ω)
  convert hg using 1
  funext j
  rw [E_pegPi]
  have := 𝔼.ar1_iterate hp 0 j
  rw [zero_add] at this
  rw [this, Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

/-- Cochrane (2023), eq. (5.13), p. 121: for `p` with `E_tp_{t+1} = rp_t`, the discounted
revision of expected inflation equals `(p_{t+1} − rp_t)/(1 − ρr)`. -/
theorem valuation_sum {ρ r ibar : ℝ} (h0 : 0 ≤ ρ * r) (h1 : ρ * r < 1) {p : ℕ → Ω → ℝ}
    (hp : 𝔼.IsAR1 r p) (t : ℕ) (ω : Ω) :
    HasSum (fun j => ρ ^ j * (𝔼.E (t + 1) (pegPi ibar p (t + 1 + j)) ω -
      𝔼.E t (pegPi ibar p (t + 1 + j)) ω)) ((1 - ρ * r)⁻¹ * (p (t + 1) ω - r * p t ω)) := by
  have hg := (hasSum_geometric_of_lt_one h0 h1).mul_right (p (t + 1) ω - r * p t ω)
  convert hg using 1
  funext j
  rw [E_pegPi, E_pegPi, 𝔼.ar1_iterate hp (t + 1) j]
  have e := 𝔼.ar1_iterate hp t (1 + j)
  rw [show t + (1 + j) = t + 1 + j by ring] at e
  rw [e]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_pow, pow_add]
  ring

/-- Cochrane (2023), §20.1, p. 469: the fiscal-theory equilibrium inflation deviation,
`p₀ = −kε₀`, `p_{t+1} = λ₁⁻¹p_t − kε_{t+1}`, with `k = 1 − ρ/λ₁`. -/
noncomputable def fiscalP (β σ κ ρ : ℝ) (ε : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  ForwardSolution.sunspotFamily (lam1 β σ κ) 0 (fun t => (-(1 - ρ * (lam1 β σ κ)⁻¹)) • ε t)
    ((-(1 - ρ * (lam1 β σ κ)⁻¹)) • ε 0)

/-- Cochrane (2023), §20.1, p. 469: any bounded equilibrium satisfying the valuation equation
has inflation `ī + fiscalP`. -/
theorem valuation_pins {β σ κ ibar ρ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) (hκ : κ ≠ 0)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {ε x π : ℕ → Ω → ℝ} (hπa : 𝔼.Adapted π)
    (hbx : BoundedProc x) (hbπ : BoundedProc π) (h : PegEq 𝔼 β σ κ ibar x π)
    (hv : Valuation 𝔼 ρ ibar ε π) : π = pegPi ibar (fiscalP β σ κ ρ ε) := by
  obtain ⟨p, hp, -, -, hπ⟩ := peg_equilibrium_char 𝔼 hβ hσκ hκ hbx hbπ h
  have hl1 := one_lt_lam1 hβ hσκ
  have hl0 : lam1 β σ κ ≠ 0 := by linarith
  set r := (lam1 β σ κ)⁻¹ with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hl1
  have h0 : 0 ≤ ρ * r := mul_nonneg hρ0 hr0.le
  have h1 : ρ * r < 1 := by nlinarith
  have hk : 0 < 1 - ρ * r := by linarith
  have hpa : 𝔼.Adapted p := fun t => by
    funext ω
    have := congrFun (hπa t) ω
    rw [hπ, E_pegPi] at this
    simp only [pegPi] at this
    linarith
  have har : 𝔼.IsAR1 r p := by
    refine ⟨hpa, fun t => ?_⟩
    funext ω
    have := congrFun (hp t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero] at this
    simp only [Pi.smul_apply, smul_eq_mul, hr]
    field_simp
    linarith
  rw [hπ] at hv
  have hpeq : p = fiscalP β σ κ ρ ε := by
    funext t ω
    induction t generalizing ω with
    | zero =>
      have := (hv.1 ω).unique (valuation_sum0 𝔼 h0 h1 har ω)
      simp only [fiscalP, ForwardSolution.sunspotFamily, Pi.smul_apply, smul_eq_mul]
      rw [← hr]
      field_simp at this ⊢
      linarith
    | succ t ih =>
      have := (hv.2 t ω).unique (valuation_sum 𝔼 h0 h1 har t ω)
      rw [fiscalP, ForwardSolution.sunspotFamily_succ, ← fiscalP]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, sub_zero,
        smul_eq_mul]
      rw [← ih ω, ← hr]
      field_simp at this ⊢
      linarith
  rw [hπ, hpeq]

/-- Cochrane (2023), §20.1, p. 469 ("Add active fiscal policy to the new-Keynesian model, and
inflation can be stable, determinate, and quiet at the zero bound"): with the valuation equation
(5.13) at the peg, there is exactly one bounded adapted equilibrium, for every bounded adapted
fiscal-news process `ε` (`E_tε_{t+1} = 0`) and every `0 ≤ ρ ≤ 1`. -/
theorem fiscal_selects {β σ κ ibar ρ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) (hκ : κ ≠ 0)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {ε : ℕ → Ω → ℝ} (hεa : 𝔼.Adapted ε) (hεb : BoundedProc ε)
    (hεmd : ∀ t, 𝔼.E t (ε (t + 1)) = 0) :
    ∃! z : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), PegEq 𝔼 β σ κ ibar z.1 z.2 ∧ 𝔼.Adapted z.1 ∧
      𝔼.Adapted z.2 ∧ BoundedProc z.1 ∧ BoundedProc z.2 ∧ Valuation 𝔼 ρ ibar ε z.2 := by
  have hl1 := one_lt_lam1 hβ hσκ
  have hl0 : lam1 β σ κ ≠ 0 := by linarith
  set r := (lam1 β σ κ)⁻¹ with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hl1
  have h0 : 0 ≤ ρ * r := mul_nonneg hρ0 hr0.le
  have h1 : ρ * r < 1 := by nlinarith
  have hk : 0 < 1 - ρ * r := by linarith
  set k := 1 - ρ * r with hkdef
  have hk' : 1 - ρ * r ≠ 0 := by linarith
  obtain ⟨Me, hMe⟩ := hεb
  have hνa : 𝔼.Adapted (fun t => (-k) • ε t) := fun t => by rw [map_smul, hεa t]
  have hν0 : 𝔼.E 0 ((-k) • ε 0) = (-k) • ε 0 := by rw [map_smul, hεa 0]
  have hνmd : ∀ t, 𝔼.E t ((fun t => (-k) • ε t) (t + 1)) = 0 := fun t => by
    simp only [map_smul, hεmd t, smul_zero]
  have hνb : ∀ t ω, |((fun t => (-k) • ε t) t) ω| ≤ k * Me := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg, abs_of_pos hk]
    exact mul_le_mul_of_nonneg_left (hMe t ω) hk.le
  obtain ⟨he1, he2, he3, he4, he5⟩ := sunspot_equilibrium 𝔼 (ibar := ibar) hβ hσκ hκ hν0
    (hνb 0) hνa hνb hνmd
  have hp : fiscalP β σ κ ρ ε = ForwardSolution.sunspotFamily (lam1 β σ κ) 0
      (fun t => (-k) • ε t) ((-k) • ε 0) := rfl
  have hua : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => by simp
  have hsol := ForwardSolution.sunspotFamily_solves 𝔼 hl0 hν0 hua hνa hνmd
  have hpa := ForwardSolution.sunspotFamily_adapted 𝔼 (a := lam1 β σ κ) hν0 hua hνa
  have har : 𝔼.IsAR1 r (fiscalP β σ κ ρ ε) := by
    refine ⟨hpa, fun t => ?_⟩
    funext ω
    have := congrFun (hsol t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero] at this
    simp only [hp, Pi.smul_apply, smul_eq_mul, hr]
    field_simp
    linarith
  have hval : Valuation 𝔼 ρ ibar ε (pegPi ibar (fiscalP β σ κ ρ ε)) := by
    refine ⟨fun ω => ?_, fun t ω => ?_⟩
    · convert valuation_sum0 𝔼 h0 h1 har ω using 1
      simp only [hp, ForwardSolution.sunspotFamily, Pi.smul_apply, smul_eq_mul]
      rw [hkdef]
      field_simp
    · convert valuation_sum 𝔼 h0 h1 har t ω using 1
      simp only [hp, ForwardSolution.sunspotFamily_succ, Pi.add_apply, Pi.smul_apply,
        Pi.zero_apply, sub_zero, smul_eq_mul]
      generalize ForwardSolution.sunspotFamily (lam1 β σ κ) 0 (fun t => -k • ε t) (-k • ε 0) t ω = S
      have hrl : r * lam1 β σ κ = 1 := by rw [hr]; exact inv_mul_cancel₀ hl0
      rw [hkdef]
      field_simp
      linear_combination S * hrl
  refine ⟨(pegX β σ κ ibar (fiscalP β σ κ ρ ε), pegPi ibar (fiscalP β σ κ ρ ε)),
    ⟨he1, he2, he3, he4, he5, hval⟩, ?_⟩
  rintro ⟨x, π⟩ ⟨g1, -, g3, g4, g5, g6⟩
  have hπ := valuation_pins 𝔼 hβ hσκ hκ hρ0 hρ1 g3 g4 g5 g1 g6
  obtain ⟨q, -, -, hx, hπq⟩ := peg_equilibrium_char 𝔼 hβ hσκ hκ g4 g5 g1
  have hq : q = fiscalP β σ κ ρ ε := by
    funext t ω
    have := congrFun (congrFun (hπq.symm.trans hπ) t) ω
    simp only [pegPi] at this
    linarith
  simp only [Prod.mk.injEq]
  exact ⟨hx.trans (by rw [hq]), hπ⟩

/-- Cochrane (2023), §20.1, p. 469: in the fiscal equilibrium, unexpected inflation is pinned
by fiscal news, `π_{t+1} − E_tπ_{t+1} = −(1 − ρ/λ₁)ε_{t+1}`. -/
theorem fiscal_unexpected_inflation {β σ κ ibar ρ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ)
    {ε : ℕ → Ω → ℝ} (hεa : 𝔼.Adapted ε) (hεmd : ∀ t, 𝔼.E t (ε (t + 1)) = 0) (t : ℕ) (ω : Ω) :
    pegPi ibar (fiscalP β σ κ ρ ε) (t + 1) ω - 𝔼.E t (pegPi ibar (fiscalP β σ κ ρ ε) (t + 1)) ω
      = -(1 - ρ / lam1 β σ κ) * ε (t + 1) ω := by
  set k := 1 - ρ * (lam1 β σ κ)⁻¹
  have hνa : 𝔼.Adapted (fun t => (-k) • ε t) := fun t => by rw [map_smul, hεa t]
  have hν0 : 𝔼.E 0 ((-k) • ε 0) = (-k) • ε 0 := by rw [map_smul, hεa 0]
  have hνmd : ∀ t, 𝔼.E t ((fun t => (-k) • ε t) (t + 1)) = 0 := fun t => by
    simp only [map_smul, hεmd t, smul_zero]
  have := sunspot_innovation 𝔼 (ibar := ibar) hβ hσκ hν0 hνa hνmd t ω
  simp only [smul_eq_mul, Pi.smul_apply] at this
  rw [fiscalP, this, div_eq_mul_inv]

/-- Cochrane (2023), §20.1, p. 469 ("stable"): in the fiscal equilibrium expected inflation
converges to the peg. -/
theorem fiscal_stable {β σ κ ibar ρ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) (hκ : κ ≠ 0)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {ε : ℕ → Ω → ℝ} (hεa : 𝔼.Adapted ε) (hεb : BoundedProc ε)
    (hεmd : ∀ t, 𝔼.E t (ε (t + 1)) = 0) (s : ℕ) (ω : Ω) :
    Tendsto (fun k => 𝔼.E s (pegPi ibar (fiscalP β σ κ ρ ε) (s + k)) ω) atTop (𝓝 ibar) := by
  obtain ⟨z, ⟨g1, -, g3, g4, g5, g6⟩, -⟩ :=
    fiscal_selects 𝔼 (ibar := ibar) hβ hσκ hκ hρ0 hρ1 hεa hεb hεmd
  have hπ := valuation_pins 𝔼 hβ hσκ hκ hρ0 hρ1 g3 g4 g5 g1 g6
  rw [← hπ]
  exact peg_expected_converges 𝔼 hβ hσκ hκ g3 g4 g5 g1 s ω

/-- Cochrane (2023), §20.1, p. 469 ("quiet"): without fiscal news the fiscal equilibrium is the
steady state, `π_t = ī` at every date and state. -/
theorem fiscal_quiet (β σ κ ibar ρ : ℝ) (t : ℕ) (ω : Ω) :
    pegPi ibar (fiscalP β σ κ ρ (0 : ℕ → Ω → ℝ)) t ω = ibar := by
  have : fiscalP β σ κ ρ (0 : ℕ → Ω → ℝ) t ω = 0 := by
    induction t generalizing ω with
    | zero => simp [fiscalP, ForwardSolution.sunspotFamily]
    | succ t ih =>
      rw [fiscalP, ForwardSolution.sunspotFamily_succ, ← fiscalP]
      simp [ih]
  simp [pegPi, this]

/-- Cochrane (2023), §20.1, p. 469 ("were a deflation to break out, our fiscal authorities
would not respond with sharp tax increases"): in the fiscal equilibrium a date-0 deflation
below the peg happens iff the date-0 fiscal news is a contraction, `ε₀ > 0`. -/
theorem deflation_iff_fiscal_contraction {β σ κ ibar ρ : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ)
    (hρ1 : ρ ≤ 1) (ε : ℕ → Ω → ℝ) (ω : Ω) :
    pegPi ibar (fiscalP β σ κ ρ ε) 0 ω < ibar ↔ 0 < ε 0 ω := by
  have hl1 := one_lt_lam1 hβ hσκ
  have hr1 : (lam1 β σ κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hr0 : 0 < (lam1 β σ κ)⁻¹ := by positivity
  have hk : 0 < 1 - ρ * (lam1 β σ κ)⁻¹ := by nlinarith
  simp only [pegPi, fiscalP, ForwardSolution.sunspotFamily, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith
  · intro h
    nlinarith

end Cochrane.ZeroBound.ZLBPeg
