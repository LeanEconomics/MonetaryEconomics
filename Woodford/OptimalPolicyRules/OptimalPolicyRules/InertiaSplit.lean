/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.GeneralLinksInertia
import OptimalPolicyRules.Prop83Links

/-!
# The inflation-inertia model: deflating splits, Proposition 8.3, and Rule III

Woodford (2003), *Interest and Prices*, Chapter 8, §3.2, pp. 592–604, and App. G.6–G.7,
pp. 724–732, through the general Propositions 8.1 and 8.3 (§1.4–1.5, pp. 553–557).

The inflation-inertia model (`GeneralLinksInertia.inProblem`: `n_Z = 1`, `Z_t = π_{t−1}`,
`z = (π, x)`) is fed through the general machinery of Propositions 8.1 and 8.3.

## Main results

* **The characteristic polynomial (1.15).** `in_pencil_eval`, `in_pencilPoly`:
  `det(A − μÎ) = −β(μ − μ₁)(μ − μ₂)(μ − μ₃)` with `μⱼ = (βλⱼ)⁻¹` for the roots `λⱼ` of
  Proposition 8.7 (`CubicRoots`); `in_assumption83` (Assumption 8.3 when `S² ≠ 4P₂₃`),
  `in_stableCount` (`n_Z + m` roots with `|μ| < β⁻¹`, `m = 1`), `in_no_circle`.
* **Proposition 8.3 for the model.** `in_prop83`: for EVERY representation of the corrected
  Proposition 8.1 (`Prop81ConclusionM`), `α(L) = det(I − ΛL)` has exactly one zero inside the unit
  circle and none on it (real or complex roots; no Assumption 8.1 needed).
* **The deflating splits (G.4).** `inSplit`: for each real root `λₛ` of `λ² − Sλ + P₂₃` (the root
  solved forward) a `DeflatingSplit` with `J = (1, μ, σμ²/(1 − μ))'`, `Ψ = [μ]`, `μ = (βλₛ)⁻¹`;
  `in_Kdet` (`det K = γ/μ`), `in_Λmat` (explicit `Λ`), `alpha_inJ`:
  `α(L) = (1 − λ₁L)(1 − (S − λₛ)L)`. `alpha_ruleI`, `alpha_ruleII`: solving `λ₃` (resp. `λ₂`)
  forward gives the lag polynomial of Rule I (3.22) (resp. Rule II (3.23)).
* **Every split is one of these; Rule III.** `split_classify`, `split_alpha`: every
  `DeflatingSplit` of the model has `Λ` (hence `α`) of some `inSplit`; `split_isEmpty`: in the
  complex case there is none; `split_not_ruleIII`: away from `S² = 4P₂₃` no split has Rule III's
  lag polynomial `(1 − λ₁L)(1 − ½(λ₂ + λ₃)L)` (3.24).
* **Proposition 8.9's `ρ₁ > 1` from Proposition 8.3.** `one_lt_trace_sub_det` (a `2 × 2` lemma:
  one zero of `α` inside, none on the circle, `det Λ, tr Λ > 0` ⇒ `tr Λ − det Λ > 1`) and
  `prop_8_9_rho1_from_general`: `ρ₁ = 1 + (λ_b − 1)(1 − λ₁) > 1` for Rules I and II.

## Implementation notes

The `3 × 3` determinants are computed by reindexing `Unit ⊕ Fin 2 ≃ Fin 3` (`eqv3`).
-/

namespace Woodford.OptimalPolicyRules.InertiaSplit

open Matrix Polynomial GeneralSetup Adjugate PencilSplit
open TargetCriterion (zerosInside)
open IRuleBasic (Calib)
open CubicRoots
open GeneralLinksInertia (inSys inProblem in_det_ne in_xvec)

/-- The reindexing `Unit ⊕ Fin 2 ≃ Fin 3` used for `3 × 3` determinants. -/
def eqv3 : Unit ⊕ Fin 2 ≃ Fin 3 :=
  (Equiv.sumCongr finOneEquiv.symm (Equiv.refl _)).trans finSumFinEquiv

/-- Woodford (2003), (1.15) (tool): `eqv3⁻¹ 0` is the predetermined coordinate `Z`. -/
theorem eqv3_0 : eqv3.symm 0 = Sum.inl () := rfl

/-- Woodford (2003), (1.15) (tool): `eqv3⁻¹ 1` is the `π`-coordinate. -/
theorem eqv3_1 : eqv3.symm 1 = Sum.inr 0 := rfl

/-- Woodford (2003), (1.15) (tool): `eqv3⁻¹ 2` is the `x`-coordinate. -/
theorem eqv3_2 : eqv3.symm 2 = Sum.inr 1 := rfl

variable (c : Calib) (γ : ℝ)
variable {ιZ ιz : Type*} [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz]

/-! ### The characteristic polynomial (1.15) of the inertia model -/

/-- Woodford (2003), App. G.6, p. 725: the root `μ = (βλ)⁻¹` of (1.15) belonging to a root `λ`
of `P(λ)` (3.17)–(3.20). -/
noncomputable def muj (l : ℂ) : ℂ := ((c.β : ℂ) * l)⁻¹

/-- Woodford (2003), eq. (1.15), p. 546, for the inertia model:
`det(A − μÎ) = γ − (1 + γ + βγ)μ + (1 + β + βγ + κσ)μ² − βμ³`. -/
theorem in_pencil_eval (hσ : c.σ ≠ 0) (hd : 1 + c.β * γ ≠ 0) (z : ℂ) :
    (inSys c γ hσ hd).pencilPoly.eval z = γ - (1 + γ + c.β * γ) * z +
      (1 + c.β + c.β * γ + c.κ * c.σ) * z ^ 2 - c.β * z ^ 3 := by
  rw [PencilSplit.pencilPoly_eval, ← det_submatrix_equiv_self eqv3.symm, det_fin_three]
  simp [eqv3_0, eqv3_1, eqv3_2, LinearRESystem.Ahat, LinearRESystem.Ihat, inSys]
  ring

/-- Woodford (2003), (1.15) at `μ = 0`: `det A = γ` for the inertia model. -/
theorem in_Ahat_det (hσ : c.σ ≠ 0) (hd : 1 + c.β * γ ≠ 0) :
    (inSys c γ hσ hd).Ahat.det = γ := by
  rw [← det_submatrix_equiv_self eqv3.symm, det_fin_three]
  simp [eqv3_0, eqv3_1, eqv3_2, LinearRESystem.Ahat, inSys]

/-- Woodford (2003), Prop. 8.7, p. 594: `λ₂ ≠ 0` (indeed `|λ₂| > 1`). -/
theorem lam2_ne_zero {β γ κ σ : ℝ} (h : Assumptions.Standing β γ κ σ) : lam2 β γ κ σ ≠ 0 :=
  fun e => by
    have := one_lt_norm_lam2 h
    rw [e, norm_zero] at this
    linarith

/-- Woodford (2003), Prop. 8.7, p. 594: `λ₃ ≠ 0` (indeed `|λ₃| > 1`). -/
theorem lam3_ne_zero {β γ κ σ : ℝ} (h : Assumptions.Standing β γ κ σ) : lam3 β γ κ σ ≠ 0 :=
  fun e => by
    have := one_lt_norm_lam3 h
    rw [e, norm_zero] at this
    linarith

/-- Woodford (2003), (1.15) and Prop. 8.7, App. G.6, p. 725: under the standing assumptions the
characteristic polynomial of the inertia model is `−β(μ − μ₁)(μ − μ₂)(μ − μ₃)`,
`μⱼ = (βλⱼ)⁻¹`. -/
theorem in_pencilPoly (h : Assumptions.Standing c.β γ c.κ c.σ) (hσ : c.σ ≠ 0)
    (hd : 1 + c.β * γ ≠ 0) :
    (inSys c γ hσ hd).pencilPoly = C (-(c.β : ℂ)) * (X - C (muj c (lam1 c.β γ c.κ c.σ))) *
      (X - C (muj c (lam2 c.β γ c.κ c.σ))) * (X - C (muj c (lam3 c.β γ c.κ c.σ))) := by
  have hβ : (c.β : ℂ) ≠ 0 := by exact_mod_cast h.beta_pos.ne'
  have h1 : (lam1 c.β γ c.κ c.σ : ℂ) ≠ 0 := by exact_mod_cast (lam1_spec h).1.ne'
  have h2 := lam2_ne_zero h
  have h3 := lam3_ne_zero h
  have hv := vieta_G19 h
  refine Polynomial.funext fun z => ?_
  rw [in_pencil_eval]
  have hA := ApolyC_factor h ((c.β : ℂ) * z)
  have key : ∀ l : ℂ, l ≠ 0 →
      (1 - l * ((c.β : ℂ) * z)) = -((c.β : ℂ) * l) * (z - ((c.β : ℂ) * l)⁻¹) := by
    intro l hl
    field_simp
    ring
  rw [key _ h1, key _ h2, key _ h3] at hA
  have e : ApolyC c.β γ c.κ c.σ ((c.β : ℂ) * z) = (c.β : ℂ) * ((γ : ℂ) - (1 + γ + c.β * γ) * z +
      (1 + c.β + c.β * γ + c.κ * c.σ) * z ^ 2 - c.β * z ^ 3) := by
    simp only [ApolyC, coefA0, coefA1, coefA2, coefA3]
    push_cast
    field_simp
    ring
  rw [e] at hA
  simp only [eval_mul, eval_C, eval_sub, eval_X, muj]
  refine mul_left_cancel₀ hβ ?_
  rw [hA]
  push_cast
  have hv' : (c.β : ℂ) * γ * ((c.β : ℂ) * lam1 c.β γ c.κ c.σ * lam2 c.β γ c.κ c.σ *
      lam3 c.β γ c.κ c.σ) = 1 := by
    rw [← hv]
    exact inv_mul_cancel₀ (by simp [hβ, h1, h2, h3])
  linear_combination (-(c.β : ℂ) ^ 2 * (z - ((c.β : ℂ) * (lam1 c.β γ c.κ c.σ : ℂ))⁻¹) *
    (z - ((c.β : ℂ) * lam2 c.β γ c.κ c.σ)⁻¹) * (z - ((c.β : ℂ) * lam3 c.β γ c.κ c.σ)⁻¹)) * hv'

/-- Woodford (2003), App. G.6: `|μ| = (β|λ|)⁻¹` for `μ = (βλ)⁻¹`. -/
theorem norm_muj (hβ : 0 < c.β) (l : ℂ) : ‖muj c l‖ = (c.β * ‖l‖)⁻¹ := by
  rw [muj, norm_inv, norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ.le]

/-- Woodford (2003), (1.15) and Prop. 8.7: the roots of (1.15) are `μ₁, μ₂, μ₃`. -/
theorem in_roots (h : Assumptions.Standing c.β γ c.κ c.σ) (hσ : c.σ ≠ 0)
    (hd : 1 + c.β * γ ≠ 0) :
    (inSys c γ hσ hd).pencilPoly.roots = {muj c (lam1 c.β γ c.κ c.σ),
      muj c (lam2 c.β γ c.κ c.σ), muj c (lam3 c.β γ c.κ c.σ)} := by
  have hβ : -(c.β : ℂ) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast h.beta_pos.ne')
  rw [in_pencilPoly c γ h, mul_assoc, mul_assoc, roots_C_mul _ hβ,
    roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (mul_ne_zero (X_sub_C_ne_zero _)
      (X_sub_C_ne_zero _))), roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]
  rfl

/-- Woodford (2003), pp. 552, 556, with Prop. 8.7: `|μ₁| > β⁻¹` (as `λ₁ < 1`) while
`|μ₂|, |μ₃| < β⁻¹` (as `|λ₂|, |λ₃| > 1`). -/
theorem in_root_norms (h : Assumptions.Standing c.β γ c.κ c.σ) :
    c.β⁻¹ < ‖muj c (lam1 c.β γ c.κ c.σ)‖ ∧ ‖muj c (lam2 c.β γ c.κ c.σ)‖ < c.β⁻¹ ∧
      ‖muj c (lam3 c.β γ c.κ c.σ)‖ < c.β⁻¹ := by
  have hβ := h.beta_pos
  have h1 := lam1_spec h
  rw [norm_muj c hβ, norm_muj c hβ, norm_muj c hβ, Complex.norm_real,
    Real.norm_of_nonneg h1.1.le]
  refine ⟨?_, ?_, ?_⟩
  · exact inv_strictAnti₀ (mul_pos hβ h1.1) (by nlinarith)
  · exact inv_strictAnti₀ hβ (by nlinarith [one_lt_norm_lam2 h])
  · exact inv_strictAnti₀ hβ (by nlinarith [one_lt_norm_lam3 h])

/-- Woodford (2003), App. G.6: `μ = (βλ)⁻¹ ≠ 0`. -/
theorem muj_ne_zero (h : Assumptions.Standing c.β γ c.κ c.σ) {l : ℂ} (hl : l ≠ 0) :
    muj c l ≠ 0 :=
  inv_ne_zero (mul_ne_zero (by exact_mod_cast h.beta_pos.ne') hl)

/-- Woodford (2003), Assumption 8.7, p. 556, for the inertia model: exactly `n_Z + 1 = 2` roots
of (1.15) have `|μ| < β⁻¹` (`A` is invertible), so `m = 1`. -/
theorem in_stableCount (h : Assumptions.Standing c.β γ c.κ c.σ) (hσ : c.σ ≠ 0)
    (hd : 1 + c.β * γ ≠ 0) :
    (inSys c γ hσ hd).stableCount c.β⁻¹ = Fintype.card Unit + 1 := by
  obtain ⟨n1, n2, n3⟩ := in_root_norms c γ h
  have hA : (inSys c γ hσ hd).Ahat.rank = 3 := by
    rw [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr ?_)]
    · simp
    · rw [in_Ahat_det]
      exact isUnit_iff_ne_zero.mpr h.gamma_pos.ne'
  have z2 := muj_ne_zero c γ h (lam2_ne_zero h)
  have z3 := muj_ne_zero c γ h (lam3_ne_zero h)
  unfold LinearRESystem.stableCount
  rw [in_roots c γ h, hA]
  simp only [Multiset.insert_eq_cons, Multiset.filter_cons, Multiset.filter_singleton]
  simp [n1.not_gt, n2, n3, z2, z3]

/-- Woodford (2003), p. 537: `det Ẽ = β` for the inertia model. -/
theorem in_Et_det (hσ : c.σ ≠ 0) (hd : 1 + c.β * γ ≠ 0) : (inSys c γ hσ hd).Et.det = c.β := by
  simp [inSys, det_fin_two]

/-- Woodford (2003), App. G.6: `λ ↦ (βλ)⁻¹` is injective. -/
theorem muj_injective (hβ : c.β ≠ 0) {l l' : ℂ} (h : muj c l = muj c l') : l = l' :=
  mul_left_cancel₀ (by exact_mod_cast hβ : (c.β : ℂ) ≠ 0) (inv_injective h)

/-- Woodford (2003), Assumption 8.3, App. G.1, p. 716, for the inertia model: (1.15) is a nonzero
polynomial with `3 = rank Ẽ + rank A − n_z` distinct nonzero roots, provided `λ₂ ≠ λ₃`
(`S² ≠ 4P₂₃`). -/
theorem in_assumption83 (h : Assumptions.Standing c.β γ c.κ c.σ) (hσ : c.σ ≠ 0)
    (hd : 1 + c.β * γ ≠ 0) (hD : discQ c.β γ c.κ c.σ ≠ 0) :
    PencilEigen.Assumption83 (inSys c γ hσ hd) := by
  obtain ⟨n1, n2, n3⟩ := in_root_norms c γ h
  have z1 := muj_ne_zero c γ h (by exact_mod_cast (lam1_spec h).1.ne' :
    (lam1 c.β γ c.κ c.σ : ℂ) ≠ 0)
  have z2 := muj_ne_zero c γ h (lam2_ne_zero h)
  have z3 := muj_ne_zero c γ h (lam3_ne_zero h)
  have hnz : PencilEigen.nonzeroRoots (inSys c γ hσ hd) = {muj c (lam1 c.β γ c.κ c.σ),
      muj c (lam2 c.β γ c.κ c.σ), muj c (lam3 c.β γ c.κ c.σ)} := by
    rw [PencilEigen.nonzeroRoots, in_roots c γ h, Multiset.filter_eq_self]
    intro a ha
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    exacts [z1, z2, z3]
  have hA : (inSys c γ hσ hd).Ahat.rank = 3 := by
    rw [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr ?_)]
    · simp
    · rw [in_Ahat_det]
      exact isUnit_iff_ne_zero.mpr h.gamma_pos.ne'
  have hE : (inSys c γ hσ hd).Et.rank = 2 := by
    rw [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr ?_)]
    · simp
    · rw [in_Et_det]
      exact isUnit_iff_ne_zero.mpr h.beta_pos.ne'
  refine (PencilEigen.Assumption83.ofRoots _ ?_ ?_ ?_).elim id
  · rw [in_pencilPoly c γ h]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (C_ne_zero.mpr
      (neg_ne_zero.mpr (by exact_mod_cast h.beta_pos.ne'))) (X_sub_C_ne_zero _))
      (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _)
  · rw [hnz]
    have h12 : muj c (lam1 c.β γ c.κ c.σ) ≠ muj c (lam2 c.β γ c.κ c.σ) := fun e => by
      rw [e] at n1; linarith
    have h13 : muj c (lam1 c.β γ c.κ c.σ) ≠ muj c (lam3 c.β γ c.κ c.σ) := fun e => by
      rw [e] at n1; linarith
    have h23 : muj c (lam2 c.β γ c.κ c.σ) ≠ muj c (lam3 c.β γ c.κ c.σ) := fun e =>
      hD (lam2_eq_lam3_iff.mp (muj_injective c h.beta_pos.ne' e))
    simp [h12, h13, h23]
  · rw [hnz, hA, hE]
    simp

/-- Woodford (2003), pp. 556–558, for the inertia model: no root of (1.15) lies on
`|μ| = β⁻¹`. -/
theorem in_no_circle (h : Assumptions.Standing c.β γ c.κ c.σ) (hσ : c.σ ≠ 0)
    (hd : 1 + c.β * γ ≠ 0) : ∀ l ∈ (inSys c γ hσ hd).pencilPoly.roots, ‖l‖ ≠ c.β⁻¹ := by
  obtain ⟨n1, n2, n3⟩ := in_root_norms c γ h
  intro l hl
  rw [in_roots c γ h] at hl
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hl
  rcases hl with rfl | rfl | rfl
  · exact n1.ne'
  · exact n2.ne
  · exact n3.ne

/-! ### A deflating split for each real selected root -/

/-- Woodford (2003), eq. (1.15), p. 546, for the inertia model at a real argument:
`det(A − μÎ) = γ − (1 + γ + βγ)μ + (1 + β + βγ + κσ)μ² − βμ³` (`in_pencil_eval`). -/
noncomputable def pR (μ : ℝ) : ℝ :=
  γ - (1 + γ + c.β * γ) * μ + (1 + c.β + c.β * γ + c.κ * c.σ) * μ ^ 2 - c.β * μ ^ 3

/-- Woodford (2003), App. G.1, (G.4), p. 717, for the inertia model: the `3 × 1` matrix
`J = (1, μ, σμ²/(1 − μ))'` spanning the right deflating subspace of a selected root `μ`
(`Z`-row, then the `π`- and `x`-rows). -/
noncomputable def inJ (μ : ℝ) : Matrix (Unit ⊕ Fin 2) Unit ℝ :=
  Matrix.of fun r _ => Sum.elim (fun _ => 1) ![μ, c.σ * μ ^ 2 / (1 - μ)] r

/-- Woodford (2003), App. G.1, (G.4), p. 717: `Ψ = [μ]` (`n_Z = 1`). -/
def inPsi (μ : ℝ) : Matrix Unit Unit ℝ := Matrix.of fun _ _ => μ

/-- Woodford (2003), (1.15): `μ = 1` is never a root, `det(A − Î) = κσ`. -/
theorem pR_one : pR c γ 1 = c.κ * c.σ := by
  unfold pR
  ring

/-- Woodford (2003), (1.15): `μ = 0` is never a root, `det A = γ`. -/
theorem pR_zero : pR c γ 0 = γ := by
  unfold pR
  ring

/-- Woodford (2003), App. G.6, p. 725: `det(A − μÎ)` at `μ = (βλ)⁻¹` is `P(λ)/(βλ³)`, so the
roots of (1.15) are the `(βλⱼ)⁻¹` of the roots `λⱼ` of (3.17)–(3.20). -/
theorem pR_inv {l : ℝ} (hβ : c.β ≠ 0) (hl : l ≠ 0) :
    pR c γ (c.β * l)⁻¹ * (c.β * l ^ 3) = Precip c.β γ c.κ c.σ l := by
  unfold pR Precip coefA2
  field_simp
  ring

/-- Woodford (2003), App. G.1, (G.4), p. 717: `A J = Î J Ψ` for `J = inJ μ`, `Ψ = [μ]`, at every
real root `μ ≠ 1` of (1.15). -/
theorem in_deflate (hσ : c.σ ≠ 0) (hd : 1 + c.β * γ ≠ 0) {μ : ℝ} (hp : pR c γ μ = 0)
    (h1 : 1 - μ ≠ 0) :
    (inSys c γ hσ hd).Ahat * inJ c μ = (inSys c γ hσ hd).Ihat * inJ c μ * inPsi μ := by
  ext r u
  rcases r with r | j
  · simp [mul_apply, Fintype.sum_sum_type, LinearRESystem.Ahat, LinearRESystem.Ihat, inSys, inJ,
      inPsi]
  · fin_cases j
    · simp [mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, LinearRESystem.Ahat,
        LinearRESystem.Ihat, inSys, inJ, inPsi]
      field_simp
      unfold pR at hp
      linear_combination -hp
    · simp [mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, LinearRESystem.Ahat,
        LinearRESystem.Ihat, inSys, inJ, inPsi]
      field_simp
      ring

/-- Woodford (2003), App. G.1, p. 718: `J₁ = 1` for `J = inJ μ`. -/
theorem in_J1 (μ : ℝ) : J1 (inJ c μ) = 1 := by
  ext a b
  simp [J1, inJ]

/-- Woodford (2003), eq. (1.21), p. 553: `Υ = −(J₁')⁻¹J₂'Ẽ' = −(βμ, σμ + σμ²/(1 − μ))`. -/
theorem in_Υmat (hσ : c.σ ≠ 0) (hd : 1 + c.β * γ ≠ 0) (μ : ℝ) :
    Υmat (inSys c γ hσ hd) (inJ c μ) =
      Matrix.of fun _ j => ![-(c.β * μ), -(c.σ * μ + c.σ * μ ^ 2 / (1 - μ))] j := by
  rw [Υmat, in_J1, transpose_one, inv_one, Matrix.one_mul]
  ext a j
  fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, J2, inJ, inSys] <;> ring

/-- Woodford (2003), eq. (1.20), p. 553: `K = A₂₂' + A₁₂'Υ` for the inertia model. -/
theorem in_Kmat (hσ : c.σ ≠ 0) (hd : 1 + c.β * γ ≠ 0) (μ : ℝ) :
    Kmat (inSys c γ hσ hd) (inJ c μ) =
      !![1 + c.β * γ - c.β * μ, -(c.σ * μ + c.σ * μ ^ 2 / (1 - μ)); -c.κ, 1] := by
  rw [Kmat, in_Υmat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, inSys]
  all_goals ring

/-- Woodford (2003), Assumption 8.4 (i) for the inertia model: `det K = γ/μ ≠ 0` at a root. -/
theorem in_Kdet (hσ : c.σ ≠ 0) (hd : 1 + c.β * γ ≠ 0) {μ : ℝ} (hp : pR c γ μ = 0)
    (h1 : 1 - μ ≠ 0) (h0 : μ ≠ 0) :
    (Kmat (inSys c γ hσ hd) (inJ c μ)).det = γ / μ := by
  rw [in_Kmat, det_fin_two_of]
  unfold pR at hp
  field_simp
  linear_combination -hp

/-- Woodford (2003), eq. (1.20), p. 553: `Λ = β⁻¹K⁻¹Ẽ'` for the inertia model,
`Λ = (μ/(βγ)) [β, σ + d; κβ, κσ + 1 + βγ − βμ]`, `d = σμ/(1 − μ)`. -/
theorem in_Λmat (hσ : c.σ ≠ 0) (hd : 1 + c.β * γ ≠ 0) (hβ : c.β ≠ 0) (hγ : γ ≠ 0) {μ : ℝ}
    (hp : pR c γ μ = 0) (h1 : 1 - μ ≠ 0) (h0 : μ ≠ 0) :
    Λmat (inSys c γ hσ hd) c.β (inJ c μ) = (μ / (c.β * γ)) •
      !![c.β, c.σ + (c.σ * μ + c.σ * μ ^ 2 / (1 - μ));
        c.κ * c.β, c.κ * c.σ + (1 + c.β * γ - c.β * μ)] := by
  have hEt : (inSys c γ hσ hd).Etᵀ = !![c.β, c.σ; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Λmat, inv_def, in_Kdet c γ hσ hd hp h1 h0, in_Kmat, adjugate_fin_two_of, hEt,
    Ring.inverse_eq_inv', Matrix.smul_mul, mul_fin_two, smul_smul]
  congr 1
  · field_simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- Woodford (2003), (1.22), p. 553: for a `2 × 2` matrix,
`α(L) = det(I − ΛL) = 1 − (tr Λ)L + (det Λ)L²`. -/
theorem alpha_fin_two (Λ : Matrix (Fin 2) (Fin 2) ℝ) :
    Adjugate.alpha Λ = 1 - C Λ.trace * X + C Λ.det * X ^ 2 := by
  rw [Adjugate.alpha, Adjugate.lagMat, det_fin_two, det_fin_two, trace_fin_two]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), smul_eq_mul, C_add, C_sub, C_mul]
  ring

/-- Woodford (2003), (1.20): `tr Λ = (μ/(βγ))(1 + β + βγ + κσ − βμ)` for the inertia model. -/
theorem in_Λ_trace (hσ : c.σ ≠ 0) (hd : 1 + c.β * γ ≠ 0) (hβ : c.β ≠ 0) (hγ : γ ≠ 0) {μ : ℝ}
    (hp : pR c γ μ = 0) (h1 : 1 - μ ≠ 0) (h0 : μ ≠ 0) :
    (Λmat (inSys c γ hσ hd) c.β (inJ c μ)).trace =
      μ / (c.β * γ) * (1 + c.β + c.β * γ + c.κ * c.σ - c.β * μ) := by
  rw [in_Λmat c γ hσ hd hβ hγ hp h1 h0, trace_fin_two]
  simp
  ring

/-- Woodford (2003), (1.20): `det Λ = μ/(βγ)` for the inertia model. -/
theorem in_Λ_det (hσ : c.σ ≠ 0) (hd : 1 + c.β * γ ≠ 0) (hβ : c.β ≠ 0) (hγ : γ ≠ 0) {μ : ℝ}
    (hp : pR c γ μ = 0) (h1 : 1 - μ ≠ 0) (h0 : μ ≠ 0) :
    (Λmat (inSys c γ hσ hd) c.β (inJ c μ)).det = μ / (c.β * γ) := by
  have hEt : (inSys c γ hσ hd).Et.det = c.β := in_Et_det c γ hσ hd
  rw [Λmat, det_smul, det_mul, det_nonsing_inv, det_transpose, hEt, in_Kdet c γ hσ hd hp h1 h0,
    Ring.inverse_eq_inv', Fintype.card_fin]
  field_simp

/-! ### The quadratic factor `λ² − Sλ + P₂₃` -/

/-- Woodford (2003), (G.18), p. 725: the quadratic `λ² − Sλ + P₂₃` with roots `λ₂, λ₃`. -/
noncomputable def quadQ (β γ κ σ l : ℝ) : ℝ := l ^ 2 - sumS β γ κ σ * l + prodP β γ κ σ

/-- Woodford (2003), App. G.6, p. 726: completing the square,
`λ² − Sλ + P₂₃ = (λ − S/2)² − (S² − 4P₂₃)/4`. -/
theorem quadQ_eq (β γ κ σ l : ℝ) :
    quadQ β γ κ σ l = (l - sumS β γ κ σ / 2) ^ 2 - discQ β γ κ σ / 4 := by
  unfold quadQ discQ
  ring

/-- Woodford (2003), Prop. 8.7, p. 594: in the real case `λ₂ʳ` is a root of the quadratic. -/
theorem quadQ_lam2r {β γ κ σ : ℝ} (hD : 0 ≤ discQ β γ κ σ) : quadQ β γ κ σ (lam2r β γ κ σ) = 0 := by
  rw [quadQ_eq]
  unfold lam2r
  have := Real.sq_sqrt hD
  linear_combination this / 4

/-- Woodford (2003), Prop. 8.7, p. 594: in the real case `λ₃ʳ` is a root of the quadratic. -/
theorem quadQ_lam3r {β γ κ σ : ℝ} (hD : 0 ≤ discQ β γ κ σ) : quadQ β γ κ σ (lam3r β γ κ σ) = 0 := by
  rw [quadQ_eq]
  unfold lam3r
  have := Real.sq_sqrt hD
  linear_combination this / 4

/-- Woodford (2003), Prop. 8.7, p. 594: a real root of `λ² − Sλ + P₂₃` exists only in the real
case, and is `λ₂ʳ` or `λ₃ʳ`. -/
theorem quadQ_cases {β γ κ σ l : ℝ} (hq : quadQ β γ κ σ l = 0) :
    0 ≤ discQ β γ κ σ ∧ (l = lam2r β γ κ σ ∨ l = lam3r β γ κ σ) := by
  rw [quadQ_eq] at hq
  have hD : discQ β γ κ σ = (2 * l - sumS β γ κ σ) ^ 2 := by linear_combination -4 * hq
  refine ⟨hD ▸ sq_nonneg _, ?_⟩
  have hs : Real.sqrt (discQ β γ κ σ) = |2 * l - sumS β γ κ σ| := by
    rw [hD, Real.sqrt_sq_eq_abs]
  unfold lam2r lam3r
  rw [hs]
  rcases le_or_gt 0 (2 * l - sumS β γ κ σ) with h | h
  · right
    rw [abs_of_nonneg h]
    ring
  · left
    rw [abs_of_neg h]
    ring

/-- Woodford (2003), Prop. 8.7, p. 594: the real roots of `λ² − Sλ + P₂₃` exceed one. -/
theorem one_lt_of_quadQ {β γ κ σ l : ℝ} (h : Assumptions.Standing β γ κ σ)
    (hq : quadQ β γ κ σ l = 0) : 1 < l := by
  rcases (quadQ_cases hq).2 with rfl | rfl
  · exact one_lt_lam2r h
  · exact one_lt_lam3r h

/-- Woodford (2003), (G.18), p. 725: `P(λ) = βγ(λ − λ₁)(λ² − Sλ + P₂₃)`, so a real root
`λ ≠ λ₁` of (3.17) is a root of the quadratic factor. -/
theorem quadQ_of_Precip {β γ κ σ l : ℝ} (h : Assumptions.Standing β γ κ σ)
    (hP : Precip β γ κ σ l = 0) (hl : l ≠ lam1 β γ κ σ) : quadQ β γ κ σ l = 0 := by
  rw [Precip_factor h] at hP
  rcases mul_eq_zero.mp hP with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 (mul_ne_zero h.beta_pos.ne' h.gamma_pos.ne')
    · exact absurd (sub_eq_zero.mp h2) hl
  · exact h1

/-! ### The split of a real root `λₛ` solved forward -/

/-- Woodford (2003), (G.20), p. 725, with (1.15): at `μ = (βλₛ)⁻¹`,
`tr Λ = λ₁ + (S − λₛ)`. -/
theorem tr_eq (h : Assumptions.Standing c.β γ c.κ c.σ) {ls : ℝ} (hls : ls ≠ 0)
    (hp : pR c γ (c.β * ls)⁻¹ = 0) :
    (c.β * ls)⁻¹ / (c.β * γ) * (1 + c.β + c.β * γ + c.κ * c.σ - c.β * (c.β * ls)⁻¹) =
      lam1 c.β γ c.κ c.σ + (sumS c.β γ c.κ c.σ - ls) := by
  have hβ := h.beta_pos.ne'
  have hγ := h.gamma_pos.ne'
  have hv := vieta_sum h
  unfold pR at hp
  field_simp at hp ⊢
  linear_combination hp - c.β * ls ^ 2 * hv

/-- Woodford (2003), (G.19), p. 725: at `μ = (βλₛ)⁻¹`, `det Λ = μ/(βγ) = λ₁(S − λₛ)`. -/
theorem det_eq (h : Assumptions.Standing c.β γ c.κ c.σ) {ls : ℝ} (hls : ls ≠ 0)
    (hq : quadQ c.β γ c.κ c.σ ls = 0) :
    (c.β * ls)⁻¹ / (c.β * γ) = lam1 c.β γ c.κ c.σ * (sumS c.β γ c.κ c.σ - ls) := by
  have hβ := h.beta_pos.ne'
  have hγ := h.gamma_pos.ne'
  have hv := vieta_const h
  unfold quadQ at hq
  field_simp at hv ⊢
  linear_combination -hv + c.β ^ 2 * γ * lam1 c.β γ c.κ c.σ * hq

/-- Woodford (2003), App. G.6: a root `λₛ` of the quadratic factor gives the root
`μ = (βλₛ)⁻¹` of (1.15), with `0 < μ < β⁻¹` and `μ ≠ 1`. -/
theorem mu_facts (h : Assumptions.Standing c.β γ c.κ c.σ) {ls : ℝ}
    (hq : quadQ c.β γ c.κ c.σ ls = 0) :
    pR c γ (c.β * ls)⁻¹ = 0 ∧ 1 - (c.β * ls)⁻¹ ≠ 0 ∧ (c.β * ls)⁻¹ ≠ 0 ∧
      0 < (c.β * ls)⁻¹ ∧ (c.β * ls)⁻¹ < c.β⁻¹ := by
  have hβ := h.beta_pos
  have hls := one_lt_of_quadQ h hq
  have hP : Precip c.β γ c.κ c.σ ls = 0 := by
    rw [Precip_factor h, show ls ^ 2 - sumS c.β γ c.κ c.σ * ls + prodP c.β γ c.κ c.σ = 0 from hq,
      mul_zero]
  have hp : pR c γ (c.β * ls)⁻¹ = 0 := by
    have e := pR_inv c γ hβ.ne' (by linarith : ls ≠ 0)
    rw [hP] at e
    rcases mul_eq_zero.mp e with e | e
    · exact e
    · exact absurd e (mul_ne_zero hβ.ne' (pow_ne_zero 3 (by linarith)))
  have hpos : 0 < (c.β * ls)⁻¹ := inv_pos.mpr (mul_pos hβ (by linarith))
  refine ⟨hp, fun e => ?_, hpos.ne', hpos, inv_strictAnti₀ hβ (by nlinarith)⟩
  have : (c.β * ls)⁻¹ = 1 := by linarith
  rw [this, pR_one] at hp
  exact (mul_pos h.kappa_pos h.sigma_pos).ne' hp

/-- **Woodford (2003), App. G.1, (G.4), pp. 717–718, for the inertia model: the deflating split
of a real root `λₛ` of `λ² − Sλ + P₂₃`** (the root solved forward; `μ = (βλₛ)⁻¹` is the selected
root of (1.15) with `|μ| < β⁻¹`), `J = inJ μ`, `Ψ = [μ]`. -/
noncomputable def inSplit (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {ls : ℝ}
    (hq : quadQ c.β γ c.κ c.σ ls = 0) :
    DeflatingSplit (inProblem c γ hc hγ0.le).sys c.β where
  J := inJ c (c.β * ls)⁻¹
  Ψ := inPsi (c.β * ls)⁻¹
  deflate := by
    have h : Assumptions.Standing c.β γ c.κ c.σ :=
      ⟨hc.2.2.1, hc.2.2.2.1, hc.1, hc.2.1, hγ0, hγ1⟩
    obtain ⟨hp, h1, -⟩ := mu_facts c γ h hq
    exact in_deflate c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le) hp h1
  eig_lt := by
    have h : Assumptions.Standing c.β γ c.κ c.σ :=
      ⟨hc.2.2.1, hc.2.2.2.1, hc.1, hc.2.1, hγ0, hγ1⟩
    obtain ⟨-, -, -, hpos, hlt⟩ := mu_facts c γ h hq
    intro ν hν
    rw [det_unique] at hν
    simp only [Matrix.sub_apply, scalar_apply, diagonal_apply_eq, Matrix.map_apply, inPsi,
      Matrix.of_apply, sub_eq_zero] at hν
    rw [hν, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    exact hlt
  J1_det := by
    rw [in_J1, det_one]
    exact one_ne_zero
  K_det := by
    have h : Assumptions.Standing c.β γ c.κ c.σ :=
      ⟨hc.2.2.1, hc.2.2.2.1, hc.1, hc.2.1, hγ0, hγ1⟩
    obtain ⟨hp, h1, h0, -⟩ := mu_facts c γ h hq
    rw [show (inProblem c γ hc hγ0.le).sys = inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le)
      from rfl, in_Kdet c γ _ _ hp h1 h0]
    exact div_ne_zero hγ0.ne' h0

/-- **Woodford (2003), (1.22) and (3.22)–(3.23), for the inertia model**: the split solving the
real root `λₛ` forward has `α(L) = det(I − ΛL) = (1 − λ₁L)(1 − λ_bL)` with `λ_b = S − λₛ` the
other root of `λ² − Sλ + P₂₃`. -/
theorem alpha_inJ (h : Assumptions.Standing c.β γ c.κ c.σ) (hσ : c.σ ≠ 0)
    (hd : 1 + c.β * γ ≠ 0) {ls : ℝ} (hq : quadQ c.β γ c.κ c.σ ls = 0) :
    alpha (Λmat (inSys c γ hσ hd) c.β (inJ c (c.β * ls)⁻¹)) =
      (1 - C (lam1 c.β γ c.κ c.σ) * X) * (1 - C (sumS c.β γ c.κ c.σ - ls) * X) := by
  obtain ⟨hp, h1, h0, -⟩ := mu_facts c γ h hq
  have hls : ls ≠ 0 := by linarith [one_lt_of_quadQ h hq]
  rw [alpha_fin_two, in_Λ_trace c γ hσ hd h.beta_pos.ne' h.gamma_pos.ne' hp h1 h0,
    in_Λ_det c γ hσ hd h.beta_pos.ne' h.gamma_pos.ne' hp h1 h0, tr_eq c γ h hls hp,
    det_eq c γ h hls hq, C_add, C_mul]
  ring

/-! ### Proposition 8.3 for the inertia model, and Proposition 8.9's `ρ₁ > 1` -/

/-- Woodford (2003), Prop. 8.7, p. 594: the standing assumptions of the cubic from an admissible
calibration with `0 < γ ≤ 1`. -/
theorem standing_of (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    Assumptions.Standing c.β γ c.κ c.σ :=
  ⟨hc.2.2.1, hc.2.2.2.1, hc.1, hc.2.1, hγ0, hγ1⟩

/-- Woodford (2003), (1.18): the constant plan `Z = π = 0`, `x = x*`, `i = 0` attains the
targets entering `T̃'W(τ − τ*)` (`T̃'W(Tv₀ − τ*) = 0`), a base point for Proposition 8.3. -/
theorem in_xvec_base (hc : c.Adm) (hγ : 0 ≤ γ) :
    (inProblem c γ hc hγ).Ttilᵀ *ᵥ ((inProblem c γ hc hγ).W *ᵥ ((inProblem c γ hc hγ).T *ᵥ
      Sum.elim (Sum.elim (fun _ => 0) ![0, c.xstar]) (fun _ => 0) -
        (inProblem c γ hc hγ).τstar)) = 0 := by
  rw [in_xvec]
  funext r
  rcases r with r | k
  · simp
  · fin_cases k <;> simp

/-- **Woodford (2003), Proposition 8.3, pp. 556–557, for the inertia model, for every
representation of Proposition 8.1** (any expectation system, nonempty sample space; real or
complex roots, `S² ≠ 4P₂₃`): `α(L) = det(I − ΛL)` has exactly one zero inside the unit circle
and none on it. Here `n_Z = 1`, (1.15) has the two roots `(βλ₂)⁻¹, (βλ₃)⁻¹` with `|μ| < β⁻¹`
(`m = 1`), and no root on `|μ| = β⁻¹`; Assumption 8.1 is not needed (`prop83M_const`). -/
theorem in_prop83 {Ω : Type*} [Nonempty Ω] (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hD : discQ c.β γ c.κ c.σ ≠ 0) (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    (H : Prop81General.Prop81ConclusionM (inProblem c γ hc hγ0.le) 𝔼 t0) :
    zerosInside (alpha H.Λ) = 1 ∧ Prop83.zerosOnCircle (alpha H.Λ) = 0 :=
  Prop83Links.prop83M_const H _ (in_xvec_base c γ hc hγ0.le)
    (in_assumption83 c γ (standing_of c γ hc hγ0 hγ1) hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le) hD)
    (in_stableCount c γ (standing_of c γ hc hγ0 hγ1) hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le))
    (in_no_circle c γ (standing_of c γ hc hγ0 hγ1) hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le))

/-- Woodford (2003), Proposition 8.3 for a `2 × 2` matrix `Λ` with `det Λ > 0` and `tr Λ > 0`:
if `α(L) = det(I − ΛL)` has exactly one zero inside the unit circle and none on it, then
`tr Λ − det Λ > 1`, i.e. `α(1) < 0`. (The eigenvalues are real, since a complex pair has equal
moduli; both are positive; one exceeds one and the other is below one.) -/
theorem one_lt_trace_sub_det (Λ : Matrix (Fin 2) (Fin 2) ℝ) (hin : zerosInside (alpha Λ) = 1)
    (hon : Prop83.zerosOnCircle (alpha Λ) = 0) (hdet : 0 < Λ.det) (htr : 0 < Λ.trace) :
    1 < Λ.trace - Λ.det := by
  rw [Prop83.zerosInside_alpha] at hin
  rw [Prop83.zerosOnCircle_alpha] at hon
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp (Prop83.card_charpoly_roots (Prop83.cmat Λ))
  have hsplit := prod_multiset_X_sub_C_of_monic_of_roots_card_eq (charpoly_monic (Prop83.cmat Λ))
    (by rw [Prop83.card_charpoly_roots, charpoly_natDegree_eq_dim])
  rw [hab, charpoly_fin_two] at hsplit
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton] at hsplit
  have htrC : (Prop83.cmat Λ).trace = (Λ.trace : ℂ) := by
    simp [trace_fin_two, Prop83.cmat]
  have hdetC : (Prop83.cmat Λ).det = (Λ.det : ℂ) := by
    simp [det_fin_two, Prop83.cmat]
  rw [htrC, hdetC] at hsplit
  have c1 : -a - b = -(Λ.trace : ℂ) := by
    simpa [coeff_X, coeff_C, mul_sub, sub_mul] using
      congrArg (fun p : ℂ[X] => p.coeff 1) hsplit
  have c0 : a * b = (Λ.det : ℂ) := by
    simpa [coeff_X, coeff_C, mul_sub, sub_mul] using
      congrArg (fun p : ℂ[X] => p.coeff 0) hsplit
  rw [hab] at hin hon
  have hs : a + b = (Λ.trace : ℂ) := by linear_combination -c1
  have him := congrArg Complex.im hs
  have hre := congrArg Complex.re hs
  have pim := congrArg Complex.im c0
  have pre := congrArg Complex.re c0
  simp only [Complex.add_im, Complex.add_re, Complex.ofReal_im, Complex.ofReal_re,
    Complex.mul_im, Complex.mul_re] at him hre pim pre
  simp only [Multiset.insert_eq_cons, Multiset.filter_cons, Multiset.filter_singleton] at hin hon
  by_cases h0 : a.im = 0
  · have h0' : b.im = 0 := by linarith
    obtain ⟨x, rfl⟩ : ∃ x : ℝ, a = x := ⟨a.re, Complex.ext (by simp) (by simp [h0])⟩
    obtain ⟨y, rfl⟩ : ∃ y : ℝ, b = y := ⟨b.re, Complex.ext (by simp) (by simp [h0'])⟩
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hre pre
    have hx : 0 < x := by
      by_contra hx
      nlinarith [not_lt.mp hx]
    have hy : 0 < y := by
      by_contra hy
      nlinarith [not_lt.mp hy]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx, abs_of_pos hy] at hin hon
    rw [← hre, ← pre]
    by_cases h1 : 1 < x <;> by_cases h2 : 1 < y <;> simp [h1, h2] at hin
    · have : y ≠ 1 := fun e => by simp [e] at hon
      have : y < 1 := lt_of_le_of_ne (not_lt.mp h2) this
      nlinarith
    · have : x ≠ 1 := fun e => by simp [e] at hon
      have : x < 1 := lt_of_le_of_ne (not_lt.mp h1) this
      nlinarith
  · exfalso
    have hbim : b.im = -a.im := by linarith
    have hbre : b.re = a.re := by
      rw [hbim] at pim
      have : a.im * (b.re - a.re) = 0 := by linear_combination pim
      rcases mul_eq_zero.mp this with e | e
      · exact absurd e h0
      · linarith
    have hb : b = (starRingEnd ℂ) a := Complex.ext (by simp [hbre]) (by simp [hbim])
    rw [hb, Complex.norm_conj] at hin
    by_cases h1 : 1 < ‖a‖ <;> simp [h1] at hin

/-- **Woodford (2003), Proposition 8.9, p. 596, `ρ₁ > 1`, obtained from the general
Proposition 8.3.** For the deflating split solving a real root `λₛ` forward, the general
Proposition 8.3 (`in_prop83`: one zero of `α(L)` inside the unit circle, none on it) together
with `det Λ > 0` and `tr Λ > 0` (read off `Λ` without its eigenvalues) gives `tr Λ − det Λ > 1`;
since `tr Λ = λ₁ + λ_b` and `det Λ = λ₁λ_b` (`λ_b = S − λₛ`), this is
`ρ₁ = 1 + (λ_b − 1)(1 − λ₁) > 1`, the coefficient of (3.25) for Rule I (`λₛ = λ₃`) and Rule II
(`λₛ = λ₂`). -/
theorem prop_8_9_rho1_from_general {Ω : Type*} [Nonempty Ω] (hc : c.Adm) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1) (hD : discQ c.β γ c.κ c.σ ≠ 0) (𝔼 : ExpectationSystem Ω) (t0 : ℕ) {ls : ℝ}
    (hq : quadQ c.β γ c.κ c.σ ls = 0) :
    1 < InflationInertiaRepresentations.rho1 (lam1 c.β γ c.κ c.σ) (sumS c.β γ c.κ c.σ - ls) := by
  have h := standing_of c γ hc hγ0 hγ1
  obtain ⟨hin, hon⟩ := in_prop83 c γ hc hγ0 hγ1 hD 𝔼 t0
    (Prop81General.prop81 _ (inSplit c γ hc hγ0 hγ1 hq) 𝔼 t0)
  obtain ⟨hp, h1, h0, hpos, hlt⟩ := mu_facts c γ h hq
  have hls : ls ≠ 0 := by linarith [one_lt_of_quadQ h hq]
  have hβγ : 0 < c.β * γ := mul_pos hc.1 hγ0
  have hΛ : (Prop81General.prop81 _ (inSplit c γ hc hγ0 hγ1 hq) 𝔼 t0).Λ =
      Λmat (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le)) c.β (inJ c (c.β * ls)⁻¹) := rfl
  rw [hΛ] at hin hon
  have htr := in_Λ_trace c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le) hc.1.ne' hγ0.ne' hp h1 h0
  have hdet := in_Λ_det c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le) hc.1.ne' hγ0.ne' hp h1 h0
  have hβμ : c.β * (c.β * ls)⁻¹ < 1 := by
    calc c.β * (c.β * ls)⁻¹ < c.β * c.β⁻¹ := mul_lt_mul_of_pos_left hlt hc.1
      _ = 1 := mul_inv_cancel₀ hc.1.ne'
  have hκσ : 0 < c.κ * c.σ := mul_pos hc.2.2.2.1 hc.2.2.1
  have key := one_lt_trace_sub_det _ hin hon (by rw [hdet]; positivity)
    (by rw [htr]; exact mul_pos (div_pos hpos hβγ) (by nlinarith [hc.1, hβγ]))
  rw [htr, hdet, tr_eq c γ h hls hp, det_eq c γ h hls hq] at key
  unfold InflationInertiaRepresentations.rho1
  linarith

/-! ### Every deflating split of the inertia model solves a real root forward -/

/-- Woodford (2003), (1.20)–(1.21), p. 553: `Υ`, hence `K` and `Λ`, depend only on the column
space of `J`: `Υ(JM) = Υ(J)` for invertible `M`. -/
theorem Υmat_mul (S : LinearRESystem ιZ ιz) (J : Matrix (ιZ ⊕ ιz) ιZ ℝ) {M : Matrix ιZ ιZ ℝ}
    (hM : IsUnit M.det) : Υmat S (J * M) = Υmat S J := by
  have hMt : IsUnit Mᵀ.det := by rwa [det_transpose]
  rw [Υmat, Υmat, J1_mul, J2_mul, transpose_mul, transpose_mul, Matrix.mul_inv_rev,
    Matrix.mul_assoc ((J1 J)ᵀ)⁻¹, ← Matrix.mul_assoc (Mᵀ)⁻¹, nonsing_inv_mul _ hMt,
    Matrix.one_mul]

/-- Woodford (2003), (1.20), p. 553: `Λ(JM) = Λ(J)` for invertible `M`. -/
theorem Λmat_mul (S : LinearRESystem ιZ ιz) (β : ℝ) (J : Matrix (ιZ ⊕ ιz) ιZ ℝ)
    {M : Matrix ιZ ιZ ℝ} (hM : IsUnit M.det) : Λmat S β (J * M) = Λmat S β J := by
  rw [Λmat, Λmat, Kmat, Kmat, Υmat_mul S J hM]

/-- **Woodford (2003), App. G.1 (G.4) for the inertia model: every deflating split is one of
`inSplit`.** For any real `J` (`3 × 1`, `J₁ ≠ 0`), `Ψ = [ψ]` with `AJ = ÎJΨ` and `|ψ| < β⁻¹`,
`ψ = (βλₛ)⁻¹` for a real root `λₛ` of `λ² − Sλ + P₂₃`, and `Λ` is that of `inJ ψ`. -/
theorem split_classify (h : Assumptions.Standing c.β γ c.κ c.σ) (hσ : c.σ ≠ 0)
    (hd : 1 + c.β * γ ≠ 0) (D : DeflatingSplit (inSys c γ hσ hd) c.β) :
    ∃ ls, quadQ c.β γ c.κ c.σ ls = 0 ∧
      Λmat (inSys c γ hσ hd) c.β D.J = Λmat (inSys c γ hσ hd) c.β (inJ c (c.β * ls)⁻¹) := by
  have hβ := h.beta_pos
  set ψ := D.Ψ () () with hψ
  set j := D.J (Sum.inl ()) () with hj
  set a := D.J (Sum.inr 0) () with ha
  set b := D.J (Sum.inr 1) () with hb
  have hΨ : D.Ψ = inPsi ψ := by
    ext u v
    rfl
  have hdef := D.deflate
  have eZ : a = j * ψ := by
    have := congrFun (congrFun hdef (Sum.inl ())) ()
    simpa [mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, LinearRESystem.Ahat,
      LinearRESystem.Ihat, inSys, hΨ, inPsi] using this
  have e0 : -(γ * j) + ((1 + c.β * γ) * a + -(c.κ * b)) = c.β * a * ψ := by
    have := congrFun (congrFun hdef (Sum.inr 0)) ()
    simpa [mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, LinearRESystem.Ahat,
      LinearRESystem.Ihat, inSys, hΨ, inPsi] using this
  have e1 : b = (c.σ * a + b) * ψ := by
    have := congrFun (congrFun hdef (Sum.inr 1)) ()
    simpa [mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, LinearRESystem.Ahat,
      LinearRESystem.Ihat, inSys, hΨ, inPsi] using this
  have hj0 : j ≠ 0 := by
    have := D.J1_det
    rwa [det_unique] at this
  have heig : ‖(ψ : ℂ)‖ < c.β⁻¹ := by
    refine D.eig_lt ψ ?_
    rw [det_unique, hΨ]
    simp [inPsi]
  rw [Complex.norm_real, Real.norm_eq_abs] at heig
  have h1 : 1 - ψ ≠ 0 := by
    intro e
    have e' : ψ = 1 := by linarith
    rw [e', mul_one] at e1
    rw [e', mul_one] at eZ
    have : c.σ * a = 0 := by linarith
    rcases mul_eq_zero.mp this with e2 | e2
    · exact hσ e2
    · exact hj0 (eZ ▸ e2)
  have hb' : b * (1 - ψ) = c.σ * ψ ^ 2 * j := by linear_combination e1 + c.σ * ψ * eZ
  have hbv : b = c.σ * ψ ^ 2 / (1 - ψ) * j := by
    rw [div_mul_eq_mul_div, eq_div_iff h1]
    linear_combination hb'
  have hp : pR c γ ψ = 0 := by
    have : j * pR c γ ψ = 0 := by
      unfold pR
      linear_combination (-(1 - ψ)) * e0 + (1 - ψ) * (1 + c.β * γ - c.β * ψ) * eZ - c.κ * hb'
    rcases mul_eq_zero.mp this with e | e
    · exact absurd e hj0
    · exact e
  have hψ0 : ψ ≠ 0 := by
    intro e
    rw [e, pR_zero] at hp
    exact h.gamma_pos.ne' hp
  set ls := (c.β * ψ)⁻¹ with hls
  have hls0 : ls ≠ 0 := inv_ne_zero (mul_ne_zero hβ.ne' hψ0)
  have hψls : (c.β * ls)⁻¹ = ψ := by
    rw [hls]
    field_simp
  have hP : Precip c.β γ c.κ c.σ ls = 0 := by
    rw [← pR_inv c γ hβ.ne' hls0, hψls, hp, zero_mul]
  have habs : 1 < |ls| := by
    rw [hls, abs_inv, abs_mul, abs_of_pos hβ]
    have hψpos : 0 < |ψ| := abs_pos.mpr hψ0
    rw [one_lt_inv₀ (mul_pos hβ hψpos)]
    calc c.β * |ψ| < c.β * c.β⁻¹ := mul_lt_mul_of_pos_left heig hβ
      _ = 1 := mul_inv_cancel₀ hβ.ne'
  have hne : ls ≠ lam1 c.β γ c.κ c.σ := by
    intro e
    have := lam1_spec h
    rw [e, abs_of_pos this.1] at habs
    linarith [this.2.1]
  refine ⟨ls, quadQ_of_Precip h hP hne, ?_⟩
  have hJ : D.J = inJ c ψ * Matrix.of (fun _ _ => j) := by
    ext r u
    cases u
    rcases r with r | k
    · simp [mul_apply, inJ, hj]
    · fin_cases k
      · simp only [mul_apply, inJ, Finset.univ_unique, Finset.sum_singleton, Matrix.of_apply,
          Sum.elim_inr]
        exact eZ.trans (mul_comm _ _)
      · simp only [mul_apply, inJ, Finset.univ_unique, Finset.sum_singleton, Matrix.of_apply,
          Sum.elim_inr]
        exact hbv
  rw [hJ, Λmat_mul _ _ _ (by rw [det_unique]; exact isUnit_iff_ne_zero.mpr hj0), hψls]

/-- Woodford (2003), (1.22), (3.22)–(3.24): for every deflating split of the inertia model,
`α(L) = (1 − λ₁L)(1 − λ_bL)` with `λ_b = S − λₛ` for a real root `λₛ` of `λ² − Sλ + P₂₃`. -/
theorem split_alpha (h : Assumptions.Standing c.β γ c.κ c.σ) (hσ : c.σ ≠ 0)
    (hd : 1 + c.β * γ ≠ 0) (D : DeflatingSplit (inSys c γ hσ hd) c.β) :
    ∃ ls, quadQ c.β γ c.κ c.σ ls = 0 ∧ alpha (Λmat (inSys c γ hσ hd) c.β D.J) =
      (1 - C (lam1 c.β γ c.κ c.σ) * X) * (1 - C (sumS c.β γ c.κ c.σ - ls) * X) := by
  obtain ⟨ls, hq, hΛ⟩ := split_classify c γ h hσ hd D
  exact ⟨ls, hq, by rw [hΛ, alpha_inJ c γ h hσ hd hq]⟩

/-- Woodford (2003), Prop. 8.7, p. 594: in the complex case (`S² − 4P₂₃ < 0`) the inertia model
has **no** real deflating split (Assumption 8.2 (i) fails: the two roots with `|μ| < β⁻¹` are a
complex pair and `n_Z = 1`). -/
theorem split_isEmpty (h : Assumptions.Standing c.β γ c.κ c.σ) (hσ : c.σ ≠ 0)
    (hd : 1 + c.β * γ ≠ 0) (hD : discQ c.β γ c.κ c.σ < 0) :
    IsEmpty (DeflatingSplit (inSys c γ hσ hd) c.β) := by
  refine ⟨fun D => ?_⟩
  obtain ⟨ls, hq, -⟩ := split_classify c γ h hσ hd D
  exact absurd (quadQ_cases hq).1 (not_le.mpr hD)

/-- Woodford (2003), (1.22): `1 − aL = 1 − bL` forces `a = b`, after cancelling a common factor
`1 − cL`. -/
theorem cancel_linear {a b d : ℝ}
    (h : (1 - C d * X) * (1 - C a * X : ℝ[X]) = (1 - C d * X) * (1 - C b * X)) : a = b := by
  have h0 : (1 - C d * X : ℝ[X]) ≠ 0 := by
    intro e
    have := congrArg (fun p : ℝ[X] => p.coeff 0) e
    simp at this
  have e := congrArg (fun p : ℝ[X] => p.coeff 1) (mul_left_cancel₀ h0 h)
  simpa using e

/-- **Woodford (2003), Rule III (3.24), p. 595, is not the rule (1.28) of any deflating split.**
Away from the bifurcation `S² = 4P₂₃`, no deflating split of the inertia model has the lag
polynomial `(1 − λ₁L)(1 − ½(λ₂ + λ₃)L)` of Rule III: every split has
`α(L) = (1 − λ₁L)(1 − λ_bL)` with `λ_b ∈ {λ₂, λ₃}` (`split_alpha`), and `λ_b = S/2` would make
`λₛ = S/2` a double root. (In the complex case there is no deflating split at all,
`split_isEmpty`.) -/
theorem split_not_ruleIII (h : Assumptions.Standing c.β γ c.κ c.σ) (hσ : c.σ ≠ 0)
    (hd : 1 + c.β * γ ≠ 0) (hD : discQ c.β γ c.κ c.σ ≠ 0)
    (D : DeflatingSplit (inSys c γ hσ hd) c.β) :
    alpha (Λmat (inSys c γ hσ hd) c.β D.J) ≠
      (1 - C (lam1 c.β γ c.κ c.σ) * X) * (1 - C (sumS c.β γ c.κ c.σ / 2) * X) := by
  obtain ⟨ls, hq, hα⟩ := split_alpha c γ h hσ hd D
  intro e
  rw [hα] at e
  have e2 := cancel_linear e
  have hls : ls = sumS c.β γ c.κ c.σ / 2 := by linarith
  rw [quadQ_eq, hls, sub_self] at hq
  exact hD (by linarith)

/-- Woodford (2003), (G.20): `λ₂ʳ + λ₃ʳ = S`. -/
theorem lam2r_add_lam3r (β γ κ σ : ℝ) : lam2r β γ κ σ + lam3r β γ κ σ = sumS β γ κ σ := by
  unfold lam2r lam3r
  ring

/-- **Woodford (2003), Rule I (3.22), p. 595, as the split solving `λ₃` forward**: in the real
case `inSplit` with `λₛ = λ₃` has `α(L) = (1 − λ₁L)(1 − λ₂L)`, the lag polynomial of Rule I. -/
theorem alpha_ruleI (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hD : 0 ≤ discQ c.β γ c.κ c.σ) :
    alpha (Λmat (inProblem c γ hc hγ0.le).sys c.β (inSplit c γ hc hγ0 hγ1 (quadQ_lam3r hD)).J) =
      (1 - C (lam1 c.β γ c.κ c.σ) * X) * (1 - C (lam2r c.β γ c.κ c.σ) * X) := by
  rw [show (inSplit c γ hc hγ0 hγ1 (quadQ_lam3r hD)).J = inJ c (c.β * lam3r c.β γ c.κ c.σ)⁻¹
    from rfl, show (inProblem c γ hc hγ0.le).sys = inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le)
    from rfl, alpha_inJ c γ ⟨hc.2.2.1, hc.2.2.2.1, hc.1, hc.2.1, hγ0, hγ1⟩ _ _ (quadQ_lam3r hD),
    ← lam2r_add_lam3r, add_sub_cancel_right]

/-- **Woodford (2003), Rule II (3.23), p. 595, as the split solving `λ₂` forward**: in the real
case `inSplit` with `λₛ = λ₂` has `α(L) = (1 − λ₁L)(1 − λ₃L)`, the lag polynomial of Rule II. -/
theorem alpha_ruleII (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hD : 0 ≤ discQ c.β γ c.κ c.σ) :
    alpha (Λmat (inProblem c γ hc hγ0.le).sys c.β (inSplit c γ hc hγ0 hγ1 (quadQ_lam2r hD)).J) =
      (1 - C (lam1 c.β γ c.κ c.σ) * X) * (1 - C (lam3r c.β γ c.κ c.σ) * X) := by
  rw [show (inSplit c γ hc hγ0 hγ1 (quadQ_lam2r hD)).J = inJ c (c.β * lam2r c.β γ c.κ c.σ)⁻¹
    from rfl, show (inProblem c γ hc hγ0.le).sys = inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le)
    from rfl, alpha_inJ c γ ⟨hc.2.2.1, hc.2.2.2.1, hc.1, hc.2.1, hγ0, hγ1⟩ _ _ (quadQ_lam2r hD),
    ← lam2r_add_lam3r, add_sub_cancel_left]

end Woodford.OptimalPolicyRules.InertiaSplit
