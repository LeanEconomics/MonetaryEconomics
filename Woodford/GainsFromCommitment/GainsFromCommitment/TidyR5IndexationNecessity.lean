/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.Indexation

/-!
# Necessity of the long-run inflation rate with indexation and transactions frictions

Woodford (2003), *Interest and Prices*, Chapter 7, §1.2, pp. 483–484.

The module Indexation proves that the steady state
`π̄ = −λ_i(r̄ − iᵐ)/(λ_i + β(1 − γ)(1 − βγ))` is the unique constant plan consistent with the
first-order conditions (`Indexation.ss_ind_iff`) and that it is optimal given its own initial
values (`Indexation.ss_ind_optimal`). Here the converse is proved: a constant plan that is
optimal among bounded feasible plans with the same `π_0, x_0` (the timeless constraint)
**must** be this steady state — without assuming that multipliers exist.

## Main results

* An explicit feasible perturbation (`dPi`, `dX`, `dI`): quasi-differenced inflation rises by `1`
  at date `2` (`dPi_t = γ^{t−2}` from date `2`), the output gap moves at dates `1, 2` only, the
  interest rate follows from (1.15); it satisfies the homogeneous (1.21) and (1.15) and leaves
  `π_0, x_0` unchanged (`pert_feasible`).
* Its discounted sums (`dsum_dPi`, `dsum_dX`, `dsum_dI`) and the exact quadratic expansion of the
  loss along it (`lossI_pert`): the first-order coefficient is
  `β/(1 − βγ) · [β(1 − γ)(1 − βγ)π̄ + λ_i(ı̄ − iᵐ)]` (`gradI_eq`).
* **Necessity** (`ss_ind_necessary`): optimality of the constant plan forces the steady-state
  condition `λ_i(ı̄ − iᵐ) = −β(1 − γ)(1 − βγ)π̄`; with feasibility this pins down the long-run
  inflation rate, so the constant plan is timelessly optimal **iff**
  `π̄ = −λ_i(r̄ − iᵐ)/(λ_i + β(1 − γ)(1 − βγ))`, `ı̄ = r̄ + π̄` and `κx̄ = (1 − β)(1 − γ)π̄`
  (`ss_ind_timeless_iff`), for `0 ≤ γ ≤ 1`.
-/

namespace Woodford.GainsFromCommitment.TidyR5IndexationNecessity

open Filter Topology Woodford.GainsFromCommitment.MonetaryFrictions
open Woodford.GainsFromCommitment.Indexation
open Sequences

/-! ### The perturbation -/

/-- Woodford (2003), p. 484 (the perturbation of inflation): `dπ_t = γ^{t−2}` for `t ≥ 2`, `0`
before, so that quasi-differenced inflation `dπ_t − γdπ_{t−1}` is `1` at `t = 2` and `0`
otherwise. -/
noncomputable def dPi (γ : ℝ) (t : ℕ) : ℝ := if 2 ≤ t then γ ^ (t - 2) else 0

/-- Woodford (2003), p. 484 (the perturbation of the output gap, from (1.21)): `−β/κ` at `t = 1`,
`1/κ` at `t = 2`, `0` otherwise. -/
noncomputable def dX (β κ : ℝ) (t : ℕ) : ℝ := if t = 1 then -β / κ else if t = 2 then 1 / κ else 0

/-- Woodford (2003), p. 484 (the perturbation of the interest rate, from (1.15)):
`di_t = dπ_{t+1} + (dx_{t+1} − dx_t)/σ`. -/
noncomputable def dI (β κ σ γ : ℝ) (t : ℕ) : ℝ := dPi γ (t + 1) + (dX β κ (t + 1) - dX β κ t) / σ

/-- Woodford (2003), p. 484 (tool): for `0 ≤ γ ≤ 1` the inflation perturbation is bounded by
`1`. -/
theorem dPi_bdd {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) : Bdd (dPi γ) := by
  refine ⟨1, fun t => ?_⟩
  unfold dPi
  split_ifs
  · rw [abs_of_nonneg (pow_nonneg hγ0 _)]; exact pow_le_one₀ hγ0 hγ1
  · norm_num

/-- Woodford (2003), p. 484 (tool): the output-gap perturbation vanishes from date `3`. -/
theorem dX_bdd (β κ : ℝ) : Bdd (dX β κ) :=
  bdd_of_zero_from 3 fun t ht => by
    simp only [dX, show t ≠ 1 by omega, show t ≠ 2 by omega, ↓reduceIte]

/-- Woodford (2003), p. 484 (tool): the interest-rate perturbation is bounded. -/
theorem dI_bdd {β κ σ γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) : Bdd (dI β κ σ γ) := by
  have h1 := (dPi_bdd hγ0 hγ1).shift
  have h2 := ((dX_bdd β κ).shift.sub (dX_bdd β κ))
  obtain ⟨A, hA⟩ := h1
  obtain ⟨B, hB⟩ := h2
  refine ⟨A + B / |σ|, fun t => ?_⟩
  unfold dI
  refine (abs_add_le _ _).trans (add_le_add (hA t) ?_)
  rw [abs_div]
  rcases eq_or_ne σ 0 with h | h
  · rw [h, abs_zero, div_zero, div_zero]
  · exact div_le_div_of_nonneg_right (hB t) (abs_nonneg _)

/-- Woodford (2003), p. 484: the perturbation satisfies the homogeneous (1.21),
`dπ_t − γdπ_{t−1} = κdx_t + β(dπ_{t+1} − γdπ_t)` with `dπ_{−1} = 0` (`κ ≠ 0`). -/
theorem pert_AS {β κ γ : ℝ} (hκ : κ ≠ 0) (t : ℕ) :
    dPi γ t - γ * lagged 0 (dPi γ) t = κ * dX β κ t + β * (dPi γ (t + 1) - γ * dPi γ t) := by
  match t with
  | 0 => simp [dPi, dX]
  | 1 => simp [dPi, dX]; field_simp; ring
  | 2 => simp [dPi, dX]; field_simp
  | s + 3 =>
    have e1 : dPi γ (s + 3) = γ ^ (s + 1) := by
      simp only [dPi, show 2 ≤ s + 3 by omega, ↓reduceIte, show s + 3 - 2 = s + 1 by omega]
    have e2 : dPi γ (s + 2) = γ ^ s := by
      simp only [dPi, show 2 ≤ s + 2 by omega, ↓reduceIte, show s + 2 - 2 = s by omega]
    have e3 : dPi γ (s + 3 + 1) = γ ^ (s + 2) := by
      simp only [dPi, show 2 ≤ s + 3 + 1 by omega, ↓reduceIte,
        show s + 3 + 1 - 2 = s + 2 by omega]
    have e4 : dX β κ (s + 3) = 0 := by
      simp only [dX, show s + 3 ≠ 1 by omega, show s + 3 ≠ 2 by omega, ↓reduceIte]
    rw [lagged_succ, e1, e2, e3, e4]
    ring

/-- Woodford (2003), p. 484: the perturbation satisfies the homogeneous (1.15),
`dx_t = dx_{t+1} − σ(di_t − dπ_{t+1})` (`σ ≠ 0`). -/
theorem pert_IS {β κ σ γ : ℝ} (hσ : σ ≠ 0) (t : ℕ) :
    dX β κ t = dX β κ (t + 1) - σ * (dI β κ σ γ t - dPi γ (t + 1)) := by
  unfold dI
  field_simp
  ring

/-- Woodford (2003), p. 484: the perturbed constant plan is feasible — (1.21) and (1.15) at every
date — whenever the constant plan is (`π_{−1} = π̄`, `κ, σ ≠ 0`). -/
theorem pert_feasible {M : IModel} (hκ : M.κ ≠ 0) (hσ : M.σ ≠ 0) {πb xb ib : ℝ}
    (hpm : M.πm1 = πb)
    (hF : ∀ t, ASi M (fun _ => πb) (fun _ => xb) t ∧ ISi M (fun _ => πb) (fun _ => xb)
      (fun _ => ib) t) (ε : ℝ) (t : ℕ) :
    ASi M (fun t => πb + ε * dPi M.γ t) (fun t => xb + ε * dX M.β M.κ t) t ∧
      ISi M (fun t => πb + ε * dPi M.γ t) (fun t => xb + ε * dX M.β M.κ t)
        (fun t => ib + ε * dI M.β M.κ M.σ M.γ t) t := by
  obtain ⟨ha, hb⟩ := hF t
  unfold ASi at ha ⊢
  unfold ISi at hb ⊢
  have hl : lagged M.πm1 (fun t => πb + ε * dPi M.γ t) t =
      lagged M.πm1 (fun _ => πb) t + ε * lagged 0 (dPi M.γ) t := lag_pert M.πm1 ε _ _ t
  rw [hpm] at hl ha
  rw [hpm, hl]
  rw [lagged_const] at ha ⊢
  have p1 := pert_AS (β := M.β) (γ := M.γ) hκ t
  have p2 := pert_IS (β := M.β) (κ := M.κ) (γ := M.γ) hσ t
  refine ⟨?_, ?_⟩
  · linear_combination ha + ε * p1
  · linear_combination hb + ε * p2

/-! ### Discounted sums along the perturbation -/

/-- Woodford (2003), p. 484: `∑ βᵗ dπ_t = β²/(1 − βγ)`. -/
theorem dsum_dPi {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    dsum β (dPi γ) = β ^ 2 / (1 - β * γ) := by
  have hbg0 : 0 ≤ β * γ := mul_nonneg hβ0.le hγ0
  have hbg1 : β * γ < 1 := by nlinarith
  have hs := summable_dsum hβ0.le hβ1 (dPi_bdd hγ0 hγ1)
  unfold dsum
  rw [← hs.sum_add_tsum_nat_add 2]
  have e : (fun t => β ^ (t + 2) * dPi γ (t + 2)) = fun t => β ^ 2 * (β * γ) ^ t := by
    funext t
    simp only [dPi, show 2 ≤ t + 2 by omega, ↓reduceIte, Nat.add_sub_cancel]
    ring
  rw [e, tsum_mul_left, tsum_geometric_of_lt_one hbg0 hbg1]
  simp [dPi, Finset.sum_range_succ]
  ring

/-- Woodford (2003), p. 484: `∑ βᵗ dπ_{t+1} = β/(1 − βγ)`. -/
theorem dsum_dPi_succ {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    dsum β (fun t => dPi γ (t + 1)) = β / (1 - β * γ) := by
  have hbg1 : β * γ < 1 := by nlinarith
  rw [dsum_shift hβ0 hβ1 (dPi_bdd hγ0 hγ1) (fun t => rfl), dsum_dPi hβ0 hβ1 hγ0 hγ1]
  simp only [dPi, show ¬ 2 ≤ 0 by omega, ↓reduceIte, sub_zero]
  have : 1 - β * γ ≠ 0 := by linarith
  field_simp

/-- Woodford (2003), p. 484: `∑ βᵗ dx_t = 0`. -/
theorem dsum_dX {β κ : ℝ} (hκ : κ ≠ 0) : dsum β (dX β κ) = 0 := by
  rw [dsum_of_zero_from β 3 fun t ht => by
    simp only [dX, show t ≠ 1 by omega, show t ≠ 2 by omega, ↓reduceIte]]
  simp [Finset.sum_range_succ, dX]
  field_simp
  ring

/-- Woodford (2003), p. 484: `∑ βᵗ dx_{t+1} = 0`. -/
theorem dsum_dX_succ {β κ : ℝ} (hκ : κ ≠ 0) : dsum β (fun t => dX β κ (t + 1)) = 0 := by
  rw [dsum_of_zero_from β 2 fun t ht => by
    simp only [dX, show t + 1 ≠ 1 by omega, show t + 1 ≠ 2 by omega, ↓reduceIte]]
  simp [Finset.sum_range_succ, dX]
  field_simp
  ring

/-- Woodford (2003), p. 484: `∑ βᵗ di_t = β/(1 − βγ)`. -/
theorem dsum_dI {β κ σ γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hκ : κ ≠ 0) : dsum β (dI β κ σ γ) = β / (1 - β * γ) := by
  have e : dI β κ σ γ = fun t => dPi γ (t + 1) + σ⁻¹ * (dX β κ (t + 1) - dX β κ t) := by
    funext t; unfold dI; ring
  have hb : Bdd (fun t => σ⁻¹ * (dX β κ (t + 1) - dX β κ t)) :=
    (bdd_const σ⁻¹).mul ((dX_bdd β κ).shift.sub (dX_bdd β κ))
  rw [e, dsum_add hβ0.le hβ1 (dPi_bdd hγ0 hγ1).shift hb, dsum_mul_left,
    dsum_sub hβ0.le hβ1 (dX_bdd β κ).shift (dX_bdd β κ), dsum_dX_succ hκ, dsum_dX hκ,
    dsum_dPi_succ hβ0 hβ1 hγ0 hγ1]
  ring


/-! ### The loss along the perturbation and necessity -/

/-- Woodford (2003), p. 483: with zero multipliers the Lagrangian is half the loss. -/
theorem lagrI_zero (M : IModel) (π x i : ℕ → ℝ) :
    lagrI M (fun _ => 0) (fun _ => 0) 0 0 π x i = lossI M π x i / 2 := by
  unfold lagrI lossI initI
  have h : (fun t => periodLossI M π x i t / 2 + (fun _ => (0 : ℝ)) t * resISi M π x i t +
      (fun _ => (0 : ℝ)) t * resASi M π x t) = fun t => (1 / 2) * periodLossI M π x i t := by
    funext t; ring
  rw [h, dsum_mul_left]
  ring

/-- Woodford (2003), p. 484: the first-order coefficient of the loss along the perturbation,
`∑βᵗ[F^π_t dπ_t + F^x_t dx_t + F^i_t di_t]` with zero multipliers at the constant plan. -/
noncomputable def gradI (M : IModel) (πb xb ib : ℝ) : ℝ :=
  dsum M.β (fun t => focPiI M (fun _ => 0) (fun _ => 0) 0 0 (fun _ => πb) t * dPi M.γ t +
    focXI M (fun _ => 0) (fun _ => 0) 0 (fun _ => xb) t * dX M.β M.κ t +
    focII M (fun _ => 0) (fun _ => ib) t * dI M.β M.κ M.σ M.γ t)

/-- Woodford (2003), p. 484: the exact expansion of the loss along the perturbation,
`L(ȳ + εd) = L(ȳ) + 2ε G + ε² Q` with `Q = ∑βᵗ Q_t(d)` (`0 ≤ γ ≤ 1`). -/
theorem lossI_pert {M : IModel} (hβ0 : 0 < M.β) (hβ1 : M.β < 1) (hγ0 : 0 ≤ M.γ) (hγ1 : M.γ ≤ 1)
    (πb xb ib ε : ℝ) :
    lossI M (fun t => πb + ε * dPi M.γ t) (fun t => xb + ε * dX M.β M.κ t)
        (fun t => ib + ε * dI M.β M.κ M.σ M.γ t) =
      lossI M (fun _ => πb) (fun _ => xb) (fun _ => ib) + 2 * ε * gradI M πb xb ib +
        ε ^ 2 * dsum M.β (quadI M (dPi M.γ) (dX M.β M.κ) (dI M.β M.κ M.σ M.γ)) := by
  have he := lagrI_expand (M := M) (φ1 := fun _ => 0) (φ2 := fun _ => 0)
    (π := fun _ => πb) (x := fun _ => xb) (i := fun _ => ib) hβ0 hβ1 0 0 ε
    (bdd_const 0) (bdd_const 0) (bdd_const πb) (bdd_const xb) (bdd_const ib)
    (dPi_bdd hγ0 hγ1) (dX_bdd M.β M.κ) (dI_bdd (β := M.β) (κ := M.κ) (σ := M.σ) hγ0 hγ1)
  rw [lagrI_zero, lagrI_zero] at he
  unfold gradI
  linarith

/-- Woodford (2003), p. 484: at the constant plan (`π_{−1} = π̄`) with zero multipliers, the
first-order coefficient is `β/(1 − βγ) · [β(1 − γ)(1 − βγ)π̄ + λ_i(ı̄ − iᵐ)]`. -/
theorem gradI_eq {M : IModel} (hβ0 : 0 < M.β) (hβ1 : M.β < 1) (hγ0 : 0 ≤ M.γ) (hγ1 : M.γ ≤ 1)
    (hκ : M.κ ≠ 0) {πb xb ib : ℝ} (hpm : M.πm1 = πb) :
    gradI M πb xb ib = M.β / (1 - M.β * M.γ) *
      (M.β * (1 - M.γ) * (1 - M.β * M.γ) * πb + M.lami * (ib - M.im)) := by
  have hbg : 1 - M.β * M.γ ≠ 0 := by nlinarith
  have e : (fun t => focPiI M (fun _ => 0) (fun _ => 0) 0 0 (fun _ => πb) t * dPi M.γ t +
      focXI M (fun _ => 0) (fun _ => 0) 0 (fun _ => xb) t * dX M.β M.κ t +
      focII M (fun _ => 0) (fun _ => ib) t * dI M.β M.κ M.σ M.γ t) =
      fun t => ((1 - M.γ) * (1 - M.β * M.γ) * πb * dPi M.γ t +
        M.lam * (xb - M.xstar) * dX M.β M.κ t) +
        M.lami * (ib - M.im) * dI M.β M.κ M.σ M.γ t := by
    funext t
    simp only [focPiI, focXI, focII, hpm, lagged_const]
    ring
  have b1 : Bdd (fun t => (1 - M.γ) * (1 - M.β * M.γ) * πb * dPi M.γ t) :=
    (bdd_const _).mul (dPi_bdd hγ0 hγ1)
  have b2 : Bdd (fun t => M.lam * (xb - M.xstar) * dX M.β M.κ t) :=
    (bdd_const _).mul (dX_bdd M.β M.κ)
  have b3 : Bdd (fun t => M.lami * (ib - M.im) * dI M.β M.κ M.σ M.γ t) :=
    (bdd_const _).mul (dI_bdd hγ0 hγ1)
  unfold gradI
  rw [e, dsum_add hβ0.le hβ1 (b1.add b2) b3, dsum_add hβ0.le hβ1 b1 b2, dsum_mul_left,
    dsum_mul_left, dsum_mul_left, dsum_dPi hβ0 hβ1 hγ0 hγ1, dsum_dX hκ,
    dsum_dI hβ0 hβ1 hγ0 hγ1 hκ]
  field_simp
  ring

/-- **Necessity of the long-run inflation rate** (Woodford (2003), p. 484): with `π_{−1} = π̄`,
`0 < β < 1`, `0 ≤ γ ≤ 1`, `κ, σ ≠ 0`, if the feasible constant plan `(π̄, x̄, ı̄)` minimises the
loss among all bounded plans satisfying (1.21) and (1.15) with `π_0 = π̄`, `x_0 = x̄`, then the
steady-state condition `λ_i(ı̄ − iᵐ) = −β(1 − γ)(1 − βγ)π̄` holds. No multiplier is assumed. -/
theorem ss_ind_necessary {M : IModel} (hβ0 : 0 < M.β) (hβ1 : M.β < 1) (hγ0 : 0 ≤ M.γ)
    (hγ1 : M.γ ≤ 1) (hκ : M.κ ≠ 0) (hσ : M.σ ≠ 0) {πb xb ib : ℝ} (hpm : M.πm1 = πb)
    (hF : ∀ t, ASi M (fun _ => πb) (fun _ => xb) t ∧
      ISi M (fun _ => πb) (fun _ => xb) (fun _ => ib) t)
    (hopt : ∀ π x i : ℕ → ℝ, Bdd π → Bdd x → Bdd i → (∀ t, ASi M π x t ∧ ISi M π x i t) →
      π 0 = πb → x 0 = xb → lossI M (fun _ => πb) (fun _ => xb) (fun _ => ib) ≤ lossI M π x i) :
    SSCondI M πb ib := by
  set G := gradI M πb xb ib with hG
  set Q := dsum M.β (quadI M (dPi M.γ) (dX M.β M.κ) (dI M.β M.κ M.σ M.γ)) with hQ
  have key : ∀ ε : ℝ, 0 ≤ 2 * ε * G + ε ^ 2 * Q := by
    intro ε
    have h := hopt _ _ _ ((bdd_const πb).add ((bdd_const ε).mul (dPi_bdd hγ0 hγ1)))
      ((bdd_const xb).add ((bdd_const ε).mul (dX_bdd M.β M.κ)))
      ((bdd_const ib).add ((bdd_const ε).mul (dI_bdd (β := M.β) (κ := M.κ) (σ := M.σ) hγ0
        hγ1)))
      (pert_feasible hκ hσ hpm hF ε) (by simp [dPi]) (by simp [dX])
    rw [lossI_pert hβ0 hβ1 hγ0 hγ1] at h
    linarith
  have hG0 : G = 0 := by
    by_contra hne
    have hq : 0 < |Q| + 1 := by positivity
    have h := key (-G / (|Q| + 1))
    have hG2 : 0 < G ^ 2 := by positivity
    have hQle : Q ≤ |Q| := le_abs_self Q
    have e : 2 * (-G / (|Q| + 1)) * G + (-G / (|Q| + 1)) ^ 2 * Q =
        G ^ 2 / (|Q| + 1) ^ 2 * (-2 * (|Q| + 1) + Q) := by
      field_simp
    rw [e] at h
    have : -2 * (|Q| + 1) + Q < 0 := by linarith
    have := mul_neg_of_pos_of_neg (div_pos hG2 (pow_pos hq 2)) this
    linarith
  rw [hG, gradI_eq hβ0 hβ1 hγ0 hγ1 hκ hpm] at hG0
  have hbg : 0 < 1 - M.β * M.γ := by nlinarith
  have hpos : 0 < M.β / (1 - M.β * M.γ) := div_pos hβ0 hbg
  have h2 := (mul_eq_zero.mp hG0).resolve_left hpos.ne'
  unfold SSCondI
  linarith

/-- **The p. 484 steady state, necessary and sufficient** (Woodford (2003), p. 484): with
`π_{−1} = π̄`, `0 < β < 1`, `0 ≤ γ ≤ 1`, `κ, σ ≠ 0`, `λ, λ_i ≥ 0` and
`λ_i + β(1 − γ)(1 − βγ) ≠ 0`, the constant plan `(π̄, x̄, ı̄)` is feasible and minimises the loss
among all bounded feasible plans with `π_0 = π̄`, `x_0 = x̄` **iff**
`π̄ = −λ_i(r̄ − iᵐ)/(λ_i + β(1 − γ)(1 − βγ))`, `ı̄ = r̄ + π̄` and `κx̄ = (1 − β)(1 − γ)π̄`. -/
theorem ss_ind_timeless_iff {M : IModel} (hβ0 : 0 < M.β) (hβ1 : M.β < 1) (hγ0 : 0 ≤ M.γ)
    (hγ1 : M.γ ≤ 1) (hκ : M.κ ≠ 0) (hσ : M.σ ≠ 0) (hlam : 0 ≤ M.lam) (hli : 0 ≤ M.lami)
    (hD : M.lami + M.β * (1 - M.γ) * (1 - M.β * M.γ) ≠ 0) {πb xb ib : ℝ} (hpm : M.πm1 = πb) :
    ((∀ t, ASi M (fun _ => πb) (fun _ => xb) t ∧
        ISi M (fun _ => πb) (fun _ => xb) (fun _ => ib) t) ∧
      ∀ π x i : ℕ → ℝ, Bdd π → Bdd x → Bdd i → (∀ t, ASi M π x t ∧ ISi M π x i t) →
        π 0 = πb → x 0 = xb →
        lossI M (fun _ => πb) (fun _ => xb) (fun _ => ib) ≤ lossI M π x i) ↔
      πb = -(M.lami * (M.rbar - M.im)) / (M.lami + M.β * (1 - M.γ) * (1 - M.β * M.γ)) ∧
        ib = M.rbar + πb ∧ M.κ * xb = (1 - M.β) * (1 - M.γ) * πb := by
  constructor
  · rintro ⟨hF, hopt⟩
    have hss := ss_ind_necessary hβ0 hβ1 hγ0 hγ1 hκ hσ hpm hF hopt
    have hfoc := (focI_const_iff (xb := xb) hβ0.ne' hσ hκ hpm).mpr hss
    exact (ss_ind_iff hβ0.ne' hσ hκ hD hpm).mp ⟨hfoc, hF⟩
  · intro h
    obtain ⟨⟨c1, c2, hfoc⟩, hF⟩ := (ss_ind_iff hβ0.ne' hσ hκ hD hpm).mpr h
    exact ⟨hF, fun π x i hπ hx hi hF' h0 h0' =>
      ss_ind_optimal hβ0 hβ1 hlam hli hfoc hF hπ hx hi hF' h0 h0'⟩

end Woodford.GainsFromCommitment.TidyR5IndexationNecessity
