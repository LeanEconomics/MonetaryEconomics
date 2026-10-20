/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.ForwardSolution
import OptimalPolicyRules.QuadraticRoots
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Predetermined spending and pricing decisions

Woodford (2003), *Interest and Prices*, Chapter 8, §2.4, pp. 569–572: eqs. (2.28)–(2.34).

Prices and private spending are fixed `d ≥ 0` periods in advance. With quasi-differenced inflation
`π^{qd}_t = π_t − γπ_{t−1}` (2.8) the aggregate-supply relation is (2.28),
`π^{qd}_t = κ E_{t−d} x_t + β E_{t−d} π^{qd}_{t+1} + E_{t−d} u_t`, and the loss is (2.2)/(2.7).

Dates are `ℕ`; the commitment starts at a date `t0 ≥ 1` (so that date `t0 − 1` exists), the first
date the policy can affect is `t0 + d`, and all values at earlier dates are history. The welfare
criterion is `E_{t0} ∑_{t ≥ t0+d} βᵗ L_t` (the earlier terms are independent of policy, as in
(2.29)), a genuine infinite sum.

## Main results

* (2.29): `lagrangian_LIE`, `lagrangian_LIE_term` (the law of iterated expectations removes
  `E_{t−d}` inside the Lagrangian) and `hasDerivAt_lagr_q`, `hasDerivAt_lagr_x`,
  `foc_iff_deriv` (the FOCs
  (2.30)–(2.31) are the exact partial derivatives of (2.29)).
* **Lagrangian sufficiency** `welfare_diff` (exact welfare-difference formula), `welfare_le`,
  `t0_optimal` (FOCs with `φ_{t0−1} = 0` ⇒ optimal among all bounded feasible plans),
  `welfare_eq_imp` and `welfare_unique_pf` (uniqueness in mean square; exact under perfect
  foresight).
* Elimination of the multipliers: `tc_of_foc`, `foc_of_tc`, `tc232_iff` — (2.30)–(2.31) with the
  self-consistent initial multiplier are equivalent to (2.9) at every date `t ≥ t0 + d`, which is
  (2.32) at every decision date `t ≥ t0`; `tc232_projected` (footnote 23); **E16**
  `printed_eq232_fails` (the printed `γ_{t+d−1}` must be `γπ_{t+d−1}`).
* `eqm_unique`, `eqm_exists`: (2.28) together with (2.32) determines unique bounded equilibrium
  paths given the history (via the second-order workhorse `secondOrder_existsUnique` on the
  shifted expectation system `shift 𝔼 t0`); `eqm_timelesslyOptimal`: that equilibrium is
  optimal from a timeless perspective (`TimelesslyOptimal`); `eq232_optimal_rule` collects
  these; `t0_optimal_exists` (the `t0`-optimal commitment exists).
* (2.33)–(2.34): `IS_fcst_iff` (the IS relation only involves `E_{t−d} i_t`), `var_decomp`,
  `iLoss_decomp`, `fcst_improves` and `eq234_of_optimal` (**for any `λᵢ > 0` every optimal plan
  has `i_t = E_{t−d} i_t` in mean square**, and replacing `i` by `E_{t−d} i` never raises the
  loss), `fcst_i_formula` and `eq234_determines_i` (with (2.34) the path of `i` is pinned down by
  (2.33)).

The second-order workhorse is restated from the Woodford Chapter 3 project
(`NominalRigidities.StickyWages`); the quadratic-root facts are in `QuadraticRoots`.
-/

namespace Woodford.OptimalPolicyRules.InflTargetPredetermined

open Filter Topology QuadraticRoots

/-! ### Lags, the shifted expectation system and the second-order workhorse (restated) -/

/-- Woodford (2003), Ch. 3, (2.16)–(2.18), pp. 189–190: the lag with an explicit date-`(−1)`
value, `prev x₋₁ x 0 = x₋₁`, `prev x₋₁ x (k + 1) = x k` (restated). -/
def prev {X : Type*} (x0 : X) (x : ℕ → X) : ℕ → X
  | 0 => x0
  | k + 1 => x k

/-- Woodford (2003), Ch. 3, p. 190: `prev x₋₁ x 0 = x₋₁`. -/
@[simp] theorem prev_zero {X : Type*} (x0 : X) (x : ℕ → X) : prev x0 x 0 = x0 := rfl

/-- Woodford (2003), Ch. 3, p. 189: `prev x₋₁ x (k + 1) = x k`. -/
@[simp] theorem prev_succ {X : Type*} (x0 : X) (x : ℕ → X) (k : ℕ) :
    prev x0 x (k + 1) = x k := rfl

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), Ch. 8, p. 571: the expectation system seen from date `k` onward,
`E'_s = E_{k+s}`. A process whose date-`(k + d + s)` value is known at date `k + s` (a variable
predetermined `d` periods in advance) is adapted for `shift 𝔼 k` after re-dating by `k + d`. -/
def shift (k : ℕ) : ExpectationSystem Ω where
  E := fun s => 𝔼.E (k + s)
  const := fun s c => 𝔼.const (k + s) c
  mono := fun s _ _ h => 𝔼.mono (k + s) h
  tower := fun h x => 𝔼.tower (Nat.add_le_add_left h k) x
  known := fun h x => 𝔼.known (Nat.add_le_add_left h k) x

/-- Woodford (2003), Ch. 8, p. 571: `E'_s = E_{k+s}` for the shifted system. -/
@[simp] theorem shift_E (k s : ℕ) (x : Ω → ℝ) : (shift 𝔼 k).E s x = 𝔼.E (k + s) x := rfl

/-- Woodford (2003), Ch. 7, (2.29) / Ch. 3, (4.22): the workhorse
`β E_t ℓ_{t+1} − (1 + β + c) ℓ_t + ℓ_{t−1} = −z_t` for all `t ≥ 0`, with `ℓ_{−1} = ℓ₋₁`
(restated from the Chapter 3 project). -/
def SecondOrder (β c : ℝ) (ℓm1 : Ω → ℝ) (z ℓ : ℕ → Ω → ℝ) : Prop :=
  ∀ t, β • 𝔼.E t (ℓ (t + 1)) - (1 + β + c) • ℓ t + prev ℓm1 ℓ t = -z t

/-- Woodford (2003), Ch. 3, p. 231: the factorised form of the workhorse (restated). -/
theorem secondOrder_of_factor {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {ℓm1 : Ω → ℝ}
    {z ℓ e : ℕ → Ω → ℝ} (hℓa : 𝔼.Adapted ℓ)
    (hℓ : ∀ t, ℓ t = lam1 β c • prev ℓm1 ℓ t + e t)
    (he : ∀ t, e t = (lam2 β c)⁻¹ • 𝔼.E t (e (t + 1)) + (β * lam2 β c)⁻¹ • z t) :
    SecondOrder 𝔼 β c ℓm1 z ℓ := by
  intro t
  have hl2 : lam2 β c ≠ 0 := (lt_trans one_pos (lam1_lt_one_lt_lam2 hβ hc).2).ne'
  have hE : 𝔼.E t (ℓ (t + 1)) = lam1 β c • ℓ t + 𝔼.E t (e (t + 1)) := by
    rw [hℓ (t + 1), map_add, map_smul, prev_succ, hℓa t]
  rw [hE]
  funext ω
  have h1 := congrFun (he t) ω
  have h2 := congrFun (hℓ t) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.neg_apply] at h1 h2 ⊢
  have hp := beta_mul_prod hβ hc
  have hs := beta_mul_sum (c := c) hβ
  have h1' : β * 𝔼.E t (e (t + 1)) ω = β * lam2 β c * e t ω - z t ω := by
    rw [h1]
    field_simp
    ring
  linear_combination h1' - β * lam2 β c * h2 + ℓ t ω * hs - prev ℓm1 ℓ t ω * hp

/-- Woodford (2003), Ch. 3, p. 231: two bounded adapted solutions of the workhorse with the
same `ℓ₋₁` coincide (restated). -/
theorem secondOrder_unique {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {ℓm1 : Ω → ℝ}
    {z ℓ ℓ' : ℕ → Ω → ℝ} (h : SecondOrder 𝔼 β c ℓm1 z ℓ) (h' : SecondOrder 𝔼 β c ℓm1 z ℓ')
    (ha : 𝔼.Adapted ℓ) (ha' : 𝔼.Adapted ℓ') (hb : BoundedProc ℓ) (hb' : BoundedProc ℓ') :
    ℓ = ℓ' := by
  set d : ℕ → Ω → ℝ := fun t => ℓ t - ℓ' t with hd
  set e : ℕ → Ω → ℝ := fun t => d t - lam1 β c • prev 0 d t with he
  have hl2' := (lam1_lt_one_lt_lam2 hβ hc).2
  have hl2 : lam2 β c ≠ 0 := (lt_trans one_pos hl2').ne'
  have hprev : ∀ t, prev ℓm1 ℓ t - prev ℓm1 ℓ' t = prev 0 d t := by
    intro t; cases t <;> simp [hd]
  have hda : ∀ t, 𝔼.E t (d t) = d t := fun t => by simp [hd, map_sub, ha t, ha' t]
  have key : ∀ t, lam2 β c • e t = 𝔼.E t (e (t + 1)) := by
    intro t
    have hEd : 𝔼.E t (e (t + 1)) = 𝔼.E t (ℓ (t + 1)) - 𝔼.E t (ℓ' (t + 1)) - lam1 β c • d t := by
      change 𝔼.E t (d (t + 1) - lam1 β c • d t) = _
      rw [map_sub, map_smul, hda t]
      simp only [hd, map_sub]
    rw [hEd]
    funext ω
    have k1 := congrFun (h t) ω
    have k2 := congrFun (h' t) ω
    have k3 := congrFun (hprev t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.neg_apply] at k1 k2 k3
    have hp := beta_mul_prod hβ hc
    have hs := beta_mul_sum (c := c) hβ
    have hX : β * (lam2 β c * (d t ω - lam1 β c * prev 0 d t ω) - (𝔼.E t (ℓ (t + 1)) ω
        - 𝔼.E t (ℓ' (t + 1)) ω - lam1 β c * d t ω)) = 0 := by
      rw [← k3]
      simp only [hd, Pi.sub_apply]
      linear_combination (ℓ t ω - ℓ' t ω) * hs
        - (prev ℓm1 ℓ t ω - prev ℓm1 ℓ' t ω) * hp - (k1 - k2)
    have hX' := (mul_eq_zero.mp hX).resolve_left hβ.ne'
    simp only [he, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hfe : ∀ t, e t = (lam2 β c)⁻¹ • 𝔼.E t (e (t + 1)) + 0 := fun t => by
    rw [← key t, smul_smul, inv_mul_cancel₀ hl2, one_smul, add_zero]
  have hebd : BoundedProc e := by
    obtain ⟨M, hM⟩ := hb
    obtain ⟨M', hM'⟩ := hb'
    refine ⟨(M + M') + |lam1 β c| * (M + M'), fun t ω => ?_⟩
    have hdb : ∀ s ω, |d s ω| ≤ M + M' := fun s ω => by
      simp only [hd, Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (hM s ω) (hM' s ω))
    have hpb : |prev 0 d t ω| ≤ M + M' := by
      cases t with
      | zero =>
        simp only [prev_zero, Pi.zero_apply, abs_zero]
        exact le_trans (abs_nonneg _) (hdb 0 ω)
      | succ t => exact hdb t ω
    simp only [he, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add (hdb t ω) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hpb (abs_nonneg _)
  have ha2 : |(lam2 β c)⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (lt_trans one_pos hl2')]
    exact inv_lt_one_of_one_lt₀ hl2'
  have he0 : e = 0 := 𝔼.forward_unique ha2 hfe (fun t => by simp) hebd ⟨0, fun _ _ => by simp⟩
  have hd0 : ∀ t, d t = 0 := by
    intro t
    induction t with
    | zero =>
      have := congrFun he0 0
      simpa [he] using this
    | succ t ih =>
      have := congrFun he0 (t + 1)
      simp only [he, prev_succ, ih, smul_zero, sub_zero, Pi.zero_apply] at this
      exact this
  funext t ω
  have := congrFun (hd0 t) ω
  simp only [hd, Pi.sub_apply, Pi.zero_apply] at this
  linarith

/-- Woodford (2003), Ch. 3, eq. (4.22), p. 231: the forward component
`β⁻¹ ∑ⱼ λ₂^{−j−1} E_t z_{t+j}` (restated). -/
noncomputable def fwdPart (β c : ℝ) (z : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  𝔼.forwardSeries (lam2 β c)⁻¹ (fun t => (β * lam2 β c)⁻¹ • z t)

/-- Woodford (2003), Ch. 3, eq. (4.22), p. 231: the solution
`ℓ_t = λ₁ ℓ_{t−1} + β⁻¹ ∑ⱼ λ₂^{−j−1} E_t z_{t+j}` (restated). -/
noncomputable def secondOrderSol (β c : ℝ) (ℓm1 : Ω → ℝ) (z : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => lam1 β c • ℓm1 + fwdPart 𝔼 β c z 0
  | t + 1 => lam1 β c • secondOrderSol β c ℓm1 z t + fwdPart 𝔼 β c z (t + 1)

/-- Woodford (2003), Ch. 3, eq. (4.22), p. 231: `ℓ_t = λ₁ ℓ_{t−1} + F_t` (restated). -/
theorem secondOrderSol_eq (β c : ℝ) (ℓm1 : Ω → ℝ) (z : ℕ → Ω → ℝ) (t : ℕ) :
    secondOrderSol 𝔼 β c ℓm1 z t =
      lam1 β c • prev ℓm1 (secondOrderSol 𝔼 β c ℓm1 z) t + fwdPart 𝔼 β c z t := by
  cases t <;> rfl

/-- Woodford (2003), Ch. 3, eq. (4.22), p. 231 (**existence and uniqueness**, restated): for
`β > 0`, `c > 0`, bounded adapted forcing and a bounded `ℓ₋₁` known at date 0, (4.22) is the
unique bounded adapted solution of the workhorse. -/
theorem secondOrder_existsUnique {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {z : ℕ → Ω → ℝ}
    (hz : BoundedProc z) (hza : 𝔼.Adapted z) {ℓm1 : Ω → ℝ} {K : ℝ}
    (hK : ∀ ω, |ℓm1 ω| ≤ K) (hm0 : 𝔼.E 0 ℓm1 = ℓm1) :
    SecondOrder 𝔼 β c ℓm1 z (secondOrderSol 𝔼 β c ℓm1 z) ∧
      BoundedProc (secondOrderSol 𝔼 β c ℓm1 z) ∧ 𝔼.Adapted (secondOrderSol 𝔼 β c ℓm1 z) ∧
      ∀ ℓ, SecondOrder 𝔼 β c ℓm1 z ℓ → BoundedProc ℓ → 𝔼.Adapted ℓ →
        ℓ = secondOrderSol 𝔼 β c ℓm1 z := by
  obtain ⟨Mz, hMz⟩ := hz
  have hl2 : 1 < lam2 β c := (lam1_lt_one_lt_lam2 hβ hc).2
  have ha : |(lam2 β c)⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (lt_trans one_pos hl2)]
    exact inv_lt_one_of_one_lt₀ hl2
  set u : ℕ → Ω → ℝ := fun t => (β * lam2 β c)⁻¹ • z t with hu
  have hub : ∀ t ω, |u t ω| ≤ |(β * lam2 β c)⁻¹| * Mz := fun t ω => by
    simp only [hu, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hMz t ω) (abs_nonneg _)
  have hua : 𝔼.Adapted u := fun t => by simp only [hu, map_smul, hza t]
  have hFs := ForwardSolution.forwardSeries_solves_abs 𝔼 ha hub hua
  obtain ⟨BF, hBF⟩ := ForwardSolution.forwardSeries_bounded_abs 𝔼 ha hub
  have hFa := ForwardSolution.forwardSeries_adapted_abs 𝔼 ha hub
  set ℓ := secondOrderSol 𝔼 β c ℓm1 z with hℓdef
  have hl1 := lam1_pos hβ hc
  have hl1' := (lam1_lt_one_lt_lam2 hβ hc).1
  have hadapt : 𝔼.Adapted ℓ := by
    intro t
    induction t with
    | zero =>
      change 𝔼.E 0 (lam1 β c • ℓm1 + fwdPart 𝔼 β c z 0) = _
      rw [map_add, map_smul, hm0]
      exact congrArg _ (hFa 0)
    | succ t ih =>
      change 𝔼.E (t + 1) (lam1 β c • ℓ t + fwdPart 𝔼 β c z (t + 1))
        = lam1 β c • ℓ t + fwdPart 𝔼 β c z (t + 1)
      rw [map_add, map_smul, ← ih, 𝔼.known (Nat.le_succ t), ih]
      congr 1
      exact hFa (t + 1)
  have hbdd : BoundedProc ℓ := by
    set B := max K (BF / (1 - lam1 β c)) with hB
    have hKB : K ≤ B := le_max_left _ _
    have hFB : BF ≤ (1 - lam1 β c) * B := by
      have := le_max_right K (BF / (1 - lam1 β c))
      rw [← hB, div_le_iff₀ (by linarith)] at this
      linarith
    refine ⟨B, fun t => ?_⟩
    induction t with
    | zero =>
      intro ω
      have e : ℓ 0 ω = lam1 β c * ℓm1 ω + 𝔼.forwardSeries (lam2 β c)⁻¹ u 0 ω := rfl
      rw [e]
      have h1 : |lam1 β c * ℓm1 ω| ≤ lam1 β c * B := by
        rw [abs_mul, abs_of_pos hl1]
        exact mul_le_mul_of_nonneg_left ((hK ω).trans hKB) hl1.le
      calc |lam1 β c * ℓm1 ω + 𝔼.forwardSeries (lam2 β c)⁻¹ u 0 ω|
          ≤ |lam1 β c * ℓm1 ω| + |𝔼.forwardSeries (lam2 β c)⁻¹ u 0 ω| := abs_add_le _ _
        _ ≤ lam1 β c * B + BF := add_le_add h1 (hBF 0 ω)
        _ ≤ B := by linarith
    | succ t ih =>
      intro ω
      have e : ℓ (t + 1) ω = lam1 β c * ℓ t ω + 𝔼.forwardSeries (lam2 β c)⁻¹ u (t + 1) ω := rfl
      rw [e]
      have h1 : |lam1 β c * ℓ t ω| ≤ lam1 β c * B := by
        rw [abs_mul, abs_of_pos hl1]
        exact mul_le_mul_of_nonneg_left (ih ω) hl1.le
      calc |lam1 β c * ℓ t ω + 𝔼.forwardSeries (lam2 β c)⁻¹ u (t + 1) ω|
          ≤ |lam1 β c * ℓ t ω| + |𝔼.forwardSeries (lam2 β c)⁻¹ u (t + 1) ω| := abs_add_le _ _
        _ ≤ lam1 β c * B + BF := add_le_add h1 (hBF (t + 1) ω)
        _ ≤ B := by linarith
  have hsol : SecondOrder 𝔼 β c ℓm1 z ℓ :=
    secondOrder_of_factor 𝔼 hβ hc hadapt (e := 𝔼.forwardSeries (lam2 β c)⁻¹ u)
      (fun t => secondOrderSol_eq 𝔼 β c ℓm1 z t) (fun t => hFs t)
  exact ⟨hsol, hbdd, hadapt, fun ℓ' h' hb' ha' =>
    secondOrder_unique 𝔼 hβ hc h' hsol ha' hadapt hb' hbdd⟩

/-! ### The model (2.28), the loss (2.7) and the welfare criterion (2.29) -/

/-- Woodford (2003), eq. (2.8), p. 562: quasi-differenced inflation `π^{qd}_t = π_t − γπ_{t−1}`. -/
def qd (γ : ℝ) (π : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := π t - γ • π (t - 1)

/-- Woodford (2003), eq. (2.8), p. 562, pointwise. -/
theorem qd_apply (γ : ℝ) (π : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    qd γ π t ω = π t ω - γ * π (t - 1) ω := rfl

/-- Woodford (2003), eq. (2.8), p. 562: `π^{qd}_{t+1} = π_{t+1} − γπ_t`. -/
theorem qd_succ (γ : ℝ) (π : ℕ → Ω → ℝ) (t : ℕ) : qd γ π (t + 1) = π (t + 1) - γ • π t := by
  simp [qd]

/-- Woodford (2003), eq. (2.28), p. 570: the aggregate-supply relation with `d`-period
predetermination, `π_t − γπ_{t−1} = κ E_{t−d} x_t + β E_{t−d}(π_{t+1} − γπ_t) + E_{t−d} u_t`,
imposed at every date `t ≥ t0 + d` (the dates the commitment made at `t0` can affect). -/
def AS (κ β γ : ℝ) (d t0 : ℕ) (u π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t, t0 + d ≤ t → qd γ π t =
    κ • 𝔼.E (t - d) (x t) + β • 𝔼.E (t - d) (qd γ π (t + 1)) + 𝔼.E (t - d) (u t)

/-- Woodford (2003), p. 570: a variable is predetermined `d` periods in advance: its date-`t`
value is known at date `t − d` (for the dates `t ≥ t0 + d` chosen under the commitment). -/
def Predet (d t0 : ℕ) (y : ℕ → Ω → ℝ) : Prop := ∀ t, t0 + d ≤ t → 𝔼.E (t - d) (y t) = y t

/-- Woodford (2003), eqs. (2.7) and (2.29), pp. 562, 570: the period loss
`½(π^{qd}_t)² + (λ/2)(x_t − x*)²`. -/
noncomputable def loss (γ lam xs : ℝ) (π x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => 1 / 2 * qd γ π t ω ^ 2 + lam / 2 * (x t ω - xs) ^ 2

/-- Woodford (2003), eqs. (2.2) and (2.29), pp. 560, 570: the expected discounted loss
`E_{t0} ∑_{t ≥ t0+d} βᵗ L_t` (terms before `t0 + d` are independent of policy and dropped). -/
noncomputable def welfare (β γ lam xs : ℝ) (d t0 : ℕ) (π x : ℕ → Ω → ℝ) : Ω → ℝ :=
  𝔼.E t0 (fun ω => ∑' n, β ^ (t0 + d + n) * loss γ lam xs π x (t0 + d + n) ω)

/-- Woodford (2003), eqs. (2.30)–(2.31), pp. 570–571: the first-order conditions
`π^{qd}_t + φ_{t−d} − φ_{t−d−1} = 0` and `λ(x_t − x*) − κφ_{t−d} = 0` for `t ≥ t0 + d`. -/
def FOC (κ γ lam xs : ℝ) (d t0 : ℕ) (π x φ : ℕ → Ω → ℝ) : Prop :=
  ∀ t, t0 + d ≤ t → ∀ ω, qd γ π t ω + φ (t - d) ω - φ (t - d - 1) ω = 0 ∧
    lam * (x t ω - xs) - κ * φ (t - d) ω = 0

/-- Woodford (2003), p. 570: the loss of a deviation, `½(Δπ^{qd}_t)² + (λ/2)(Δx_t)²`. -/
noncomputable def devLoss (γ lam : ℝ) (π x π' x' : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => 1 / 2 * (qd γ π' t ω - qd γ π t ω) ^ 2 + lam / 2 * (x' t ω - x t ω) ^ 2

/-- Woodford (2003), eq. (2.8): `π^{qd}` of a bounded process is bounded. -/
theorem qd_bounded {γ : ℝ} {π : ℕ → Ω → ℝ} (h : BoundedProc π) : BoundedProc (qd γ π) := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M + |γ| * M, fun t ω => ?_⟩
  rw [qd_apply]
  calc |π t ω - γ * π (t - 1) ω| ≤ |π t ω| + |γ * π (t - 1) ω| := abs_sub _ _
    _ ≤ M + |γ| * M := by
      rw [abs_mul]
      exact add_le_add (hM t ω) (mul_le_mul_of_nonneg_left (hM _ ω) (abs_nonneg γ))

/-- Woodford (2003), eq. (2.7): the period loss of bounded processes is bounded. -/
theorem loss_bounded (γ lam xs : ℝ) {π x : ℕ → Ω → ℝ} (hπ : BoundedProc π)
    (hx : BoundedProc x) : ∃ M, ∀ t ω, |loss γ lam xs π x t ω| ≤ M := by
  obtain ⟨Q, hQ⟩ := qd_bounded (γ := γ) hπ
  obtain ⟨X, hX⟩ := hx
  refine ⟨1 / 2 * Q ^ 2 + |lam| / 2 * (X + |xs|) ^ 2, fun t ω => ?_⟩
  have h2 : |x t ω - xs| ≤ X + |xs| := (abs_sub _ _).trans (add_le_add (hX t ω) le_rfl)
  have e1 : qd γ π t ω ^ 2 ≤ Q ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) (hQ t ω) 2
    rwa [sq_abs] at this
  have e2 : (x t ω - xs) ^ 2 ≤ (X + |xs|) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) h2 2
    rwa [sq_abs] at this
  unfold loss
  calc |1 / 2 * qd γ π t ω ^ 2 + lam / 2 * (x t ω - xs) ^ 2|
      ≤ |1 / 2 * qd γ π t ω ^ 2| + |lam / 2 * (x t ω - xs) ^ 2| := abs_add_le _ _
    _ = 1 / 2 * qd γ π t ω ^ 2 + |lam| / 2 * (x t ω - xs) ^ 2 := by
      rw [abs_of_nonneg (by positivity), abs_mul, abs_div, abs_two,
        abs_of_nonneg (sq_nonneg (x t ω - xs))]
    _ ≤ 1 / 2 * Q ^ 2 + |lam| / 2 * (X + |xs|) ^ 2 := by gcongr

/-- Woodford (2003), p. 570: geometric weights `β^{T+n}` make a bounded sequence summable. -/
theorem summable_weighted {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (T : ℕ) {g : ℕ → ℝ}
    (hg : ∀ n, |g n| ≤ M) : Summable (fun n => β ^ (T + n) * g n) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right M)
    (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 _)]
  have hb : β ^ (T + n) ≤ β ^ n := pow_le_pow_of_le_one hβ0 hβ1.le (by omega)
  exact mul_le_mul hb (hg n) (abs_nonneg _) (pow_nonneg hβ0 _)

/-- Woodford (2003), eq. (2.29), p. 570: the welfare criterion is the series of discounted
expected period losses (`E_{t0}` commutes with the geometrically dominated series). -/
theorem welfare_apply {β γ lam xs : ℝ} {d t0 : ℕ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {π x : ℕ → Ω → ℝ} (hπ : BoundedProc π) (hx : BoundedProc x) (ω : Ω) :
    welfare 𝔼 β γ lam xs d t0 π x ω =
      ∑' n, β ^ (t0 + d + n) * 𝔼.E t0 (loss γ lam xs π x (t0 + d + n)) ω := by
  obtain ⟨M, hM⟩ := loss_bounded γ lam xs hπ hx
  have hf : ∀ n ω', |β ^ (t0 + d + n) * loss γ lam xs π x (t0 + d + n) ω'| ≤ β ^ n * M := by
    intro n ω'
    rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 _)]
    have hb : β ^ (t0 + d + n) ≤ β ^ n := pow_le_pow_of_le_one hβ0 hβ1.le (by omega)
    exact mul_le_mul hb (hM _ _) (abs_nonneg _) (pow_nonneg hβ0 _)
  have h := 𝔼.E_tsum hβ0 hβ1 hf t0 ω
  unfold welfare
  rw [h]
  refine tsum_congr fun n => ?_
  change 𝔼.E t0 (β ^ (t0 + d + n) • loss γ lam xs π x (t0 + d + n)) ω = _
  rw [map_smul]
  rfl

/-- Woodford (2003), (2.28) for two plans: the deviation of quasi-differenced inflation obeys
`Δπ^{qd}_t = κ Δx_t + β E_{t−d} Δπ^{qd}_{t+1}` (the shock cancels; `x` is predetermined). -/
theorem as_diff {κ β γ : ℝ} {d t0 : ℕ} {u π x π' x' : ℕ → Ω → ℝ}
    (hAS : AS 𝔼 κ β γ d t0 u π x) (hAS' : AS 𝔼 κ β γ d t0 u π' x')
    (hPx : Predet 𝔼 d t0 x) (hPx' : Predet 𝔼 d t0 x') {t : ℕ} (ht : t0 + d ≤ t) (ω : Ω) :
    qd γ π' t ω - qd γ π t ω = κ * (x' t ω - x t ω) +
      β * 𝔼.E (t - d) (qd γ π' (t + 1) - qd γ π (t + 1)) ω := by
  have h1 := congrFun (hAS t ht) ω
  have h2 := congrFun (hAS' t ht) ω
  rw [hPx t ht] at h1
  rw [hPx' t ht] at h2
  rw [map_sub]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h1 h2 ⊢
  rw [h1, h2]
  ring

/-- Woodford (2003), (2.29)–(2.31), p. 570: the per-date welfare identity behind Lagrangian
sufficiency. Writing `Δ_t = π'^{qd}_t − π^{qd}_t`, the FOCs (2.30)–(2.31) and (2.28) give
`E_{t0}[L'_t − L_t] = E_{t0}[φ_{t−d−1}Δ_t] − β E_{t0}[φ_{t−d}Δ_{t+1}] + E_{t0}[devLoss_t]`. -/
theorem E_loss_diff {β κ γ lam xs : ℝ} {d t0 : ℕ} (hPO : 𝔼.PullOut)
    {u π x π' x' φ : ℕ → Ω → ℝ}
    (hAS : AS 𝔼 κ β γ d t0 u π x) (hAS' : AS 𝔼 κ β γ d t0 u π' x')
    (hPx : Predet 𝔼 d t0 x) (hPx' : Predet 𝔼 d t0 x')
    (hFOC : FOC κ γ lam xs d t0 π x φ) (hφa : ∀ s, t0 ≤ s → 𝔼.E s (φ s) = φ s) (n : ℕ) :
    𝔼.E t0 (loss γ lam xs π' x' (t0 + d + n)) - 𝔼.E t0 (loss γ lam xs π x (t0 + d + n)) =
      𝔼.E t0 (φ (t0 + n - 1) * (qd γ π' (t0 + d + n) - qd γ π (t0 + d + n)))
      - β • 𝔼.E t0 (φ (t0 + n) * (qd γ π' (t0 + d + n + 1) - qd γ π (t0 + d + n + 1)))
      + 𝔼.E t0 (devLoss γ lam π x π' x' (t0 + d + n)) := by
  set t := t0 + d + n with htdef
  have ht : t0 + d ≤ t := by omega
  have htd : t - d = t0 + n := by omega
  set Δ1 : Ω → ℝ := qd γ π' (t + 1) - qd γ π (t + 1) with hΔ1
  have hfun : (fun ω => loss γ lam xs π' x' t ω - loss γ lam xs π x t ω) =
      φ (t0 + n - 1) * (qd γ π' t - qd γ π t) - β • (φ (t0 + n) * 𝔼.E (t0 + n) Δ1)
      + devLoss γ lam π x π' x' t := by
    funext ω
    obtain ⟨f1, f2⟩ := hFOC t ht ω
    rw [htd] at f1 f2
    have hd := as_diff 𝔼 hAS hAS' hPx hPx' ht ω
    rw [htd] at hd
    simp only [loss, devLoss, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply,
      smul_eq_mul]
    linear_combination (qd γ π' t ω - qd γ π t ω) * f1 + (x' t ω - x t ω) * f2
      - φ (t0 + n) ω * hd
  have hpo : φ (t0 + n) * 𝔼.E (t0 + n) Δ1 = 𝔼.E (t0 + n) (φ (t0 + n) * Δ1) :=
    (hPO (t0 + n) _ _ (hφa _ (by omega))).symm
  have htow : 𝔼.E t0 (𝔼.E (t0 + n) (φ (t0 + n) * Δ1)) = 𝔼.E t0 (φ (t0 + n) * Δ1) :=
    𝔼.tower (by omega) _
  rw [← map_sub]
  change 𝔼.E t0 (fun ω => loss γ lam xs π' x' t ω - loss γ lam xs π x t ω) = _
  rw [hfun, hpo, map_add, map_sub, map_smul, htow]

/-- Woodford (2003), (2.29)–(2.31), pp. 570–571 (**the welfare-difference formula**): for a
plan `(π, x)` satisfying (2.28) and the FOCs with a bounded multiplier process `φ`, and any other
bounded plan `(π', x')` satisfying (2.28) with predetermined `x'`,
`W' − W = β^{t0+d} E_{t0}[φ_{t0−1}(π'^{qd}_{t0+d} − π^{qd}_{t0+d})]
  + ∑ₙ β^{t0+d+n} E_{t0}[½(Δπ^{qd})² + (λ/2)(Δx)²]`
(summation by parts of the Lagrangian; the series telescopes because `β < 1` and everything is
bounded). -/
theorem welfare_diff {β κ γ lam xs : ℝ} {d t0 : ℕ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hPO : 𝔼.PullOut) {u π x π' x' φ : ℕ → Ω → ℝ}
    (hAS : AS 𝔼 κ β γ d t0 u π x) (hAS' : AS 𝔼 κ β γ d t0 u π' x')
    (hPx : Predet 𝔼 d t0 x) (hPx' : Predet 𝔼 d t0 x')
    (hFOC : FOC κ γ lam xs d t0 π x φ) (hφa : ∀ s, t0 ≤ s → 𝔼.E s (φ s) = φ s)
    (hπ : BoundedProc π) (hx : BoundedProc x) (hπ' : BoundedProc π') (hx' : BoundedProc x')
    (hφ : BoundedProc φ) (ω : Ω) :
    welfare 𝔼 β γ lam xs d t0 π' x' ω - welfare 𝔼 β γ lam xs d t0 π x ω =
      β ^ (t0 + d) * 𝔼.E t0 (φ (t0 - 1) * (qd γ π' (t0 + d) - qd γ π (t0 + d))) ω +
      ∑' n, β ^ (t0 + d + n) * 𝔼.E t0 (devLoss γ lam π x π' x' (t0 + d + n)) ω := by
  rw [welfare_apply 𝔼 hβ0 hβ1 hπ' hx', welfare_apply 𝔼 hβ0 hβ1 hπ hx]
  obtain ⟨M, hM⟩ := loss_bounded γ lam xs hπ hx
  obtain ⟨M', hM'⟩ := loss_bounded γ lam xs hπ' hx'
  obtain ⟨Q, hQ⟩ := qd_bounded (γ := γ) hπ
  obtain ⟨Q', hQ'⟩ := qd_bounded (γ := γ) hπ'
  obtain ⟨X, hX⟩ := hx
  obtain ⟨X', hX'⟩ := hx'
  obtain ⟨P, hP⟩ := hφ
  set T := t0 + d with hT
  have hsA : Summable (fun n => β ^ (T + n) * 𝔼.E t0 (loss γ lam xs π' x' (T + n)) ω) :=
    summable_weighted hβ0 hβ1 T (fun n => 𝔼.abs_E_le (hM' _) t0 ω)
  have hsB : Summable (fun n => β ^ (T + n) * 𝔼.E t0 (loss γ lam xs π x (T + n)) ω) :=
    summable_weighted hβ0 hβ1 T (fun n => 𝔼.abs_E_le (hM _) t0 ω)
  set a : ℕ → ℝ := fun n => 𝔼.E t0 (φ (t0 + n - 1) * (qd γ π' (T + n) - qd γ π (T + n))) ω
    with ha
  set D : ℕ → ℝ := fun n => 𝔼.E t0 (devLoss γ lam π x π' x' (T + n)) ω with hD
  set b : ℕ → ℝ := fun n => β ^ (T + n) * a n with hb
  have hab : ∀ n, |a n| ≤ P * (Q' + Q) := by
    intro n
    refine 𝔼.abs_E_le (fun ω' => ?_) t0 ω
    simp only [Pi.mul_apply, Pi.sub_apply, abs_mul]
    exact mul_le_mul (hP _ ω') ((abs_sub _ _).trans (add_le_add (hQ' _ ω') (hQ _ ω')))
      (abs_nonneg _) ((abs_nonneg _).trans (hP 0 ω'))
  have hDb : ∀ n, |D n| ≤ 1 / 2 * (Q' + Q) ^ 2 + |lam| / 2 * (X' + X) ^ 2 := by
    intro n
    refine 𝔼.abs_E_le (fun ω' => ?_) t0 ω
    have h1 : |qd γ π' (T + n) ω' - qd γ π (T + n) ω'| ≤ Q' + Q :=
      (abs_sub _ _).trans (add_le_add (hQ' _ ω') (hQ _ ω'))
    have h2 : |x' (T + n) ω' - x (T + n) ω'| ≤ X' + X :=
      (abs_sub _ _).trans (add_le_add (hX' _ ω') (hX _ ω'))
    have e1 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    have e2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
    rw [sq_abs] at e1 e2
    simp only [devLoss]
    calc |1 / 2 * (qd γ π' (T + n) ω' - qd γ π (T + n) ω') ^ 2
          + lam / 2 * (x' (T + n) ω' - x (T + n) ω') ^ 2|
        ≤ |1 / 2 * (qd γ π' (T + n) ω' - qd γ π (T + n) ω') ^ 2|
          + |lam / 2 * (x' (T + n) ω' - x (T + n) ω') ^ 2| := abs_add_le _ _
      _ = 1 / 2 * (qd γ π' (T + n) ω' - qd γ π (T + n) ω') ^ 2
          + |lam| / 2 * (x' (T + n) ω' - x (T + n) ω') ^ 2 := by
        rw [abs_of_nonneg (by positivity), abs_mul, abs_div, abs_two,
          abs_of_nonneg (sq_nonneg (x' (T + n) ω' - x (T + n) ω'))]
      _ ≤ 1 / 2 * (Q' + Q) ^ 2 + |lam| / 2 * (X' + X) ^ 2 := by gcongr
  have hsb : Summable b := summable_weighted hβ0 hβ1 T hab
  have hsb1 : Summable (fun n => b (n + 1)) := (summable_nat_add_iff 1).mpr hsb
  have hsD : Summable (fun n => β ^ (T + n) * D n) := summable_weighted hβ0 hβ1 T hDb
  have hterm : ∀ n, β ^ (T + n) * 𝔼.E t0 (loss γ lam xs π' x' (T + n)) ω
      - β ^ (T + n) * 𝔼.E t0 (loss γ lam xs π x (T + n)) ω
      = (b n - b (n + 1)) + β ^ (T + n) * D n := by
    intro n
    have h := congrFun (E_loss_diff 𝔼 hPO hAS hAS' hPx hPx' hFOC hφa n) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
    have hn : t0 + (n + 1) - 1 = t0 + n := by omega
    simp only [hb, ha, hD, hn]
    rw [show T + (n + 1) = T + n + 1 by omega, pow_succ]
    rw [← mul_sub, h]
    ring
  rw [← hsA.tsum_sub hsB, tsum_congr hterm, (hsb.sub hsb1).tsum_add hsD,
    hsb.tsum_sub hsb1, hsb.tsum_eq_zero_add]
  simp only [hb, ha, add_zero]
  ring

/-- Woodford (2003), pp. 570–571 (**Lagrangian sufficiency**): under the hypotheses of
`welfare_diff`, if the boundary term vanishes and `λ ≥ 0`, the plan satisfying the FOCs has
weakly lower expected discounted loss than any other bounded feasible plan. -/
theorem welfare_le {β κ γ lam xs : ℝ} {d t0 : ℕ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hlam : 0 ≤ lam)
    (hPO : 𝔼.PullOut) {u π x π' x' φ : ℕ → Ω → ℝ}
    (hAS : AS 𝔼 κ β γ d t0 u π x) (hAS' : AS 𝔼 κ β γ d t0 u π' x')
    (hPx : Predet 𝔼 d t0 x) (hPx' : Predet 𝔼 d t0 x')
    (hFOC : FOC κ γ lam xs d t0 π x φ) (hφa : ∀ s, t0 ≤ s → 𝔼.E s (φ s) = φ s)
    (hπ : BoundedProc π) (hx : BoundedProc x) (hπ' : BoundedProc π') (hx' : BoundedProc x')
    (hφ : BoundedProc φ)
    (hbd : 𝔼.E t0 (φ (t0 - 1) * (qd γ π' (t0 + d) - qd γ π (t0 + d))) = 0) (ω : Ω) :
    welfare 𝔼 β γ lam xs d t0 π x ω ≤ welfare 𝔼 β γ lam xs d t0 π' x' ω := by
  have h := welfare_diff 𝔼 hβ0 hβ1 hPO hAS hAS' hPx hPx' hFOC hφa hπ hx hπ' hx' hφ ω
  rw [hbd, Pi.zero_apply, mul_zero, zero_add] at h
  have hnn : 0 ≤ ∑' n, β ^ (t0 + d + n) * 𝔼.E t0 (devLoss γ lam π x π' x' (t0 + d + n)) ω := by
    refine tsum_nonneg fun n => mul_nonneg (pow_nonneg hβ0 _) ?_
    have h0 : (0 : Ω → ℝ) ≤ devLoss γ lam π x π' x' (t0 + d + n) := fun ω' => by
      simp only [Pi.zero_apply, devLoss]
      positivity
    have := 𝔼.mono t0 h0 ω
    simpa using this
  linarith

/-- Woodford (2003), p. 570: the optimal commitment chosen at `t0` (`t0`-optimality). If the
FOCs hold with the initial multiplier `φ_{t0−1} = 0` (no constraint binds before the commitment),
the plan minimises the expected discounted loss among **all** bounded feasible plans. -/
theorem t0_optimal {β κ γ lam xs : ℝ} {d t0 : ℕ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hlam : 0 ≤ lam)
    (hPO : 𝔼.PullOut) {u π x φ : ℕ → Ω → ℝ}
    (hAS : AS 𝔼 κ β γ d t0 u π x) (hPx : Predet 𝔼 d t0 x)
    (hFOC : FOC κ γ lam xs d t0 π x φ) (hφa : ∀ s, t0 ≤ s → 𝔼.E s (φ s) = φ s)
    (hφ0 : φ (t0 - 1) = 0)
    (hπ : BoundedProc π) (hx : BoundedProc x) (hφ : BoundedProc φ)
    {π' x' : ℕ → Ω → ℝ} (hAS' : AS 𝔼 κ β γ d t0 u π' x') (hPx' : Predet 𝔼 d t0 x')
    (hπ' : BoundedProc π') (hx' : BoundedProc x') (ω : Ω) :
    welfare 𝔼 β γ lam xs d t0 π x ω ≤ welfare 𝔼 β γ lam xs d t0 π' x' ω :=
  welfare_le 𝔼 hβ0 hβ1 hlam hPO hAS hAS' hPx hPx' hFOC hφa hπ hx hπ' hx' hφ
    (by rw [hφ0, zero_mul, map_zero]) ω

/-- Woodford (2003), pp. 570–571 (**uniqueness**): if a competing plan attains the same loss
(with vanishing boundary term, `β > 0`, `λ > 0`), it coincides with the FOC plan in mean square:
`E_{t0}(Δπ^{qd}_t)² = 0` and `E_{t0}(Δx_t)² = 0` at every date `t ≥ t0 + d`. -/
theorem welfare_eq_imp {β κ γ lam xs : ℝ} {d t0 : ℕ} (hβ : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hPO : 𝔼.PullOut) {u π x π' x' φ : ℕ → Ω → ℝ}
    (hAS : AS 𝔼 κ β γ d t0 u π x) (hAS' : AS 𝔼 κ β γ d t0 u π' x')
    (hPx : Predet 𝔼 d t0 x) (hPx' : Predet 𝔼 d t0 x')
    (hFOC : FOC κ γ lam xs d t0 π x φ) (hφa : ∀ s, t0 ≤ s → 𝔼.E s (φ s) = φ s)
    (hπ : BoundedProc π) (hx : BoundedProc x) (hπ' : BoundedProc π') (hx' : BoundedProc x')
    (hφ : BoundedProc φ)
    (hbd : 𝔼.E t0 (φ (t0 - 1) * (qd γ π' (t0 + d) - qd γ π (t0 + d))) = 0) (ω : Ω)
    (heq : welfare 𝔼 β γ lam xs d t0 π' x' ω = welfare 𝔼 β γ lam xs d t0 π x ω) (n : ℕ) :
    𝔼.E t0 (fun ω' => (qd γ π' (t0 + d + n) ω' - qd γ π (t0 + d + n) ω') ^ 2) ω = 0 ∧
      𝔼.E t0 (fun ω' => (x' (t0 + d + n) ω' - x (t0 + d + n) ω') ^ 2) ω = 0 := by
  have h := welfare_diff 𝔼 hβ.le hβ1 hPO hAS hAS' hPx hPx' hFOC hφa hπ hx hπ' hx' hφ ω
  rw [hbd, Pi.zero_apply, mul_zero, zero_add, heq, sub_self] at h
  have hnn : ∀ m, 0 ≤ 𝔼.E t0 (devLoss γ lam π x π' x' (t0 + d + m)) ω := by
    intro m
    have h0 : (0 : Ω → ℝ) ≤ devLoss γ lam π x π' x' (t0 + d + m) := fun ω' => by
      simp only [Pi.zero_apply, devLoss]
      have := hlam.le
      positivity
    have := 𝔼.mono t0 h0 ω
    simpa using this
  -- the summable nonnegative series has sum zero, so every term vanishes
  obtain ⟨Q, hQ⟩ := qd_bounded (γ := γ) hπ
  obtain ⟨Q', hQ'⟩ := qd_bounded (γ := γ) hπ'
  obtain ⟨X, hX⟩ := hx
  obtain ⟨X', hX'⟩ := hx'
  have hDb : ∀ m, |𝔼.E t0 (devLoss γ lam π x π' x' (t0 + d + m)) ω| ≤
      1 / 2 * (Q' + Q) ^ 2 + lam / 2 * (X' + X) ^ 2 := by
    intro m
    refine 𝔼.abs_E_le (fun ω' => ?_) t0 ω
    have h1 : |qd γ π' (t0 + d + m) ω' - qd γ π (t0 + d + m) ω'| ≤ Q' + Q :=
      (abs_sub _ _).trans (add_le_add (hQ' _ ω') (hQ _ ω'))
    have h2 : |x' (t0 + d + m) ω' - x (t0 + d + m) ω'| ≤ X' + X :=
      (abs_sub _ _).trans (add_le_add (hX' _ ω') (hX _ ω'))
    have e1 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    have e2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
    rw [sq_abs] at e1 e2
    simp only [devLoss]
    rw [abs_of_nonneg (by have := hlam.le; positivity)]
    have := hlam.le
    gcongr
  have hs := summable_weighted hβ.le hβ1 (t0 + d) hDb
  have hnn' : ∀ m, 0 ≤ β ^ (t0 + d + m) * 𝔼.E t0 (devLoss γ lam π x π' x' (t0 + d + m)) ω :=
    fun m => mul_nonneg (pow_nonneg hβ.le _) (hnn m)
  have hS : HasSum (fun m => β ^ (t0 + d + m) * 𝔼.E t0 (devLoss γ lam π x π' x' (t0 + d + m)) ω)
      0 := by
    have := hs.hasSum
    rwa [← h] at this
  have hzero := (hasSum_zero_iff_of_nonneg hnn').mp hS
  have hDn : 𝔼.E t0 (devLoss γ lam π x π' x' (t0 + d + n)) ω = 0 := by
    have := congrFun hzero n
    simp only [Pi.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_left (pow_pos hβ _).ne'
  -- both squared deviations are dominated by the deviation loss
  set A : Ω → ℝ := fun ω' => (qd γ π' (t0 + d + n) ω' - qd γ π (t0 + d + n) ω') ^ 2 with hA
  set B : Ω → ℝ := fun ω' => (x' (t0 + d + n) ω' - x (t0 + d + n) ω') ^ 2 with hB
  have hdev : devLoss γ lam π x π' x' (t0 + d + n) = (1 / 2 : ℝ) • A + (lam / 2) • B := by
    funext ω'
    simp [devLoss, hA, hB]
  have hA0 : 0 ≤ 𝔼.E t0 A ω := by
    have := 𝔼.mono t0 (show (0 : Ω → ℝ) ≤ A from fun ω' => by simp only [hA]; positivity) ω
    simpa using this
  have hB0 : 0 ≤ 𝔼.E t0 B ω := by
    have := 𝔼.mono t0 (show (0 : Ω → ℝ) ≤ B from fun ω' => by simp only [hB]; positivity) ω
    simpa using this
  rw [hdev, map_add, map_smul, map_smul] at hDn
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hDn
  have hl2 : 0 < lam / 2 := by linarith
  constructor
  · nlinarith [mul_nonneg hl2.le hB0]
  · nlinarith [mul_nonneg hl2.le hB0]

/-- Woodford (2003), pp. 570–571: under perfect foresight the optimum is unique outright — a
competing bounded feasible plan with the same loss coincides with the FOC plan at every date
`t ≥ t0 + d` (in `π^{qd}` and in `x`). -/
theorem welfare_unique_pf {β κ γ lam xs : ℝ} {d t0 : ℕ} (hβ : 0 < β) (hβ1 : β < 1)
    (hlam : 0 < lam) {u π x π' x' φ : ℕ → Unit → ℝ}
    (hAS : AS perfectForesight κ β γ d t0 u π x) (hAS' : AS perfectForesight κ β γ d t0 u π' x')
    (hFOC : FOC κ γ lam xs d t0 π x φ)
    (hπ : BoundedProc π) (hx : BoundedProc x) (hπ' : BoundedProc π') (hx' : BoundedProc x')
    (hφ : BoundedProc φ)
    (hbd : φ (t0 - 1) () * (qd γ π' (t0 + d) () - qd γ π (t0 + d) ()) = 0)
    (heq : welfare perfectForesight β γ lam xs d t0 π' x' () =
      welfare perfectForesight β γ lam xs d t0 π x ()) (n : ℕ) :
    qd γ π' (t0 + d + n) () = qd γ π (t0 + d + n) () ∧ x' (t0 + d + n) () = x (t0 + d + n) () := by
  have hP : ∀ y : ℕ → Unit → ℝ, Predet perfectForesight d t0 y := fun _ _ _ => rfl
  have h := welfare_eq_imp perfectForesight hβ hβ1 hlam perfectForesight_pullOut hAS hAS'
    (hP x) (hP x') hFOC (fun _ _ => rfl) hπ hx hπ' hx' hφ
    (by funext ω; exact hbd) () heq n
  change (qd γ π' (t0 + d + n) () - qd γ π (t0 + d + n) ()) ^ 2 = 0 ∧
    (x' (t0 + d + n) () - x (t0 + d + n) ()) ^ 2 = 0 at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1),
    sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)⟩

/-! ### The Lagrangian (2.29): law of iterated expectations and exact derivatives -/

/-- Woodford (2003), p. 570 (passing from the first Lagrangian to (2.29)): for a multiplier `φ`
known at date `s ≥ t0`, the law of iterated expectations (with pull-out) removes the inner
expectation, `E_{t0}[φ E_s y] = E_{t0}[φ y]`. -/
theorem lagrangian_LIE (hPO : 𝔼.PullOut) {s t0 : ℕ} (hs : t0 ≤ s) {φ : Ω → ℝ}
    (hφ : 𝔼.E s φ = φ) (y : Ω → ℝ) : 𝔼.E t0 (φ * 𝔼.E s y) = 𝔼.E t0 (φ * y) := by
  rw [← hPO s φ y hφ, 𝔼.tower hs]

/-- Woodford (2003), (2.29), p. 570: the date-`t` multiplier term of the Lagrangian equals, after
`E_{t0}`, the same term with `E_{t−d}` removed, minus `E_{t0}[φ_{t−d} u_t]`, which does not depend
on policy (the step "dropping terms that are independent of policy"). -/
theorem lagrangian_LIE_term (hPO : 𝔼.PullOut) {κ β γ : ℝ} {d t0 t : ℕ} (ht : t0 + d ≤ t)
    {φ : Ω → ℝ} (hφ : 𝔼.E (t - d) φ = φ) (u π x : ℕ → Ω → ℝ) :
    𝔼.E t0 (φ * (qd γ π t - κ • x t - β • 𝔼.E (t - d) (qd γ π (t + 1)) - 𝔼.E (t - d) (u t))) =
      𝔼.E t0 (φ * (qd γ π t - κ • x t - β • qd γ π (t + 1))) - 𝔼.E t0 (φ * u t) := by
  have hs : t0 ≤ t - d := by omega
  simp only [mul_sub, mul_smul_comm, map_sub, map_smul, lagrangian_LIE 𝔼 hPO hs hφ]

/-- Woodford (2003), (2.29)–(2.30), p. 570: `π^{qd}_{t+1}` enters the Lagrangian through the
date-`(t+1)` loss and multiplier term and through the date-`t` term `−β φ_{t−d} π^{qd}_{t+1}`; the
exact partial derivative is `β^{t+1}(π^{qd}_{t+1} + φ_{t+1−d} − φ_{t−d})`. -/
theorem hasDerivAt_lagr_q (β φ0 φ1 : ℝ) (t : ℕ) (v : ℝ) :
    HasDerivAt (fun w => β ^ (t + 1) * (1 / 2 * w ^ 2 + φ0 * w) - β ^ t * (β * φ1 * w))
      (β ^ (t + 1) * (v + φ0 - φ1)) v := by
  have h1 : HasDerivAt (fun w : ℝ => 1 / 2 * w ^ 2 + φ0 * w)
      (1 / 2 * ((2 : ℕ) * v ^ (2 - 1)) + φ0 * 1) v :=
    HasDerivAt.add (HasDerivAt.const_mul (1 / 2 : ℝ) (hasDerivAt_pow 2 v))
      (HasDerivAt.const_mul φ0 (hasDerivAt_id' v))
  have h2 := HasDerivAt.sub (HasDerivAt.const_mul (β ^ (t + 1)) h1)
    (HasDerivAt.const_mul (β ^ t * (β * φ1)) (hasDerivAt_id' v))
  convert h2 using 1
  · funext w; simp only [Pi.sub_apply]; ring
  · push_cast; ring

/-- Woodford (2003), (2.29), (2.31), p. 571: the exact partial derivative of the Lagrangian in
`x_t` is `βᵗ(λ(x_t − x*) − κφ_{t−d})`. -/
theorem hasDerivAt_lagr_x (β lam xs κ φ0 : ℝ) (t : ℕ) (v : ℝ) :
    HasDerivAt (fun w => β ^ t * (lam / 2 * (w - xs) ^ 2 - φ0 * (κ * w)))
      (β ^ t * (lam * (v - xs) - κ * φ0)) v := by
  have h1 : HasDerivAt (fun w : ℝ => lam / 2 * w ^ 2 + (-(lam * xs) - κ * φ0) * w
      + lam / 2 * xs ^ 2) (lam / 2 * ((2 : ℕ) * v ^ (2 - 1)) + (-(lam * xs) - κ * φ0) * 1 + 0) v :=
    HasDerivAt.add (HasDerivAt.add (HasDerivAt.const_mul (lam / 2) (hasDerivAt_pow 2 v))
      (HasDerivAt.const_mul _ (hasDerivAt_id' v))) (hasDerivAt_const v _)
  have h2 := HasDerivAt.const_mul (β ^ t) h1
  convert h2 using 1
  · funext w; ring
  · push_cast; ring

/-- Woodford (2003), (2.30)–(2.31), p. 570: for `β ≠ 0` the two partial derivatives vanish
exactly when the first-order conditions (2.30)–(2.31) hold. -/
theorem foc_iff_deriv {β : ℝ} (hβ : β ≠ 0) (lam xs κ φ0 φ1 q xv : ℝ) (t : ℕ) :
    (β ^ (t + 1) * (q + φ0 - φ1) = 0 ∧ β ^ t * (lam * (xv - xs) - κ * φ0) = 0) ↔
      (q + φ0 - φ1 = 0 ∧ lam * (xv - xs) - κ * φ0 = 0) := by
  simp only [mul_eq_zero, pow_eq_zero_iff', hβ, false_and, false_or]

/-! ### Eliminating the multipliers: the target criterion (2.9) / (2.32) -/

/-- Woodford (2003), eq. (2.9) with predetermination, p. 571:
`π_t − γπ_{t−1} + φ(x_t − x_{t−1}) = 0`
at every date `t ≥ t0 + d`. -/
def TC (γ phi : ℝ) (d t0 : ℕ) (π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t, t0 + d ≤ t → ∀ ω, qd γ π t ω + phi * (x t ω - x (t - 1) ω) = 0

/-- Woodford (2003), eq. (2.32), p. 571 (corrected, **E16**): at each decision date `t ≥ t0` the
bank's projection satisfies `π_{t+d} − γπ_{t+d−1} + φ(x_{t+d} − x_{t+d−1}) = 0`. -/
def TC232 (γ phi : ℝ) (d t0 : ℕ) (π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t, t0 ≤ t → ∀ ω,
    π (t + d) ω - γ * π (t + d - 1) ω + phi * (x (t + d) ω - x (t + d - 1) ω) = 0

/-- Woodford (2003), p. 571: (2.32) imposed at every decision date `t ≥ t0` is (2.9) imposed at
every date `t ≥ t0 + d`. -/
theorem tc232_iff {γ phi : ℝ} {d t0 : ℕ} {π x : ℕ → Ω → ℝ} :
    TC232 γ phi d t0 π x ↔ TC γ phi d t0 π x := by
  constructor
  · intro h t ht ω
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
    have := h (t0 + s) (by omega) ω
    rw [show t0 + s + d = t0 + d + s by omega] at this
    rw [qd_apply]
    linarith
  · intro h t ht ω
    have := h (t + d) (by omega) ω
    rw [qd_apply] at this
    linarith

/-- Woodford (2003), p. 571: the multiplier identified from (2.31), `φ_s = (λ/κ)(x_{s+d} − x*)`
(so that `φ_{t0−1} = (λ/κ)(x_{t0+d−1} − x*)` is the self-consistent initial multiplier, cf.
Ch. 7, (5.2)). -/
noncomputable def multOf (lam κ xs : ℝ) (d : ℕ) (x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun s ω => lam / κ * (x (s + d) ω - xs)

/-- Woodford (2003), p. 571 (**elimination**): the FOCs (2.30)–(2.31) with the self-consistent
initial multiplier `φ_{t0−1} = (λ/κ)(x_{t0+d−1} − x*)` imply the target criterion (2.9) with
`φ = λ/κ` at every date `t ≥ t0 + d`. -/
theorem tc_of_foc {κ γ lam xs : ℝ} (hκ : κ ≠ 0) {d t0 : ℕ} {π x φ : ℕ → Ω → ℝ}
    (h : FOC κ γ lam xs d t0 π x φ)
    (hφ0 : ∀ ω, φ (t0 - 1) ω = lam / κ * (x (t0 + d - 1) ω - xs)) :
    TC γ (lam / κ) d t0 π x := by
  intro t ht ω
  obtain ⟨f1, f2⟩ := h t ht ω
  have e0 : φ (t - d) ω - lam / κ * (x t ω - xs) = 0 := by
    field_simp
    linarith
  have e1 : φ (t - d - 1) ω - lam / κ * (x (t - 1) ω - xs) = 0 := by
    rcases Nat.eq_or_lt_of_le ht with h0 | h0
    · rw [show t - d - 1 = t0 - 1 by omega, hφ0, show t - 1 = t0 + d - 1 by omega, sub_self]
    · obtain ⟨_, f2'⟩ := h (t - 1) (by omega) ω
      rw [show t - 1 - d = t - d - 1 by omega] at f2'
      field_simp
      linarith
  linear_combination f1 - e0 + e1

/-- Woodford (2003), p. 571 (**converse**): if (2.9) holds with `φ = λ/κ` at every `t ≥ t0 + d`
(and `t0 ≥ 1`), the multipliers `multOf` satisfy the FOCs (2.30)–(2.31). -/
theorem foc_of_tc {κ γ lam xs : ℝ} (hκ : κ ≠ 0) {d t0 : ℕ} (ht0 : 1 ≤ t0) {π x : ℕ → Ω → ℝ}
    (h : TC γ (lam / κ) d t0 π x) : FOC κ γ lam xs d t0 π x (multOf lam κ xs d x) := by
  intro t ht ω
  have h1 : t - d + d = t := by omega
  have h2 : t - d - 1 + d = t - 1 := by omega
  simp only [multOf, h1, h2]
  constructor
  · linear_combination h t ht ω
  · field_simp
    ring

/-- Woodford (2003), p. 571: the multipliers `multOf` are known at their date (for `s ≥ t0`)
because the output gap is predetermined. -/
theorem multOf_adapted {lam κ xs : ℝ} {d t0 : ℕ} {x : ℕ → Ω → ℝ} (hPx : Predet 𝔼 d t0 x)
    (s : ℕ) (hs : t0 ≤ s) : 𝔼.E s (multOf lam κ xs d x s) = multOf lam κ xs d x s := by
  have e : multOf lam κ xs d x s = (lam / κ) • (x (s + d) - fun _ => xs) := by
    funext ω; simp [multOf]
  have hx := hPx (s + d) (by omega)
  rw [show s + d - d = s by omega] at hx
  rw [e, map_smul, map_sub, hx, 𝔼.const]

/-- Woodford (2003), p. 571: the multipliers `multOf` of a bounded output gap are bounded. -/
theorem multOf_bounded {lam κ xs : ℝ} {d : ℕ} {x : ℕ → Ω → ℝ} (hx : BoundedProc x) :
    BoundedProc (multOf lam κ xs d x) := by
  obtain ⟨M, hM⟩ := hx
  refine ⟨|lam / κ| * (M + |xs|), fun s ω => ?_⟩
  simp only [multOf, abs_mul]
  exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hM _ ω) le_rfl))
    (abs_nonneg _)

/-- Woodford (2003), p. 571, footnote 23: since inflation and the output gap are predetermined
`d` periods in advance (and the history is known at `t0`), the left-hand side of (2.32) is known
at date `t`: the criterion may equivalently be stated for date-`t` forecasts. -/
theorem tc232_projected {γ phi : ℝ} {d t0 : ℕ} {π x : ℕ → Ω → ℝ} (hPπ : Predet 𝔼 d t0 π)
    (hPx : Predet 𝔼 d t0 x) (hπh : 𝔼.E t0 (π (t0 + d - 1)) = π (t0 + d - 1))
    (hxh : 𝔼.E t0 (x (t0 + d - 1)) = x (t0 + d - 1)) {t : ℕ} (ht : t0 ≤ t) :
    𝔼.E t (π (t + d) - γ • π (t + d - 1) + phi • (x (t + d) - x (t + d - 1))) =
      π (t + d) - γ • π (t + d - 1) + phi • (x (t + d) - x (t + d - 1)) := by
  have known : ∀ y : ℕ → Ω → ℝ, Predet 𝔼 d t0 y → 𝔼.E t0 (y (t0 + d - 1)) = y (t0 + d - 1) →
      𝔼.E t (y (t + d)) = y (t + d) ∧ 𝔼.E t (y (t + d - 1)) = y (t + d - 1) := by
    intro y hy hyh
    have h0 := hy (t + d) (by omega)
    rw [show t + d - d = t by omega] at h0
    refine ⟨h0, ?_⟩
    rcases Nat.eq_or_lt_of_le ht with h1 | h1
    · subst h1; exact hyh
    · have h2 := hy (t + d - 1) (by omega)
      exact ForwardSolution.E_of_known 𝔼 (by omega : t + d - 1 - d ≤ t) h2
  obtain ⟨a1, a2⟩ := known π hPπ hπh
  obtain ⟨b1, b2⟩ := known x hPx hxh
  simp only [map_add, map_sub, map_smul, a1, a2, b1, b2]

/-- Woodford (2003), p. 571, **E16**: the printed (2.32) reads `π_{t+d} − γ_{t+d−1} + …`; read with
`γ` a constant it is not the optimality condition. With no shocks, a zero history and `x* = 0` the
zero plan satisfies (2.28), the FOCs (with zero multipliers) and the corrected criterion, yet the
printed form fails whenever `γ ≠ 0`; the intended term is `γπ_{t+d−1}`. -/
theorem printed_eq232_fails [Nonempty Ω] {κ β γ lam phi : ℝ} (hγ : γ ≠ 0) (d t0 : ℕ) :
    AS 𝔼 κ β γ d t0 0 0 0 ∧ FOC κ γ lam 0 d t0 (0 : ℕ → Ω → ℝ) 0 0 ∧
      TC232 γ phi d t0 (0 : ℕ → Ω → ℝ) 0 ∧
      ¬ (∀ t, t0 ≤ t → ∀ ω : Ω,
        (0 : ℕ → Ω → ℝ) (t + d) ω - γ + phi * ((0 : ℕ → Ω → ℝ) (t + d) ω
          - (0 : ℕ → Ω → ℝ) (t + d - 1) ω) = 0) := by
  refine ⟨fun t _ => ?_, fun t _ ω => ?_, fun t _ ω => by simp, fun h => ?_⟩
  · funext ω; simp [qd]
  · simp [qd]
  · have := h t0 le_rfl (Classical.arbitrary Ω)
    simp only [Pi.zero_apply, zero_sub, sub_self, mul_zero, add_zero, neg_eq_zero] at this
    exact hγ this

/-! ### (2.28) + (2.32) determine a unique bounded equilibrium -/

/-- Woodford (2003), p. 571: an equilibrium under the commitment to (2.32): (2.28) and the target
criterion hold at every date `t ≥ t0 + d`, and inflation and the output gap are predetermined. -/
def Eqm (κ β γ phi : ℝ) (d t0 : ℕ) (u π x : ℕ → Ω → ℝ) : Prop :=
  AS 𝔼 κ β γ d t0 u π x ∧ TC γ phi d t0 π x ∧ Predet 𝔼 d t0 x ∧ Predet 𝔼 d t0 π

/-- Woodford (2003), p. 571: the lag seen from the first chosen date `T`:
`prev y_{T−1} (s ↦ y_{T+s}) s = y_{T+s−1}`. -/
theorem prev_shift (T : ℕ) (y : ℕ → Ω → ℝ) (s : ℕ) :
    prev (y (T - 1)) (fun k => y (T + k)) s = y (T + s - 1) := by
  cases s with
  | zero => simp
  | succ k => simp [show T + (k + 1) - 1 = T + k by omega]

/-- Woodford (2003), p. 571: the forcing term of the workhorse equation for (2.28) + (2.32),
`z_s = −φ⁻¹ E_{t0+s} u_{t0+d+s}`. -/
noncomputable def forcing (phi : ℝ) (d t0 : ℕ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun s => (-phi⁻¹) • 𝔼.E (t0 + s) (u (t0 + d + s))

/-- Woodford (2003), p. 571: in an equilibrium the output gap from date `t0 + d` on solves the
second-order equation `β E_{t−d} x_{t+1} − (1 + β + κ/φ) x_t + x_{t−1} = φ⁻¹ E_{t−d} u_t`,
i.e. the workhorse for the shifted expectation system `shift 𝔼 t0`. -/
theorem eqm_secondOrder {κ β γ phi : ℝ} (hphi : phi ≠ 0) {d t0 : ℕ} {u π x : ℕ → Ω → ℝ}
    (h : Eqm 𝔼 κ β γ phi d t0 u π x) :
    SecondOrder (shift 𝔼 t0) β (κ / phi) (x (t0 + d - 1)) (forcing 𝔼 phi d t0 u)
      (fun s => x (t0 + d + s)) := by
  obtain ⟨hAS, hTC, hPx, _⟩ := h
  intro s
  set t := t0 + d + s with htdef
  have ht : t0 + d ≤ t := by omega
  have htd : t - d = t0 + s := by omega
  have hq1 : qd γ π (t + 1) = (-phi) • (x (t + 1) - x t) := by
    funext ω
    have := hTC (t + 1) (by omega) ω
    simp only [Nat.add_sub_cancel] at this
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linarith
  have hxt := hPx t ht
  rw [htd] at hxt
  have hA := hAS t ht
  rw [htd, hxt, hq1, map_smul, map_sub, hxt] at hA
  funext ω
  have hA' := congrFun hA ω
  have hT := hTC t ht ω
  have hp := congrFun (prev_shift (t0 + d) x s) ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hA' hp ⊢
  simp only [shift_E, forcing, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, hp]
  rw [qd_apply] at hA' hT
  have hc : phi * (κ / phi) = κ := mul_div_cancel₀ κ hphi
  have hi : phi * phi⁻¹ = 1 := mul_inv_cancel₀ hphi
  have key : phi * (β * 𝔼.E (t0 + s) (x (t0 + d + (s + 1))) ω - (1 + β + κ / phi) * x t ω
      + x (t - 1) ω - -(-phi⁻¹ * 𝔼.E (t0 + s) (u t) ω)) = 0 := by
    linear_combination hA' - hT - x t ω * hc - 𝔼.E (t0 + s) (u t) ω * hi
  have := (mul_eq_zero.mp key).resolve_left hphi
  linarith

/-- Woodford (2003), p. 571 (**uniqueness**): two bounded equilibria under (2.32) with the same
history `π_{t0+d−1}`, `x_{t0+d−1}` coincide at every date `t ≥ t0 + d`. -/
theorem eqm_unique {κ β γ phi : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hphi : 0 < phi) {d t0 : ℕ}
    {u π x π' x' : ℕ → Ω → ℝ} (h : Eqm 𝔼 κ β γ phi d t0 u π x)
    (h' : Eqm 𝔼 κ β γ phi d t0 u π' x') (hbx : BoundedProc x) (hbx' : BoundedProc x')
    (hx0 : x (t0 + d - 1) = x' (t0 + d - 1)) (hπ0 : π (t0 + d - 1) = π' (t0 + d - 1)) (s : ℕ) :
    π (t0 + d + s) = π' (t0 + d + s) ∧ x (t0 + d + s) = x' (t0 + d + s) := by
  have hs1 := eqm_secondOrder 𝔼 hphi.ne' h
  have hs2 := eqm_secondOrder 𝔼 hphi.ne' h'
  rw [← hx0] at hs2
  have had : ∀ y : ℕ → Ω → ℝ, Predet 𝔼 d t0 y → (shift 𝔼 t0).Adapted (fun s => y (t0 + d + s)) :=
    fun y hy s => by
      have := hy (t0 + d + s) (by omega)
      rwa [show t0 + d + s - d = t0 + s by omega] at this
  have hbd : ∀ y : ℕ → Ω → ℝ, BoundedProc y → BoundedProc (fun s => y (t0 + d + s)) :=
    fun y ⟨M, hM⟩ => ⟨M, fun s ω => hM _ ω⟩
  have hX := secondOrder_unique (shift 𝔼 t0) hβ (div_pos hκ hphi) hs1 hs2 (had x h.2.2.1)
    (had x' h'.2.2.1) (hbd x hbx) (hbd x' hbx')
  have hxs : ∀ k, x (t0 + d + k) = x' (t0 + d + k) := fun k => congrFun hX k
  have hxs1 : ∀ k, x (t0 + d + k - 1) = x' (t0 + d + k - 1) := by
    intro k
    cases k with
    | zero => simpa using hx0
    | succ k => rw [show t0 + d + (k + 1) - 1 = t0 + d + k by omega]; exact hxs k
  have hπs : ∀ k, π (t0 + d + k) = π' (t0 + d + k) := by
    intro k
    induction k with
    | zero =>
      funext ω
      have e1 := h.2.1 (t0 + d) (by omega) ω
      have e2 := h'.2.1 (t0 + d) (by omega) ω
      rw [qd_apply] at e1 e2
      have := congrFun hπ0 ω
      have hx1 := congrFun (hxs 0) ω
      have hx2 := congrFun hx0 ω
      simp only [add_zero] at hx1 e1 e2 ⊢
      rw [this, hx1, hx2] at e1
      linarith
    | succ k ih =>
      funext ω
      have e1 := h.2.1 (t0 + d + (k + 1)) (by omega) ω
      have e2 := h'.2.1 (t0 + d + (k + 1)) (by omega) ω
      rw [qd_apply, show t0 + d + (k + 1) - 1 = t0 + d + k by omega] at e1 e2
      have hx1 := congrFun (hxs (k + 1)) ω
      have hx2 := congrFun (hxs k) ω
      have hpi := congrFun ih ω
      rw [hpi, hx1, hx2] at e1
      linarith
  exact ⟨hπs s, hxs s⟩

/-- Woodford (2003), p. 571: the inflation path implied by (2.32) from date `t0 + d` on,
`π_{t0+d+s} = γπ_{t0+d+s−1} − φ(x_{t0+d+s} − x_{t0+d+s−1})`, given `π_{t0+d−1}`. -/
noncomputable def piPath (γ phi : ℝ) (πh xh : Ω → ℝ) (ℓ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => γ • πh - phi • (ℓ 0 - xh)
  | s + 1 => γ • piPath γ phi πh xh ℓ s - phi • (ℓ (s + 1) - ℓ s)

/-- Woodford (2003), p. 571: `π_{T+s} − γπ_{T+s−1} = −φ(x_{T+s} − x_{T+s−1})` for `piPath`. -/
theorem piPath_qd (γ phi : ℝ) (πh xh : Ω → ℝ) (ℓ : ℕ → Ω → ℝ) (s : ℕ) :
    piPath γ phi πh xh ℓ s - γ • prev πh (piPath γ phi πh xh ℓ) s =
      -(phi • (ℓ s - prev xh ℓ s)) := by
  cases s <;> simp [piPath]

/-- Woodford (2003), p. 571: a process equal to the history `h` before `T` and to `p` from
`T` on. -/
noncomputable def glue (T : ℕ) (h : Ω → ℝ) (p : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => if t < T then h else p (t - T)

/-- Woodford (2003), p. 571: `glue T h p (T + s) = p s`. -/
theorem glue_add (T : ℕ) (h : Ω → ℝ) (p : ℕ → Ω → ℝ) (s : ℕ) : glue T h p (T + s) = p s := by
  simp [glue]

/-- Woodford (2003), p. 571: `glue T h p (T + s − 1) = prev h p s` for `T ≥ 1`. -/
theorem glue_sub_one {T : ℕ} (hT : 1 ≤ T) (h : Ω → ℝ) (p : ℕ → Ω → ℝ) (s : ℕ) :
    glue T h p (T + s - 1) = prev h p s := by
  cases s with
  | zero => simp [glue, show T - 1 < T by omega]
  | succ k => simp [glue, show T + (k + 1) - 1 = T + k by omega]

/-- Woodford (2003), p. 571 (**existence**): given bounded shocks and a history `π_{t0+d−1}`,
`x_{t0+d−1}` known at `t0`, with `0 < β`, `κ, φ > 0` and `0 ≤ γ ≤ 1`, there is a bounded
equilibrium under the commitment to (2.32) with that history. (Bounded inflation uses
`γ ≤ 1` through `π_t + φx_t = γ(π_{t−1} + φx_{t−1}) + (1 − γ)φx_{t−1}`.) -/
theorem eqm_exists {κ β γ phi : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hphi : 0 < phi) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) {d t0 : ℕ} (ht0 : 1 ≤ t0) {u : ℕ → Ω → ℝ} (hu : BoundedProc u)
    {πh xh : Ω → ℝ} {K : ℝ} (hπK : ∀ ω, |πh ω| ≤ K) (hxK : ∀ ω, |xh ω| ≤ K)
    (hπh : 𝔼.E t0 πh = πh) (hxh : 𝔼.E t0 xh = xh) :
    ∃ π x : ℕ → Ω → ℝ, Eqm 𝔼 κ β γ phi d t0 u π x ∧ BoundedProc π ∧ BoundedProc x ∧
      π (t0 + d - 1) = πh ∧ x (t0 + d - 1) = xh := by
  have hT : 1 ≤ t0 + d := by omega
  set 𝔼s := shift 𝔼 t0 with h𝔼s
  set z := forcing 𝔼 phi d t0 u with hz
  have hzb : BoundedProc z := by
    obtain ⟨M, hM⟩ := hu
    refine ⟨|phi⁻¹| * M, fun s ω => ?_⟩
    simp only [hz, forcing, Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hM _) _ ω) (abs_nonneg _)
  have hza : 𝔼s.Adapted z := fun s => by
    simp only [h𝔼s, shift_E, hz, forcing, map_smul, 𝔼.E_E_self]
  have hm0 : 𝔼s.E 0 xh = xh := by simpa [h𝔼s] using hxh
  obtain ⟨hsol, ⟨Mℓ, hMℓ⟩, hℓa, -⟩ :=
    secondOrder_existsUnique 𝔼s hβ (div_pos hκ hphi) hzb hza hxK hm0
  set ℓ := secondOrderSol 𝔼s β (κ / phi) xh z with hℓ
  set P := piPath γ phi πh xh ℓ with hP
  refine ⟨glue (t0 + d) πh P, glue (t0 + d) xh ℓ, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- (2.28)
    intro t ht
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [show (t0 + d) + s - d = t0 + s by omega]
    have hq : ∀ k, qd γ (glue (t0 + d) πh P) ((t0 + d) + k) = -(phi • (ℓ k - prev xh ℓ k)) := by
      intro k
      simp only [qd, glue_add, glue_sub_one hT]
      exact piPath_qd γ phi πh xh ℓ k
    rw [hq s, show (t0 + d) + s + 1 = (t0 + d) + (s + 1) by omega, hq (s + 1), glue_add]
    have hl := congrFun (hsol s)
    have hℓs : 𝔼.E (t0 + s) (ℓ s) = ℓ s := hℓa s
    funext ω
    have e := hl ω
    simp only [h𝔼s, shift_E, hz, forcing, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      Pi.neg_apply, smul_eq_mul] at e
    simp only [prev_succ, map_neg, map_smul, map_sub, hℓs, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    have hc : phi * (κ / phi) = κ := mul_div_cancel₀ κ hphi.ne'
    have hi : phi * phi⁻¹ = 1 := mul_inv_cancel₀ hphi.ne'
    linear_combination phi * e + ℓ s ω * hc + 𝔼.E (t0 + s) (u ((t0 + d) + s)) ω * hi
  · -- (2.32)
    intro t ht ω
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
    have hq := congrFun (piPath_qd γ phi πh xh ℓ s) ω
    simp only [qd_apply, glue_add, glue_sub_one hT, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
      smul_eq_mul] at hq ⊢
    linarith
  · -- the output gap is predetermined
    intro t ht
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [show (t0 + d) + s - d = t0 + s by omega, glue_add]
    exact hℓa s
  · -- inflation is predetermined
    intro t ht
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [show (t0 + d) + s - d = t0 + s by omega, glue_add]
    clear ht
    induction s with
    | zero =>
      have h0 : 𝔼.E t0 (ℓ 0) = ℓ 0 := by simpa [h𝔼s] using hℓa 0
      simp only [hP, piPath, add_zero, map_sub, map_smul, hπh, hxh, h0]
    | succ k ih =>
      have h1 : 𝔼.E (t0 + (k + 1)) (P k) = P k :=
        ForwardSolution.E_of_known 𝔼 (by omega) ih
      have h2 : 𝔼.E (t0 + (k + 1)) (ℓ k) = ℓ k :=
        ForwardSolution.E_of_known 𝔼 (by omega) (hℓa k)
      have h3 : 𝔼.E (t0 + (k + 1)) (ℓ (k + 1)) = ℓ (k + 1) := hℓa (k + 1)
      change 𝔼.E (t0 + (k + 1)) (γ • P k - phi • (ℓ (k + 1) - ℓ k))
        = γ • P k - phi • (ℓ (k + 1) - ℓ k)
      simp only [map_sub, map_smul, h1, h2, h3]
  · -- inflation is bounded
    set B := max (γ * K + phi * K) (phi * Mℓ) with hB
    have hv : ∀ k ω, |P k ω + phi * ℓ k ω| ≤ B := by
      intro k
      induction k with
      | zero =>
        intro ω
        simp only [hP, piPath, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        have : γ * πh ω - phi * (ℓ 0 ω - xh ω) + phi * ℓ 0 ω = γ * πh ω + phi * xh ω := by ring
        rw [this]
        refine ((abs_add_le _ _).trans ?_).trans (le_max_left _ _)
        rw [abs_mul, abs_mul, abs_of_nonneg hγ0, abs_of_pos hphi]
        exact add_le_add (mul_le_mul_of_nonneg_left (hπK ω) hγ0)
          (mul_le_mul_of_nonneg_left (hxK ω) hphi.le)
      | succ k ih =>
        intro ω
        have e : P (k + 1) ω + phi * ℓ (k + 1) ω =
            γ * (P k ω + phi * ℓ k ω) + (1 - γ) * (phi * ℓ k ω) := by
          simp only [hP, piPath, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [e]
        have h1 : |γ * (P k ω + phi * ℓ k ω)| ≤ γ * B := by
          rw [abs_mul, abs_of_nonneg hγ0]
          exact mul_le_mul_of_nonneg_left (ih ω) hγ0
        have h2 : |(1 - γ) * (phi * ℓ k ω)| ≤ (1 - γ) * B := by
          rw [abs_mul, abs_of_nonneg (by linarith), abs_mul, abs_of_pos hphi]
          exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (hMℓ k ω) hphi.le).trans
            (le_max_right _ _)) (by linarith)
        calc |γ * (P k ω + phi * ℓ k ω) + (1 - γ) * (phi * ℓ k ω)|
            ≤ |γ * (P k ω + phi * ℓ k ω)| + |(1 - γ) * (phi * ℓ k ω)| := abs_add_le _ _
          _ ≤ γ * B + (1 - γ) * B := add_le_add h1 h2
          _ = B := by ring
    refine ⟨max K (B + phi * Mℓ), fun t ω => ?_⟩
    by_cases htT : t < (t0 + d)
    · simp only [glue, htT, ↓reduceIte]
      exact (hπK ω).trans (le_max_left _ _)
    · simp only [glue, htT, ↓reduceIte]
      have e : P (t - (t0 + d)) ω =
          (P (t - (t0 + d)) ω + phi * ℓ (t - (t0 + d)) ω) - phi * ℓ (t - (t0 + d)) ω := by ring
      rw [e]
      refine ((abs_sub _ _).trans (add_le_add (hv _ ω) ?_)).trans (le_max_right _ _)
      rw [abs_mul, abs_of_pos hphi]
      exact mul_le_mul_of_nonneg_left (hMℓ _ ω) hphi.le
  · -- the output gap is bounded
    refine ⟨max K Mℓ, fun t ω => ?_⟩
    by_cases htT : t < (t0 + d)
    · simp only [glue, htT, ↓reduceIte]
      exact (hxK ω).trans (le_max_left _ _)
    · simp only [glue, htT, ↓reduceIte]
      exact (hMℓ _ ω).trans (le_max_right _ _)
  · simp [glue, show (t0 + d) - 1 < (t0 + d) by omega]
  · simp [glue, show (t0 + d) - 1 < (t0 + d) by omega]

/-! ### Timeless optimality of the commitment to (2.32) -/

/-- Woodford (2003), p. 571 with Ch. 7 §1.1 (**optimality from a timeless perspective**): the
feasible plan `(π, x)` minimises the expected discounted loss (2.29) among all bounded plans that
satisfy (2.28) with a predetermined output gap and honour the same initial commitment on
`π^{qd}_{t0+d}` (the self-consistent constraint the policy would itself have implied). -/
def TimelesslyOptimal (β κ γ lam xs : ℝ) (d t0 : ℕ) (u π x : ℕ → Ω → ℝ) : Prop :=
  AS 𝔼 κ β γ d t0 u π x ∧ Predet 𝔼 d t0 x ∧ BoundedProc π ∧ BoundedProc x ∧
    ∀ π' x' : ℕ → Ω → ℝ, AS 𝔼 κ β γ d t0 u π' x' → Predet 𝔼 d t0 x' → BoundedProc π' →
      BoundedProc x' → qd γ π' (t0 + d) = qd γ π (t0 + d) →
        ∀ ω, welfare 𝔼 β γ lam xs d t0 π x ω ≤ welfare 𝔼 β γ lam xs d t0 π' x' ω

/-- Woodford (2003), p. 571 (**the commitment to (2.32) is timelessly optimal**): a bounded
equilibrium under (2.32) with `φ = λ/κ` is optimal from a timeless perspective. -/
theorem eqm_timelesslyOptimal {β κ γ lam xs : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    (hlam : 0 ≤ lam) (hPO : 𝔼.PullOut) {d t0 : ℕ} (ht0 : 1 ≤ t0) {u π x : ℕ → Ω → ℝ}
    (h : Eqm 𝔼 κ β γ (lam / κ) d t0 u π x) (hπ : BoundedProc π) (hx : BoundedProc x) :
    TimelesslyOptimal 𝔼 β κ γ lam xs d t0 u π x := by
  obtain ⟨hAS, hTC, hPx, _⟩ := h
  refine ⟨hAS, hPx, hπ, hx, fun π' x' hAS' hPx' hπ' hx' hq ω => ?_⟩
  exact welfare_le 𝔼 hβ0 hβ1 hlam hPO hAS hAS' hPx hPx' (foc_of_tc hκ ht0 hTC)
    (fun s hs => multOf_adapted 𝔼 hPx s hs) hπ hx hπ' hx' (multOf_bounded hx)
    (by rw [hq, sub_self, mul_zero, map_zero]) ω

/-- Woodford (2003), p. 571 (**summary**): for `0 < β < 1`, `κ, λ > 0`, `0 ≤ γ ≤ 1`, bounded
shocks and a history known at `t0`, the commitment to (2.32) with `φ = λ/κ` has a bounded
equilibrium, it is the only bounded equilibrium with that history, and it is optimal from a
timeless perspective. -/
theorem eq232_optimal_rule {β κ γ lam xs : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hPO : 𝔼.PullOut) {d t0 : ℕ} (ht0 : 1 ≤ t0)
    {u : ℕ → Ω → ℝ} (hu : BoundedProc u) {πh xh : Ω → ℝ} {K : ℝ} (hπK : ∀ ω, |πh ω| ≤ K)
    (hxK : ∀ ω, |xh ω| ≤ K) (hπh : 𝔼.E t0 πh = πh) (hxh : 𝔼.E t0 xh = xh) :
    ∃ π x : ℕ → Ω → ℝ, Eqm 𝔼 κ β γ (lam / κ) d t0 u π x ∧ BoundedProc π ∧ BoundedProc x ∧
      π (t0 + d - 1) = πh ∧ x (t0 + d - 1) = xh ∧
      TimelesslyOptimal 𝔼 β κ γ lam xs d t0 u π x ∧
      ∀ π' x' : ℕ → Ω → ℝ, Eqm 𝔼 κ β γ (lam / κ) d t0 u π' x' → BoundedProc x' →
        π' (t0 + d - 1) = πh → x' (t0 + d - 1) = xh →
          ∀ s, π' (t0 + d + s) = π (t0 + d + s) ∧ x' (t0 + d + s) = x (t0 + d + s) := by
  obtain ⟨π, x, h, hπ, hx, h1, h2⟩ :=
    eqm_exists 𝔼 hβ hκ (div_pos hlam hκ) hγ0 hγ1 ht0 hu hπK hxK hπh hxh
  refine ⟨π, x, h, hπ, hx, h1, h2,
    eqm_timelesslyOptimal 𝔼 hβ.le hβ1 hκ.ne' hlam.le hPO ht0 h hπ hx,
    fun π' x' h' hx' h1' h2' s => ?_⟩
  exact eqm_unique 𝔼 hβ hκ (div_pos hlam hκ) h' h hx' hx (by rw [h2', h2])
    (by rw [h1', h1]) s

/-- Woodford (2003), p. 570 (**existence of the `t0`-optimal commitment**): for `0 < β < 1`,
`κ, λ > 0`, `0 ≤ γ ≤ 1`, bounded shocks and `π_{t0+d−1}` known at `t0`, there is a bounded plan
satisfying (2.28) that minimises the expected discounted loss among **all** bounded feasible plans.
It satisfies (2.9) from `t0 + d + 1` on and the initial condition
`π^{qd}_{t0+d} + (λ/κ)(x_{t0+d} − x*) = 0` (the FOCs with `φ_{t0−1} = 0`); the date-`(t0+d−1)` value
of the returned output process is set to `x*`, which enters neither (2.28) nor the loss. -/
theorem t0_optimal_exists {β κ γ lam xs : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hPO : 𝔼.PullOut) {d t0 : ℕ} (ht0 : 1 ≤ t0)
    {u : ℕ → Ω → ℝ} (hu : BoundedProc u) {πh : Ω → ℝ} {K : ℝ} (hπK : ∀ ω, |πh ω| ≤ K)
    (hxsK : |xs| ≤ K) (hπh : 𝔼.E t0 πh = πh) :
    ∃ π x : ℕ → Ω → ℝ, AS 𝔼 κ β γ d t0 u π x ∧ Predet 𝔼 d t0 x ∧ Predet 𝔼 d t0 π ∧
      BoundedProc π ∧ BoundedProc x ∧ π (t0 + d - 1) = πh ∧
      (∀ ω, qd γ π (t0 + d) ω + lam / κ * (x (t0 + d) ω - xs) = 0) ∧
      ∀ π' x' : ℕ → Ω → ℝ, AS 𝔼 κ β γ d t0 u π' x' → Predet 𝔼 d t0 x' → BoundedProc π' →
        BoundedProc x' → ∀ ω,
          welfare 𝔼 β γ lam xs d t0 π x ω ≤ welfare 𝔼 β γ lam xs d t0 π' x' ω := by
  obtain ⟨π, x, ⟨hAS, hTC, hPx, hPπ⟩, hπ, hx, h1, h2⟩ :=
    eqm_exists 𝔼 (d := d) hβ hκ (div_pos hlam hκ) hγ0 hγ1 ht0 hu hπK (fun _ => hxsK) hπh
      (𝔼.const t0 xs)
  refine ⟨π, x, hAS, hPx, hPπ, hπ, hx, h1, fun ω => ?_, fun π' x' hAS' hPx' hπ' hx' ω => ?_⟩
  · have := hTC (t0 + d) le_rfl ω
    rw [h2] at this
    exact this
  · refine t0_optimal 𝔼 hβ.le hβ1 hlam.le hPO hAS hPx (foc_of_tc hκ.ne' ht0 hTC)
      (fun s hs => multOf_adapted 𝔼 hPx s hs) ?_ hπ hx (multOf_bounded hx) hAS' hPx' hπ' hx' ω
    funext ω'
    simp only [multOf, show t0 - 1 + d = t0 + d - 1 by omega, h2, sub_self, mul_zero,
      Pi.zero_apply]

/-! ### (2.33)–(2.34): interest rates should be forecastable `d` periods in advance -/

/-- Woodford (2003), eq. (2.33), p. 571: the IS relation with predetermined spending,
`x_t = E_{t−d} x_{t+1} − σ E_{t−d}(i_t − π_{t+1} − rⁿ_t)`, for `t ≥ t0 + d`. -/
def IS (σ : ℝ) (d t0 : ℕ) (rn π x i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, t0 + d ≤ t → x t = 𝔼.E (t - d) (x (t + 1)) - σ • 𝔼.E (t - d) (i t - π (t + 1) - rn t)

/-- Woodford (2003), p. 572: the forecastable component `E_{t−d} i_t` of the interest rate. -/
def fcst (d : ℕ) (i : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => 𝔼.E (t - d) (i t)

/-- Woodford (2003), p. 572: only the forecastable component of the interest rate enters (2.33):
a plan satisfies the IS relation iff it does so with `i_t` replaced by `E_{t−d} i_t`. -/
theorem IS_fcst_iff {σ : ℝ} {d t0 : ℕ} {rn π x i : ℕ → Ω → ℝ} :
    IS 𝔼 σ d t0 rn π x i ↔ IS 𝔼 σ d t0 rn π x (fcst 𝔼 d i) := by
  simp only [IS, fcst, map_sub, 𝔼.E_E_self]

/-- Woodford (2003), eq. (2.34), p. 572: `E_{t−d} i_t` itself satisfies (2.34),
`E_{t−d}(E_{t−d} i_t) = E_{t−d} i_t`. -/
theorem fcst_eq234 (d : ℕ) (i : ℕ → Ω → ℝ) (t : ℕ) :
    𝔼.E (t - d) (fcst 𝔼 d i t) = fcst 𝔼 d i t :=
  𝔼.E_E_self _ _

/-- Woodford (2003), p. 572: the forecastable component of a bounded interest rate is bounded. -/
theorem fcst_bounded {d : ℕ} {i : ℕ → Ω → ℝ} (hi : BoundedProc i) : BoundedProc (fcst 𝔼 d i) := by
  obtain ⟨M, hM⟩ := hi
  exact ⟨M, fun t ω => 𝔼.abs_E_le (hM t) _ ω⟩

/-- Woodford (2003), §2.4 with Ch. 6 §4 (p. 572): the feasible plans of the problem with an
interest-rate stabilisation objective — (2.28) and (2.33) at every `t ≥ t0 + d`, with inflation
and the output gap predetermined. -/
def FeasibleI (κ β γ σ : ℝ) (d t0 : ℕ) (u rn π x i : ℕ → Ω → ℝ) : Prop :=
  AS 𝔼 κ β γ d t0 u π x ∧ IS 𝔼 σ d t0 rn π x i ∧ Predet 𝔼 d t0 x ∧ Predet 𝔼 d t0 π

/-- Woodford (2003), p. 572 (with Ch. 6 §4.1–4.2): the expected discounted loss including an
interest-rate term,
`E_{t0} ∑_{t ≥ t0+d} βᵗ [½(π^{qd}_t)² + (λ/2)(x_t − x*)² + (λᵢ/2)(i_t − i*)²]`. -/
noncomputable def welfareI (β γ lam xs lami istar : ℝ) (d t0 : ℕ) (π x i : ℕ → Ω → ℝ) :
    Ω → ℝ :=
  𝔼.E t0 (fun ω => ∑' n, β ^ (t0 + d + n) *
    (loss γ lam xs π x (t0 + d + n) ω + lami / 2 * (i (t0 + d + n) ω - istar) ^ 2))

/-- Woodford (2003), p. 572: the interest-rate part `E_{t0} ∑ βᵗ (λᵢ/2)(i_t − i*)²` of the loss. -/
noncomputable def iLoss (β lami istar : ℝ) (d t0 : ℕ) (i : ℕ → Ω → ℝ) : Ω → ℝ :=
  𝔼.E t0 (fun ω => ∑' n, β ^ (t0 + d + n) * (lami / 2 * (i (t0 + d + n) ω - istar) ^ 2))

/-- Woodford (2003), p. 570: `E_{t0}` commutes with a `β`-discounted series of uniformly bounded
random variables. -/
theorem E_tsum_weighted {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (T t0 : ℕ) {f : ℕ → Ω → ℝ}
    (hf : ∀ n ω, |f n ω| ≤ M) (ω : Ω) :
    𝔼.E t0 (fun ω' => ∑' n, β ^ (T + n) * f n ω') ω = ∑' n, β ^ (T + n) * 𝔼.E t0 (f n) ω := by
  have hg : ∀ n ω', |β ^ (T + n) * f n ω'| ≤ β ^ n * M := by
    intro n ω'
    rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 _)]
    have hb : β ^ (T + n) ≤ β ^ n := pow_le_pow_of_le_one hβ0 hβ1.le (by omega)
    exact mul_le_mul hb (hf _ _) (abs_nonneg _) (pow_nonneg hβ0 _)
  rw [𝔼.E_tsum hβ0 hβ1 hg t0 ω]
  refine tsum_congr fun n => ?_
  change 𝔼.E t0 (β ^ (T + n) • f n) ω = _
  rw [map_smul]
  rfl

/-- Woodford (2003), p. 572: the period interest-rate loss of a bounded process is bounded. -/
theorem iLossTerm_bounded {lami istar : ℝ} {i : ℕ → Ω → ℝ} (hi : BoundedProc i) :
    ∃ M, ∀ t ω, |lami / 2 * (i t ω - istar) ^ 2| ≤ M := by
  obtain ⟨M, hM⟩ := hi
  refine ⟨|lami| / 2 * (M + |istar|) ^ 2, fun t ω => ?_⟩
  have h2 : |i t ω - istar| ≤ M + |istar| := (abs_sub _ _).trans (add_le_add (hM t ω) le_rfl)
  have e2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
  rw [sq_abs] at e2
  rw [abs_mul, abs_div, abs_two, abs_of_nonneg (sq_nonneg (i t ω - istar))]
  gcongr

/-- Woodford (2003), p. 572: the total loss splits into the inflation/output part (2.29) and the
interest-rate part. -/
theorem welfareI_split {β γ lam xs lami istar : ℝ} {d t0 : ℕ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {π x i : ℕ → Ω → ℝ} (hπ : BoundedProc π) (hx : BoundedProc x) (hi : BoundedProc i)
    (ω : Ω) :
    welfareI 𝔼 β γ lam xs lami istar d t0 π x i ω =
      welfare 𝔼 β γ lam xs d t0 π x ω + iLoss 𝔼 β lami istar d t0 i ω := by
  obtain ⟨M1, hM1⟩ := loss_bounded γ lam xs hπ hx
  obtain ⟨M2, hM2⟩ := iLossTerm_bounded (lami := lami) (istar := istar) hi
  set f1 : ℕ → Ω → ℝ := fun n => loss γ lam xs π x (t0 + d + n) with hf1
  set f2 : ℕ → Ω → ℝ := fun n ω => lami / 2 * (i (t0 + d + n) ω - istar) ^ 2 with hf2
  have hs : ∀ n ω, |f1 n ω + f2 n ω| ≤ M1 + M2 := fun n ω =>
    (abs_add_le _ _).trans (add_le_add (hM1 _ ω) (hM2 _ ω))
  have e0 := E_tsum_weighted 𝔼 hβ0 hβ1 (t0 + d) t0 hs ω
  have e1 := E_tsum_weighted 𝔼 hβ0 hβ1 (t0 + d) t0 (fun n ω => hM1 (t0 + d + n) ω) ω
  have e2 := E_tsum_weighted 𝔼 hβ0 hβ1 (t0 + d) t0 (f := f2) (fun n ω => hM2 (t0 + d + n) ω) ω
  have hs1 : Summable (fun n => β ^ (t0 + d + n) * 𝔼.E t0 (f1 n) ω) :=
    summable_weighted hβ0 hβ1 _ (fun n => 𝔼.abs_E_le (hM1 _) t0 ω)
  have hs2 : Summable (fun n => β ^ (t0 + d + n) * 𝔼.E t0 (f2 n) ω) :=
    summable_weighted hβ0 hβ1 _ (fun n => 𝔼.abs_E_le (fun ω' => hM2 _ ω') t0 ω)
  unfold welfareI welfare iLoss
  change 𝔼.E t0 (fun ω' => ∑' n, β ^ (t0 + d + n) * (f1 n ω' + f2 n ω')) ω =
    𝔼.E t0 (fun ω' => ∑' n, β ^ (t0 + d + n) * f1 n ω') ω +
      𝔼.E t0 (fun ω' => ∑' n, β ^ (t0 + d + n) * f2 n ω') ω
  rw [e0, e1, e2, ← hs1.tsum_add hs2]
  refine tsum_congr fun n => ?_
  rw [← mul_add]
  congr 1
  change 𝔼.E t0 (f1 n + f2 n) ω = _
  rw [map_add]
  rfl

/-- Woodford (2003), p. 572 (**the variance argument**): with pull-out, for `t0 ≤ s`,
`E_{t0}(y − c)² = E_{t0}(E_s y − c)² + E_{t0}(y − E_s y)²` — the unforecastable component only
adds to the expected squared deviation. -/
theorem var_decomp (hPO : 𝔼.PullOut) {s t0 : ℕ} (hs : t0 ≤ s) (y : Ω → ℝ) (c : ℝ) :
    𝔼.E t0 (fun ω => (y ω - c) ^ 2) =
      𝔼.E t0 (fun ω => (𝔼.E s y ω - c) ^ 2) + 𝔼.E t0 (fun ω => (y ω - 𝔼.E s y ω) ^ 2) := by
  set a : Ω → ℝ := 𝔼.E s y - fun _ => c with ha
  have hak : 𝔼.E s a = a := by rw [ha, map_sub, 𝔼.E_E_self, 𝔼.const]
  have hcross : 𝔼.E t0 (a * (y - 𝔼.E s y)) = 0 := by
    rw [← 𝔼.tower hs, hPO s a _ hak, map_sub, 𝔼.E_E_self, sub_self, mul_zero, map_zero]
  have hfun : (fun ω => (y ω - c) ^ 2) = (fun ω => (𝔼.E s y ω - c) ^ 2) +
      (fun ω => (y ω - 𝔼.E s y ω) ^ 2) + (2 : ℝ) • (a * (y - 𝔼.E s y)) := by
    funext ω
    simp only [ha, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [hfun, map_add, map_add, map_smul, hcross, smul_zero, add_zero]

/-- Woodford (2003), p. 572: the interest-rate loss of `i` equals that of its forecastable part
`E_{t−d} i_t` plus `∑ βᵗ (λᵢ/2) E_{t0}(i_t − E_{t−d} i_t)²`. -/
theorem iLoss_decomp {β lami istar : ℝ} {d t0 : ℕ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hPO : 𝔼.PullOut) {i : ℕ → Ω → ℝ} (hi : BoundedProc i) (ω : Ω) :
    iLoss 𝔼 β lami istar d t0 i ω = iLoss 𝔼 β lami istar d t0 (fcst 𝔼 d i) ω +
      ∑' n, β ^ (t0 + d + n) * (lami / 2 *
        𝔼.E t0 (fun ω' => (i (t0 + d + n) ω' - fcst 𝔼 d i (t0 + d + n) ω') ^ 2) ω) := by
  obtain ⟨M, hM⟩ := iLossTerm_bounded (lami := lami) (istar := istar) hi
  obtain ⟨M', hM'⟩ := iLossTerm_bounded (lami := lami) (istar := istar) (fcst_bounded 𝔼 hi)
  obtain ⟨B, hB⟩ := hi
  have e1 := E_tsum_weighted 𝔼 hβ0 hβ1 (t0 + d) t0
    (f := fun n ω => lami / 2 * (i (t0 + d + n) ω - istar) ^ 2) (fun n ω => hM _ ω) ω
  have e2 := E_tsum_weighted 𝔼 hβ0 hβ1 (t0 + d) t0
    (f := fun n ω => lami / 2 * (fcst 𝔼 d i (t0 + d + n) ω - istar) ^ 2) (fun n ω => hM' _ ω) ω
  have hvb : ∀ n, |lami / 2 * 𝔼.E t0 (fun ω' => (i (t0 + d + n) ω'
      - fcst 𝔼 d i (t0 + d + n) ω') ^ 2) ω| ≤ |lami| / 2 * (B + B) ^ 2 := by
    intro n
    rw [abs_mul, abs_div, abs_two]
    gcongr
    refine 𝔼.abs_E_le (fun ω' => ?_) t0 ω
    have h1 : |i (t0 + d + n) ω' - fcst 𝔼 d i (t0 + d + n) ω'| ≤ B + B :=
      (abs_sub _ _).trans (add_le_add (hB _ ω') (𝔼.abs_E_le (hB _) _ ω'))
    have := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs] at this
    rwa [abs_of_nonneg (sq_nonneg _)]
  have hs2 : Summable (fun n => β ^ (t0 + d + n) *
      𝔼.E t0 (fun ω => lami / 2 * (fcst 𝔼 d i (t0 + d + n) ω - istar) ^ 2) ω) :=
    summable_weighted hβ0 hβ1 _ (fun n => 𝔼.abs_E_le (fun ω' => hM' _ ω') t0 ω)
  have hs3 := summable_weighted hβ0 hβ1 (t0 + d) hvb
  unfold iLoss
  rw [e1, e2, ← hs2.tsum_add hs3]
  refine tsum_congr fun n => ?_
  rw [← mul_add]
  congr 1
  have hv := var_decomp 𝔼 hPO (show t0 ≤ t0 + d + n - d by omega) (i (t0 + d + n)) istar
  have hsm : ∀ g : Ω → ℝ, 𝔼.E t0 (fun ω' => lami / 2 * g ω') = (lami / 2) • 𝔼.E t0 g := by
    intro g
    rw [← map_smul]
    rfl
  rw [hsm, hsm, hv]
  simp only [fcst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), p. 572 (**replacing `i_t` by `E_{t−d} i_t` never hurts**): for `λᵢ ≥ 0`, if
`(π, x, i)` is a bounded feasible plan then so is `(π, x, E_{t−d} i)`, the inflation/output
paths are unchanged, and its total loss is lower by exactly
`∑ βᵗ (λᵢ/2) E_{t0}(i_t − E_{t−d} i_t)² ≥ 0`. -/
theorem fcst_improves {κ β γ σ lam xs lami istar : ℝ} {d t0 : ℕ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hlami : 0 ≤ lami) (hPO : 𝔼.PullOut) {u rn π x i : ℕ → Ω → ℝ}
    (hF : FeasibleI 𝔼 κ β γ σ d t0 u rn π x i) (hπ : BoundedProc π) (hx : BoundedProc x)
    (hi : BoundedProc i) :
    FeasibleI 𝔼 κ β γ σ d t0 u rn π x (fcst 𝔼 d i) ∧ BoundedProc (fcst 𝔼 d i) ∧
      ∀ ω, welfareI 𝔼 β γ lam xs lami istar d t0 π x i ω =
        welfareI 𝔼 β γ lam xs lami istar d t0 π x (fcst 𝔼 d i) ω +
        ∑' n, β ^ (t0 + d + n) * (lami / 2 *
          𝔼.E t0 (fun ω' => (i (t0 + d + n) ω' - fcst 𝔼 d i (t0 + d + n) ω') ^ 2) ω) ∧
      welfareI 𝔼 β γ lam xs lami istar d t0 π x (fcst 𝔼 d i) ω ≤
        welfareI 𝔼 β γ lam xs lami istar d t0 π x i ω := by
  obtain ⟨hAS, hIS, hPx, hPπ⟩ := hF
  have hfb := fcst_bounded 𝔼 (d := d) hi
  refine ⟨⟨hAS, IS_fcst_iff 𝔼 |>.mp hIS, hPx, hPπ⟩, hfb, fun ω => ?_⟩
  have hdec := iLoss_decomp 𝔼 (lami := lami) (istar := istar) (d := d) (t0 := t0) hβ0 hβ1 hPO hi ω
  rw [welfareI_split 𝔼 hβ0 hβ1 hπ hx hi, welfareI_split 𝔼 hβ0 hβ1 hπ hx hfb, hdec]
  refine ⟨by ring, ?_⟩
  have hnn : 0 ≤ ∑' n, β ^ (t0 + d + n) * (lami / 2 *
      𝔼.E t0 (fun ω' => (i (t0 + d + n) ω' - fcst 𝔼 d i (t0 + d + n) ω') ^ 2) ω) := by
    refine tsum_nonneg fun n => mul_nonneg (pow_nonneg hβ0 _) (mul_nonneg (by linarith) ?_)
    have := 𝔼.mono t0 (show (0 : Ω → ℝ) ≤ fun ω' =>
      (i (t0 + d + n) ω' - fcst 𝔼 d i (t0 + d + n) ω') ^ 2 from fun ω' => sq_nonneg _) ω
    simpa using this
  linarith

/-- Woodford (2003), eq. (2.34), p. 572 (**optimality of forecastable interest rates**): for any
`λᵢ > 0` (and `0 < β < 1`), a plan that minimises the total loss among bounded feasible plans has
`E_{t0}(i_t − E_{t−d} i_t)² = 0` at every date `t ≥ t0 + d`: the unforecastable component of the
interest rate is zero in mean square. -/
theorem eq234_of_optimal {κ β γ σ lam xs lami istar : ℝ} {d t0 : ℕ} (hβ : 0 < β) (hβ1 : β < 1)
    (hlami : 0 < lami) (hPO : 𝔼.PullOut) {u rn π x i : ℕ → Ω → ℝ}
    (hF : FeasibleI 𝔼 κ β γ σ d t0 u rn π x i) (hπ : BoundedProc π) (hx : BoundedProc x)
    (hi : BoundedProc i)
    (hopt : ∀ π' x' i' : ℕ → Ω → ℝ, FeasibleI 𝔼 κ β γ σ d t0 u rn π' x' i' →
      BoundedProc π' → BoundedProc x' → BoundedProc i' → ∀ ω,
        welfareI 𝔼 β γ lam xs lami istar d t0 π x i ω ≤
          welfareI 𝔼 β γ lam xs lami istar d t0 π' x' i' ω)
    (n : ℕ) (ω : Ω) :
    𝔼.E t0 (fun ω' => (i (t0 + d + n) ω' - 𝔼.E (t0 + n) (i (t0 + d + n)) ω') ^ 2) ω = 0 := by
  obtain ⟨hF', hfb, hw⟩ :=
    fcst_improves 𝔼 (lam := lam) (xs := xs) (istar := istar) hβ.le hβ1 hlami.le hPO hF hπ hx hi
  obtain ⟨heq, -⟩ := hw ω
  have hle := hopt π x (fcst 𝔼 d i) hF' hπ hx hfb ω
  set v : ℕ → ℝ := fun m => 𝔼.E t0 (fun ω' => (i (t0 + d + m) ω'
    - fcst 𝔼 d i (t0 + d + m) ω') ^ 2) ω with hv
  have hv0 : ∀ m, 0 ≤ v m := by
    intro m
    have := 𝔼.mono t0 (show (0 : Ω → ℝ) ≤ fun ω' =>
      (i (t0 + d + m) ω' - fcst 𝔼 d i (t0 + d + m) ω') ^ 2 from fun ω' => sq_nonneg _) ω
    simpa using this
  obtain ⟨B, hB⟩ := hi
  have hvb : ∀ m, |lami / 2 * v m| ≤ lami / 2 * (B + B) ^ 2 := by
    intro m
    rw [abs_of_nonneg (mul_nonneg (by linarith) (hv0 m))]
    gcongr
    refine (le_abs_self _).trans (𝔼.abs_E_le (fun ω' => ?_) t0 ω)
    have h1 : |i (t0 + d + m) ω' - fcst 𝔼 d i (t0 + d + m) ω'| ≤ B + B :=
      (abs_sub _ _).trans (add_le_add (hB _ ω') (𝔼.abs_E_le (hB _) _ ω'))
    have := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs] at this
    rwa [abs_of_nonneg (sq_nonneg _)]
  have hs := summable_weighted hβ.le hβ1 (t0 + d) hvb
  have hnn : ∀ m, 0 ≤ β ^ (t0 + d + m) * (lami / 2 * v m) :=
    fun m => mul_nonneg (pow_nonneg hβ.le _) (mul_nonneg (by linarith) (hv0 m))
  have hsum0 : ∑' m, β ^ (t0 + d + m) * (lami / 2 * v m) = 0 := by
    have h0 : 0 ≤ ∑' m, β ^ (t0 + d + m) * (lami / 2 * v m) := tsum_nonneg hnn
    simp only [hv] at heq h0 ⊢
    linarith
  have hS : HasSum (fun m => β ^ (t0 + d + m) * (lami / 2 * v m)) 0 := by
    have := hs.hasSum
    rwa [hsum0] at this
  have hz := congrFun ((hasSum_zero_iff_of_nonneg hnn).mp hS) n
  simp only [Pi.zero_apply] at hz
  have h1 := (mul_eq_zero.mp hz).resolve_left (pow_pos hβ _).ne'
  have h2 := (mul_eq_zero.mp h1).resolve_left (by positivity)
  simp only [hv, fcst, show t0 + d + n - d = t0 + n by omega] at h2
  exact h2

/-- Woodford (2003), p. 572: (2.33) determines the forecastable component of the interest rate
from the paths of inflation and the output gap,
`E_{t−d} i_t = E_{t−d} π_{t+1} + E_{t−d} rⁿ_t + σ⁻¹(E_{t−d} x_{t+1} − x_t)` (`x` predetermined). -/
theorem fcst_i_formula {σ : ℝ} (hσ : σ ≠ 0) {d t0 : ℕ} {rn π x i : ℕ → Ω → ℝ}
    (hIS : IS 𝔼 σ d t0 rn π x i) {t : ℕ} (ht : t0 + d ≤ t) :
    𝔼.E (t - d) (i t) = 𝔼.E (t - d) (π (t + 1)) + 𝔼.E (t - d) (rn t) +
      σ⁻¹ • (𝔼.E (t - d) (x (t + 1)) - x t) := by
  have h := hIS t ht
  funext ω
  have h' := congrFun h ω
  simp only [map_sub, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply] at h' ⊢
  field_simp
  linarith

/-- Woodford (2003), p. 572: with (2.34) the whole interest-rate path is pinned down — two plans
with the same inflation and output paths that satisfy (2.33) and (2.34) have the same interest
rate at every date `t ≥ t0 + d` (so (2.32), which fixes `π` and `x`, and (2.34) determine `i`). -/
theorem eq234_determines_i {σ : ℝ} (hσ : σ ≠ 0) {d t0 : ℕ} {rn π x i i' : ℕ → Ω → ℝ}
    (hIS : IS 𝔼 σ d t0 rn π x i) (hIS' : IS 𝔼 σ d t0 rn π x i')
    (h : ∀ t, t0 + d ≤ t → 𝔼.E (t - d) (i t) = i t)
    (h' : ∀ t, t0 + d ≤ t → 𝔼.E (t - d) (i' t) = i' t) {t : ℕ} (ht : t0 + d ≤ t) :
    i t = i' t := by
  rw [← h t ht, ← h' t ht, fcst_i_formula 𝔼 hσ hIS ht, fcst_i_formula 𝔼 hσ hIS' ht]
end Woodford.OptimalPolicyRules.InflTargetPredetermined
