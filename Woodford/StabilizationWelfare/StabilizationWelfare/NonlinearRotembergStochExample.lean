/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergStochModels

/-!
# The second-order welfare of Rotemberg and Calvo differs when `m < 1`

Woodford (2003), *Interest and Prices*, Chapter 6, §2 and §4.1, Chapter 3 fn. 44, Chapter 4 (2.7).
`NonlinearRotembergStochModels.models_welfare_difference` shows that the second-order welfare of
the two perturbation equilibria differs by exactly `(ε²/2)(1 − m)Σβᵗ(ŷ₂ᴿ − ŷ₂ᶜ)`. This module
shows that the second-order output paths do differ, so the difference is NOT zero in general:
on the one-state chain (a permanent interest-rate disturbance `εν̄`), both equilibria satisfy
`ŷ = Y(π)` and `(1 − φ_π)π − φ_yY(π) = εν̄` for their own steady-state output curves `Y = Y_R`
(`NonlinearRotembergBoundary.ssY`) and `Y = Y_C` (`NonlinearRotembergTrendWelfare.yC`), which agree
to first order and differ to second order.

## Main results

* `one_state_jets`: if `ŷ = Y(π)` and `(1 − φ_π)π − φ_yŷ = εν̄` along a `C²` family, then
  `ŷ₂ = (1 − φ_π)ν̄²Y″(0)/N₁³` with `N₁ = 1 − φ_π − φ_yY′(0)`.
* `rot_one_state`, `calvo_one_state`: the two equilibria on the one-state chain satisfy these
  relations.
* **`one_state_difference`**: `ŷ₂ᴿ − ŷ₂ᶜ = (1 − φ_π)ν̄²(Y_R″(0) − Y_C″(0))/N₁³`, so the
  second-order welfare difference is `(1 − m)(1 − φ_π)ν̄²(Y_R″(0) − Y_C″(0))/((1 − β)N₁³)`.
* **`welfare_differs`**: at `β = α = 1/2`, `σ = 1`, `ω = 0`, `θ = 2`, `m = 1/2`, `φ_π = 3/2`,
  `φ_y = 0`, `ν̄ = 1` (Taylor principle holds) the second-order welfare difference is `80/9 ≠ 0`:
  Rotemberg and Calvo do NOT have the same second-order welfare under the equivalence map when the
  steady state is distorted.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergStochExample

open Filter Topology
open NonlinearRotembergJets NonlinearRotembergStochWelfare NonlinearRotembergStochModels
open NonlinearRotembergLinks (wedge)
open NonlinearRotembergBoundary (ssY)
open NonlinearRotembergTrendWelfare (KR J_YR yC lx ell J_yC)

/-- Woodford (2003), App. A.3: Jets are unique. -/
theorem J2_unique {f : ℝ → ℝ} {a1 a2 b1 b2 : ℝ} (ha : J2 f a1 a2) (hb : J2 f b1 b2) :
    a1 = b1 ∧ a2 = b2 := by
  obtain ⟨h1, h2⟩ := J2_deriv ha
  obtain ⟨k1, k2⟩ := J2_deriv hb
  exact ⟨h1.symm.trans k1, h2.symm.trans k2⟩

/-- Woodford (2003), Ch. 4 (2.7) (**the second-order output of a permanent disturbance**): if a
`C²` family has `ŷ = Y(π)` and `(1 − φ_π)π − φ_yŷ = εν̄` near `ε = 0`, with `Y(0) = 0` and
`N₁ = 1 − φ_π − φ_yY₁ ≠ 0`, then `π₁ = ν̄/N₁` and `ŷ₂ = (1 − φ_π)ν̄²Y₂/N₁³`. -/
theorem one_state_jets {Y y π : ℝ → ℝ} {Y1 Y2 y1 y2 π1 π2 φ φy ν : ℝ} (hY : J2 Y Y1 Y2)
    (hy : J2 y y1 y2) (hπ : J2 π π1 π2) (hπ0 : π 0 = 0)
    (hyY : ∀ᶠ ε in 𝓝 0, y ε = Y (π ε)) (hN : ∀ᶠ ε in 𝓝 0, (1 - φ) * π ε - φy * y ε = ε * ν)
    (hN1 : 1 - φ - φy * Y1 ≠ 0) :
    π1 = ν / (1 - φ - φy * Y1) ∧ y2 = (1 - φ) * ν ^ 2 * Y2 / (1 - φ - φy * Y1) ^ 3 := by
  obtain ⟨Y1f, hYe, hYd, hY10⟩ := hY
  have hYe' : ∀ᶠ x in 𝓝 (π 0), HasDerivAt Y (Y1f x) x := by rw [hπ0]; exact hYe
  have hYd' : HasDerivAt Y1f Y2 (π 0) := by rw [hπ0]; exact hYd
  have hc := J2_comp hYe' hYd' hπ
  have hY10' : Y1f (π 0) = Y1 := by rw [hπ0]; exact hY10
  rw [hY10'] at hc
  have hc' : J2 y (Y1 * π1) (Y2 * π1 * π1 + Y1 * π2) :=
    J2_congr_ev hc (hyY.mono fun ε h => h.symm)
  obtain ⟨e1, e2⟩ := J2_unique hy hc'
  have hl := J2_sub (J2_const_mul (1 - φ) hπ) (J2_const_mul φy hy)
  have hr : J2 (fun ε => ε * ν) ν 0 :=
    J2_eq (J2_congr (J2_const_mul ν J2_id) fun ε => by ring) (by ring) (by ring)
  have hl' := J2_congr_ev hl hN
  obtain ⟨f1, f2⟩ := J2_unique hl' hr
  rw [e1] at f1
  rw [e2] at f2
  have hπ1 : π1 = ν / (1 - φ - φy * Y1) := by
    rw [eq_div_iff hN1]; linarith
  refine ⟨hπ1, ?_⟩
  have hπ2 : π2 * (1 - φ - φy * Y1) = φy * Y2 * π1 * π1 := by linarith
  rw [e2]
  have hπ2' : π2 = φy * Y2 * π1 * π1 / (1 - φ - φy * Y1) := by
    rw [eq_div_iff hN1]; exact hπ2
  rw [hπ2', hπ1]
  field_simp
  ring

/-! ## The two steady-state output curves -/

/-- Woodford (2003), Ch. 3 fn. 44 (**the Rotemberg pricing steady state**): on the resource
manifold, `(1 − β)G = H` gives `ŷ = Y_R(π)` (`NonlinearRotembergBoundary.ssY`). -/
theorem ssY_of_pricing {p : NonlinearRotemberg.Par} (hp : p.Basic) {z : Fin 3 → ℝ}
    (hpr : (1 - p.β) * NonlinearRotemberg.Gadj p z = NonlinearRotemberg.Hmc p 0 z)
    (hres : NonlinearRotembergCentreLocal.Res p z) : z 0 = ssY p (z 1) := by
  have hc := NonlinearRotembergCentreLocal.res_c hres
  have hθm : 0 < p.θ * p.m := mul_pos (by linarith [hp.one_lt_θ]) hp.m_pos
  have hs : p.σ + p.ω ≠ 0 := by linarith [hp.σ_pos, hp.ω_nonneg]
  set A := Real.exp (z 0 - p.σ * z 2) with hA
  have hA0 : 0 < A := Real.exp_pos _
  simp only [NonlinearRotemberg.Gadj, NonlinearRotemberg.Hmc, Pi.zero_apply, add_zero,
    mul_zero, sub_zero] at hpr
  have hθ0 : p.θ ≠ 0 := by linarith [hp.one_lt_θ]
  have hm0 : p.m ≠ 0 := hp.m_pos.ne'
  have h1 : Real.exp ((1 + p.ω) * z 0) = A * (1 + (1 - p.β) * p.ψ *
      ((Real.exp (z 1) - 1) * Real.exp (z 1)) / (p.θ * p.m)) := by
    rw [← hA] at hpr
    field_simp
    linear_combination -hpr
  have hpos : 0 < 1 + (1 - p.β) * p.ψ * ((Real.exp (z 1) - 1) * Real.exp (z 1)) /
      (p.θ * p.m) := by
    have := Real.exp_pos ((1 + p.ω) * z 0)
    rw [h1] at this; exact pos_of_mul_pos_right this hA0.le
  have hlog : Real.log (1 + (1 - p.β) * p.ψ * ((Real.exp (z 1) - 1) * Real.exp (z 1)) /
      (p.θ * p.m)) = (1 + p.ω) * z 0 - (z 0 - p.σ * z 2) := by
    rw [eq_sub_iff_add_eq, ← Real.exp_eq_exp, Real.exp_add, Real.exp_log hpos, ← hA, mul_comm,
      h1]
  unfold ssY
  rw [hlog, hc, eq_div_iff hs]
  ring

/-- Woodford (2003), Ch. 3 (**the Calvo steady state**): the recursions for `F̂`, `K̂` and the price
index at a constant state give `ŷ = Y_C(π)` (`NonlinearRotembergTrendWelfare.yC`). -/
theorem yC_of_eqs (p : NonlinearRotemberg.Par) {α y π F K : ℝ} (hα1 : α < 1) (hθ : 1 < p.θ)
    (hs : p.σ + p.ω ≠ 0) (hω : 0 ≤ p.ω)
    (e1 : Real.exp F - (1 - α * p.β) * Real.exp ((1 - p.σ) * y) -
      α * p.β * Real.exp ((p.θ - 1) * π + F) = 0)
    (e2 : Real.exp K - (1 - α * p.β) * Real.exp ((1 + p.ω) * y) -
      α * p.β * Real.exp (p.θ * (1 + p.ω) * π + K) = 0)
    (e3 : α * (Real.exp ((p.θ - 1) * π) - 1) +
      (1 - α) * (Real.exp (-((p.θ - 1) * ((K - F) / (1 + p.ω * p.θ)))) - 1) = 0)
    (hab : 0 < 1 - α * p.β) : y = yC p α π := by
  have h1α : 0 < 1 - α := by linarith
  have hb : p.θ - 1 ≠ 0 := by linarith
  have hc0 : 1 + p.ω * p.θ ≠ 0 := by
    have : 0 ≤ p.ω * p.θ := mul_nonneg hω (by linarith)
    linarith
  -- `F̂`
  have hF1 : Real.exp F * (1 - α * p.β * Real.exp ((p.θ - 1) * π)) =
      (1 - α * p.β) * Real.exp ((1 - p.σ) * y) := by
    rw [Real.exp_add] at e1; linear_combination e1
  have hg1 : 0 < 1 - α * p.β * Real.exp ((p.θ - 1) * π) := by
    have := mul_pos hab (Real.exp_pos ((1 - p.σ) * y))
    rw [← hF1] at this; exact pos_of_mul_pos_right this (Real.exp_pos F).le
  have hF : F = Real.log (1 - α * p.β) + (1 - p.σ) * y - ell (α * p.β) (p.θ - 1) π := by
    unfold ell
    rw [← Real.exp_eq_exp, Real.exp_sub, Real.exp_add, Real.exp_log hab, Real.exp_log hg1,
      eq_div_iff hg1.ne', hF1]
  -- `K̂`
  have hK1 : Real.exp K * (1 - α * p.β * Real.exp (p.θ * (1 + p.ω) * π)) =
      (1 - α * p.β) * Real.exp ((1 + p.ω) * y) := by
    rw [Real.exp_add] at e2; linear_combination e2
  have hg2 : 0 < 1 - α * p.β * Real.exp (p.θ * (1 + p.ω) * π) := by
    have := mul_pos hab (Real.exp_pos ((1 + p.ω) * y))
    rw [← hK1] at this; exact pos_of_mul_pos_right this (Real.exp_pos K).le
  have hK : K = Real.log (1 - α * p.β) + (1 + p.ω) * y -
      ell (α * p.β) (p.θ * (1 + p.ω)) π := by
    unfold ell
    rw [← Real.exp_eq_exp, Real.exp_sub, Real.exp_add, Real.exp_log hab, Real.exp_log hg2,
      eq_div_iff hg2.ne', hK1]
  -- the price index
  set x := (K - F) / (1 + p.ω * p.θ) with hx
  have hP1 : (1 - α) * Real.exp (-((p.θ - 1) * x)) = 1 - α * Real.exp ((p.θ - 1) * π) := by
    linear_combination e3
  have hg3 : 0 < 1 - α * Real.exp ((p.θ - 1) * π) := by
    rw [← hP1]; exact mul_pos h1α (Real.exp_pos _)
  have hxl : x = lx p α π := by
    have h2 : -((p.θ - 1) * x) = Real.log (1 - α * Real.exp ((p.θ - 1) * π)) -
        Real.log (1 - α) := by
      rw [← Real.exp_eq_exp, Real.exp_sub, Real.exp_log hg3, Real.exp_log h1α, eq_div_iff
        h1α.ne', mul_comm, hP1]
    have h3 : x * (p.θ - 1) = -(Real.log (1 - α * Real.exp ((p.θ - 1) * π)) -
        Real.log (1 - α)) := by linarith
    unfold lx ell
    rw [eq_div_iff hb]
    exact h3
  have hKF : K - F = (1 + p.ω * p.θ) * lx p α π := by
    rw [← hxl, hx]; field_simp
  unfold yC
  rw [eq_div_iff hs]
  rw [hK, hF] at hKF
  linear_combination hKF

/-! ## The one-state chain -/

/-- Woodford (2003), App. A.3: The one-state chain (a permanent disturbance). -/
def P1 : Unit → Unit → ℝ := fun _ _ => 1

/-- Woodford (2003), App. A.3: The one-state chain is stochastic. -/
theorem P1_stochastic : NonlinearNKMarkov.Stochastic P1 :=
  ⟨fun _ _ => zero_le_one, fun _ => by simp [P1]⟩

/-- Woodford (2003), Ch. 4 (2.7) and Ch. 3 fn. 44 (**the Rotemberg equilibrium with a permanent
interest-rate disturbance `εν̄`**): `ŷ = Y_R(π)` and `(1 − φ_π)π − φ_yŷ = εν̄`. -/
theorem rot_one_state {p : NonlinearRotemberg.Par} (hp : p.Basic) {ν0 ε : ℝ}
    {w : Unit → Fin 3 → ℝ}
    (h : NonlinearRotembergSmooth.PhiJ P1 (xiR (fun _ => ν0) (fun _ => 0))
      (NonlinearRotembergSmooth.vecOf p, ε) w = 0) :
    w () 0 = ssY p (w () 1) ∧ (1 - p.φ) * w () 1 - p.φy * w () 0 = ε * ν0 := by
  have hc : ∀ i, NonlinearRotemberg.Qmap p (ε • xiR (fun _ => ν0) (fun _ => 0) (), w ()) i +
      NonlinearRotemberg.Nmap p (ε • xiR (fun _ => ν0) (fun _ => 0) (), w ()) i = 0 := fun i => by
    have := congrFun (congrFun h ()) i
    rw [NonlinearRotembergSmooth.PhiJ_apply] at this
    simp only [P1, one_mul, Finset.univ_unique, Finset.sum_singleton, Pi.zero_apply] at this
    exact this
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  simp only [NonlinearRotemberg.Qmap, NonlinearRotemberg.Nmap, xiR, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Pi.smul_apply, smul_eq_mul] at h0 h1 h2
  have hres : NonlinearRotembergCentreLocal.Res p (w ()) := by
    simp only [NonlinearRotembergCentreLocal.Res, NonlinearRotemberg.Qmap, Matrix.cons_val]
    linarith
  have hH : NonlinearRotemberg.Hmc p (ε • ![ν0, 0, 0]) (w ()) =
      NonlinearRotemberg.Hmc p 0 (w ()) := by
    simp [NonlinearRotemberg.Hmc]
  have hpr : (1 - p.β) * NonlinearRotemberg.Gadj p (w ()) = NonlinearRotemberg.Hmc p 0 (w ()) := by
    rw [← hH]; linarith
  refine ⟨ssY_of_pricing hp hpr hres, ?_⟩
  have he := Real.exp_injective (show Real.exp (-(p.φ * w () 1 + p.φy * w () 0 + ε * ν0 +
    p.σ * w () 2)) = Real.exp (-(p.σ * w () 2) - w () 1) by linarith)
  linarith

/-- Woodford (2003), §5 and Ch. 4 (2.7) (**the Calvo equilibrium with a permanent interest-rate
disturbance `εν̄`**): `ŷ = Y_C(π)` and `(1 − φ_π)π − φ_yŷ = εν̄`. -/
theorem calvo_one_state (p : NonlinearRotemberg.Par) {c : NonlinearNKMarkov.Par} (hc : c.Std)
    (hβ : p.β = c.β) (hσ : p.σ = c.σ) (hω : p.ω = c.ω) (hθ : p.θ = c.θ) {ν0 ε : ℝ}
    {w : Unit → Fin 4 → ℝ}
    (h : NonlinearNKMarkov.IsMarkovEqm c (NonlinearNKMarkov.chainOp P1)
      (xiC (fun _ => ν0) (fun _ => 0)) ε w) :
    w () 0 = yC p c.α (w () 1) ∧ (1 - c.φ) * w () 1 - c.φy * w () 0 = ε * ν0 := by
  have hcomp : ∀ i, NonlinearNKMarkov.Qmap c (ε • xiC (fun _ => ν0) (fun _ => 0) (), w ()) i +
      NonlinearNKMarkov.Nmap c (ε • xiC (fun _ => ν0) (fun _ => 0) (), w ()) i = 0 := fun i => by
    have := congrFun (congrFun h ()) i
    simpa [NonlinearNKMarkov.Phi, NonlinearNKMarkov.Mv, NonlinearNKMarkov.chainOp, P1]
      using this
  have h0 := hcomp 0
  have h1 := hcomp 1
  have h2 := hcomp 2
  have h3 := hcomp 3
  simp only [NonlinearNKMarkov.Qmap, NonlinearNKMarkov.Nmap, xiC, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Pi.smul_apply, smul_eq_mul, mul_zero, add_zero,
    sub_zero, NonlinearNKMarkov.Par.c0] at h0 h1 h2 h3
  have hs : p.σ + p.ω ≠ 0 := by rw [hσ, hω]; linarith [hc.σ_pos, hc.ω_nonneg]
  have hab : 0 < 1 - c.α * p.β := by rw [hβ]; linarith [hc.ab_lt_one]
  have hθ1 : 1 < p.θ := by rw [hθ]; exact hc.one_lt_θ
  have hω0 : 0 ≤ p.ω := by rw [hω]; exact hc.ω_nonneg
  refine ⟨yC_of_eqs p (y := w () 0) (π := w () 1) (F := w () 2) (K := w () 3) hc.α_lt_one hθ1
    hs hω0 ?_ ?_ ?_ hab, ?_⟩
  · rw [hβ, hσ, hθ]; linarith
  · rw [hβ, hω, hθ]; linarith
  · rw [hθ, hω, mul_div_assoc] at *; linarith
  · have he := Real.exp_injective (show Real.exp (-(c.φ * w () 1 + c.φy * w () 0 + ε * ν0 +
      c.σ * w () 0)) = Real.exp (-(c.σ * w () 0) - w () 1) by linarith)
    linarith

/-! ## The difference of second-order output and of second-order welfare -/

/-- Woodford (2003), Ch. 3 fn. 44: the common first-order slope `Y′(0) = K/(σ+ω)` of the
steady-state output curves. -/
noncomputable def Y1 (p : NonlinearRotemberg.Par) : ℝ := KR p / (p.σ + p.ω)

/-- Woodford (2003), App. A.3: `Y_R″(0) = (3K − K² + σψ)/(σ+ω)`. -/
noncomputable def Y2R (p : NonlinearRotemberg.Par) : ℝ :=
  (3 * KR p - KR p ^ 2 + p.σ * p.ψ) / (p.σ + p.ω)

/-- Woodford (2003), App. A.3: `Y_C″(0)` (the second jet of `NonlinearRotembergTrendWelfare.J_yC`).
-/
noncomputable def Y2C (p : NonlinearRotemberg.Par) (α : ℝ) : ℝ :=
  ((1 + p.ω * p.θ) * (α * (p.θ - 1) / (1 - α) ^ 2) -
    (-(α * p.β * (p.θ - 1) ^ 2) / (1 - α * p.β) ^ 2) +
    (-(α * p.β * (p.θ * (1 + p.ω)) ^ 2) / (1 - α * p.β) ^ 2)) / (p.σ + p.ω)

/-- Woodford (2003), Prop. 4.3: `N₁ = 1 − φ_π − φ_yY′(0)`. -/
noncomputable def N1 (p : NonlinearRotemberg.Par) : ℝ := 1 - p.φ - p.φy * Y1 p

/-- Woodford (2003), Prop. 4.3: under the Taylor principle `N₁ < 0`. -/
theorem N1_neg {p : NonlinearRotemberg.Par} (hp : p.Std) : N1 p < 0 := by
  have hb := hp.basic
  have hk := hb.κ_pos
  have hs : 0 < p.σ + p.ω := by linarith [hb.σ_pos, hb.ω_nonneg]
  have hθm : 0 < p.θ * p.m := mul_pos (by linarith [hb.one_lt_θ]) hb.m_pos
  have hY : Y1 p = (1 - p.β) / p.κ := by
    unfold Y1 KR NonlinearRotemberg.Par.κ
    have := hb.ψ_pos.ne'
    field_simp
  have e : N1 p = -(p.κ * (p.φ - 1) + (1 - p.β) * p.φy) / p.κ := by
    unfold N1; rw [hY]; field_simp; ring
  rw [e]
  exact div_neg_of_neg_of_pos (by linarith [hp.taylor]) hk

set_option maxHeartbeats 1000000 in
-- assembling the two one-state computations
/-- Woodford (2003), Ch. 6, §2 and §4.1 and Ch. 4 (2.7) (**the exact second-order difference on
the one-state chain**): with a permanent interest-rate disturbance `εν̄` and the equivalence map,
the actual (locally unique) perturbation equilibria satisfy
`ŷ₂ᴿ − ŷ₂ᶜ = (1 − φ_π)ν̄²(Y_R″(0) − Y_C″(0))/N₁³`, and
`W_R(ε) − W_C(ε) = (ε²/2)(1 − m)Σβᵗ(ŷ₂ᴿ − ŷ₂ᶜ) + o(ε²)`. -/
theorem one_state_difference (p : NonlinearRotemberg.Par) (c : NonlinearNKMarkov.Par)
    (hp : p.Std) (hc : c.Std) (hβ : p.β = c.β) (hσ : p.σ = c.σ) (hω : p.ω = c.ω)
    (hθ : p.θ = c.θ) (hφ : p.φ = c.φ) (hφy : p.φy = c.φy)
    (hψ : p.ψ = p.θ * p.m * c.α * (1 + p.ω * p.θ) / ((1 - c.α) * (1 - c.α * p.β))) (ν0 : ℝ) :
    ∃ zR : ℝ → Unit → Fin 3 → ℝ, ∃ zC : ℝ → Unit → Fin 4 → ℝ,
      (∀ᶠ ε in 𝓝 0, NonlinearRotembergSmooth.PhiJ P1 (xiR (fun _ => ν0) (fun _ => 0))
        (NonlinearRotembergSmooth.vecOf p, ε) (zR ε) = 0) ∧
      (∀ᶠ ε in 𝓝 0, NonlinearNKMarkov.IsMarkovEqm c (NonlinearNKMarkov.chainOp P1)
        (xiC (fun _ => ν0) (fun _ => 0)) ε (zC ε)) ∧
      (∃ r > 0, ∀ᶠ ε in 𝓝 0, ∀ w : Unit → Fin 3 → ℝ, ‖w‖ < r →
        NonlinearRotembergSmooth.PhiJ P1 (xiR (fun _ => ν0) (fun _ => 0))
          (NonlinearRotembergSmooth.vecOf p, ε) w = 0 → w = zR ε) ∧
      (∃ r > 0, ∀ᶠ ε in 𝓝 0, ∀ w : Unit → Fin 4 → ℝ, ‖w‖ < r →
        NonlinearNKMarkov.IsMarkovEqm c (NonlinearNKMarkov.chainOp P1)
          (xiC (fun _ => ν0) (fun _ => 0)) ε w → w = zC ε) ∧
      d2 zR () 0 - d2 zC () 0 = (1 - p.φ) * ν0 ^ 2 * (Y2R p - Y2C p c.α) / N1 p ^ 3 ∧
      ∀ η > 0, ∀ᶠ ε in 𝓝 0, ∀ sp : ℕ → Unit,
        |WRp p.β p.σ p.ω p.m zR ε sp - WCp p.β p.σ p.ω p.m c.α p.θ zC ε sp -
          ε ^ 2 / 2 * ((1 - p.m) * ∑' t, p.β ^ t * (d2 zR (sp t) 0 - d2 zC (sp t) 0))| ≤
          η * ε ^ 2 := by
  obtain ⟨zR, zC, hRE, hCE, hR0, hC0, hRC, hCC, hres, hCpi, h1, hRU, hCU⟩ :=
    models_families p c hp hc hβ hσ hω hθ hφ hφy hψ P1_stochastic (fun _ => ν0) (fun _ => 0)
  have hb := hp.basic
  have hα0 := hc.α_pos
  have hα1 := hc.α_lt_one
  refine ⟨zR, zC, hRE, hCE, hRU, hCU, ?_, fun η hη => welfare_difference (σ := p.σ) hb.β_pos
    hb.β_lt_one hb.ω_nonneg hα0.le hα1 hb.one_lt_θ hψ hR0 hRC hres hC0 hCC hCpi
    (fun s => (h1 s).1) (fun s => (h1 s).2) hη⟩
  have hN1 := (N1_neg hp).ne
  -- Rotemberg
  have hyR : ∀ᶠ ε in 𝓝 0, zR ε () 0 = ssY p (zR ε () 1) :=
    hRE.mono fun ε hε => (rot_one_state hb hε).1
  have hNR : ∀ᶠ ε in 𝓝 0, (1 - p.φ) * zR ε () 1 - p.φy * zR ε () 0 = ε * ν0 :=
    hRE.mono fun ε hε => (rot_one_state hb hε).2
  have hR := one_state_jets (J_YR hb) (J_comp hRC () 0) (J_comp hRC () 1) (by simp [hR0]) hyR hNR
    hN1
  -- Calvo
  have hyC : ∀ᶠ ε in 𝓝 0, zC ε () 0 = yC p c.α (zC ε () 1) :=
    hCE.mono fun ε hε => (calvo_one_state p hc hβ hσ hω hθ hε).1
  have hNC : ∀ᶠ ε in 𝓝 0, (1 - p.φ) * zC ε () 1 - p.φy * zC ε () 0 = ε * ν0 :=
    hCE.mono fun ε hε => by rw [hφ, hφy]; exact (calvo_one_state p hc hβ hσ hω hθ hε).2
  have hJC := J_yC hb hα0 hα1
  -- the first-order slopes agree under the map
  have hθ0 : p.θ ≠ 0 := by linarith [hb.one_lt_θ]
  have hm0 : p.m ≠ 0 := hb.m_pos.ne'
  have h1α : 1 - c.α ≠ 0 := by linarith
  have hab : 1 - c.α * p.β ≠ 0 := by nlinarith [hb.β_lt_one, hb.β_pos]
  have hs : p.σ + p.ω ≠ 0 := by linarith [hb.σ_pos, hb.ω_nonneg]
  have hY1 : ((1 + p.ω * p.θ) * (c.α / (1 - c.α)) - (-(c.α * p.β * (p.θ - 1)) / (1 - c.α * p.β)) +
      (-(c.α * p.β * (p.θ * (1 + p.ω))) / (1 - c.α * p.β))) / (p.σ + p.ω) = Y1 p := by
    unfold Y1 KR; rw [hψ]; field_simp; ring
  rw [hY1] at hJC
  have hC := one_state_jets hJC (J_comp hCC () 0) (J_comp hCC () 1) (by simp [hC0]) hyC hNC
    (by unfold N1 at hN1; exact hN1)
  rw [hR.2, hC.2]
  unfold N1 Y1 Y2R Y2C
  ring

/-- Woodford (2003), Ch. 6, §2 and §4.1 (**the second-order welfare of Rotemberg and Calvo is NOT
the same in general**): at `β = α = 1/2`, `σ = 1`, `ω = 0`, `θ = 2`, `m = 1/2`, `φ_π = 3/2`,
`φ_y = 0` (Taylor principle), `ψ = 4/3` (the equivalence map) and a permanent interest-rate
disturbance `εν̄` with `ν̄ = 1`, the actual perturbation equilibria have
`W_R(ε) − W_C(ε) = (40/9)ε² + o(ε²)`: the second-order welfare coefficient differs by
`(1 − m)Σβᵗ(ŷ₂ᴿ − ŷ₂ᶜ) = 80/9 ≠ 0`. -/
theorem welfare_differs :
    ∃ zR : ℝ → Unit → Fin 3 → ℝ, ∃ zC : ℝ → Unit → Fin 4 → ℝ,
      (∀ᶠ ε in 𝓝 0, NonlinearRotembergSmooth.PhiJ P1 (xiR (fun _ => 1) (fun _ => 0))
        (NonlinearRotembergSmooth.vecOf ⟨1 / 2, 1, 0, 2, 4 / 3, 1 / 2, 3 / 2, 0⟩, ε) (zR ε) = 0) ∧
      (∀ᶠ ε in 𝓝 0, NonlinearNKMarkov.IsMarkovEqm ⟨1 / 2, 1 / 2, 2, 0, 1, 3 / 2, 0⟩
        (NonlinearNKMarkov.chainOp P1) (xiC (fun _ => 1) (fun _ => 0)) ε (zC ε)) ∧
      (∃ r > 0, ∀ᶠ ε in 𝓝 0, ∀ w : Unit → Fin 3 → ℝ, ‖w‖ < r →
        NonlinearRotembergSmooth.PhiJ P1 (xiR (fun _ => 1) (fun _ => 0))
          (NonlinearRotembergSmooth.vecOf ⟨1 / 2, 1, 0, 2, 4 / 3, 1 / 2, 3 / 2, 0⟩, ε) w = 0 →
            w = zR ε) ∧
      (∃ r > 0, ∀ᶠ ε in 𝓝 0, ∀ w : Unit → Fin 4 → ℝ, ‖w‖ < r →
        NonlinearNKMarkov.IsMarkovEqm ⟨1 / 2, 1 / 2, 2, 0, 1, 3 / 2, 0⟩
          (NonlinearNKMarkov.chainOp P1) (xiC (fun _ => 1) (fun _ => 0)) ε w → w = zC ε) ∧
      ∀ η > 0, ∀ᶠ ε in 𝓝 0, ∀ sp : ℕ → Unit,
        |WRp (1 / 2) 1 0 (1 / 2) zR ε sp - WCp (1 / 2) 1 0 (1 / 2) (1 / 2) 2 zC ε sp -
          40 / 9 * ε ^ 2| ≤ η * ε ^ 2 := by
  set p : NonlinearRotemberg.Par := ⟨1 / 2, 1, 0, 2, 4 / 3, 1 / 2, 3 / 2, 0⟩ with hpd
  set c : NonlinearNKMarkov.Par := ⟨1 / 2, 1 / 2, 2, 0, 1, 3 / 2, 0⟩ with hcd
  have hp : p.Std := ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num⟩,
    by simp only [hpd, NonlinearRotemberg.Par.κ]; norm_num⟩
  have hc : c.Std := ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num,
    by simp only [hcd, NonlinearNKMarkov.Par.κ, Moments.calvoKappa]; norm_num⟩
  obtain ⟨zR, zC, hRE, hCE, hRU, hCU, hd, hW⟩ := one_state_difference p c hp hc rfl rfl rfl rfl
    rfl rfl (by simp only [hpd, hcd]; norm_num) 1
  refine ⟨zR, zC, hRE, hCE, hRU, hCU, fun η hη => ?_⟩
  have hval : d2 zR () 0 - d2 zC () 0 = 80 / 9 := by
    rw [hd]
    simp only [hpd, hcd, N1, Y1, Y2R, Y2C, KR]
    norm_num
  filter_upwards [hW η hη] with ε hε sp
  have := hε sp
  have hsum : ∑' t, (1 / 2 : ℝ) ^ t * (d2 zR (sp t) 0 - d2 zC (sp t) 0) = 160 / 9 := by
    have e : ∀ t, d2 zR (sp t) 0 - d2 zC (sp t) 0 = 80 / 9 := fun t => by
      rw [show sp t = () from rfl]; exact hval
    simp only [e]
    rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  simp only [hpd] at this
  rw [hsum] at this
  convert this using 2
  ring

end Woodford.StabilizationWelfare.NonlinearRotembergStochExample
