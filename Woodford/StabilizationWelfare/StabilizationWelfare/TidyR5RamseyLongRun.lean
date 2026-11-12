/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearNKMarkovRamseyLin

/-!
# Optimal long-run inflation is zero for every distortion `Φ`

Woodford (2003), *Interest and Prices*, Chapter 6, §3.2, p. 415 ("the optimal commitment
involves a long-run inflation rate of zero, even when the natural rate of output is inefficiently
low") and §5, pp. 455–463 (Benigno–Woodford: the exact Calvo model with a distortion `Φ` of any
size); Chapter 7, §1 (the timeless perspective).

`NonlinearNKMarkovRamsey.ramsey_steadyState` shows that the zero-inflation point solves the exact
Ramsey conditions for every `Φ`. Here the converse is proved: a steady state of the exact
first-order conditions of the Ramsey problem (constant variables and multipliers) MUST have zero
inflation, for every distortion with `(1 − Φ)(1 − σ) ≠ 1 + ω` — in particular for every
`0 ≤ Φ < 1` (`σ > 0`, `ω ≥ 0`) — and the exceptional value is a genuine exception.

## Main results

* `ss_eqs`: the nine steady-state equations in explicit form.
* **`ramsey_ss_pi_zero`**: if `A_u ≠ 0` and `(1 − Φ)(1 − σ) ≠ 1 + ω`, every steady state of the
  exact Ramsey conditions has `π = 0`. The proof: off zero inflation the inflation condition
  forces the price-index multiplier combination `W = −(1 − α)Qλ₄`, and then the output condition
  reduces to `A_u(1 + ω − (1 − σ)(1 − Φ))e^{(1−σ)ŷ} = 0`.
* **`ramsey_ss_iff`**: the steady states with inflation `π̄` exist iff `π̄ = 0`.
* **`ramsey_longrun_zero`**: every deterministic path of the exact Ramsey conditions (date-0 or
  timeless, any initial condition, disturbances dying out) that converges has long-run inflation
  zero: the long-run inflation rate of the optimal commitment is zero for every `0 ≤ Φ < 1`.
* **`ramsey_ss_continuum`** (the exception is genuine): if `(1 − Φ)(1 − σ) = 1 + ω` then for
  every `π ≤ 0` there is a steady state with inflation `π`.
-/

namespace Woodford.StabilizationWelfare.TidyR5RamseyLongRun

open Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovRamsey NonlinearNKMarkovRamseyLin

/-- Woodford (2003), §5 (**the steady-state equations**): the nine exact Ramsey conditions at a
constant point `w` (lag = current = lead) without disturbances. -/
theorem ss_eqs (p : Par) (R : RPar) (w : Fin 9 → ℝ) (h : ramseyQ p R 0 w w + ramseyN p w = 0) :
    R.Au * Real.exp ((1 - p.σ) * w 0) - (1 - R.Φ) * R.Au * w 4 * Real.exp ((1 + p.ω) * w 0) -
        w 5 * (1 - p.α * p.β) * (1 - p.σ) * Real.exp ((1 - p.σ) * w 0) -
        w 6 * (1 - p.α * p.β) * (1 + p.ω) * Real.exp ((1 + p.ω) * w 0) = 0 ∧
    -(p.α * (p.θ - 1) * w 5 * Real.exp ((p.θ - 1) * w 1 + w 2)) -
        p.α * aE p * w 6 * Real.exp (aE p * w 1 + w 3) +
        p.α * (p.θ - 1) * w 7 * Real.exp ((p.θ - 1) * w 1) -
        p.α * aE p * w 8 * w 4 * Real.exp (aE p * w 1) = 0 ∧
    w 5 * Real.exp (w 2) - p.α * w 5 * Real.exp ((p.θ - 1) * w 1 + w 2) +
        (1 - p.α) * ((p.θ - 1) / p.c0) * w 7 * Real.exp (-((p.θ - 1) * ((w 3 - w 2) / p.c0))) -
        (1 - p.α) * (aE p / p.c0) * w 8 * Real.exp (-(aE p * ((w 3 - w 2) / p.c0))) = 0 ∧
    w 6 * Real.exp (w 3) - p.α * w 6 * Real.exp (aE p * w 1 + w 3) -
        (1 - p.α) * ((p.θ - 1) / p.c0) * w 7 * Real.exp (-((p.θ - 1) * ((w 3 - w 2) / p.c0))) +
        (1 - p.α) * (aE p / p.c0) * w 8 * Real.exp (-(aE p * ((w 3 - w 2) / p.c0))) = 0 ∧
    -((1 - R.Φ) * R.Au * Real.exp ((1 + p.ω) * w 0) / (1 + p.ω)) + w 8 +
        -(p.β * p.α * w 8 * Real.exp (aE p * w 1)) = 0 ∧
    Real.exp (w 2) - (1 - p.α * p.β) * Real.exp ((1 - p.σ) * w 0) +
        -(p.α * p.β * Real.exp ((p.θ - 1) * w 1 + w 2)) = 0 ∧
    Real.exp (w 3) - (1 - p.α * p.β) * Real.exp ((1 + p.ω) * w 0) +
        -(p.α * p.β * Real.exp (aE p * w 1 + w 3)) = 0 ∧
    p.α * (Real.exp ((p.θ - 1) * w 1) - 1) +
        (1 - p.α) * (Real.exp (-((p.θ - 1) * ((w 3 - w 2) / p.c0))) - 1) = 0 ∧
    w 4 - p.α * w 4 * Real.exp (aE p * w 1) -
        (1 - p.α) * Real.exp (-(aE p * ((w 3 - w 2) / p.c0))) = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  have h6 := congrFun h 6
  have h7 := congrFun h 7
  have h8 := congrFun h 8
  simp only [ramseyQ, Fin.isValue, Pi.zero_apply, mul_zero, add_zero, sub_zero, ramseyN,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- Woodford (2003), §5: `a − b = 1 + ωθ` for `a = θ(1+ω)`, `b = θ − 1`. -/
theorem aE_sub (p : Par) : aE p - (p.θ - 1) = p.c0 := by unfold aE Par.c0; ring

/-- **Woodford (2003), p. 415 and §5 (Benigno–Woodford): every steady state of the exact Ramsey
conditions has ZERO inflation**, for every distortion `Φ` with `(1 − Φ)(1 − σ) ≠ 1 + ω` (which
holds for all `0 ≤ Φ < 1`, see `ss_condition_of_mem`), given `A_u ≠ 0`. -/
theorem ramsey_ss_pi_zero {p : Par} (R : RPar) (hp : p.Std) (hAu : R.Au ≠ 0)
    (hΦ : (1 - R.Φ) * (1 - p.σ) ≠ 1 + p.ω) {w : Fin 9 → ℝ}
    (h : ramseyQ p R 0 w w + ramseyN p w = 0) : w 1 = 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := ss_eqs p R w h
  by_contra hπ
  have hα0 := hp.α_pos
  have hα1 := hp.α_lt_one
  have hc0 := hp.c0_pos
  have hω : 0 < 1 + p.ω := by linarith [hp.ω_nonneg]
  have hb : 0 < p.θ - 1 := by linarith [hp.one_lt_θ]
  have ha : 0 < aE p := by unfold aE; nlinarith [hp.one_lt_θ, hp.ω_nonneg]
  set b := p.θ - 1 with hbdef
  set a := aE p with hadef
  set c0 := p.c0 with hc0def
  set x := (w 3 - w 2) / c0 with hx
  set B := Real.exp (b * w 1) with hB
  set A := Real.exp (a * w 1) with hA
  set EF := Real.exp (w 2) with hEF
  set EK := Real.exp (w 3) with hEK
  set P := Real.exp (-(b * x)) with hP
  set Q := Real.exp (-(a * x)) with hQ
  set U := Real.exp ((1 - p.σ) * w 0) with hU
  set V := Real.exp ((1 + p.ω) * w 0) with hV
  have eB : Real.exp (b * w 1 + w 2) = B * EF := Real.exp_add _ _
  have eA : Real.exp (a * w 1 + w 3) = A * EK := Real.exp_add _ _
  rw [eB, eA] at h1
  rw [eB] at h2 h5
  rw [eA] at h3 h6
  have hQK : Q * EK = P * EF := by
    rw [hQ, hEK, hP, hEF, ← Real.exp_add, ← Real.exp_add]
    congr 1
    have hab : a - b = c0 := aE_sub p
    have hcx : c0 * x = w 3 - w 2 := by rw [hx]; field_simp
    linear_combination -hcx - x * hab
  have hPpos : 0 < P := Real.exp_pos _
  have hQpos : 0 < Q := Real.exp_pos _
  have hUpos : 0 < U := Real.exp_pos _
  have hVpos : 0 < V := Real.exp_pos _
  have hEFpos : 0 < EF := Real.exp_pos _
  have hEKpos : 0 < EK := Real.exp_pos _
  -- the price index and the dispersion law
  have e1 : (1 - p.α) * P = 1 - p.α * B := by linarith
  have e8 : w 4 * (1 - p.α * A) = (1 - p.α) * Q := by linarith
  have h1B : 1 - p.α * B ≠ 0 := by
    rw [← e1]; exact (mul_pos (by linarith) hPpos).ne'
  have h1A : 1 - p.α * A ≠ 0 := by
    intro h0'
    rw [h0', mul_zero] at e8
    exact (mul_pos (by linarith) hQpos).ne' e8.symm
  have h1bA : 1 - p.α * p.β * A ≠ 0 := by
    intro h0'
    have : EK * (1 - p.α * p.β * A) = (1 - p.α * p.β) * V := by linarith
    rw [h0', mul_zero] at this
    exact (mul_pos (by linarith [hp.ab_lt_one]) hVpos).ne' this.symm
  -- `A ≠ B` off zero inflation
  have hAB : A ≠ B := by
    intro hAB'
    have := Real.exp_injective hAB'
    have hab := aE_sub p
    apply hπ
    have h' : (a - b) * w 1 = 0 := by linarith
    rw [hadef, hbdef, hab] at h'
    exact (mul_eq_zero.mp h').resolve_left hc0.ne'
  -- the combination `W`
  set W := (1 - p.α) / c0 * (b * w 7 * P - a * w 8 * Q) with hW
  have e2 : w 5 * EF * (1 - p.α * B) + W = 0 := by rw [hW]; linear_combination h2
  have e3 : w 6 * EK * (1 - p.α * A) - W = 0 := by rw [hW]; linear_combination h3
  have hWdef : (1 - p.α) * b * w 7 * P = c0 * W + (1 - p.α) * a * w 8 * Q := by
    rw [hW]; field_simp; ring
  have hc0a : a - b = c0 := aE_sub p
  -- the inflation condition forces `W = −(1 − α)λ₄Q`
  have hT' : p.α * (a * (B - A) * (W + (1 - p.α) * w 8 * Q)) = 0 := by
    linear_combination (1 - p.α * B) * (1 - p.α * A) * h1 +
      p.α * W * B * (1 - p.α * A) * hc0a - p.α * B * (1 - p.α * A) * hWdef +
      p.α * b * B * (1 - p.α * A) * e2 + p.α * a * A * (1 - p.α * B) * e3 +
      p.α * b * w 7 * B * (1 - p.α * A) * e1 + p.α * a * w 8 * A * (1 - p.α * B) * e8
  have hT : a * (B - A) * (W + (1 - p.α) * w 8 * Q) = 0 :=
    (mul_eq_zero.mp hT').resolve_left hα0.ne'
  have hWv : W = -((1 - p.α) * w 8 * Q) := by
    have h' := (mul_eq_zero.mp hT).resolve_left
      (mul_ne_zero ha.ne' (sub_ne_zero.mpr (Ne.symm hAB)))
    linarith
  -- the output condition
  have h4' : (1 + p.ω) * (1 - p.α * p.β * A) * w 8 = (1 - R.Φ) * R.Au * V := by
    field_simp at h4; linear_combination h4
  have h5' : (1 - p.α * p.β) * U = EF * (1 - p.α * p.β * B) := by linarith
  have h6' : (1 - p.α * p.β) * V = EK * (1 - p.α * p.β * A) := by linarith
  have h0A : R.Au * U - (1 - R.Φ) * R.Au * w 4 * V - (1 - p.σ) * (1 - p.α * p.β * B) *
      (w 5 * EF) - (1 + p.ω) * (1 - p.α * p.β * A) * (w 6 * EK) = 0 := by
    linear_combination h0 + (1 - p.σ) * w 5 * h5' + (1 + p.ω) * w 6 * h6'
  have hBB : (1 - p.α * B) * (1 - p.α * A) * R.Au * U -
      (1 - R.Φ) * R.Au * V * (1 - p.α * B) * (1 - p.α) * Q +
      (1 - p.σ) * (1 - p.α * p.β * B) * (1 - p.α * A) * W -
      (1 + p.ω) * (1 - p.α * p.β * A) * (1 - p.α * B) * W = 0 := by
    linear_combination (1 - p.α * B) * (1 - p.α * A) * h0A +
      (1 - R.Φ) * R.Au * V * (1 - p.α * B) * e8 +
      (1 - p.σ) * (1 - p.α * p.β * B) * (1 - p.α * A) * e2 +
      (1 + p.ω) * (1 - p.α * p.β * A) * (1 - p.α * B) * e3
  rw [hWv] at hBB
  have hCC : (1 - p.α * A) * ((1 - p.α * B) * R.Au * U -
      (1 - p.σ) * (1 - p.α * p.β * B) * (1 - p.α) * Q * w 8) = 0 := by
    linear_combination hBB - (1 - p.α * B) * (1 - p.α) * Q * h4'
  have hC : (1 - p.α * B) * R.Au * U - (1 - p.σ) * (1 - p.α * p.β * B) * (1 - p.α) * Q * w 8 =
      0 := (mul_eq_zero.mp hCC).resolve_left h1A
  have hkey : (1 - p.α * p.β * A) * (1 - p.α * B) * (1 - p.α * p.β) * R.Au * U *
      ((1 + p.ω) - (1 - p.σ) * (1 - R.Φ)) = 0 := by
    linear_combination (1 + p.ω) * (1 - p.α * p.β * A) * (1 - p.α * p.β) * hC +
      (1 - p.σ) * (1 - p.α * p.β * B) * (1 - p.α) * Q * (1 - p.α * p.β) * h4' +
      (1 - p.σ) * (1 - p.α * p.β * B) * (1 - p.α) * (1 - R.Φ) * R.Au * Q * h6' +
      (1 - p.σ) * (1 - p.α * p.β * B) * (1 - p.α) * (1 - R.Φ) * R.Au *
        (1 - p.α * p.β * A) * hQK +
      (1 - p.σ) * (1 - p.α * p.β * B) * (1 - R.Φ) * R.Au * (1 - p.α * p.β * A) * EF * e1 -
      (1 - p.σ) * (1 - R.Φ) * R.Au * (1 - p.α * p.β * A) * (1 - p.α * B) * h5'
  have hne : (1 - p.α * p.β * A) * (1 - p.α * B) * (1 - p.α * p.β) * R.Au * U *
      ((1 + p.ω) - (1 - p.σ) * (1 - R.Φ)) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h1bA h1B) ?_) hAu)
      hUpos.ne') ?_
    · linarith [hp.ab_lt_one]
    · intro h'
      apply hΦ
      linarith
  exact hne hkey

/-- Woodford (2003), §5 (**the condition holds for every admissible distortion**): for
`0 ≤ Φ ≤ 1`, `σ > 0` and `ω ≥ 0`, `(1 − Φ)(1 − σ) < 1 + ω`. -/
theorem ss_condition_of_mem {p : Par} (R : RPar) (hp : p.Std) (hΦ0 : 0 ≤ R.Φ) (hΦ1 : R.Φ ≤ 1) :
    (1 - R.Φ) * (1 - p.σ) ≠ 1 + p.ω := by
  have hσ := hp.σ_pos
  have hω := hp.ω_nonneg
  intro h
  rcases le_or_gt 0 (1 - p.σ) with h1 | h1
  · have : (1 - R.Φ) * (1 - p.σ) ≤ 1 - p.σ := by nlinarith
    linarith
  · have : (1 - R.Φ) * (1 - p.σ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) h1.le
    linarith

/-- Woodford (2003), §5 (**the converse of `ss_eqs`**): the nine explicit equations imply that
`w` is a steady state of the exact Ramsey conditions. -/
theorem ss_of_eqs (p : Par) (R : RPar) (w : Fin 9 → ℝ)
    (h0 : R.Au * Real.exp ((1 - p.σ) * w 0) - (1 - R.Φ) * R.Au * w 4 * Real.exp ((1 + p.ω) * w 0) -
        w 5 * (1 - p.α * p.β) * (1 - p.σ) * Real.exp ((1 - p.σ) * w 0) -
        w 6 * (1 - p.α * p.β) * (1 + p.ω) * Real.exp ((1 + p.ω) * w 0) = 0)
    (h1 : -(p.α * (p.θ - 1) * w 5 * Real.exp ((p.θ - 1) * w 1 + w 2)) -
        p.α * aE p * w 6 * Real.exp (aE p * w 1 + w 3) +
        p.α * (p.θ - 1) * w 7 * Real.exp ((p.θ - 1) * w 1) -
        p.α * aE p * w 8 * w 4 * Real.exp (aE p * w 1) = 0)
    (h2 : w 5 * Real.exp (w 2) - p.α * w 5 * Real.exp ((p.θ - 1) * w 1 + w 2) +
        (1 - p.α) * ((p.θ - 1) / p.c0) * w 7 * Real.exp (-((p.θ - 1) * ((w 3 - w 2) / p.c0))) -
        (1 - p.α) * (aE p / p.c0) * w 8 * Real.exp (-(aE p * ((w 3 - w 2) / p.c0))) = 0)
    (h3 : w 6 * Real.exp (w 3) - p.α * w 6 * Real.exp (aE p * w 1 + w 3) -
        (1 - p.α) * ((p.θ - 1) / p.c0) * w 7 * Real.exp (-((p.θ - 1) * ((w 3 - w 2) / p.c0))) +
        (1 - p.α) * (aE p / p.c0) * w 8 * Real.exp (-(aE p * ((w 3 - w 2) / p.c0))) = 0)
    (h4 : -((1 - R.Φ) * R.Au * Real.exp ((1 + p.ω) * w 0) / (1 + p.ω)) + w 8 +
        -(p.β * p.α * w 8 * Real.exp (aE p * w 1)) = 0)
    (h5 : Real.exp (w 2) - (1 - p.α * p.β) * Real.exp ((1 - p.σ) * w 0) +
        -(p.α * p.β * Real.exp ((p.θ - 1) * w 1 + w 2)) = 0)
    (h6 : Real.exp (w 3) - (1 - p.α * p.β) * Real.exp ((1 + p.ω) * w 0) +
        -(p.α * p.β * Real.exp (aE p * w 1 + w 3)) = 0)
    (h7 : p.α * (Real.exp ((p.θ - 1) * w 1) - 1) +
        (1 - p.α) * (Real.exp (-((p.θ - 1) * ((w 3 - w 2) / p.c0))) - 1) = 0)
    (h8 : w 4 - p.α * w 4 * Real.exp (aE p * w 1) -
        (1 - p.α) * Real.exp (-(aE p * ((w 3 - w 2) / p.c0))) = 0) :
    ramseyQ p R 0 w w + ramseyN p w = 0 := by
  funext i
  fin_cases i <;>
    simp only [ramseyQ, Fin.isValue, Pi.zero_apply, mul_zero, add_zero, sub_zero, ramseyN,
      Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk]
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8

/-- **Woodford (2003), p. 415 and §5 (the long-run (timeless) Ramsey inflation rate is zero for
every distortion).** If `A_u ≠ 0` and `(1 − Φ)(1 − σ) ≠ 1 + ω` (e.g. any `0 ≤ Φ ≤ 1`), a steady
state of the exact Ramsey conditions with inflation `π̄` exists if and only if `π̄ = 0`. -/
theorem ramsey_ss_iff {p : Par} (R : RPar) (hp : p.Std) (hAu : R.Au ≠ 0)
    (hΦ : (1 - R.Φ) * (1 - p.σ) ≠ 1 + p.ω) (πbar : ℝ) :
    (∃ w : Fin 9 → ℝ, ramseyQ p R 0 w w + ramseyN p w = 0 ∧ w 1 = πbar) ↔ πbar = 0 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ramsey_ss_pi_zero R hp hAu hΦ hw
  · rintro rfl
    exact ⟨ramseySS p R, ramsey_steadyState p R hp, by simp [ramseySS]⟩

/-- **Woodford (2003), p. 415 and Ch. 7 (the long-run inflation of every Ramsey plan is zero, for
every `0 ≤ Φ ≤ 1`).** Let `w_{t}` be a deterministic path of the exact Ramsey conditions from date
`1` on (`Q(e_{t+1}, w_t, w_{t+1}) + N(w_{t+2}) = 0`; the date-0 condition, where the date-0 and
the timeless problems differ, is not used), with disturbances `e_t → 0`. If `w_{t}` converges, then
its inflation converges to zero. -/
theorem ramsey_longrun_zero {p : Par} (R : RPar) (hp : p.Std) (hAu : R.Au ≠ 0)
    (hΦ : (1 - R.Φ) * (1 - p.σ) ≠ 1 + p.ω) {w : ℕ → Fin 9 → ℝ} {e : ℕ → Fin 5 → ℝ}
    (heq : ∀ t, ramseyQ p R (e (t + 1)) (w t) (w (t + 1)) + ramseyN p (w (t + 2)) = 0)
    {wbar : Fin 9 → ℝ} (hw : Tendsto w atTop (𝓝 wbar)) (he : Tendsto e atTop (𝓝 0)) :
    wbar 1 = 0 ∧ Tendsto (fun t => w t 1) atTop (𝓝 0) := by
  have hQ : Continuous (Qd p R) := (contDiff_Qd (n := 0) p R).continuous
  have hN : Continuous (Nd p R) := (contDiff_Nd (n := 0) p R).continuous
  set ss := ramseySS p R
  have hw1 := hw.comp (tendsto_add_atTop_nat 1)
  have hw2 := hw.comp (tendsto_add_atTop_nat 2)
  have he1 := he.comp (tendsto_add_atTop_nat 1)
  have hlim : Tendsto (fun t => Qd p R (e (t + 1), w t - ss, w (t + 1) - ss) +
      Nd p R (w (t + 2) - ss)) atTop (𝓝 (Qd p R (0, wbar - ss, wbar - ss) + Nd p R (wbar - ss))) :=
    ((hQ.tendsto _).comp (he1.prodMk_nhds ((hw.sub_const ss).prodMk_nhds
      (hw1.sub_const ss)))).add ((hN.tendsto _).comp (hw2.sub_const ss))
  have hz : (fun t => Qd p R (e (t + 1), w t - ss, w (t + 1) - ss) + Nd p R (w (t + 2) - ss)) =
      fun _ => 0 := by
    funext t
    simpa [Qd, Nd, ss] using heq t
  rw [hz] at hlim
  have hss : ramseyQ p R 0 wbar wbar + ramseyN p wbar = 0 := by
    have h' := tendsto_nhds_unique hlim tendsto_const_nhds
    simpa [Qd, Nd, ss] using h'
  have h1 := ramsey_ss_pi_zero R hp hAu hΦ hss
  refine ⟨h1, ?_⟩
  have := (continuous_apply 1).continuousAt.tendsto.comp hw
  rwa [h1] at this

/-- Woodford (2003), §5: `ss_of_eqs` for the vector `![ŷ, π, F̂, K̂, Δ, λ₁, λ₂, λ₃, λ₄]`. -/
theorem ss_of_vals (p : Par) (R : RPar) (y π F K D l1 l2 l3 l4 : ℝ)
    (h0 : R.Au * Real.exp ((1 - p.σ) * y) - (1 - R.Φ) * R.Au * D * Real.exp ((1 + p.ω) * y) -
        l1 * (1 - p.α * p.β) * (1 - p.σ) * Real.exp ((1 - p.σ) * y) -
        l2 * (1 - p.α * p.β) * (1 + p.ω) * Real.exp ((1 + p.ω) * y) = 0)
    (h1 : -(p.α * (p.θ - 1) * l1 * Real.exp ((p.θ - 1) * π + F)) -
        p.α * aE p * l2 * Real.exp (aE p * π + K) +
        p.α * (p.θ - 1) * l3 * Real.exp ((p.θ - 1) * π) -
        p.α * aE p * l4 * D * Real.exp (aE p * π) = 0)
    (h2 : l1 * Real.exp F - p.α * l1 * Real.exp ((p.θ - 1) * π + F) +
        (1 - p.α) * ((p.θ - 1) / p.c0) * l3 * Real.exp (-((p.θ - 1) * ((K - F) / p.c0))) -
        (1 - p.α) * (aE p / p.c0) * l4 * Real.exp (-(aE p * ((K - F) / p.c0))) = 0)
    (h3 : l2 * Real.exp K - p.α * l2 * Real.exp (aE p * π + K) -
        (1 - p.α) * ((p.θ - 1) / p.c0) * l3 * Real.exp (-((p.θ - 1) * ((K - F) / p.c0))) +
        (1 - p.α) * (aE p / p.c0) * l4 * Real.exp (-(aE p * ((K - F) / p.c0))) = 0)
    (h4 : -((1 - R.Φ) * R.Au * Real.exp ((1 + p.ω) * y) / (1 + p.ω)) + l4 +
        -(p.β * p.α * l4 * Real.exp (aE p * π)) = 0)
    (h5 : Real.exp F - (1 - p.α * p.β) * Real.exp ((1 - p.σ) * y) +
        -(p.α * p.β * Real.exp ((p.θ - 1) * π + F)) = 0)
    (h6 : Real.exp K - (1 - p.α * p.β) * Real.exp ((1 + p.ω) * y) +
        -(p.α * p.β * Real.exp (aE p * π + K)) = 0)
    (h7 : p.α * (Real.exp ((p.θ - 1) * π) - 1) +
        (1 - p.α) * (Real.exp (-((p.θ - 1) * ((K - F) / p.c0))) - 1) = 0)
    (h8 : D - p.α * D * Real.exp (aE p * π) -
        (1 - p.α) * Real.exp (-(aE p * ((K - F) / p.c0))) = 0) :
    ramseyQ p R 0 ![y, π, F, K, D, l1, l2, l3, l4] ![y, π, F, K, D, l1, l2, l3, l4] +
      ramseyN p ![y, π, F, K, D, l1, l2, l3, l4] = 0 :=
  ss_of_eqs p R _ h0 h1 h2 h3 h4 h5 h6 h7 h8

/-- **Woodford (2003), §5 (the exceptional distortion is a genuine exception).** If
`(1 − Φ)(1 − σ) = 1 + ω` (possible only outside `0 ≤ Φ ≤ 1`), then EVERY inflation rate `π ≤ 0`
is the inflation rate of a steady state of the exact Ramsey conditions: the long-run inflation
rate is not pinned down. -/
theorem ramsey_ss_continuum {p : Par} (R : RPar) (hp : p.Std)
    (hΦ : (1 - R.Φ) * (1 - p.σ) = 1 + p.ω) {π : ℝ} (hπ : π ≤ 0) :
    ∃ w : Fin 9 → ℝ, ramseyQ p R 0 w w + ramseyN p w = 0 ∧ w 1 = π := by
  have hα0 := hp.α_pos
  have hα1 := hp.α_lt_one
  have h1α : (1 : ℝ) - p.α ≠ 0 := by linarith
  have hβ0 := hp.β_pos
  have hc0 := hp.c0_pos
  have hω : 0 < 1 + p.ω := by linarith [hp.ω_nonneg]
  have hσω : 0 < p.σ + p.ω := by linarith [hp.ω_nonneg, hp.σ_pos]
  have hb : 0 < p.θ - 1 := by linarith [hp.one_lt_θ]
  have ha : 0 < aE p := by unfold aE; nlinarith [hp.one_lt_θ, hp.ω_nonneg]
  have hab0 : 0 < 1 - p.α * p.β := by linarith [hp.ab_lt_one]
  have hc0a := aE_sub p
  have hc0inv : p.c0 * p.c0⁻¹ = 1 := mul_inv_cancel₀ hc0.ne'
  obtain ⟨B, hB⟩ : ∃ B, Real.exp ((p.θ - 1) * π) = B := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, Real.exp (aE p * π) = A := ⟨_, rfl⟩
  have hB1 : B ≤ 1 := hB ▸ Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hb.le hπ)
  have hA1 : A ≤ 1 := hA ▸ Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ha.le hπ)
  have hBp : 0 < B := hB ▸ Real.exp_pos _
  have hAp : 0 < A := hA ▸ Real.exp_pos _
  have hαB : 0 < 1 - p.α * B := by nlinarith
  have hαA : 0 < 1 - p.α * A := by nlinarith
  have hαβB : 0 < 1 - p.α * p.β * B := by nlinarith [mul_pos hα0 hβ0, hp.ab_lt_one]
  have hαβA : 0 < 1 - p.α * p.β * A := by nlinarith [mul_pos hα0 hβ0, hp.ab_lt_one]
  obtain ⟨P, hP⟩ : ∃ P, (1 - p.α * B) / (1 - p.α) = P := ⟨_, rfl⟩
  have hPp : 0 < P := hP ▸ div_pos hαB (by linarith)
  obtain ⟨x, hx⟩ : ∃ x, -Real.log P / (p.θ - 1) = x := ⟨_, rfl⟩
  have hxP : Real.exp (-((p.θ - 1) * x)) = P := by
    rw [← hx, show -((p.θ - 1) * (-Real.log P / (p.θ - 1))) = Real.log P by field_simp,
      Real.exp_log hPp]
  obtain ⟨Q, hQ⟩ : ∃ Q, Real.exp (-(aE p * x)) = Q := ⟨_, rfl⟩
  have hQp : 0 < Q := hQ ▸ Real.exp_pos _
  obtain ⟨LA, hLA⟩ : ∃ LA, Real.log ((1 - p.α * p.β) / (1 - p.α * p.β * A)) = LA := ⟨_, rfl⟩
  obtain ⟨LB, hLB⟩ : ∃ LB, Real.log ((1 - p.α * p.β) / (1 - p.α * p.β * B)) = LB := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, (p.c0 * x - LA + LB) / (p.σ + p.ω) = y := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, (1 - p.σ) * y + LB = F := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, (1 + p.ω) * y + LA = K := ⟨_, rfl⟩
  have hKF : (K - F) / p.c0 = x := by
    rw [← hK, ← hF, ← hy]; field_simp; ring
  obtain ⟨U, hU⟩ : ∃ U, Real.exp ((1 - p.σ) * y) = U := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, Real.exp ((1 + p.ω) * y) = V := ⟨_, rfl⟩
  obtain ⟨EF, hEF⟩ : ∃ EF, Real.exp F = EF := ⟨_, rfl⟩
  obtain ⟨EK, hEK⟩ : ∃ EK, Real.exp K = EK := ⟨_, rfl⟩
  have hEFp : 0 < EF := hEF ▸ Real.exp_pos _
  have hEKp : 0 < EK := hEK ▸ Real.exp_pos _
  have r5 : (1 - p.α * p.β) * U = EF * (1 - p.α * p.β * B) := by
    rw [← hEF, ← hF, Real.exp_add, hU, ← hLB, Real.exp_log (div_pos hab0 hαβB)]; field_simp
  have r6 : (1 - p.α * p.β) * V = EK * (1 - p.α * p.β * A) := by
    rw [← hEK, ← hK, Real.exp_add, hV, ← hLA, Real.exp_log (div_pos hab0 hαβA)]; field_simp
  have r7 : (1 - p.α) * P = 1 - p.α * B := by rw [← hP]; field_simp
  obtain ⟨D, hD⟩ : ∃ D, (1 - p.α) * Q / (1 - p.α * A) = D := ⟨_, rfl⟩
  have r8 : D * (1 - p.α * A) = (1 - p.α) * Q := by rw [← hD]; field_simp
  obtain ⟨l4, hl4⟩ : ∃ l4, (1 - R.Φ) * R.Au * V / ((1 + p.ω) * (1 - p.α * p.β * A)) = l4 :=
    ⟨_, rfl⟩
  have r4 : (1 + p.ω) * (1 - p.α * p.β * A) * l4 = (1 - R.Φ) * R.Au * V := by
    rw [← hl4]; field_simp
  obtain ⟨W, hW⟩ : ∃ W, -((1 - p.α) * Q * l4) = W := ⟨_, rfl⟩
  obtain ⟨l3, hl3⟩ : ∃ l3, (p.c0 * W / (1 - p.α) + aE p * l4 * Q) / ((p.θ - 1) * P) = l3 :=
    ⟨_, rfl⟩
  have r3 : (1 - p.α) * (p.θ - 1) * l3 * P = p.c0 * W + (1 - p.α) * aE p * l4 * Q := by
    rw [← hl3]; field_simp
  obtain ⟨l1, hl1⟩ : ∃ l1, -W / (EF * (1 - p.α * B)) = l1 := ⟨_, rfl⟩
  have r1 : l1 * EF * (1 - p.α * B) + W = 0 := by rw [← hl1]; field_simp; ring
  obtain ⟨l2, hl2⟩ : ∃ l2, W / (EK * (1 - p.α * A)) = l2 := ⟨_, rfl⟩
  have r2 : l2 * EK * (1 - p.α * A) - W = 0 := by rw [← hl2]; field_simp; ring
  have rQK : Q * EK = P * EF := by
    rw [← hQ, ← hEK, ← hxP, ← hEF, ← Real.exp_add, ← Real.exp_add]
    congr 1
    have hcx : p.c0 * x = K - F := by rw [← hKF]; field_simp
    linear_combination -hcx - x * hc0a
  have hWv : W = -((1 - p.α) * Q * l4) := hW.symm
  have eB : Real.exp ((p.θ - 1) * π + F) = B * EF := by rw [Real.exp_add, hB, hEF]
  have eA : Real.exp (aE p * π + K) = A * EK := by rw [Real.exp_add, hA, hEK]
  refine ⟨![y, π, F, K, D, l1, l2, l3, l4], ss_of_vals p R y π F K D l1 l2 l3 l4 ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_, rfl⟩
  · -- output
    rw [hU, hV]
    set Z := (1 - p.α * B) * R.Au * U - (1 - p.σ) * (1 - p.α * p.β * B) * (1 - p.α) * Q * l4
      with hZd
    have hZ' : (1 + p.ω) * (1 - p.α * p.β * A) * (1 - p.α * p.β) * Z = 0 := by
      linear_combination -(1 - p.α * p.β * A) * (1 - p.α * B) * (1 - p.α * p.β) * R.Au * U * hΦ -
        (1 - p.σ) * (1 - p.α * p.β * B) * (1 - p.α) * Q * (1 - p.α * p.β) * r4 -
        (1 - p.σ) * (1 - p.α * p.β * B) * (1 - p.α) * (1 - R.Φ) * R.Au * Q * r6 -
        (1 - p.σ) * (1 - p.α * p.β * B) * (1 - p.α) * (1 - R.Φ) * R.Au *
          (1 - p.α * p.β * A) * rQK -
        (1 - p.σ) * (1 - p.α * p.β * B) * (1 - R.Φ) * R.Au * (1 - p.α * p.β * A) * EF * r7 +
        (1 - p.σ) * (1 - R.Φ) * R.Au * (1 - p.α * p.β * A) * (1 - p.α * B) * r5
    have hZ : Z = 0 := (mul_eq_zero.mp hZ').resolve_left
      (mul_ne_zero (mul_ne_zero hω.ne' hαβA.ne') hab0.ne')
    have hG2 : (1 - p.α * B) * (1 - p.α * A) * R.Au * U -
        (1 - R.Φ) * R.Au * V * (1 - p.α * B) * (1 - p.α) * Q +
        (1 - p.σ) * (1 - p.α * p.β * B) * (1 - p.α * A) * W -
        (1 + p.ω) * (1 - p.α * p.β * A) * (1 - p.α * B) * W = 0 := by
      linear_combination (1 - p.α * A) * hZ + (1 - p.α * B) * (1 - p.α) * Q * r4 +
        ((1 - p.σ) * (1 - p.α * p.β * B) * (1 - p.α * A) -
          (1 + p.ω) * (1 - p.α * p.β * A) * (1 - p.α * B)) * hWv
    have hG0A : (1 - p.α * B) * (1 - p.α * A) * (R.Au * U - (1 - R.Φ) * R.Au * D * V -
        (1 - p.σ) * (1 - p.α * p.β * B) * (l1 * EF) -
        (1 + p.ω) * (1 - p.α * p.β * A) * (l2 * EK)) = 0 := by
      linear_combination hG2 - (1 - R.Φ) * R.Au * V * (1 - p.α * B) * r8 -
        (1 - p.σ) * (1 - p.α * p.β * B) * (1 - p.α * A) * r1 -
        (1 + p.ω) * (1 - p.α * p.β * A) * (1 - p.α * B) * r2
    have hA0 := (mul_eq_zero.mp hG0A).resolve_left (mul_ne_zero hαB.ne' hαA.ne')
    linear_combination hA0 - (1 - p.σ) * l1 * r5 - (1 + p.ω) * l2 * r6
  · -- inflation
    rw [eB, eA, hB, hA]
    have hH : (1 - p.α * B) * (1 - p.α * A) * (-(p.α * (p.θ - 1) * l1 * (B * EF)) -
        p.α * aE p * l2 * (A * EK) + p.α * (p.θ - 1) * l3 * B - p.α * aE p * l4 * D * A) = 0 := by
      linear_combination p.α * aE p * (B - A) * hWv - p.α * W * B * (1 - p.α * A) * hc0a +
        p.α * B * (1 - p.α * A) * r3 - p.α * (p.θ - 1) * B * (1 - p.α * A) * r1 -
        p.α * aE p * A * (1 - p.α * B) * r2 - p.α * (p.θ - 1) * l3 * B * (1 - p.α * A) * r7 -
        p.α * aE p * l4 * A * (1 - p.α * B) * r8
    exact (mul_eq_zero.mp hH).resolve_left (mul_ne_zero hαB.ne' hαA.ne')
  · -- `F`
    rw [hKF, hxP, hQ, eB, hEF]
    linear_combination r1 + p.c0⁻¹ * r3 + W * hc0inv
  · -- `K`
    rw [hKF, hxP, hQ, eA, hEK]
    linear_combination r2 - p.c0⁻¹ * r3 - W * hc0inv
  · -- dispersion multiplier
    rw [hV, hA]
    have e : (1 - R.Φ) * R.Au * V / (1 + p.ω) = (1 - p.α * p.β * A) * l4 := by
      rw [← r4]; field_simp
    rw [e]; ring
  · -- `F` recursion
    rw [eB, hEF, hU]
    linear_combination -r5
  · -- `K` recursion
    rw [eA, hEK, hV]
    linear_combination -r6
  · -- price index
    rw [hKF, hxP, hB]
    linear_combination r7
  · -- dispersion
    rw [hKF, hQ, hA]
    linear_combination r8

end Woodford.StabilizationWelfare.TidyR5RamseyLongRun
