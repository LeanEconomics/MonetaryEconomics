/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR5RamseyStability
import StabilizationWelfare.NonlinearNKMarkovRamseyMarkov

/-!
# The date-0 optimal commitment of the exact model: existence and convergence

Woodford (2003), *Interest and Prices*, Chapter 6, §3.2, pp. 413–415 ("the optimal commitment
from date zero onward … should converge asymptotically to zero", "the rate at which inflation is
committed to decline to zero should be completely unaffected by random disturbances") and §5
(Benigno–Woodford: the exact Calvo model with a distortion `Φ`); Chapter 7, §1 (the date-0 plan
and the plan that is optimal from a timeless perspective).

The date-0 Ramsey problem has no constraint before date 0, so its first-order conditions are the
exact Ramsey conditions `NonlinearNKMarkovRamsey.ramseyQ` with the lagged multipliers of the
`F` and `K` recursions equal to ZERO at date 0 (`lagD0`); the timeless plan instead starts from
the steady-state multipliers (`lagTL`). With `Φ > 0` the steady-state multipliers are not zero, so
the two plans differ.

## Main results

* **`absorb`**: the distortion is a constant disturbance:
  `ramseyQ` of the economy `(A/(1−Φ), Φ)` equals `ramseyQ` of the efficient economy `(A, 0)` with
  the constant shocks `ĉ = −log(1−Φ)/σ`, `τ̂ = log(1−Φ)` (`ePhi`). The radii of the implicit
  function theorem therefore do not depend on `Φ`.
* `RamseyL` (the conditions in levels on an event tree with a root lag), `PhiR_level`,
  `ramseyL_iff`, `ramseyL_absorb`, `ramseyL_congr_lag`, `PhiR_congr_lag`, `phiR_zero_small`.
* **`date0_main`**: for `0 ≤ Φ` small, on every event tree with small disturbances and initial
  dispersion, the date-0 plan and the timeless plan both exist and are locally unique, and they
  differ by at most `C|λ̄₁(Φ)|μ^{date}` (`max(α, z₁) < μ ≤ 1`): the date-0 plan converges to the
  timeless plan, geometrically, whatever the disturbances.
* **`date0_converges_ss`**: without disturbances the date-0 plan converges geometrically to the
  zero-inflation steady state, `‖w(y) − w̄(Φ)‖ ≤ C(|λ̄₁(Φ)| + |Δ_{−1} − 1|)μ^{date(y)}`
  (`ss_solves`, `norm_ss_sub`); `natTree` (the deterministic time line), `ramseyL_nat`, and
  **`date0_path`**: the deterministic date-0 path exists and its inflation rate and output gap
  converge to zero and its dispersion to one.
* **`small_of_Phi`**: the smallness conditions hold for all `Φ ∈ [0, Φ₀]`.
* `ramseyQ_scale`, `ramseyN_scale`, `scale_solution`: the conditions are homogeneous of degree one
  in `(A_u, multipliers)`, so the real allocation does not depend on the normalisation;
  **`date0_path_Au`**: the same convergence with `A_{u}` (instead of `A_v = (1 − Φ)A_u`) held fixed.

The solutions are those of the FIRST-ORDER conditions (the Lagrangian derivatives of
NonlinearNKMarkovRamsey); that they maximise the nonlinear objective (second-order sufficiency
in infinite dimensions) is not proved here. In the linear-quadratic approximation used on
p. 415 optimality is proved in TidyR5CommitLQ.
-/

namespace Woodford.StabilizationWelfare.TidyR5RamseyDate0

open Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovGeneral NonlinearNKMarkovRamsey NonlinearNKMarkovRamseyLin
open NonlinearNKMarkovRamseyTree NonlinearNKMarkovRamseyIFT NonlinearNKMarkovRamseyMarkov
open TidyR5RamseyWeighted TidyR5RamseyStability

/-! ## The distortion as a constant disturbance -/

/-- Woodford (2003), §5: the efficient economy with welfare weight `A` (`Φ = 0`). -/
def R0 (A : ℝ) : RPar := ⟨A, 0⟩

/-- Woodford (2003), §5: the economy with distortion `Φ` and `A_v = (1 − Φ)A_u = A`. -/
noncomputable def RPhi (A Φ : ℝ) : RPar := ⟨A / (1 - Φ), Φ⟩

/-- Woodford (2003), §5 (Benigno–Woodford): the constant disturbances `ĉ = −log(1−Φ)/σ`,
`τ̂ = log(1−Φ)` equivalent to the distortion `Φ`. -/
noncomputable def ePhi (p : Par) (Φ : ℝ) : Fin 5 → ℝ :=
  ![0, -(Real.log (1 - Φ) / p.σ), Real.log (1 - Φ), 0, 0]

/-- **Woodford (2003), §5 (the distortion is a constant disturbance).** For `Φ < 1` and `σ ≠ 0`
the exact Ramsey conditions of the economy `(A/(1−Φ), Φ)` are those of the efficient economy
`(A, 0)` with the disturbances shifted by `ePhi`. -/
theorem absorb (p : Par) {A Φ : ℝ} (hΦ : Φ < 1) (hσ : p.σ ≠ 0) (e : Fin 5 → ℝ)
    (wm w : Fin 9 → ℝ) : ramseyQ p (RPhi A Φ) e wm w = ramseyQ p (R0 A) (e + ePhi p Φ) wm w := by
  have h1 : (0 : ℝ) < 1 - Φ := by linarith
  have hfh : (1 - p.σ) * w 0 + p.σ * (e 1 + -(Real.log (1 - Φ) / p.σ)) +
      (e 2 + Real.log (1 - Φ)) = (1 - p.σ) * w 0 + p.σ * e 1 + e 2 := by
    field_simp; ring
  have hu : Real.exp ((1 - p.σ) * w 0 + p.σ * (e 1 + -(Real.log (1 - Φ) / p.σ))) =
      Real.exp ((1 - p.σ) * w 0 + p.σ * e 1) / (1 - Φ) := by
    rw [show (1 - p.σ) * w 0 + p.σ * (e 1 + -(Real.log (1 - Φ) / p.σ)) =
      (1 - p.σ) * w 0 + p.σ * e 1 - Real.log (1 - Φ) by field_simp; ring, Real.exp_sub,
      Real.exp_log h1]
  have hAv : (1 - Φ) * (A / (1 - Φ)) = A := by field_simp
  funext i
  fin_cases i
  all_goals simp only [ramseyQ, RPhi, R0, ePhi, Pi.add_apply, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, add_zero,
    sub_zero, one_mul]
  · rw [hfh, hu, hAv]; field_simp
  · rw [hAv]
  · rw [hfh]

/-- Woodford (2003), §5 (**homogeneity**): scaling the welfare weight `A_{u}` by `s` and the four
multipliers by `s` scales the five first-order conditions by `s` and leaves the four constraints
unchanged. -/
theorem ramseyQ_scale (p : Par) (Au Φ s : ℝ) (e : Fin 5 → ℝ) (wm w : Fin 9 → ℝ) :
    ramseyQ p ⟨s * Au, Φ⟩ e ![wm 0, wm 1, wm 2, wm 3, wm 4, s * wm 5, s * wm 6, s * wm 7, s * wm 8]
      ![w 0, w 1, w 2, w 3, w 4, s * w 5, s * w 6, s * w 7, s * w 8] =
      fun i => (if i.val < 5 then s else 1) * ramseyQ p ⟨Au, Φ⟩ e wm w i := by
  funext i
  fin_cases i <;> simp [ramseyQ] <;> ring

/-- Woodford (2003), §5 (**homogeneity of the lead part**). -/
theorem ramseyN_scale (p : Par) (s : ℝ) (w : Fin 9 → ℝ) :
    ramseyN p ![w 0, w 1, w 2, w 3, w 4, s * w 5, s * w 6, s * w 7, s * w 8] =
      fun i => (if i.val < 5 then s else 1) * ramseyN p w i := by
  funext i
  fin_cases i <;> (simp [ramseyN]; try ring)

/-! ## The conditions in levels on an event tree -/

variable {Y : Type*}

/-- Woodford (2003), §5 and Ch. 7 (**the exact Ramsey conditions in levels on an event tree**):
`Q(e_t, w_{t−1}, w_t) + E_t N(w_{t+1}) = 0` at every node, with the given initial lag at the
roots. -/
def RamseyL (T : LagTree Y) (p : Par) (R : RPar) (e : Y → Fin 5 → ℝ) (lag : Fin 9 → ℝ)
    (w : Y → Fin 9 → ℝ) : Prop :=
  ∀ x, ramseyQ p R (e x) (if T.depth x = 0 then lag else w (T.par x)) (w x) +
    Mv T.M (fun y => ramseyN p (w y)) x = 0

/-- Woodford (2003), Ch. 7: the root lag of the DATE-0 problem: given dispersion `Δ_{−1}`, and
the lagged multipliers of the `F`, `K` recursions equal to zero (no constraint precedes date 0).
-/
def lagD0 (Dm1 : ℝ) : Fin 9 → ℝ := ![0, 0, 0, 0, Dm1, 0, 0, 0, 0]

/-- Woodford (2003), Ch. 7: the root lag of the TIMELESS problem: given dispersion `Δ_{−1}` and
the steady-state multipliers (the commitment "made far in the past"). -/
noncomputable def lagTL (p : Par) (R : RPar) (Dm1 : ℝ) : Fin 9 → ℝ :=
  ![0, 0, 0, 0, Dm1, ramseyLam p R 0, ramseyLam p R 1, ramseyLam p R 2, ramseyLam p R 3]

/-- Woodford (2003), App. A.3: `PhiR` in deviations is the level residual. -/
theorem PhiR_level (T : LagTree Y) (p : Par) (R : RPar) (e : Y → Fin 5 → ℝ) (lag : Fin 9 → ℝ)
    (w : Y → Fin 9 → ℝ) (x : Y) :
    PhiR T p R e (fun _ => lag - ramseySS p R) (fun y => w y - ramseySS p R) x =
      ramseyQ p R (e x) (if T.depth x = 0 then lag else w (T.par x)) (w x) +
        Mv T.M (fun y => ramseyN p (w y)) x := by
  simp only [PhiR, Qd, Nd, lagI]
  split_ifs <;> simp

/-- Woodford (2003), App. A.3: the level conditions are `PhiR = 0` in deviations. -/
theorem ramseyL_iff (T : LagTree Y) (p : Par) (R : RPar) (e : Y → Fin 5 → ℝ) (lag : Fin 9 → ℝ)
    (w : Y → Fin 9 → ℝ) : RamseyL T p R e lag w ↔
      PhiR T p R e (fun _ => lag - ramseySS p R) (fun y => w y - ramseySS p R) = 0 := by
  constructor
  · intro h; funext x; rw [PhiR_level]; exact h x
  · intro h x; rw [← PhiR_level]; exact congrFun h x

/-- Woodford (2003), §5: the level conditions of the distorted economy are those of the efficient
economy with the shifted disturbances. -/
theorem ramseyL_absorb (T : LagTree Y) (p : Par) {A Φ : ℝ} (hΦ : Φ < 1) (hσ : p.σ ≠ 0)
    (e : Y → Fin 5 → ℝ) (lag : Fin 9 → ℝ) (w : Y → Fin 9 → ℝ) :
    RamseyL T p (RPhi A Φ) e lag w ↔ RamseyL T p (R0 A) (fun y => e y + ePhi p Φ) lag w := by
  simp only [RamseyL, absorb p hΦ hσ]

/-- Woodford (2003), §5: the conditions depend on the lag only through `(Δ, λ₁, λ₂)`. -/
theorem ramseyQ_congr (p : Par) (R : RPar) (e : Fin 5 → ℝ) {a a' : Fin 9 → ℝ} (u : Fin 9 → ℝ)
    (h4 : a 4 = a' 4) (h5 : a 5 = a' 5) (h6 : a 6 = a' 6) :
    ramseyQ p R e a u = ramseyQ p R e a' u := by
  simp only [ramseyQ, h4, h5, h6]

/-- Woodford (2003), Ch. 7: lags with the same `(Δ, λ₁, λ₂)` give the same conditions. -/
theorem ramseyL_congr_lag (T : LagTree Y) (p : Par) (R : RPar) (e : Y → Fin 5 → ℝ)
    {lag lag' : Fin 9 → ℝ} (h4 : lag 4 = lag' 4) (h5 : lag 5 = lag' 5) (h6 : lag 6 = lag' 6)
    (w : Y → Fin 9 → ℝ) : RamseyL T p R e lag w ↔ RamseyL T p R e lag' w := by
  have key : ∀ x, ramseyQ p R (e x) (if T.depth x = 0 then lag else w (T.par x)) (w x) =
      ramseyQ p R (e x) (if T.depth x = 0 then lag' else w (T.par x)) (w x) := fun x => by
    split_ifs
    · exact ramseyQ_congr p R _ _ h4 h5 h6
    · rfl
  simp only [RamseyL, key]

/-- Woodford (2003), Ch. 7: `PhiR` depends on the initial lag only through `(Δ̂, λ̂₁, λ̂₂)`. -/
theorem PhiR_congr_lag (T : LagTree Y) (p : Par) (R : RPar) (e : Y → Fin 5 → ℝ)
    {d d' : Y → Fin 9 → ℝ} (h : ∀ y, d y 4 = d' y 4 ∧ d y 5 = d' y 5 ∧ d y 6 = d' y 6)
    (z : Y → Fin 9 → ℝ) : PhiR T p R e d z = PhiR T p R e d' z := by
  funext x
  simp only [PhiR, lagI]
  split_ifs
  · rw [Qd_congr R (e x) (z x) (h x).1 (h x).2.1 (h x).2.2]
  · rfl

/-- Woodford (2003), App. A.3: for small disturbances and initial lags, the residual at the
steady state is small, uniformly over event trees. -/
theorem phiR_zero_small {p : Par} (R : RPar) (hp : p.Std) {τ : ℝ} (hτ : 0 < τ) :
    ∃ δ > 0, ∀ {Y : Type*} (T : LagTree Y) (e : Y → Fin 5 → ℝ) (d : Y → Fin 9 → ℝ),
      (∀ y, ‖e y‖ ≤ δ) → (∀ y, ‖d y‖ ≤ δ) → ∀ y, ‖PhiR T p R e d (fun _ => 0) y‖ ≤ τ := by
  obtain ⟨δQ, hδQ, hQc⟩ := Metric.continuousAt_iff.1
    ((contDiff_Qd (n := 0) p R).continuous.continuousAt (x := 0)) τ hτ
  refine ⟨δQ / 2, by positivity, fun {Y} T e d he hd y => ?_⟩
  have hss := Qd_Nd_zero R hp
  have e1 : PhiR T p R e d (fun _ => 0) y =
      Qd p R (e y, lagI T (fun _ => 0) d y, 0) - Qd p R 0 := by
    simp only [PhiR, Mv_const']
    rw [eq_neg_of_add_eq_zero_right hss]
    abel
  rw [e1, ← dist_eq_norm]
  refine (hQc ?_).le
  rw [dist_zero_right, Prod.norm_def, Prod.norm_def]
  have hl : ‖lagI T (fun _ => (0 : Fin 9 → ℝ)) d y‖ ≤ δQ / 2 := by
    unfold lagI; split_ifs
    · exact hd y
    · rw [norm_zero]; positivity
  have h0 : ‖(0 : Fin 9 → ℝ)‖ ≤ δQ / 2 := by rw [norm_zero]; positivity
  exact lt_of_le_of_lt (max_le (he y) (max_le hl h0)) (by linarith)

/-! ## The date-0 and the timeless plans near the efficient steady state -/

/-- Woodford (2003), §5: in the efficient economy the multipliers of the `F`, `K` recursions are
zero at the steady state. -/
theorem lam_R0 (p : Par) (A : ℝ) : ramseyLam p (R0 A) 0 = 0 ∧ ramseyLam p (R0 A) 1 = 0 := by
  simp [ramseyLam, R0]

/-- Woodford (2003), §5: the steady-state dispersion multiplier does not depend on `Φ` when
`A_v = (1 − Φ)A_u = A` is held fixed. -/
theorem lam3_RPhi (p : Par) {A Φ : ℝ} (hΦ : Φ ≠ 1) :
    ramseyLam p (RPhi A Φ) 3 = ramseyLam p (R0 A) 3 := by
  have h1 : (1 : ℝ) - Φ ≠ 0 := sub_ne_zero.mpr (Ne.symm hΦ)
  simp only [ramseyLam, RPhi, R0, Matrix.cons_val, sub_zero]
  field_simp

/-- A sup-norm bound for vectors of `ℝ⁹` from bounds on the components. -/
theorem norm_le_of_abs {v : Fin 9 → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, |v i| ≤ c) : ‖v‖ ≤ c :=
  (pi_norm_le_iff_of_nonneg hc).2 fun i => by rw [Real.norm_eq_abs]; exact h i

/-- Woodford (2003), Ch. 7: the date-0 root lag in deviations from the efficient steady state. -/
def d0v (Dm1 : ℝ) : Fin 9 → ℝ := ![0, 0, 0, 0, Dm1 - 1, 0, 0, 0, 0]

/-- Woodford (2003), Ch. 7: the timeless root lag of the economy `(A/(1−Φ), Φ)` in deviations
from the efficient steady state (relevant components). -/
noncomputable def dTv (p : Par) (A Φ Dm1 : ℝ) : Fin 9 → ℝ :=
  ![0, 0, 0, 0, Dm1 - 1, ramseyLam p (RPhi A Φ) 0, ramseyLam p (RPhi A Φ) 1, 0, 0]

/-- Woodford (2003), Ch. 7: the size of the date-0 root lag. -/
theorem norm_d0v (Dm1 : ℝ) : ‖d0v Dm1‖ ≤ |Dm1 - 1| :=
  norm_le_of_abs (abs_nonneg _) fun i => by
    fin_cases i <;> simp [d0v]

/-- Woodford (2003), Ch. 7: the size of the timeless root lag. -/
theorem norm_dTv (p : Par) (A Φ Dm1 : ℝ) :
    ‖dTv p A Φ Dm1‖ ≤ |Dm1 - 1| + |ramseyLam p (RPhi A Φ) 0| :=
  norm_le_of_abs (by positivity) fun i => by
    have h1 : ramseyLam p (RPhi A Φ) 1 = -ramseyLam p (RPhi A Φ) 0 := rfl
    have a1 := abs_nonneg (Dm1 - 1)
    have a2 := abs_nonneg (ramseyLam p (RPhi A Φ) 0)
    fin_cases i <;> simp only [dTv, h1, Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero,
      Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val, abs_zero, abs_neg] <;>
      first | positivity | linarith

/-- **Woodford (2003), Ch. 7 (the two plans differ only in the initial multipliers).** The date-0
and the timeless root lags differ by `|λ̄₁(Φ)|`, the steady-state multiplier of the `F`
recursion (zero exactly when `Φ = 0`). -/
theorem norm_d0v_sub_dTv (p : Par) (A Φ Dm1 : ℝ) :
    ‖d0v Dm1 - dTv p A Φ Dm1‖ ≤ |ramseyLam p (RPhi A Φ) 0| :=
  norm_le_of_abs (abs_nonneg _) fun i => by
    have h1 : ramseyLam p (RPhi A Φ) 1 = -ramseyLam p (RPhi A Φ) 0 := rfl
    fin_cases i <;> simp [d0v, dTv, h1]

/-- Woodford (2003), Ch. 7: the date-0 conditions of the economy `(A/(1−Φ), Φ)` in levels are the
efficient-economy conditions in deviations, with the shifted disturbances and the root lag
`d0v`. -/
theorem date0_iff (T : LagTree Y) (p : Par) {A Φ : ℝ} (hΦ : Φ < 1) (hσ : p.σ ≠ 0)
    (e : Y → Fin 5 → ℝ) (Dm1 : ℝ) (w : Y → Fin 9 → ℝ) :
    RamseyL T p (RPhi A Φ) e (lagD0 Dm1) w ↔ PhiR T p (R0 A) (fun y => e y + ePhi p Φ)
      (fun _ => d0v Dm1) (fun y => w y - ramseySS p (R0 A)) = 0 := by
  rw [ramseyL_absorb T p hΦ hσ, ramseyL_iff, PhiR_congr_lag T p (R0 A) _ (d' := fun _ => d0v Dm1)
    (fun y => by simp [d0v, lagD0, ramseySS, (lam_R0 p A).1, (lam_R0 p A).2])]

/-- Woodford (2003), Ch. 7: the timeless conditions of the economy `(A/(1−Φ), Φ)` in levels are
the efficient-economy conditions in deviations, with the root lag `dTv`. -/
theorem timeless_iff (T : LagTree Y) (p : Par) {A Φ : ℝ} (hΦ : Φ < 1) (hσ : p.σ ≠ 0)
    (e : Y → Fin 5 → ℝ) (Dm1 : ℝ) (w : Y → Fin 9 → ℝ) :
    RamseyL T p (RPhi A Φ) e (lagTL p (RPhi A Φ) Dm1) w ↔ PhiR T p (R0 A)
      (fun y => e y + ePhi p Φ) (fun _ => dTv p A Φ Dm1) (fun y => w y - ramseySS p (R0 A)) =
        0 := by
  rw [ramseyL_absorb T p hΦ hσ, ramseyL_iff, PhiR_congr_lag T p (R0 A) _
    (d' := fun _ => dTv p A Φ Dm1)
    (fun y => by simp [dTv, lagTL, ramseySS, (lam_R0 p A).1, (lam_R0 p A).2])]

/-- **Woodford (2003), pp. 414–415 and Ch. 7 (the date-0 optimal plan exists and converges to the
timeless plan, for the exact model).** Let `A ≠ 0` and `max(α, z₁) < μ ≤ 1`. There are `r, δ > 0`
and `C ≥ 0` such that for every distortion `0 ≤ Φ < 1` with `‖ePhi Φ‖ ≤ δ` and `|λ̄₁(Φ)| ≤ δ`
(`small_of_Phi`: all `Φ ∈ [0, Φ₀]`), every event tree, every disturbance process with
`‖e‖ ≤ δ` and every initial dispersion with `|Δ_{−1} − 1| ≤ δ`:
* the date-0 Ramsey conditions (`lagD0`) have a solution `w⁰` within `r` of the efficient
  steady state, and it is the only one there;
* the timeless Ramsey conditions (`lagTL`) have a solution `wᵀ`, the only one there;
* `‖w⁰(y) − wᵀ(y)‖ ≤ C|λ̄₁(Φ)|μ^{date(y)}`. -/
theorem date0_main {p : Par} (hp : p.Std) {A : ℝ} (hA : A ≠ 0) {μ : ℝ} (hμα : p.α < μ)
    (hμz : z1 p < μ) (hμ1 : μ ≤ 1) :
    ∃ r > 0, ∃ δ > 0, ∃ C, 0 ≤ C ∧ ∀ Φ, 0 ≤ Φ → Φ < 1 → ‖ePhi p Φ‖ ≤ δ →
      |ramseyLam p (RPhi A Φ) 0| ≤ δ → ∀ {Y : Type*} (T : LagTree Y) (e : Y → Fin 5 → ℝ)
        (Dm1 : ℝ), (∀ y, ‖e y‖ ≤ δ) → |Dm1 - 1| ≤ δ →
          ∃ w0 wT : Y → Fin 9 → ℝ,
            (RamseyL T p (RPhi A Φ) e (lagD0 Dm1) w0 ∧
              (∀ y, ‖w0 y - ramseySS p (R0 A)‖ ≤ r) ∧
              ∀ w', RamseyL T p (RPhi A Φ) e (lagD0 Dm1) w' →
                (∀ y, ‖w' y - ramseySS p (R0 A)‖ ≤ r) → w' = w0) ∧
            (RamseyL T p (RPhi A Φ) e (lagTL p (RPhi A Φ) Dm1) wT ∧
              (∀ y, ‖wT y - ramseySS p (R0 A)‖ ≤ r) ∧
              ∀ w', RamseyL T p (RPhi A Φ) e (lagTL p (RPhi A Φ) Dm1) w' →
                (∀ y, ‖w' y - ramseySS p (R0 A)‖ ≤ r) → w' = wT) ∧
            ∀ y, ‖w0 y - wT y‖ ≤ C * |ramseyLam p (RPhi A Φ) 0| * μ ^ T.depth y := by
  have hσ : p.σ ≠ 0 := hp.σ_pos.ne'
  have hG : (R0 A).Au * Gw p (R0 A) ≠ 0 := by
    have : 0 < Gw p (R0 A) := by
      simp only [Gw, R0, zero_mul, add_zero]; linarith [hp.σ_pos, hp.ω_nonneg]
    exact mul_ne_zero hA this.ne'
  obtain ⟨rE, hrE, δE, hδE, CE, hCE, hEx⟩ := ramsey_existence (R0 A) hp hG
  obtain ⟨rS, hrS, CS, hCS, hSt⟩ := lag_stability (R0 A) hp hG hμα hμz hμ1
  set r := min rE rS with hr
  have hr0 : 0 < r := lt_min hrE hrS
  obtain ⟨δc, hδc, hsmall⟩ := phiR_zero_small (R0 A) hp (τ := r / (2 * CE)) (by positivity)
  set δ := min (min (δE / 2) (r / 2)) (min (δc / 2) (r / (2 * (CS + 1)))) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ δE / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ r / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : δ ≤ δc / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ4 : δ ≤ r / (2 * (CS + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r, hr0, δ, hδ0, CS, hCS, fun Φ hΦ0 hΦ1 hePhi hlam {Y} T e Dm1 he hDm1 => ?_⟩
  obtain ⟨e', he'⟩ : ∃ e' : Y → Fin 5 → ℝ, e' = fun y => e y + ePhi p Φ := ⟨_, rfl⟩
  obtain ⟨ss0, hss0⟩ : ∃ ss0 : Fin 9 → ℝ, ss0 = ramseySS p (R0 A) := ⟨_, rfl⟩
  set lam := |ramseyLam p (RPhi A Φ) 0| with hlamd
  have he'b : ∀ y, ‖e' y‖ ≤ 2 * δ := fun y => by
    rw [he']; exact (norm_add_le _ _).trans (by linarith [he y])
  have hd0b : ∀ y : Y, ‖(fun _ => d0v Dm1) y‖ ≤ δ := fun _ => (norm_d0v Dm1).trans hDm1
  have hdTb : ∀ y : Y, ‖(fun _ => dTv p A Φ Dm1) y‖ ≤ 2 * δ := fun _ =>
    (norm_dTv p A Φ Dm1).trans (by linarith)
  -- the existence theorem in the efficient frame
  have exist : ∀ dd : Y → Fin 9 → ℝ, (∀ y, ‖dd y‖ ≤ 2 * δ) →
      ∃ z : Y → Fin 9 → ℝ, ((∀ y, ‖z y‖ ≤ r / 2) ∧ PhiR T p (R0 A) e' dd z = 0) ∧
        ∀ z' : Y → Fin 9 → ℝ, (∀ y, ‖z' y‖ ≤ r) → PhiR T p (R0 A) e' dd z' = 0 → z' = z := by
    intro dd hdd
    obtain ⟨z, ⟨hzb, hz⟩, huniq, hsm⟩ := hEx T e' dd (fun y => (he'b y).trans (by linarith))
      (fun y => (hdd y).trans (by linarith))
    have hzs := hsm (r / (2 * CE)) (by positivity) (hsmall T e' dd
      (fun y => (he'b y).trans (by linarith)) (fun y => (hdd y).trans (by linarith)))
    refine ⟨z, ⟨fun y => (hzs y).trans (le_of_eq (by field_simp)), hz⟩,
      fun z' hz'b hz' => huniq z' (fun y => (hz'b y).trans (min_le_left _ _)) hz'⟩
  obtain ⟨z0, ⟨hz0b, hz0⟩, hu0⟩ := exist (fun _ => d0v Dm1) (fun y => (hd0b y).trans (by linarith))
  obtain ⟨zT, ⟨hzTb, hzT⟩, huT⟩ := exist (fun _ => dTv p A Φ Dm1) hdTb
  -- stability: the date-0 solution is near the timeless one
  obtain ⟨Z, hZb, hZ, hZw⟩ := hSt r hr0 (min_le_right _ _) T e' (fun _ => d0v Dm1)
    (fun _ => dTv p A Φ Dm1) zT (fun y => (he'b y).trans (by linarith))
    (fun y => (hd0b y).trans (by linarith)) (fun y => (hdTb y).trans (by linarith)) hzTb hzT lam
    (abs_nonneg _) (fun _ => norm_d0v_sub_dTv p A Φ Dm1) (by
      have : CS * lam ≤ CS * (r / (2 * (CS + 1))) :=
        mul_le_mul_of_nonneg_left (hlam.trans hδ4) hCS
      refine this.trans ?_
      rw [show CS * (r / (2 * (CS + 1))) = r / 2 * (CS / (CS + 1)) by field_simp]
      have : CS / (CS + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      nlinarith)
  have hZz0 : Z = z0 := hu0 Z hZb hZ
  refine ⟨fun y => ss0 + z0 y, fun y => ss0 + zT y, ⟨?_, fun y => ?_, fun w' hw' hw'b => ?_⟩,
    ⟨?_, fun y => ?_, fun w' hw' hw'b => ?_⟩, fun y => ?_⟩
  · rw [date0_iff T p hΦ1 hσ, ← he', ← hss0]
    simpa using hz0
  · simp only [add_sub_cancel_left, ← hss0]; exact (hz0b y).trans (by linarith)
  · have := hu0 (fun y => w' y - ss0) (by rw [hss0]; exact hw'b)
      (by rw [he', hss0]; exact (date0_iff T p hΦ1 hσ e Dm1 w').1 hw')
    funext y
    have h := congrFun this y
    rw [← h]; abel
  · rw [timeless_iff T p hΦ1 hσ, ← he', ← hss0]
    simpa using hzT
  · simp only [add_sub_cancel_left, ← hss0]; exact (hzTb y).trans (by linarith)
  · have := huT (fun y => w' y - ss0) (by rw [hss0]; exact hw'b)
      (by rw [he', hss0]; exact (timeless_iff T p hΦ1 hσ e Dm1 w').1 hw')
    funext y
    have h := congrFun this y
    rw [← h]; abel
  · have h := hZw y
    rw [hZz0] at h
    simpa [add_sub_add_left_eq_sub] using h

/-! ## Without disturbances: convergence to the zero-inflation steady state -/

/-- Woodford (2003), §5: the zero-inflation steady state of the economy `(A/(1−Φ), Φ)` solves the
efficient-economy conditions with the constant disturbances `ePhi`, on every event tree, with
itself as the lag. -/
theorem ss_solves (T : LagTree Y) {p : Par} (hp : p.Std) {A Φ : ℝ} (hΦ : Φ < 1) :
    RamseyL T p (R0 A) (fun _ => 0 + ePhi p Φ) (ramseySS p (RPhi A Φ))
      (fun _ => ramseySS p (RPhi A Φ)) := by
  intro x
  have h := ramsey_steadyState p (RPhi A Φ) hp
  rw [absorb p hΦ hp.σ_pos.ne'] at h
  have hM : Mv T.M (fun _ => ramseyN p (ramseySS p (RPhi A Φ))) x =
      ramseyN p (ramseySS p (RPhi A Φ)) := Mv_const T.markov _ x
  rw [hM]
  split_ifs <;> exact h

/-- Woodford (2003), §5: the steady state of the economy `(A/(1−Φ), Φ)` is within
`(1 + (1+ωθ)/(θ−1))|λ̄₁(Φ)|` of the efficient steady state. -/
theorem norm_ss_sub {p : Par} (hp : p.Std) {A Φ : ℝ} (hΦ : Φ ≠ 1) :
    ‖ramseySS p (RPhi A Φ) - ramseySS p (R0 A)‖ ≤
      (1 + p.c0 / (p.θ - 1)) * |ramseyLam p (RPhi A Φ) 0| := by
  have hθ : 0 < p.θ - 1 := by linarith [hp.one_lt_θ]
  have hc := hp.c0_pos
  have h3 := lam3_RPhi p (A := A) hΦ
  obtain ⟨l0, l1⟩ := lam_R0 p A
  have h1 : ramseyLam p (RPhi A Φ) 1 = -ramseyLam p (RPhi A Φ) 0 := rfl
  have h2 : ramseyLam p (RPhi A Φ) 2 - ramseyLam p (R0 A) 2 =
      -(p.c0 / (p.θ - 1) * ramseyLam p (RPhi A Φ) 0) := by
    have e1 : ramseyLam p (RPhi A Φ) 2 = (aE p * ramseyLam p (RPhi A Φ) 3 -
        p.c0 * ramseyLam p (RPhi A Φ) 0) / (p.θ - 1) := rfl
    have e2 : ramseyLam p (R0 A) 2 = (aE p * ramseyLam p (R0 A) 3 -
        p.c0 * ramseyLam p (R0 A) 0) / (p.θ - 1) := rfl
    rw [e1, e2, h3, l0]
    field_simp
    ring
  have hk : 0 ≤ p.c0 / (p.θ - 1) := by positivity
  set L := |ramseyLam p (RPhi A Φ) 0|
  have hL : 0 ≤ L := abs_nonneg _
  refine norm_le_of_abs (by positivity) fun i => ?_
  fin_cases i <;> simp only [ramseySS, Pi.sub_apply, Fin.isValue, Fin.zero_eta,
    Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val,
    sub_self, abs_zero, l0, l1, sub_zero, h1, abs_neg, h2, h3]
  all_goals have hm := abs_mul (p.c0 / (p.θ - 1)) (ramseyLam p (RPhi A Φ) 0)
  all_goals have hk' := abs_of_nonneg hk
  all_goals first | positivity | nlinarith

/-- **Woodford (2003), pp. 414–415 ("the deterministic path for planned inflation should converge
asymptotically to zero"), for the exact model.** Let `A ≠ 0` and `max(α, z₁) < μ ≤ 1`. There are
`r, δ > 0` and `C ≥ 0` such that for every `0 ≤ Φ < 1` with `‖ePhi Φ‖ ≤ δ`, `|λ̄₁(Φ)| ≤ δ`, every
event tree and every initial dispersion with `|Δ_{−1} − 1| ≤ δ`, the date-0 Ramsey conditions
WITHOUT disturbances have a solution `w` within `r` of the efficient steady state, the only one
there, and `‖w(y) − w̄(Φ)‖ ≤ C(|λ̄₁(Φ)| + |Δ_{−1} − 1|)μ^{date(y)}`, `w̄(Φ)` the zero-inflation
steady state. -/
theorem date0_converges_ss {p : Par} (hp : p.Std) {A : ℝ} (hA : A ≠ 0) {μ : ℝ}
    (hμα : p.α < μ) (hμz : z1 p < μ) (hμ1 : μ ≤ 1) :
    ∃ r > 0, ∃ δ > 0, ∃ C, 0 ≤ C ∧ ∀ Φ, 0 ≤ Φ → Φ < 1 → ‖ePhi p Φ‖ ≤ δ →
      |ramseyLam p (RPhi A Φ) 0| ≤ δ → ∀ {Y : Type*} (T : LagTree Y) (Dm1 : ℝ),
        |Dm1 - 1| ≤ δ → ∃ w : Y → Fin 9 → ℝ,
          RamseyL T p (RPhi A Φ) (fun _ => 0) (lagD0 Dm1) w ∧
            (∀ y, ‖w y - ramseySS p (R0 A)‖ ≤ r) ∧
            (∀ w', RamseyL T p (RPhi A Φ) (fun _ => 0) (lagD0 Dm1) w' →
              (∀ y, ‖w' y - ramseySS p (R0 A)‖ ≤ r) → w' = w) ∧
            ∀ y, ‖w y - ramseySS p (RPhi A Φ)‖ ≤
              C * (|ramseyLam p (RPhi A Φ) 0| + |Dm1 - 1|) * μ ^ T.depth y := by
  have hσ : p.σ ≠ 0 := hp.σ_pos.ne'
  have hG : (R0 A).Au * Gw p (R0 A) ≠ 0 := by
    have : 0 < Gw p (R0 A) := by
      simp only [Gw, R0, zero_mul, add_zero]; linarith [hp.σ_pos, hp.ω_nonneg]
    exact mul_ne_zero hA this.ne'
  have hθ : 0 < p.θ - 1 := by linarith [hp.one_lt_θ]
  set cz := 1 + p.c0 / (p.θ - 1) with hcz
  have hcz1 : 1 ≤ cz := by
    have : 0 ≤ p.c0 / (p.θ - 1) := div_nonneg hp.c0_pos.le hθ.le
    rw [hcz]; linarith
  obtain ⟨rE, hrE, δE, hδE, CE, hCE, hEx⟩ := ramsey_existence (R0 A) hp hG
  obtain ⟨rS, hrS, CS, hCS, hSt⟩ := lag_stability (R0 A) hp hG hμα hμz hμ1
  set r := min rE rS with hr
  have hr0 : 0 < r := lt_min hrE hrS
  obtain ⟨δc, hδc, hsmall⟩ := phiR_zero_small (R0 A) hp (τ := r / (2 * CE)) (by positivity)
  set δ := min (min (δE / 2) (r / (4 * cz))) (min (δc / 2) (r / (4 * (CS + 1)))) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ δE / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ r / (4 * cz) := (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : δ ≤ δc / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ4 : δ ≤ r / (4 * (CS + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hδr : δ ≤ r / 4 := hδ2.trans (by
    rw [div_le_div_iff_of_pos_left hr0 (by positivity) (by norm_num)]; linarith)
  refine ⟨r, hr0, δ, hδ0, CS, hCS, fun Φ hΦ0 hΦ1 hePhi hlam {Y} T Dm1 hDm1 => ?_⟩
  obtain ⟨e', he'⟩ : ∃ e' : Y → Fin 5 → ℝ, e' = fun _ => 0 + ePhi p Φ := ⟨_, rfl⟩
  obtain ⟨ss0, hss0⟩ : ∃ ss0 : Fin 9 → ℝ, ss0 = ramseySS p (R0 A) := ⟨_, rfl⟩
  set lam := |ramseyLam p (RPhi A Φ) 0| with hlamd
  have he'b : ∀ y, ‖e' y‖ ≤ δ := fun y => by rw [he', zero_add]; exact hePhi
  have hd0b : ∀ y : Y, ‖(fun _ => d0v Dm1) y‖ ≤ δ := fun _ => (norm_d0v Dm1).trans hDm1
  -- the date-0 solution from the existence theorem
  obtain ⟨z0, ⟨hz0b, hz0⟩, hu0, hsm⟩ := hEx T e' (fun _ => d0v Dm1)
    (fun y => (he'b y).trans (by linarith)) (fun y => (hd0b y).trans (by linarith))
  have hz0s := hsm (r / (2 * CE)) (by positivity) (hsmall T e' (fun _ => d0v Dm1)
    (fun y => (he'b y).trans (by linarith)) (fun y => (hd0b y).trans (by linarith)))
  have hz0r : ∀ y, ‖z0 y‖ ≤ r / 2 := fun y => (hz0s y).trans (le_of_eq (by field_simp))
  have hu0r : ∀ z' : Y → Fin 9 → ℝ, (∀ y, ‖z' y‖ ≤ r) → PhiR T p (R0 A) e' (fun _ => d0v Dm1) z' = 0
      → z' = z0 := fun z' hz'b hz' => hu0 z' (fun y => (hz'b y).trans (min_le_left _ _)) hz'
  -- the steady state as the comparison solution
  set zb : Fin 9 → ℝ := ramseySS p (RPhi A Φ) - ss0 with hzb
  have hzbn : ‖zb‖ ≤ cz * lam := by rw [hzb, hss0]; exact norm_ss_sub hp hΦ1.ne
  have hzbs : PhiR T p (R0 A) e' (fun _ => dTv p A Φ 1) (fun _ => zb) = 0 := by
    have h := (ramseyL_iff T p (R0 A) _ _ _).1 (ss_solves T hp hΦ1 (A := A))
    rw [PhiR_congr_lag T p (R0 A) _ (d' := fun _ => dTv p A Φ 1) (fun y => by
      simp [dTv, ramseySS, (lam_R0 p A).1, (lam_R0 p A).2])] at h
    rw [he', hzb, hss0]
    exact h
  have hdd : ∀ y : Y, ‖(fun _ => d0v Dm1) y - (fun _ => dTv p A Φ 1) y‖ ≤ lam + |Dm1 - 1| :=
    fun _ => by
      refine norm_le_of_abs (by positivity) fun i => ?_
      have h1 : ramseyLam p (RPhi A Φ) 1 = -ramseyLam p (RPhi A Φ) 0 := rfl
      have a1 := abs_nonneg (Dm1 - 1)
      have a2 := abs_nonneg (ramseyLam p (RPhi A Φ) 0)
      fin_cases i <;> simp only [d0v, dTv, h1, Pi.sub_apply, Fin.isValue, Fin.zero_eta,
        Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val,
        sub_self, abs_zero, sub_neg_eq_add, zero_sub, abs_neg, sub_zero, zero_add] <;>
        first | positivity | linarith
  have hdTb : ∀ y : Y, ‖(fun _ => dTv p A Φ 1) y‖ ≤ 2 * δ := fun _ =>
    (norm_dTv p A Φ 1).trans (by simp only [sub_self, abs_zero, zero_add]; linarith)
  obtain ⟨Z, hZb, hZ, hZw⟩ := hSt r hr0 (min_le_right _ _) T e' (fun _ => d0v Dm1)
    (fun _ => dTv p A Φ 1) (fun _ => zb) (fun y => (he'b y).trans (by linarith))
    (fun y => (hd0b y).trans (by linarith)) (fun y => (hdTb y).trans (by linarith))
    (fun _ => hzbn.trans (by
      have : cz * lam ≤ cz * δ := mul_le_mul_of_nonneg_left hlam (by linarith)
      have : cz * δ ≤ cz * (r / (4 * cz)) := mul_le_mul_of_nonneg_left hδ2 (by linarith)
      have : cz * (r / (4 * cz)) = r / 4 := by field_simp
      linarith))
    hzbs (lam + |Dm1 - 1|) (by positivity) hdd (by
      have h1 : lam + |Dm1 - 1| ≤ 2 * δ := by linarith
      have : CS * (lam + |Dm1 - 1|) ≤ CS * (2 * (r / (4 * (CS + 1)))) :=
        mul_le_mul_of_nonneg_left (h1.trans (by linarith)) hCS
      refine this.trans ?_
      rw [show CS * (2 * (r / (4 * (CS + 1)))) = r / 2 * (CS / (CS + 1)) by field_simp; ring]
      have : CS / (CS + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      nlinarith)
  have hZz0 : Z = z0 := hu0r Z hZb hZ
  refine ⟨fun y => ss0 + z0 y, ?_, fun y => ?_, fun w' hw' hw'b => ?_, fun y => ?_⟩
  · rw [date0_iff T p hΦ1 hσ]
    have e1 : (fun y : Y => (fun _ : Y => (0 : Fin 5 → ℝ)) y + ePhi p Φ) = e' := by rw [he']
    rw [e1, ← hss0]
    simpa using hz0
  · simp only [add_sub_cancel_left, ← hss0]; exact (hz0r y).trans (by linarith)
  · have e1 : (fun y : Y => (fun _ : Y => (0 : Fin 5 → ℝ)) y + ePhi p Φ) = e' := by rw [he']
    have h' := (date0_iff T p hΦ1 hσ _ Dm1 w').1 hw'
    rw [e1, ← hss0] at h'
    have := hu0r (fun y => w' y - ss0) (by rw [hss0]; exact hw'b) h'
    funext y
    have h := congrFun this y
    rw [← h]; abel
  · have h := hZw y
    rw [hZz0] at h
    have e2 : ss0 + z0 y - ramseySS p (RPhi A Φ) = z0 y - zb := by rw [hzb]; abel
    rw [e2]
    simpa using h

/-! ## The deterministic time line -/

/-- Woodford (2003), App. A.3: the shift `(Mf)(t) = f(t+1)`, the expectation operator of a
deterministic economy. -/
def natM : (ℕ → ℝ) →ₗ[ℝ] (ℕ → ℝ) where
  toFun f t := f (t + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Woodford (2003), pp. 414–415 (**the deterministic time line as an event tree**): one node per
date, the parent of `t + 1` is `t`. -/
def natTree : LagTree ℕ where
  M := natM
  markov := ⟨rfl, fun _ _ hC x => hC (x + 1)⟩
  par t := t - 1
  depth t := t
  depth_par t ht := by omega
  M_par f := by funext t; simp [natM]
  M_root f g h := by funext t; exact h (t + 1) (by omega)

/-- Woodford (2003), pp. 414–415: on the time line the conditions are
`Q(e_t, w_{t−1}, w_t) + N(w_{t+1}) = 0` with the root lag at `t = 0`. -/
theorem ramseyL_nat (p : Par) (R : RPar) (e : ℕ → Fin 5 → ℝ) (lag : Fin 9 → ℝ)
    (w : ℕ → Fin 9 → ℝ) : RamseyL natTree p R e lag w ↔
      ramseyQ p R (e 0) lag (w 0) + ramseyN p (w 1) = 0 ∧
        ∀ t, ramseyQ p R (e (t + 1)) (w t) (w (t + 1)) + ramseyN p (w (t + 2)) = 0 := by
  have hM : ∀ t, Mv natM (fun y => ramseyN p (w y)) t = ramseyN p (w (t + 1)) := fun t => by
    funext i; rfl
  unfold RamseyL
  simp only [natTree, hM]
  constructor
  · intro h
    refine ⟨by simpa using h 0, fun t => ?_⟩
    have := h (t + 1)
    simpa using this
  · rintro ⟨h0, h⟩ t
    cases t with
    | zero => simpa using h0
    | succ t => simpa using h t

/-- Woodford (2003), §5: the smallness conditions of `date0_main` and `date0_converges_ss` hold for
all distortions `0 ≤ Φ ≤ Φ₀`. -/
theorem small_of_Phi (p : Par) (A : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Φ0 > 0, Φ0 < 1 ∧ ∀ Φ, 0 ≤ Φ → Φ ≤ Φ0 → ‖ePhi p Φ‖ ≤ δ ∧
      |ramseyLam p (RPhi A Φ) 0| ≤ δ := by
  have hlog : ContinuousAt (fun Φ : ℝ => Real.log (1 - Φ)) 0 :=
    (Real.continuousAt_log (by norm_num : (1 : ℝ) - 0 ≠ 0)).comp
      (continuousAt_const.sub continuousAt_id)
  have hc1 : ContinuousAt (fun Φ => ePhi p Φ) 0 := by
    refine continuousAt_pi.2 fun i => ?_
    fin_cases i <;> simp only [ePhi, Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero,
      Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val]
    · exact continuousAt_const
    · exact (hlog.div_const _).neg
    · exact hlog
    · exact continuousAt_const
    · exact continuousAt_const
  have hc2 : ContinuousAt (fun Φ => ramseyLam p (RPhi A Φ) 0) 0 := by
    simp only [ramseyLam, RPhi, Matrix.cons_val_zero]
    refine ((continuousAt_id.mul (continuousAt_const.div (continuousAt_const.sub
      continuousAt_id) (by norm_num))).div_const _).neg
  have e1 : ePhi p 0 = 0 := by funext i; fin_cases i <;> simp [ePhi]
  have e2 : ramseyLam p (RPhi A 0) 0 = 0 := by simp [ramseyLam, RPhi]
  obtain ⟨η1, hη1, h1⟩ := Metric.continuousAt_iff.1 hc1 δ hδ
  obtain ⟨η2, hη2, h2⟩ := Metric.continuousAt_iff.1 hc2 δ hδ
  refine ⟨min (min (η1 / 2) (η2 / 2)) (1 / 2), by positivity, by
    have := min_le_right (min (η1 / 2) (η2 / 2)) (1 / 2 : ℝ); linarith, fun Φ hΦ0 hΦ1 => ?_⟩
  have hd1 : dist Φ 0 < η1 := by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hΦ0]
    have := (min_le_left (min (η1 / 2) (η2 / 2)) (1 / 2 : ℝ)).trans
      (min_le_left (η1 / 2) (η2 / 2))
    linarith
  have hd2 : dist Φ 0 < η2 := by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hΦ0]
    have := (min_le_left (min (η1 / 2) (η2 / 2)) (1 / 2 : ℝ)).trans
      (min_le_right (η1 / 2) (η2 / 2))
    linarith
  have k1 := h1 hd1
  have k2 := h2 hd2
  rw [e1, dist_zero_right] at k1
  rw [e2, dist_zero_right, Real.norm_eq_abs] at k2
  exact ⟨k1.le, k2.le⟩

/-- **Woodford (2003), pp. 414–415 (the deterministic date-0 optimal path of the exact model
exists and its inflation rate and output gap converge to zero).** Let `A ≠ 0`. There are
`Φ₀, δ > 0` such that for every distortion `0 ≤ Φ ≤ Φ₀` and initial dispersion
`|Δ_{−1} − 1| ≤ δ` there is a path `w_{t}` solving the first-order conditions of the date-0
Ramsey problem of the economy `(A/(1−Φ), Φ)` (no disturbances; zero initial multipliers), and
it converges geometrically to the zero-inflation steady state: `π_t → 0`, `ŷ_t → 0`,
`Δ_t → 1`. -/
theorem date0_path {p : Par} (hp : p.Std) {A : ℝ} (hA : A ≠ 0) :
    ∃ Φ0 > 0, ∃ δ > 0, ∀ Φ, 0 ≤ Φ → Φ ≤ Φ0 → ∀ Dm1, |Dm1 - 1| ≤ δ →
      ∃ w : ℕ → Fin 9 → ℝ,
        (ramseyQ p (RPhi A Φ) 0 (lagD0 Dm1) (w 0) + ramseyN p (w 1) = 0 ∧
          ∀ t, ramseyQ p (RPhi A Φ) 0 (w t) (w (t + 1)) + ramseyN p (w (t + 2)) = 0) ∧
        Tendsto w atTop (𝓝 (ramseySS p (RPhi A Φ))) ∧
        Tendsto (fun t => w t 1) atTop (𝓝 0) ∧ Tendsto (fun t => w t 0) atTop (𝓝 0) ∧
        Tendsto (fun t => w t 4) atTop (𝓝 1) := by
  obtain ⟨hz0, hz1, -, -, -⟩ := z_props hp
  set μ := (max p.α (z1 p) + 1) / 2 with hμ
  have hμα : p.α < μ := by rw [hμ]; have := le_max_left p.α (z1 p); linarith [hp.α_lt_one]
  have hμz : z1 p < μ := by rw [hμ]; have := le_max_right p.α (z1 p); linarith
  have hμ1 : μ < 1 := by rw [hμ]; have := max_lt hp.α_lt_one hz1; linarith
  have hμ0 : 0 < μ := lt_trans hp.α_pos hμα
  obtain ⟨r, hr, δ, hδ, C, hC, H⟩ := date0_converges_ss hp hA hμα hμz hμ1.le
  obtain ⟨Φ0, hΦ0, hΦ01, hsm⟩ := small_of_Phi p A hδ
  refine ⟨Φ0, hΦ0, δ, hδ, fun Φ hΦ0' hΦ1 Dm1 hDm1 => ?_⟩
  obtain ⟨hs1, hs2⟩ := hsm Φ hΦ0' hΦ1
  obtain ⟨w, hw, -, -, hconv⟩ := H Φ hΦ0' (by linarith) hs1 hs2 natTree Dm1 hDm1
  have hw' := (ramseyL_nat p (RPhi A Φ) (fun _ => 0) (lagD0 Dm1) w).1 hw
  have hlim : Tendsto w atTop (𝓝 (ramseySS p (RPhi A Φ))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hg : Tendsto (fun t : ℕ => C * (|ramseyLam p (RPhi A Φ) 0| + |Dm1 - 1|) * μ ^ t) atTop
        (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hμ0.le hμ1).const_mul
        (C * (|ramseyLam p (RPhi A Φ) 0| + |Dm1 - 1|))
    exact squeeze_zero (fun _ => norm_nonneg _) (fun t => hconv t) hg
  have hc : ∀ i : Fin 9, Tendsto (fun t => w t i) atTop (𝓝 (ramseySS p (RPhi A Φ) i)) :=
    fun i => (continuous_apply i).continuousAt.tendsto.comp hlim
  refine ⟨w, ⟨hw'.1, hw'.2⟩, hlim, ?_, ?_, ?_⟩
  · simpa [ramseySS] using hc 1
  · simpa [ramseySS] using hc 0
  · simpa [ramseySS] using hc 4

/-- Woodford (2003), §5: rescaling the multipliers of a solution of the conditions of the economy
`(A_u, Φ)` by `s` gives a solution of the conditions of `(sA_u, Φ)`. -/
theorem scale_solution (p : Par) (Au Φ s : ℝ) (e : Fin 5 → ℝ) (wm w wn : Fin 9 → ℝ)
    (h : ramseyQ p ⟨Au, Φ⟩ e wm w + ramseyN p wn = 0) :
    ramseyQ p ⟨s * Au, Φ⟩ e ![wm 0, wm 1, wm 2, wm 3, wm 4, s * wm 5, s * wm 6, s * wm 7, s * wm 8]
      ![w 0, w 1, w 2, w 3, w 4, s * w 5, s * w 6, s * w 7, s * w 8] +
      ramseyN p ![wn 0, wn 1, wn 2, wn 3, wn 4, s * wn 5, s * wn 6, s * wn 7, s * wn 8] = 0 := by
  rw [ramseyQ_scale, ramseyN_scale]
  funext i
  have := congrFun h i
  simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
  rw [← mul_add, this, mul_zero]

/-- **Woodford (2003), pp. 414–415, with the welfare weight `A_{u}` held fixed.** For every
`A_u ≠ 0` there are `Φ₀, δ > 0` such that for every `0 ≤ Φ ≤ Φ₀` and `|Δ_{−1} − 1| ≤ δ` the
first-order conditions of the date-0 Ramsey problem of the economy `(A_u, Φ)` (no disturbances,
zero initial multipliers) have a deterministic solution whose inflation rate and output gap
converge to zero and whose dispersion converges to one. -/
theorem date0_path_Au {p : Par} (hp : p.Std) {Au : ℝ} (hA : Au ≠ 0) :
    ∃ Φ0 > 0, ∃ δ > 0, ∀ Φ, 0 ≤ Φ → Φ ≤ Φ0 → ∀ Dm1, |Dm1 - 1| ≤ δ →
      ∃ w : ℕ → Fin 9 → ℝ,
        (ramseyQ p ⟨Au, Φ⟩ 0 (lagD0 Dm1) (w 0) + ramseyN p (w 1) = 0 ∧
          ∀ t, ramseyQ p ⟨Au, Φ⟩ 0 (w t) (w (t + 1)) + ramseyN p (w (t + 2)) = 0) ∧
        Tendsto (fun t => w t 1) atTop (𝓝 0) ∧ Tendsto (fun t => w t 0) atTop (𝓝 0) ∧
        Tendsto (fun t => w t 4) atTop (𝓝 1) := by
  obtain ⟨Φ0, hΦ0, δ, hδ, H⟩ := date0_path hp hA
  obtain ⟨Φ1, hΦ1, hΦ11, -⟩ := small_of_Phi p Au (δ := 1) one_pos
  refine ⟨min Φ0 Φ1, lt_min hΦ0 hΦ1, δ, hδ, fun Φ hΦa hΦb Dm1 hDm1 => ?_⟩
  have hΦlt : Φ < 1 := lt_of_le_of_lt (hΦb.trans (min_le_right _ _)) hΦ11
  obtain ⟨w, ⟨h0, ht⟩, -, hπ, hy, hD⟩ := H Φ hΦa (hΦb.trans (min_le_left _ _)) Dm1 hDm1
  set s := 1 - Φ with hs
  have hR : (⟨s * (Au / (1 - Φ)), Φ⟩ : RPar) = ⟨Au, Φ⟩ := by
    have : (1 : ℝ) - Φ ≠ 0 := by linarith
    rw [hs]; congr 1; field_simp
  set S : (Fin 9 → ℝ) → Fin 9 → ℝ :=
    fun v => ![v 0, v 1, v 2, v 3, v 4, s * v 5, s * v 6, s * v 7, s * v 8] with hS
  refine ⟨fun t => S (w t), ⟨?_, fun t => ?_⟩, ?_, ?_, ?_⟩
  · have h := scale_solution p (Au / (1 - Φ)) Φ s 0 (lagD0 Dm1) (w 0) (w 1) h0
    rw [hR] at h
    have hl : ![lagD0 Dm1 0, lagD0 Dm1 1, lagD0 Dm1 2, lagD0 Dm1 3, lagD0 Dm1 4,
        s * lagD0 Dm1 5, s * lagD0 Dm1 6, s * lagD0 Dm1 7, s * lagD0 Dm1 8] = lagD0 Dm1 := by
      funext i; fin_cases i <;> simp [lagD0]
    rw [hl] at h
    exact h
  · have h := scale_solution p (Au / (1 - Φ)) Φ s 0 (w t) (w (t + 1)) (w (t + 2)) (ht t)
    rw [hR] at h
    exact h
  · simpa [hS] using hπ
  · simpa [hS] using hy
  · simpa [hS] using hD

end Woodford.StabilizationWelfare.TidyR5RamseyDate0
