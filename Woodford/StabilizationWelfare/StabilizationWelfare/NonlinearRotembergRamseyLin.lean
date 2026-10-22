/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergRamsey

/-!
# The linearised Rotemberg Ramsey conditions: targeting rule, root condition, contrast with Calvo

Woodford (2003), *Interest and Prices*, Chapter 7, §1–2 ((1.17)–(1.20): the commitment system,
the targeting rule `π_t + (λ_x/κ)(x_t − x_{t−1}) = 0` and its root condition, pp. 475–476) and
Chapter 6, §5, applied to the exact Ramsey conditions of `NonlinearRotembergRamsey`.

## Main results

* `Qd`, `Nd` (the conditions in deviations from `w̄`), **`fderiv_Qd`, `fderiv_Nd`**: the exact
  derivatives at the steady state are `DQr`, `DNr`.
* **`commitment_system`**: with zero forcing, the linearisation is EXACTLY the commitment system
  `ĉ = ŷ`, `π = κŷ + βE π′`, and the targeting rule `ŷ_t − ŷ_{t−1} + θ_R π_t = 0` with the
  Rotemberg coefficient `θ_R = θm(ω + mσ)/G`, `G = 1 + ω − m(1 − σ)` (`thR`, `Gw`).
* **`ramsey_root_condition`**: `βz² − (1 + β + κθ_R)z + 1` has exactly one root inside and one
  outside the unit circle, for every admissible calibration and distortion.
* **`thR_eq_theta_iff`, `thR_lt_theta`** (the qualitative DIFFERENCE from Calvo): the Calvo
  targeting rule has coefficient `θ` for every `Φ` (`NonlinearNKMarkovRamseyLin.key_theta`); the
  Rotemberg coefficient equals `θ` iff `Φ = 0`, and is strictly smaller when `0 < Φ < 1`.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergRamseyLin

open Filter Topology
open NonlinearRotemberg NonlinearRotembergRamsey
open NonlinearNKMarkovRamseyLin (commit_roots hdlin)

variable {p : Par}

/-! ## The conditions in deviations -/

/-- Woodford (2003), Ch. 7: the current part of the Ramsey conditions in deviations
`(w₋ − w̄, w − w̄)` from the steady state. -/
noncomputable def Qd (p : Par) (q : (Fin 3 → ℝ) × (Fin 5 → ℝ) × (Fin 5 → ℝ)) : Fin 5 → ℝ :=
  Qr p q.1 (wbar p + q.2.1) (wbar p + q.2.2)

/-- Woodford (2003), Ch. 7: the lead part in deviations. -/
noncomputable def Nd (p : Par) (n : Fin 5 → ℝ) : Fin 5 → ℝ := Nr p (wbar p + n)

/-- The current part in deviations is `C^∞`. -/
theorem contDiff_Qd {n : WithTop ℕ∞} (p : Par) : ContDiff ℝ n (Qd p) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp only [Qd, Qr, xs, Gadj, GaP, HmY, HmC, RrY, RrP, Uc, Vy, Hmc, Rr,
    Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one,
    Fin.reduceFinMk, Matrix.cons_val, Pi.add_apply] <;> fun_prop

/-- The lead part in deviations is `C^∞`. -/
theorem contDiff_Nd {n : WithTop ℕ∞} (p : Par) : ContDiff ℝ n (Nd p) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp only [Nd, Nr, xs, Gadj, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
    Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val, Pi.add_apply] <;> fun_prop

/-- Woodford (2003), Ch. 7: the deviations vanish together at the steady state, for every `Φ`. -/
theorem Qd_Nd_zero (hp : p.Basic) : Qd p (0, 0, 0) + Nd p 0 = 0 := by
  have h := ramsey_steadyState hp
  simp only [Qd, Nd, add_zero]
  exact h

/-! ## The linearisation -/

/-- The linearisation of the current part at the steady state, in `(lag, current)` deviations. -/
noncomputable def DQr (p : Par) (um u : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![-(p.m * ((1 + p.ω) * u 0)) - (u 3 * (p.θ * p.m * p.ω) + lamb p * (p.θ * p.m *
      ((1 + p.ω) * ((1 + p.ω) * u 0) - (u 0 - p.σ * u 2)))) + (u 4 + gamb p * u 0),
    (u 3 - um 3) * p.ψ - gamb p * (p.ψ * u 1),
    (1 - p.σ) * u 2 - (u 3 * (p.θ * p.m * p.σ) + lamb p * (p.θ * p.m * p.σ * (u 0 - p.σ * u 2))) -
      (u 4 + gamb p * u 2),
    p.ψ * u 1 - p.θ * p.m * (p.ω * u 0 + p.σ * u 2),
    u 0 - u 2]

/-- The linearisation of the lead part at the steady state. -/
noncomputable def DNr (p : Par) (n : Fin 5 → ℝ) : Fin 5 → ℝ := ![0, 0, 0, -(p.β * (p.ψ * n 1)), 0]

/-- The allocation coordinates along the line `w̄ + t·u`. -/
theorem xs_line (u : Fin 5 → ℝ) (t : ℝ) : xs (wbar p + t • u) = t • xs u := by
  funext i; fin_cases i <;> simp [xs, wbar]

/-- The multiplier coordinates along the line `w̄ + t·u`. -/
theorem wline (u : Fin 5 → ℝ) (t : ℝ) :
    (wbar p + t • u) 2 = t * u 2 ∧ (wbar p + t • u) 3 = lamb p + t * u 3 ∧
      (wbar p + t • u) 4 = gamb p + t * u 4 := by
  simp [wbar]

/-- `t ↦ a·e^{tc}` has derivative `ac` at `0`. -/
theorem hde (a c : ℝ) : HasDerivAt (fun t : ℝ => a * Real.exp (t * c)) (a * c) 0 := by
  have h := hd_exp a c 0 0
  simp only [zero_mul, add_zero, Real.exp_zero, mul_one] at h
  exact h

/-- Derivatives along `t ↦ t·v` at `0` of the functions entering the Ramsey conditions. -/
theorem hd_G (v : Fin 3 → ℝ) : HasDerivAt (fun t : ℝ => Gadj p (t • v)) (p.ψ * v 1) 0 := by
  have h := (hde p.ψ (v 0 - p.σ * v 2 + 2 * v 1)).sub (hde p.ψ (v 0 - p.σ * v 2 + v 1))
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [Gadj_eq, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  ring_nf

/-- Derivative of `G_π` along the line. -/
theorem hd_GaP (v : Fin 3 → ℝ) :
    HasDerivAt (fun t : ℝ => GaP p (t • v)) (p.ψ * (v 0 - p.σ * v 2 + 3 * v 1)) 0 := by
  have h := (hde (2 * p.ψ) (v 0 - p.σ * v 2 + 2 * v 1)).sub (hde p.ψ (v 0 - p.σ * v 2 + v 1))
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [GaP, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  ring_nf

/-- Derivative of `H_y` along the line. -/
theorem hd_HmY (v : Fin 3 → ℝ) :
    HasDerivAt (fun t : ℝ => HmY p 0 (t • v))
      (p.θ * p.m * ((1 + p.ω) * ((1 + p.ω) * v 0) - (v 0 - p.σ * v 2))) 0 := by
  have h := (hde (p.θ * p.m * (1 + p.ω)) ((1 + p.ω) * v 0)).sub
    (hde (p.θ * p.m) (v 0 - p.σ * v 2))
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [HmY, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.zero_apply]
  ring_nf

/-- Derivative of `H_c` along the line. -/
theorem hd_HmC (v : Fin 3 → ℝ) :
    HasDerivAt (fun t : ℝ => HmC p (t • v)) (p.θ * p.m * p.σ * (v 0 - p.σ * v 2)) 0 := by
  have h := hde (p.θ * p.m * p.σ) (v 0 - p.σ * v 2)
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [HmC, Pi.smul_apply, smul_eq_mul]
  ring_nf

/-- Derivative of `H` along the line. -/
theorem hd_Hmc (v : Fin 3 → ℝ) :
    HasDerivAt (fun t : ℝ => Hmc p 0 (t • v)) (p.θ * p.m * (p.ω * v 0 + p.σ * v 2)) 0 := by
  have h := (hde (p.θ * p.m) ((1 + p.ω) * v 0)).sub (hde (p.θ * p.m) (v 0 - p.σ * v 2))
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [Hmc, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.zero_apply]
  ring_nf

/-- Derivative of `R_y` along the line. -/
theorem hd_RrY (v : Fin 3 → ℝ) : HasDerivAt (fun t : ℝ => RrY p (t • v)) (v 0) 0 := by
  have h3 := (((hde 1 (v 1)).sub_const 1).pow 2).const_mul (p.ψ / 2) |>.const_sub 1
  have h := (hde 1 (v 0)).mul h3
  refine (h.congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [RrY, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.pow_apply, one_mul]

/-- Derivative of `R_π` along the line. -/
theorem hd_RrP (v : Fin 3 → ℝ) : HasDerivAt (fun t : ℝ => RrP p (t • v)) (-(p.ψ * v 1)) 0 := by
  have h := (((hde 1 (v 0)).mul (((hde 1 (v 1)).sub_const 1).const_mul p.ψ)).mul
    (hde 1 (v 1))).neg
  refine (h.congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [RrP, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.neg_apply, one_mul]
  ring_nf

/-- Derivative of `R` along the line. -/
theorem hd_Rr (v : Fin 3 → ℝ) : HasDerivAt (fun t : ℝ => Rr p (t • v)) (v 0 - v 2) 0 := by
  have h3 := (((hde 1 (v 1)).sub_const 1).pow 2).const_mul (p.ψ / 2) |>.const_sub 1
  have h := ((hde 1 (v 0)).mul h3).sub (hde 1 (v 2))
  refine (h.congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [Rr, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, one_mul]

/-- Derivative of `u′` along the line. -/
theorem hd_Uc (v : Fin 3 → ℝ) : HasDerivAt (fun t : ℝ => Uc p (t • v)) ((1 - p.σ) * v 2) 0 := by
  have h := hde 1 ((1 - p.σ) * v 2)
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [Uc, Pi.smul_apply, smul_eq_mul, one_mul]
  ring_nf

/-- Derivative of `v′` along the line. -/
theorem hd_Vy (v : Fin 3 → ℝ) :
    HasDerivAt (fun t : ℝ => Vy p 0 (t • v)) (p.m * ((1 + p.ω) * v 0)) 0 := by
  have h := hde p.m ((1 + p.ω) * v 0)
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [Vy, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  ring_nf

/-- Woodford (2003), Ch. 7: the derivative of the current part along `t ↦ (0, t·um, t·u)` at the
steady state is `DQr um u`. -/
theorem hasDerivAt_Qd_line (um u : Fin 5 → ℝ) (i : Fin 5) :
    HasDerivAt (fun t : ℝ => Qd p (0, t • um, t • u) i) (DQr p um u i) 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := ss_vals (p := p)
  have hl3 := hdlin (lamb p) (u 3)
  have hm3 := hdlin (lamb p) (um 3)
  have hl4 := hdlin (gamb p) (u 4)
  have e3 : ∀ t : ℝ, (wbar p + t • u) 3 = lamb p + t * u 3 := fun t => (wline u t).2.1
  have e3m : ∀ t : ℝ, (wbar p + t • um) 3 = lamb p + t * um 3 := fun t => (wline um t).2.1
  have e4 : ∀ t : ℝ, (wbar p + t • u) 4 = gamb p + t * u 4 := fun t => (wline u t).2.2
  have e2 : ∀ t : ℝ, (wbar p + t • u) 2 = t * u 2 := fun t => (wline u t).1
  fin_cases i
  · have h := (((hd_Vy (p := p) (xs u)).neg.add ((hl3.sub hm3).mul (hd_G (p := p) (xs u)))).sub
      (hl3.mul (hd_HmY (p := p) (xs u)))).add (hl4.mul (hd_RrY (p := p) (xs u)))
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    · simp only [Pi.sub_apply, zero_smul, zero_mul,
        mul_zero, add_zero, sub_self, h1, h3, h5, DQr, xs,
        Fin.zero_eta, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val]
      ring
    · simp only [Qd, Qr, xs_line, e3, e3m, e4, Fin.zero_eta, Matrix.cons_val_zero, Pi.add_apply,
        Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]
  · have h := ((hl3.sub hm3).mul (hd_GaP (p := p) (xs u))).add (hl4.mul (hd_RrP (p := p) (xs u)))
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    · simp only [Pi.sub_apply, zero_smul, zero_mul,
        mul_zero, add_zero, sub_self, h2, h6, DQr, xs,
        Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val]
      ring
    · simp only [Qd, Qr, xs_line, e3, e3m, e4, Fin.mk_one, Matrix.cons_val_one,
        Matrix.cons_val_zero, Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
  · have hE : HasDerivAt (fun t : ℝ => Real.exp (t * u 2)) (u 2) 0 := by
      simpa using hde 1 (u 2)
    have h := ((((hd_Uc (p := p) (xs u)).add ((hl3.sub hm3).mul ((hd_G (p := p) (xs u)).const_mul
      p.σ).neg)).sub (hl3.mul (hd_HmC (p := p) (xs u)))).add (hl4.mul hE.neg))
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    · simp only [Pi.sub_apply, Pi.neg_apply, zero_smul, zero_mul,
        mul_zero, add_zero, sub_self, h1, h4, DQr, xs, Real.exp_zero,
        Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val]
      ring
    · simp only [Qd, Qr, xs_line, e2, e3, e3m, e4, Fin.reduceFinMk, Matrix.cons_val,
        Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]
  · have h := (hd_G (p := p) (xs u)).sub (hd_Hmc (p := p) (xs u))
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    · simp only [DQr, xs, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val]
    · simp only [Qd, Qr, xs_line, Fin.reduceFinMk, Matrix.cons_val, Pi.sub_apply]
  · have h := hd_Rr (p := p) (xs u)
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    · simp only [DQr, xs, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val]
    · simp only [Qd, Qr, xs_line, Fin.reduceFinMk, Matrix.cons_val]

/-- Woodford (2003), Ch. 7: the derivative of the lead part along `t ↦ t·n` at `0` is `DNr n`. -/
theorem hasDerivAt_Nd_line (n : Fin 5 → ℝ) (i : Fin 5) :
    HasDerivAt (fun t : ℝ => Nd p (t • n) i) (DNr p n i) 0 := by
  fin_cases i
  · simp only [Nd, Nr, DNr, Fin.zero_eta, Matrix.cons_val_zero]; exact hasDerivAt_const _ _
  · simp only [Nd, Nr, DNr, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact hasDerivAt_const _ _
  · simp only [Nd, Nr, DNr, Fin.reduceFinMk, Matrix.cons_val]; exact hasDerivAt_const _ _
  · have h := (hd_G (p := p) (xs n)).const_mul p.β |>.neg
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    · simp only [DNr, xs, Fin.reduceFinMk, Matrix.cons_val, Matrix.cons_val_one,
        Matrix.cons_val_zero]
    · simp only [Nd, Nr, xs_line, Fin.reduceFinMk, Matrix.cons_val, Pi.neg_apply]
  · simp only [Nd, Nr, DNr, Fin.reduceFinMk, Matrix.cons_val]; exact hasDerivAt_const _ _

/-- Woodford (2003), Ch. 7 (**the exact derivative of the current part**): `DQ(0)(0, um, u) =
DQr um u`. -/
theorem fderiv_Qd (um u : Fin 5 → ℝ) : fderiv ℝ (Qd p) 0 (0, um, u) = DQr p um u := by
  have hd : HasFDerivAt (Qd p) (fderiv ℝ (Qd p) 0) 0 :=
    ((contDiff_Qd (n := 1) p).differentiable one_ne_zero 0).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => ((0 : Fin 3 → ℝ), t • um, t • u))
      ((0 : Fin 3 → ℝ), um, u) 0 := by
    have := (hasDerivAt_const (0 : ℝ) (0 : Fin 3 → ℝ)).prodMk
      (((hasDerivAt_id (0 : ℝ)).smul_const um).prodMk ((hasDerivAt_id (0 : ℝ)).smul_const u))
    simpa using this
  have hc := hd.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp; rfl)
  exact hc.unique (hasDerivAt_pi.2 fun i => hasDerivAt_Qd_line um u i)

/-- Woodford (2003), Ch. 7 (**the exact derivative of the lead part**): `DN(0) n = DNr n`. -/
theorem fderiv_Nd (n : Fin 5 → ℝ) : fderiv ℝ (Nd p) 0 n = DNr p n := by
  have hd : HasFDerivAt (Nd p) (fderiv ℝ (Nd p) 0) 0 :=
    ((contDiff_Nd (n := 1) p).differentiable one_ne_zero 0).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => t • n) n 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const n
  have hc := hd.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  exact hc.unique (hasDerivAt_pi.2 fun i => hasDerivAt_Nd_line n i)

/-! ## The commitment system and the targeting rule -/

/-- Woodford (2003), Ch. 7: `G = 1 + ω − m(1 − σ) = σ + ω + Φ(1 − σ)`, the coefficient of output
in the combined first-order conditions (the same `G` as in the Calvo model,
`NonlinearNKMarkovRamseyLin.Gw`). -/
def Gw (p : Par) : ℝ := 1 + p.ω - p.m * (1 - p.σ)

/-- Woodford (2003), Ch. 7 with Rotemberg pricing (**the targeting-rule coefficient**):
`θ_R = θm(ω + mσ)/G`. -/
noncomputable def thR (p : Par) : ℝ := p.θ * p.m * (p.ω + p.m * p.σ) / Gw p

/-- `G > 0` whenever `0 < m ≤ 1` (a nonnegative distortion `Φ`). -/
theorem Gw_pos (hp : p.Basic) (hm1 : p.m ≤ 1) : 0 < Gw p := by
  unfold Gw
  have := hp.ω_nonneg; have := hp.σ_pos; have := hp.m_pos
  rcases le_or_gt p.σ 1 with h | h
  · nlinarith
  · nlinarith

/-- `λ̄θm(σ + ω) = 1 − m`. -/
theorem lamb_mul (hp : p.Basic) : lamb p * (p.θ * p.m * (p.σ + p.ω)) = 1 - p.m := by
  have hθ : p.θ ≠ 0 := by linarith [hp.one_lt_θ]
  have hm : p.m ≠ 0 := hp.m_pos.ne'
  have hs : p.σ + p.ω ≠ 0 := by linarith [hp.σ_pos, hp.ω_nonneg]
  unfold lamb; field_simp

/-- `γ̄(σ + ω) = ω + mσ`. -/
theorem gamb_mul (hp : p.Basic) : gamb p * (p.σ + p.ω) = p.ω + p.m * p.σ := by
  have hs : p.σ + p.ω ≠ 0 := by linarith [hp.σ_pos, hp.ω_nonneg]
  unfold gamb; field_simp

/-- Woodford (2003), Ch. 7 (**the combined output and consumption conditions**): the sum of the
first and third linearised conditions is `−G ĉ − θm(σ+ω)λ̂ + c(ŷ − ĉ)` with
`c = −m(1+ω) − λ̄θm(ω² + 2ω + σ) + γ̄`. -/
theorem red_lam (hp : p.Basic) (um u : Fin 5 → ℝ) :
    DQr p um u 0 + DQr p um u 2 = -(Gw p * u 2) - p.θ * p.m * (p.σ + p.ω) * u 3 +
      (-(p.m * (1 + p.ω)) - lamb p * (p.θ * p.m * (p.ω ^ 2 + 2 * p.ω + p.σ)) + gamb p) *
        (u 0 - u 2) := by
  have hl := lamb_mul hp
  have hg := gamb_mul hp
  have hs : p.σ + p.ω ≠ 0 := by linarith [hp.σ_pos, hp.ω_nonneg]
  simp only [DQr, Gw, Matrix.cons_val_zero, Matrix.cons_val]
  have e : lamb p * (p.θ * p.m) * (p.ω ^ 2 + 2 * p.ω + 2 * p.σ - p.σ ^ 2) =
      (1 - p.m) * (2 + p.ω - p.σ) := by
    have : lamb p * (p.θ * p.m) * (p.σ + p.ω) = 1 - p.m := by linarith
    have h2 : p.ω ^ 2 + 2 * p.ω + 2 * p.σ - p.σ ^ 2 = (p.σ + p.ω) * (2 + p.ω - p.σ) := by ring
    rw [h2, ← mul_assoc, this]
  linear_combination (-(u 2)) * e

/-- Woodford (2003), Ch. 7, (1.17)–(1.20) with Rotemberg pricing (**THE LINEARISED RAMSEY
CONDITIONS ARE THE COMMITMENT SYSTEM**): if the linearised conditions hold with zero forcing
(`DQr um u + DNr n = 0`, `n` the expected lead) and the previous date's combined condition holds
(`G ĉ₋ + θm(σ+ω)λ̂₋ = 0`), then `ŷ = ĉ`, the NKPC `π = κŷ + βE π′`, the combined condition
`G ĉ + θm(σ+ω)λ̂ = 0`, and the targeting rule `G(ĉ − ĉ₋) + θm(ω + mσ)π = 0`. -/
theorem commitment_system (hp : p.Basic) (um u n : Fin 5 → ℝ) (h : DQr p um u + DNr p n = 0)
    (hm : Gw p * um 2 + p.θ * p.m * (p.σ + p.ω) * um 3 = 0) :
    u 0 = u 2 ∧ u 1 = p.κ * u 0 + p.β * n 1 ∧
      Gw p * u 2 + p.θ * p.m * (p.σ + p.ω) * u 3 = 0 ∧
      Gw p * (u 2 - um 2) + p.θ * p.m * (p.ω + p.m * p.σ) * u 1 = 0 := by
  have c : ∀ i, DQr p um u i + DNr p n i = 0 := fun i => by
    have := congrFun h i; simpa using this
  have c0 := c 0
  have c1 := c 1
  have c2 := c 2
  have c3 := c 3
  have c4 := c 4
  simp only [DNr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    add_zero] at c0 c1 c2 c3 c4
  have e4 : u 0 = u 2 := by
    simp only [DQr, Matrix.cons_val] at c4; linarith
  have hl := red_lam hp um u
  rw [e4, sub_self, mul_zero, add_zero] at hl
  have e02 : Gw p * u 2 + p.θ * p.m * (p.σ + p.ω) * u 3 = 0 := by linarith
  have hψ := hp.ψ_pos
  have hk := hp.κ_mul
  have e3 : u 1 = p.κ * u 0 + p.β * n 1 := by
    simp only [DQr, Matrix.cons_val] at c3
    have : p.ψ * (u 1 - p.κ * u 0 - p.β * n 1) = 0 := by
      rw [← e4] at c3
      linear_combination c3 - u 0 * hk
    have := (mul_eq_zero.1 this).resolve_left hψ.ne'
    linarith
  have e1 : u 3 - um 3 = gamb p * u 1 := by
    simp only [DQr, Matrix.cons_val_one, Matrix.cons_val_zero] at c1
    have : p.ψ * (u 3 - um 3 - gamb p * u 1) = 0 := by linear_combination c1
    have := (mul_eq_zero.1 this).resolve_left hψ.ne'
    linarith
  refine ⟨e4, e3, e02, ?_⟩
  have hg := gamb_mul hp
  linear_combination e02 - hm - p.θ * p.m * (p.σ + p.ω) * e1 - p.θ * p.m * u 1 * hg

/-- Woodford (2003), Ch. 7 (**the Rotemberg targeting rule**): under `commitment_system`, if
`G ≠ 0` then `ĉ_t − ĉ_{t−1} + θ_R π_t = 0`. -/
theorem targeting_rule (hp : p.Basic) (hG : Gw p ≠ 0) (um u n : Fin 5 → ℝ)
    (h : DQr p um u + DNr p n = 0)
    (hm : Gw p * um 2 + p.θ * p.m * (p.σ + p.ω) * um 3 = 0) :
    u 2 - um 2 + thR p * u 1 = 0 := by
  obtain ⟨-, -, -, h4⟩ := commitment_system hp um u n h hm
  unfold thR
  field_simp
  linear_combination h4

/-- Woodford (2003), Ch. 7, (1.20), pp. 475–476, Rotemberg pricing (**the root condition**): with
`G > 0`, `βz² − (1 + β + κθ_R)z + 1` has two real roots `0 < z₁ < 1 < z₂` with `βz₁z₂ = 1`,
`β(z₁ + z₂) = 1 + β + κθ_R`, and no others: one stable root (inherited inertia) and one unstable
root (determinacy of the commitment equilibrium). -/
theorem ramsey_root_condition (hp : p.Basic) (hG : 0 < Gw p) :
    ∃ z1 z2 : ℝ, 0 < z1 ∧ z1 < 1 ∧ 1 < z2 ∧ p.β * z1 * z2 = 1 ∧
      p.β * (z1 + z2) = 1 + p.β + p.κ * thR p ∧
      (∀ z : ℝ, p.β * z ^ 2 - (1 + p.β + p.κ * thR p) * z + 1 = 0 ↔ z = z1 ∨ z = z2) := by
  have hθ : 0 < p.θ := by linarith [hp.one_lt_θ]
  have hR : 0 < thR p := by
    unfold thR
    have := hp.m_pos; have := hp.σ_pos; have := hp.ω_nonneg
    positivity
  exact commit_roots hp.β_pos hp.β_lt_one (mul_pos hp.κ_pos hR)

/-! ## The difference from Calvo -/

/-- Woodford (2003), Ch. 7 (**the Rotemberg targeting coefficient equals Calvo's `θ` iff the steady
state is efficient**): with `G > 0`, `θ_R = θ ⟺ m = 1 ⟺ Φ = 0`. In the Calvo model the coefficient
is `θ` for EVERY `Φ` (`NonlinearNKMarkovRamseyLin.key_theta`), so for a distorted steady state the
optimal targeting rules of the two models differ even when their NKPC slopes coincide. -/
theorem thR_eq_theta_iff (hp : p.Basic) (hG : 0 < Gw p) : thR p = p.θ ↔ p.m = 1 := by
  have hθ : 0 < p.θ := by linarith [hp.one_lt_θ]
  have hpos : 0 < p.ω + p.m * p.σ + 1 := by
    have := hp.m_pos; have := hp.σ_pos; have := hp.ω_nonneg; positivity
  unfold thR
  rw [div_eq_iff hG.ne']
  unfold Gw
  constructor
  · intro h
    have : p.θ * ((p.m - 1) * (p.ω + p.m * p.σ + 1)) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 hθ.ne'
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · linarith
      · exact absurd h2 hpos.ne'
  · intro h; rw [h]; ring

/-- Woodford (2003), Ch. 7 (**with a positive distortion the Rotemberg planner puts LESS weight on
inflation in the targeting rule than the Calvo planner**): for `0 < m < 1` (`0 < Φ < 1`),
`θ_R < θ`. -/
theorem thR_lt_theta (hp : p.Basic) (hm1 : p.m < 1) : thR p < p.θ := by
  have hG := Gw_pos hp hm1.le
  have hθ : 0 < p.θ := by linarith [hp.one_lt_θ]
  unfold thR
  rw [div_lt_iff₀ hG]
  unfold Gw
  have : 0 < p.θ * ((1 - p.m) * (p.ω + p.m * p.σ + 1)) := by
    have := hp.m_pos; have := hp.σ_pos; have := hp.ω_nonneg
    have : 0 < 1 - p.m := by linarith
    positivity
  nlinarith

end Woodford.StabilizationWelfare.NonlinearRotembergRamseyLin
