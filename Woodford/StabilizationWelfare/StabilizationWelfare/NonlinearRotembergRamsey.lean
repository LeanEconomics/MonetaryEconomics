/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotemberg
import StabilizationWelfare.NonlinearNKMarkovRamseyLin

/-!
# The timeless Ramsey policy of the exact Rotemberg model

Woodford (2003), *Interest and Prices*, Chapter 6, §5 and Chapter 7, §1–2 (optimal policy from a
timeless perspective, the Lagrangian with the lagged multiplier on the forward-looking pricing
condition), with Rotemberg (1982) pricing (Ch. 3, fn. 44).

The planner maximises `E ∑ βᵗ [u(C_t) − v(Y_t)]` subject to the exact pricing condition
`G(x_t) − H(e_t, x_t) − βE_tG(x_{t+1}) = 0` (`NonlinearRotemberg.Gadj`, `NonlinearRotemberg.Hmc`)
and the resource constraint `R(x_t) = e^{ŷ}(1 − (ψ/2)(e^π − 1)²) − e^{ĉ} = 0` (`Rr`); the interest
rate is free, so the Euler equation is not a constraint. With `λ` the multiplier on the pricing
condition and `γ` on the resource constraint, the date-`t` part of the timeless Lagrangian is
`u(ĉ) − v(ŷ) + λ_t(G − H) − λ_{t−1}G + γ_t R` (`lagr`); normalisation `u′(ĉ) = e^{(1−σ)ĉ}`,
`v′(ŷ) = m e^{(1+ω)(ŷ−a)}` (`Ȳ^{1−σ} = 1`).

## Main results

* `Qr`, `Nr`: the five exact conditions (three first-order conditions and the two constraints)
  `Q(e_t, w_{t−1}, w_t) + E_tN(w_{t+1}) = 0`, `w = (ŷ, π, ĉ, λ, γ)`; **`lagr_deriv_y`,
  `lagr_deriv_pi`, `lagr_deriv_c`**: the first-order conditions ARE the partial derivatives of
  the Lagrangian (derived, not assumed).
* **`ramsey_steadyState`**: for EVERY distortion `Φ = 1 − m`, zero inflation with
  `λ̄ = Φ/(θm(σ+ω))`, `γ̄ = (ω + mσ)/(σ + ω)` is a steady state of the Ramsey conditions.
* **`ramsey_ss_char`**: every Ramsey steady state either IS this zero-inflation steady state, or
  has `γ = 0` and strictly NEGATIVE inflation; in particular no Ramsey steady state has positive
  inflation, for any `Φ` — the timeless optimal steady-state inflation is zero, as in Calvo.
* **`golden_rule_inflation`**: by contrast the steady state maximising steady-state welfare
  (`Qgold`, the same conditions with the promise `λ_{t−1}` replaced by `βλ`) can have zero
  inflation ONLY if `Φ = 0`.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergRamsey

open Filter Topology
open NonlinearRotemberg

variable {p : Par}

/-! ## The Ramsey conditions -/

/-- Woodford (2003), Ch. 7: the steady-state multiplier on the pricing condition,
`λ̄ = (1 − m)/(θm(σ + ω)) = Φ/(θm(σ + ω))`. -/
noncomputable def lamb (p : Par) : ℝ := (1 - p.m) / (p.θ * p.m * (p.σ + p.ω))

/-- Woodford (2003), Ch. 7: the steady-state multiplier on the resource constraint,
`γ̄ = (ω + mσ)/(σ + ω)`. -/
noncomputable def gamb (p : Par) : ℝ := (p.ω + p.m * p.σ) / (p.σ + p.ω)

/-- The first three coordinates `x = (ŷ, π, ĉ)` of `w = (ŷ, π, ĉ, λ, γ)`. -/
def xs (w : Fin 5 → ℝ) : Fin 3 → ℝ := ![w 0, w 1, w 2]

/-- `∂G/∂π`. -/
noncomputable def GaP (p : Par) (x : Fin 3 → ℝ) : ℝ :=
  p.ψ * (2 * Real.exp (x 0 - p.σ * x 2 + 2 * x 1) - Real.exp (x 0 - p.σ * x 2 + x 1))

/-- `∂H/∂ŷ`. -/
noncomputable def HmY (p : Par) (e x : Fin 3 → ℝ) : ℝ :=
  p.θ * p.m * ((1 + p.ω) * Real.exp ((1 + p.ω) * x 0 + e 2 - (1 + p.ω) * e 1) -
    Real.exp (x 0 - p.σ * x 2))

/-- `∂H/∂ĉ`. -/
noncomputable def HmC (p : Par) (x : Fin 3 → ℝ) : ℝ := p.θ * p.m * p.σ * Real.exp (x 0 - p.σ * x 2)

/-- Rotemberg (1982) (**the resource constraint**): `R(x) = e^{ŷ}(1 − (ψ/2)(e^π − 1)²) − e^{ĉ}`. -/
noncomputable def Rr (p : Par) (x : Fin 3 → ℝ) : ℝ :=
  Real.exp (x 0) * (1 - p.ψ / 2 * (Real.exp (x 1) - 1) ^ 2) - Real.exp (x 2)

/-- `∂R/∂ŷ`. -/
noncomputable def RrY (p : Par) (x : Fin 3 → ℝ) : ℝ :=
  Real.exp (x 0) * (1 - p.ψ / 2 * (Real.exp (x 1) - 1) ^ 2)

/-- `∂R/∂π`. -/
noncomputable def RrP (p : Par) (x : Fin 3 → ℝ) : ℝ :=
  -(Real.exp (x 0) * (p.ψ * (Real.exp (x 1) - 1) * Real.exp (x 1)))

/-- Marginal utility `u′(ĉ) = e^{(1−σ)ĉ}`. -/
noncomputable def Uc (p : Par) (x : Fin 3 → ℝ) : ℝ := Real.exp ((1 - p.σ) * x 2)

/-- Marginal disutility `v′(ŷ) = m e^{(1+ω)(ŷ − a)}`. -/
noncomputable def Vy (p : Par) (e x : Fin 3 → ℝ) : ℝ := p.m * Real.exp ((1 + p.ω) * (x 0 - e 1))

/-- Woodford (2003), Ch. 7 with Rotemberg pricing (**the exact Ramsey conditions, current
part**): with `x = (ŷ, π, ĉ)`, `λ = w₃`, `γ = w₄`, `λ₋ = wm₃`:
* `ŷ`: `−v′ + (λ − λ₋)G − λH_y + γR_y`;
* `π`: `(λ − λ₋)G_π + γR_π`;
* `ĉ`: `u′ − σ(λ − λ₋)G − λH_c − γe^{ĉ}`;
* the pricing condition `G − H` (lead `−βG′` in `Nr`); the resource constraint `R`. -/
noncomputable def Qr (p : Par) (e : Fin 3 → ℝ) (wm w : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![-Vy p e (xs w) + (w 3 - wm 3) * Gadj p (xs w) - w 3 * HmY p e (xs w) + w 4 * RrY p (xs w),
    (w 3 - wm 3) * GaP p (xs w) + w 4 * RrP p (xs w),
    Uc p (xs w) + (w 3 - wm 3) * (-(p.σ * Gadj p (xs w))) - w 3 * HmC p (xs w) +
      w 4 * (-Real.exp (w 2)),
    Gadj p (xs w) - Hmc p e (xs w),
    Rr p (xs w)]

/-- Woodford (2003), Ch. 7 (**the part inside `E_t`**): the lead `−βG(x′)` of the pricing
condition. -/
noncomputable def Nr (p : Par) (w : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![0, 0, 0, -(p.β * Gadj p (xs w)), 0]

/-! ## The first-order conditions are derived from the Lagrangian -/

/-- The utility of consumption, normalised so that `u′(ĉ) = e^{(1−σ)ĉ}` (log utility at
`σ = 1`). -/
noncomputable def Uf (p : Par) (c : ℝ) : ℝ :=
  if p.σ = 1 then c else (Real.exp ((1 - p.σ) * c) - 1) / (1 - p.σ)

/-- The disutility of output, normalised so that `v′(ŷ) = m e^{(1+ω)(ŷ − a)}`. -/
noncomputable def Vf (p : Par) (e : Fin 3 → ℝ) (y : ℝ) : ℝ :=
  p.m * (Real.exp ((1 + p.ω) * (y - e 1)) - 1) / (1 + p.ω)

/-- Woodford (2003), Ch. 7 (**the date-`t` part of the timeless Lagrangian**):
`u(ĉ) − v(ŷ) + λ(G − H) − λ₋G + γR`. -/
noncomputable def lagr (p : Par) (e : Fin 3 → ℝ) (lm l g : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  Uf p (x 2) - Vf p e (x 0) + l * (Gadj p x - Hmc p e x) - lm * Gadj p x + g * Rr p x

/-- `t ↦ a·e^{tc + d}` has derivative `a·c·e^{t₀c + d}` at `t₀`. -/
theorem hd_exp (a c d t0 : ℝ) :
    HasDerivAt (fun t : ℝ => a * Real.exp (t * c + d)) (a * (c * Real.exp (t0 * c + d))) t0 := by
  have h := ((((hasDerivAt_id t0).mul_const c).add_const d).exp).const_mul a
  refine h.congr_deriv ?_
  simp only [id, one_mul]; ring

/-- Woodford (2003), Ch. 7 (**the output first-order condition is derived**): the derivative of
the Lagrangian in `ŷ` is the first Ramsey condition. -/
theorem lagr_deriv_y (hω : 1 + p.ω ≠ 0) (e : Fin 3 → ℝ) (wm w : Fin 5 → ℝ) :
    HasDerivAt (fun y => lagr p e (wm 3) (w 3) (w 4) ![y, w 1, w 2]) (Qr p e wm w 0) (w 0) := by
  have hG : HasDerivAt (fun y => Gadj p ![y, w 1, w 2]) (Gadj p (xs w)) (w 0) := by
    have h := (hd_exp p.ψ 1 (-(p.σ * w 2) + 2 * w 1) (w 0)).sub
      (hd_exp p.ψ 1 (-(p.σ * w 2) + w 1) (w 0))
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    · simp only [Gadj_eq, xs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      ring_nf
    · simp only [Gadj_eq, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val]
      ring_nf
  have hH : HasDerivAt (fun y => Hmc p e ![y, w 1, w 2]) (HmY p e (xs w)) (w 0) := by
    have h := (hd_exp (p.θ * p.m) (1 + p.ω) (e 2 - (1 + p.ω) * e 1) (w 0)).sub
      (hd_exp (p.θ * p.m) 1 (-(p.σ * w 2)) (w 0))
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    · simp only [HmY, xs, Matrix.cons_val_zero, Matrix.cons_val]
      ring_nf
    · simp only [Hmc, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val]
      ring_nf
  have hR : HasDerivAt (fun y => Rr p ![y, w 1, w 2]) (RrY p (xs w)) (w 0) := by
    have h := (hd_exp (1 - p.ψ / 2 * (Real.exp (w 1) - 1) ^ 2) 1 0 (w 0)).sub_const
      (Real.exp (w 2))
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    · simp only [RrY, xs, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring_nf
    · simp only [Rr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      ring_nf
  have hV : HasDerivAt (fun y => Vf p e y) (Vy p e (xs w)) (w 0) := by
    have h := (hd_exp (p.m / (1 + p.ω)) (1 + p.ω) (-((1 + p.ω) * e 1)) (w 0)).sub_const
      (p.m / (1 + p.ω))
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    · simp only [Vy, xs, Matrix.cons_val_zero]
      field_simp
      ring_nf
    · simp only [Vf]
      field_simp
      ring_nf
  have h := (((hasDerivAt_const (w 0) (Uf p (w 2))).sub hV).add (hG.sub hH |>.const_mul (w 3))).sub
    (hG.const_mul (wm 3)) |>.add (hR.const_mul (w 4))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  · simp only [Qr, Matrix.cons_val_zero]; ring
  · simp only [lagr, Matrix.cons_val_zero, Matrix.cons_val, Pi.add_apply, Pi.sub_apply]

/-- Woodford (2003), Ch. 7 (**the inflation first-order condition is derived**): the derivative of
the Lagrangian in `π` is the second Ramsey condition. -/
theorem lagr_deriv_pi (e : Fin 3 → ℝ) (wm w : Fin 5 → ℝ) :
    HasDerivAt (fun π => lagr p e (wm 3) (w 3) (w 4) ![w 0, π, w 2]) (Qr p e wm w 1) (w 1) := by
  have hG : HasDerivAt (fun π => Gadj p ![w 0, π, w 2]) (GaP p (xs w)) (w 1) := by
    have h := (hd_exp p.ψ 2 (w 0 - p.σ * w 2) (w 1)).sub
      (hd_exp p.ψ 1 (w 0 - p.σ * w 2) (w 1))
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    · simp only [GaP, xs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      ring_nf
    · simp only [Gadj_eq, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val]
      ring_nf
  have hR : HasDerivAt (fun π => Rr p ![w 0, π, w 2]) (RrP p (xs w)) (w 1) := by
    have h := (((((Real.hasDerivAt_exp (w 1)).sub_const 1).pow 2).const_mul (p.ψ / 2)).const_sub
      1).const_mul (Real.exp (w 0)) |>.sub_const (Real.exp (w 2))
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    · simp only [RrP, xs, Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast; ring
    · simp only [Rr, Pi.pow_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  have hH : HasDerivAt (fun π => Hmc p e ![w 0, π, w 2]) 0 (w 1) := by
    have : (fun π => Hmc p e ![w 0, π, w 2]) = fun _ => Hmc p e (xs w) := by
      funext π; simp [Hmc, xs]
    rw [this]; exact hasDerivAt_const _ _
  have h := (((hasDerivAt_const (w 1) (Uf p (w 2) - Vf p e (w 0))).add
    ((hG.sub hH).const_mul (w 3))).sub (hG.const_mul (wm 3))).add (hR.const_mul (w 4))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  · simp only [Qr, Matrix.cons_val_one, Matrix.cons_val_zero]; ring
  · simp only [lagr, Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val]

/-- Woodford (2003), Ch. 7 (**the consumption first-order condition is derived**): the derivative
of the Lagrangian in `ĉ` is the third Ramsey condition. -/
theorem lagr_deriv_c (e : Fin 3 → ℝ) (wm w : Fin 5 → ℝ) :
    HasDerivAt (fun c => lagr p e (wm 3) (w 3) (w 4) ![w 0, w 1, c]) (Qr p e wm w 2) (w 2) := by
  have hU : HasDerivAt (fun c => Uf p c) (Uc p (xs w)) (w 2) := by
    by_cases hσ : p.σ = 1
    · have e1 : Uc p (xs w) = 1 := by simp [Uc, hσ]
      have e2 : (fun c => Uf p c) = id := by funext c; simp [Uf, hσ]
      rw [e1, e2]; exact hasDerivAt_id _
    · have h1 : 1 - p.σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
      have h := (hd_exp (1 / (1 - p.σ)) (1 - p.σ) 0 (w 2)).sub_const (1 / (1 - p.σ))
      refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
      · simp only [Uc, xs, Matrix.cons_val]; field_simp; ring_nf
      · simp only [Uf, hσ, ↓reduceIte]; field_simp; ring_nf
  have hG : HasDerivAt (fun c => Gadj p ![w 0, w 1, c]) (-(p.σ * Gadj p (xs w))) (w 2) := by
    have h := (hd_exp p.ψ (-p.σ) (w 0 + 2 * w 1) (w 2)).sub
      (hd_exp p.ψ (-p.σ) (w 0 + w 1) (w 2))
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    · simp only [Gadj_eq, xs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      ring_nf
    · simp only [Gadj_eq, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val]
      ring_nf
  have hH : HasDerivAt (fun c => Hmc p e ![w 0, w 1, c]) (HmC p (xs w)) (w 2) := by
    have h := (hd_exp (p.θ * p.m) (-p.σ) (w 0) (w 2)).const_sub
      (p.θ * p.m * Real.exp ((1 + p.ω) * w 0 + e 2 - (1 + p.ω) * e 1))
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    · simp only [HmC, xs, Matrix.cons_val_zero, Matrix.cons_val]
      ring_nf
    · simp only [Hmc, Matrix.cons_val_zero, Matrix.cons_val]
      ring_nf
  have hR : HasDerivAt (fun c => Rr p ![w 0, w 1, c]) (-Real.exp (w 2)) (w 2) := by
    have h := (Real.hasDerivAt_exp (w 2)).const_sub
      (Real.exp (w 0) * (1 - p.ψ / 2 * (Real.exp (w 1) - 1) ^ 2))
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    simp only [Rr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  have h := ((((hU.sub (hasDerivAt_const (w 2) (Vf p e (w 0)))).add
    ((hG.sub hH).const_mul (w 3))).sub (hG.const_mul (wm 3))).add (hR.const_mul (w 4)))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  · simp only [Qr, Matrix.cons_val]; ring
  · simp only [lagr, Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val]

/-! ## The steady state -/

/-- Woodford (2003), Ch. 7: the zero-inflation steady state of the Ramsey conditions,
`(ŷ, π, ĉ, λ, γ) = (0, 0, 0, λ̄, γ̄)`. -/
noncomputable def wbar (p : Par) : Fin 5 → ℝ := ![0, 0, 0, lamb p, gamb p]

/-- The allocation part of the steady state is the zero vector. -/
theorem xs_wbar : xs (wbar p) = 0 := by
  funext i; fin_cases i <;> rfl

/-- The steady-state values of the functions entering the conditions. -/
theorem ss_vals :
    Gadj p 0 = 0 ∧ GaP p 0 = p.ψ ∧ HmY p 0 0 = p.θ * p.m * p.ω ∧ HmC p 0 = p.θ * p.m * p.σ ∧
      RrY p 0 = 1 ∧ RrP p 0 = 0 ∧ Uc p 0 = 1 ∧ Vy p 0 0 = p.m ∧ Hmc p 0 0 = 0 ∧ Rr p 0 = 0 := by
  refine ⟨by norm_num [Gadj], by norm_num [GaP], by norm_num [HmY], by norm_num [HmC],
    by norm_num [RrY], by norm_num [RrP], by norm_num [Uc], by norm_num [Vy], by norm_num [Hmc],
    by norm_num [Rr]⟩

/-- Woodford (2003), Ch. 7 with Rotemberg pricing (**the zero-inflation steady state of the
timeless Ramsey policy for EVERY distortion `Φ = 1 − m`**): `w̄ = (0, 0, 0, λ̄, γ̄)` solves the
exact Ramsey conditions without disturbances. -/
theorem ramsey_steadyState (hp : p.Basic) : Qr p 0 (wbar p) (wbar p) + Nr p (wbar p) = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := ss_vals (p := p)
  have hθ : p.θ ≠ 0 := by linarith [hp.one_lt_θ]
  have hm : p.m ≠ 0 := hp.m_pos.ne'
  have hs : p.σ + p.ω ≠ 0 := by linarith [hp.σ_pos, hp.ω_nonneg]
  have hw2 : wbar p 2 = 0 := rfl
  have hw3 : wbar p 3 = lamb p := rfl
  have hw4 : wbar p 4 = gamb p := rfl
  funext i
  fin_cases i <;> simp only [Qr, Nr, xs_wbar, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hw2, hw3,
    hw4, Pi.add_apply, Pi.zero_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
    Matrix.cons_val_zero, Matrix.cons_val_one, sub_self, zero_mul, mul_zero, add_zero,
    neg_zero, Real.exp_zero]
  · simp only [lamb, gamb]; field_simp; ring
  · simp only [lamb, gamb]; field_simp; ring

/-- The components of the steady-state conditions of a constant `w` (no disturbances). -/
theorem ss_eqs (w : Fin 5 → ℝ) (wm3 : ℝ) (h : Qr p 0 (Function.update w 3 wm3) w + Nr p w = 0) :
    -Vy p 0 (xs w) + (w 3 - wm3) * Gadj p (xs w) - w 3 * HmY p 0 (xs w) +
        w 4 * RrY p (xs w) = 0 ∧
      (w 3 - wm3) * GaP p (xs w) + w 4 * RrP p (xs w) = 0 ∧
      Uc p (xs w) + (w 3 - wm3) * (-(p.σ * Gadj p (xs w))) - w 3 * HmC p (xs w) +
        w 4 * (-Real.exp (w 2)) = 0 ∧
      Gadj p (xs w) - Hmc p 0 (xs w) - p.β * Gadj p (xs w) = 0 ∧ Rr p (xs w) = 0 := by
  have c0 := congrFun h 0
  have c1 := congrFun h 1
  have c2 := congrFun h 2
  have c3 := congrFun h 3
  have c4 := congrFun h 4
  simp only [Qr, Nr, Pi.add_apply, Pi.zero_apply, Function.update_self, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, add_zero] at c0 c1 c2 c3 c4
  exact ⟨c0, c1, c2, by linarith, c4⟩

/-- Woodford (2003), Ch. 7 with Rotemberg pricing (**THE RAMSEY STEADY STATES**): a constant `w`
solving the exact Ramsey conditions without disturbances is EITHER the zero-inflation steady state
`w̄` OR has a zero multiplier on the resource constraint and strictly NEGATIVE inflation. Hence no
timeless Ramsey steady state has positive inflation, for ANY distortion `Φ`, and the
zero-inflation steady state is the unique one with `γ ≠ 0`. -/
theorem ramsey_ss_char (hp : p.Basic) (w : Fin 5 → ℝ) (h : Qr p 0 w w + Nr p w = 0) :
    w = wbar p ∨ (w 4 = 0 ∧ w 1 < 0) := by
  have hw : Function.update w 3 (w 3) = w := Function.update_eq_self 3 w
  rw [← hw] at h
  obtain ⟨c0, c1, c2, c3, c4⟩ := ss_eqs w (w 3) h
  rw [sub_self, zero_mul] at c1
  rw [sub_self, zero_mul, add_zero] at c0
  rw [sub_self, zero_mul, add_zero] at c2
  have hθ : 0 < p.θ := by linarith [hp.one_lt_θ]
  have hθm : 0 < p.θ * p.m := mul_pos hθ hp.m_pos
  have hψ := hp.ψ_pos
  simp only [xs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, RrP, RrY, Rr, Vy,
    HmY, HmC, Uc, Gadj, Hmc, Pi.zero_apply, mul_zero, sub_zero, add_zero] at c0 c1 c2 c3 c4
  rcases eq_or_ne (w 4) 0 with h4 | h4
  · right
    refine ⟨h4, ?_⟩
    rw [h4, zero_mul, add_zero] at c2
    rw [h4, zero_mul, add_zero] at c0
    -- the multiplier is positive
    have hl : 0 < w 3 := by
      have hpos : 0 < p.θ * p.m * p.σ * Real.exp (w 0 - p.σ * w 2) := by
        have := hp.σ_pos; positivity
      have hU := Real.exp_pos ((1 - p.σ) * w 2)
      by_contra hc
      push Not at hc
      nlinarith [mul_nonneg (neg_nonneg.2 hc) hpos.le]
    -- `e^{(1+ω)ŷ} < e^{ŷ − σĉ}`
    have hlt : Real.exp ((1 + p.ω) * w 0) < Real.exp (w 0 - p.σ * w 2) := by
      have hv := Real.exp_pos ((1 + p.ω) * w 0)
      have hm := hp.m_pos
      have h1 : w 3 * (p.θ * p.m * ((1 + p.ω) * Real.exp ((1 + p.ω) * w 0) -
          Real.exp (w 0 - p.σ * w 2))) < 0 := by
        have : 0 < p.m * Real.exp ((1 + p.ω) * w 0) := by positivity
        linarith
      have h2 : (1 + p.ω) * Real.exp ((1 + p.ω) * w 0) - Real.exp (w 0 - p.σ * w 2) < 0 := by
        by_contra hc; push Not at hc
        have := mul_nonneg hl.le (mul_nonneg hθm.le hc)
        linarith
      nlinarith [hp.ω_nonneg]
    -- the adjustment term is negative, so inflation is negative
    have hG : p.ψ * (Real.exp (w 0 - p.σ * w 2) * ((Real.exp (w 1) - 1) * Real.exp (w 1))) < 0 := by
      have hβ : 0 < 1 - p.β := by linarith [hp.β_lt_one]
      have : (1 - p.β) * (p.ψ * (Real.exp (w 0 - p.σ * w 2) * ((Real.exp (w 1) - 1) *
          Real.exp (w 1)))) < 0 := by
        have : p.θ * p.m * (Real.exp ((1 + p.ω) * w 0) - Real.exp (w 0 - p.σ * w 2)) < 0 :=
          mul_neg_of_pos_of_neg hθm (by linarith)
        linarith
      by_contra hc; push Not at hc
      have := mul_nonneg hβ.le hc
      linarith
    have he : Real.exp (w 1) - 1 < 0 := by
      by_contra hc; push Not at hc
      have := mul_nonneg hψ.le (mul_nonneg (Real.exp_pos (w 0 - p.σ * w 2)).le
        (mul_nonneg hc (Real.exp_pos (w 1)).le))
      linarith
    have : Real.exp (w 1) < Real.exp 0 := by rw [Real.exp_zero]; linarith
    exact Real.exp_lt_exp.1 this
  · left
    -- zero inflation
    have hπ : w 1 = 0 := by
      have hz : (Real.exp (w 1) - 1) * (w 4 * (Real.exp (w 0) * p.ψ * Real.exp (w 1))) = 0 := by
        linear_combination -c1
      have hq : w 4 * (Real.exp (w 0) * p.ψ * Real.exp (w 1)) ≠ 0 :=
        mul_ne_zero h4 (by positivity)
      have h1 := (mul_eq_zero.1 hz).resolve_right hq
      have : Real.exp (w 1) = Real.exp 0 := by rw [Real.exp_zero]; linarith
      exact Real.exp_injective this
    rw [hπ] at c0 c3 c4
    simp only [Real.exp_zero, sub_self, mul_zero, sub_zero, pow_two,
      mul_one] at c0 c3 c4
    have h20 : w 2 = w 0 := by
      have : Real.exp (w 2) = Real.exp (w 0) := by linarith
      exact Real.exp_injective this
    have h00 : w 0 = 0 := by
      have hH : Real.exp ((1 + p.ω) * w 0) = Real.exp (w 0 - p.σ * w 2) := by
        have : p.θ * p.m * (Real.exp ((1 + p.ω) * w 0) - Real.exp (w 0 - p.σ * w 2)) = 0 := by
          linarith
        have := (mul_eq_zero.1 this).resolve_left hθm.ne'
        linarith
      have := Real.exp_injective hH
      rw [h20] at this
      have hs : 0 < p.σ + p.ω := by linarith [hp.σ_pos, hp.ω_nonneg]
      nlinarith
    rw [h20, h00] at c0 c2
    simp only [mul_zero, Real.exp_zero, mul_one, sub_zero] at c0 c2
    have hs : p.σ + p.ω ≠ 0 := by linarith [hp.σ_pos, hp.ω_nonneg]
    have hs' : 0 < p.σ + p.ω := by linarith [hp.σ_pos, hp.ω_nonneg]
    have hl3 : w 3 = lamb p := by
      unfold lamb
      rw [eq_div_iff (by positivity)]
      linear_combination (-1 : ℝ) * c0 - c2
    have hl4 : w 4 = gamb p := by
      unfold gamb
      rw [eq_div_iff hs]
      rw [hl3] at c2
      have key : lamb p * (p.θ * p.m * p.σ) * (p.σ + p.ω) = (1 - p.m) * p.σ := by
        unfold lamb
        have : p.θ ≠ 0 := hθ.ne'
        have : p.m ≠ 0 := hp.m_pos.ne'
        field_simp
      linear_combination (-(p.σ + p.ω)) * c2 - key
    funext i
    fin_cases i
    · exact h00
    · exact hπ
    · simp only [wbar, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]; rw [h20, h00]
    · exact hl3
    · exact hl4

/-- Woodford (2003), Ch. 7 (**the golden-rule conditions**): the first-order conditions of
maximising steady-state welfare `u − v` subject to the STATIONARY constraints `(1−β)G = H` and
`R = 0` are the Ramsey conditions with the promise `λ_{t−1}` replaced by `βλ` (the Lagrangian
`u − v + λ((1−β)G − H) + γR`). -/
noncomputable def Qgold (p : Par) (w : Fin 5 → ℝ) : Fin 5 → ℝ :=
  Qr p 0 (Function.update w 3 (p.β * w 3)) w + Nr p w

/-- Woodford (2003), Ch. 7 (**the steady state that maximises steady-state welfare has NONZERO
inflation whenever the steady state is distorted**): if a solution of the golden-rule conditions
has zero inflation then `m = 1`, i.e. `Φ = 0`. Contrast `ramsey_ss_char`: the timeless Ramsey
steady state has zero inflation for every `Φ`. -/
theorem golden_rule_inflation (hp : p.Basic) (w : Fin 5 → ℝ) (h : Qgold p w = 0)
    (hπ : w 1 = 0) : p.m = 1 := by
  obtain ⟨c0, c1, c2, c3, c4⟩ := ss_eqs w (p.β * w 3) h
  have hθ : 0 < p.θ := by linarith [hp.one_lt_θ]
  have hθm : 0 < p.θ * p.m := mul_pos hθ hp.m_pos
  simp only [xs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, RrP, RrY, Rr, Vy,
    HmY, HmC, Uc, Gadj, GaP, Hmc, Pi.zero_apply, mul_zero, sub_zero, add_zero, hπ,
    Real.exp_zero, sub_self, zero_mul] at c0 c1 c2 c3 c4
  have hl : w 3 = 0 := by
    have hE := Real.exp_pos (w 0 - p.σ * w 2)
    have h1 : (1 - p.β) * p.ψ * Real.exp (w 0 - p.σ * w 2) ≠ 0 := by
      have := hp.ψ_pos
      have : 0 < 1 - p.β := by linarith [hp.β_lt_one]
      positivity
    have : (1 - p.β) * p.ψ * Real.exp (w 0 - p.σ * w 2) * w 3 = 0 := by
      linear_combination c1
    exact (mul_eq_zero.1 this).resolve_left h1
  have h20 : w 2 = w 0 := by
    have : Real.exp (w 2) = Real.exp (w 0) := by norm_num at c4; linarith
    exact Real.exp_injective this
  have h00 : w 0 = 0 := by
    have hH : Real.exp ((1 + p.ω) * w 0) = Real.exp (w 0 - p.σ * w 2) := by
      have : p.θ * p.m * (Real.exp ((1 + p.ω) * w 0) - Real.exp (w 0 - p.σ * w 2)) = 0 := by
        linarith
      have := (mul_eq_zero.1 this).resolve_left hθm.ne'
      linarith
    have := Real.exp_injective hH
    rw [h20] at this
    have hs : 0 < p.σ + p.ω := by linarith [hp.σ_pos, hp.ω_nonneg]
    nlinarith
  rw [hl, h20, h00] at c0 c2
  norm_num at c0 c2
  linarith

end Woodford.StabilizationWelfare.NonlinearRotembergRamsey
