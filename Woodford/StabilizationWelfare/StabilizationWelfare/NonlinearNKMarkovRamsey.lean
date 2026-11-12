/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearNKMarkov

/-!
# The exact Ramsey problem of the Calvo model: first-order conditions and steady state

Woodford (2003), *Interest and Prices*, Chapter 6, §5 (pp. 455–463, Benigno–Woodford), and
Chapter 7 (optimal policy from a timeless perspective).

The planner chooses `(ŷ_t, π_t, F̂_t, K̂_t, Δ_t)` to maximise `E₀∑βᵗ[u(Y_t) − v(Y_t)Δ_t]` subject
to the exact Calvo recursions for `F` and `K`, the price index with the optimal reset price and
the dispersion law (the interest rate is residual, so the Euler equation does not bind). With
multipliers `λ₁, λ₂` (the `F`, `K` recursions), `λ₃` (price index) and `λ₄` (dispersion law), and
the law of iterated expectations turning `βᵗλ_{t}αβE_t[⋯_{t+1}]` into a date-`t+1` term
multiplied by `λ_t`, the first-order conditions at date `t` depend on the LAGGED multipliers
`λ₁, λ₂` and the lagged dispersion — the predetermined state of the timeless-perspective
problem.

## Main results

* `ramseyQ`, `ramseyN`: the nine exact conditions (five first-order conditions, four
  constraints) in the form `Q(e_t, w_{t−1}, w_t) + E_t N(w_t, w_{t+1}) = 0`,
  `w = (ŷ, π, F̂, K̂, Δ, λ₁, λ₂, λ₃, λ₄)`, with isoelastic `u`, `v`
  (`u_y = A_u e^{(1−σ)ŷ+σĉ}`, `v = A_v e^{(1+ω)ŷ−ωq}/(1+ω)`, `A_v = (1 − Φ)A_u`).
* `ramseyQ_deriv_y`, `ramseyQ_deriv_pi`, `ramseyQ_deriv_F`, `ramseyQ_deriv_K`,
  `ramseyQ_deriv_Delta`: the five first-order conditions are the partial derivatives of the
  Lagrangian terms in the corresponding variable (`lagY`, `lagPi`, `lagF`, `lagK`, `lagDelta`).
* **`ramsey_steadyState`**: for every distortion `Φ`, the zero-inflation point `π = 0`, `Δ = 1`,
  `ŷ = F̂ = K̂ = 0` with the explicit multipliers `ramseyLam` solves all nine conditions (the
  timeless-perspective steady state of Benigno–Woodford).
* **`ramsey_disp_block`** and **`ramsey_mu_block`**: at the zero-inflation steady state the
  linearised dispersion `Δ̂_t = αΔ̂_{t−1}` and the summed multiplier `μ = dλ₁ + dλ₂`,
  `μ_t = αμ_{t−1}`, are autonomous stable backward recursions: two of the three predetermined
  variables form a stable block decoupled from the rest at first order.

## What is not proved (see the report)

Existence and local uniqueness of the bounded timeless Ramsey solution from a given
`(Δ_{−1}, λ_{−1})` requires the Blanchard–Kahn root condition for the remaining linearised
system (one predetermined combination of `λ₁, λ₂` and forward variables) and a sequence-space
implicit function theorem with lags; neither is proved here.
-/

namespace Woodford.StabilizationWelfare.NonlinearNKMarkovRamsey

open NonlinearNKMarkov

/-- Woodford (2003), §5: the welfare weights — `A_u = u_c Ȳ`, `A_v = v_y Ȳ = (1 − Φ)A_u`. -/
structure RPar where
  /-- The marginal utility of output at the steady state, times output. -/
  Au : ℝ
  /-- The distortion `Φ` of the steady state. -/
  Φ : ℝ

/-- The exponents `a = θ(1+ω)` and `b = θ − 1`. -/
def aE (p : Par) : ℝ := p.θ * (1 + p.ω)

/-- Woodford (2003), §5 (**the exact Ramsey conditions, current part**). With
`w = (ŷ, π, F̂, K̂, Δ, λ₁, λ₂, λ₃, λ₄)`, lagged `w₋`, disturbances `e = (·, ĉ, τ̂, q, μ̂ʷ)`,
`x̂ = (K̂ − F̂)/(1+ωθ)`:
0. `∂ŷ`: `A_u e^{(1−σ)ŷ+σĉ} − A_vΔe^{(1+ω)ŷ−ωq} − λ₁(1−αβ)(1−σ)e^{f̂} − λ₂(1−αβ)(1+ω)e^{k̂}`;
1. `∂π`: `−α(θ−1)λ₁₋e^{(θ−1)π+F̂} − αaλ₂₋e^{aπ+K̂} + α(θ−1)λ₃e^{(θ−1)π} − αaλ₄Δ₋e^{aπ}`;
2. `∂F̂`: `λ₁e^{F̂} − αλ₁₋e^{(θ−1)π+F̂} + (1−α)((θ−1)/(1+ωθ))λ₃e^{−(θ−1)x̂}
   − (1−α)(a/(1+ωθ))λ₄e^{−ax̂}`;
3. `∂K̂`: `λ₂e^{K̂} − αλ₂₋e^{aπ+K̂} − (1−α)((θ−1)/(1+ωθ))λ₃e^{−(θ−1)x̂}
   + (1−α)(a/(1+ωθ))λ₄e^{−ax̂}`;
4. `∂Δ`: `−A_v e^{(1+ω)ŷ−ωq}/(1+ω) + λ₄`;
5. `F`: `e^{F̂} − (1−αβ)e^{f̂}`; 6. `K`: `e^{K̂} − (1−αβ)e^{k̂}`;
7. price index; 8. dispersion `Δ − αΔ₋e^{aπ} − (1−α)e^{−ax̂}`. -/
noncomputable def ramseyQ (p : Par) (R : RPar) (e : Fin 5 → ℝ) (wm w : Fin 9 → ℝ) : Fin 9 → ℝ :=
  let x := (w 3 - w 2) / p.c0
  let fh := (1 - p.σ) * w 0 + p.σ * e 1 + e 2
  let kh := (1 + p.ω) * w 0 - p.ω * e 3 + e 4
  let Av := (1 - R.Φ) * R.Au
  ![R.Au * Real.exp ((1 - p.σ) * w 0 + p.σ * e 1)
      - Av * w 4 * Real.exp ((1 + p.ω) * w 0 - p.ω * e 3)
      - w 5 * (1 - p.α * p.β) * (1 - p.σ) * Real.exp fh
      - w 6 * (1 - p.α * p.β) * (1 + p.ω) * Real.exp kh,
    -(p.α * (p.θ - 1) * wm 5 * Real.exp ((p.θ - 1) * w 1 + w 2))
      - p.α * aE p * wm 6 * Real.exp (aE p * w 1 + w 3)
      + p.α * (p.θ - 1) * w 7 * Real.exp ((p.θ - 1) * w 1)
      - p.α * aE p * w 8 * wm 4 * Real.exp (aE p * w 1),
    w 5 * Real.exp (w 2) - p.α * wm 5 * Real.exp ((p.θ - 1) * w 1 + w 2)
      + (1 - p.α) * ((p.θ - 1) / p.c0) * w 7 * Real.exp (-((p.θ - 1) * x))
      - (1 - p.α) * (aE p / p.c0) * w 8 * Real.exp (-(aE p * x)),
    w 6 * Real.exp (w 3) - p.α * wm 6 * Real.exp (aE p * w 1 + w 3)
      - (1 - p.α) * ((p.θ - 1) / p.c0) * w 7 * Real.exp (-((p.θ - 1) * x))
      + (1 - p.α) * (aE p / p.c0) * w 8 * Real.exp (-(aE p * x)),
    -(Av * Real.exp ((1 + p.ω) * w 0 - p.ω * e 3) / (1 + p.ω)) + w 8,
    Real.exp (w 2) - (1 - p.α * p.β) * Real.exp fh,
    Real.exp (w 3) - (1 - p.α * p.β) * Real.exp kh,
    p.α * (Real.exp ((p.θ - 1) * w 1) - 1) + (1 - p.α) * (Real.exp (-((p.θ - 1) * x)) - 1),
    w 4 - p.α * wm 4 * Real.exp (aE p * w 1) - (1 - p.α) * Real.exp (-(aE p * x))]

/-- Woodford (2003), §5 (**the exact Ramsey conditions, the part inside `E_t`**), as a function of
the current and next-period variables: `∂Δ`: `−βαλ₄′e^{aπ′}`; `F`: `−αβe^{(θ−1)π′+F̂′}`;
`K`: `−αβe^{aπ′+K̂′}`; zero elsewhere. -/
noncomputable def ramseyN (p : Par) (wn : Fin 9 → ℝ) : Fin 9 → ℝ :=
  ![0, 0, 0, 0, -(p.β * p.α * wn 8 * Real.exp (aE p * wn 1)),
    -(p.α * p.β * Real.exp ((p.θ - 1) * wn 1 + wn 2)),
    -(p.α * p.β * Real.exp (aE p * wn 1 + wn 3)), 0, 0]

/-! ## The first-order conditions are derivatives of the Lagrangian -/

/-- Woodford (2003), §5: the date-`t` terms of the Lagrangian that involve `ŷ_t`:
`u(Y) − v(Y)Δ + λ₁[e^{F̂} − (1−αβ)e^{f̂}] + λ₂[e^{K̂} − (1−αβ)e^{k̂}]`, with
`u = A_u e^{(1−σ)ŷ+σĉ}/(1−σ)` (`σ ≠ 1`) and `v = A_v e^{(1+ω)ŷ−ωq}/(1+ω)`. -/
noncomputable def lagY (p : Par) (R : RPar) (e : Fin 5 → ℝ) (w : Fin 9 → ℝ) (y : ℝ) : ℝ :=
  R.Au * Real.exp ((1 - p.σ) * y + p.σ * e 1) / (1 - p.σ)
    - (1 - R.Φ) * R.Au * w 4 * Real.exp ((1 + p.ω) * y - p.ω * e 3) / (1 + p.ω)
    + w 5 * (Real.exp (w 2) - (1 - p.α * p.β) * Real.exp ((1 - p.σ) * y + p.σ * e 1 + e 2))
    + w 6 * (Real.exp (w 3) - (1 - p.α * p.β) * Real.exp ((1 + p.ω) * y - p.ω * e 3 + e 4))

/-- Woodford (2003), §5 (**the output condition is `∂ℒ/∂ŷ`**). -/
theorem ramseyQ_deriv_y (p : Par) (R : RPar) (hσ : p.σ ≠ 1) (hω : 1 + p.ω ≠ 0)
    (e : Fin 5 → ℝ) (wm w : Fin 9 → ℝ) :
    HasDerivAt (lagY p R e w) (ramseyQ p R e wm w 0) (w 0) := by
  have h1σ : 1 - p.σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
  have hexp : ∀ c d : ℝ, HasDerivAt (fun y => Real.exp (c * y + d))
      (Real.exp (c * w 0 + d) * c) (w 0) := fun c d => by
    have := (((hasDerivAt_id (w 0)).const_mul c).add_const d).exp
    simpa using this
  have d1 := HasDerivAt.div_const (HasDerivAt.const_mul R.Au (hexp (1 - p.σ) (p.σ * e 1)))
    (1 - p.σ)
  have d2 := HasDerivAt.div_const (HasDerivAt.const_mul ((1 - R.Φ) * R.Au * w 4)
    (hexp (1 + p.ω) (-(p.ω * e 3)))) (1 + p.ω)
  have d3 := HasDerivAt.const_mul (w 5) (HasDerivAt.const_sub (Real.exp (w 2))
    (HasDerivAt.const_mul (1 - p.α * p.β) (hexp (1 - p.σ) (p.σ * e 1 + e 2))))
  have d4 := HasDerivAt.const_mul (w 6) (HasDerivAt.const_sub (Real.exp (w 3))
    (HasDerivAt.const_mul (1 - p.α * p.β) (hexp (1 + p.ω) (-(p.ω * e 3) + e 4))))
  have h := HasDerivAt.add (HasDerivAt.add (HasDerivAt.sub d1 d2) d3) d4
  have hf : lagY p R e w = fun y => R.Au * Real.exp ((1 - p.σ) * y + p.σ * e 1) / (1 - p.σ) -
      (1 - R.Φ) * R.Au * w 4 * Real.exp ((1 + p.ω) * y + -(p.ω * e 3)) / (1 + p.ω) +
      w 5 * (Real.exp (w 2) - (1 - p.α * p.β) * Real.exp ((1 - p.σ) * y + (p.σ * e 1 + e 2))) +
      w 6 * (Real.exp (w 3) - (1 - p.α * p.β) * Real.exp ((1 + p.ω) * y +
        (-(p.ω * e 3) + e 4))) := by
    funext y; simp only [lagY]; ring_nf
  rw [hf]
  refine h.congr_deriv ?_
  simp only [ramseyQ, Matrix.cons_val]
  field_simp
  ring_nf

/-- Woodford (2003), §5: the terms of the Lagrangian involving `Δ_t` — `−v(Y)Δ_t` and
`λ₄[Δ_t − αΔ₋e^{aπ} − (1−α)e^{−ax̂}]` at date `t`, and `βλ₄′[Δ′ − αΔ_t e^{aπ′} − ⋯]` at `t+1`. -/
noncomputable def lagDelta (p : Par) (R : RPar) (e : Fin 5 → ℝ) (w wn : Fin 9 → ℝ) (Δ : ℝ) : ℝ :=
  -((1 - R.Φ) * R.Au * Real.exp ((1 + p.ω) * w 0 - p.ω * e 3) / (1 + p.ω)) * Δ
    + w 8 * Δ - p.β * wn 8 * (p.α * Δ * Real.exp (aE p * wn 1))

/-- Woodford (2003), §5 (**the dispersion condition is `∂ℒ/∂Δ`**, the next-period term inside
`E_t`). -/
theorem ramseyQ_deriv_Delta (p : Par) (R : RPar) (e : Fin 5 → ℝ) (wm w wn : Fin 9 → ℝ) :
    HasDerivAt (lagDelta p R e w wn) (ramseyQ p R e wm w 4 + ramseyN p wn 4) (w 4) := by
  have d := (((hasDerivAt_id (w 4)).const_mul
    (-((1 - R.Φ) * R.Au * Real.exp ((1 + p.ω) * w 0 - p.ω * e 3) / (1 + p.ω)))).add
    ((hasDerivAt_id (w 4)).const_mul (w 8))).sub
    ((((hasDerivAt_id (w 4)).const_mul p.α).mul_const (Real.exp (aE p * wn 1))).const_mul
      (p.β * wn 8))
  refine d.congr_deriv ?_
  simp only [ramseyQ, ramseyN, Matrix.cons_val]
  ring

/-- Woodford (2003), §5: the terms of the Lagrangian involving `π_t` — the date-`(t−1)` recursions
weighted by the lagged multipliers (`β⁻¹` absorbed by the law of iterated expectations), the price
index and the dispersion law at `t`. -/
noncomputable def lagPi (p : Par) (wm w : Fin 9 → ℝ) (π : ℝ) : ℝ :=
  -(p.α * wm 5 * Real.exp ((p.θ - 1) * π + w 2)) - p.α * wm 6 * Real.exp (aE p * π + w 3)
    + w 7 * (p.α * (Real.exp ((p.θ - 1) * π) - 1))
    + w 8 * (w 4 - p.α * wm 4 * Real.exp (aE p * π))

/-- Woodford (2003), §5 (**the inflation condition is `∂ℒ/∂π`**). -/
theorem ramseyQ_deriv_pi (p : Par) (R : RPar) (e : Fin 5 → ℝ) (wm w : Fin 9 → ℝ) :
    HasDerivAt (lagPi p wm w) (ramseyQ p R e wm w 1) (w 1) := by
  have hexp : ∀ c d : ℝ, HasDerivAt (fun y => Real.exp (c * y + d))
      (Real.exp (c * w 1 + d) * c) (w 1) := fun c d => by
    have := (((hasDerivAt_id (w 1)).const_mul c).add_const d).exp
    simpa using this
  have d1 := HasDerivAt.neg (HasDerivAt.const_mul (p.α * wm 5) (hexp (p.θ - 1) (w 2)))
  have d2 := HasDerivAt.const_mul (p.α * wm 6) (hexp (aE p) (w 3))
  have d3 := HasDerivAt.const_mul (w 7) (HasDerivAt.const_mul p.α
    (HasDerivAt.sub_const 1 (hexp (p.θ - 1) 0)))
  have d4 := HasDerivAt.const_mul (w 8) (HasDerivAt.const_sub (w 4)
    (HasDerivAt.const_mul (p.α * wm 4) (hexp (aE p) 0)))
  have h := HasDerivAt.add (HasDerivAt.add (HasDerivAt.sub d1 d2) d3) d4
  have hf : lagPi p wm w = fun y => -(p.α * wm 5 * Real.exp ((p.θ - 1) * y + w 2)) -
      p.α * wm 6 * Real.exp (aE p * y + w 3) +
      w 7 * (p.α * (Real.exp ((p.θ - 1) * y + 0) - 1)) +
      w 8 * (w 4 - p.α * wm 4 * Real.exp (aE p * y + 0)) := by
    funext y; simp only [lagPi, add_zero]
  rw [hf]
  refine h.congr_deriv ?_
  simp only [ramseyQ, Matrix.cons_val, add_zero]
  ring

/-- Woodford (2003), §5: the terms of the Lagrangian involving `F̂_t` (`x̂ = (K̂ − F̂)/(1+ωθ)`). -/
noncomputable def lagF (p : Par) (wm w : Fin 9 → ℝ) (F : ℝ) : ℝ :=
  w 5 * Real.exp F - p.α * wm 5 * Real.exp ((p.θ - 1) * w 1 + F)
    + w 7 * ((1 - p.α) * (Real.exp (-((p.θ - 1) * ((w 3 - F) / p.c0))) - 1))
    + w 8 * (-((1 - p.α) * Real.exp (-(aE p * ((w 3 - F) / p.c0)))))

/-- Woodford (2003), §5 (**the `F` condition is `∂ℒ/∂F̂`**). -/
theorem ramseyQ_deriv_F (p : Par) (R : RPar) (hp : p.Std) (e : Fin 5 → ℝ) (wm w : Fin 9 → ℝ) :
    HasDerivAt (lagF p wm w) (ramseyQ p R e wm w 2) (w 2) := by
  have hc0 := hp.c0_pos.ne'
  have hexp : ∀ c d : ℝ, HasDerivAt (fun y => Real.exp (c * y + d))
      (Real.exp (c * w 2 + d) * c) (w 2) := fun c d => by
    have := (((hasDerivAt_id (w 2)).const_mul c).add_const d).exp
    simpa using this
  have d1 := HasDerivAt.const_mul (w 5) (hexp 1 0)
  have d2 := HasDerivAt.const_mul (p.α * wm 5) (hexp 1 ((p.θ - 1) * w 1))
  have d3 := HasDerivAt.const_mul (w 7) (HasDerivAt.const_mul (1 - p.α)
    (HasDerivAt.sub_const 1 (hexp ((p.θ - 1) / p.c0) (-((p.θ - 1) * w 3 / p.c0)))))
  have d4 := HasDerivAt.const_mul (w 8) (HasDerivAt.neg (HasDerivAt.const_mul (1 - p.α)
    (hexp (aE p / p.c0) (-(aE p * w 3 / p.c0)))))
  have h := HasDerivAt.add (HasDerivAt.add (HasDerivAt.sub d1 d2) d3) d4
  have hf : lagF p wm w = fun y => w 5 * Real.exp (1 * y + 0) -
      p.α * wm 5 * Real.exp (1 * y + (p.θ - 1) * w 1) +
      w 7 * ((1 - p.α) * (Real.exp ((p.θ - 1) / p.c0 * y + -((p.θ - 1) * w 3 / p.c0)) - 1)) +
      w 8 * -((1 - p.α) * Real.exp (aE p / p.c0 * y + -(aE p * w 3 / p.c0))) := by
    funext y
    simp only [lagF, one_mul, add_zero]
    congr 2 <;> [ring_nf; skip; skip] <;> congr 2 <;> field_simp <;> ring
  rw [hf]
  refine h.congr_deriv ?_
  simp only [ramseyQ, Matrix.cons_val, one_mul, add_zero, mul_one]
  have e1 : (p.θ - 1) / p.c0 * w 2 + -((p.θ - 1) * w 3 / p.c0) =
      -((p.θ - 1) * ((w 3 - w 2) / p.c0)) := by field_simp; ring
  have e2 : aE p / p.c0 * w 2 + -(aE p * w 3 / p.c0) = -(aE p * ((w 3 - w 2) / p.c0)) := by
    field_simp; ring
  rw [e1, e2, add_comm ((p.θ - 1) * w 1) (w 2)]
  ring

/-- Woodford (2003), §5: the terms of the Lagrangian involving `K̂_t`. -/
noncomputable def lagK (p : Par) (wm w : Fin 9 → ℝ) (K : ℝ) : ℝ :=
  w 6 * Real.exp K - p.α * wm 6 * Real.exp (aE p * w 1 + K)
    + w 7 * ((1 - p.α) * (Real.exp (-((p.θ - 1) * ((K - w 2) / p.c0))) - 1))
    + w 8 * (-((1 - p.α) * Real.exp (-(aE p * ((K - w 2) / p.c0)))))

/-- Woodford (2003), §5 (**the `K` condition is `∂ℒ/∂K̂`**). -/
theorem ramseyQ_deriv_K (p : Par) (R : RPar) (hp : p.Std) (e : Fin 5 → ℝ) (wm w : Fin 9 → ℝ) :
    HasDerivAt (lagK p wm w) (ramseyQ p R e wm w 3) (w 3) := by
  have hc0 := hp.c0_pos.ne'
  have hexp : ∀ c d : ℝ, HasDerivAt (fun y => Real.exp (c * y + d))
      (Real.exp (c * w 3 + d) * c) (w 3) := fun c d => by
    have := (((hasDerivAt_id (w 3)).const_mul c).add_const d).exp
    simpa using this
  have d1 := HasDerivAt.const_mul (w 6) (hexp 1 0)
  have d2 := HasDerivAt.const_mul (p.α * wm 6) (hexp 1 (aE p * w 1))
  have d3 := HasDerivAt.const_mul (w 7) (HasDerivAt.const_mul (1 - p.α)
    (HasDerivAt.sub_const 1 (hexp (-((p.θ - 1) / p.c0)) ((p.θ - 1) * w 2 / p.c0))))
  have d4 := HasDerivAt.const_mul (w 8) (HasDerivAt.neg (HasDerivAt.const_mul (1 - p.α)
    (hexp (-(aE p / p.c0)) (aE p * w 2 / p.c0))))
  have h := HasDerivAt.add (HasDerivAt.add (HasDerivAt.sub d1 d2) d3) d4
  have hf : lagK p wm w = fun y => w 6 * Real.exp (1 * y + 0) -
      p.α * wm 6 * Real.exp (1 * y + aE p * w 1) +
      w 7 * ((1 - p.α) * (Real.exp (-((p.θ - 1) / p.c0) * y + (p.θ - 1) * w 2 / p.c0) - 1)) +
      w 8 * -((1 - p.α) * Real.exp (-(aE p / p.c0) * y + aE p * w 2 / p.c0)) := by
    funext y
    simp only [lagK, one_mul, add_zero]
    congr 2 <;> [ring_nf; skip; skip] <;> congr 2 <;> field_simp <;> ring
  rw [hf]
  refine h.congr_deriv ?_
  simp only [ramseyQ, Matrix.cons_val, one_mul, add_zero, mul_one]
  have e1 : -((p.θ - 1) / p.c0) * w 3 + (p.θ - 1) * w 2 / p.c0 =
      -((p.θ - 1) * ((w 3 - w 2) / p.c0)) := by field_simp; ring
  have e2 : -(aE p / p.c0) * w 3 + aE p * w 2 / p.c0 = -(aE p * ((w 3 - w 2) / p.c0)) := by
    field_simp; ring
  rw [e1, e2, add_comm (aE p * w 1) (w 3)]
  ring

/-! ## The timeless-perspective steady state -/

/-- Woodford (2003), §5 (Benigno–Woodford): the steady-state multipliers,
`λ₁ = −Φ A_u/((1−αβ)(ω+σ))`, `λ₂ = −λ₁`, `λ₄ = A_v/((1+ω)(1−αβ))`,
`λ₃ = (aλ₄ − (1+ωθ)λ₁)/(θ − 1)`. -/
noncomputable def ramseyLam (p : Par) (R : RPar) : Fin 4 → ℝ :=
  let l1 := -(R.Φ * R.Au / ((1 - p.α * p.β) * (p.ω + p.σ)))
  let l4 := (1 - R.Φ) * R.Au / ((1 + p.ω) * (1 - p.α * p.β))
  ![l1, -l1, (aE p * l4 - p.c0 * l1) / (p.θ - 1), l4]

/-- The steady-state point `w̄ = (0, 0, 0, 0, 1, λ̄₁, λ̄₂, λ̄₃, λ̄₄)`. -/
noncomputable def ramseySS (p : Par) (R : RPar) : Fin 9 → ℝ :=
  ![0, 0, 0, 0, 1, ramseyLam p R 0, ramseyLam p R 1, ramseyLam p R 2, ramseyLam p R 3]

/-- Woodford (2003), §5 and Ch. 7 (**the zero-inflation timeless-perspective steady state**): for
every distortion `Φ`, the point `π = 0`, `Δ = 1`, `ŷ = F̂ = K̂ = 0` with the multipliers
`ramseyLam` solves all nine exact Ramsey conditions without disturbances, with itself as the lagged
state. -/
theorem ramsey_steadyState (p : Par) (R : RPar) (hp : p.Std) :
    ramseyQ p R 0 (ramseySS p R) (ramseySS p R) + ramseyN p (ramseySS p R) = 0 := by
  have hab : 1 - p.α * p.β ≠ 0 := by linarith [hp.ab_lt_one]
  have hωσ : p.ω + p.σ ≠ 0 := by linarith [hp.ω_nonneg, hp.σ_pos]
  have hω : 1 + p.ω ≠ 0 := by linarith [hp.ω_nonneg]
  have hθ : p.θ - 1 ≠ 0 := by linarith [hp.one_lt_θ]
  have hc0 := hp.c0_pos.ne'
  have ha : aE p - (p.θ - 1) = p.c0 := by unfold aE Par.c0; ring
  funext i
  fin_cases i <;>
    simp [ramseyQ, ramseyN, ramseySS, ramseyLam, Matrix.cons_val] <;>
    field_simp <;> unfold aE Par.c0 at * <;> ring

/-! ## First-order decoupling of the predetermined block -/

/-- Woodford (2003), (2.20) at the zero-inflation steady state (**the linearised dispersion law is
autonomous**): if the linearised price index `(1−α)x̂ = απ̂` holds, the linearised dispersion law
`Δ̂ − αΔ̂₋ − αaπ̂ + (1−α)ax̂ = 0` is `Δ̂ = αΔ̂₋`: a stable backward recursion independent of the
rest of the system. -/
theorem ramsey_disp_block (p : Par) {D Dm π x : ℝ} (hPI : (1 - p.α) * x = p.α * π)
    (hlin : D - p.α * Dm - p.α * aE p * π + (1 - p.α) * aE p * x = 0) : D = p.α * Dm := by
  linear_combination hlin - aE p * hPI

/-- Woodford (2003), §5 and Ch. 7 (**the summed multiplier is autonomous**): adding the linearised
`∂F̂` and `∂K̂` conditions at the steady state (where `λ̄₂ = −λ̄₁`) and using the linearised price
index `(1−α)x̂ = απ̂` (`x̂ = (K̂ − F̂)/(1+ωθ)`), the sum `μ = dλ₁ + dλ₂` obeys `μ_t = αμ_{t−1}`. -/
theorem ramsey_mu_block (p : Par) (hp : p.Std) {l1 dl1 dl2 dl1m dl2m π F K : ℝ}
    (hPI : (1 - p.α) * ((K - F) / p.c0) = p.α * π)
    (hsum : (dl1 + dl2) - p.α * (dl1m + dl2m) + l1 * (F - K) -
      p.α * l1 * ((p.θ - 1) * π + F - aE p * π - K) = 0) :
    dl1 + dl2 = p.α * (dl1m + dl2m) := by
  have hc0 := hp.c0_pos.ne'
  have ha : aE p - (p.θ - 1) = p.c0 := by unfold aE Par.c0; ring
  have h2 : (1 - p.α) * (K - F) = p.α * p.c0 * π := by
    field_simp at hPI; linarith
  have : l1 * (F - K) - p.α * l1 * ((p.θ - 1) * π + F - aE p * π - K) = 0 := by
    have e : (p.θ - 1) * π - aE p * π = -(p.c0 * π) := by rw [← ha]; ring
    linear_combination (-l1) * h2 - p.α * l1 * e
  linarith

end Woodford.StabilizationWelfare.NonlinearNKMarkovRamsey
