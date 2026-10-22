/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergJets
import StabilizationWelfare.NonlinearRotembergBoundary

/-!
# Second-order welfare of trend inflation: Rotemberg versus Calvo with a distorted steady state

Woodford (2003), *Interest and Prices*, Chapter 6, §2 (pp. 393–400) and §4.1 (the cost of a
distorted steady state, `Φ = 1 − m`), Chapter 3, §2 and footnote 44 (the Calvo and Rotemberg
pricing conditions). The family of exact equilibria compared here is the family of steady states
indexed by trend inflation `π`, each an exact equilibrium for its inflation target. Both welfare
measures include the LINEAR term `(1 − m)ŷ` evaluated at the exact (hence second-order) steady-state
output.

Units: `u_c Ȳ = 1`, `u(C) = (e^{(1−σ)ĉ} − 1)/(1 − σ)` (`σ ≠ 1`), disutility of output
`m(e^{(1+ω)ŷ}Δ − 1)/(1 + ω)` (dispersion `Δ` in Calvo, `Δ = 1` in Rotemberg).

* Rotemberg: `ŷ_R(π) = (log(1 + (1−β)ψ(e^π−1)e^π/(θm)) − σ log(C/Y))/(σ+ω)` (the exact steady
  state, `NonlinearRotembergBoundary.ssY`), `ĉ = ŷ + log(C/Y)`, welfare `WR`.
* Calvo: `ŷ_C`, the log reset price `lx` and dispersion `LD = log Δ` of `calvo_steady` (price
  index, reset condition and dispersion law at trend inflation), welfare `WC`.

## Main results

* **`trend_welfare`**: under the equivalence map `ψ = θmα(1+ωθ)/((1−α)(1−αβ))`, the first
  derivatives in `π` at zero inflation coincide, `(1 − m)Y₁`, while the second derivatives differ by
  `(1 − m)(Y₂ᴿ − Y₂ᶜ) + mθα²(1+ωθ)(1−β)/((1−α)²(1−αβ))`.
* **`trend_welfare_differ`**: at `m = 1` the difference is strictly positive, and for any other
  parameters the second-order totals coincide for at most two values of `m`: the totals do NOT
  coincide in general, with or without a distortion.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergTrendWelfare

open Filter Topology
open NonlinearRotemberg
open NonlinearRotembergJets
open NonlinearRotembergLinks (wedge)
open NonlinearRotembergBoundary (ssY)

variable {p : Par}

/-! ## Elementary jets -/

/-- `e^π − 1`. -/
theorem J_h : J2 (fun π => Real.exp π - 1) 1 1 :=
  J2_eq (J2_congr (J2_sub (J2_exp 1) (J2_const 1)) fun x => by simp) (by ring) (by ring)

/-- `(e^π − 1)e^π`. -/
theorem J_g : J2 (fun π => (Real.exp π - 1) * Real.exp π) 1 3 := by
  have he : J2 (fun π => Real.exp π) 1 1 :=
    J2_eq (J2_congr (J2_exp 1) fun x => by simp) (by ring) (by ring)
  exact J2_eq (J2_mul J_h he) (by simp) (by norm_num)

/-- `C/Y = 1 − (ψ/2)(e^π − 1)²`. -/
theorem J_w (ψ : ℝ) : J2 (wedge ψ) 0 (-ψ) := by
  have h2 := J2_mul J_h J_h
  have := J2_sub (J2_const 1) (J2_const_mul (ψ / 2) h2)
  refine J2_eq (J2_congr this fun x => by simp [wedge, sq]) (by simp) (by simp)

/-- `log(C/Y)`. -/
theorem J_lw (ψ : ℝ) : J2 (fun π => Real.log (wedge ψ π)) 0 (-ψ) := by
  have h0 : (0 : ℝ) < wedge ψ 0 := by simp [wedge]
  exact J2_eq (J2_log (J_w ψ) h0) (by simp) (by simp [wedge])

/-- `log(1 − c e^{eπ})` for `c < 1`. -/
theorem J_ell {c e : ℝ} (hc : c < 1) :
    J2 (fun π => Real.log (1 - c * Real.exp (e * π))) (-(c * e) / (1 - c))
      (-(c * e ^ 2) / (1 - c) ^ 2) := by
  have hq := J2_sub (J2_const 1) (J2_const_mul c (J2_exp e))
  have h0 : (0 : ℝ) < (fun π => 1 - c * Real.exp (e * π)) 0 := by simp; linarith
  have h1c : 1 - c ≠ 0 := by linarith
  refine J2_eq (J2_congr (J2_log hq h0) fun x => rfl) ?_ ?_
  · simp; field_simp
  · simp; field_simp; ring

/-! ## The Rotemberg steady state and welfare -/

/-- `u(c) = (e^{(1−σ)c} − 1)/(1 − σ)`. -/
noncomputable def uu (σ c : ℝ) : ℝ := (Real.exp ((1 - σ) * c) - 1) / (1 - σ)

/-- `v(y) = (e^{(1+ω)y} − 1)/(1 + ω)`. -/
noncomputable def vv (ω y : ℝ) : ℝ := (Real.exp ((1 + ω) * y) - 1) / (1 + ω)

/-- Jets of `u ∘ f` with `f 0 = 0`. -/
theorem J_uu {σ : ℝ} (hσ : σ ≠ 1) {f : ℝ → ℝ} {a1 a2 : ℝ} (hf : J2 f a1 a2) (h0 : f 0 = 0) :
    J2 (fun x => uu σ (f x)) a1 ((1 - σ) * a1 * a1 + a2) := by
  have h1 : 1 - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
  have he := J2_expc (J2_const_mul (1 - σ) hf)
  have := J2_const_mul (1 / (1 - σ)) (J2_sub he (J2_const 1))
  refine J2_eq (J2_congr this fun x => by simp only [uu]; ring) ?_ ?_
  · simp [h0]; field_simp
  · simp [h0]; field_simp

/-- Jets of `v ∘ f` with `f 0 = 0`. -/
theorem J_vv {ω : ℝ} (hω : 0 ≤ ω) {f : ℝ → ℝ} {a1 a2 : ℝ} (hf : J2 f a1 a2) (h0 : f 0 = 0) :
    J2 (fun x => vv ω (f x)) a1 ((1 + ω) * a1 * a1 + a2) := by
  have h1 : 1 + ω ≠ 0 := by linarith
  have he := J2_expc (J2_const_mul (1 + ω) hf)
  have := J2_const_mul (1 / (1 + ω)) (J2_sub he (J2_const 1))
  refine J2_eq (J2_congr this fun x => by simp only [vv]; ring) ?_ ?_
  · simp [h0]; field_simp
  · simp [h0]; field_simp

/-- Woodford (2003), Ch. 3, fn. 44: Rotemberg steady-state consumption at trend inflation. -/
noncomputable def cR (p : Par) (π : ℝ) : ℝ := ssY p π + Real.log (wedge p.ψ π)

/-- Woodford (2003), Ch. 6: Rotemberg steady-state welfare at trend inflation. -/
noncomputable def WR (p : Par) (π : ℝ) : ℝ := uu p.σ (cR p π) - p.m * vv p.ω (ssY p π)

/-- The long-run steady-state coefficient `K = (1−β)ψ/(θm)` of the Rotemberg model (not the
slope `κ_R`). -/
noncomputable def KR (p : Par) : ℝ := (1 - p.β) * p.ψ / (p.θ * p.m)

/-- Woodford (2003), Ch. 3, fn. 44 (**the Rotemberg steady-state output curve to second order**):
`ŷ_R′(0) = K/(σ+ω)`, `ŷ_R″(0) = (3K − K² + σψ)/(σ+ω)`. -/
theorem J_YR (hp : p.Basic) :
    J2 (ssY p) (KR p / (p.σ + p.ω)) ((3 * KR p - KR p ^ 2 + p.σ * p.ψ) / (p.σ + p.ω)) := by
  have hs : p.σ + p.ω ≠ 0 := by linarith [hp.σ_pos, hp.ω_nonneg]
  have hin := J2_add (J2_const 1) (J2_const_mul (KR p) J_g)
  have h0 : (0 : ℝ) < (fun x => 1 + KR p * ((Real.exp x - 1) * Real.exp x)) 0 := by simp
  have hl := J2_log hin h0
  have := J2_const_mul (1 / (p.σ + p.ω)) (J2_sub hl (J2_const_mul p.σ (J_lw p.ψ)))
  refine J2_eq (J2_congr this fun x => ?_) ?_ ?_
  · simp only [ssY, KR]; ring_nf
  · simp; field_simp
  · simp; field_simp; ring

/-- Woodford (2003), Ch. 6 (**Rotemberg trend-inflation welfare to second order**). -/
theorem J_WR (hp : p.Basic) (hσ1 : p.σ ≠ 1) :
    J2 (WR p) ((1 - p.m) * (KR p / (p.σ + p.ω)))
      ((1 - p.σ) * (KR p / (p.σ + p.ω)) ^ 2 +
          ((3 * KR p - KR p ^ 2 + p.σ * p.ψ) / (p.σ + p.ω) - p.ψ) -
        p.m * ((1 + p.ω) * (KR p / (p.σ + p.ω)) ^ 2 +
          (3 * KR p - KR p ^ 2 + p.σ * p.ψ) / (p.σ + p.ω))) := by
  have hY := J_YR hp
  have hY0 : ssY p 0 = 0 := by simp [ssY, wedge]
  have hC := J2_add hY (J_lw p.ψ)
  have hC0 : (fun x => ssY p x + Real.log (wedge p.ψ x)) 0 = 0 := by simp [hY0, wedge]
  have hu := J_uu hσ1 hC hC0
  have hv := J_vv hp.ω_nonneg hY hY0
  have := J2_sub hu (J2_const_mul p.m hv)
  refine J2_eq (J2_congr this fun x => rfl) (by ring) (by ring)

/-! ## The Calvo steady state and welfare -/

/-- `log(1 − c e^{eπ})`. -/
noncomputable def ell (c e π : ℝ) : ℝ := Real.log (1 - c * Real.exp (e * π))

/-- Woodford (2003), Ch. 3: the log relative reset price at trend inflation,
`lx = −(log(1 − αe^{(θ−1)π}) − log(1 − α))/(θ − 1)`. -/
noncomputable def lx (p : Par) (α π : ℝ) : ℝ := -(ell α (p.θ - 1) π - Real.log (1 - α)) / (p.θ - 1)

/-- Woodford (2003), Ch. 3: Calvo steady-state output at trend inflation. -/
noncomputable def yC (p : Par) (α π : ℝ) : ℝ :=
  ((1 + p.ω * p.θ) * lx p α π - ell (α * p.β) (p.θ - 1) π + ell (α * p.β) (p.θ * (1 + p.ω)) π) /
    (p.σ + p.ω)

/-- Woodford (2003), App. E.2: log dispersion at trend inflation. -/
noncomputable def LD (p : Par) (α π : ℝ) : ℝ :=
  -(p.θ * (1 + p.ω)) * lx p α π - (ell α (p.θ * (1 + p.ω)) π - Real.log (1 - α))

/-- Woodford (2003), Ch. 3, (2.7)–(2.12) and App. E.2 (**the Calvo steady state at trend
inflation**): the price index `αΠ^{θ−1} + (1−α)x^{1−θ} = 1`, the reset condition
`x^{1+ωθ} = Y^{σ+ω}(1 − αβΠ^{θ−1})/(1 − αβΠ^{θ(1+ω)})` and the stationary dispersion law
`Δ = αΠ^{θ(1+ω)}Δ + (1−α)x^{−θ(1+ω)}` hold with `x = e^{lx}`, `Y = e^{yC}`, `Δ = e^{LD}`. -/
theorem calvo_steady (p : Par) {α : ℝ} (hα1 : α < 1) (hθ : 1 < p.θ) (hs : p.σ + p.ω ≠ 0)
    (π : ℝ) (h1 : 0 < 1 - α * Real.exp ((p.θ - 1) * π))
    (h2 : 0 < 1 - α * Real.exp (p.θ * (1 + p.ω) * π))
    (h3 : 0 < 1 - α * p.β * Real.exp ((p.θ - 1) * π))
    (h4 : 0 < 1 - α * p.β * Real.exp (p.θ * (1 + p.ω) * π)) :
    α * Real.exp ((p.θ - 1) * π) + (1 - α) * Real.exp (-(p.θ - 1) * lx p α π) = 1 ∧
      Real.exp ((1 + p.ω * p.θ) * lx p α π) = Real.exp ((p.σ + p.ω) * yC p α π) *
        (1 - α * p.β * Real.exp ((p.θ - 1) * π)) /
          (1 - α * p.β * Real.exp (p.θ * (1 + p.ω) * π)) ∧
      Real.exp (LD p α π) = α * Real.exp (p.θ * (1 + p.ω) * π) * Real.exp (LD p α π) +
        (1 - α) * Real.exp (-(p.θ * (1 + p.ω)) * lx p α π) := by
  have hb : p.θ - 1 ≠ 0 := by linarith
  have h1α : 0 < 1 - α := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have e : -(p.θ - 1) * lx p α π = ell α (p.θ - 1) π - Real.log (1 - α) := by
      unfold lx; field_simp
    rw [e, Real.exp_sub, ell, Real.exp_log h1, Real.exp_log h1α]
    field_simp; ring
  · have e : (p.σ + p.ω) * yC p α π = (1 + p.ω * p.θ) * lx p α π -
        ell (α * p.β) (p.θ - 1) π + ell (α * p.β) (p.θ * (1 + p.ω)) π := by
      unfold yC; field_simp
    rw [e, Real.exp_add, Real.exp_sub, ell, ell, Real.exp_log h3, Real.exp_log h4]
    have h4' : 1 - α * p.β * Real.exp (p.θ * π * (1 + p.ω)) ≠ 0 := by
      rw [show p.θ * π * (1 + p.ω) = p.θ * (1 + p.ω) * π by ring]; exact h4.ne'
    field_simp
  · have e : LD p α π = -(p.θ * (1 + p.ω)) * lx p α π - (ell α (p.θ * (1 + p.ω)) π -
        Real.log (1 - α)) := rfl
    have hD : Real.exp (LD p α π) * (1 - α * Real.exp (p.θ * (1 + p.ω) * π)) =
        (1 - α) * Real.exp (-(p.θ * (1 + p.ω)) * lx p α π) := by
      rw [e, Real.exp_sub, Real.exp_sub, ell, Real.exp_log h2, Real.exp_log h1α]
      field_simp
    linear_combination hD

/-- Woodford (2003), Ch. 6: Calvo steady-state welfare at trend inflation. -/
noncomputable def WC (p : Par) (α π : ℝ) : ℝ :=
  uu p.σ (yC p α π) - p.m * vv p.ω (yC p α π + LD p α π / (1 + p.ω))

/-- `lx` to second order. -/
theorem J_lx (hθ : 1 < p.θ) {α : ℝ} (hα1 : α < 1) :
    J2 (lx p α) (α / (1 - α)) (α * (p.θ - 1) / (1 - α) ^ 2) := by
  have hb : p.θ - 1 ≠ 0 := by linarith
  have h1 : 1 - α ≠ 0 := by linarith
  have := J2_const_mul (-(1 / (p.θ - 1))) (J2_sub (J_ell (e := p.θ - 1) hα1)
    (J2_const (Real.log (1 - α))))
  refine J2_eq (J2_congr this fun x => by simp only [lx, ell]; ring) ?_ ?_
  · field_simp; ring
  · field_simp; ring

/-- Woodford (2003), Ch. 3 (**the Calvo steady-state output curve to second order**). -/
theorem J_yC (hp : p.Basic) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    J2 (yC p α)
      (((1 + p.ω * p.θ) * (α / (1 - α)) - (-(α * p.β * (p.θ - 1)) / (1 - α * p.β)) +
          (-(α * p.β * (p.θ * (1 + p.ω))) / (1 - α * p.β))) / (p.σ + p.ω))
      (((1 + p.ω * p.θ) * (α * (p.θ - 1) / (1 - α) ^ 2) -
          (-(α * p.β * (p.θ - 1) ^ 2) / (1 - α * p.β) ^ 2) +
          (-(α * p.β * (p.θ * (1 + p.ω)) ^ 2) / (1 - α * p.β) ^ 2)) / (p.σ + p.ω)) := by
  have hθ := hp.one_lt_θ
  have hab : α * p.β < 1 := by nlinarith [hp.β_lt_one, hp.β_pos]
  have := J2_const_mul (1 / (p.σ + p.ω)) (J2_add (J2_sub (J2_const_mul (1 + p.ω * p.θ)
    (J_lx hθ hα1)) (J_ell (e := p.θ - 1) hab)) (J_ell (e := p.θ * (1 + p.ω)) hab))
  refine J2_eq (J2_congr this fun x => by simp only [yC, ell]; ring) (by ring) (by ring)

/-- Woodford (2003), App. E.2 (**log dispersion at trend inflation to second order**):
`LD′(0) = 0`, `LD″(0) = αθ(1+ω)(1+ωθ)/(1−α)²`. -/
theorem J_LD (hp : p.Basic) {α : ℝ} (hα1 : α < 1) :
    J2 (LD p α) 0 (α * (p.θ * (1 + p.ω)) * (1 + p.ω * p.θ) / (1 - α) ^ 2) := by
  have hθ := hp.one_lt_θ
  have h1 : 1 - α ≠ 0 := by linarith
  have := J2_sub (J2_const_mul (-(p.θ * (1 + p.ω))) (J_lx hθ hα1))
    (J2_sub (J_ell (e := p.θ * (1 + p.ω)) hα1) (J2_const (Real.log (1 - α))))
  refine J2_eq (J2_congr this fun x => by simp only [LD, ell]) ?_ ?_
  · field_simp; ring
  · field_simp; ring


/-- Woodford (2003), Ch. 6 (**Calvo trend-inflation welfare to second order**). -/
theorem J_WC (hp : p.Basic) (hσ1 : p.σ ≠ 1) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    J2 (WC p α)
      ((1 - p.m) * (((1 + p.ω * p.θ) * (α / (1 - α)) - (-(α * p.β * (p.θ - 1)) / (1 - α * p.β)) +
          (-(α * p.β * (p.θ * (1 + p.ω))) / (1 - α * p.β))) / (p.σ + p.ω)))
      ((1 - p.σ) * ((((1 + p.ω * p.θ) * (α / (1 - α)) -
          (-(α * p.β * (p.θ - 1)) / (1 - α * p.β)) +
          (-(α * p.β * (p.θ * (1 + p.ω))) / (1 - α * p.β))) / (p.σ + p.ω)) ^ 2) +
        (((1 + p.ω * p.θ) * (α * (p.θ - 1) / (1 - α) ^ 2) -
          (-(α * p.β * (p.θ - 1) ^ 2) / (1 - α * p.β) ^ 2) +
          (-(α * p.β * (p.θ * (1 + p.ω)) ^ 2) / (1 - α * p.β) ^ 2)) / (p.σ + p.ω)) -
        p.m * ((1 + p.ω) * ((((1 + p.ω * p.θ) * (α / (1 - α)) -
          (-(α * p.β * (p.θ - 1)) / (1 - α * p.β)) +
          (-(α * p.β * (p.θ * (1 + p.ω))) / (1 - α * p.β))) / (p.σ + p.ω)) ^ 2) +
          ((((1 + p.ω * p.θ) * (α * (p.θ - 1) / (1 - α) ^ 2) -
            (-(α * p.β * (p.θ - 1) ^ 2) / (1 - α * p.β) ^ 2) +
            (-(α * p.β * (p.θ * (1 + p.ω)) ^ 2) / (1 - α * p.β) ^ 2)) / (p.σ + p.ω)) +
            α * (p.θ * (1 + p.ω)) * (1 + p.ω * p.θ) / (1 - α) ^ 2 / (1 + p.ω)))) := by
  have hy := J_yC hp hα0 hα1
  have hl := J_LD hp hα1
  have hy0 : yC p α 0 = 0 := by simp [yC, lx, ell]
  have hl0 : LD p α 0 = 0 := by simp [LD, lx, ell]
  have hh := J2_add hy (J2_const_mul (1 / (1 + p.ω)) hl)
  have hh0 : (fun x => yC p α x + 1 / (1 + p.ω) * LD p α x) 0 = 0 := by simp [hy0, hl0]
  have hu := J_uu hσ1 hy hy0
  have hv := J_vv hp.ω_nonneg hh hh0
  have := J2_sub hu (J2_const_mul p.m hv)
  refine J2_eq (J2_congr this fun x => by simp only [WC]; ring_nf) (by ring) (by ring)

/-- Woodford (2003), Ch. 6, §2 and §4.1 (**the second-order welfare of trend inflation, Rotemberg
versus Calvo**): under the equivalence map `ψ = θmα(1+ωθ)/((1−α)(1−αβ))`, for every distortion `m`,
the first derivatives at zero inflation coincide, `W′(0) = (1 − m)Y₁` with
`Y₁ = (1−β)α(1+ωθ)/((1−α)(1−αβ)(σ+ω))` (the long-run Phillips-curve slope, equal in both models),
while the second derivatives differ by
`(1 − m)(Y₂ᴿ − Y₂ᶜ) + mθα²(1+ωθ)(1−β)/((1−α)²(1−αβ))`, with `Y₂ᴿ = (3K − K² + σψ)/(σ+ω)`,
`K = (1−β)α(1+ωθ)/((1−α)(1−αβ))`, and `Y₂ᶜ` the second derivative of Calvo steady-state output. -/
theorem trend_welfare (hp : p.Basic) (hσ1 : p.σ ≠ 1) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hψ : p.ψ = p.θ * p.m * α * (1 + p.ω * p.θ) / ((1 - α) * (1 - α * p.β))) :
    deriv (WR p) 0 = (1 - p.m) * ((1 - p.β) * α * (1 + p.ω * p.θ) /
        ((1 - α) * (1 - α * p.β) * (p.σ + p.ω))) ∧
      deriv (WC p α) 0 = (1 - p.m) * ((1 - p.β) * α * (1 + p.ω * p.θ) /
        ((1 - α) * (1 - α * p.β) * (p.σ + p.ω))) ∧
      deriv (deriv (WR p)) 0 - deriv (deriv (WC p α)) 0 =
        (1 - p.m) * ((3 * ((1 - p.β) * α * (1 + p.ω * p.θ) / ((1 - α) * (1 - α * p.β))) -
            ((1 - p.β) * α * (1 + p.ω * p.θ) / ((1 - α) * (1 - α * p.β))) ^ 2 +
            p.σ * p.ψ) / (p.σ + p.ω) -
          ((1 + p.ω * p.θ) * α * (p.θ - 1) / (1 - α) ^ 2 +
            α * p.β * (p.θ - 1) ^ 2 / (1 - α * p.β) ^ 2 -
            α * p.β * (p.θ * (1 + p.ω)) ^ 2 / (1 - α * p.β) ^ 2) / (p.σ + p.ω)) +
        p.m * p.θ * α ^ 2 * (1 + p.ω * p.θ) * (1 - p.β) / ((1 - α) ^ 2 * (1 - α * p.β)) := by
  obtain ⟨r1, r2⟩ := J2_deriv (J_WR hp hσ1)
  obtain ⟨c1, c2⟩ := J2_deriv (J_WC hp hσ1 hα0 hα1)
  have hθ0 : p.θ ≠ 0 := by linarith [hp.one_lt_θ]
  have hm0 : p.m ≠ 0 := hp.m_pos.ne'
  have h1α : 1 - α ≠ 0 := by linarith
  have hab : 1 - α * p.β ≠ 0 := by nlinarith [hp.β_lt_one, hp.β_pos]
  have hs : p.σ + p.ω ≠ 0 := by linarith [hp.σ_pos, hp.ω_nonneg]
  have hω : 1 + p.ω ≠ 0 := by linarith [hp.ω_nonneg]
  have hK : KR p = (1 - p.β) * α * (1 + p.ω * p.θ) / ((1 - α) * (1 - α * p.β)) := by
    unfold KR; rw [hψ]; field_simp
  have hY1 : ((1 + p.ω * p.θ) * (α / (1 - α)) - (-(α * p.β * (p.θ - 1)) / (1 - α * p.β)) +
      (-(α * p.β * (p.θ * (1 + p.ω))) / (1 - α * p.β))) / (p.σ + p.ω) =
      (1 - p.β) * α * (1 + p.ω * p.θ) / ((1 - α) * (1 - α * p.β)) / (p.σ + p.ω) := by
    field_simp; ring
  have key : -p.ψ + p.m * (α * (p.θ * (1 + p.ω)) * (1 + p.ω * p.θ) / (1 - α) ^ 2 / (1 + p.ω)) =
      p.m * p.θ * α ^ 2 * (1 + p.ω * p.θ) * (1 - p.β) / ((1 - α) ^ 2 * (1 - α * p.β)) := by
    rw [hψ]; field_simp; ring
  rw [r1, c1, r2, c2, hK, hY1]
  refine ⟨by field_simp, by field_simp, ?_⟩
  linear_combination key

/-- The second-order difference of `trend_welfare` as a function of the distortion `m` (with `ψ`
moving with `m` through the equivalence map). -/
noncomputable def Dm (β σ ω θ α m : ℝ) : ℝ :=
  (1 - m) * ((3 * ((1 - β) * α * (1 + ω * θ) / ((1 - α) * (1 - α * β))) -
      ((1 - β) * α * (1 + ω * θ) / ((1 - α) * (1 - α * β))) ^ 2 +
      σ * (θ * m * α * (1 + ω * θ) / ((1 - α) * (1 - α * β)))) / (σ + ω) -
    ((1 + ω * θ) * α * (θ - 1) / (1 - α) ^ 2 + α * β * (θ - 1) ^ 2 / (1 - α * β) ^ 2 -
      α * β * (θ * (1 + ω)) ^ 2 / (1 - α * β) ^ 2) / (σ + ω)) +
  m * θ * α ^ 2 * (1 + ω * θ) * (1 - β) / ((1 - α) ^ 2 * (1 - α * β))

/-- `trend_welfare` in terms of `Dm`. -/
theorem trend_welfare_Dm (hp : p.Basic) (hσ1 : p.σ ≠ 1) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hψ : p.ψ = p.θ * p.m * α * (1 + p.ω * p.θ) / ((1 - α) * (1 - α * p.β))) :
    deriv (deriv (WR p)) 0 - deriv (deriv (WC p α)) 0 = Dm p.β p.σ p.ω p.θ α p.m := by
  rw [(trend_welfare hp hσ1 hα0 hα1 hψ).2.2, hψ]; rfl

/-- Woodford (2003), Ch. 6, §2 and §4.1 (**the second-order totals do NOT coincide**): with
`0 < α < 1`, `0 < β < 1`, `θ > 1`, `ω ≥ 0`, the difference is strictly positive at
`m = 1` (no distortion: Calvo's dispersion accumulates at rate `α` against the Rotemberg cost
discounted at `αβ`), and it vanishes for at most two values of `m`. -/
theorem trend_welfare_differ {β σ ω θ α : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hω : 0 ≤ ω) (hθ : 1 < θ) (hα0 : 0 < α) (hα1 : α < 1) :
    0 < Dm β σ ω θ α 1 ∧ ∀ m1 m2 m3 : ℝ, m1 ≠ m2 → m1 ≠ m3 → m2 ≠ m3 →
      Dm β σ ω θ α m1 = 0 → Dm β σ ω θ α m2 = 0 → Dm β σ ω θ α m3 = 0 → False := by
  have h1α : 0 < 1 - α := by linarith
  have hab : 0 < 1 - α * β := by nlinarith
  have hd : 0 < 1 + ω * θ := by nlinarith
  have hF : 0 < θ * α ^ 2 * (1 + ω * θ) * (1 - β) / ((1 - α) ^ 2 * (1 - α * β)) := by
    have : 0 < 1 - β := by linarith
    have : 0 < θ := by linarith
    positivity
  have hD1 : Dm β σ ω θ α 1 = θ * α ^ 2 * (1 + ω * θ) * (1 - β) / ((1 - α) ^ 2 * (1 - α * β)) := by
    unfold Dm; ring
  refine ⟨by rw [hD1]; exact hF, fun m1 m2 m3 h12 h13 h23 e1 e2 e3 => ?_⟩
  -- `Dm` is a quadratic in `m`
  obtain ⟨c0, c1, c2, hq⟩ : ∃ c0 c1 c2 : ℝ, ∀ m, Dm β σ ω θ α m = c0 + c1 * m + c2 * m ^ 2 := by
    refine ⟨Dm β σ ω θ α 0, Dm β σ ω θ α 1 - Dm β σ ω θ α 0 -
      (-(σ * (θ * α * (1 + ω * θ) / ((1 - α) * (1 - α * β))) / (σ + ω))),
      -(σ * (θ * α * (1 + ω * θ) / ((1 - α) * (1 - α * β))) / (σ + ω)), fun m => ?_⟩
    unfold Dm; ring
  rw [hq] at e1 e2 e3
  have s12 : c1 + c2 * (m1 + m2) = 0 := by
    have : (m1 - m2) * (c1 + c2 * (m1 + m2)) = 0 := by linear_combination e1 - e2
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h12)
  have s13 : c1 + c2 * (m1 + m3) = 0 := by
    have : (m1 - m3) * (c1 + c2 * (m1 + m3)) = 0 := by linear_combination e1 - e3
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h13)
  have hc2 : c2 = 0 := by
    have : (m2 - m3) * c2 = 0 := by linear_combination s12 - s13
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h23)
  have hc1 : c1 = 0 := by rw [hc2] at s12; linarith
  have hc0 : c0 = 0 := by rw [hc1, hc2] at e1; linarith
  have := hq 1
  rw [hc0, hc1, hc2, hD1] at this
  linarith

end Woodford.StabilizationWelfare.NonlinearRotembergTrendWelfare
