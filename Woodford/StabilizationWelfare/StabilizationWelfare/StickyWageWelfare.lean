/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TwoSectorWelfare

/-!
# Sticky wages and prices: welfare

Woodford (2003), *Interest and Prices*, Chapter 6, §4.4 "Sticky Wages and Prices",
pp. 443–448, and Appendix E, §E.8, pp. 707–708.

The welfare approximation for the Erceg–Henderson–Levin model of Chapter 3, §4 (staggered
wages and prices): Proposition 6.12 (period utility), Proposition 6.13 (the discounted loss with
price- and wage-inflation terms; the book omits the proof, which is supplied here) and the
discussion that follows. Chapter 3's Proposition 3.9 and (4.13)–(4.15) are restated as
hypotheses; the cross-sectional, Calvo and discounting machinery is imported from
`TwoSectorWelfare` (same chain).

## Main results

* Exact derivatives: `vhTaylor_coeffs`, `vhTaylor_ray` ((E.34) including the shock term
  `−νh̄ĥ`, via `ray_taylor`), `hasDerivAt_v_exp`, `v_exp_second` ((E.34): `ĥ + ½(1 + ν)ĥ²`),
  `finv_derivs`, `labor_requirement_coeffs` ((E.36): `f⁻¹(ȳeᵘ)/H̄ = 1 + φ_h u + ½φ_h(1 + ω_p)u²`
  to second order, with `φ_h = Ȳ/(H̄f')`, `ω_p = −f''Ȳ/(f')²`), `logMean_derivs`
  (`log E G(ε u)` has derivatives `g₁E u` and `g₂E u² − g₁²(E u)²`).
* (E.34): `Tvh`, `TvhMom`, `sum_Tvh`, `labor_demand_moments` (`var log h = θ_w² var log w`),
  `relative_wage_mean`, `E34`, `E34_population`.
* (E.36): `HT`, `HT_eq_taylor`, `H2`, `R36`, `E36`.
* **Proposition 6.12, Layer A**: `steady_state_vh` (`H̄v_h = (1 − Φ)Ȳu_c/φ_h`),
  `prop_6_12_layerA` (exact identity with explicit t.i.p. `tip612` and remainder `R612`),
  `R612_scale`, `R612_isBigO`.
* **Proposition 6.13**: `Dsum` (`ξ_p`, `ξ_w` are the Calvo slopes `Moments.calvoXi`), `lamP`,
  `lamW`, `lamX613`, `loss429`,
  `lamP_add_lamW`, `weights613_pos`, `calvo_coeff613` (dispersion weights become `θ_p/ξ_p` and
  `θ_wφ_h⁻¹/ξ_w`), `prop_6_13`, and `prop_6_13_calvo` (from the price and wage Calvo
  processes of `TwoSectorWelfare`).
* Discussion: `eq_4_30`, `weighted_sq_identity'`, `weights_equal_theta` (`λ_x = κ/θ`),
  `kappaW_eq_kappaP_iff`, `lamW_critical_value` (`.30/.63 = 10/21 ≈ .48`), `table_6_4_values`,
  `xi_sum_eq`, `fn66_value` (`32.4`), `tendsto_xi_inv`, `lam_flexible_limits`, `loss429_nonneg`,
  `pibar_pc` ((4.14) restated), `gap_iff_pibar_wages` (`φ = λ_p`), `realWage_policy_invariant`,
  `pibar_stabilisation_optimal`.

## Corrections and remarks

* (E.33), (E.36), p. 445 (`λ_w`) and p. 446 (survey error 28, cosmetic): `φ` is printed where
  `φ_h` (the inverse output elasticity of labour) is meant; (E.36) also writes `f⁻¹(y_t(i))` for
  `f⁻¹(y_t(i)/A_t)`.
* (E.33) (survey item): the final combination is only asserted ("I obtain"); it is proved here
  (`prop_6_12_layerA`), the coefficient of `Ŷ²` reducing to `½(1 + ω_p + νφ_h) = ½(1 + ω)`.
* Proposition 6.13 (survey error 27): the proof is omitted in the book ("I omit details"); it is
  supplied in `prop_6_13`, and the printed weights are confirmed.
* Table 6.4 (pp. 446–447): `(σ⁻¹ + ω)/κ` with the rounded Table 5.1 values is `26.25`, not the
  printed `26.7`; the printed value is consistent with `κ ≈ .0236` (which rounds to `.024`) and
  with the printed `λ_x = .048` (`table_6_4_values`).
-/

namespace Woodford.StabilizationWelfare.StickyWageWelfare

open Filter Topology
open Woodford.StabilizationWelfare.TwoSectorWelfare
open Sequences hiding dispersion_tsum
open ExpLogCES (crossMean crossVar crossVar_eq)
open Moments (crossMean_affine crossVar_affine mean_quadratic calvoXi)
open Prop61 (Tu xStarLin)

variable {ι : Type*} [Fintype ι]

/-! ### Exact derivatives behind (E.34) and (E.36) -/

/-- Woodford (2003), (E.34), p. 707: along `h = H̄ exp(ε ĥ)` the disutility `v(h)` has first
derivative `v'(h) h ĥ` (with respect to `ε`). -/
theorem hasDerivAt_v_exp {v v' : ℝ → ℝ} (hv : ∀ x, HasDerivAt v (v' x) x) (Hbar hh ε : ℝ) :
    HasDerivAt (fun e => v (Hbar * Real.exp (e * hh)))
      (v' (Hbar * Real.exp (ε * hh)) * (Hbar * Real.exp (ε * hh) * hh)) ε := by
  have h1 : HasDerivAt (fun e => Hbar * Real.exp (e * hh)) (Hbar * (Real.exp (ε * hh) * hh)) ε :=
    (((hasDerivAt_id ε).mul_const hh).exp.congr_deriv (by simp)).const_mul Hbar
  exact ((hv _).comp ε h1).congr_deriv (by ring)

/-- Woodford (2003), (E.34), p. 707 (**exact derivative**): the second derivative at `ε = 0` of
`ε ↦ v(H̄ exp(ε ĥ))` is `H̄ v_h (1 + ν) ĥ²`, with `ν = H̄ v_hh / v_h`; so the Taylor polynomial
in units of `H̄ v_h` is `ĥ + ½(1 + ν) ĥ²`. -/
theorem v_exp_second {v' : ℝ → ℝ} {v2 Hbar : ℝ} (hv' : HasDerivAt v' v2 Hbar)
    (hvh : v' Hbar ≠ 0) (hh : ℝ) :
    HasDerivAt (fun e => v' (Hbar * Real.exp (e * hh)) * (Hbar * Real.exp (e * hh) * hh))
      (Hbar * v' Hbar * (1 + Hbar * v2 / v' Hbar) * hh ^ 2) 0 := by
  have h1 : HasDerivAt (fun e => Hbar * Real.exp (e * hh)) (Hbar * (Real.exp (0 * hh) * hh)) 0 :=
    (((hasDerivAt_id (0 : ℝ)).mul_const hh).exp.congr_deriv (by simp)).const_mul Hbar
  have h1' : HasDerivAt (fun e => Hbar * Real.exp (e * hh) * hh)
      (Hbar * (Real.exp (0 * hh) * hh) * hh) 0 := h1.mul_const hh
  have hv'' : HasDerivAt v' v2 (Hbar * Real.exp (0 * hh)) := by simpa using hv'
  have h2 := (hv''.comp 0 h1).mul h1'
  refine h2.congr_deriv ?_
  simp only [zero_mul, Real.exp_zero, mul_one, Function.comp]
  field_simp
  ring

/-- Woodford (2003), (E.36), p. 708 (**inverse-function derivatives**): if `f ∘ f⁻¹ = id`,
`f` has derivative `f'` everywhere, `f'` has derivative `f₂` at `H̄ = f⁻¹(ȳ)` and `f⁻¹` has
derivative `d₁` with `d₁` differentiable at `ȳ` (derivative `d₂`), then `f'(H̄) d₁(ȳ) = 1` and
`d₂ = −f₂ d₁(ȳ)²/f'(H̄)`, i.e. `d₁ = 1/f'` and `d₂ = −f''/(f')³`. -/
theorem finv_derivs {f finv f' d1 : ℝ → ℝ} {f2 d2 ybar : ℝ} (hinv : ∀ y, f (finv y) = y)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : HasDerivAt f' f2 (finv ybar))
    (hd : ∀ y, HasDerivAt finv (d1 y) y) (hd1 : HasDerivAt d1 d2 ybar) :
    f' (finv ybar) * d1 ybar = 1 ∧ f2 * d1 ybar * d1 ybar + f' (finv ybar) * d2 = 0 := by
  have hone : ∀ y, f' (finv y) * d1 y = 1 := by
    intro y
    have h1 : HasDerivAt (f ∘ finv) (f' (finv y) * d1 y) y := (hf (finv y)).comp y (hd y)
    have h2 : HasDerivAt (f ∘ finv) 1 y := by
      have : (f ∘ finv) = id := funext fun y => hinv y
      rw [this]; exact hasDerivAt_id y
    exact h1.unique h2
  refine ⟨hone ybar, ?_⟩
  have h3 : HasDerivAt (fun y => f' (finv y) * d1 y) (f2 * d1 ybar * d1 ybar + f' (finv ybar) * d2)
      ybar := by
    have := (hf'.comp ybar (hd ybar)).mul hd1
    refine this.congr_deriv ?_
    simp only [Function.comp]
  have h4 : HasDerivAt (fun y => f' (finv y) * d1 y) 0 ybar := by
    have : (fun y => f' (finv y) * d1 y) = fun _ => (1 : ℝ) := funext hone
    rw [this]; exact hasDerivAt_const _ _
  exact h3.unique h4

/-- Woodford (2003), (E.36), p. 708 (**exact derivatives of the labour requirement**): with
`G(u) = f⁻¹(ȳ eᵘ)/H̄`, `ȳ = f(H̄)`, `φ_h = ȳ/(H̄ f'(H̄))` and `ω_p = −f''(H̄) ȳ/f'(H̄)²`:
`G(0) = 1`, `G'(0) = φ_h`, `G''(0) = φ_h(1 + ω_p)`; i.e.
`f⁻¹(y(i)) = H̄[1 + φ_h ŷ + ½(1 + ω_p)φ_h ŷ² + O(ŷ³)]`. -/
theorem labor_requirement_coeffs {f finv f' d1 : ℝ → ℝ} {f2 d2 ybar Hbar : ℝ}
    (hinv : ∀ y, f (finv y) = y) (hf : ∀ x, HasDerivAt f (f' x) x) (hH : finv ybar = Hbar)
    (hHpos : Hbar ≠ 0) (hf' : HasDerivAt f' f2 Hbar) (hd : ∀ y, HasDerivAt finv (d1 y) y)
    (hd1 : HasDerivAt d1 d2 ybar) :
    let G' := fun u => d1 (ybar * Real.exp u) * (ybar * Real.exp u) / Hbar
    (fun u => finv (ybar * Real.exp u) / Hbar) 0 = 1 ∧
      (∀ u, HasDerivAt (fun u => finv (ybar * Real.exp u) / Hbar) (G' u) u) ∧
      G' 0 = ybar / (Hbar * f' Hbar) ∧
      HasDerivAt G' (ybar / (Hbar * f' Hbar) * (1 + -(f2 * ybar / f' Hbar ^ 2))) 0 := by
  intro G'
  obtain ⟨e1, e2⟩ := finv_derivs hinv hf (hH ▸ hf') hd hd1
  rw [hH] at e1 e2
  have hf0 : f' Hbar ≠ 0 := by intro h; rw [h, zero_mul] at e1; exact zero_ne_one e1
  have hd1v : d1 ybar = 1 / f' Hbar := by field_simp; linear_combination e1
  have hd2v : d2 = -f2 / f' Hbar ^ 3 := by
    rw [hd1v] at e2; field_simp at e2 ⊢; linear_combination e2
  have hexp : ∀ u, HasDerivAt (fun u => ybar * Real.exp u) (ybar * Real.exp u) u :=
    fun u => (Real.hasDerivAt_exp u).const_mul ybar
  refine ⟨by simp [hH, hHpos], fun u => ?_, ?_, ?_⟩
  · exact (((hd _).comp u (hexp u)).div_const Hbar).congr_deriv (by simp [G'])
  · simp only [G', Real.exp_zero, mul_one, hd1v]
    field_simp
  · have hd1' : HasDerivAt d1 d2 (ybar * Real.exp 0) := by simpa using hd1
    have h := ((hd1'.comp 0 (hexp 0)).mul (hexp 0)).div_const Hbar
    refine h.congr_deriv ?_
    simp only [Function.comp_apply, Real.exp_zero, mul_one]
    rw [hd1v, hd2v]
    field_simp
    ring

/-- Woodford (2003), (E.36), p. 708 (**exact derivatives of the aggregate labour input**): for
weights `w` summing to one and a function `G` with `G(0) = 1`, `G' (0) = g₁`, `G''(0) = g₂`,
`K(ε) = log ∑ w_i G(ε u_i)` has `K'(0) = g₁ E u` and `K''(0) = g₂ E u² − g₁² (E u)²`. -/
theorem logMean_derivs {w u : ι → ℝ} (hw : ∑ i, w i = 1) {G G' : ℝ → ℝ} {g2 : ℝ}
    (hG : ∀ x, HasDerivAt G (G' x) x) (hG' : HasDerivAt G' g2 0) (hG0 : G 0 = 1) :
    (∀ ε, ∑ i, w i * G (ε * u i) ≠ 0 →
        HasDerivAt (fun e => Real.log (∑ i, w i * G (e * u i)))
          ((∑ i, w i * u i * G' (ε * u i)) / ∑ i, w i * G (ε * u i)) ε) ∧
      (∑ i, w i * u i * G' (0 * u i)) / ∑ i, w i * G (0 * u i) = G' 0 * crossMean w u ∧
      HasDerivAt (fun e => (∑ i, w i * u i * G' (e * u i)) / ∑ i, w i * G (e * u i))
        (g2 * ∑ i, w i * u i ^ 2 - G' 0 ^ 2 * crossMean w u ^ 2) 0 := by
  have hS : ∀ ε, HasDerivAt (fun e => ∑ i, w i * G (e * u i))
      (∑ i, w i * u i * G' (ε * u i)) ε := by
    intro ε
    have : ∀ i ∈ Finset.univ, HasDerivAt (fun e => w i * G (e * u i))
        (w i * (G' (ε * u i) * u i)) ε := fun i _ =>
      (((hG _).comp ε ((hasDerivAt_id ε).mul_const (u i))).congr_deriv (by simp)).const_mul _
    exact (HasDerivAt.fun_sum this).congr_deriv (Finset.sum_congr rfl fun i _ => by ring)
  have hS' : HasDerivAt (fun e => ∑ i, w i * u i * G' (e * u i))
      (∑ i, w i * u i * (g2 * u i)) 0 := by
    have : ∀ i ∈ Finset.univ, HasDerivAt (fun e => w i * u i * G' (e * u i))
        (w i * u i * (g2 * u i)) 0 := fun i _ => by
      have hc : HasDerivAt G' g2 ((0 : ℝ) * u i) := by simpa using hG'
      exact ((hc.comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).mul_const (u i))).congr_deriv
        (by simp)).const_mul _
    exact HasDerivAt.fun_sum this
  have hS0 : ∑ i, w i * G (0 * u i) = 1 := by simp [hG0, hw]
  refine ⟨fun ε hε => (hS ε).log hε, ?_, ?_⟩
  · rw [hS0, div_one]
    simp only [zero_mul, crossMean, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · refine (hS'.div (hS 0) (by rw [hS0]; exact one_ne_zero)).congr_deriv ?_
    rw [hS0]
    simp only [zero_mul, crossMean, one_pow, div_one, mul_one]
    have e1 : ∑ i, w i * u i * (g2 * u i) = g2 * ∑ i, w i * u i ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i, w i * u i * G' 0 = G' 0 * ∑ i, w i * u i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2]
    ring

/-! ### Proposition 6.12, Layer A: (E.34)–(E.36)

Units: `Ȳ u_c` for utility, `H̄ v_h` inside (E.34). Endogenous: `Ŷ`, the price dispersion
`V_p = var_i log p(i)` and the wage dispersion `V_w = var_j log w(j)`; exogenous: `g`, `a`
(technology), `h̄` (labour-supply shock) and the distortion `Φ`. Weighted degree: `Ŷ, g, a, h̄, Φ`
one; `V_p, V_w` two. -/

/-- Woodford (2003), (E.34), p. 707: the second-order Taylor polynomial of `v(h(j); ξ)` in
units of `H̄ v_h`, `ĥ + ½(1 + ν)ĥ² − ν h̄ ĥ` (`v_exp_second`). -/
noncomputable def Tvh (ν hb hh : ℝ) : ℝ := hh + (1 + ν) / 2 * hh ^ 2 - ν * hb * hh

/-- Woodford (2003), eq. (E.34), p. 707 (**exact Taylor coefficients of `v` in the shock**):
with `v_h = W_X(H̄, 0)`, `v_hh = W_XX`, `v_hξ ξ = ½(W_Xξ + W_ξX)ξ`, `ν = H̄v_hh/v_h` and
`h̄ = −v_hξ ξ/(H̄v_hh)`, the second-order Taylor polynomial along `(H̄e^{εĥ}, εξ)` is
`(v_ξξ + ½v_ξξξ²) + H̄v_h[ĥ + ½(1 + ν)ĥ² − νh̄ĥ]`. -/
theorem vhTaylor_coeffs {Hbar vh vhh cross vξ vξξ : ℝ} (hH : Hbar ≠ 0) (hvh : vh ≠ 0)
    (hvhh : vhh ≠ 0) (hh ξ : ℝ) :
    (Hbar * vh * hh + vξ * ξ) +
        ((Hbar ^ 2 * vhh + Hbar * vh) * hh ^ 2 + Hbar * (2 * cross) * hh * ξ + vξξ * ξ ^ 2) / 2 =
      (vξ * ξ + vξξ / 2 * ξ ^ 2) +
        Hbar * vh * Tvh (Hbar * vhh / vh) (-(cross * ξ / (Hbar * vhh))) hh := by
  unfold Tvh
  field_simp
  ring

/-- Woodford (2003), eq. (E.34), p. 707 (**`v` from the primitive**): for `v(h, ξ)` with the
differentiability of `ray_taylor`, `F(ε) = v(H̄e^{εĥ}, εξ)` satisfies
`F'(0) + ½F''(0) = (v_ξξ + ½v_ξξξ²) + H̄v_h Tvh(ν, h̄, ĥ)`. -/
theorem vhTaylor_ray {v vh vξ : ℝ × ℝ → ℝ} {Hbar vhh vhξ vξh vξξ : ℝ} (hH : Hbar ≠ 0)
    (hvh : vh (Hbar, 0) ≠ 0) (hvhh : vhh ≠ 0) (hh ξ : ℝ)
    (hv : ∀ p, HasFDerivAt v (vh p • ContinuousLinearMap.fst ℝ ℝ ℝ +
      vξ p • ContinuousLinearMap.snd ℝ ℝ ℝ) p)
    (hvH : HasFDerivAt vh (vhh • ContinuousLinearMap.fst ℝ ℝ ℝ +
      vhξ • ContinuousLinearMap.snd ℝ ℝ ℝ) (Hbar, 0))
    (hvξ : HasFDerivAt vξ (vξh • ContinuousLinearMap.fst ℝ ℝ ℝ +
      vξξ • ContinuousLinearMap.snd ℝ ℝ ℝ) (Hbar, 0)) :
    let F' := fun e => vh (Hbar * Real.exp (e * hh), e * ξ) * (Hbar * Real.exp (e * hh) * hh) +
      vξ (Hbar * Real.exp (e * hh), e * ξ) * ξ
    let B := (Hbar ^ 2 * vhh + Hbar * vh (Hbar, 0)) * hh ^ 2 + Hbar * (vhξ + vξh) * hh * ξ +
      vξξ * ξ ^ 2
    (∀ ε, HasDerivAt (fun e => v (Hbar * Real.exp (e * hh), e * ξ)) (F' ε) ε) ∧
      HasDerivAt F' B 0 ∧
      F' 0 + B / 2 = (vξ (Hbar, 0) * ξ + vξξ / 2 * ξ ^ 2) + Hbar * vh (Hbar, 0) *
        Tvh (Hbar * vhh / vh (Hbar, 0)) (-((vhξ + vξh) / 2 * ξ / (Hbar * vhh))) hh := by
  intro F' B
  obtain ⟨h1, h2⟩ := ray_taylor hh ξ hv hvH hvξ
  refine ⟨h1, h2, ?_⟩
  have e := vhTaylor_coeffs (cross := (vhξ + vξh) / 2) (vξ := vξ (Hbar, 0)) (vξξ := vξξ) hH hvh
    hvhh hh ξ
  simp only [F', B, zero_mul, Real.exp_zero, mul_one]
  rw [← e]; ring

/-- Woodford (2003), (E.34): `Tvh` integrated over labour types, in terms of the mean `m` and
variance `V` of `ĥ(j)`. -/
noncomputable def TvhMom (ν hb m V : ℝ) : ℝ := m + (1 + ν) / 2 * (m ^ 2 + V) - ν * hb * m

/-- Woodford (2003), (E.34), p. 707: `∑ w_j Tvh(ĥ_j) = TvhMom(E ĥ, var ĥ)`. -/
theorem sum_Tvh {w : ι → ℝ} (hw : ∑ i, w i = 1) (ν hb : ℝ) (hh : ι → ℝ) :
    ∑ i, w i * Tvh ν hb (hh i) = TvhMom ν hb (crossMean w hh) (crossVar w hh) := by
  have h : ∀ i, w i * Tvh ν hb (hh i) = w i * ((1 - ν * hb) * hh i + (1 + ν) / 2 * hh i ^ 2) :=
    fun i => by unfold Tvh; ring
  simp only [h, mean_quadratic hw]
  unfold TvhMom; ring

/-- Woodford (2003), eq. (4.27), p. 443 and (E.34): labour demands `h(j) = H (w(j)/W)^{−θ_w}`
give `ĥ(j) = Ĥ − θ_w ŵ(j)` with `ŵ(j) = log(w(j)/W)`, so `E ĥ = Ĥ − θ_w E ŵ` and
`var ĥ = θ_w² var ŵ` (the book's "`var_j log h = θ_w² var_j log w`"). -/
theorem labor_demand_moments {w : ι → ℝ} (hw : ∑ i, w i = 1) (H θw : ℝ) (wh : ι → ℝ) :
    crossMean w (fun j => H + -θw * wh j) = H - θw * crossMean w wh ∧
      crossVar w (fun j => H + -θw * wh j) = θw ^ 2 * crossVar w wh := by
  rw [crossMean_affine hw, crossVar_affine hw, neg_sq]
  exact ⟨by ring, rfl⟩

/-- Woodford (2003), (E.34): the wage index `W = (∫ w(j)^{1−θ_w})^{1/(1−θ_w)}` has, to second
order (`ces_taylor` with `r = 1 − θ_w`), `log W = E log w + ½(1 − θ_w) var log w`; then the
relative wages `ŵ(j) = log w(j) − log W` satisfy `E ŵ = −½(1 − θ_w) var ŵ`. -/
theorem relative_wage_mean {w : ι → ℝ} (hw : ∑ i, w i = 1) {θw lW : ℝ} (lw : ι → ℝ)
    (hW : lW = crossMean w lw + (1 - θw) / 2 * crossVar w lw) :
    crossMean w (fun j => -lW + 1 * lw j) =
      -((1 - θw) / 2) * crossVar w (fun j => -lW + 1 * lw j) := by
  rw [crossMean_affine hw, crossVar_affine hw, hW]; ring

/-- Woodford (2003), (E.34), p. 707: the third-order remainder of the integrated wage-side
expansion. -/
noncomputable def R34 (ν θw H hb Vw : ℝ) : ℝ :=
  (1 + ν) / 2 * θw * (1 - θw) * H * Vw + (1 + ν) / 8 * θw ^ 2 * (1 - θw) ^ 2 * Vw ^ 2 -
    ν * hb * θw * (1 - θw) / 2 * Vw

/-- Woodford (2003), **(E.34)**, p. 707 (exact): with `E ĥ = Ĥ − θ_w E ŵ`, `var ĥ = θ_w² V_w` and
`E ŵ = −½(1 − θ_w)V_w`, the integrated disutility is
`Ĥ + ½(1 + ν)Ĥ² − νh̄Ĥ + ½θ_w(1 + νθ_w)V_w + R34`. -/
theorem E34 (ν θw H hb Vw : ℝ) :
    TvhMom ν hb (H - θw * (-((1 - θw) / 2) * Vw)) (θw ^ 2 * Vw) =
      H + (1 + ν) / 2 * H ^ 2 - ν * hb * H + θw * (1 + ν * θw) / 2 * Vw + R34 ν θw H hb Vw := by
  unfold TvhMom R34; ring

/-- Woodford (2003), (E.36), first line, p. 708: the second-order polynomial
`φ_h(m − a) + ½(1 + ω_p − φ_h)φ_h(m − a)² + ½(1 + ω_p)φ_h V` in the mean `m = E_i ŷ` and the
variance `V = var_i ŷ`. -/
noncomputable def HT (φh ωp m a V : ℝ) : ℝ :=
  φh * (m - a) + (1 + ωp - φh) * φh / 2 * (m - a) ^ 2 + (1 + ωp) * φh / 2 * V

/-- Woodford (2003), (E.36), p. 708: `HT` is exactly the second-order Taylor polynomial of
`Ĥ = log E_i G(ŷ_i − a)` given by `logMean_derivs` and `labor_requirement_coeffs`
(`g₁ = φ_h`, `g₂ = φ_h(1 + ω_p)`): `g₁ E u + ½(g₂ E u² − g₁²(E u)²)` with `E u = m − a`,
`E u² = (m − a)² + V`. -/
theorem HT_eq_taylor (φh ωp m a V : ℝ) :
    φh * (m - a) + (φh * (1 + ωp) * ((m - a) ^ 2 + V) - φh ^ 2 * (m - a) ^ 2) / 2 =
      HT φh ωp m a V := by
  unfold HT; ring

/-- Woodford (2003), (E.36), second line: the policy-relevant polynomial
`φ_h(Ŷ − a) + ½(1 + ω_p − φ_h)φ_h(Ŷ − a)² + ½(1 + ω_pθ_p)θ_pφ_h V_p`. -/
noncomputable def H2 (φh ωp θp u Vp : ℝ) : ℝ :=
  φh * u + (1 + ωp - φh) * φh / 2 * u ^ 2 + (1 + ωp * θp) * θp * φh / 2 * Vp

/-- Woodford (2003), (E.36), p. 708: the third-order remainder created by (E.5)
(`k = θ_p(θ_p − 1)/2`, `u = Ŷ − a`). -/
noncomputable def R36 (φh ωp θp u Vp : ℝ) : ℝ :=
  -((1 + ωp - φh) * φh * (θp * (θp - 1) / 2) * u * Vp) +
    (1 + ωp - φh) * φh / 2 * (θp * (θp - 1) / 2) ^ 2 * Vp ^ 2

/-- Woodford (2003), **(E.36)**, p. 708 (exact): substituting (E.5),
`E_i ŷ = Ŷ − ½(1 − θ_p⁻¹) var_i ŷ`, and (2.12), `var_i ŷ = θ_p² var_i log p`, into the first
line gives the second line plus `R36`. -/
theorem E36 {θp : ℝ} (hθ : θp ≠ 0) (φh ωp Y a Vp : ℝ) :
    HT φh ωp (meanE28 θp⁻¹ Y (θp ^ 2 * Vp)) a (θp ^ 2 * Vp) =
      H2 φh ωp θp (Y - a) Vp + R36 φh ωp θp (Y - a) Vp := by
  unfold HT meanE28 H2 R36
  field_simp
  ring

/-- Woodford (2003), (E.34): the integrated wage-side polynomial
`W34 = Ĥ + ½(1 + ν)Ĥ² − νh̄Ĥ + ½θ_w(1 + νθ_w)V_w`. -/
noncomputable def W34 (ν θw H hb Vw : ℝ) : ℝ :=
  H + (1 + ν) / 2 * H ^ 2 - ν * hb * H + θw * (1 + ν * θw) / 2 * Vw

/-- Woodford (2003), (E.36): the second-order-and-higher part of `Ĥ`,
`E₂ = Ĥ − φ_h(Ŷ − a)`. -/
noncomputable def E2 (φh ωp θp u Vp : ℝ) : ℝ :=
  (1 + ωp - φh) * φh / 2 * u ^ 2 + (1 + ωp * θp) * θp * φh / 2 * Vp + R36 φh ωp θp u Vp

/-- Woodford (2003), (E.33): the cubic cross terms of `W34` when `Ĥ = φ_h u + E₂`. -/
noncomputable def C3 (ν φh hb u e2 : ℝ) : ℝ :=
  (1 + ν) * φh * u * e2 + (1 + ν) / 2 * e2 ^ 2 - ν * hb * e2

/-- Woodford (2003), (E.33): the quadratic terms multiplied by `Φ`. -/
noncomputable def Q2 (ω ν θp ωp θw φh u hb Vp Vw : ℝ) : ℝ :=
  (1 + ω) / 2 * u ^ 2 - ν * hb * u + θp * (1 + ωp * θp) / 2 * Vp +
    θw * (1 + ν * θw) / (2 * φh) * Vw

/-- Woodford (2003), (E.33), p. 707: the explicit remainder `O(‖Φ, Ŷ, p̂, ŵ, ξ̃‖³)`. -/
noncomputable def R612 (ω ν θp ωp θw φh Phi Y a hb Vp Vw : ℝ) : ℝ :=
  Phi * Q2 ω ν θp ωp θw φh (Y - a) hb Vp Vw -
    (1 - Phi) / φh * (C3 ν φh hb (Y - a) (E2 φh ωp θp (Y - a) Vp) + R36 φh ωp θp (Y - a) Vp +
      R34 ν θw (φh * (Y - a) + E2 φh ωp θp (Y - a) Vp) hb Vw)

/-- Woodford (2003), p. 225 (Chapter 3) and (E.33): the natural rate of output in the sticky-wage
model, `Ŷⁿ = (σ⁻¹g + (1 + ω)a + νh̄)/(σ⁻¹ + ω)`, `ω = ω_p + νφ_h`. -/
noncomputable def natY612 (σi ω ν g a hb : ℝ) : ℝ := (σi * g + (1 + ω) * a + ν * hb) / (σi + ω)

/-- Woodford (2003), (E.33): the terms independent of policy (functions of `g, a, h̄, Φ`). -/
noncomputable def tip612 (σi ω ν Phi g a hb : ℝ) : ℝ :=
  (Phi + σi * g + (1 + ω) * a + ν * hb) ^ 2 / (2 * (σi + ω)) + a - (1 + ω) / 2 * a ^ 2 -
    ν * hb * a - Phi * a

/-- Woodford (2003), (E.33) (steady state): with `v_h = (1 − Φ) u_c f'(H̄)` (the definition of
`Φ` through `v_y = v_h/f' = (1 − Φ)u_c`) and `φ_h = Ȳ/(H̄ f'(H̄))`,
`H̄ v_h = (1 − Φ) Ȳ u_c / φ_h`. -/
theorem steady_state_vh {Hbar Ybar vh uc fp Phi : ℝ} (hH : Hbar ≠ 0) (hf : fp ≠ 0)
    (hY : Ybar ≠ 0) (hss : vh = (1 - Phi) * uc * fp) :
    Hbar * vh = (1 - Phi) * Ybar * uc / (Ybar / (Hbar * fp)) := by
  rw [hss]; field_simp

/-- Woodford (2003), **Proposition 6.12**, eq. (4.28), p. 444 and (E.33), p. 707 (**Layer A**):
with `Ĥ` the (E.36) polynomial (after (E.5) and (2.12)), the wage side (E.34) and
`H̄v_h = (1 − Φ)Ȳu_c/φ_h`, the second-order utility in units of `Ȳu_c` is
`−½[(σ⁻¹ + ω)(Ŷ − Ŷⁿ − x*)² + θ_p(1 + ω_pθ_p) var_i log p + θ_wφ_h⁻¹(1 + νθ_w) var_j log w]`
`+ t.i.p. + R612`, `ω = ω_p + νφ_h`. -/
theorem prop_6_12_layerA {σi ω ν θp ωp θw φh : ℝ} (hω : ω = ωp + ν * φh) (hφ : φh ≠ 0)
    (hσω : σi + ω ≠ 0) (hθ : θp ≠ 0) (Phi Y g a hb Vp Vw : ℝ) :
    let H := HT φh ωp (meanE28 θp⁻¹ Y (θp ^ 2 * Vp)) a (θp ^ 2 * Vp)
    Tu σi g Y - (1 - Phi) / φh * (W34 ν θw H hb Vw + R34 ν θw H hb Vw) =
      -((σi + ω) * (Y - natY612 σi ω ν g a hb - xStarLin σi ω Phi) ^ 2 +
          θp * (1 + ωp * θp) * Vp + θw / φh * (1 + ν * θw) * Vw) / 2 +
        tip612 σi ω ν Phi g a hb + R612 ω ν θp ωp θw φh Phi Y a hb Vp Vw := by
  intro H
  have hH : H = φh * (Y - a) + E2 φh ωp θp (Y - a) Vp := by
    simp only [H]; rw [E36 hθ]; unfold H2 E2; ring
  set u := Y - a with hu
  set R := R36 φh ωp θp u Vp
  set X := C3 ν φh hb u (E2 φh ωp θp u Vp) + R + R34 ν θw (φh * u + E2 φh ωp θp u Vp) hb Vw
    with hX
  -- step 1: the wage side divided by `φ_h`
  have step1 : (W34 ν θw H hb Vw + R34 ν θw H hb Vw) / φh =
      (u + (1 + ω) / 2 * u ^ 2 - ν * hb * u + θp * (1 + ωp * θp) / 2 * Vp +
        θw * (1 + ν * θw) / (2 * φh) * Vw) + X / φh := by
    rw [hH, hX]
    unfold W34 C3 E2
    rw [hω]
    field_simp
    ring
  -- step 2: combine with (E.2) and complete the square
  have step2 : Tu σi g Y - (1 - Phi) * ((u + (1 + ω) / 2 * u ^ 2 - ν * hb * u +
        θp * (1 + ωp * θp) / 2 * Vp + θw * (1 + ν * θw) / (2 * φh) * Vw) + X / φh) =
      -((σi + ω) * (Y - natY612 σi ω ν g a hb - xStarLin σi ω Phi) ^ 2 +
          θp * (1 + ωp * θp) * Vp + θw / φh * (1 + ν * θw) * Vw) / 2 +
        tip612 σi ω ν Phi g a hb + R612 ω ν θp ωp θw φh Phi Y a hb Vp Vw := by
    unfold R612 Q2
    rw [← hu]
    change _ = _ + _ + (Phi * _ - (1 - Phi) / φh * X)
    unfold Tu natY612 xStarLin tip612
    rw [hu]
    field_simp
    ring
  rw [← step2, ← step1]
  ring

/-- Woodford (2003), (E.33): rescaled pieces for the scaling lemma (`s` scales weight-one
variables by `s` and weight-two variables by `s²`). -/
noncomputable def R36Hat (s φh ωp θp u Vp : ℝ) : ℝ :=
  -((1 + ωp - φh) * φh * (θp * (θp - 1) / 2) * u * Vp) +
    s * ((1 + ωp - φh) * φh / 2 * (θp * (θp - 1) / 2) ^ 2 * Vp ^ 2)

/-- Woodford (2003), (E.33): `E₂(s·) = s² E2Hat s`. -/
noncomputable def E2Hat (s φh ωp θp u Vp : ℝ) : ℝ :=
  (1 + ωp - φh) * φh / 2 * u ^ 2 + (1 + ωp * θp) * θp * φh / 2 * Vp + s * R36Hat s φh ωp θp u Vp

/-- Woodford (2003), (E.33): `R612(s·) = s³ R612Hat s`. -/
noncomputable def R612Hat (s ω ν θp ωp θw φh Phi Y a hb Vp Vw : ℝ) : ℝ :=
  Phi * Q2 ω ν θp ωp θw φh (Y - a) hb Vp Vw -
    (1 - s * Phi) / φh *
      (((1 + ν) * φh * (Y - a) * E2Hat s φh ωp θp (Y - a) Vp +
          s * ((1 + ν) / 2 * E2Hat s φh ωp θp (Y - a) Vp ^ 2) -
          ν * hb * E2Hat s φh ωp θp (Y - a) Vp) +
        R36Hat s φh ωp θp (Y - a) Vp +
        ((1 + ν) / 2 * θw * (1 - θw) * (φh * (Y - a) + s * E2Hat s φh ωp θp (Y - a) Vp) * Vw +
          s * ((1 + ν) / 8 * θw ^ 2 * (1 - θw) ^ 2 * Vw ^ 2) - ν * hb * θw * (1 - θw) / 2 * Vw))

/-- Woodford (2003), (E.33), p. 707 (**scaling lemma**): the remainder of Proposition 6.12 has
weighted degree at least three. -/
theorem R612_scale (ω ν θp ωp θw φh Phi Y a hb Vp Vw s : ℝ) :
    R612 ω ν θp ωp θw φh (s * Phi) (s * Y) (s * a) (s * hb) (s ^ 2 * Vp) (s ^ 2 * Vw) =
      s ^ 3 * R612Hat s ω ν θp ωp θw φh Phi Y a hb Vp Vw := by
  unfold R612 R612Hat C3 E2 E2Hat R36 R36Hat R34 Q2
  ring

/-- Woodford (2003), (E.33): along any scaled family the remainder is `O(s³)`. -/
theorem R612_isBigO (ω ν θp ωp θw φh Phi Y a hb Vp Vw : ℝ) :
    (fun s : ℝ => R612 ω ν θp ωp θw φh (s * Phi) (s * Y) (s * a) (s * hb) (s ^ 2 * Vp)
      (s ^ 2 * Vw)) =O[𝓝 0] fun s => s ^ 3 := by
  refine OneParamTaylor.isBigO_cube_of_scaling
    (fun s => R612_scale ω ν θp ωp θw φh Phi Y a hb Vp Vw s) ?_
  apply Continuous.continuousAt
  unfold R612Hat E2Hat R36Hat Q2; fun_prop

/-- Woodford (2003), p. 707 (**the full (E.34)**): for a finite population of labour types with
weights `w`, relative wages `ŵ` with `E ŵ = −½(1 − θ_w) var ŵ` (`relative_wage_mean`) and
demands `ĥ(j) = Ĥ − θ_wŵ(j)`, the integrated Taylor polynomial is
`Ĥ + ½(1 + ν)Ĥ² − νh̄Ĥ + ½θ_w(1 + νθ_w) var ŵ + R34`. -/
theorem E34_population {w : ι → ℝ} (hw : ∑ i, w i = 1) (ν θw H hb : ℝ) (wh : ι → ℝ)
    (hmean : crossMean w wh = -((1 - θw) / 2) * crossVar w wh) :
    ∑ j, w j * Tvh ν hb (H + -θw * wh j) =
      H + (1 + ν) / 2 * H ^ 2 - ν * hb * H + θw * (1 + ν * θw) / 2 * crossVar w wh +
        R34 ν θw H hb (crossVar w wh) := by
  rw [sum_Tvh hw ν hb (fun j => H + -θw * wh j)]
  obtain ⟨h1, h2⟩ := labor_demand_moments hw H θw wh
  rw [h1, h2, hmean, E34]

/-! ### Proposition 6.13 (the book omits the proof) -/

/-- Woodford (2003), Proposition 6.13, p. 445: the normalising sum
`D = θ_pξ_p⁻¹ + θ_wφ_h⁻¹ξ_w⁻¹`. -/
noncomputable def Dsum (θp ξp θw φh ξw : ℝ) : ℝ := θp / ξp + θw / φh / ξw

/-- Woodford (2003), Proposition 6.13, p. 445: `λ_p = θ_pξ_p⁻¹/D`. -/
noncomputable def lamP (θp ξp θw φh ξw : ℝ) : ℝ := θp / ξp / Dsum θp ξp θw φh ξw

/-- Woodford (2003), Proposition 6.13, p. 445: `λ_w = θ_wφ_h⁻¹ξ_w⁻¹/D`. -/
noncomputable def lamW (θp ξp θw φh ξw : ℝ) : ℝ := θw / φh / ξw / Dsum θp ξp θw φh ξw

/-- Woodford (2003), Proposition 6.13, p. 445: `λ_x = (σ⁻¹ + ω)/D`. -/
noncomputable def lamX613 (σi ω θp ξp θw φh ξw : ℝ) : ℝ := (σi + ω) / Dsum θp ξp θw φh ξw

/-- Woodford (2003), eq. (4.29), p. 445: `L = λ_pπ² + λ_wπ_w² + λ_x(x − x*)²`. -/
def loss429 (lp lw lx π πw x xs : ℝ) : ℝ := lp * π ^ 2 + lw * πw ^ 2 + lx * (x - xs) ^ 2

/-- Woodford (2003), Proposition 6.13, p. 445: `λ_p + λ_w = 1`. -/
theorem lamP_add_lamW {θp ξp θw φh ξw : ℝ} (hD : Dsum θp ξp θw φh ξw ≠ 0) :
    lamP θp ξp θw φh ξw + lamW θp ξp θw φh ξw = 1 := by
  unfold lamP lamW
  rw [← add_div]
  exact div_self hD

/-- Woodford (2003), Proposition 6.13, p. 445: all weights are positive (`θ_p, θ_w, φ_h > 0`,
`ξ_p, ξ_w > 0`, `σ⁻¹ + ω > 0`). -/
theorem weights613_pos {σi ω θp ξp θw φh ξw : ℝ} (hθp : 0 < θp) (hξp : 0 < ξp) (hθw : 0 < θw)
    (hφ : 0 < φh) (hξw : 0 < ξw) (hσω : 0 < σi + ω) :
    0 < lamP θp ξp θw φh ξw ∧ 0 < lamW θp ξp θw φh ξw ∧ 0 < lamX613 σi ω θp ξp θw φh ξw := by
  have hD : 0 < Dsum θp ξp θw φh ξw := by unfold Dsum; positivity
  unfold lamP lamW lamX613
  exact ⟨by positivity, by positivity, by positivity⟩

/-- Woodford (2003), Proposition 6.13 (derivation omitted in the book, p. 445): the Calvo
dispersion sums turn the weight `θ(1 + εθ)` on dispersion into
`θ(1 + εθ)·α/((1 − α)(1 − αβ)) = θ/ξ`, `ξ = (1 − α)(1 − αβ)/(α(1 + εθ))`; with `(ε, θ) =
(ω_p, θ_p)` this is `θ_p/ξ_p`, and with the factor `φ_h⁻¹` and `(ε, θ) = (ν, θ_w)` it is
`θ_wφ_h⁻¹/ξ_w`. -/
theorem calvo_coeff613 (c α β e θ : ℝ) :
    c * (1 + e * θ) * (α / ((1 - α) * (1 - α * β))) =
      c / ((1 - α) * (1 - α * β) / (α * (1 + e * θ))) := by
  rw [div_div_eq_mul_div]; ring

/-- Woodford (2003), **Proposition 6.13**, eq. (4.29), p. 445 (**proof supplied; Layer A,
discounted form**). If the period utility is Proposition 6.12's quadratic form (`hU`, units
`K = Ȳu_c`) and both the price dispersion `Δ_p` and the wage dispersion `Δ_w` follow the exact
Calvo recursions (`Moments.mix_var`, with `π̄`, `π̄_w` the changes in the mean log price and
wage), then
`∑ βᵗU_t = −Ω ∑ βᵗ L_t + T.I.P. + REM` with `L` the loss (4.29) with weights `λ_p, λ_w, λ_x`,
`Ω = (K/2)D`, T.I.P. depending only on `tipU` and `Δ_{p,−1}, Δ_{w,−1}`, and the third-order
`REM = ∑ βᵗR_t − (K/2)[θ_pξ_p⁻¹∑βᵗ(π̄_t² − π_t²) + θ_wφ_h⁻¹ξ_w⁻¹∑βᵗ(π̄_{wt}² − π_{wt}²)]`. -/
theorem prop_6_13 {K σi ω θp ωp θw ν φh β αp αw xs Δpm Δwm : ℝ}
    {U x π πw pb wb Δp Δw tipU R : ℕ → ℝ}
    (hap0 : 0 < αp) (hap1 : αp < 1) (haw0 : 0 < αw) (haw1 : αw < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hθp : 0 < θp) (hθw : 0 < θw) (hφ : 0 < φh) (hωθ : 0 < 1 + ωp * θp)
    (hνθ : 0 < 1 + ν * θw) (hσω : 0 < σi + ω)
    (hU : ∀ t, U t = -K / 2 * ((σi + ω) * (x t - xs) ^ 2 + θp * (1 + ωp * θp) * Δp t +
        θw / φh * (1 + ν * θw) * Δw t) + tipU t + R t)
    (hp0 : Δp 0 = αp * Δpm + αp / (1 - αp) * pb 0 ^ 2)
    (hps : ∀ t, Δp (t + 1) = αp * Δp t + αp / (1 - αp) * pb (t + 1) ^ 2)
    (hw0 : Δw 0 = αw * Δwm + αw / (1 - αw) * wb 0 ^ 2)
    (hws : ∀ t, Δw (t + 1) = αw * Δw t + αw / (1 - αw) * wb (t + 1) ^ 2)
    (hx : Bdd x) (hπ : Bdd π) (hπw : Bdd πw) (hpb : Bdd pb) (hwb : Bdd wb) (hΔp : Bdd Δp)
    (hΔw : Bdd Δw) (htip : Bdd tipU) (hR : Bdd R) :
    let ξp := calvoXi αp β ωp θp
    let ξw := calvoXi αw β ν θw
    ∑' t, β ^ t * U t =
      -(K / 2 * Dsum θp ξp θw φh ξw) * ∑' t, β ^ t * loss429 (lamP θp ξp θw φh ξw)
          (lamW θp ξp θw φh ξw) (lamX613 σi ω θp ξp θw φh ξw) (π t) (πw t) (x t) xs +
        (∑' t, β ^ t * tipU t - K / 2 * (θp * (1 + ωp * θp) * (αp * Δpm / (1 - αp * β)) +
          θw / φh * (1 + ν * θw) * (αw * Δwm / (1 - αw * β)))) +
        (∑' t, β ^ t * R t - K / 2 * (θp / ξp * ∑' t, β ^ t * (pb t ^ 2 - π t ^ 2) +
          θw / φh / ξw * ∑' t, β ^ t * (wb t ^ 2 - πw t ^ 2))) := by
  intro ξp ξw
  have hβp : αp * β < 1 := by nlinarith
  have hβw : αw * β < 1 := by nlinarith
  have hξp : 0 < ξp := by
    simp only [ξp, calvoXi]
    have : 0 < 1 - αp * β := by linarith
    have : 0 < 1 - αp := by linarith
    positivity
  have hξw : 0 < ξw := by
    simp only [ξw, calvoXi]
    have : 0 < 1 - αw * β := by linarith
    have : 0 < 1 - αw := by linarith
    positivity
  have hD : 0 < Dsum θp ξp θw φh ξw := by unfold Dsum; positivity
  have cp : θp * (1 + ωp * θp) * (αp / ((1 - αp) * (1 - αp * β))) = θp / ξp :=
    calvo_coeff613 θp αp β ωp θp
  have cw : θw / φh * (1 + ν * θw) * (αw / ((1 - αw) * (1 - αw * β))) = θw / φh / ξw :=
    calvo_coeff613 (θw / φh) αw β ν θw
  have dp := dispersion_tsum (β := β) hap0.le hap1 hβ0 hβ1 hΔp hpb hp0 hps
  have dw := dispersion_tsum (β := β) haw0.le haw1 hβ0 hβ1 hΔw hwb hw0 hws
  set D := Dsum θp ξp θw φh ξw with hDdef
  set Ω := K / 2 * D with hΩ
  set cp' := αp / ((1 - αp) * (1 - αp * β)) with hcp'
  set cw' := αw / ((1 - αw) * (1 - αw * β)) with hcw'
  have sL : Summable fun t => β ^ t * loss429 (lamP θp ξp θw φh ξw) (lamW θp ξp θw φh ξw)
      (lamX613 σi ω θp ξp θw φh ξw) (π t) (πw t) (x t) xs := by
    have hb : Bdd fun t => loss429 (lamP θp ξp θw φh ξw) (lamW θp ξp θw φh ξw)
        (lamX613 σi ω θp ξp θw φh ξw) (π t) (πw t) (x t) xs := by
      have h1 := (hπ.pow 2).lin (hπw.pow 2) (lamP θp ξp θw φh ξw) (lamW θp ξp θw φh ξw)
      have h2 := ((hx.lin (Bdd.const xs) 1 (-1)).pow 2)
      convert h1.lin h2 1 (lamX613 σi ω θp ξp θw φh ξw) using 2 with t
      unfold loss429; ring
    exact hb.summable hβ0 hβ1
  have sT := htip.summable hβ0 hβ1
  have sR := hR.summable hβ0 hβ1
  have sDp := hΔp.summable hβ0 hβ1
  have sDw := hΔw.summable hβ0 hβ1
  have sP := (hπ.pow 2).summable hβ0 hβ1
  have sW := (hπw.pow 2).summable hβ0 hβ1
  have sQp := (hpb.pow 2).summable hβ0 hβ1
  have sQw := (hwb.pow 2).summable hβ0 hβ1
  have hwp : Ω * lamP θp ξp θw φh ξw = K / 2 * (θp * (1 + ωp * θp)) * cp' := by
    rw [hΩ, mul_assoc (K / 2) (θp * (1 + ωp * θp)), cp]
    unfold lamP; rw [← hDdef]; field_simp
  have hww : Ω * lamW θp ξp θw φh ξw = K / 2 * (θw / φh * (1 + ν * θw)) * cw' := by
    rw [hΩ, mul_assoc (K / 2) (θw / φh * (1 + ν * θw)), cw]
    unfold lamW; rw [← hDdef]; field_simp
  have hlx : Ω * lamX613 σi ω θp ξp θw φh ξw = K / 2 * (σi + ω) := by
    rw [hΩ]; unfold lamX613; rw [← hDdef]; field_simp
  have hpt : ∀ t, β ^ t * U t =
      -Ω * (β ^ t * loss429 (lamP θp ξp θw φh ξw) (lamW θp ξp θw φh ξw)
          (lamX613 σi ω θp ξp θw φh ξw) (π t) (πw t) (x t) xs) + β ^ t * tipU t + β ^ t * R t -
        K / 2 * (θp * (1 + ωp * θp) * (β ^ t * Δp t - cp' * (β ^ t * π t ^ 2)) +
          θw / φh * (1 + ν * θw) * (β ^ t * Δw t - cw' * (β ^ t * πw t ^ 2))) := by
    intro t
    rw [hU t]
    unfold loss429
    linear_combination (β ^ t * (x t - xs) ^ 2) * hlx + (β ^ t * π t ^ 2) * hwp +
      (β ^ t * πw t ^ 2) * hww
  have H := (((sL.hasSum.mul_left (-Ω)).add sT.hasSum).add sR.hasSum).sub
    ((((sDp.hasSum.sub (sP.hasSum.mul_left cp')).mul_left (θp * (1 + ωp * θp))).add
      ((sDw.hasSum.sub (sW.hasSum.mul_left cw')).mul_left (θw / φh * (1 + ν * θw)))).mul_left
        (K / 2))
  rw [funext hpt, H.tsum_eq, dp, dw]
  have t1 : ∑' t, β ^ t * (pb t ^ 2 - π t ^ 2) =
      ∑' t, β ^ t * pb t ^ 2 - ∑' t, β ^ t * π t ^ 2 := by
    rw [← sQp.tsum_sub sP]; congr 1; funext t; ring
  have t2 : ∑' t, β ^ t * (wb t ^ 2 - πw t ^ 2) =
      ∑' t, β ^ t * wb t ^ 2 - ∑' t, β ^ t * πw t ^ 2 := by
    rw [← sQw.tsum_sub sW]; congr 1; funext t; ring
  rw [t1, t2]
  linear_combination (-(K / 2 * (∑' t, β ^ t * pb t ^ 2 - ∑' t, β ^ t * π t ^ 2))) * cp -
    (K / 2 * (∑' t, β ^ t * wb t ^ 2 - ∑' t, β ^ t * πw t ^ 2)) * cw

/-- Woodford (2003), **Proposition 6.13 from the Calvo model**: the conclusion of `prop_6_13`
holds with the price and wage dispersions and the mean-price and mean-wage inflation rates
generated by the Calvo processes for prices (`α_p`, reset prices `p*`) and wages (`α_w`, reset
wages `w*`) from initial cross-sections `Lp0`, `Lw0` (nonnegative weights, unit mass, all values
and reset values bounded by `M`); the recursions and bounds come from `calvo_recursion` and
`calvo_bdd`. -/
theorem prop_6_13_calvo {K σi ω θp ωp θw ν φh β αp αw xs M : ℝ}
    {U x π πw tipU R psp psw : ℕ → ℝ} {Lp0 Lw0 : List (ℝ × ℝ)}
    (hap0 : 0 < αp) (hap1 : αp < 1) (haw0 : 0 < αw) (haw1 : αw < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hθp : 0 < θp) (hθw : 0 < θw) (hφ : 0 < φh) (hωθ : 0 < 1 + ωp * θp)
    (hνθ : 0 < 1 + ν * θw) (hσω : 0 < σi + ω)
    (hwp : ∀ z ∈ Lp0, 0 ≤ z.1) (hpp : ∀ z ∈ Lp0, |z.2| ≤ M) (hmp : lmass Lp0 = 1)
    (hww : ∀ z ∈ Lw0, 0 ≤ z.1) (hpw : ∀ z ∈ Lw0, |z.2| ≤ M) (hmw : lmass Lw0 = 1)
    (hpsp : ∀ t, |psp t| ≤ M) (hpsw : ∀ t, |psw t| ≤ M)
    (hU : ∀ t, U t = -K / 2 * ((σi + ω) * (x t - xs) ^ 2 +
        θp * (1 + ωp * θp) * lvar (calvoPop αp Lp0 psp t) +
        θw / φh * (1 + ν * θw) * lvar (calvoPop αw Lw0 psw t)) + tipU t + R t)
    (hx : Bdd x) (hπ : Bdd π) (hπw : Bdd πw) (htip : Bdd tipU) (hR : Bdd R) :
    let ξp := calvoXi αp β ωp θp
    let ξw := calvoXi αw β ν θw
    let pb := fun t => lmean (calvoPop αp Lp0 psp t) - lagMean αp Lp0 psp t
    let wb := fun t => lmean (calvoPop αw Lw0 psw t) - lagMean αw Lw0 psw t
    ∑' t, β ^ t * U t =
      -(K / 2 * Dsum θp ξp θw φh ξw) * ∑' t, β ^ t * loss429 (lamP θp ξp θw φh ξw)
          (lamW θp ξp θw φh ξw) (lamX613 σi ω θp ξp θw φh ξw) (π t) (πw t) (x t) xs +
        (∑' t, β ^ t * tipU t - K / 2 * (θp * (1 + ωp * θp) * (αp * lvar Lp0 / (1 - αp * β)) +
          θw / φh * (1 + ν * θw) * (αw * lvar Lw0 / (1 - αw * β)))) +
        (∑' t, β ^ t * R t - K / 2 * (θp / ξp * ∑' t, β ^ t * (pb t ^ 2 - π t ^ 2) +
          θw / φh / ξw * ∑' t, β ^ t * (wb t ^ 2 - πw t ^ 2))) := by
  intro ξp ξw pb wb
  obtain ⟨rp0, rps⟩ := calvo_recursion (ne_of_lt hap1) hmp psp
  obtain ⟨rw0, rws⟩ := calvo_recursion (ne_of_lt haw1) hmw psw
  obtain ⟨bΔp, bpb⟩ := calvo_bdd hap0.le hap1.le hwp hpp hmp hpsp
  obtain ⟨bΔw, bwb⟩ := calvo_bdd haw0.le haw1.le hww hpw hmw hpsw
  exact prop_6_13 hap0 hap1 haw0 haw1 hβ0 hβ1 hθp hθw hφ hωθ hνθ hσω hU rp0 rps rw0 rws hx hπ
    hπw bpb bwb bΔp bΔw htip hR

/-! ### The discussion of Proposition 6.13 (pp. 445–448) -/

/-- Woodford (2003), eq. (4.30), p. 446: when `λ_p + λ_w = 1` and `π_w − π = log w − log w_{−1}`
(the real wage `w = W/P`), the loss (4.29) is
`π̄² + λ_pλ_w(log w − log w_{−1})² + λ_x(x − x*)²`, `π̄ = λ_pπ + λ_wπ_w`. -/
theorem eq_4_30 {lp lw lx π πw x xs lwr lwrm : ℝ} (h : lp + lw = 1)
    (hw : πw - π = lwr - lwrm) :
    loss429 lp lw lx π πw x xs =
      (lp * π + lw * πw) ^ 2 + lp * lw * (lwr - lwrm) ^ 2 + lx * (x - xs) ^ 2 := by
  unfold loss429
  rw [← hw]
  have : lw = 1 - lp := by linarith
  subst this
  ring

/-- Woodford (2003), (4.30): the underlying identity
`λ_pa² + λ_wb² = (λ_pa + λ_wb)² + λ_pλ_w(a − b)²` for `λ_p + λ_w = 1`. -/
theorem weighted_sq_identity' {lp lw : ℝ} (h : lp + lw = 1) (a b : ℝ) :
    lp * a ^ 2 + lw * b ^ 2 = (lp * a + lw * b) ^ 2 + lp * lw * (a - b) ^ 2 := by
  have : lw = 1 - lp := by linarith
  subst this; ring

/-- Woodford (2003), p. 445: when `θ_wφ_h⁻¹ = θ_p = θ`, the weights reduce to
`λ_p = ξ_p⁻¹/(ξ_p⁻¹ + ξ_w⁻¹)`, `λ_w = ξ_w⁻¹/(ξ_p⁻¹ + ξ_w⁻¹)` and `λ_x = κ/θ` with
`κ = (σ⁻¹ + ω)/(ξ_p⁻¹ + ξ_w⁻¹)` the slope of (4.14) of Chapter 3. -/
theorem weights_equal_theta {σi ω θ ξp θw φh ξw : ℝ} (hθ : θw / φh = θ) (hθ0 : θ ≠ 0) :
    lamP θ ξp θw φh ξw = ξp⁻¹ / (ξp⁻¹ + ξw⁻¹) ∧ lamW θ ξp θw φh ξw = ξw⁻¹ / (ξp⁻¹ + ξw⁻¹) ∧
      lamX613 σi ω θ ξp θw φh ξw = (σi + ω) / (ξp⁻¹ + ξw⁻¹) / θ := by
  have hD : Dsum θ ξp θw φh ξw = θ * (ξp⁻¹ + ξw⁻¹) := by
    unfold Dsum; rw [hθ]; ring
  unfold lamP lamW lamX613
  rw [hD, hθ]
  refine ⟨?_, ?_, ?_⟩
  · rw [div_eq_mul_inv θ ξp, mul_div_mul_left _ _ hθ0]
  · rw [div_eq_mul_inv θ ξw, mul_div_mul_left _ _ hθ0]
  · rw [div_div, mul_comm]

/-- Woodford (2003), p. 447 ("the intermediate special case is that in which
`λ_w = (σ⁻¹ + ω_w)/(σ⁻¹ + ω)`, so that `κ_w = κ_p`"): with `κ_w = ξ_w(ω_w + σ⁻¹)`,
`κ_p = ξ_pω_p` (Proposition 3.9) and `λ_w = ξ_w⁻¹/(ξ_p⁻¹ + ξ_w⁻¹)`,
`κ_w = κ_p ⟺ λ_w = (σ⁻¹ + ω_w)/(σ⁻¹ + ω_w + ω_p)`. -/
theorem kappaW_eq_kappaP_iff {ξp ξw ωw ωp σi : ℝ} (hξp : 0 < ξp) (hξw : 0 < ξw)
    (hσω : 0 < σi + (ωw + ωp)) :
    ξw * (ωw + σi) = ξp * ωp ↔ ξw⁻¹ / (ξp⁻¹ + ξw⁻¹) = (σi + ωw) / (σi + (ωw + ωp)) := by
  have hl : ξw⁻¹ / (ξp⁻¹ + ξw⁻¹) = ξp / (ξp + ξw) := by field_simp; ring
  rw [hl, div_eq_div_iff (by positivity) hσω.ne']
  constructor <;> intro h <;> linarith

/-- Woodford (2003), p. 447: with Table 5.1 (`σ⁻¹ = .16`, `ω_w = .14`, `ω_p = .33`), the
critical `λ_w = (σ⁻¹ + ω_w)/(σ⁻¹ + ω) = .30/.63 = 10/21 ≈ .476`, printed `.48`. -/
theorem lamW_critical_value :
    ((0.16 : ℝ) + 0.14) / (0.16 + (0.14 + 0.33)) = 10 / 21 ∧
      (0.475 : ℝ) < 10 / 21 ∧ (10 / 21 : ℝ) < 0.485 := by
  norm_num

/-- Woodford (2003), Table 6.4 and fn 66, pp. 446–447: `ξ_w⁻¹ + ξ_p⁻¹ = (σ⁻¹ + ω)/κ`
(from (4.15)). With Table 5.1's rounded `σ⁻¹ + ω = .63`, `κ = .024` this is `26.25`; the
printed `26.7` corresponds to `κ = .63/26.7 ≈ .0236`, which rounds to the printed `.024`; and
with `θ = 7.88` the implied `λ_x = 16(σ⁻¹ + ω)/(θ · 26.7) ≈ .0479` rounds to the printed `.048`
(whereas `16 · .024/7.88 ≈ .0487` would round to `.049`). -/
theorem table_6_4_values :
    (0.63 : ℝ) / 0.024 = 26.25 ∧
      ((0.0235 : ℝ) ≤ 0.63 / 26.7 ∧ (0.63 : ℝ) / 26.7 < 0.0245) ∧
      ((0.0475 : ℝ) ≤ 16 * 0.63 / (7.88 * 26.7) ∧ 16 * (0.63 : ℝ) / (7.88 * 26.7) < 0.0485) ∧
      ((0.0485 : ℝ) ≤ 16 * 0.024 / 7.88 ∧ 16 * (0.024 : ℝ) / 7.88 < 0.0495) := by
  norm_num

/-- Woodford (2003), (4.15) of Chapter 3 restated: `ξ_p⁻¹ + ξ_w⁻¹ = (σ⁻¹ + ω)/κ`. -/
theorem xi_sum_eq {ξp ξw σi ω : ℝ} (hσω : σi + ω ≠ 0) :
    ξp⁻¹ + ξw⁻¹ = (σi + ω) / ((σi + ω) / (ξp⁻¹ + ξw⁻¹)) := by
  field_simp

/-- Woodford (2003), fn 66, p. 446: the Amato–Laubach estimates (Table 5.2, `ξ_w = .066`,
`ξ_p = .058`) give `ξ_w⁻¹ + ξ_p⁻¹ = 1/.066 + 1/.058 ≈ 32.39`, printed `32.4`. -/
theorem fn66_value :
    (32.35 : ℝ) ≤ 1 / 0.066 + 1 / 0.058 ∧ 1 / (0.066 : ℝ) + 1 / 0.058 < 32.45 := by
  norm_num

/-- Woodford (2003), p. 445: `ξ⁻¹ = α(1 + εθ)/((1 − α)(1 − αβ)) → 0` as `α → 0⁺`, the limit of
flexible wages (`ξ_w → ∞`) or flexible prices (`ξ_p → ∞`). -/
theorem tendsto_xi_inv (β e θ : ℝ) :
    Tendsto (fun α : ℝ => ((1 - α) * (1 - α * β) / (α * (1 + e * θ)))⁻¹) (𝓝[>] 0) (𝓝 0) := by
  have h : (fun α : ℝ => ((1 - α) * (1 - α * β) / (α * (1 + e * θ)))⁻¹) =
      fun α => α * (1 + e * θ) / ((1 - α) * (1 - α * β)) := by
    funext α; rw [inv_div]
  rw [h]
  have hc := (by fun_prop : Continuous fun α : ℝ => (1 - α) * (1 - α * β)).tendsto' 0 1
    (by simp)
  have := (tendsto_id.mul_const (1 + e * θ)).div hc one_ne_zero
  simp only [id, zero_mul, zero_div] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- Woodford (2003), p. 445 ("if only prices are sticky (`ξ_w → +∞`), only price inflation
matters (`λ_w = 0`)"; and symmetrically for `ξ_p → +∞`): as `α_w → 0⁺`, `λ_w → 0`; as
`α_p → 0⁺`, `λ_p → 0` (`θ_p, θ_w, φ_h > 0`, the other `ξ > 0`). -/
theorem lam_flexible_limits {β ν θw ωp θp φh ξp ξw : ℝ} (hθp : 0 < θp) (hθw : 0 < θw)
    (hφ : 0 < φh) (hξp : 0 < ξp) (hξw : 0 < ξw) :
    Tendsto (fun αw => lamW θp ξp θw φh (calvoXi αw β ν θw)) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun αp => lamP θp (calvoXi αp β ωp θp) θw φh ξw) (𝓝[>] 0) (𝓝 0) := by
  have e1 : ∀ ξ, lamW θp ξp θw φh ξ = θw / φh * ξ⁻¹ / (θp / ξp + θw / φh * ξ⁻¹) := by
    intro ξ; unfold lamW Dsum; simp only [div_eq_mul_inv]
  have e2 : ∀ ξ, lamP θp ξ θw φh ξw = θp * ξ⁻¹ / (θp * ξ⁻¹ + θw / φh / ξw) := by
    intro ξ; unfold lamP Dsum; simp only [div_eq_mul_inv]
  constructor
  · simp only [e1]
    have hg := tendsto_xi_inv β ν θw
    have hnum := hg.const_mul (θw / φh)
    have hden := (hg.const_mul (θw / φh)).const_add (θp / ξp)
    have := hnum.div hden (by rw [mul_zero, add_zero]; positivity)
    rw [mul_zero, zero_div] at this
    exact this
  · simp only [e2]
    have hg := tendsto_xi_inv β ωp θp
    have hnum := hg.const_mul θp
    have hden := (hg.const_mul θp).add_const (θw / φh / ξw)
    have := hnum.div hden (by rw [mul_zero, zero_add]; positivity)
    rw [mul_zero, zero_div] at this
    exact this

/-- Woodford (2003), (4.29), p. 445: the loss is nonnegative for nonnegative weights. -/
theorem loss429_nonneg {lp lw lx : ℝ} (hp : 0 ≤ lp) (hw : 0 ≤ lw) (hx : 0 ≤ lx)
    (π πw x xs : ℝ) : 0 ≤ loss429 lp lw lx π πw x xs := by
  unfold loss429; positivity

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), (4.13)–(4.14) of Chapter 3 (restated): from Proposition 3.9's (4.11) and
(4.12), `π_w = κ_w x + ξ_w(log wⁿ − log w) + βE π_w'` and `π = κ_p x + ξ_p(log w − log wⁿ) +
βE π'`, the weighted average `π̄ = (ξ_p⁻¹π + ξ_w⁻¹π_w)/(ξ_p⁻¹ + ξ_w⁻¹)` satisfies
`π̄ = κ x + βE π̄'` with `κ = (σ⁻¹ + ω)/(ξ_p⁻¹ + ξ_w⁻¹)`. -/
theorem pibar_pc {β ξw ξp ωw ωp σi : ℝ} (hξw : 0 < ξw) (hξp : 0 < ξp)
    {πw π x lw lwn : ℕ → Ω → ℝ}
    (h411 : ∀ t, πw t = (ξw * (ωw + σi)) • x t + ξw • (lwn t - lw t) + β • 𝔼.E t (πw (t + 1)))
    (h412 : ∀ t, π t = (ξp * ωp) • x t + ξp • (lw t - lwn t) + β • 𝔼.E t (π (t + 1)))
    (t : ℕ) :
    let lp := ξp⁻¹ / (ξp⁻¹ + ξw⁻¹)
    let lw' := ξw⁻¹ / (ξp⁻¹ + ξw⁻¹)
    lp • π t + lw' • πw t =
      ((σi + (ωw + ωp)) / (ξp⁻¹ + ξw⁻¹)) • x t + β • 𝔼.E t (lp • π (t + 1) + lw' • πw (t + 1)) := by
  intro lp lw'
  funext o
  have e1 := congrFun (h411 t) o
  have e2 := congrFun (h412 t) o
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_smul, Pi.sub_apply]
    at e1 e2 ⊢
  rw [e1, e2]
  simp only [lp, lw']
  have h1 := hξw.ne'
  have h2 := hξp.ne'
  have h3 : ξp⁻¹ + ξw⁻¹ ≠ 0 := (add_pos (inv_pos.mpr hξp) (inv_pos.mpr hξw)).ne'
  field_simp
  ring

/-- Woodford (2003), p. 446 and p. 448 (**output-gap targeting = targeting `π̄`, `φ = λ_p`**):
with bounded `π̄` satisfying (4.14), `x ≡ 0 ⟺ λ_pπ + λ_wπ_w ≡ 0`, where (when
`θ_wφ_h⁻¹ = θ_p`, `weights_equal_theta`) `λ_p = ξ_p⁻¹/(ξ_p⁻¹ + ξ_w⁻¹) = 1 − λ_w`. -/
theorem gap_iff_pibar_wages {β ξw ξp ωw ωp σi : ℝ} (hξw : 0 < ξw) (hξp : 0 < ξp)
    (hσω : 0 < σi + (ωw + ωp)) (hβ : |β| < 1) {πw π x lw lwn : ℕ → Ω → ℝ}
    (h411 : ∀ t, πw t = (ξw * (ωw + σi)) • x t + ξw • (lwn t - lw t) + β • 𝔼.E t (πw (t + 1)))
    (h412 : ∀ t, π t = (ξp * ωp) • x t + ξp • (lw t - lwn t) + β • 𝔼.E t (π (t + 1)))
    (hb : BoundedProc fun t => (ξp⁻¹ / (ξp⁻¹ + ξw⁻¹)) • π t + (ξw⁻¹ / (ξp⁻¹ + ξw⁻¹)) • πw t) :
    (∀ t, x t = 0) ↔
      ∀ t, (ξp⁻¹ / (ξp⁻¹ + ξw⁻¹)) • π t + (ξw⁻¹ / (ξp⁻¹ + ξw⁻¹)) • πw t = 0 := by
  have hS : 0 < ξp⁻¹ + ξw⁻¹ := add_pos (inv_pos.mpr hξp) (inv_pos.mpr hξw)
  exact gap_iff_pibar 𝔼 (div_pos hσω hS).ne' hβ hb (fun t => pibar_pc 𝔼 hξw hξp h411 h412 t)

/-- Woodford (2003), p. 446 ("in the case that `κ_w = κ_p`, the evolution of the real wage is
independent of monetary policy, as shown in Chapter 3"): with `κ_w = κ_p = k`, (4.11), (4.12)
and `π_w − π = log w − log w_{−1}`, two bounded adapted equilibria with the same initial real
wage and the same natural real wage have the same real-wage path. -/
theorem realWage_policy_invariant {k ξw ξp β : ℝ} (hξw : 0 < ξw) (hξp : 0 < ξp) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {lwm1 : Ω → ℝ} {lwn : ℕ → Ω → ℝ} {π πw x lw π' πw' x' lw' : ℕ → Ω → ℝ}
    (h411 : ∀ t, πw t = k • x t + (-ξw) • (lw t - lwn t) + β • 𝔼.E t (πw (t + 1)))
    (h412 : ∀ t, π t = k • x t + ξp • (lw t - lwn t) + β • 𝔼.E t (π (t + 1)))
    (hreal : ∀ t, πw t - π t = lw t - lagP lwm1 lw t)
    (h411' : ∀ t, πw' t = k • x' t + (-ξw) • (lw' t - lwn t) + β • 𝔼.E t (πw' (t + 1)))
    (h412' : ∀ t, π' t = k • x' t + ξp • (lw' t - lwn t) + β • 𝔼.E t (π' (t + 1)))
    (hreal' : ∀ t, πw' t - π' t = lw' t - lagP lwm1 lw' t)
    (ha : 𝔼.Adapted lw) (ha' : 𝔼.Adapted lw') (hb : BoundedProc lw) (hb' : BoundedProc lw') :
    lw = lw' :=
  relPrice_policy_invariant 𝔼 hβ0 hβ1 (by linarith) h412 h411 hreal h412' h411' hreal' ha ha' hb
    hb'

/-- Woodford (2003), p. 446 (**`κ_w = κ_p` and `θ_wφ_h⁻¹ = θ_p`: completely stabilising `π̄` is
optimal**): with `λ_p = ξ_p⁻¹/(ξ_p⁻¹ + ξ_w⁻¹)`, `λ_w = 1 − λ_p`, `x* = 0` and `λ_x ≥ 0`, an
equilibrium with `π̄ = λ_pπ + λ_wπ_w ≡ 0` has, date by date and state by state, a loss (4.29) no
larger than any other bounded equilibrium with the same initial real wage. -/
theorem pibar_stabilisation_optimal {k ξw ξp β lx : ℝ} (hk : k ≠ 0) (hξw : 0 < ξw)
    (hξp : 0 < ξp) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hx : 0 ≤ lx) {lwm1 : Ω → ℝ}
    {lwn : ℕ → Ω → ℝ} {π πw x lw π' πw' x' lw' : ℕ → Ω → ℝ}
    (h411 : ∀ t, πw t = k • x t + (-ξw) • (lw t - lwn t) + β • 𝔼.E t (πw (t + 1)))
    (h412 : ∀ t, π t = k • x t + ξp • (lw t - lwn t) + β • 𝔼.E t (π (t + 1)))
    (hreal : ∀ t, πw t - π t = lw t - lagP lwm1 lw t)
    (h411' : ∀ t, πw' t = k • x' t + (-ξw) • (lw' t - lwn t) + β • 𝔼.E t (πw' (t + 1)))
    (h412' : ∀ t, π' t = k • x' t + ξp • (lw' t - lwn t) + β • 𝔼.E t (π' (t + 1)))
    (hreal' : ∀ t, πw' t - π' t = lw' t - lagP lwm1 lw' t)
    (ha : 𝔼.Adapted lw) (ha' : 𝔼.Adapted lw') (hb : BoundedProc lw) (hb' : BoundedProc lw')
    (hstab : ∀ t, (ξp⁻¹ / (ξp⁻¹ + ξw⁻¹)) • π t + (1 - ξp⁻¹ / (ξp⁻¹ + ξw⁻¹)) • πw t = 0)
    (t : ℕ) (o : Ω) :
    loss429 (ξp⁻¹ / (ξp⁻¹ + ξw⁻¹)) (1 - ξp⁻¹ / (ξp⁻¹ + ξw⁻¹)) lx (π t o) (πw t o) (x t o) 0 ≤
      loss429 (ξp⁻¹ / (ξp⁻¹ + ξw⁻¹)) (1 - ξp⁻¹ / (ξp⁻¹ + ξw⁻¹)) lx (π' t o) (πw' t o)
        (x' t o) 0 := by
  have hS : 0 < ξp⁻¹ + ξw⁻¹ := add_pos (inv_pos.mpr hξp) (inv_pos.mpr hξw)
  have hn : ξp⁻¹ / (ξp⁻¹ + ξw⁻¹) * ξp + (1 - ξp⁻¹ / (ξp⁻¹ + ξw⁻¹)) * -ξw = 0 := by
    field_simp; ring
  have h := equal_stickiness_optimal 𝔼 (lR := 0) hk hβ0 hβ1 (by linarith) hn hx h412 h411 hreal
    h412' h411' hreal' ha ha' hb hb' hstab t o
  simpa [loss425, loss429] using h

end Woodford.StabilizationWelfare.StickyWageWelfare
