/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergSmooth
import StabilizationWelfare.NonlinearNKMarkovGoods

/-!
# Rotemberg and Calvo: first-order agreement, second-order difference

Woodford (2003), *Interest and Prices*, Chapter 3, §2.2, footnote 44 (p. 188: the Rotemberg
(1982) quadratic adjustment-cost model implies "the same form of aggregate supply relation, up to
the log-linear approximation") and Chapter 6, §2 (pp. 393–400: the welfare-relevant distortion
of Calvo pricing is relative-price dispersion, a second-order quantity).

## Main results

* **`first_order_agree`**: on every finite Markov chain, if the Rotemberg and Calvo economies
  share `β, σ, ω, θ, φ_π, φ_y`, the adjustment cost is the equivalence map
  `ψ = θmα(1+ωθ)/((1−α)(1−αβ))` (`κ_eq_calvo_iff`), and the disturbances enter the IS curve and
  the natural rate identically, then the first-order solutions `(ŷ₁, π₁)` of the two exact
  nonlinear models coincide state by state.
* **`calvo_dispersion_first_order`**: the Calvo dispersion law has zero inflation derivative at
  `Δ = 1` on the price-index curve (dispersion is a second-order distortion).
* **`rotemberg_resource_second_order`**: the Rotemberg resource wedge `C/Y = 1 − (ψ/2)(Π − 1)²`
  has value `1`, slope `0` and curvature `−ψ < 0` at zero inflation, and is `< 1` at every
  nonzero inflation rate.
* **`second_order_difference`**: the explicit second-order difference: in Calvo `C = Y` at every
  inflation rate (curvature `0` of `C/Y`), in Rotemberg the curvature of `C/Y` in inflation is
  `−ψ ≠ 0`; under the equivalence map `−ψ = −θmα(1+ωθ)/((1−α)(1−αβ))`.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergLinks

open Filter Topology
open NonlinearNKMarkov (chainOp Stochastic chainOp_isMarkov M_lin IsMarkovEqm)
open NonlinearRotemberg (Lop Lop_apply Lop_injective DQe)

/-! ## First-order agreement under the equivalence map -/

variable {S : Type*} [Fintype S]

/-- Woodford (2003), Ch. 3, fn. 44 and (2.19) (**the equivalence map gives equal slopes**): if
the two economies share `β, σ, ω, θ` and `ψ = θmα(1+ωθ)/((1−α)(1−αβ))`, the Rotemberg slope
`θm(σ+ω)/ψ` equals the Calvo slope `κ`. -/
theorem kappa_eq (p : NonlinearRotemberg.Par) (c : NonlinearNKMarkov.Par) (hp : p.Basic)
    (hc : c.Std) (hβ : p.β = c.β) (hσ : p.σ = c.σ) (hω : p.ω = c.ω) (hθ : p.θ = c.θ)
    (hψ : p.ψ = p.θ * p.m * c.α * (1 + p.ω * p.θ) / ((1 - c.α) * (1 - c.α * p.β))) :
    p.κ = c.κ := by
  have h := (NonlinearRotemberg.κ_eq_calvo_iff hp hc.α_pos hc.α_lt_one).2 hψ
  rw [h, hβ, hσ, hω, hθ]
  rfl

/-- Woodford (2003), Ch. 3, fn. 44 (p. 188) and Proposition 4.3 (**Rotemberg and Calvo agree to
first order**): on a finite Markov chain `P`, let `z₁ᶜ = z′(0)` be the first-order solution of a
smooth family of exact Calvo Markov equilibria with disturbances `εξᶜ`, and `z₁ʳ` the first-order
solution of the exact Rotemberg model (`L z₁ʳ + ∂Φ/∂ε = 0`, `NonlinearRotembergSmooth.firstOrder`)
with disturbances `ξʳ`. If the economies share `β, σ, ω, θ, φ_π, φ_y`, the Rotemberg
adjustment cost is the equivalence map, the IS-curve disturbance and the natural rate coincide,
and the Rotemberg Taylor principle holds, then output and inflation agree state by state. -/
theorem first_order_agree (p : NonlinearRotemberg.Par) (c : NonlinearNKMarkov.Par)
    (hp : p.Std) (hc : c.Std) (hβ : p.β = c.β) (hσ : p.σ = c.σ) (hω : p.ω = c.ω)
    (hθ : p.θ = c.θ) (hφ : p.φ = c.φ) (hφy : p.φy = c.φy)
    (hψ : p.ψ = p.θ * p.m * c.α * (1 + p.ω * p.θ) / ((1 - c.α) * (1 - c.α * p.β)))
    {P : S → S → ℝ} (hP : Stochastic P) (ξc : S → Fin 5 → ℝ) (ξr : S → Fin 3 → ℝ)
    {z : ℝ → S → Fin 4 → ℝ} {zc : S → Fin 4 → ℝ} (hz0 : z 0 = 0) (hz : HasDerivAt z zc 0)
    (heq : ∀ᶠ ε in 𝓝 0, IsMarkovEqm c (chainOp P) ξc ε (z ε))
    {zr : S → Fin 3 → ℝ} (hr : Lop p (chainOp P) zr + (fun s => DQe p (ξr s)) = 0)
    (hν : ∀ s, ξr s 0 = ξc s 0 - c.σ * ξc s 1 + c.σ * chainOp P (fun s' => ξc s' 1) s)
    (hn : ∀ s, ((1 + p.ω) * ξr s 1 - ξr s 2) / (p.σ + p.ω) =
      (c.ω * ξc s 3 + c.σ * ξc s 1 - ξc s 4 + ξc s 2) / (c.ω + c.σ)) (s : S) :
    zc s 0 = zr s 0 ∧ zc s 1 = zr s 1 := by
  have hb := hp.basic
  have hκ := kappa_eq p c hb hc hβ hσ hω hθ hψ
  have hψ0 := hb.ψ_pos
  have hk := hb.κ_mul
  -- the difference of the two first-order solutions, with `ĉ = ŷ`
  set v : S → Fin 3 → ℝ := fun s => ![zc s 0 - zr s 0, zc s 1 - zr s 1, zc s 0 - zr s 0] with hv
  have hr' := fun s => NonlinearRotembergSmooth.firstOrder_eqs hb P ξr hr s
  have hc' := fun s => NonlinearNKMarkov.firstOrder_eqs P ξc hz0 hz heq s
  have hcn := fun s => NonlinearNKMarkov.firstOrder_nkpc hc P ξc hz0 hz heq s
  have hM : ∀ (i j : Fin 3) (k : Fin 4) (l : Fin 3), (∀ s, v s i = zc s k - zr s l) →
      ∀ s, chainOp P (fun s' => v s' i) s =
        chainOp P (fun s' => zc s' k) s - chainOp P (fun s' => zr s' l) s := by
    intro i _ k l h s
    have e : (fun s' => v s' i) = fun s' => 1 * zc s' k + -1 * zr s' l := by
      funext s'; rw [h s']; ring
    rw [e, M_lin]; ring
  have hM0 := hM 0 0 0 0 (fun _ => rfl)
  have hM1 := hM 1 0 1 1 (fun _ => rfl)
  have hM2 := hM 2 0 0 0 (fun _ => rfl)
  have hL : Lop p (chainOp P) v = 0 := by
    funext s i
    obtain ⟨l0, l1, l2⟩ := Lop_apply (p := p) (chainOp P) v s
    obtain ⟨r2, r0, r1⟩ := hr' s
    obtain ⟨c0, -, -, -⟩ := hc' s
    have c1 := hcn s
    have v0 : v s 0 = zc s 0 - zr s 0 := rfl
    have v1 : v s 1 = zc s 1 - zr s 1 := rfl
    have v2 : v s 2 = zc s 0 - zr s 0 := rfl
    have hfr : (fun s' => zr s' 2) = fun s' => zr s' 0 := funext fun s' => (hr' s').1
    fin_cases i
    · simp only [Fin.zero_eta, Pi.zero_apply]
      rw [l0, v0, v1, v2, hM1, hM2]
      rw [hν] at r0
      rw [← hσ, ← hφ, ← hφy] at c0
      rw [← hσ] at r0
      linear_combination c0 - r0
    · simp only [Fin.mk_one, Pi.zero_apply]
      rw [l1, v0, v1, v2, hM1]
      rw [← hκ, ← hβ, ← hn s] at c1
      linear_combination p.ψ * c1 - p.ψ * r1 + (zc s 0 - zr s 0) * hk
    · simp only [Fin.reduceFinMk, Pi.zero_apply]
      rw [l2, v0, v2]; ring
  have hbd : ∀ s, ‖v s‖ ≤ ∑ s', ‖v s'‖ := fun s =>
    Finset.single_le_sum (f := fun s' => ‖v s'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ s)
  have h0 := Lop_injective hp (chainOp_isMarkov hP) hbd hL
  have e0 := congrFun (congrFun h0 s) 0
  have e1 := congrFun (congrFun h0 s) 1
  simp only [hv, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at e0 e1
  exact ⟨by linarith, by linarith⟩

/-! ## The second-order difference: dispersion versus resource cost -/

/-- Woodford (2003), Ch. 6, §2, (2.13) and App. E.2 (**Calvo dispersion is second order**): on
the price-index curve `α(e^{(θ−1)π} − 1) + (1−α)(e^{−(θ−1)x(π)} − 1) = 0` through zero, the
Calvo dispersion law `Δ′ = αΔe^{θ(1+ω)π} + (1−α)e^{−θ(1+ω)x}` has zero inflation derivative at
`Δ = 1`: relative-price dispersion is a second-order distortion. -/
theorem calvo_dispersion_first_order (c : NonlinearNKMarkov.Par) (hc : c.Std) {x : ℝ → ℝ}
    {x' : ℝ} (hx : HasDerivAt x x' 0) (hx0 : x 0 = 0)
    (hPI : ∀ π, c.α * (Real.exp ((c.θ - 1) * π) - 1) +
      (1 - c.α) * (Real.exp (-((c.θ - 1) * x π)) - 1) = 0) :
    HasDerivAt (fun π => c.α * 1 * Real.exp (c.θ * (1 + c.ω) * π) +
      (1 - c.α) * Real.exp (-(c.θ * (1 + c.ω) * x π))) 0 0 := by
  have hx' := NonlinearNKMarkovGoods.priceIndex_curve_deriv hc.α_lt_one hc.one_lt_θ hx hx0 hPI
  rw [hx'] at hx
  have h := NonlinearNKMarkovGoods.dispLaw_pi_deriv (a := c.θ * (1 + c.ω)) (Δ := 1)
    hc.α_lt_one hx hx0
  simpa using h

/-- Woodford (2003), Ch. 3, fn. 44 and Rotemberg (1982) (**the Rotemberg resource wedge**): the
ratio `C/Y = 1 − (ψ/2)(e^π − 1)²` of consumption to output at inflation `π`. -/
noncomputable def wedge (ψ π : ℝ) : ℝ := 1 - ψ / 2 * (Real.exp π - 1) ^ 2

/-- Woodford (2003), Ch. 3, fn. 44: the exact Rotemberg resource constraint (third component of
`Qmap`) says `C/Y = 1 − (ψ/2)(Π − 1)²`, `e^{ĉ−ŷ} = wedge ψ π`. -/
theorem resource_iff (p : NonlinearRotemberg.Par) (e x : Fin 3 → ℝ) :
    NonlinearRotemberg.Qmap p (e, x) 2 = 0 ↔ Real.exp (x 2 - x 0) = wedge p.ψ (x 1) := by
  simp only [NonlinearRotemberg.Qmap, Matrix.cons_val, wedge]
  rw [Real.exp_sub, div_eq_iff (Real.exp_pos _).ne', sub_eq_zero, mul_comm]

/-- The slope of the wedge: `d/dπ wedge = −ψ(e^π − 1)e^π`. -/
theorem hasDerivAt_wedge (ψ π : ℝ) :
    HasDerivAt (wedge ψ) (-(ψ * (Real.exp π - 1) * Real.exp π)) π := by
  have h := ((Real.hasDerivAt_exp π).sub_const 1).pow 2
  have h2 := (h.const_mul (ψ / 2)).const_sub 1
  refine h2.congr_deriv ?_
  simp only [Nat.cast_ofNat]
  ring

/-- The derivative of the slope at zero inflation is `−ψ`. -/
theorem hasDerivAt_wedge_slope (ψ : ℝ) :
    HasDerivAt (fun π => -(ψ * (Real.exp π - 1) * Real.exp π)) (-ψ) 0 := by
  have h := (((Real.hasDerivAt_exp 0).sub_const 1).const_mul ψ).mul (Real.hasDerivAt_exp 0)
  refine h.neg.congr_deriv ?_
  simp

/-- Woodford (2003), Ch. 3, fn. 44 (**the Rotemberg resource cost is second order with curvature
`−ψ`**): at zero inflation the wedge `C/Y` equals `1`, has slope `0` and second derivative `−ψ`;
for `ψ > 0` it is strictly below `1` at every nonzero inflation rate. -/
theorem rotemberg_resource_second_order (ψ : ℝ) :
    wedge ψ 0 = 1 ∧ deriv (wedge ψ) 0 = 0 ∧ deriv (deriv (wedge ψ)) 0 = -ψ ∧
      (0 < ψ → ∀ π, π ≠ 0 → wedge ψ π < 1) := by
  have hd : deriv (wedge ψ) = fun π => -(ψ * (Real.exp π - 1) * Real.exp π) :=
    funext fun π => (hasDerivAt_wedge ψ π).deriv
  refine ⟨by simp [wedge], by rw [hd]; simp, by rw [hd]; exact (hasDerivAt_wedge_slope ψ).deriv,
    fun hψ π hπ => ?_⟩
  have he : Real.exp π - 1 ≠ 0 := by
    rw [sub_ne_zero, Ne, Real.exp_eq_one_iff]; exact hπ
  have hsq : 0 < (Real.exp π - 1) ^ 2 := by positivity
  unfold wedge
  have : 0 < ψ / 2 * (Real.exp π - 1) ^ 2 := by positivity
  linarith

/-- Woodford (2003), Ch. 3, fn. 44 and Ch. 6, §2 (**an explicit second-order difference**): in
the Calvo model consumption equals output at every inflation rate (`C/Y ≡ 1`, curvature `0`;
the Calvo distortion is dispersion, `calvo_dispersion_first_order`), while in the Rotemberg model
the curvature of `C/Y` in inflation at zero inflation is `−ψ`. Under the equivalence map
(`first_order_agree`) the Rotemberg curvature is `−θmα(1+ωθ)/((1−α)(1−αβ)) < 0`, so the two
exact models, which agree to first order, differ at second order. -/
theorem second_order_difference (p : NonlinearRotemberg.Par) (c : NonlinearNKMarkov.Par)
    (hp : p.Basic)
    (hψ : p.ψ = p.θ * p.m * c.α * (1 + p.ω * p.θ) / ((1 - c.α) * (1 - c.α * p.β))) :
    deriv (deriv (fun _ : ℝ => (1 : ℝ))) 0 = 0 ∧
      deriv (deriv (wedge p.ψ)) 0 = -(p.θ * p.m * c.α * (1 + p.ω * p.θ) /
        ((1 - c.α) * (1 - c.α * p.β))) ∧
      deriv (deriv (wedge p.ψ)) 0 < 0 := by
  obtain ⟨-, -, h2, -⟩ := rotemberg_resource_second_order p.ψ
  refine ⟨by simp, by rw [h2, hψ], by rw [h2]; linarith [hp.ψ_pos]⟩

end Woodford.StabilizationWelfare.NonlinearRotembergLinks
