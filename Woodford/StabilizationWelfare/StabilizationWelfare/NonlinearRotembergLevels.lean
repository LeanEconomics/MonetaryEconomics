/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergMarkov

/-!
# The Rotemberg model in levels: equivalence, the firm's first-order condition, steady states

Woodford (2003), *Interest and Prices*, Chapter 3, §2 (pp. 177–188, the household and firm problems,
real marginal cost `s = v_y/u_c`, fn. 44 on Rotemberg (1987)), Chapter 4, §2.2 ((2.7)–(2.8), the
rule), and Rotemberg (1982), "Sticky prices in the United States", *JPE* 90.

* **`levels_iff`**: the three level conditions — the Euler equation with the rule
  `β(1+i)C^σ E[C′^{−σ}/Π′] = 1`, `1+i = β⁻¹Π^{φ_π}(Y/Ȳ)^{φ_y}e^ν`; the Rotemberg pricing condition
  `ψ(Π−1)Π = θ(mc − m) + β(C^σ/Y)E[C′^{−σ}Y′ψ(Π′−1)Π′]` with `mc = λ_v Y^ω C^σ e^{μ−(1+ω)a}`
  (`= v_y/u_c`); the resource constraint `C = Y(1 − (ψ/2)(Π−1)²)` — hold at a state iff the
  log-deviation residual `NonlinearRotembergNewton.PhiG (Qmap p) (Nmap p)` vanishes there, when
  `λ_v Ȳ^{ω+σ} = m` (the steady-state normalisation).
* **`firm_foc`**: the pricing condition is DERIVED: it is `Y_t⁻¹` times the derivative, at the
  symmetric point, of firm `i`'s objective `D_t(P_i) + βE[Λ D_{t+1}]` with respect to its log price.
* **`ybar_existsUnique`**, `zero_inflation_steady_state_unique`: the zero-inflation steady state is
  unique (`Ȳ = (m/λ_v)^{1/(σ+ω)}`); **`steady_state_unique_of_phiy_zero`**: with `φ_y = 0`,
  `φ_π ≠ 1` it is the ONLY steady state.
* **`second_steady_state`** (a correction): with `φ_y > 0` global uniqueness FAILS: at
  `β = 0.99, σ = ω = 1, θ = 6, ψ = 100, m = 5/6, φ_π = 1.5, φ_y = 0.125` (the Taylor principle
  holds) there is a second, deflationary steady state with `Π ∈ (0.88, 0.9)`.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergLevels

open Filter Topology
open NonlinearNKMarkov (Mv IsMarkov)
open NonlinearRotemberg NonlinearRotembergNewton

variable {p : Par} {X : Type*}

/-- `M(c·f) = c·M f` pointwise. -/
theorem M_smul (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (c : ℝ) (f : X → ℝ) (x : X) :
    M (fun x' => c * f x') x = c * M f x := by
  have : (fun x' => c * f x') = c • f := rfl
  rw [this, map_smul]; rfl

/-- `(Ȳe^y)^s = Ȳ^s e^{sy}` for `Ȳ > 0`. -/
theorem rpow_level {Yb : ℝ} (hY : 0 < Yb) (y s : ℝ) :
    (Yb * Real.exp y) ^ s = Yb ^ s * Real.exp (s * y) := by
  rw [Real.mul_rpow hY.le (Real.exp_pos y).le, ← Real.exp_mul, mul_comm y s]

/-- Woodford (2003), Ch. 4, (2.7)–(2.8) (**the Euler equation with the rule, in levels**): with
`Y = Ȳe^y`, `Π = e^π`, `C = Ȳe^c` and `X₀` the forecast of `e^{−σĉ′ − π′}`, the level condition
`β(1+i)C^σ·Ȳ^{−σ}X₀ = 1` is the residual condition `−e^{−(φ_π π + φ_y y + ν + σc)} + X₀ = 0`. -/
theorem euler_iff {β φ φy σ Yb : ℝ} (hβ : β ≠ 0) (hY : 0 < Yb) (y π c ν X0 : ℝ) :
    β * (β⁻¹ * Real.exp π ^ φ * (Yb * Real.exp y / Yb) ^ φy * Real.exp ν) *
        (Yb * Real.exp c) ^ σ * (Yb ^ (-σ) * X0) = 1 ↔
      -Real.exp (-(φ * π + φy * y + ν + σ * c)) + X0 = 0 := by
  have hYne := hY.ne'
  have e1 : β * (β⁻¹ * Real.exp π ^ φ * (Yb * Real.exp y / Yb) ^ φy * Real.exp ν) *
      (Yb * Real.exp c) ^ σ * (Yb ^ (-σ) * X0) =
      Real.exp (φ * π + φy * y + ν + σ * c) * X0 := by
    rw [mul_div_cancel_left₀ _ hYne, rpow_level hY, ← Real.exp_mul, ← Real.exp_mul,
      Real.rpow_neg hY.le, Real.exp_add, Real.exp_add, Real.exp_add]
    have : Yb ^ σ ≠ 0 := (Real.rpow_pos_of_pos hY σ).ne'
    field_simp
  rw [e1, Real.exp_neg]
  have hp := Real.exp_pos (φ * π + φy * y + ν + σ * c)
  constructor
  · intro h; field_simp; linarith
  · intro h
    have : X0 = (Real.exp (φ * π + φy * y + ν + σ * c))⁻¹ := by linarith
    rw [this]; field_simp

/-- Rotemberg (1982) in Woodford's notation (**the pricing condition in levels**): with
`λ_v Ȳ^{ω+σ} = m`, `Y = Ȳe^{x₀}`, `Π = e^{x₁}`, `C = Ȳe^{x₂}` and `G′` the forecast of the
next-period adjustment term, the level condition
`ψ(Π−1)Π = θ(mc − m) + β(C^σ/Y)·Ȳ^{1−σ}G′` is the residual condition `G(x) − H(e, x) − βG′ = 0`. -/
theorem price_iff {Yb lv : ℝ} (hY : 0 < Yb) (hss : lv * Yb ^ (p.ω + p.σ) = p.m)
    (x e : Fin 3 → ℝ) (G' : ℝ) :
    p.ψ * (Real.exp (x 1) - 1) * Real.exp (x 1) =
        p.θ * (lv * (Yb * Real.exp (x 0)) ^ p.ω * (Yb * Real.exp (x 2)) ^ p.σ *
          Real.exp (e 2 - (1 + p.ω) * e 1) - p.m) +
        p.β * ((Yb * Real.exp (x 2)) ^ p.σ / (Yb * Real.exp (x 0))) * (Yb ^ (1 - p.σ) * G') ↔
      Gadj p x - Hmc p e x + -(p.β * G') = 0 := by
  have hYne := hY.ne'
  have hmc : lv * (Yb * Real.exp (x 0)) ^ p.ω * (Yb * Real.exp (x 2)) ^ p.σ *
      Real.exp (e 2 - (1 + p.ω) * e 1) =
      p.m * Real.exp (p.ω * x 0 + p.σ * x 2 + (e 2 - (1 + p.ω) * e 1)) := by
    rw [rpow_level hY, rpow_level hY, ← hss, Real.rpow_add hY, Real.exp_add, Real.exp_add]
    ring
  have hratio : (Yb * Real.exp (x 2)) ^ p.σ / (Yb * Real.exp (x 0)) * Yb ^ (1 - p.σ) =
      Real.exp (p.σ * x 2 - x 0) := by
    rw [rpow_level hY, Real.rpow_sub hY, Real.rpow_one, Real.exp_sub]
    have : Yb ^ p.σ ≠ 0 := (Real.rpow_pos_of_pos hY _).ne'
    field_simp
  have e2 : p.β * ((Yb * Real.exp (x 2)) ^ p.σ / (Yb * Real.exp (x 0))) *
      (Yb ^ (1 - p.σ) * G') = p.β * Real.exp (p.σ * x 2 - x 0) * G' := by
    rw [← hratio]; ring
  rw [hmc, e2]
  have hk : Real.exp (x 0 - p.σ * x 2) * Real.exp (p.σ * x 2 - x 0) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (x 0 - p.σ * x 2)
  have hH : Hmc p e x = p.θ * p.m * Real.exp (x 0 - p.σ * x 2) *
      (Real.exp (p.ω * x 0 + p.σ * x 2 + (e 2 - (1 + p.ω) * e 1)) - 1) := by
    have h3 : Real.exp (x 0 - p.σ * x 2) *
        Real.exp (p.ω * x 0 + p.σ * x 2 + (e 2 - (1 + p.ω) * e 1)) =
        Real.exp ((1 + p.ω) * x 0 + e 2 - (1 + p.ω) * e 1) := by
      rw [← Real.exp_add]; ring_nf
    unfold Hmc
    rw [← h3]; ring
  have hG : Gadj p x = Real.exp (x 0 - p.σ * x 2) *
      (p.ψ * (Real.exp (x 1) - 1) * Real.exp (x 1)) := by
    unfold Gadj; ring
  rw [hH, hG]
  constructor
  · intro h
    rw [h]
    linear_combination (p.β * G') * hk
  · intro h
    have h2 : Real.exp (x 0 - p.σ * x 2) * (p.ψ * (Real.exp (x 1) - 1) * Real.exp (x 1) -
        (p.θ * (p.m * Real.exp (p.ω * x 0 + p.σ * x 2 + (e 2 - (1 + p.ω) * e 1)) - p.m) +
          p.β * Real.exp (p.σ * x 2 - x 0) * G')) = 0 := by
      linear_combination h - (p.β * G') * hk
    have := (mul_eq_zero.1 h2).resolve_left hpos.ne'
    linarith

/-- Woodford (2003), Ch. 3 §2 and Ch. 4 (2.7)–(2.8), with Rotemberg (1982) pricing (**THE LEVEL
MODEL IS THE LOG-DEVIATION MODEL**). Let `Ȳ, λ_v > 0` with `λ_v Ȳ^{ω+σ} = m`, and at every state
`Y = Ȳe^{ŷ}`, `Π = e^{π}`, `C = Ȳe^{ĉ}` (every positive level can be so written). Then at a state
`x` the Euler equation with the rule, the Rotemberg pricing condition and the resource constraint
hold in levels iff `Φ(z)(x) = 0`. -/
theorem levels_iff (hβ : p.β ≠ 0) {Yb lv : ℝ} (hY : 0 < Yb) (hss : lv * Yb ^ (p.ω + p.σ) = p.m)
    (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (e z : X → Fin 3 → ℝ) (x : X) :
    (p.β * (p.β⁻¹ * Real.exp (z x 1) ^ p.φ * (Yb * Real.exp (z x 0) / Yb) ^ p.φy *
        Real.exp (e x 0)) * (Yb * Real.exp (z x 2)) ^ p.σ *
        M (fun x' => (Yb * Real.exp (z x' 2)) ^ (-p.σ) / Real.exp (z x' 1)) x = 1 ∧
      p.ψ * (Real.exp (z x 1) - 1) * Real.exp (z x 1) =
        p.θ * (lv * (Yb * Real.exp (z x 0)) ^ p.ω * (Yb * Real.exp (z x 2)) ^ p.σ *
          Real.exp (e x 2 - (1 + p.ω) * e x 1) - p.m) +
        p.β * ((Yb * Real.exp (z x 2)) ^ p.σ / (Yb * Real.exp (z x 0))) *
          M (fun x' => (Yb * Real.exp (z x' 2)) ^ (-p.σ) * (Yb * Real.exp (z x' 0)) *
            (p.ψ * (Real.exp (z x' 1) - 1) * Real.exp (z x' 1))) x ∧
      Yb * Real.exp (z x 2) = Yb * Real.exp (z x 0) *
        (1 - p.ψ / 2 * (Real.exp (z x 1) - 1) ^ 2)) ↔
    PhiG (Qmap p) (Nmap p) M e z x = 0 := by
  have hM1 : M (fun x' => (Yb * Real.exp (z x' 2)) ^ (-p.σ) / Real.exp (z x' 1)) x =
      Yb ^ (-p.σ) * M (fun x' => Real.exp (-(p.σ * z x' 2) - z x' 1)) x := by
    have hfg : (fun x' => (Yb * Real.exp (z x' 2)) ^ (-p.σ) / Real.exp (z x' 1)) =
        fun x' => Yb ^ (-p.σ) * Real.exp (-(p.σ * z x' 2) - z x' 1) := by
      funext x'
      rw [rpow_level hY, Real.exp_sub, neg_mul]
      field_simp
    rw [hfg, M_smul]
  have hM2 : M (fun x' => (Yb * Real.exp (z x' 2)) ^ (-p.σ) * (Yb * Real.exp (z x' 0)) *
      (p.ψ * (Real.exp (z x' 1) - 1) * Real.exp (z x' 1))) x =
      Yb ^ (1 - p.σ) * M (fun x' => Gadj p (z x')) x := by
    have hfg : (fun x' => (Yb * Real.exp (z x' 2)) ^ (-p.σ) * (Yb * Real.exp (z x' 0)) *
        (p.ψ * (Real.exp (z x' 1) - 1) * Real.exp (z x' 1))) =
        fun x' => Yb ^ (1 - p.σ) * Gadj p (z x') := by
      funext x'
      rw [rpow_level hY, Gadj, Real.rpow_sub hY, Real.rpow_one, Real.exp_sub, Real.rpow_neg hY.le,
        neg_mul, Real.exp_neg]
      have : Yb ^ p.σ ≠ 0 := (Real.rpow_pos_of_pos hY _).ne'
      field_simp
    rw [hfg, M_smul]
  have hN0 : Mv M (fun x' => Nmap p (e x', z x')) x 0 =
      M (fun x' => Real.exp (-(p.σ * z x' 2) - z x' 1)) x := rfl
  have hN1 : Mv M (fun x' => Nmap p (e x', z x')) x 1 =
      -(p.β * M (fun x' => Gadj p (z x')) x) := by
    change M (fun x' => -(p.β * Gadj p (z x'))) x = _
    have := M_smul M (-p.β) (fun x' => Gadj p (z x')) x
    simp only [neg_mul] at this ⊢
    rw [this]
  have hN2 : Mv M (fun x' => Nmap p (e x', z x')) x 2 = 0 := by
    change M (fun _ => (0 : ℝ)) x = 0
    have : (fun _ : X => (0 : ℝ)) = 0 := rfl
    rw [this, map_zero]; rfl
  have hE := euler_iff (φ := p.φ) (φy := p.φy) (σ := p.σ) hβ hY (z x 0) (z x 1) (z x 2) (e x 0)
    (M (fun x' => Real.exp (-(p.σ * z x' 2) - z x' 1)) x)
  have hP := price_iff (p := p) hY hss (z x) (e x) (M (fun x' => Gadj p (z x')) x)
  rw [hM1, hM2, hE, hP]
  have hR : Yb * Real.exp (z x 2) = Yb * Real.exp (z x 0) *
      (1 - p.ψ / 2 * (Real.exp (z x 1) - 1) ^ 2) ↔
      Real.exp (z x 2) - Real.exp (z x 0) * (1 - p.ψ / 2 * (Real.exp (z x 1) - 1) ^ 2) + 0 = 0 := by
    constructor
    · intro h
      have := mul_left_cancel₀ hY.ne' (h.trans (mul_assoc _ _ _))
      rw [this]; ring
    · intro h
      have : Real.exp (z x 2) = Real.exp (z x 0) * (1 - p.ψ / 2 * (Real.exp (z x 1) - 1) ^ 2) := by
        linarith
      rw [this]; ring
  rw [hR]
  constructor
  · rintro ⟨h0, h1, h2⟩
    funext i
    fin_cases i
    · simp only [PhiG, Pi.add_apply, Pi.zero_apply, Fin.zero_eta, Qmap, Matrix.cons_val_zero]
      rw [hN0]; linarith
    · simp only [PhiG, Pi.add_apply, Pi.zero_apply, Fin.mk_one, Qmap, Matrix.cons_val_one,
        Matrix.cons_val_zero]
      rw [hN1]; exact h1
    · simp only [PhiG, Pi.add_apply, Pi.zero_apply, Fin.reduceFinMk, Qmap, Matrix.cons_val]
      rw [hN2]; exact h2
  · intro h
    have c0 := congrFun h 0
    have c1 := congrFun h 1
    have c2 := congrFun h 2
    simp only [PhiG, Pi.add_apply, Pi.zero_apply, Qmap, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val] at c0 c1 c2
    rw [hN0] at c0
    rw [hN1] at c1
    rw [hN2] at c2
    exact ⟨by linarith, c1, c2⟩

/-! ## The firm's first-order condition is derived -/

/-- Rotemberg (1982) and Woodford (2003), Ch. 3 §2 (**the pricing condition is the firm's
first-order condition**). Firm `i` chooses its log price `q` (`P_i = e^q`) given the price level
`P`, its own last price `P₋`, output `Y`, consumption `C`, the subsidy `1 + τ` with
`(1+τ)(θ−1) = θm`, and the cost `Ψ(y) = λ_v C^σ e^u y^{1+ω}/(1+ω)` of producing
`y = (P_i/P)^{−θ}Y` (so `Ψ′(Y) = mc = λ_v Y^ω C^σ e^u = v_y/u_c`). Its objective is current real
profit plus the discounted expected adjustment cost it causes next period,
`J(q) = (1+τ)e^{(1−θ)(q−log P)}Y − Ψ(e^{−θ(q−log P)}Y) − (ψ/2)(e^q/P₋ − 1)²Y
  + β ∑_s w_s Λ_s [−(ψ/2)(P Π′_s e^{−q} − 1)² Y′_s]`
over finitely many successor states with probabilities `w_s` and stochastic discount factors
`Λ_s = (C′_s/C)^{−σ}`. At the symmetric point `q = log P` its derivative is
`Y·[θ(mc − m) − ψ(Π − 1)Π + β ∑_s w_s Λ_s (Y′_s/Y) ψ(Π′_s − 1)Π′_s]`, `Π = P/P₋`: it vanishes iff
the Rotemberg pricing condition holds. -/
theorem firm_foc {S : Type*} [Fintype S] {θ m ω σ ψ β τ lv C u P Pm Y : ℝ}
    (hτ : (1 + τ) * (θ - 1) = θ * m) (hP : 0 < P) (hY : 0 < Y)
    (w Λ Pn Y' : S → ℝ) (hω : 1 + ω ≠ 0) :
    HasDerivAt (fun q => (1 + τ) * Real.exp ((1 - θ) * (q - Real.log P)) * Y -
        lv * C ^ σ * Real.exp u * Y ^ (1 + ω) / (1 + ω) *
          Real.exp (-θ * (1 + ω) * (q - Real.log P)) -
        ψ / 2 * (Real.exp q / Pm - 1) ^ 2 * Y +
        β * ∑ s, w s * Λ s * (-(ψ / 2) * (P * Pn s / Real.exp q - 1) ^ 2 * Y' s))
      (Y * (θ * (lv * Y ^ ω * C ^ σ * Real.exp u - m) - ψ * (P / Pm - 1) * (P / Pm) +
        β * ∑ s, w s * Λ s * (Y' s / Y) * (ψ * (Pn s - 1) * Pn s))) (Real.log P) := by
  have hexp : Real.exp (Real.log P) = P := Real.exp_log hP
  have h1 : HasDerivAt (fun q => (1 + τ) * Real.exp ((1 - θ) * (q - Real.log P)) * Y)
      ((1 + τ) * (1 - θ) * Y) (Real.log P) := by
    have := (((hasDerivAt_id (Real.log P)).sub_const (Real.log P)).const_mul (1 - θ)).exp
    have := (this.const_mul (1 + τ)).mul_const Y
    refine this.congr_deriv ?_
    simp
  have h2 : HasDerivAt (fun q => lv * C ^ σ * Real.exp u * Y ^ (1 + ω) / (1 + ω) *
      Real.exp (-θ * (1 + ω) * (q - Real.log P)))
      (lv * C ^ σ * Real.exp u * Y ^ (1 + ω) / (1 + ω) * (-θ * (1 + ω))) (Real.log P) := by
    have := (((hasDerivAt_id (Real.log P)).sub_const (Real.log P)).const_mul
      (-θ * (1 + ω))).exp.const_mul (lv * C ^ σ * Real.exp u * Y ^ (1 + ω) / (1 + ω))
    refine this.congr_deriv ?_
    simp
  have h3 : HasDerivAt (fun q => ψ / 2 * (Real.exp q / Pm - 1) ^ 2 * Y)
      (ψ * (P / Pm - 1) * (P / Pm) * Y) (Real.log P) := by
    have := ((((Real.hasDerivAt_exp (Real.log P)).div_const Pm).sub_const 1).pow 2).const_mul
      (ψ / 2) |>.mul_const Y
    convert this using 1
    rw [hexp]; push_cast; ring
  have h4 : ∀ s ∈ (Finset.univ : Finset S), HasDerivAt
      (fun q => w s * Λ s * (-(ψ / 2) * (P * Pn s / Real.exp q - 1) ^ 2 * Y' s))
      (w s * Λ s * (ψ * (Pn s - 1) * Pn s * Y' s)) (Real.log P) := by
    intro s _
    have hinv := (Real.hasDerivAt_exp (Real.log P)).inv (Real.exp_pos _).ne'
    have := ((((hinv.const_mul (P * Pn s)).sub_const 1).pow 2).const_mul (-(ψ / 2))).mul_const
      (Y' s) |>.const_mul (w s * Λ s)
    convert this using 1
    · funext q; simp [div_eq_mul_inv]
    · simp only [Pi.inv_apply, hexp]; field_simp; push_cast; ring
  have h := ((h1.sub h2).sub h3).add ((HasDerivAt.sum h4).const_mul β)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun q => ?_)).congr_deriv ?_
  · simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_apply]
  · have hmc : lv * C ^ σ * Real.exp u * Y ^ (1 + ω) / (1 + ω) * (-θ * (1 + ω)) =
        -(θ * (lv * Y ^ ω * C ^ σ * Real.exp u) * Y) := by
      rw [Real.rpow_add hY, Real.rpow_one]; field_simp
    rw [hmc]
    have e1 : (1 + τ) * (1 - θ) = -(θ * m) := by linarith
    rw [e1]
    have hsum : Y * (β * ∑ i, w i * Λ i * (Y' i / Y) * (ψ * (Pn i - 1) * Pn i)) =
        β * ∑ i, w i * Λ i * (ψ * (Pn i - 1) * Pn i * Y' i) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by field_simp
    rw [mul_add, hsum]
    ring

/-! ## Steady states -/

/-- Woodford (2003), Ch. 3 §2 (**the zero-inflation steady-state output is unique**): for
`λ_v, m > 0` and `σ + ω > 0` there is exactly one `Ȳ > 0` with `λ_v Ȳ^{ω+σ} = m`
(`Ȳ = (m/λ_v)^{1/(ω+σ)}`). -/
theorem ybar_existsUnique {lv m s : ℝ} (hlv : 0 < lv) (hm : 0 < m) (hs : 0 < s) :
    ∃! Y : ℝ, 0 < Y ∧ lv * Y ^ s = m := by
  refine ⟨(m / lv) ^ (1 / s), ⟨Real.rpow_pos_of_pos (div_pos hm hlv) _, ?_⟩, ?_⟩
  · rw [← Real.rpow_mul (div_pos hm hlv).le, one_div, inv_mul_cancel₀ hs.ne', Real.rpow_one]
    field_simp
  · rintro Y ⟨hY, hYs⟩
    have : Y ^ s = m / lv := by rw [eq_div_iff hlv.ne']; linarith
    rw [← this, ← Real.rpow_mul hY.le, one_div, mul_inv_cancel₀ hs.ne', Real.rpow_one]

/-- Woodford (2003), Ch. 3 §2 with Rotemberg pricing (**the zero-inflation steady state is the
only steady state with zero inflation**): a constant `x` with `π = 0` solving the conditions
without disturbances is `x = 0` (for every rule). -/
theorem zero_inflation_steady_state_unique (hp : p.Basic) (x : Fin 3 → ℝ) (hx1 : x 1 = 0)
    (h : Qmap p (0, x) + Nmap p (0, x) = 0) : x = 0 := by
  have c1 := congrFun h 1
  have c2 := congrFun h 2
  simp only [Qmap, Nmap, Pi.add_apply, Pi.zero_apply, Matrix.cons_val_one,
    Matrix.cons_val_zero, Matrix.cons_val, Gadj, Hmc, hx1, Real.exp_zero, sub_self, zero_mul,
    mul_zero, add_zero] at c1 c2
  have h2 : x 2 = x 0 := by
    have : Real.exp (x 2) = Real.exp (x 0) := by
      norm_num at c2; linarith
    exact Real.exp_injective this
  have hθm : 0 < p.θ * p.m := mul_pos (by linarith [hp.one_lt_θ]) hp.m_pos
  have h0 : x 0 = 0 := by
    have e : Real.exp ((1 + p.ω) * x 0) = Real.exp (x 0 - p.σ * x 2) := by
      have := c1
      simp only [sub_zero, zero_sub, add_zero, neg_zero] at this
      have : p.θ * p.m * (Real.exp ((1 + p.ω) * x 0) - Real.exp (x 0 - p.σ * x 2)) = 0 := by
        linarith
      have := (mul_eq_zero.1 this).resolve_left hθm.ne'
      linarith
    have := Real.exp_injective e
    rw [h2] at this
    have hs : 0 < p.σ + p.ω := by linarith [hp.σ_pos, hp.ω_nonneg]
    nlinarith
  funext i
  fin_cases i
  · exact h0
  · exact hx1
  · simp only [Fin.reduceFinMk, Fin.isValue, Pi.zero_apply]; rw [h2, h0]

/-- Woodford (2003), Ch. 4 (2.7) with Rotemberg pricing (**global uniqueness of the steady state
under an inflation-only rule**): if `φ_y = 0` and `φ_π ≠ 1`, the zero-inflation steady state is
the ONLY steady state. -/
theorem steady_state_unique_of_phiy_zero (hp : p.Basic) (hφy : p.φy = 0) (hφ : p.φ ≠ 1)
    (x : Fin 3 → ℝ) (h : Qmap p (0, x) + Nmap p (0, x) = 0) : x = 0 := by
  have c0 := congrFun h 0
  simp only [Qmap, Nmap, Pi.add_apply, Pi.zero_apply, Matrix.cons_val_zero, hφy, zero_mul,
    add_zero] at c0
  have e : Real.exp (-(p.φ * x 1 + p.σ * x 2)) = Real.exp (-(p.σ * x 2) - x 1) := by linarith
  have e2 := Real.exp_injective e
  have hx1 : x 1 = 0 := by
    have : (p.φ - 1) * x 1 = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hφ)
  exact zero_inflation_steady_state_unique hp x hx1 h

/-- The parameters of the counterexample: `β = 0.99`, `σ = ω = 1`, `θ = 6`, `ψ = 100`,
`m = 5/6` (no subsidy), `φ_π = 1.5`, `φ_y = 0.125`. -/
noncomputable def pc : Par := ⟨99 / 100, 1, 1, 6, 100, 5 / 6, 3 / 2, 1 / 8⟩

/-- The counterexample parameters satisfy the maintained restrictions and the Taylor principle
(`κ = 0.1`). -/
theorem pc_std : pc.Std := by
  have hκ : pc.κ = 1 / 10 := by simp only [Par.κ, pc]; norm_num
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals first
    | (rw [hκ]; simp only [pc]; norm_num)
    | (simp only [pc]; norm_num)

/-- The steady-state residual of the counterexample as a function of log inflation `π`
(with `ŷ = −4π` from the rule and `ĉ = ŷ + log f(π)`):
`g(π) = 5(f(π)e^{−8π} − 1) − (e^π − 1)e^π`, `f(π) = 1 − 50(e^π − 1)²`. -/
noncomputable def gss (π : ℝ) : ℝ :=
  5 * ((1 - 50 * (Real.exp π - 1) ^ 2) * Real.exp (-8 * π) - 1) - (Real.exp π - 1) * Real.exp π

/-- `e^{−8 log q} = (1/q)⁸`. -/
theorem exp_neg8_log {q : ℝ} (hq : 0 < q) : Real.exp (-8 * Real.log q) = (1 / q) ^ 8 := by
  rw [show -8 * Real.log q = ((8 : ℕ) : ℝ) * Real.log (1 / q) by
    rw [one_div, Real.log_inv]; push_cast; ring, Real.exp_nat_mul,
    Real.exp_log (by positivity)]

/-- The residual is negative at `Π = 0.88`. -/
theorem gss_lo : gss (Real.log (22 / 25)) < 0 := by
  unfold gss
  rw [exp_neg8_log (by norm_num), Real.exp_log (by norm_num)]
  norm_num

/-- The residual is positive at `Π = 0.9`. -/
theorem gss_hi : 0 < gss (Real.log (9 / 10)) := by
  unfold gss
  rw [exp_neg8_log (by norm_num), Real.exp_log (by norm_num)]
  norm_num

/-- Woodford (2003), Ch. 3 §2 and Ch. 4 (2.7) with Rotemberg pricing (**a CORRECTION: the
steady state is NOT globally unique when the rule responds to output**). At the parameters `pc`
(which satisfy the Taylor principle) there is a second steady state `z ≠ 0`: a deflationary one
with `Π = e^π ∈ (0.88, 0.9)`, `Y/Ȳ = Π^{−4}` (the rule `Π^{φ_π−1}(Y/Ȳ)^{φ_y} = 1`) and
`C = Y(1 − 50(Π − 1)²) > 0`. -/
theorem second_steady_state :
    ∃ z : Fin 3 → ℝ, z ≠ 0 ∧ Real.log (22 / 25) ≤ z 1 ∧ z 1 ≤ Real.log (9 / 10) ∧
      Qmap pc (0, z) + Nmap pc (0, z) = 0 := by
  have hab : Real.log (22 / 25) ≤ Real.log (9 / 10) :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hc : ContinuousOn gss (Set.Icc (Real.log (22 / 25)) (Real.log (9 / 10))) := by
    unfold gss; fun_prop
  obtain ⟨π, ⟨hπ1, hπ2⟩, hg⟩ := intermediate_value_Icc hab hc ⟨gss_lo.le, gss_hi.le⟩
  have hE1 : 22 / 25 ≤ Real.exp π := by
    have := Real.exp_le_exp.2 hπ1; rwa [Real.exp_log (by norm_num)] at this
  have hE2 : Real.exp π ≤ 9 / 10 := by
    have := Real.exp_le_exp.2 hπ2; rwa [Real.exp_log (by norm_num)] at this
  set f := 1 - 50 * (Real.exp π - 1) ^ 2 with hf
  have hf0 : 0 < f := by rw [hf]; nlinarith
  have hπ0 : π < 0 := lt_of_le_of_lt hπ2 (Real.log_neg (by norm_num) (by norm_num))
  refine ⟨![-4 * π, π, -4 * π + Real.log f], ?_, hπ1, hπ2, ?_⟩
  · intro h
    have := congrFun h 1
    simp at this
    linarith
  · have hexpc : Real.exp (-4 * π + Real.log f) = Real.exp (-4 * π) * f := by
      rw [Real.exp_add, Real.exp_log hf0]
    funext i
    fin_cases i
    · simp only [Qmap, Nmap, pc, Pi.add_apply, Pi.zero_apply, Fin.zero_eta,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      have : -((3 / 2 : ℝ) * π + 1 / 8 * (-4 * π) + 0 + 1 * (-4 * π + Real.log f)) =
          -(1 * (-4 * π + Real.log f)) - π := by ring
      rw [this]; ring
    · simp only [Qmap, Nmap, pc, Pi.add_apply, Pi.zero_apply, Fin.mk_one, Gadj, Hmc,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      unfold gss at hg
      have e1 : Real.exp (-4 * π - 1 * (-4 * π + Real.log f)) = f⁻¹ := by
        rw [show -4 * π - 1 * (-4 * π + Real.log f) = -Real.log f by ring, Real.exp_neg,
          Real.exp_log hf0]
      have e2 : Real.exp ((1 + 1) * (-4 * π) + 0 - (1 + 1) * 0) = Real.exp (-8 * π) := by
        congr 1; ring
      rw [e1, e2]
      set E8 := Real.exp (-8 * π) with hE8
      set Ep := Real.exp π with hEp
      rw [hf]
      rw [hf] at hf0
      field_simp
      linear_combination (-(1 : ℝ)) * hg
    · simp only [Qmap, Nmap, pc, Pi.add_apply, Pi.zero_apply, Fin.reduceFinMk,
        Matrix.cons_val]
      rw [hexpc, hf]; ring

end Woodford.StabilizationWelfare.NonlinearRotembergLevels
