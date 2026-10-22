/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergLinks

/-!
# Rotemberg and Calvo: the discounted second-order costs of inflation coincide under the map

Woodford (2003), *Interest and Prices*, Chapter 6, §2 (pp. 393–400) and Appendix E.2 (p. 695:
the law of motion of relative-price dispersion and its second-order approximation), and
Chapter 3, footnote 44 (p. 188: the Rotemberg (1982) adjustment-cost model).

In the Calvo model the welfare cost of inflation is the extra disutility of supplying dispersed
output, `v(Ȳ)(Δ_t − 1)` with `v(Y) = A Y^{1+ω}/(1+ω)` and `v′(Ȳ)Ȳ = m·u_c Ȳ` (the distortion
`Φ = 1 − m`), i.e. `m/(1+ω)·(Δ_t − 1)` in units of `u_c Ȳ`. In the Rotemberg model it is the
resource cost `C/Y = 1 − (ψ/2)(Π − 1)²`, i.e. `(ψ/2)π_t²` in the same units.

## Main results

* **`disp_on_curve`**: on the price-index curve the exact Calvo dispersion law at `Δ = 1` is the
  closed form `fdisp π = αe^{aπ} + (1−α)^{1−a/b}(1 − αe^{bπ})^{a/b}`, `a = θ(1+ω)`, `b = θ−1`.
* **`fdisp_second_order`**: `fdisp 0 = 1`, `fdisp′(0) = 0`, `fdisp″(0) = αa(a−b)/(1−α)
  = αθ(1+ω)(1+ωθ)/(1−α)`: the second-order dispersion law is
  `D_t = αD_{t−1} + c_C π_t²` with `c_C = αθ(1+ω)(1+ωθ)/(2(1−α))`.
* **`cost_coefficients_eq`**: under the equivalence map `ψ = θmα(1+ωθ)/((1−α)(1−αβ))`,
  `m/(1+ω) · c_C/(1−αβ) = ψ/2`, for EVERY distortion `m`.
* **`discounted_cost_equiv`**: for every bounded inflation path, with dispersion starting at
  `Δ_{−1} = 1`, the discounted Calvo dispersion cost `Σ βᵗ m/(1+ω)·D_t` equals the discounted
  Rotemberg resource cost `Σ βᵗ (ψ/2)π_t²`.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergWelfare

open Filter Topology Finset

/-! ## The Calvo dispersion law at `Δ = 1` on the price-index curve -/

/-- Woodford (2003), App. E.2: the exact Calvo dispersion law at `Δ = 1` on the price-index
curve, `αe^{aπ} + (1−α)^{1−a/b}(1 − αe^{bπ})^{a/b}`. -/
noncomputable def fdisp (α a b π : ℝ) : ℝ :=
  α * Real.exp (a * π) + (1 - α) ^ (1 - a / b) * (1 - α * Real.exp (b * π)) ^ (a / b)

/-- Woodford (2003), App. E.2 (**the dispersion law on the price-index curve in closed form**): if
`α(e^{bπ} − 1) + (1−α)(e^{−bx} − 1) = 0` (the price index, `b = θ − 1`), then
`αΔe^{aπ} + (1−α)e^{−ax}` at `Δ = 1` equals `fdisp α a b π`. -/
theorem disp_on_curve {α a b π x : ℝ} (hα1 : α < 1) (hb : b ≠ 0)
    (hPI : α * (Real.exp (b * π) - 1) + (1 - α) * (Real.exp (-(b * x)) - 1) = 0) :
    α * 1 * Real.exp (a * π) + (1 - α) * Real.exp (-(a * x)) = fdisp α a b π := by
  have h1α : 0 < 1 - α := by linarith
  have hg : Real.exp (-(b * x)) = (1 - α * Real.exp (b * π)) / (1 - α) := by
    rw [eq_div_iff h1α.ne']; linear_combination hPI
  have hpos : 0 < (1 - α * Real.exp (b * π)) / (1 - α) := by rw [← hg]; exact Real.exp_pos _
  have hgp : 0 < 1 - α * Real.exp (b * π) := by
    have := mul_pos hpos h1α; rwa [div_mul_cancel₀ _ h1α.ne'] at this
  have hax : Real.exp (-(a * x)) = ((1 - α * Real.exp (b * π)) / (1 - α)) ^ (a / b) := by
    rw [← hg, ← Real.exp_mul]; congr 1; field_simp
  unfold fdisp
  rw [hax, Real.div_rpow hgp.le h1α.le, Real.rpow_sub h1α, Real.rpow_one]
  field_simp

/-- The slope of `fdisp` where `αe^{bπ} < 1`. -/
noncomputable def fdisp1 (α a b π : ℝ) : ℝ :=
  α * a * Real.exp (a * π) + (1 - α) ^ (1 - a / b) *
    ((-(α * b) * Real.exp (b * π)) * (a / b) * (1 - α * Real.exp (b * π)) ^ (a / b - 1))

/-- `fdisp′ = fdisp1` where `αe^{bπ} < 1`. -/
theorem hasDerivAt_fdisp {α a b π : ℝ} (hg : 0 < 1 - α * Real.exp (b * π)) :
    HasDerivAt (fdisp α a b) (fdisp1 α a b π) π := by
  have h1 := ((Real.hasDerivAt_exp (a * π)).comp π ((hasDerivAt_id π).const_mul a)).const_mul α
  have hgd : HasDerivAt (fun π => 1 - α * Real.exp (b * π)) (-(α * (Real.exp (b * π) * b))) π :=
    (((Real.hasDerivAt_exp (b * π)).comp π ((hasDerivAt_id π).const_mul b)).const_mul α).const_sub 1
      |>.congr_deriv (by simp)
  have h2 := (hgd.rpow_const (p := a / b) (Or.inl hg.ne')).const_mul ((1 - α) ^ (1 - a / b))
  refine (h1.add h2).congr_deriv ?_
  simp only [fdisp1]
  ring

/-- Woodford (2003), App. E.2: `αe^{bπ} < 1` near `π = 0`. -/
theorem eventually_pos {α b : ℝ} (hα1 : α < 1) :
    ∀ᶠ π in 𝓝 (0 : ℝ), 0 < 1 - α * Real.exp (b * π) := by
  have hc : Continuous fun π : ℝ => 1 - α * Real.exp (b * π) := by fun_prop
  have h0 : 0 < 1 - α * Real.exp (b * 0) := by simp; linarith
  exact hc.continuousAt.eventually (lt_mem_nhds h0)

/-- Woodford (2003), App. E.2, p. 695 (**the second-order dispersion law**): `fdisp 0 = 1`,
`fdisp′(0) = 0` and `fdisp″(0) = αa(a − b)/(1 − α)`; with `a = θ(1+ω)`, `b = θ − 1` this is
`αθ(1+ω)(1+ωθ)/(1−α)`, so `Δ_t − 1 ≈ α(Δ_{t−1} − 1) + c_C π_t²`, `c_C = αθ(1+ω)(1+ωθ)/(2(1−α))`. -/
theorem fdisp_second_order {α a b : ℝ} (hα1 : α < 1) (hb : b ≠ 0) :
    fdisp α a b 0 = 1 ∧ deriv (fdisp α a b) 0 = 0 ∧
      deriv (deriv (fdisp α a b)) 0 = α * a * (a - b) / (1 - α) := by
  have h1α : 0 < 1 - α := by linarith
  have hk : (1 - α) ^ (1 - a / b) * (1 - α) ^ (a / b - 1) = 1 := by
    rw [← Real.rpow_add h1α]; simp
  have hk2 : (1 - α) ^ (1 - a / b) * (1 - α) ^ (a / b - 1 - 1) = 1 / (1 - α) := by
    rw [← Real.rpow_add h1α]
    have : 1 - a / b + (a / b - 1 - 1) = -1 := by ring
    rw [this, Real.rpow_neg_one, one_div]
  have hg0 : 0 < 1 - α * Real.exp (b * 0) := by simp; linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold fdisp
    simp only [mul_zero, Real.exp_zero, mul_one]
    rw [← Real.rpow_add h1α]; simp
  · rw [(hasDerivAt_fdisp hg0).deriv]
    simp only [fdisp1, mul_zero, Real.exp_zero, mul_one]
    have e : (1 - α) ^ (1 - a / b) * (-(α * b) * (a / b) * (1 - α) ^ (a / b - 1)) =
        -(α * b) * (a / b) * ((1 - α) ^ (1 - a / b) * (1 - α) ^ (a / b - 1)) := by ring
    rw [e, hk]; field_simp; ring
  · have hev : deriv (fdisp α a b) =ᶠ[𝓝 0] fdisp1 α a b :=
      (eventually_pos (b := b) hα1).mono fun π h => (hasDerivAt_fdisp h).deriv
    rw [hev.deriv_eq]
    -- the derivative of the slope at zero
    have he := ((Real.hasDerivAt_exp (a * 0)).comp 0 ((hasDerivAt_id (0 : ℝ)).const_mul a))
    have hb' := ((Real.hasDerivAt_exp (b * 0)).comp 0 ((hasDerivAt_id (0 : ℝ)).const_mul b))
    have hgd : HasDerivAt (fun π => 1 - α * Real.exp (b * π)) (-(α * (Real.exp (b * 0) * b)))
        0 := (hb'.const_mul α).const_sub 1 |>.congr_deriv (by simp)
    have hr := hgd.rpow_const (p := a / b - 1) (Or.inl hg0.ne')
    have hd : HasDerivAt (fdisp1 α a b) (α * a * (Real.exp (a * 0) * a) + (1 - α) ^ (1 - a / b) *
        ((-(α * b) * (Real.exp (b * 0) * b)) * (a / b) * (1 - α * Real.exp (b * 0)) ^ (a / b - 1) +
          (-(α * b) * Real.exp (b * 0)) * (a / b) *
            (-(α * (Real.exp (b * 0) * b)) * (a / b - 1) *
              (1 - α * Real.exp (b * 0)) ^ (a / b - 1 - 1)))) 0 := by
      have := ((he.const_mul (α * a)).add
        (((((hb'.const_mul (-(α * b))).mul_const (a / b)).mul hr)).const_mul
          ((1 - α) ^ (1 - a / b))))
      refine this.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
      · simp only [Function.comp_apply]; ring
      · exact Eventually.of_forall fun π => by
          simp only [fdisp1, Function.comp_apply, Pi.add_apply, Pi.mul_apply]
    rw [hd.deriv]
    simp only [mul_zero, Real.exp_zero, mul_one, one_mul]
    have e : α * a * a + (1 - α) ^ (1 - a / b) * (-(α * b) * b * (a / b) * (1 - α) ^ (a / b - 1) +
        -(α * b) * (a / b) * (-(α * b) * (a / b - 1) * (1 - α) ^ (a / b - 1 - 1))) =
        α * a * a - α * b * b * (a / b) * ((1 - α) ^ (1 - a / b) * (1 - α) ^ (a / b - 1)) +
          α * b * (a / b) * (α * b) * (a / b - 1) *
            ((1 - α) ^ (1 - a / b) * (1 - α) ^ (a / b - 1 - 1)) := by ring
    rw [e, hk, hk2]
    field_simp
    ring

/-! ## The cost coefficients under the equivalence map -/

/-- Woodford (2003), App. E.2: the second-order coefficient of the Calvo dispersion law,
`c_C = αθ(1+ω)(1+ωθ)/(2(1−α))`. -/
noncomputable def cC (α θ ω : ℝ) : ℝ := α * θ * (1 + ω) * (1 + ω * θ) / (2 * (1 - α))

/-- `c_C` is half of `fdisp″(0)` at `a = θ(1+ω)`, `b = θ − 1`. -/
theorem cC_eq {α θ ω : ℝ} (hα1 : α < 1) (hθ : 1 < θ) :
    2 * cC α θ ω = deriv (deriv (fdisp α (θ * (1 + ω)) (θ - 1))) 0 := by
  rw [(fdisp_second_order hα1 (by linarith : θ - 1 ≠ 0)).2.2]
  have : 1 - α ≠ 0 := by linarith
  unfold cC; field_simp; ring

/-- Woodford (2003), Ch. 3, fn. 44 and Ch. 6, §2 (**the cost coefficients coincide under the
map**): if `ψ = θmα(1+ωθ)/((1−α)(1−αβ))`, the discounted Calvo cost per unit of `π²`,
`m/(1+ω)·c_C/(1−αβ)`, equals the Rotemberg cost per unit of `π²`, `ψ/2`, for every `m`. -/
theorem cost_coefficients_eq {α β θ ω m ψ : ℝ} (hα1 : α < 1) (hαβ : α * β < 1) (hω : 0 ≤ ω)
    (hψ : ψ = θ * m * α * (1 + ω * θ) / ((1 - α) * (1 - α * β))) :
    m / (1 + ω) * (cC α θ ω / (1 - α * β)) = ψ / 2 := by
  have h1 : 1 - α ≠ 0 := by linarith
  have h2 : 1 - α * β ≠ 0 := by linarith
  have h3 : 1 + ω ≠ 0 := by linarith
  rw [hψ]; unfold cC; field_simp

/-! ## Discounted costs along every inflation path -/

/-- Woodford (2003), App. E.2: second-order dispersion from `Δ_{−1} = 1`,
`D_t = Σ_{s ≤ t} α^{t−s} c π_s²`. -/
noncomputable def Dsec (α c : ℝ) (π : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ s ∈ range (t + 1), α ^ (t - s) * (c * π s ^ 2)

/-- Woodford (2003), App. E.2: `D_0 = cπ_0²` and `D_{t+1} = αD_t + cπ_{t+1}²`. -/
theorem Dsec_rec (α c : ℝ) (π : ℕ → ℝ) (t : ℕ) :
    Dsec α c π 0 = c * π 0 ^ 2 ∧ Dsec α c π (t + 1) = α * Dsec α c π t + c * π (t + 1) ^ 2 := by
  refine ⟨by simp [Dsec], ?_⟩
  unfold Dsec
  rw [sum_range_succ, Nat.sub_self, pow_zero, one_mul, mul_sum]
  congr 1
  refine sum_congr rfl fun s hs => ?_
  have : s ≤ t := Nat.lt_succ_iff.1 (mem_range.1 hs)
  rw [show t + 1 - s = (t - s) + 1 by omega]; ring

/-- Woodford (2003), Ch. 6, §2 (**discounted dispersion**): for a bounded path and
`0 ≤ α < 1`, `0 < β < 1`, `Σ βᵗ D_t = Σ βᵗ cπ_t² / (1 − αβ)`. -/
theorem tsum_Dsec {α β c B : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (π : ℕ → ℝ) (hB : ∀ t, |π t| ≤ B) :
    ∑' t, β ^ t * Dsec α c π t = (∑' t, β ^ t * (c * π t ^ 2)) / (1 - α * β) := by
  have hab0 : 0 ≤ α * β := mul_nonneg hα0 hβ0.le
  have hab1 : α * β < 1 := by nlinarith
  have hf : Summable fun k : ℕ => ‖(α * β) ^ k‖ := by
    simpa [abs_of_nonneg (pow_nonneg hab0 _)] using summable_geometric_of_lt_one hab0 hab1
  have hg : Summable fun s : ℕ => ‖β ^ s * (c * π s ^ 2)‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun s => ?_)
      ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right (|c| * B ^ 2))
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (pow_pos hβ0 _), abs_pow, sq_abs]
    have : π s ^ 2 ≤ B ^ 2 := by
      have := hB s; have h0 : 0 ≤ |π s| := abs_nonneg _
      calc π s ^ 2 = |π s| ^ 2 := (sq_abs _).symm
        _ ≤ B ^ 2 := pow_le_pow_left₀ h0 this 2
    have := mul_le_mul_of_nonneg_left this (abs_nonneg c)
    have := mul_le_mul_of_nonneg_left this (pow_nonneg hβ0.le s)
    linarith
  have h := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hg
  rw [tsum_geometric_of_lt_one hab0 hab1] at h
  have h2 : ∀ t, β ^ t * Dsec α c π t = ∑ k ∈ range (t + 1),
      (α * β) ^ k * (β ^ (t - k) * (c * π (t - k) ^ 2)) := fun t => by
    unfold Dsec
    rw [mul_sum, ← sum_range_reflect]
    refine sum_congr rfl fun j hj => ?_
    have hjt : j ≤ t := Nat.lt_succ_iff.1 (mem_range.1 hj)
    have e1 : t + 1 - 1 - j = t - j := by omega
    have e2 : t - (t - j) = j := by omega
    rw [e1, e2]
    have e : β ^ t = β ^ j * β ^ (t - j) := by rw [← pow_add, Nat.add_sub_cancel' hjt]
    rw [e, mul_pow]; ring
  rw [tsum_congr h2, ← h, div_eq_inv_mul]

/-- Woodford (2003), Ch. 3, fn. 44 and Ch. 6, §2 (**the discounted second-order costs of inflation
coincide**): under the equivalence map `ψ = θmα(1+ωθ)/((1−α)(1−αβ))`, for every bounded inflation
path and every distortion `m`, the discounted Calvo dispersion cost `Σ βᵗ m/(1+ω)·D_t` (dispersion
from `Δ_{−1} = 1`, second-order law `D_t = αD_{t−1} + c_Cπ_t²`) equals the discounted Rotemberg
resource cost `Σ βᵗ (ψ/2)π_t²`. -/
theorem discounted_cost_equiv {α β θ ω m ψ B : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hω : 0 ≤ ω)
    (hψ : ψ = θ * m * α * (1 + ω * θ) / ((1 - α) * (1 - α * β))) (π : ℕ → ℝ)
    (hB : ∀ t, |π t| ≤ B) :
    ∑' t, β ^ t * (m / (1 + ω) * Dsec α (cC α θ ω) π t) = ∑' t, β ^ t * (ψ / 2 * π t ^ 2) := by
  have hab : α * β < 1 := by nlinarith
  have e1 : (fun t => β ^ t * (m / (1 + ω) * Dsec α (cC α θ ω) π t)) =
      fun t => m / (1 + ω) * (β ^ t * Dsec α (cC α θ ω) π t) := by funext t; ring
  have e2 : (fun t => β ^ t * (ψ / 2 * π t ^ 2)) =
      fun t => (ψ / 2 / cC α θ ω) * (β ^ t * (cC α θ ω * π t ^ 2)) := by
    funext t
    by_cases hc : cC α θ ω = 0
    · have : ψ / 2 = 0 := by
        rw [← cost_coefficients_eq hα1 hab hω hψ, hc]; simp
      rw [this, hc]; simp
    · field_simp
  rw [e1, e2, tsum_mul_left, tsum_mul_left, tsum_Dsec hα0 hα1 hβ0 hβ1 π hB,
    ← cost_coefficients_eq hα1 hab hω hψ]
  by_cases hc : cC α θ ω = 0
  · simp [hc]
  · have : 1 - α * β ≠ 0 := by linarith
    field_simp
    congr 1
    exact tsum_congr fun t => by ring

end Woodford.StabilizationWelfare.NonlinearRotembergWelfare
