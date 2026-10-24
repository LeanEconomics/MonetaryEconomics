/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.InflationInertiaRules
import OptimalPolicyRules.IRuleBasic

/-!
# The roots of the first-order system of the inflation-inertia model

Woodford (2003), *Interest and Prices*, Chapter 8, §3.2, p. 593 (the characteristic polynomial
`D(μ)` of the optimal-plan system, `InflationInertiaRules.charD`), with Appendix G.4, (G.13)
(the reciprocal pairing `μ ↔ (βμ)⁻¹`).

`InflationInertiaRules` showed that the roots of `D` pair as `μ ↔ (βμ)⁻¹` and that `D(1)`,
`D(β⁻¹)` are not zero. This module completes the root count for **every admissible
calibration** (`0 < β < 1`, `κ, σ, λₓ, λᵢ > 0`, `0 < γ ≤ 1`):

* `charD_ne_zero_of_annulus`: `D` has **no root in the closed annulus** `1 ≤ |μ| ≤ β⁻¹`. In the
  variables `a = μ⁻¹`, `a' = βμ` (`aa' = β`) one has `D(μ) = (κσ)²λᵢ⁻¹ μ³ S(a, a')` with
  `S = uu'(1 + λ'w) + κ'(1 + hwu)(1 + hwu')`, `u = 1 − γa`, `u' = 1 − γa'`,
  `w = (1 − a)(1 − a')`, `λ' = λₓ/κ²`, `κ' = λᵢ/β`, `h = (κσ)⁻¹` (`charD_eq_S`). On the annulus
  (by the symmetries `a ↔ a'` and conjugation, `|a| ≥ √β` and `Im a ≥ 0`) `w` lies in the closed
  fourth quadrant, and with `Z = u⁻¹ + hw`, `Z' = u'⁻¹ + hw` one has `Re Z, Re Z' > 0`,
  `Im Z' ≤ 0`; `S = uu'(1 + λ'w + κ'ZZ')`, and `S = 0` would need `ZZ' = −(1 + λ'w)/κ'`, a
  number with negative real part and nonnegative imaginary part, which a product `ZZ'` with
  these signs never is (`S_ne_zero_core`, `quad_contra`). (On p. 593 the book takes the
  existence of a bounded optimal plan as given; this root count is what supplies it, see
  `InertiaAssumption81`.)
* `charD_split`: `D(μ) = −β²γ ∏ⱼ (μ − mⱼ)(μ − mⱼ')` with `mⱼmⱼ' = β⁻¹`, through the cubic
  `G(ν)` with `D(μ) = μ³G(μ + (βμ)⁻¹)` (`charD_expand`, the palindromic coefficients); in each
  pair exactly one root lies in the open unit disc (none lies in the annulus).
* `charD_inside_three`: hence **exactly three roots (with multiplicity) in the open unit disc and
  none on the unit circle** — the count the Blanchard–Kahn conditions for the first-order system
  need (`InertiaAssumption81`).
-/

namespace Woodford.OptimalPolicyRules.InertiaFOCRoots

open Polynomial ComplexConjugate
open CubicRoots CubicRoots.Assumptions
open InflationInertiaRules (charD recipC)
open IRuleBasic (Annulus ind ind_pair_eq_one_iff exists_sum_prod)

/-! ### The symmetric form `S(a, a')` -/

/-- Woodford (2003), p. 593 (the structure of `D`): with `a = μ⁻¹`, `a' = βμ`,
`S(a, a') = uu'(1 + λ'w) + κ'(1 + hwu)(1 + hwu')`, `u = 1 − γa`, `u' = 1 − γa'`,
`w = (1 − a)(1 − a')`, `λ' = λₓ/κ²`, `κ' = λᵢ/β`, `h = (κσ)⁻¹`. -/
noncomputable def Sab (β γ κ σ lx li : ℝ) (a a' : ℂ) : ℂ :=
  (1 - γ * a) * (1 - γ * a') * (1 + ((lx / κ ^ 2 : ℝ) : ℂ) * ((1 - a) * (1 - a'))) +
    ((li / β : ℝ) : ℂ) * (1 + ((κ * σ)⁻¹ : ℝ) * ((1 - a) * (1 - a')) * (1 - γ * a)) *
      (1 + ((κ * σ)⁻¹ : ℝ) * ((1 - a) * (1 - a')) * (1 - γ * a'))

/-- Woodford (2003), p. 593: `D(μ) = (κσ)²λᵢ⁻¹ μ³ S(μ⁻¹, βμ)` for `μ ≠ 0`. -/
theorem charD_eq_S {β γ κ σ lx li : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0) (hσ : σ ≠ 0) (hli : li ≠ 0)
    {μ : ℂ} (hμ : μ ≠ 0) :
    charD β γ κ σ lx li μ =
      (((κ * σ) ^ 2 / li : ℝ) : ℂ) * μ ^ 3 * Sab β γ κ σ lx li μ⁻¹ (β * μ) := by
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
  have hσc : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ
  have hlic : (li : ℂ) ≠ 0 := by exact_mod_cast hli
  unfold charD recipC Sab coefA0 coefA1 coefA2 coefA3
  push_cast
  field_simp
  ring

/-- Woodford (2003), (G.13) (tool): `S` is symmetric in `a ↔ a'`. -/
theorem Sab_symm (β γ κ σ lx li : ℝ) (a a' : ℂ) :
    Sab β γ κ σ lx li a a' = Sab β γ κ σ lx li a' a := by
  unfold Sab
  ring

/-- Woodford (2003), (G.13) (tool): `S` has real coefficients, `S(ā, ā') = conj S(a, a')`. -/
theorem Sab_conj (β γ κ σ lx li : ℝ) (a a' : ℂ) :
    Sab β γ κ σ lx li (conj a) (conj a') = conj (Sab β γ κ σ lx li a a') := by
  unfold Sab
  simp only [map_add, map_mul, map_sub, map_one, Complex.conj_ofReal]

/-- Woodford (2003), p. 593 (tool): with `Re Z, Re Z' > 0`, `Im Z' ≤ 0`, `w` in the closed fourth
quadrant and `λ' ≥ 0 < κ'`, the number `1 + λ'w + κ'ZZ'` is not zero (in real coordinates). -/
theorem quad_contra {lp kp wr wi p1 q1 p2 q2 : ℝ} (hlp : 0 ≤ lp) (hkp : 0 < kp) (hwr : 0 ≤ wr)
    (hwi : wi ≤ 0) (hp1 : 0 < p1) (hp2 : 0 < p2) (hq2 : q2 ≤ 0)
    (hre : 1 + lp * wr + kp * (p1 * p2 - q1 * q2) = 0)
    (him : lp * wi + kp * (p1 * q2 + q1 * p2) = 0) : False := by
  have h1 : 0 < kp * (q1 * q2) := by nlinarith [mul_nonneg hlp hwr, mul_pos hp1 hp2]
  have h2 : 0 < q1 * q2 := pos_of_mul_pos_right h1 hkp.le
  have hq2' : q2 < 0 :=
    lt_of_le_of_ne hq2 (fun e => by rw [e, mul_zero] at h2; exact lt_irrefl _ h2)
  have hq1 : q1 < 0 := by
    by_contra hc
    push Not at hc
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hc hq2]
  have h3 : p1 * q2 + q1 * p2 < 0 := by
    nlinarith [mul_neg_of_pos_of_neg hp1 hq2', mul_neg_of_neg_of_pos hq1 hp2]
  have h4 : lp * wi ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlp hwi
  nlinarith [mul_neg_of_pos_of_neg hkp h3]

/-- Woodford (2003), p. 593 (**the key step**): for `aa' = β`, `Im a ≥ 0` and
`β ≤ |a|² ≤ 1`, `S(a, a') ≠ 0`. -/
theorem S_ne_zero_core {β γ κ σ lx li : ℝ} (h : Standing β γ κ σ) (hlx : 0 ≤ lx)
    (hli : 0 < li) {a a' : ℂ} (haa : a * a' = β) (him : 0 ≤ a.im)
    (hn1 : Complex.normSq a ≤ 1) (hnb : β ≤ Complex.normSq a) :
    Sab β γ κ σ lx li a a' ≠ 0 := by
  have hβ0 := h.beta_pos
  have hβ1 := h.beta_lt_one
  have hγ0 := h.gamma_pos
  have hγ1 := h.gamma_le_one
  have hks := h.kappa_sigma_pos
  set x := a.re with hx
  set y := a.im with hy
  set ρ := Complex.normSq a with hρ
  have hρx : ρ = x * x + y * y := Complex.normSq_apply a
  have hρ0 : 0 < ρ := lt_of_lt_of_le hβ0 hnb
  have ha0 : a ≠ 0 := fun e => by rw [hρ, e, map_zero] at hρ0; exact lt_irrefl _ hρ0
  -- `a' = t ā` with `t = β/|a|²`
  set t := β / ρ with ht
  have ht0 : 0 < t := div_pos hβ0 hρ0
  have ht1 : t ≤ 1 := (div_le_one hρ0).mpr hnb
  have ha' : a' = β / a := by field_simp; rw [mul_comm]; exact haa
  have hre' : a'.re = t * x := by
    rw [ha', Complex.div_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [ht]
    ring
  have him' : a'.im = -(t * y) := by
    rw [ha', Complex.div_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [ht]
    ring
  have hx1 : x ≤ 1 := by nlinarith
  have hxm1 : -1 ≤ x := by nlinarith
  have htx : t * x < 1 := by
    have h1 : t * t * ρ = t * β := by rw [ht]; field_simp
    have h2 : t * β ≤ β := by nlinarith
    have h3 : (t * x) * (t * x) ≤ t * t * ρ := by nlinarith
    nlinarith
  -- the components of `w`, `u`, `u'`
  set lp : ℝ := lx / κ ^ 2 with hlp
  set kp : ℝ := li / β with hkp
  set hr : ℝ := (κ * σ)⁻¹ with hhr
  have hlp0 : 0 ≤ lp := div_nonneg hlx (sq_nonneg κ)
  have hkp0 : 0 < kp := div_pos hli hβ0
  have hhr0 : 0 < hr := inv_pos.mpr hks
  set W : ℂ := (1 - a) * (1 - a') with hW
  set U : ℂ := 1 - γ * a with hU
  set U' : ℂ := 1 - γ * a' with hU'
  have hWre : W.re = (1 - x) * (1 - t * x) + t * y * y := by
    rw [hW, Complex.mul_re, Complex.sub_re, Complex.sub_re, Complex.sub_im, Complex.sub_im,
      Complex.one_re, Complex.one_im, hre', him']
    ring
  have hWim : W.im = y * (t - 1) := by
    rw [hW, Complex.mul_im, Complex.sub_re, Complex.sub_re, Complex.sub_im, Complex.sub_im,
      Complex.one_re, Complex.one_im, hre', him']
    ring
  have hUre : U.re = 1 - γ * x := by
    rw [hU, Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul]
  have hUim : U.im = -(γ * y) := by
    rw [hU, Complex.sub_im, Complex.one_im, Complex.im_ofReal_mul]
    ring
  have hU're : U'.re = 1 - γ * (t * x) := by
    rw [hU', Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul, hre']
  have hU'im : U'.im = γ * (t * y) := by
    rw [hU', Complex.sub_im, Complex.one_im, Complex.im_ofReal_mul, him']
    ring
  have hWre0 : 0 ≤ W.re := by
    rw [hWre]
    have : 0 ≤ 1 - t * x := by linarith
    have : 0 ≤ t * y * y := by positivity
    nlinarith
  have hWim0 : W.im ≤ 0 := by
    rw [hWim]
    exact mul_nonpos_of_nonneg_of_nonpos him (by linarith)
  have hU're0 : 0 < U'.re := by
    rw [hU're]
    rcases le_or_gt (t * x) 0 with h0 | h0
    · nlinarith
    · nlinarith
  have hU'0 : U' ≠ 0 := fun e => by rw [e, Complex.zero_re] at hU're0; exact lt_irrefl _ hU're0
  have hS : Sab β γ κ σ lx li a a' =
      U * U' * (1 + (lp : ℂ) * W) + (kp : ℂ) * (1 + (hr : ℂ) * W * U) * (1 + (hr : ℂ) * W * U') :=
    rfl
  have hUnn : 0 ≤ U.re := by
    rw [hUre]
    have := mul_le_of_le_one_right hγ0.le hx1
    linarith
  rcases eq_or_lt_of_le hUnn with hU0 | hUre0
  · -- `a = 1`: then `w = 0` and `S = (1 − γ)(1 − γβ) + κ' > 0`
    have hγx : γ * x = 1 := by rw [hUre] at hU0; linarith
    have hx' : x = 1 := by
      by_contra hne
      have := mul_lt_mul_of_pos_left (lt_of_le_of_ne hx1 hne) hγ0
      linarith
    have hγ' : γ = 1 := by rw [hx', mul_one] at hγx; exact hγx
    have hy0 : y = 0 := by
      have hyy : y * y ≤ 0 := by rw [hρx, hx'] at hn1; linarith
      exact mul_self_eq_zero.mp (le_antisymm hyy (mul_self_nonneg y))
    have ha1 : a = 1 := Complex.ext (by rw [← hx, hx']; rfl) (by rw [← hy, hy0]; rfl)
    have hW0 : W = 0 := by rw [hW, ha1, sub_self, zero_mul]
    rw [hS, hW0]
    intro h0
    have hre := congrArg Complex.re h0
    have hUU : (U * U').re = 0 := by
      rw [Complex.mul_re, hUre, hUim, hU're, hU'im, hy0, hγx]
      ring
    simp only [mul_zero, zero_mul, add_zero, mul_one, Complex.add_re, Complex.zero_re,
      Complex.ofReal_re, hUU] at hre
    linarith
  · have hU0 : U ≠ 0 := fun e => by rw [e, Complex.zero_re] at hUre0; exact lt_irrefl _ hUre0
    set Z : ℂ := U⁻¹ + (hr : ℂ) * W with hZ
    set Z' : ℂ := U'⁻¹ + (hr : ℂ) * W with hZ'
    have hS' : Sab β γ κ σ lx li a a' = U * U' * (1 + (lp : ℂ) * W + (kp : ℂ) * (Z * Z')) := by
      rw [hS, hZ, hZ']
      field_simp
    have hnU : 0 < Complex.normSq U := Complex.normSq_pos.mpr hU0
    have hnU' : 0 < Complex.normSq U' := Complex.normSq_pos.mpr hU'0
    have hZre : 0 < Z.re := by
      rw [hZ, Complex.add_re, Complex.inv_re, Complex.re_ofReal_mul]
      have := div_pos hUre0 hnU
      have := mul_nonneg hhr0.le hWre0
      linarith
    have hZ're : 0 < Z'.re := by
      rw [hZ', Complex.add_re, Complex.inv_re, Complex.re_ofReal_mul]
      have := div_pos hU're0 hnU'
      have := mul_nonneg hhr0.le hWre0
      linarith
    have hZ'im : Z'.im ≤ 0 := by
      rw [hZ', Complex.add_im, Complex.inv_im, Complex.im_ofReal_mul, hU'im, neg_div]
      have : 0 ≤ γ * (t * y) / Complex.normSq U' := by positivity
      have := mul_nonpos_of_nonneg_of_nonpos hhr0.le hWim0
      linarith
    rw [hS']
    intro h0
    have h1 : 1 + (lp : ℂ) * W + (kp : ℂ) * (Z * Z') = 0 :=
      (mul_eq_zero.mp h0).resolve_left (mul_ne_zero hU0 hU'0)
    have hre := congrArg Complex.re h1
    have him2 := congrArg Complex.im h1
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.zero_re,
      Complex.zero_im] at hre him2
    exact quad_contra (q1 := Z.im) hlp0 hkp0 hWre0 hWim0 hZre hZ're hZ'im
      (by linear_combination hre) (by linear_combination him2)

/-- Woodford (2003), p. 593: `S(a, a') ≠ 0` whenever `aa' = β` and `|a|, |a'| ≤ 1`. -/
theorem S_ne_zero {β γ κ σ lx li : ℝ} (h : Standing β γ κ σ) (hlx : 0 ≤ lx) (hli : 0 < li)
    {a a' : ℂ} (haa : a * a' = β) (h1 : ‖a‖ ≤ 1) (h1' : ‖a'‖ ≤ 1) :
    Sab β γ κ σ lx li a a' ≠ 0 := by
  have hβ0 := h.beta_pos
  have hprod : Complex.normSq a * Complex.normSq a' = β * β := by
    rw [← Complex.normSq_mul, haa, Complex.normSq_ofReal]
  have hn1 : Complex.normSq a ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  have hn1' : Complex.normSq a' ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg a']
  have key : ∀ b b' : ℂ, b * b' = β → Complex.normSq b ≤ 1 → β ≤ Complex.normSq b →
      Sab β γ κ σ lx li b b' ≠ 0 := by
    intro b b' hbb hb1 hbb2
    rcases le_or_gt 0 b.im with hi | hi
    · exact S_ne_zero_core h hlx hli hbb hi hb1 hbb2
    · intro h0
      have hc := S_ne_zero_core h hlx hli (a := conj b) (a' := conj b')
        (by rw [← map_mul, hbb, Complex.conj_ofReal]) (by rw [Complex.conj_im]; linarith)
        (by rwa [Complex.normSq_conj]) (by rwa [Complex.normSq_conj])
      exact hc (by rw [Sab_conj, h0, map_zero])
  rcases le_or_gt β (Complex.normSq a) with hb | hb
  · exact key a a' haa hn1 hb
  · rw [Sab_symm]
    refine key a' a (by rw [mul_comm]; exact haa) hn1' ?_
    by_contra hc
    push Not at hc
    have : Complex.normSq a * Complex.normSq a' < β * β :=
      mul_lt_mul'' hb hc (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
    linarith

/-- **Woodford (2003), p. 593 with App. G.4: the characteristic polynomial `D` of the optimal-plan
system of the inflation-inertia model has no root in the closed annulus `1 ≤ |μ| ≤ β⁻¹`** (in
particular none on the unit circle), for every admissible calibration. -/
theorem charD_ne_zero_of_annulus {β γ κ σ lx li : ℝ} (h : Standing β γ κ σ) (hlx : 0 ≤ lx)
    (hli : 0 < li) {μ : ℂ} (ha : Annulus β μ) : charD β γ κ σ lx li μ ≠ 0 := by
  have hβ0 := h.beta_pos
  obtain ⟨h1, h2⟩ := ha
  have hμ : μ ≠ 0 := by
    intro e
    rw [e, norm_zero] at h1
    linarith
  have hnμ : 0 < ‖μ‖ := norm_pos_iff.mpr hμ
  rw [charD_eq_S hβ0.ne' h.kappa_pos.ne' h.sigma_pos.ne' hli.ne' hμ]
  refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero 3 hμ)) ?_
  · have : (0 : ℝ) < (κ * σ) ^ 2 / li := div_pos (pow_pos h.kappa_sigma_pos 2) hli
    exact_mod_cast this.ne'
  · refine S_ne_zero h hlx hli ?_ ?_ ?_
    · field_simp
    · rw [norm_inv]
      exact inv_le_one_of_one_le₀ h1
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ0.le]
      rw [le_div_iff₀ hβ0] at h2
      linarith

/-! ### The palindromic factorisation and the root count -/

/-- Woodford (2003), p. 593: the coefficient `d₀ = −γ/β` of `D(μ) = ∑ dⱼμʲ` (`d₆ = β³d₀`). -/
noncomputable def dc0 (β γ : ℝ) : ℝ := -γ / β

/-- Woodford (2003), p. 593: the coefficient `d₁` of `D` (`d₅ = β²d₁`). -/
noncomputable def dc1 (β γ κ σ lx li : ℝ) : ℝ :=
  2 * γ + 2 * γ / β + 1 / β + γ ^ 2 + γ * κ * σ / β + γ * lx * σ ^ 2 / li

/-- Woodford (2003), p. 593: the coefficient `d₂` of `D` (`d₄ = βd₂`). -/
noncomputable def dc2 (β γ κ σ lx li : ℝ) : ℝ :=
  -5 * γ - β * γ - γ / β - 2 * β * γ ^ 2 - 2 / β - 2 * γ ^ 2 - lx * σ ^ 2 / li - γ * κ * σ -
    2 * κ * σ / β - γ * κ ^ 2 * σ ^ 2 / li - γ * κ * σ / β - γ * lx * σ ^ 2 / li -
    β * γ * lx * σ ^ 2 / li - β * γ ^ 2 * lx * σ ^ 2 / li - 2

/-- Woodford (2003), p. 593: the middle coefficient `d₃` of `D`. -/
noncomputable def dc3 (β γ κ σ lx li : ℝ) : ℝ :=
  β + 4 * γ + 4 * β * γ + 2 * κ * σ + 4 * β * γ ^ 2 + 1 / β + γ ^ 2 + β ^ 2 * γ ^ 2 +
    lx * σ ^ 2 / li + 2 * γ * κ * σ + κ ^ 2 * σ ^ 2 / β + κ ^ 2 * σ ^ 2 / li + 2 * κ * σ / β +
    β * lx * σ ^ 2 / li + 2 * β * γ * lx * σ ^ 2 / li + β * γ ^ 2 * lx * σ ^ 2 / li +
    β * γ ^ 2 * κ ^ 2 * σ ^ 2 / li + β ^ 2 * γ ^ 2 * lx * σ ^ 2 / li + 4

/-- Woodford (2003), p. 593 with (G.13): `D(μ) = β³d₀μ⁶ + β²d₁μ⁵ + βd₂μ⁴ + d₃μ³ + d₂μ² + d₁μ + d₀`
(the `β`-palindromic structure behind `charD_reciprocal`). -/
theorem charD_expand {β γ κ σ lx li : ℝ} (hβ : β ≠ 0) (hli : li ≠ 0) (μ : ℂ) :
    charD β γ κ σ lx li μ =
      ((β ^ 3 * dc0 β γ : ℝ) : ℂ) * μ ^ 6 + ((β ^ 2 * dc1 β γ κ σ lx li : ℝ) : ℂ) * μ ^ 5 +
        ((β * dc2 β γ κ σ lx li : ℝ) : ℂ) * μ ^ 4 + ((dc3 β γ κ σ lx li : ℝ) : ℂ) * μ ^ 3 +
        ((dc2 β γ κ σ lx li : ℝ) : ℂ) * μ ^ 2 + ((dc1 β γ κ σ lx li : ℝ) : ℂ) * μ +
        ((dc0 β γ : ℝ) : ℂ) := by
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have hlic : (li : ℂ) ≠ 0 := by exact_mod_cast hli
  unfold charD recipC coefA0 coefA1 coefA2 coefA3 dc0 dc1 dc2 dc3
  push_cast
  field_simp
  ring

/-- Woodford (2003), (G.13) for `D` (tool): the cubic `G(ν) = g₃ν³ + g₂ν² + g₁ν + g₀` with
`D(μ) = μ³G(μ + (βμ)⁻¹)`: `g₃ = β³d₀`, `g₂ = β²d₁`, `g₁ = βd₂ − 3β²d₀`, `g₀ = d₃ − 2βd₁`. -/
noncomputable def Gpoly (β γ κ σ lx li : ℝ) : ℂ[X] :=
  C ((β ^ 3 * dc0 β γ : ℝ) : ℂ) * X ^ 3 + C ((β ^ 2 * dc1 β γ κ σ lx li : ℝ) : ℂ) * X ^ 2 +
    C ((β * dc2 β γ κ σ lx li - 3 * β ^ 2 * dc0 β γ : ℝ) : ℂ) * X +
    C ((dc3 β γ κ σ lx li - 2 * β * dc1 β γ κ σ lx li : ℝ) : ℂ)

/-- Woodford (2003), (G.13) for `D`: `D(μ) = −β²γ ∏ⱼ (μ − mⱼ)(μ − mⱼ')` with `mⱼmⱼ' = β⁻¹`: the
six roots come in three reciprocal pairs (from the roots `νⱼ = mⱼ + mⱼ'` of `G`). -/
theorem charD_split {β γ κ σ lx li : ℝ} (hβ : β ≠ 0) (hγ : γ ≠ 0) (hli : li ≠ 0) :
    ∃ m1 m1' m2 m2' m3 m3' : ℂ, m1 * m1' = 1 / β ∧ m2 * m2' = 1 / β ∧ m3 * m3' = 1 / β ∧
      ∀ μ, charD β γ κ σ lx li μ = ((-(β ^ 2 * γ) : ℝ) : ℂ) *
        ((μ - m1) * (μ - m1') * ((μ - m2) * (μ - m2')) * ((μ - m3) * (μ - m3'))) := by
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  set g3 : ℂ := ((β ^ 3 * dc0 β γ : ℝ) : ℂ) with hg3
  set g2 : ℂ := ((β ^ 2 * dc1 β γ κ σ lx li : ℝ) : ℂ) with hg2
  set g1 : ℂ := ((β * dc2 β γ κ σ lx li - 3 * β ^ 2 * dc0 β γ : ℝ) : ℂ) with hg1
  set g0 : ℂ := ((dc3 β γ κ σ lx li - 2 * β * dc1 β γ κ σ lx li : ℝ) : ℂ) with hg0
  have hg3e : g3 = ((-(β ^ 2 * γ) : ℝ) : ℂ) := by
    rw [hg3, dc0]
    push_cast
    field_simp
  have hg3ne : g3 ≠ 0 := by
    rw [hg3e]
    have : -(β ^ 2 * γ) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hβ) hγ)
    exact_mod_cast this
  have hdeg : 0 < (Gpoly β γ κ σ lx li).degree := by
    rw [Gpoly, degree_cubic hg3ne]
    norm_num
  obtain ⟨ν1, hν1⟩ := Complex.exists_root hdeg
  have hG : g3 * ν1 ^ 3 + g2 * ν1 ^ 2 + g1 * ν1 + g0 = 0 := by
    have := hν1
    simp only [Gpoly, IsRoot, eval_add, eval_mul, eval_C, eval_pow, eval_X] at this
    exact this
  obtain ⟨ν2, ν3, hs, hp⟩ := exists_sum_prod (-(g2 + g3 * ν1) / g3)
    ((g1 + g2 * ν1 + g3 * ν1 ^ 2) / g3)
  have hE1 : g3 * (ν2 + ν3) + g2 + g3 * ν1 = 0 := by
    rw [hs]
    field_simp
    ring
  have hE2 : g3 * (ν2 * ν3) - (g1 + g2 * ν1 + g3 * ν1 ^ 2) = 0 := by
    rw [hp]
    field_simp
    ring
  obtain ⟨m1, m1', h1s, h1p⟩ := exists_sum_prod ν1 (1 / β)
  obtain ⟨m2, m2', h2s, h2p⟩ := exists_sum_prod ν2 (1 / β)
  obtain ⟨m3, m3', h3s, h3p⟩ := exists_sum_prod ν3 (1 / β)
  refine ⟨m1, m1', m2, m2', m3, m3', h1p, h2p, h3p, fun μ => ?_⟩
  have hq : ∀ {m m' ν : ℂ}, m + m' = ν → m * m' = 1 / β →
      (μ - m) * (μ - m') = (μ ^ 2 + 1 / β) - ν * μ := by
    intro m m' ν hsum hprod
    rw [← hsum]
    linear_combination hprod
  rw [hq h1s h1p, hq h2s h2p, hq h3s h3p, ← hg3e, charD_expand hβ hli]
  set q : ℂ := μ ^ 2 + 1 / β with hqdef
  have key : g3 * q ^ 3 + g2 * q ^ 2 * μ + g1 * q * μ ^ 2 + g0 * μ ^ 3 =
      ((β ^ 3 * dc0 β γ : ℝ) : ℂ) * μ ^ 6 + ((β ^ 2 * dc1 β γ κ σ lx li : ℝ) : ℂ) * μ ^ 5 +
        ((β * dc2 β γ κ σ lx li : ℝ) : ℂ) * μ ^ 4 + ((dc3 β γ κ σ lx li : ℝ) : ℂ) * μ ^ 3 +
        ((dc2 β γ κ σ lx li : ℝ) : ℂ) * μ ^ 2 + ((dc1 β γ κ σ lx li : ℝ) : ℂ) * μ +
        ((dc0 β γ : ℝ) : ℂ) := by
    rw [hqdef, hg3, hg2, hg1, hg0]
    push_cast
    field_simp
    ring
  rw [← key]
  linear_combination μ ^ 3 * hG + (q - ν1 * μ) * μ * q * hE1 - (q - ν1 * μ) * μ ^ 2 * hE2

/-- **Woodford (2003), p. 593 with App. G.4: exactly three roots inside.** For every admissible
calibration (`λₓ ≥ 0`, `λᵢ > 0`) the characteristic polynomial `D` of the optimal-plan system of
the inflation-inertia model is `−β²γ ∏_{m ∈ s} (μ − m)` for a multiset `s` of six roots, exactly
three of which (with multiplicity) lie in the open unit disc, and none on the unit circle. -/
theorem charD_inside_three {β γ κ σ lx li : ℝ} (h : Standing β γ κ σ) (hlx : 0 ≤ lx)
    (hli : 0 < li) :
    ∃ s : Multiset ℂ, Multiset.card s = 6 ∧
      (∀ μ, charD β γ κ σ lx li μ = ((-(β ^ 2 * γ) : ℝ) : ℂ) * (s.map (fun m => μ - m)).prod) ∧
      Multiset.card (s.filter (fun m => ‖m‖ < 1)) = 3 ∧ ∀ m ∈ s, ‖m‖ ≠ 1 := by
  have hβ0 := h.beta_pos
  have hβ1 := h.beta_lt_one
  obtain ⟨m1, m1', m2, m2', m3, m3', h1, h2, h3, hD⟩ :=
    charD_split hβ0.ne' h.gamma_pos.ne' hli.ne' (κ := κ) (σ := σ) (lx := lx)
  have hroot : ∀ m, charD β γ κ σ lx li m = 0 → ¬ Annulus β m := fun m hm ha =>
    charD_ne_zero_of_annulus h hlx hli ha hm
  have r1 := hroot m1 (by rw [hD]; ring)
  have r1' := hroot m1' (by rw [hD]; ring)
  have r2 := hroot m2 (by rw [hD]; ring)
  have r2' := hroot m2' (by rw [hD]; ring)
  have r3 := hroot m3 (by rw [hD]; ring)
  have r3' := hroot m3' (by rw [hD]; ring)
  have e1 := (ind_pair_eq_one_iff hβ0 hβ1 h1).mpr ⟨r1, r1'⟩
  have e2 := (ind_pair_eq_one_iff hβ0 hβ1 h2).mpr ⟨r2, r2'⟩
  have e3 := (ind_pair_eq_one_iff hβ0 hβ1 h3).mpr ⟨r3, r3'⟩
  refine ⟨m1 ::ₘ m1' ::ₘ m2 ::ₘ m2' ::ₘ m3 ::ₘ m3' ::ₘ 0, by simp, fun μ => ?_, ?_, ?_⟩
  · rw [hD]
    simp only [Multiset.map_cons, Multiset.map_zero, Multiset.prod_cons, Multiset.prod_zero]
    ring
  · simp only [IRuleBasic.card_filter_cons, Multiset.filter_zero, Multiset.card_zero]
    omega
  · have hb : (1 : ℝ) ≤ 1 / β := by rw [le_div_iff₀ hβ0]; linarith
    intro m hm h1m
    have hn : Annulus β m := ⟨h1m.ge, h1m ▸ hb⟩
    simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact r1 hn
    · exact r1' hn
    · exact r2 hn
    · exact r2' hn
    · exact r3 hn
    · exact r3' hn

end Woodford.OptimalPolicyRules.InertiaFOCRoots
