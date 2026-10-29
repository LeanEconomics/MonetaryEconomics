/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergCentreLocal
import StabilizationWelfare.NonlinearRotembergTrendWelfare

/-!
# The transcritical coefficient of the boundary centre dynamics

Woodford (2003), *Interest and Prices*, Chapter 4, Proposition 4.3 (p. 254) and Appendix A.3, for
the exact Rotemberg model of `NonlinearRotembergCentreLocal` on the boundary
`κ(φ_π − 1) + (1 − β)φ_y = 0`. The drift `D(x)` of the centre coordinate has a vanishing linear
part on the resource manifold; its SECOND-order part along the centre direction is the
transcritical coefficient

`D ≈ q·L²`,  `q = f₂Θ²/(2Γ²)`,  `f₂ = φ_yψS/(Θθm)`,
`S = σ(θm)² + 3(1−β)θm − (1−β)²ψ` (`Sc`).

## Main results

* **`J_f`**: along the centre line `x(π) = (aπ, π, aπ + log(C/Y))`, `a = (1−β)ψ/Θ`, the drift has
  `D′(0) = 0` and `D″(0) = f₂` (an exact jet computation).
* **`peano2`**: a second-order jet with zero value and slope gives `|f(x) − (v₂/2)x²| ≤ ηx²` near
  `0` (Peano remainder, by the mean value theorem).
* **`transverse_bound`**: moving off the centre line by `v` changes `D` by at most
  `C(|π| + |v|)|v|` (the `v`-derivative of `D` vanishes at the steady state).
* **`second_order_D`**: for every `η > 0`, near the steady state on the resource manifold,
  `|D(x) − qL(x)²| ≤ ηL(x)² + C|V(x)|(|L(x)| + |V(x)|)`.
* **`q_pos_iff`**: `q > 0 ⟺ S > 0` and `q < 0 ⟺ S < 0` (for `φ_y > 0`).
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergCentreSecond

open Filter Topology
open NonlinearRotemberg NonlinearRotembergJets NonlinearRotembergCentreLocal
open NonlinearRotembergLinks (wedge)
open NonlinearRotembergBoundaryPair (Lf kc rem_logw)
open NonlinearRotembergTrendWelfare (J_g J_lw)

variable {p : Par}

/-! ## The transcritical coefficient -/

/-- Woodford (2003), Prop. 4.3: the transcritical numerator `S = σ(θm)² + 3(1−β)θm − (1−β)²ψ`. -/
noncomputable def Sc (p : Par) : ℝ :=
  p.σ * (p.θ * p.m) ^ 2 + 3 * (1 - p.β) * (p.θ * p.m) - (1 - p.β) ^ 2 * p.ψ

/-- Woodford (2003), Prop. 4.3: the second derivative of the drift along the centre line,
`f₂ = φ_yψS/(Θθm)`. -/
noncomputable def f2 (p : Par) : ℝ := p.φy * p.ψ * Sc p / (Th p * (p.θ * p.m))

/-- Woodford (2003), Prop. 4.3: the transcritical coefficient `q = f₂Θ²/(2Γ²)` of `D ≈ qL²`. -/
noncomputable def qc (p : Par) : ℝ := f2 p * Th p ^ 2 / (2 * Gam p ^ 2)

/-- Woodford (2003), App. A.3: The slope `a = (1−β)ψ/Θ` of the centre line (`ŷ = aπ`). -/
noncomputable def aa (p : Par) : ℝ := (1 - p.β) * p.ψ / Th p

/-- Woodford (2003), Prop. 4.3 (**the sign of the transcritical coefficient**): for `φ_y > 0`,
`q > 0 ⟺ S > 0` and `q < 0 ⟺ S < 0`. -/
theorem q_pos_iff (hp : p.Basic) (hφy : 0 < p.φy) : (0 < qc p ↔ 0 < Sc p) ∧
    (qc p < 0 ↔ Sc p < 0) := by
  have hT := Th_pos hp
  have hG := Gam_pos hp
  have hθm : 0 < p.θ * p.m := mul_pos (by linarith [hp.one_lt_θ]) hp.m_pos
  have hψ := hp.ψ_pos
  have hc : 0 < p.φy * p.ψ / (Th p * (p.θ * p.m)) * Th p ^ 2 / (2 * Gam p ^ 2) := by positivity
  have e : qc p = p.φy * p.ψ / (Th p * (p.θ * p.m)) * Th p ^ 2 / (2 * Gam p ^ 2) * Sc p := by
    unfold qc f2; ring
  rw [e]
  exact ⟨⟨fun h => pos_of_mul_pos_right h hc.le, fun h => mul_pos hc h⟩,
    ⟨fun h => by
      by_contra h'; push Not at h'; nlinarith,
      fun h => mul_neg_of_pos_of_neg hc h⟩⟩

/-! ## The centre line and its jet -/

/-- Woodford (2003), Prop. 4.3: the resource-manifold point with inflation `π` and transverse
coordinate `v = Θŷ − (1−β)ψπ`: `(aπ + v/Θ, π, aπ + v/Θ + log(C/Y))`. -/
noncomputable def zz (p : Par) (π v : ℝ) : Fin 3 → ℝ :=
  ![aa p * π + v / Th p, π, aa p * π + v / Th p + Real.log (wedge p.ψ π)]

/-- Woodford (2003), App. A.3: The transverse coordinate `v = Θŷ − (1−β)ψπ`. -/
noncomputable def vv (p : Par) (z : Fin 3 → ℝ) : ℝ := Th p * z 0 - (1 - p.β) * p.ψ * z 1

/-- Woodford (2003), App. A.3: Every point of the resource manifold is `zz(π, v)` with `π = x₁`, `v
= vv x`. -/
theorem zz_of_res (hp : p.Basic) {z : Fin 3 → ℝ} (h : Res p z) : zz p (z 1) (vv p z) = z := by
  have hc := res_c h
  have hT := (Th_pos hp).ne'
  have e0 : aa p * z 1 + vv p z / Th p = z 0 := by
    unfold aa vv; field_simp; ring
  funext i
  fin_cases i
  · simp [zz, e0]
  · simp [zz]
  · simp only [zz, Fin.reduceFinMk, Matrix.cons_val, e0]; rw [hc]

/-- Woodford (2003), App. A.3: `zz(π, v)` lies on the resource manifold when `C/Y > 0`. -/
theorem res_zz {π v : ℝ} (hw : 0 < wedge p.ψ π) : Res p (zz p π v) := by
  simp only [Res, Qmap, zz, Matrix.cons_val]
  rw [Real.exp_add, Real.exp_log hw]
  simp only [wedge]; ring

/-- Woodford (2003), Prop. 4.3 (**the transcritical coefficient, as a jet**): along the centre
line `π ↦ zz(π, 0)` the drift has `D(0) = 0`, `D′(0) = 0` and `D″(0) = f₂ = φ_yψS/(Θθm)`. -/
theorem J_f (hp : p.Basic) (hb : p.κ * (p.φ - 1) + (1 - p.β) * p.φy = 0) :
    J2 (fun π => Dfun p (zz p π 0)) 0 (f2 p) := by
  have hT := (Th_pos hp).ne'
  have hθ : p.θ ≠ 0 := by linarith [hp.one_lt_θ]
  have hm : p.m ≠ 0 := hp.m_pos.ne'
  have hbT := boundary_Th hp hb
  have hk := kc_mul_Th hp
  have hw0 : wedge p.ψ 0 = 1 := by simp [wedge]
  have hY : J2 (fun π => aa p * π) (aa p) 0 :=
    J2_eq (J2_const_mul (aa p) J2_id) (by ring) (by ring)
  have hA : J2 (fun π => aa p * π - p.σ * (aa p * π + Real.log (wedge p.ψ π)))
      ((1 - p.σ) * aa p) (p.σ * p.ψ) :=
    J2_eq (J2_sub hY (J2_const_mul p.σ (J2_add hY (J_lw p.ψ)))) (by ring) (by ring)
  have hA0 : aa p * 0 - p.σ * (aa p * 0 + Real.log (wedge p.ψ 0)) = 0 := by
    simp [hw0]
  have hE := J2_expc hA
  rw [hA0, Real.exp_zero] at hE
  have hg := J_g
  have hGz := J2_const_mul p.ψ (J2_mul hE hg)
  have hH1 := J2_exp ((1 + p.ω) * aa p)
  have hH := J2_const_mul (p.θ * p.m) (J2_sub hH1 hE)
  have hf := J2_sub (J2_add (J2_const_mul (p.φ - 1) J2_id) (J2_const_mul p.φy hY))
    (J2_const_mul (kc p) (J2_sub (J2_const_mul (1 - p.β) hGz) hH))
  refine J2_eq (J2_congr hf fun π => ?_) ?_ ?_
  · simp only [Dfun, zz, Gadj, Hmc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Pi.zero_apply, zero_div, add_zero, mul_zero, sub_zero]
    ring_nf
  · simp only [hw0, Real.log_one, Real.exp_zero, sub_self, mul_zero, add_zero,
      mul_one, one_mul, zero_add]
    have ha : Th p * aa p = (1 - p.β) * p.ψ := by unfold aa; field_simp
    have e1 : p.θ * p.m * ((1 + p.ω) * aa p - (1 - p.σ) * aa p) = (1 - p.β) * p.ψ := by
      rw [← ha]; unfold Th; ring
    have e2 : p.φ - 1 + p.φy * aa p = 0 := by
      unfold aa; field_simp; linear_combination hbT
    rw [e1, sub_self, mul_zero, sub_zero, e2]
  · simp only [hw0, Real.log_one, Real.exp_zero, sub_self, mul_zero, add_zero,
      mul_one, one_mul, zero_add]
    have hs : p.σ + p.ω ≠ 0 := by linarith [hp.σ_pos, hp.ω_nonneg]
    unfold f2 Sc aa kc Th
    field_simp
    ring

/-! ## The Peano remainder of a second-order jet -/

/-- Woodford (2003), Ch. 6, §1 and App. A.3 (**Peano's form of the second-order remainder**): if
`f(0) = 0`, `f′(0) = 0` and `f″(0) = v₂` (a `J2` jet), then for every `η > 0`,
`|f(x) − (v₂/2)x²| ≤ ηx²` near `0`. -/
theorem peano2 {f : ℝ → ℝ} {v2 : ℝ} (hf : J2 f 0 v2) (h0 : f 0 = 0) {η : ℝ} (hη : 0 < η) :
    ∃ ρ > 0, ∀ x, |x| < ρ → |f x - v2 / 2 * x ^ 2| ≤ η * x ^ 2 := by
  obtain ⟨f1, hev, hd, h10⟩ := hf
  obtain ⟨ρ1, hρ1, hr⟩ := NonlinearRotembergBoundary.small_remainder hd.differentiableAt hη
  obtain ⟨ρ2, hρ2, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨min ρ1 ρ2, lt_min hρ1 hρ2, fun x hx => ?_⟩
  have hfd : fderiv ℝ f1 0 = ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v2 :=
    hd.hasFDerivAt.fderiv
  set g : ℝ → ℝ := fun t => f t - v2 / 2 * t ^ 2
  have hseg : ∀ t ∈ Set.uIcc 0 x, |t| ≤ |x| := fun t ht => by
    rcases le_total 0 x with h | h
    · rw [Set.uIcc_of_le h] at ht
      rw [abs_of_nonneg ht.1, abs_of_nonneg h]; exact ht.2
    · rw [Set.uIcc_of_ge h] at ht
      rw [abs_of_nonpos ht.2, abs_of_nonpos h]; linarith [ht.1]
  have hder : ∀ t ∈ Set.uIcc 0 x, HasDerivWithinAt g (f1 t - v2 * t) (Set.uIcc 0 x) t :=
    fun t ht => by
      have ht2 : dist t 0 < ρ2 := by
        rw [Real.dist_eq, sub_zero]
        exact lt_of_le_of_lt (hseg t ht) (hx.trans_le (min_le_right _ _))
      have h1 := hball ht2
      have h2 := (hasDerivAt_pow 2 t).const_mul (v2 / 2)
      refine (h1.sub h2).hasDerivWithinAt.congr_deriv ?_
      push_cast; ring
  have hbound : ∀ t ∈ Set.uIcc 0 x, ‖f1 t - v2 * t‖ ≤ η * |x| := fun t ht => by
    have ht1 : ‖t‖ < ρ1 := by
      rw [Real.norm_eq_abs]
      exact lt_of_le_of_lt (hseg t ht) (hx.trans_le (min_le_left _ _))
    have := hr t ht1
    rw [hfd, h10] at this
    simp only [ContinuousLinearMap.smulRight_apply, smul_eq_mul,
      sub_zero, Real.norm_eq_abs] at this
    rw [Real.norm_eq_abs, mul_comm v2 t]
    exact this.trans (mul_le_mul_of_nonneg_left (hseg t ht) hη.le)
  have hmv := (convex_uIcc (0 : ℝ) x).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound
    Set.left_mem_uIcc Set.right_mem_uIcc
  have hg0 : g 0 = 0 := by simp [g, h0]
  rw [hg0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmv
  calc |f x - v2 / 2 * x ^ 2| = |g x| := rfl
    _ ≤ η * |x| * |x| := hmv
    _ = η * x ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-! ## Moving off the centre line -/

/-- Woodford (2003), Prop. 4.3: the `v`-derivative of the drift at `zz(π, v)`. -/
noncomputable def dvf (p : Par) (π v : ℝ) : ℝ :=
  p.φy / Th p - kc p * ((1 - p.β) * (p.ψ *
    (Real.exp (aa p * π + v / Th p - p.σ * (aa p * π + v / Th p + Real.log (wedge p.ψ π))) *
      ((1 - p.σ) / Th p) * ((Real.exp π - 1) * Real.exp π))) -
    p.θ * p.m * (Real.exp ((1 + p.ω) * (aa p * π + v / Th p)) * ((1 + p.ω) / Th p) -
      Real.exp (aa p * π + v / Th p - p.σ * (aa p * π + v / Th p + Real.log (wedge p.ψ π))) *
        ((1 - p.σ) / Th p)))

/-- Woodford (2003), Prop. 4.3: `v ↦ D(zz(π, v))` has derivative `dvf π v`. -/
theorem hasDerivAt_Dzz (π v : ℝ) : HasDerivAt (fun w => Dfun p (zz p π w)) (dvf p π v) v := by
  have hY : HasDerivAt (fun w => aa p * π + w / Th p) (1 / Th p) v := by
    simpa using ((hasDerivAt_id v).div_const (Th p)).const_add (aa p * π)
  have hA : HasDerivAt (fun w => aa p * π + w / Th p - p.σ * (aa p * π + w / Th p +
      Real.log (wedge p.ψ π))) ((1 - p.σ) / Th p) v := by
    have := hY.sub ((hY.add_const (Real.log (wedge p.ψ π))).const_mul p.σ)
    refine this.congr_deriv ?_; ring
  have hB : HasDerivAt (fun w => (1 + p.ω) * (aa p * π + w / Th p)) ((1 + p.ω) / Th p) v := by
    have := hY.const_mul (1 + p.ω)
    refine this.congr_deriv ?_; ring
  have hEA := hA.exp
  have hEB := hB.exp
  have h := ((hY.const_mul p.φy).const_add ((p.φ - 1) * π)).sub
    ((((hEA.mul_const ((Real.exp π - 1) * Real.exp π)).const_mul p.ψ).const_mul (1 - p.β)).sub
      ((hEB.sub hEA).const_mul (p.θ * p.m)) |>.const_mul (kc p))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
  · simp only [dvf]; ring
  · simp only [Dfun, zz, Gadj, Hmc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Pi.zero_apply, mul_zero, sub_zero, add_zero, Pi.sub_apply]

/-- Woodford (2003), App. A.3: `dvf` vanishes at the steady state. -/
theorem dvf_zero (hp : p.Basic) : dvf p 0 0 = 0 := by
  have hT := (Th_pos hp).ne'
  have hk := kc_mul_Th hp
  have hw0 : wedge p.ψ 0 = 1 := by simp [wedge]
  simp only [dvf, mul_zero, zero_div, add_zero, hw0, Real.log_one, Real.exp_zero, sub_self,
    mul_one, one_mul]
  field_simp
  unfold Th at hk ⊢
  linear_combination hk

/-- Woodford (2003), Prop. 4.3 (**the transverse derivative is small**): there are `ρ > 0` and
`C ≥ 0` with `|dvf π v| ≤ C max(|π|, |v|)` for `|π|, |v| < ρ`. -/
theorem dvf_bound (hp : p.Basic) : ∃ ρ > 0, ∃ C ≥ 0, ∀ π v : ℝ, |π| < ρ → |v| < ρ →
    |dvf p π v| ≤ C * max |π| |v| := by
  set F : ℝ × ℝ → ℝ := fun w => dvf p w.1 w.2 with hF
  have hw0 : wedge p.ψ 0 ≠ 0 := by simp [wedge]
  have hdw : DifferentiableAt ℝ (fun w : ℝ × ℝ => Real.log (wedge p.ψ w.1)) 0 := by
    have h1 : DifferentiableAt ℝ (fun w : ℝ × ℝ => wedge p.ψ w.1) 0 := by
      unfold wedge; fun_prop
    exact h1.log (by simpa using hw0)
  have hd : DifferentiableAt ℝ F 0 := by
    simp only [hF, dvf]
    fun_prop
  obtain ⟨ρ, hρ, h⟩ := NonlinearRotembergBoundary.small_remainder hd one_pos
  refine ⟨ρ, hρ, ‖fderiv ℝ F 0‖ + 1, by positivity, fun π v hπ hv => ?_⟩
  have hn : ‖((π, v) : ℝ × ℝ)‖ = max |π| |v| := by simp [Prod.norm_def]
  have hlt : ‖((π, v) : ℝ × ℝ)‖ < ρ := by rw [hn]; exact max_lt hπ hv
  have h1 := h (π, v) hlt
  have hF0 : F 0 = 0 := dvf_zero hp
  rw [hF0, sub_zero] at h1
  have h2 := (fderiv ℝ F 0).le_opNorm (π, v)
  have h3 : ‖F (π, v)‖ ≤ ‖fderiv ℝ F 0 (π, v)‖ + 1 * ‖((π, v) : ℝ × ℝ)‖ := by
    have := norm_le_insert' (F (π, v)) (fderiv ℝ F 0 (π, v)); linarith
  rw [hn] at h2 h3
  rw [Real.norm_eq_abs] at h3
  change |dvf p π v| ≤ _
  nlinarith [norm_nonneg (fderiv ℝ F 0)]

/-- Woodford (2003), Prop. 4.3 (**moving off the centre line**): there are `ρ > 0` and `C ≥ 0`
with `|D(zz(π, v)) − D(zz(π, 0))| ≤ C(|π| + |v|)|v|` for `|π|, |v| < ρ`. -/
theorem transverse_bound (hp : p.Basic) : ∃ ρ > 0, ∃ C ≥ 0, ∀ π v : ℝ, |π| < ρ → |v| < ρ →
    |Dfun p (zz p π v) - Dfun p (zz p π 0)| ≤ C * (|π| + |v|) * |v| := by
  obtain ⟨ρ, hρ, C, hC, h⟩ := dvf_bound hp
  refine ⟨ρ, hρ, C, hC, fun π v hπ hv => ?_⟩
  have hseg : ∀ t ∈ Set.uIcc 0 v, |t| ≤ |v| := fun t ht => by
    rcases le_total 0 v with h | h
    · rw [Set.uIcc_of_le h] at ht
      rw [abs_of_nonneg ht.1, abs_of_nonneg h]; exact ht.2
    · rw [Set.uIcc_of_ge h] at ht
      rw [abs_of_nonpos ht.2, abs_of_nonpos h]; linarith [ht.1]
  have hder : ∀ t ∈ Set.uIcc 0 v, HasDerivWithinAt (fun w => Dfun p (zz p π w)) (dvf p π t)
      (Set.uIcc 0 v) t := fun t _ => (hasDerivAt_Dzz π t).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.uIcc 0 v, ‖dvf p π t‖ ≤ C * (|π| + |v|) := fun t ht => by
    rw [Real.norm_eq_abs]
    refine (h π t hπ (lt_of_le_of_lt (hseg t ht) hv)).trans ?_
    refine mul_le_mul_of_nonneg_left (max_le (by linarith [abs_nonneg v]) ?_) hC
    linarith [hseg t ht, abs_nonneg π]
  have hmv := (convex_uIcc (0 : ℝ) v).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound
    Set.left_mem_uIcc Set.right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero] at hmv
  exact hmv

/-- Woodford (2003), Prop. 4.3 (**the drift near the centre line**): for every `η > 0` there are
`ρ > 0` and `C ≥ 0` with `|D(zz(π, v)) − (f₂/2)π²| ≤ ηπ² + C(|π| + |v|)|v|` for
`|π|, |v| < ρ`. -/
theorem drift_pi_v (hp : p.Basic) (hb : p.κ * (p.φ - 1) + (1 - p.β) * p.φy = 0) {η : ℝ}
    (hη : 0 < η) : ∃ ρ > 0, ∃ C ≥ 0, ∀ π v : ℝ, |π| < ρ → |v| < ρ →
      |Dfun p (zz p π v) - f2 p / 2 * π ^ 2| ≤ η * π ^ 2 + C * (|π| + |v|) * |v| := by
  have h0 : (fun π => Dfun p (zz p π 0)) 0 = 0 := by
    simp [Dfun, zz, Gadj, Hmc, wedge]
  obtain ⟨ρ1, hρ1, h1⟩ := peano2 (J_f hp hb) h0 hη
  obtain ⟨ρ2, hρ2, C, hC, h2⟩ := transverse_bound hp
  refine ⟨min ρ1 ρ2, lt_min hρ1 hρ2, C, hC, fun π v hπ hv => ?_⟩
  have a := h1 π (hπ.trans_le (min_le_left _ _))
  have b := h2 π v (hπ.trans_le (min_le_right _ _)) (hv.trans_le (min_le_right _ _))
  calc _ = |(Dfun p (zz p π v) - Dfun p (zz p π 0)) + (Dfun p (zz p π 0) - f2 p / 2 * π ^ 2)| := by
        ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

/-! ## The second-order estimate in the exact coordinates -/

/-- Woodford (2003), App. A.3: `|v| ≤ (Θ + (1−β)ψ)‖x‖`. -/
theorem abs_vv_le (hp : p.Basic) (z : Fin 3 → ℝ) :
    |vv p z| ≤ (Th p + (1 - p.β) * p.ψ) * ‖z‖ := by
  have h0 := abs_le_norm z 0
  have h1 := abs_le_norm z 1
  have hT := Th_pos hp
  have hb : 0 ≤ (1 - p.β) * p.ψ := mul_nonneg (by linarith [hp.β_lt_one]) hp.ψ_pos.le
  unfold vv
  calc _ ≤ |Th p * z 0| + |(1 - p.β) * p.ψ * z 1| := abs_sub _ _
    _ ≤ Th p * ‖z‖ + (1 - p.β) * p.ψ * ‖z‖ := by
        rw [abs_mul, abs_mul, abs_of_pos hT, abs_of_nonneg hb]
        exact add_le_add (mul_le_mul_of_nonneg_left h0 hT.le) (mul_le_mul_of_nonneg_left h1 hb)
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
-- a long chain of explicit estimates
/-- Woodford (2003), Prop. 4.3 and App. A.3 (**the drift of the centre coordinate is `qL²` to
second order**): for every `η > 0` there are `ρ > 0` and `C ≥ 0` such that every `x` on the
resource manifold with `‖x‖ < ρ` satisfies
`|D(x) − qL(x)²| ≤ ηL(x)² + C|V(x)|(|L(x)| + |V(x)|)`. -/
theorem second_order_D (hp : p.Basic) (hb : p.κ * (p.φ - 1) + (1 - p.β) * p.φy = 0) {η : ℝ}
    (hη : 0 < η) : ∃ ρ > 0, ∃ C ≥ 0, ∀ z : Fin 3 → ℝ, ‖z‖ < ρ → Res p z →
      |Dfun p z - qc p * Lf p z ^ 2| ≤
        η * Lf p z ^ 2 + C * |Vf p z| * (|Lf p z| + |Vf p z|) := by
  have hT := Th_pos hp
  have hG := Gam_pos hp
  have hσ := hp.σ_pos
  have hψ := hp.ψ_pos
  obtain ⟨ρK, hρK, K, hK, hnorm⟩ := norm_le_LV hp
  set η1 := η / (4 * K ^ 2 + 4) with hη1
  have hη1p : 0 < η1 := by positivity
  have hη1K : η1 * K ^ 2 ≤ η / 4 := by
    rw [hη1, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  obtain ⟨ρ1, hρ1, C1, hC1, hA⟩ := drift_pi_v hp hb hη1p
  set cv := Th p + (1 - p.β) * p.ψ with hcv
  have hcv0 : 0 < cv := by
    have : 0 ≤ (1 - p.β) * p.ψ := mul_nonneg (by linarith [hp.β_lt_one]) hψ.le
    positivity
  set C2 := |f2 p| * p.σ / Gam p + |f2 p| * p.σ ^ 2 / (2 * Gam p ^ 2) with hC2
  have hC20 : 0 ≤ C2 := by positivity
  set C3 := C1 + C2 with hC3
  have hC30 : 0 ≤ C3 := by positivity
  set C6 := C3 * (1 + cv) * K / (p.σ * p.ψ) with hC6
  have hC60 : 0 ≤ C6 := by positivity
  set C5 := |qc p| * K * (2 + K) with hC5
  have hC50 : 0 ≤ C5 := by positivity
  set η2 := min 1 (η / (2 * (C5 + C6 * K) + 2)) with hη2
  have hη2p : 0 < η2 := lt_min one_pos (by positivity)
  have hη21 : η2 ≤ 1 := min_le_left _ _
  have hη2C : η2 * (C5 + C6 * K) ≤ η / 2 := by
    have h := min_le_right 1 (η / (2 * (C5 + C6 * K) + 2))
    rw [← hη2] at h
    have h' := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ C5 + C6 * K)
    refine h'.trans ?_
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨ρ2, hρ2, hLV⟩ := rem_LV hp hη2p
  refine ⟨min (min ρK ρ2) (ρ1 / (cv + 1)), lt_min (lt_min hρK hρ2) (by positivity),
    2 * η + C6, by positivity, fun z hz hres => ?_⟩
  have hzK : ‖z‖ < ρK := hz.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hz2 : ‖z‖ < ρ2 := hz.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hz1 : ‖z‖ < ρ1 / (cv + 1) := hz.trans_le (min_le_right _ _)
  have hzn := norm_nonneg z
  set π := z 1 with hπdef
  set v := vv p z with hvdef
  have hπn : |π| ≤ ‖z‖ := abs_le_norm z 1
  have hvn : |v| ≤ cv * ‖z‖ := abs_vv_le hp z
  have hzρ : (cv + 1) * ‖z‖ < ρ1 := by rwa [lt_div_iff₀ (by positivity), mul_comm] at hz1
  have hπρ : |π| < ρ1 := by nlinarith
  have hvρ : |v| < ρ1 := by nlinarith
  -- step (i): the drift near the centre line
  have h1 := hA π v hπρ hvρ
  rw [zz_of_res hp hres] at h1
  -- step (ii): from `π²` to `L_l²`
  have hLl : Ll p z = (Gam p * π + p.σ * v) / Th p := by
    rw [eq_div_iff hT.ne']; simp only [Ll, Gam, π, v, vv, kc, Th]; ring
  have hVl : Vl p z = p.σ * p.ψ * v := by simp only [Vl, v, vv]; ring
  have hq2 : qc p * Ll p z ^ 2 = f2 p / 2 * π ^ 2 + f2 p * p.σ * π * v / Gam p +
      f2 p * p.σ ^ 2 * v ^ 2 / (2 * Gam p ^ 2) := by
    rw [hLl]; unfold qc; field_simp; ring
  have h2 : |f2 p / 2 * π ^ 2 - qc p * Ll p z ^ 2| ≤ C2 * (|π| + |v|) * |v| := by
    rw [hq2]
    have e : f2 p / 2 * π ^ 2 - (f2 p / 2 * π ^ 2 + f2 p * p.σ * π * v / Gam p +
        f2 p * p.σ ^ 2 * v ^ 2 / (2 * Gam p ^ 2)) =
        -(f2 p * p.σ * π * v / Gam p + f2 p * p.σ ^ 2 * v ^ 2 / (2 * Gam p ^ 2)) := by ring
    rw [e, abs_neg]
    have a1 : |f2 p * p.σ * π * v / Gam p| = |f2 p| * p.σ / Gam p * (|π| * |v|) := by
      rw [abs_div, abs_mul, abs_mul, abs_mul, abs_of_pos hσ, abs_of_pos hG]; ring
    have a2 : |f2 p * p.σ ^ 2 * v ^ 2 / (2 * Gam p ^ 2)| =
        |f2 p| * p.σ ^ 2 / (2 * Gam p ^ 2) * (|v| * |v|) := by
      rw [abs_div, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < p.σ ^ 2),
        abs_of_pos (by positivity : 0 < 2 * Gam p ^ 2), abs_pow, sq |v|]; ring
    have b1 : 0 ≤ |f2 p| * p.σ / Gam p := by positivity
    have b2 : 0 ≤ |f2 p| * p.σ ^ 2 / (2 * Gam p ^ 2) := by positivity
    calc _ ≤ |f2 p * p.σ * π * v / Gam p| + |f2 p * p.σ ^ 2 * v ^ 2 / (2 * Gam p ^ 2)| :=
          abs_add_le _ _
      _ = |f2 p| * p.σ / Gam p * (|π| * |v|) +
          |f2 p| * p.σ ^ 2 / (2 * Gam p ^ 2) * (|v| * |v|) := by rw [a1, a2]
      _ ≤ |f2 p| * p.σ / Gam p * ((|π| + |v|) * |v|) +
          |f2 p| * p.σ ^ 2 / (2 * Gam p ^ 2) * ((|π| + |v|) * |v|) := by
          gcongr <;> nlinarith [abs_nonneg π, abs_nonneg v]
      _ = C2 * (|π| + |v|) * |v| := by simp only [hC2]; ring
  -- the exact coordinates
  set L := Lf p z with hL
  set V := Vf p z with hV
  set X := |L| + |V| with hX
  have hX0 : 0 ≤ X := by positivity
  have hzX : ‖z‖ ≤ K * X := hnorm z hzK hres
  obtain ⟨r1, r2⟩ := hLV z hz2 hres
  -- step (iii): from `L_l²` to `L²`
  have h3 : |qc p * Ll p z ^ 2 - qc p * L ^ 2| ≤ C5 * η2 * X ^ 2 := by
    have e : qc p * Ll p z ^ 2 - qc p * L ^ 2 = qc p * ((Ll p z - L) * (Ll p z + L)) := by ring
    rw [e, abs_mul, abs_mul]
    have d1 : |Ll p z - L| ≤ η2 * (K * X) := by
      rw [abs_sub_comm]; exact r1.trans (mul_le_mul_of_nonneg_left hzX hη2p.le)
    have d2 : |Ll p z + L| ≤ 2 * X + K * X := by
      have : |Ll p z| ≤ |L| + η2 * (K * X) := by
        have := abs_sub_abs_le_abs_sub (Ll p z) L; linarith
      have : η2 * (K * X) ≤ K * X := by nlinarith [mul_nonneg hK.le hX0]
      have := abs_add_le (Ll p z) L
      have : |L| ≤ X := by simp only [hX]; linarith [abs_nonneg V]
      linarith
    calc |qc p| * (|Ll p z - L| * |Ll p z + L|) ≤ |qc p| * ((η2 * (K * X)) * (2 * X + K * X)) := by
          gcongr
      _ = C5 * η2 * X ^ 2 := by simp only [hC5]; ring
  -- step (iv): the transverse terms
  have hvV : |v| ≤ (|V| + η2 * (K * X)) / (p.σ * p.ψ) := by
    rw [le_div_iff₀ (by positivity)]
    have : |Vl p z| = p.σ * p.ψ * |v| := by
      rw [hVl, abs_mul, abs_of_pos (by positivity : 0 < p.σ * p.ψ)]
    have h' : |Vl p z| ≤ |V| + η2 * (K * X) := by
      have := abs_sub_abs_le_abs_sub (Vl p z) V
      rw [abs_sub_comm] at this
      have := r2.trans (mul_le_mul_of_nonneg_left hzX hη2p.le)
      linarith
    linarith
  have h4 : C3 * (|π| + |v|) * |v| ≤ C6 * X * |V| + C6 * K * η2 * X ^ 2 := by
    have hs : |π| + |v| ≤ (1 + cv) * (K * X) := by
      have : |π| + |v| ≤ (1 + cv) * ‖z‖ := by linarith
      exact this.trans (mul_le_mul_of_nonneg_left hzX (by positivity))
    calc C3 * (|π| + |v|) * |v| ≤ C3 * ((1 + cv) * (K * X)) *
          ((|V| + η2 * (K * X)) / (p.σ * p.ψ)) := by gcongr
      _ = C6 * X * |V| + C6 * K * η2 * X ^ 2 := by simp only [hC6]; field_simp
  -- step (v): the `ηπ²` term
  have h5 : η1 * π ^ 2 ≤ η1 * K ^ 2 * X ^ 2 := by
    have : π ^ 2 ≤ (K * X) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hπn.trans hzX) 2
    calc η1 * π ^ 2 ≤ η1 * (K * X) ^ 2 := mul_le_mul_of_nonneg_left this hη1p.le
      _ = η1 * K ^ 2 * X ^ 2 := by ring
  -- assembly
  have hXsq : X ^ 2 ≤ L ^ 2 + 2 * |V| * X := by
    have e : X ^ 2 = L ^ 2 + 2 * |V| * X - |V| ^ 2 := by simp only [hX]; rw [← sq_abs L]; ring
    have := sq_nonneg |V|
    linarith
  have htot : |Dfun p z - qc p * L ^ 2| ≤ (η1 * K ^ 2 + η2 * (C5 + C6 * K)) * X ^ 2 +
      C6 * X * |V| := by
    have e : Dfun p z - qc p * L ^ 2 = (Dfun p z - f2 p / 2 * π ^ 2) +
        (f2 p / 2 * π ^ 2 - qc p * Ll p z ^ 2) + (qc p * Ll p z ^ 2 - qc p * L ^ 2) := by ring
    rw [e]
    have t1 := abs_add_le (Dfun p z - f2 p / 2 * π ^ 2 + (f2 p / 2 * π ^ 2 - qc p * Ll p z ^ 2))
      (qc p * Ll p z ^ 2 - qc p * L ^ 2)
    have t2 := abs_add_le (Dfun p z - f2 p / 2 * π ^ 2) (f2 p / 2 * π ^ 2 - qc p * Ll p z ^ 2)
    have hC3e : C1 * (|π| + |v|) * |v| + C2 * (|π| + |v|) * |v| = C3 * (|π| + |v|) * |v| := by
      simp only [hC3]; ring
    have e2 : (η1 * K ^ 2 + η2 * (C5 + C6 * K)) * X ^ 2 + C6 * X * |V| =
        η1 * K ^ 2 * X ^ 2 + C5 * η2 * X ^ 2 + (C6 * X * |V| + C6 * K * η2 * X ^ 2) := by ring
    rw [e2]
    linarith
  have hcoef : η1 * K ^ 2 + η2 * (C5 + C6 * K) ≤ 3 * η / 4 := by linarith
  have hA1 : (η1 * K ^ 2 + η2 * (C5 + C6 * K)) * X ^ 2 ≤ 3 * η / 4 * X ^ 2 :=
    mul_le_mul_of_nonneg_right hcoef (sq_nonneg X)
  have hA2 : 3 * η / 4 * X ^ 2 ≤ 3 * η / 4 * (L ^ 2 + 2 * |V| * X) :=
    mul_le_mul_of_nonneg_left hXsq (by positivity)
  have key : η * L ^ 2 + (2 * η + C6) * |V| * (|L| + |V|) -
      (3 * η / 4 * (L ^ 2 + 2 * |V| * X) + C6 * X * |V|) = η / 4 * L ^ 2 + η / 2 * (|V| * X) := by
    simp only [hX]; ring
  have hk0 : 0 ≤ η / 4 * L ^ 2 + η / 2 * (|V| * X) := by positivity
  linarith

end Woodford.StabilizationWelfare.NonlinearRotembergCentreSecond
