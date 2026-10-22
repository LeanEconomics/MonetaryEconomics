/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.BridgeLinks

/-!
# Proposition 6.15, Layer B, over a probability space of goods

Woodford (2003), *Interest and Prices*, Chapter 6, §5 (pp. 455–463, Proposition 6.15), §2.2
(pp. 396–405: the Calvo cross-section) and Appendix E (pp. 692–695).

`BridgeExtensions.prop615_layerB` and `BridgeLinks.prop615_goods_layerB` take the cross-section of
goods to be a FINITE weighted set (`Fintype ι`). Here the goods form an arbitrary probability
space `(Gs, γ)` (for instance the continuum of Calvo reset histories of
`NonlinearNKMarkovGoods.goodsMeasure`), and every cross-sectional object is an integral:

* `logYM` (the log Dixit–Stiglitz output index, `CrossSection.logMeanExp` with exponent
  `1 − θ⁻¹`), `periodUM` (the actual period utility `u(Y) − ∫ v(y(i)) dγ`), `cesAtomM`;
* `logYM_o`, `crossVarM_o`, `cesAtomM_o`: orders of the aggregates when the cross-section is
  `O(s)` UNIFORMLY in the goods (`L ×ˢ ⊤`), from `CrossSection.abs_logMeanExp_le` and
  `CrossSection.logMeanExp_second_order`;
* `int_o`: integrating a remainder that is `O(sⁿ)` uniformly in the goods;
* `eq51_exactM` ((5.1) as an exact identity with integrals) and **`eq51_actualM`** ((5.1) from
  primitives over a goods probability space).
* **`prop615_layerBM`**: Proposition 6.15, Layer B, with the cross-section any goods
  probability space (`LargeDistortions.prop615` applied with `V = var ŷ` an integral).
* `logPM`, **`goods_state_packageM`**: from a Calvo population on `(G, γ)`
  (`Links.GoodsPop.Calvo`), `var ŷ = θ²D`, the exact dispersion law, `D = O(ε²)` and
  `π̄ − π = O(ε²)` uniformly (`CrossSection.logMeanExp_sub_mean_le`), and
  **`prop615_goods_layerBM`**.
* `logMeanExp_wMeasure`, `logYM_wMeasure`, `logPM_wMeasure`, `periodUM_wMeasure`,
  **`special_case`**: over `BridgeLinks.wMeasure w` every object is the finite weighted one.
-/

namespace Woodford.StabilizationWelfare.NonlinearNKMarkovGoodsLayerB

open MeasureTheory Filter Topology Asymptotics
open CrossSection (crossMean crossVar logMeanExp)
open ExpLogCES (expRem)
open BridgeExtensions (dY dYY dXi dYXi dXiXi tip51)

variable {Gs : Type*} [MeasurableSpace Gs] (γ : Measure Gs) [IsProbabilityMeasure γ]
variable {B : Type*} {L : Filter B} {s : B → ℝ}

/-! ## The cross-sectional aggregates -/

/-- Woodford (2003), eq. (2.6), p. 393: `Ŷ = log(Y/Ȳ)`, the log of the Dixit–Stiglitz index
(elasticity `θ`) of `e^{ŷ(i)}` over the goods probability space. -/
noncomputable def logYM (θ : ℝ) (yh : Gs → ℝ) : ℝ := logMeanExp γ (1 - θ⁻¹) yh

/-- Woodford (2003), eq. (E.5), p. 694: the CES atom `r_C = E ŷ − [Ŷ − ½(1 − θ⁻¹) var ŷ]`. -/
noncomputable def cesAtomM (θ : ℝ) (yh : Gs → ℝ) : ℝ :=
  crossMean γ yh - (logYM γ θ yh - (1 - θ⁻¹) / 2 * crossVar γ yh)

/-- Woodford (2003), §2, eq. (2.1) and §5, p. 455: the ACTUAL period utility
`u(Y; ξ) − ∫ v(y(i); ξ) dγ(i)` of a cross-section of goods with outputs `y(i) = Ȳe^{ŷ(i)}`. -/
noncomputable def periodUM {Ξ : Type*} (u v : ℝ × Ξ → ℝ) (θ Ybar : ℝ) (yh : Gs → ℝ) (xu xv : Ξ) :
    ℝ :=
  u (Ybar * Real.exp (logYM γ θ yh), xu) - ∫ i, v (Ybar * Real.exp (yh i), xv) ∂γ

/-- A continuous function of a bounded measurable cross-section is integrable. -/
theorem int_comp {φ : ℝ → ℝ} (hφ : Continuous φ) {y : Gs → ℝ} (hy : Measurable y) {M : ℝ}
    (hM : ∀ i, |y i| ≤ M) : Integrable (fun i => φ (y i)) γ := by
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℝ) M).exists_bound_of_continuousOn hφ.continuousOn
  exact CrossSection.integrable_of_abs_le γ (hφ.measurable.comp hy) (K := K) fun i => by
    rw [← Real.norm_eq_abs]
    exact hK _ (by rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]; exact hM i)

/-- A joint order bound uniform in the goods gives one constant for all goods. -/
theorem goods_bound {H : Type*} {F : B → H → ℝ} {n : ℕ}
    (h : (fun p : B × H => F p.1 p.2) =O[L ×ˢ (⊤ : Filter H)] fun p => s p.1 ^ n) :
    ∃ C, ∀ᶠ b in L, ∀ i, |F b i| ≤ C * |s b ^ n| :=
  BridgeExtensions.uniform_bound (f := fun p : B × H => F p.1 p.2) (g := fun b => s b ^ n) h

/-- Woodford (2003), App. E, p. 693: integrating over the goods a remainder that is `O(sⁿ)`
uniformly in the goods gives `O(sⁿ)`. -/
theorem int_o {F : B → Gs → ℝ} {n : ℕ}
    (h : (fun p : B × Gs => F p.1 p.2) =O[L ×ˢ (⊤ : Filter Gs)] fun p => s p.1 ^ n) :
    (fun b => ∫ i, F b i ∂γ) =O[L] fun b => s b ^ n := by
  obtain ⟨C, hC⟩ := goods_bound h
  refine IsBigO.of_bound C ?_
  filter_upwards [hC] with b hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := C * |s b ^ n|)
    (Eventually.of_forall fun i => by rw [Real.norm_eq_abs]; exact hb i)).trans ?_
  rw [probReal_univ, mul_one]

/-- Woodford (2003), App. E, p. 693: a cross-section `O(s)` uniformly in the goods, as an
eventual bound `|ŷ(i)| ≤ C|s|`. -/
theorem ub_of {H : Type*} {yh : B → H → ℝ}
    (h : (fun p : B × H => yh p.1 p.2) =O[L ×ˢ (⊤ : Filter H)] fun p => s p.1 ^ 1) :
    ∃ C, 0 ≤ C ∧ ∀ᶠ b in L, ∀ i, |yh b i| ≤ C * |s b| := by
  obtain ⟨C, hC⟩ := goods_bound h
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  filter_upwards [hC] with b hb i
  have h1 := hb i
  rw [pow_one] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))

/-- Woodford (2003), (E.5), p. 694: the log output index of an `O(s)` cross-section is `O(s)`. -/
theorem logYM_o {θ : ℝ} (hθ : θ ≠ 1) {yh : B → Gs → ℝ} (hm : ∀ b, Measurable (yh b))
    (h : (fun p : B × Gs => yh p.1 p.2) =O[L ×ˢ (⊤ : Filter Gs)] fun p => s p.1 ^ 1) :
    (fun b => logYM γ θ (yh b)) =O[L] fun b => s b ^ 1 := by
  obtain ⟨C, hC0, hC⟩ := ub_of h
  have hr : (1 : ℝ) - θ⁻¹ ≠ 0 := by
    intro h0; apply hθ; have : θ⁻¹ = 1 := by linarith
    exact inv_eq_one.1 this
  refine IsBigO.of_bound C ?_
  filter_upwards [hC] with b hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs, pow_one]
  exact CrossSection.abs_logMeanExp_le γ (hm b) hb hr

/-- Woodford (2003), App. E, p. 693: the cross-sectional variance of an `O(s)` cross-section is
`O(s²)`. -/
theorem crossVarM_o {yh : B → Gs → ℝ} (hm : ∀ b, Measurable (yh b))
    (h : (fun p : B × Gs => yh p.1 p.2) =O[L ×ˢ (⊤ : Filter Gs)] fun p => s p.1 ^ 1) :
    (fun b => crossVar γ (yh b)) =O[L] fun b => s b ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := ub_of h
  refine IsBigO.of_bound ((2 * C) ^ 2) ?_
  filter_upwards [hC] with b hb
  have hmean : |crossMean γ (yh b)| ≤ C * |s b| := by
    unfold crossMean
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := C * |s b|)
      (Eventually.of_forall fun i => by rw [Real.norm_eq_abs]; exact hb i)).trans ?_
    rw [probReal_univ, mul_one]
  have hcen : ∀ i, |yh b i - crossMean γ (yh b)| ≤ 2 * C * |s b| := fun i => by
    have := abs_sub (yh b i) (crossMean γ (yh b)); have := hb i; linarith
  obtain ⟨-, -, -, -, -, hV⟩ := CrossSection.centred_facts γ (hm b) hcen 1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (CrossSection.crossVar_nonneg _ _),
    abs_pow]
  calc _ ≤ (2 * C * |s b|) ^ 2 := hV
    _ = _ := by ring

/-- Woodford (2003), (E.5), p. 694: the CES atom of an `O(s)` cross-section is `O(s³)`. -/
theorem cesAtomM_o (hs : Tendsto s L (𝓝 0)) {θ : ℝ} (hθ : θ ≠ 1) {yh : B → Gs → ℝ}
    (hm : ∀ b, Measurable (yh b))
    (h : (fun p : B × Gs => yh p.1 p.2) =O[L ×ˢ (⊤ : Filter Gs)] fun p => s p.1 ^ 1) :
    (fun b => cesAtomM γ θ (yh b)) =O[L] fun b => s b ^ 3 := by
  obtain ⟨C, hC0, hC⟩ := ub_of h
  set r := (1 : ℝ) - θ⁻¹ with hrdef
  have hr : r ≠ 0 := by
    intro h0; apply hθ; have : θ⁻¹ = 1 := by linarith
    exact inv_eq_one.1 this
  have hsmall : ∀ᶠ b in L, |r| * (2 * C * |s b|) ≤ 1 / 2 := by
    have ht : Tendsto (fun b => |r| * (2 * C * |s b|)) L (𝓝 0) := by
      have := ((hs.abs).const_mul (2 * C)).const_mul |r|
      simpa using this
    exact ht.eventually (ge_mem_nhds (by norm_num))
  refine IsBigO.of_bound (r ^ 2 * (2 * C) ^ 3) ?_
  filter_upwards [hC, hsmall] with b hb hsb
  have hmean : |crossMean γ (yh b)| ≤ C * |s b| := by
    unfold crossMean
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := C * |s b|)
      (Eventually.of_forall fun i => by rw [Real.norm_eq_abs]; exact hb i)).trans ?_
    rw [probReal_univ, mul_one]
  have hcen : ∀ i, |yh b i - crossMean γ (yh b)| ≤ 2 * C * |s b| := fun i => by
    have := abs_sub (yh b i) (crossMean γ (yh b)); have := hb i; linarith
  obtain ⟨-, -, -, -, -, hV⟩ := CrossSection.centred_facts γ (hm b) hcen 1
  have h2 := CrossSection.logMeanExp_second_order γ (hm b) hcen hr hsb
  have hV0 := CrossSection.crossVar_nonneg γ (yh b)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
  have e : cesAtomM γ θ (yh b) = -(logMeanExp γ r (yh b) - crossMean γ (yh b) -
      r / 2 * crossVar γ (yh b)) := by
    unfold cesAtomM logYM; rw [hrdef]; ring
  rw [e, abs_neg]
  calc _ ≤ r ^ 2 * (2 * C * |s b|) * crossVar γ (yh b) := h2
    _ ≤ r ^ 2 * (2 * C * |s b|) * (2 * C * |s b|) ^ 2 :=
        mul_le_mul_of_nonneg_left hV (by positivity)
    _ = _ := by ring

/-! ## (5.1) over a goods probability space -/

/-- Woodford (2003), eq. (5.1), p. 455, as an EXACT identity over a goods probability space
(`LargeDistortions.eq51_exact` with the finite weighted sum replaced by `∫ · dγ`). -/
theorem eq51_exactM {Ybar uc ucc ucxi vy vyy vyxi σ ω θ Φ g q : ℝ}
    (hucc : ucc = -(σ * uc / Ybar)) (hucxi : ucxi = σ * uc * g) (hvy : vy = (1 - Φ) * uc)
    (hvyy : vyy = ω * vy / Ybar) (hvyxi : vyxi = -(ω * vy * q))
    (ubar uxi uxixi vbar vxi vxixi Y rY rC : ℝ) (yh ry : Gs → ℝ) (h1 : Integrable yh γ)
    (h2 : Integrable (fun i => yh i ^ 2) γ)
    (h3 : Integrable (fun i => Prop61.Rv 0 ω q (yh i) (ry i)) γ)
    (hC : crossMean γ yh = Y - (1 - θ⁻¹) / 2 * crossVar γ yh + rC) :
    Prop61.uTaylor ubar uc ucc uxi ucxi uxixi (Ybar * (Y + Y ^ 2 / 2 + rY)) -
        ∫ i, Prop61.vTaylor vbar vy vyy vxi vyxi vxixi (Ybar * (yh i + yh i ^ 2 / 2 + ry i)) ∂γ =
      -(Ybar * uc / 2) * LargeDistortions.quad51 σ ω θ Φ g q Y (crossVar γ yh) +
        ((ubar + uxi + uxixi / 2) - (vbar + vxi + vxixi / 2)) +
        Ybar * uc * LargeDistortions.R51 σ ω θ Φ g q Y (crossVar γ yh) rY rC
          (∫ i, Prop61.Rv 0 ω q (yh i) (ry i) ∂γ) := by
  rw [Prop61.uTaylor_eq_of_coeffs hucc hucxi]
  have hv : ∀ i, Prop61.vTaylor vbar vy vyy vxi vyxi vxixi (Ybar * (yh i + yh i ^ 2 / 2 + ry i)) =
      (vbar + vxi + vxixi / 2) + (Ybar * vy - Ybar * vy * (ω * q)) * yh i +
        Ybar * vy * ((1 + ω) / 2) * yh i ^ 2 + Ybar * vy * Prop61.Rv 0 ω q (yh i) (ry i) := by
    intro i
    rw [Prop61.vTaylor_eq_of_coeffs (Φ := 0) (uc := vy) (by ring) hvyy hvyxi]
    unfold Prop61.Tv
    ring
  simp_rw [hv]
  set c := vbar + vxi + vxixi / 2 with hc
  set a1 := Ybar * vy - Ybar * vy * (ω * q) with ha1
  set a2 := Ybar * vy * ((1 + ω) / 2) with ha2
  set a3 := Ybar * vy with ha3
  have I : ∫ i, (c + a1 * yh i + a2 * yh i ^ 2 + a3 * Prop61.Rv 0 ω q (yh i) (ry i)) ∂γ =
      c + a1 * ∫ i, yh i ∂γ + a2 * ∫ i, yh i ^ 2 ∂γ +
        a3 * ∫ i, Prop61.Rv 0 ω q (yh i) (ry i) ∂γ := by
    rw [integral_add (f := fun i => c + a1 * yh i + a2 * yh i ^ 2)
        (g := fun i => a3 * Prop61.Rv 0 ω q (yh i) (ry i))
        (((integrable_const c).add (h1.const_mul a1)).add (h2.const_mul a2)) (h3.const_mul a3),
      integral_add (f := fun i => c + a1 * yh i) (g := fun i => a2 * yh i ^ 2)
        ((integrable_const c).add (h1.const_mul a1)) (h2.const_mul a2),
      integral_add (f := fun _ => c) (g := fun i => a1 * yh i) (integrable_const c)
        (h1.const_mul a1), integral_const, integral_const_mul, integral_const_mul,
      integral_const_mul, probReal_univ, one_smul]
  rw [I]
  have hE2 : ∫ i, yh i ^ 2 ∂γ = crossVar γ yh + crossMean γ yh ^ 2 := by
    rw [CrossSection.crossVar_eq γ h1 h2]; ring
  have hm : ∫ i, yh i ∂γ = crossMean γ yh := rfl
  rw [hE2, hm, hC, hc, ha1, ha2, ha3, hvy]
  unfold LargeDistortions.quad51 LargeDistortions.R51 LargeDistortions.Rint Prop61.Tu
  ring

variable {Ξ : Type*} [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]

/-- Woodford (2003), eq. (5.1), p. 455, PROVED from primitives over a goods probability space
(Layer B; `BridgeExtensions.eq51_actual` with the finite cross-section replaced by `(Gs, γ)`):
for `C³` utilities with the book's coefficient definitions and a cross-section `ŷ(i)` that is
measurable and `O(s)` UNIFORMLY in the goods, with disturbances `O(s)`,
`u(Y) − ∫v(y(i))dγ = −(Ȳu_c/2)·quad51(Ŷ, var ŷ) + tip51(ξ) + O(s³)`. -/
theorem eq51_actualM (hs : Tendsto s L (𝓝 0)) {θ : ℝ} (hθ : θ ≠ 1) {u v : ℝ × Ξ → ℝ}
    (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v) {Ybar σ ω Φ : ℝ}
    (hucc : dYY u (Ybar, 0) = -(σ * dY u (Ybar, 0) / Ybar))
    (hvy : dY v (Ybar, 0) = (1 - Φ) * dY u (Ybar, 0))
    (hvyy : dYY v (Ybar, 0) = ω * dY v (Ybar, 0) / Ybar)
    {yh : B → Gs → ℝ} {xu xv : B → Ξ} {g q : B → ℝ} (hm : ∀ b, Measurable (yh b))
    (hyh : (fun p : B × Gs => yh p.1 p.2) =O[L ×ˢ (⊤ : Filter Gs)] fun p => s p.1 ^ 1)
    (hxu : xu =O[L] fun b => s b ^ 1) (hxv : xv =O[L] fun b => s b ^ 1)
    (hgO : g =O[L] fun b => s b ^ 1) (hqO : q =O[L] fun b => s b ^ 1)
    (hg : ∀ b, dYXi u (Ybar, 0) (xu b) = σ * dY u (Ybar, 0) * g b)
    (hq : ∀ b, dYXi v (Ybar, 0) (xv b) = -(ω * dY v (Ybar, 0) * q b)) :
    (fun b => periodUM γ u v θ Ybar (yh b) (xu b) (xv b) -
      (-(Ybar * dY u (Ybar, 0) / 2) * LargeDistortions.quad51 σ ω θ Φ (g b) (q b)
          (logYM γ θ (yh b)) (crossVar γ (yh b)) + tip51 u v Ybar (xu b) (xv b)))
      =O[L] fun b => s b ^ 3 := by
  have hs' : Tendsto (fun p : B × Gs => s p.1) (L ×ˢ (⊤ : Filter Gs)) (𝓝 0) := hs.comp tendsto_fst
  have hYO := logYM_o γ hθ hm hyh
  have hu1 := BridgeExtensions.uTaylor_family_exp hu Ybar hs hYO hxu
  have hxv' : (fun p : B × Gs => xv p.1) =O[L ×ˢ (⊤ : Filter Gs)] fun p => s p.1 ^ 1 :=
    hxv.comp_tendsto tendsto_fst
  have hqO' : (fun p : B × Gs => q p.1) =O[L ×ˢ (⊤ : Filter Gs)] fun p => s p.1 ^ 1 :=
    hqO.comp_tendsto tendsto_fst
  -- the per-good remainders, uniformly in the goods, integrated
  have hv1 := BridgeExtensions.uTaylor_family_exp (L := L ×ˢ (⊤ : Filter Gs))
    (s := fun p : B × Gs => s p.1) (x := fun p => yh p.1 p.2) (ξ := fun p => xv p.1) hv Ybar hs'
    hyh hxv'
  have hvI := int_o γ (F := fun b i => v (Ybar * Real.exp (yh b i), xv b) -
    Prop61.uTaylor (v (Ybar, 0)) (dY v (Ybar, 0)) (dYY v (Ybar, 0)) (dXi v (Ybar, 0) (xv b))
      (dYXi v (Ybar, 0) (xv b)) (dXiXi v (Ybar, 0) (xv b))
      (Ybar * (yh b i + yh b i ^ 2 / 2 + expRem (yh b i)))) hv1
  have hRv1 := BridgeExtensions.Rv0_o hs' ω hqO' hyh (BridgeExtensions.expRem_o hs' hyh)
  have hRvI := int_o γ (F := fun b i => Prop61.Rv 0 ω (q b) (yh b i) (expRem (yh b i))) hRv1
  have hR := BridgeExtensions.R51_o hs σ ω θ Φ hgO hqO hYO (crossVarM_o γ hm hyh)
    (BridgeExtensions.expRem_o hs hYO) (cesAtomM_o γ hs hθ hm hyh) hRvI
  obtain ⟨C, hC0, hC⟩ := ub_of hyh
  refine ((hu1.sub hvI).add (hR.const_mul_left (Ybar * dY u (Ybar, 0)))).congr' ?_
    (Eventually.of_forall fun _ => rfl)
  filter_upwards [hC] with b hb
  -- integrability of the per-good terms
  have hyb : Integrable (yh b) γ := int_comp γ continuous_id (hm b) hb
  have hy2 : Integrable (fun i => yh b i ^ 2) γ := int_comp γ (continuous_pow 2) (hm b) hb
  have hRvb : Integrable (fun i => Prop61.Rv 0 ω (q b) (yh b i) (expRem (yh b i))) γ :=
    int_comp γ (φ := fun y => Prop61.Rv 0 ω (q b) y (expRem y))
      (by unfold Prop61.Rv ExpLogCES.expRem; fun_prop) (hm b) hb
  have hvb : Integrable (fun i => v (Ybar * Real.exp (yh b i), xv b)) γ :=
    int_comp γ (φ := fun y => v (Ybar * Real.exp y, xv b))
      (hv.continuous.comp (by fun_prop)) (hm b) hb
  have hTb : Integrable (fun i => Prop61.uTaylor (v (Ybar, 0)) (dY v (Ybar, 0)) (dYY v (Ybar, 0))
      (dXi v (Ybar, 0) (xv b)) (dYXi v (Ybar, 0) (xv b)) (dXiXi v (Ybar, 0) (xv b))
      (Ybar * (yh b i + yh b i ^ 2 / 2 + expRem (yh b i)))) γ :=
    int_comp γ (φ := fun y => Prop61.uTaylor (v (Ybar, 0)) (dY v (Ybar, 0)) (dYY v (Ybar, 0))
      (dXi v (Ybar, 0) (xv b)) (dYXi v (Ybar, 0) (xv b)) (dXiXi v (Ybar, 0) (xv b))
      (Ybar * (y + y ^ 2 / 2 + expRem y))) (by unfold Prop61.uTaylor ExpLogCES.expRem; fun_prop)
      (hm b) hb
  have key := eq51_exactM γ (Ybar := Ybar) (θ := θ) (ucxi := dYXi u (Ybar, 0) (xu b))
    (vyxi := dYXi v (Ybar, 0) (xv b)) hucc (hg b) hvy hvyy (hq b) (u (Ybar, 0))
    (dXi u (Ybar, 0) (xu b)) (dXiXi u (Ybar, 0) (xu b)) (v (Ybar, 0))
    (dXi v (Ybar, 0) (xv b)) (dXiXi v (Ybar, 0) (xv b)) (logYM γ θ (yh b))
    (expRem (logYM γ θ (yh b))) (cesAtomM γ θ (yh b)) (yh b) (fun i => expRem (yh b i)) hyb hy2
    hRvb (by unfold cesAtomM; ring)
  have hsub : ∫ i, (v (Ybar * Real.exp (yh b i), xv b) -
      Prop61.uTaylor (v (Ybar, 0)) (dY v (Ybar, 0)) (dYY v (Ybar, 0)) (dXi v (Ybar, 0) (xv b))
        (dYXi v (Ybar, 0) (xv b)) (dXiXi v (Ybar, 0) (xv b))
        (Ybar * (yh b i + yh b i ^ 2 / 2 + expRem (yh b i)))) ∂γ =
      ∫ i, v (Ybar * Real.exp (yh b i), xv b) ∂γ -
        ∫ i, Prop61.vTaylor (v (Ybar, 0)) (dY v (Ybar, 0)) (dYY v (Ybar, 0))
          (dXi v (Ybar, 0) (xv b)) (dYXi v (Ybar, 0) (xv b)) (dXiXi v (Ybar, 0) (xv b))
          (Ybar * (yh b i + yh b i ^ 2 / 2 + expRem (yh b i))) ∂γ := by
    rw [integral_sub hvb hTb]
    rfl
  rw [hsub]
  unfold periodUM tip51
  linear_combination (-1 : ℝ) * key

/-! ## Proposition 6.15 over a goods probability space -/

open BridgeExtensions (UProc tendsto_amp o_weaken o_mul remAS_o bdd_of_o0 bdd_of_o tip51_o
  dsum_sub dsum_o W0615 tip615)

variable {A : Type*} {l : Filter A} {e : A → ℝ} {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), **Proposition 6.15**, (5.5)–(5.8), pp. 458–459, LAYER B over a GOODS
PROBABILITY SPACE (`BridgeExtensions.prop615_layerB` with the cross-section an arbitrary
probability space of goods): with every first-order variable `O(ε)` uniformly, outputs `O(ε)`
uniformly in the goods, `π̄ − π = O(ε²)` and `D = O(ε²)`,
`∑βᵗE_0U_t = W_0 − Ω̃ ∑βᵗE_0 L̃_t + t.i.p. + O(ε³)`. -/
theorem prop615_layerBM {α β θ ω σ sC Φ Ybar : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ : 1 < θ) (hω : 0 < ω) (hσ : 0 < σ) (hsC : 0 < sC) (hΦ0 : 0 ≤ Φ)
    (hΦ : Φ < 1) (hMd : LargeDistortions.Mden ω σ sC Φ ≠ 0)
    (he : Tendsto e l (𝓝 0))
    {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    (hucc : dYY u (Ybar, 0) = -(σ * dY u (Ybar, 0) / Ybar))
    (hvy : dY v (Ybar, 0) = (1 - Φ) * dY u (Ybar, 0))
    (hvyy : dYY v (Ybar, 0) = ω * dY v (Ybar, 0) / Ybar)
    {yh : A → ℕ → Ω → Gs → ℝ} {xu xv : A → ℕ → Ω → Ξ}
    {infl xr F K f k G cb q muw tau D pib : A → ℕ → Ω → ℝ}
    (hM : ∀ a, LargeDistortions.CalvoModel.CalvoAS 𝔼 α β θ ω σ sC (infl a) (xr a) (F a) (K a)
      (f a) (k a) (fun t z => logYM γ θ (yh a t z)) (G a) (cb a) (q a) (muw a) (tau a))
    (hym : ∀ a t z, Measurable (yh a t z))
    (hyh : (fun p : (A × (ℕ × Ω)) × Gs => yh p.1.1 p.1.2.1 p.1.2.2 p.2) =O[(l ×ˢ ⊤) ×ˢ ⊤]
      fun p => e p.1.1 ^ 1) (hxu : UProc l xu fun a => e a ^ 1)
    (hxv : UProc l xv fun a => e a ^ 1) (hiO : UProc l infl fun a => e a ^ 1)
    (hxrO : UProc l xr fun a => e a ^ 1) (hFO : UProc l F fun a => e a ^ 1)
    (hKO : UProc l K fun a => e a ^ 1) (hfO : UProc l f fun a => e a ^ 1)
    (hkO : UProc l k fun a => e a ^ 1) (hGO : UProc l G fun a => e a ^ 1)
    (hcbO : UProc l cb fun a => e a ^ 1) (hqO : UProc l q fun a => e a ^ 1)
    (hmO : UProc l muw fun a => e a ^ 1) (htO : UProc l tau fun a => e a ^ 1)
    (hpO : UProc l (fun a t z => pib a t z - infl a t z) fun a => e a ^ 2)
    (hDO : UProc l D fun a => e a ^ 2)
    (hg : ∀ a t z, dYXi u (Ybar, 0) (xu a t z) =
      σ * dY u (Ybar, 0) * (G a t z + sC * cb a t z))
    (hq : ∀ a t z, dYXi v (Ybar, 0) (xv a t z) = -(ω * dY v (Ybar, 0) * q a t z))
    (hV : ∀ a t, (fun z => crossVar γ (yh a t z)) = θ ^ 2 • D a (t + 1))
    (hD : ∀ a t, D a (t + 1) = α • D a t + (α / (1 - α)) • pib a t ^ 2) (w0 : Ω) :
    (fun a => Sequences.dsum 𝔼 β
        (fun t z => periodUM γ u v θ Ybar (yh a t z) (xu a t z) (xv a t z)) w0 -
      (W0615 𝔼 α β θ ω σ Φ Ybar (dY u (Ybar, 0)) (infl a) (F a) (K a) w0 -
        LargeDistortions.OmegaTilde Ybar (dY u (Ybar, 0)) α β θ ω σ Φ *
          Sequences.dsum 𝔼 β (LargeDistortions.loss615 α β θ ω σ sC Φ (infl a)
            (fun t z => logYM γ θ (yh a t z)) (G a) (cb a) (q a) (muw a) (tau a)) w0 +
        tip615 𝔼 α β θ ω σ sC Φ Ybar (dY u (Ybar, 0))
          (fun t z => tip51 u v Ybar (xu a t z) (xv a t z)) (D a) (G a) (cb a) (q a) (muw a)
          (tau a) w0))
      =O[l] fun a => e a ^ 3 := by
  have hs := tendsto_amp (J := ℕ × Ω) he
  have hβ : |β| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hθ0 : 0 < θ := by linarith
  set Om := LargeDistortions.OmegaW Ybar (dY u (Ybar, 0)) (Moments.calvoKappa α β ω θ σ) θ Φ ω σ
    with hOm
  set gb := LargeDistortions.gbarC θ ω σ Φ with hgb
  set R : A → ℕ → Ω → ℝ := fun a t z =>
    periodUM γ u v θ Ybar (yh a t z) (xu a t z) (xv a t z) -
      (-(Ybar * dY u (Ybar, 0) / 2) * LargeDistortions.quad51 σ ω θ Φ
        (G a t z + sC * cb a t z) (q a t z)
        (logYM γ θ (yh a t z)) (crossVar γ (yh a t z)) +
          tip51 u v Ybar (xu a t z) (xv a t z)) with hR
  have hG' : (fun p : A × (ℕ × Ω) => G p.1 p.2.1 p.2.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 := hGO
  have hcb' : (fun p : A × (ℕ × Ω) => cb p.1 p.2.1 p.2.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 :=
    hcbO
  have hgO : UProc l (fun a t z => G a t z + sC * cb a t z) fun a => e a ^ 1 :=
    hG'.add (hcb'.const_mul_left sC)
  have hRO : UProc l R fun a => e a ^ 3 :=
    eq51_actualM γ (L := l ×ˢ ⊤) (s := fun p : A × (ℕ × Ω) => e p.1) hs hθ.ne' hu hv hucc
      hvy hvyy (yh := fun p => yh p.1 p.2.1 p.2.2) (fun p => hym _ _ _)
      (xu := fun p => xu p.1 p.2.1 p.2.2)
      (xv := fun p => xv p.1 p.2.1 p.2.2)
      (g := fun p => G p.1 p.2.1 p.2.2 + sC * cb p.1 p.2.1 p.2.2)
      (q := fun p => q p.1 p.2.1 p.2.2) hyh hxu hxv hgO hqO (fun p => hg _ _ _)
      (fun p => hq _ _ _)
  have hpO' : (fun p : A × (ℕ × Ω) => pib p.1 p.2.1 p.2.2 - infl p.1 p.2.1 p.2.2)
      =O[l ×ˢ ⊤] fun p => e p.1 ^ 2 := hpO
  have hiO' : (fun p : A × (ℕ × Ω) => infl p.1 p.2.1 p.2.2)
      =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 := hiO
  have hPO : UProc l (fun a t => pib a t ^ 2 - infl a t ^ 2) fun a => e a ^ 3 := by
    have h1 := (o_weaken hs (by norm_num : 1 ≤ 2) hpO').add (hiO'.const_mul_left 2)
    refine (o_mul hpO' h1 (by norm_num : 2 + 1 = 3)).congr_left fun p => ?_
    simp only [Pi.sub_apply, Pi.pow_apply]
    ring
  have hYO := logYM_o γ (L := l ×ˢ ⊤) (s := fun p : A × (ℕ × Ω) => e p.1) hθ.ne'
    (yh := fun p => yh p.1 p.2.1 p.2.2) (fun p => hym _ _ _) hyh
  have hAS := remAS_o 𝔼 he α β θ ω σ sC (Y := fun a t z => logYM γ θ (yh a t z)) hiO hxrO
    hFO hKO hfO hkO hYO hGO hcbO htO
  -- boundedness for amplitudes near `0`
  have bY := bdd_of_o0 (X := fun a t z => logYM γ θ (yh a t z)) he hYO
  have bi := bdd_of_o0 he hiO
  have bF := bdd_of_o0 he hFO
  have bK := bdd_of_o0 he hKO
  have bG := bdd_of_o0 he hGO
  have bcb := bdd_of_o0 he hcbO
  have bq := bdd_of_o0 he hqO
  have bm := bdd_of_o0 he hmO
  have bt := bdd_of_o0 he htO
  have bD := bdd_of_o0 he hDO
  have bp := bdd_of_o0 (X := pib) he
    (((o_weaken hs (by norm_num : 1 ≤ 2) hpO').add hiO').congr_left fun p => by ring)
  have bT := bdd_of_o (X := fun a t z => tip51 u v Ybar (xu a t z) (xv a t z)) he
    (tip51 u v Ybar 0 0) (tip51_o (L := l ×ˢ ⊤) (s := fun p : A × (ℕ × Ω) => e p.1) hs u v Ybar
      (xu := fun p => xu p.1 p.2.1 p.2.2) (xv := fun p => xv p.1 p.2.1 p.2.2) hxu hxv)
  have bR := bdd_of_o0 he hRO
  have hev : ∀ᶠ a in l, Sequences.dsum 𝔼 β
        (fun t z => periodUM γ u v θ Ybar (yh a t z) (xu a t z) (xv a t z)) w0 -
      (W0615 𝔼 α β θ ω σ Φ Ybar (dY u (Ybar, 0)) (infl a) (F a) (K a) w0 -
        LargeDistortions.OmegaTilde Ybar (dY u (Ybar, 0)) α β θ ω σ Φ *
          Sequences.dsum 𝔼 β (LargeDistortions.loss615 α β θ ω σ sC Φ (infl a)
            (fun t z => logYM γ θ (yh a t z)) (G a) (cb a) (q a) (muw a) (tau a)) w0 +
        tip615 𝔼 α β θ ω σ sC Φ Ybar (dY u (Ybar, 0))
          (fun t z => tip51 u v Ybar (xu a t z) (xv a t z)) (D a) (G a) (cb a) (q a) (muw a)
          (tau a) w0) =
      Sequences.dsum 𝔼 β (R a) w0 -
        Om * Sequences.dsum 𝔼 β (fun t => pib a t ^ 2 - infl a t ^ 2) w0 -
        2 * Om * gb * Sequences.dsum 𝔼 β (LargeDistortions.remAS 𝔼 α β θ ω σ sC (infl a) (xr a)
          (F a) (K a) (f a) (k a) (fun t z => logYM γ θ (yh a t z)) (G a) (cb a) (tau a))
          w0 := by
    filter_upwards [bY, bi, bF, bK, bG, bcb, bq, bm, bt, bD, bp, bT, bR] with a hYb hib hFb hKb
      hGb hcbb hqb hmb htb hDb hpb hTb hRb
    have h51 : ∀ t, (fun z => periodUM γ u v θ Ybar (yh a t z) (xu a t z) (xv a t z)) =
        (fun z => -(Ybar * dY u (Ybar, 0) / 2) * LargeDistortions.quad51 σ ω θ Φ
          (G a t z + sC * cb a t z) (q a t z) (logYM γ θ (yh a t z))
          (crossVar γ (yh a t z))) + (fun z => tip51 u v Ybar (xu a t z) (xv a t z)) + R a t := by
      intro t
      funext z
      simp only [Pi.add_apply, hR]
      ring
    have h := LargeDistortions.prop615 𝔼 hα0 hα1 hβ0 hβ1 hθ hω hσ hsC hΦ0 hΦ hMd (hM a) hib hFb
      hKb hYb hGb hcbb hqb hmb htb hDb hpb hTb hRb h51 (hV a) (hD a) w0
    rw [h, ← dsum_sub 𝔼 hβ (Sequences.bdd_sq hpb) (Sequences.bdd_sq hib)]
    unfold W0615 tip615
    ring
  exact (((dsum_o 𝔼 hβ0.le hβ1 hRO w0).sub ((dsum_o 𝔼 hβ0.le hβ1 hPO w0).const_mul_left Om)).sub
    ((dsum_o 𝔼 hβ0.le hβ1 hAS w0).const_mul_left (2 * Om * gb))).congr'
      (hev.mono fun a ha => ha.symm) (Eventually.of_forall fun _ => rfl)

/-! ## The dispersion package from a Calvo population on a goods probability space -/

/-- Woodford (2003), eq. (2.2), p. 392: the log Dixit–Stiglitz price index
`log P = (1 − θ)⁻¹ log ∫ p(i)^{1−θ} dγ` of the log prices `q`. -/
noncomputable def logPM (θ : ℝ) (q : Gs → ℝ) : ℝ := logMeanExp γ (1 - θ) q

/-- An eventual property on `l ×ˢ ⊤` holds eventually for every index. -/
theorem ev_prod_top {J : Type*} {P : A × J → Prop} (h : ∀ᶠ q in l ×ˢ (⊤ : Filter J), P q) :
    ∀ᶠ a in l, ∀ j, P (a, j) := by
  rw [Filter.prod_top, Filter.eventually_comap] at h
  filter_upwards [h] with a ha j
  exact ha (a, j) rfl

/-- Woodford (2003), (2.12), (2.20), Prop. 6.3 and (5.2)–(5.3), pp. 396–399, 456 (**the
dispersion package from a Calvo population on a goods probability space, uniformly in the date
and the state**): with `D_t = var log p_{t−1}`, `π̄_t = P̄_t − P̄_{t−1}` and `π_t` index
inflation, `var ŷ_t = θ²D_{t+1}`, `D_{t+1} = αD_t + α/(1 − α)π̄_t²`, `D = O(ε²)` and
`π̄ − π = O(ε²)`, uniformly — the hypotheses `hV`, `hD`, `hDO`, `hpO` of `prop615_layerBM`. -/
theorem goods_state_packageM (he : Tendsto e l (𝓝 0)) {θ α : ℝ} (hθ0 : θ ≠ 0)
    (hθ1 : θ ≠ 1) (hα1 : α ≠ 1) {yh X : A → ℕ → Ω → Gs → ℝ}
    (hyh : (fun p : (A × (ℕ × Ω)) × Gs => yh p.1.1 p.1.2.1 p.1.2.2 p.2) =O[(l ×ˢ ⊤) ×ˢ ⊤]
      fun p => e p.1.1 ^ 1)
    (hXm : ∀ a t z, Measurable (X a t z)) {Rs : A → Ω → ℕ → Set Gs} {ps : A → Ω → ℕ → ℝ}
    {LY LP : A → ℕ → Ω → ℝ}
    (hG : ∀ a z, Links.GoodsPop.Calvo γ α (fun t => X a t z) (Rs a z) (ps a z) fun _ => 0)
    (hdem : ∀ a t z i, yh a t z i = LY a t z - θ * (X a (t + 1) z i - LP a t z))
    (hX0 : ∃ C0, ∀ᶠ a in l, ∀ z i, |X a 0 z i - crossMean γ (X a 0 z)| ≤ C0 * |e a|) :
    (∀ a t, (fun z => crossVar γ (yh a t z)) = θ ^ 2 • fun z => crossVar γ (X a (t + 1) z)) ∧
    (∀ a t, (fun z => crossVar γ (X a (t + 1) z)) = α • (fun z => crossVar γ (X a t z)) +
      (α / (1 - α)) • (fun z => crossMean γ (X a (t + 1) z) - crossMean γ (X a t z)) ^ 2) ∧
    UProc l (fun a t z => crossVar γ (X a t z)) (fun a => e a ^ 2) ∧
    UProc l (fun a t z => (crossMean γ (X a (t + 1) z) - crossMean γ (X a t z)) -
      (logPM γ θ (X a (t + 1) z) - logPM γ θ (X a t z))) fun a => e a ^ 2 := by
  refine ⟨fun a t => ?_, fun a t => ?_, ?_⟩
  · funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    exact CrossSection.crossVar_demand γ ((hG a z).int1 (t + 1)) (hdem a t z)
  · funext z
    have h := Links.goods_disp_rec γ (hG a z) hα1 t
    simp only [sub_zero] at h
    simp only [Pi.add_apply, Pi.smul_apply, Pi.pow_apply, smul_eq_mul]
    exact h
  -- a uniform bound on relative prices at every date
  obtain ⟨C, hC⟩ := goods_bound (L := l ×ˢ ⊤) (s := fun q : A × (ℕ × Ω) => e q.1) (n := 1)
    (F := fun (q : A × (ℕ × Ω)) i => yh q.1 q.2.1 q.2.2 i) hyh
  have hC' := ev_prod_top hC
  obtain ⟨C0, hC0⟩ := hX0
  set K := 2 * |θ⁻¹| * |C| + |C0| with hK
  have hcen : ∀ᶠ a in l, ∀ t z i, |X a t z i - crossMean γ (X a t z)| ≤ K * |e a| := by
    filter_upwards [hC', hC0] with a ha ha0 t z i
    cases t with
    | zero =>
      have hK0 : C0 ≤ K := by
        rw [hK]; have := abs_nonneg C; have := abs_nonneg θ⁻¹
        nlinarith [le_abs_self C0]
      exact (ha0 z i).trans (mul_le_mul_of_nonneg_right hK0 (abs_nonneg _))
    | succ t =>
      have hy : ∀ j, |yh a t z j| ≤ |C| * |e a| := fun j => by
        have := ha (t, z) j; simp only [pow_one] at this
        exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg _))
      have hint := (hG a z).int1 (t + 1)
      have hmy : crossMean γ (yh a t z) = LY a t z - θ * (crossMean γ (X a (t + 1) z) -
          LP a t z) := by
        have e1 : yh a t z = fun j => (LY a t z + θ * LP a t z) + (-θ) * X a (t + 1) z j := by
          funext j; rw [hdem a t z j]; ring
        rw [e1, CrossSection.crossMean_affine γ hint]; ring
      have hmb : |crossMean γ (yh a t z)| ≤ |C| * |e a| := by
        unfold crossMean
        rw [← Real.norm_eq_abs]
        refine (norm_integral_le_of_norm_le_const (C := |C| * |e a|)
          (Eventually.of_forall fun j => by rw [Real.norm_eq_abs]; exact hy j)).trans ?_
        rw [probReal_univ, mul_one]
      have hxi : X a (t + 1) z i - crossMean γ (X a (t + 1) z) =
          -θ⁻¹ * (yh a t z i - crossMean γ (yh a t z)) := by
        rw [hmy, hdem a t z i]; field_simp; ring
      rw [hxi, abs_mul, abs_neg]
      have h2 : |yh a t z i - crossMean γ (yh a t z)| ≤ 2 * |C| * |e a| := by
        have := abs_sub (yh a t z i) (crossMean γ (yh a t z)); have := hy i; linarith
      calc _ ≤ |θ⁻¹| * (2 * |C| * |e a|) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ ≤ K * |e a| := by
          rw [hK]; have := abs_nonneg C0; have := abs_nonneg (e a)
          nlinarith [abs_nonneg θ⁻¹, abs_nonneg C]
  have hvar : ∀ᶠ a in l, ∀ t z, crossVar γ (X a t z) ≤ (K * |e a|) ^ 2 := by
    filter_upwards [hcen] with a ha t z
    exact (CrossSection.centred_facts γ (hXm a t z) (ha t z) 1).2.2.2.2.2
  set r := (1 : ℝ) - θ with hr
  have hr0 : r ≠ 0 := by rw [hr]; exact sub_ne_zero.2 (Ne.symm hθ1)
  have hsmall : ∀ᶠ a in l, |r| * (K * |e a|) ≤ 1 := by
    have ht : Tendsto (fun a => |r| * (K * |e a|)) l (𝓝 0) := by
      simpa using ((he.abs).const_mul K).const_mul |r|
    exact ht.eventually (ge_mem_nhds one_pos)
  have hlp : ∀ᶠ a in l, ∀ t z, |logPM γ θ (X a t z) - crossMean γ (X a t z)| ≤
      |r| * (K * |e a|) ^ 2 := by
    filter_upwards [hcen, hvar, hsmall] with a ha hv hs t z
    exact (CrossSection.logMeanExp_sub_mean_le γ (hXm a t z) (ha t z) hr0 hs).trans
      (mul_le_mul_of_nonneg_left (hv t z) (abs_nonneg _))
  refine ⟨IsBigO.of_bound (K ^ 2) ?_, IsBigO.of_bound (2 * |r| * K ^ 2) ?_⟩
  · rw [Filter.prod_top, Filter.eventually_comap]
    filter_upwards [hvar] with a ha q hq
    subst hq
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (CrossSection.crossVar_nonneg _ _),
      abs_pow]
    calc _ ≤ (K * |e q.1|) ^ 2 := ha _ _
      _ = _ := by ring
  · rw [Filter.prod_top, Filter.eventually_comap]
    filter_upwards [hlp] with a ha q hq
    subst hq
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
    have h1 := ha (q.2.1 + 1) q.2.2
    have h2 := ha q.2.1 q.2.2
    calc _ ≤ |logPM γ θ (X q.1 q.2.1 q.2.2) - crossMean γ (X q.1 q.2.1 q.2.2)| +
          |logPM γ θ (X q.1 (q.2.1 + 1) q.2.2) - crossMean γ (X q.1 (q.2.1 + 1) q.2.2)| := by
          have := abs_sub (logPM γ θ (X q.1 q.2.1 q.2.2) - crossMean γ (X q.1 q.2.1 q.2.2))
            (logPM γ θ (X q.1 (q.2.1 + 1) q.2.2) - crossMean γ (X q.1 (q.2.1 + 1) q.2.2))
          refine le_trans (le_of_eq ?_) this
          congr 1; ring
      _ ≤ |r| * (K * |e q.1|) ^ 2 + |r| * (K * |e q.1|) ^ 2 := add_le_add h2 h1
      _ = _ := by ring

/-- Woodford (2003), **Proposition 6.15**, (5.5)–(5.8), pp. 458–459, LAYER B FROM A CALVO
POPULATION ON A GOODS PROBABILITY SPACE (`BridgeLinks.prop615_goods_layerB` with the finite
weighted cross-section replaced by an arbitrary probability space of goods): the dispersion
hypotheses are discharged by `goods_state_packageM`; inflation is index inflation of the
Dixit–Stiglitz price index `logPM`. -/
theorem prop615_goods_layerBM
    {α β θ ω σ sC Φ Ybar : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : 1 < θ) (hω : 0 < ω) (hσ : 0 < σ) (hsC : 0 < sC) (hΦ0 : 0 ≤ Φ) (hΦ : Φ < 1)
    (hMd : LargeDistortions.Mden ω σ sC Φ ≠ 0) (he : Tendsto e l (𝓝 0))
    {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u)
    (hv : ContDiff ℝ 3 v)
    (hucc : BridgeExtensions.dYY u (Ybar, 0) = -(σ * BridgeExtensions.dY u (Ybar, 0) / Ybar))
    (hvy : BridgeExtensions.dY v (Ybar, 0) = (1 - Φ) * BridgeExtensions.dY u (Ybar, 0))
    (hvyy : BridgeExtensions.dYY v (Ybar, 0) = ω * BridgeExtensions.dY v (Ybar, 0) / Ybar)
    {yh : A → ℕ → Ω → Gs → ℝ} {xu xv : A → ℕ → Ω → Ξ}
    {xr F K f k G cb q muw tau : A → ℕ → Ω → ℝ} {X : A → ℕ → Ω → Gs → ℝ}
    {Rs : A → Ω → ℕ → Set Gs} {ps : A → Ω → ℕ → ℝ} {LY LP : A → ℕ → Ω → ℝ}
    (hM : ∀ a, LargeDistortions.CalvoModel.CalvoAS 𝔼 α β θ ω σ sC
      (fun t z => logPM γ θ (X a (t + 1) z) - logPM γ θ (X a t z)) (xr a) (F a) (K a) (f a)
      (k a) (fun t z => logYM γ θ (yh a t z)) (G a) (cb a) (q a) (muw a)
      (tau a))
    (hym : ∀ a t z, Measurable (yh a t z)) (hXm : ∀ a t z, Measurable (X a t z))
    (hyh : (fun p : (A × (ℕ × Ω)) × Gs => yh p.1.1 p.1.2.1 p.1.2.2 p.2) =O[(l ×ˢ ⊤) ×ˢ ⊤]
      fun p => e p.1.1 ^ 1)
    (hxu : BridgeExtensions.UProc l xu fun a => e a ^ 1)
    (hxv : BridgeExtensions.UProc l xv fun a => e a ^ 1)
    (hiO : BridgeExtensions.UProc l (fun a t z => logPM γ θ (X a (t + 1) z) -
      logPM γ θ (X a t z)) fun a => e a ^ 1)
    (hxrO : BridgeExtensions.UProc l xr fun a => e a ^ 1)
    (hFO : BridgeExtensions.UProc l F fun a => e a ^ 1)
    (hKO : BridgeExtensions.UProc l K fun a => e a ^ 1)
    (hfO : BridgeExtensions.UProc l f fun a => e a ^ 1)
    (hkO : BridgeExtensions.UProc l k fun a => e a ^ 1)
    (hGO : BridgeExtensions.UProc l G fun a => e a ^ 1)
    (hcbO : BridgeExtensions.UProc l cb fun a => e a ^ 1)
    (hqO : BridgeExtensions.UProc l q fun a => e a ^ 1)
    (hmO : BridgeExtensions.UProc l muw fun a => e a ^ 1)
    (htO : BridgeExtensions.UProc l tau fun a => e a ^ 1)
    (hg : ∀ a t z, BridgeExtensions.dYXi u (Ybar, 0) (xu a t z) =
      σ * BridgeExtensions.dY u (Ybar, 0) * (G a t z + sC * cb a t z))
    (hq : ∀ a t z, BridgeExtensions.dYXi v (Ybar, 0) (xv a t z) =
      -(ω * BridgeExtensions.dY v (Ybar, 0) * q a t z))
    (hG : ∀ a z, Links.GoodsPop.Calvo γ α (fun t => X a t z) (Rs a z) (ps a z)
      fun _ => 0)
    (hdem : ∀ a t z i, yh a t z i = LY a t z - θ * (X a (t + 1) z i - LP a t z))
    (hX0 : ∃ C0, ∀ᶠ a in l, ∀ z i, |X a 0 z i - crossMean γ (X a 0 z)| ≤ C0 * |e a|)
    (w0 : Ω) :
    (fun a => Sequences.dsum 𝔼 β
        (fun t z => periodUM γ u v θ Ybar (yh a t z) (xu a t z) (xv a t z)) w0 -
      (BridgeExtensions.W0615 𝔼 α β θ ω σ Φ Ybar (BridgeExtensions.dY u (Ybar, 0))
          (fun t z => logPM γ θ (X a (t + 1) z) - logPM γ θ (X a t z)) (F a) (K a) w0 -
        LargeDistortions.OmegaTilde Ybar (BridgeExtensions.dY u (Ybar, 0)) α β θ ω σ Φ *
          Sequences.dsum 𝔼 β (LargeDistortions.loss615 α β θ ω σ sC Φ
            (fun t z => logPM γ θ (X a (t + 1) z) - logPM γ θ (X a t z))
            (fun t z => logYM γ θ (yh a t z)) (G a) (cb a) (q a) (muw a)
            (tau a)) w0 +
        BridgeExtensions.tip615 𝔼 α β θ ω σ sC Φ Ybar (BridgeExtensions.dY u (Ybar, 0))
          (fun t z => BridgeExtensions.tip51 u v Ybar (xu a t z) (xv a t z))
          (fun t z => crossVar γ (X a t z)) (G a) (cb a) (q a) (muw a) (tau a) w0))
      =O[l] fun a => e a ^ 3 := by
  obtain ⟨hV, hD, hDO, hpO⟩ :=
    goods_state_packageM γ he (by linarith) hθ.ne' hα1.ne hyh hXm hG hdem hX0
  exact prop615_layerBM γ 𝔼 hα0 hα1 hβ0 hβ1 hθ hω hσ hsC hΦ0 hΦ hMd he hu hv hucc hvy hvyy hM
    hym hyh hxu hxv hiO hxrO hFO hKO hfO hkO hGO hcbO hqO hmO htO hpO hDO hg hq hV hD w0

/-! ## The finite weighted cross-section is the special case -/

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Woodford (2003), App. E.2, p. 695: over `BridgeLinks.wMeasure w` the log-mean-exp is the
finite cumulant. -/
theorem logMeanExp_wMeasure {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (r : ℝ) (y : ι → ℝ) :
    logMeanExp (BridgeLinks.wMeasure w) r y = ExpLogCES.cumulant w r y := by
  unfold logMeanExp ExpLogCES.cumulant ExpLogCES.cesMoment
  rw [BridgeLinks.integral_wMeasure hw]
  ring

/-- Woodford (2003), (2.6): over `wMeasure w` the output index is `BridgeExtensions.logYidx`. -/
theorem logYM_wMeasure {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (θ : ℝ)
    (yh : ι → ℝ) : logYM (BridgeLinks.wMeasure w) θ yh = BridgeExtensions.logYidx w θ yh := by
  unfold logYM BridgeExtensions.logYidx
  rw [logMeanExp_wMeasure hw, ExpLogCES.log_cesIndex_exp hw hw1]

/-- Woodford (2003), (2.2): over `wMeasure w` the price index is `BridgeLinks.logP`. -/
theorem logPM_wMeasure {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (θ : ℝ)
    (q : ι → ℝ) : logPM (BridgeLinks.wMeasure w) θ q = BridgeLinks.logP w θ q := by
  unfold logPM BridgeLinks.logP
  rw [logMeanExp_wMeasure hw, ExpLogCES.log_cesIndex_exp hw hw1]

/-- Woodford (2003), (2.1): over `wMeasure w` the period utility is `BridgeExtensions.periodU`. -/
theorem periodUM_wMeasure {Ξ' : Type*} {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (u v : ℝ × Ξ' → ℝ) (θ Ybar : ℝ) (yh : ι → ℝ) (xu xv : Ξ') :
    periodUM (BridgeLinks.wMeasure w) u v θ Ybar yh xu xv =
      BridgeExtensions.periodU u v w θ Ybar yh xu xv := by
  unfold periodUM BridgeExtensions.periodU
  rw [logYM_wMeasure hw hw1, BridgeLinks.integral_wMeasure hw]

/-- Woodford (2003), App. E.2, p. 695 (**the finite cross-section is the special case**): with
`γ = wMeasure w` the cross-sectional objects of this module are those of
`BridgeExtensions`/`BridgeLinks` — the output index, the price index, the period utility, the
mean and the variance — so `prop615_goods_layerBM` at `γ = wMeasure w` is a statement about the
finite weighted cross-section. -/
theorem special_case {Ξ' : Type*} {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (u v : ℝ × Ξ' → ℝ) (θ Ybar : ℝ) (yh q : ι → ℝ) (xu xv : Ξ') :
    IsProbabilityMeasure (BridgeLinks.wMeasure w) ∧
      logYM (BridgeLinks.wMeasure w) θ yh = BridgeExtensions.logYidx w θ yh ∧
      logPM (BridgeLinks.wMeasure w) θ q = BridgeLinks.logP w θ q ∧
      periodUM (BridgeLinks.wMeasure w) u v θ Ybar yh xu xv =
        BridgeExtensions.periodU u v w θ Ybar yh xu xv ∧
      crossMean (BridgeLinks.wMeasure w) q = ExpLogCES.crossMean w q ∧
      crossVar (BridgeLinks.wMeasure w) q = ExpLogCES.crossVar w q :=
  ⟨BridgeLinks.isProbabilityMeasure_wMeasure hw hw1, logYM_wMeasure hw hw1 θ yh,
    logPM_wMeasure hw hw1 θ q, periodUM_wMeasure hw hw1 u v θ Ybar yh xu xv,
    BridgeLinks.crossMean_wMeasure hw q, BridgeLinks.crossVar_wMeasure hw q⟩


end Woodford.StabilizationWelfare.NonlinearNKMarkovGoodsLayerB
