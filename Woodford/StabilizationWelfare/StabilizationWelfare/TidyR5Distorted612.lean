/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR5Distorted610

/-!
# Proposition 6.12 expanded around the distorted steady state

Woodford (2003), *Interest and Prices*, Chapter 6, §4.4, Proposition 6.12, (4.28), p. 444, and
Appendix E.8, (E.33)–(E.36), pp. 707–708, with the steady-state relation
`v_h = (1 − Φ)u_c f′(H̄)` of (E.33) and `x* = Φ/(σ⁻¹ + ω) + O(Φ²)` of (2.17), p. 399.

`BridgeExtensions.prop612_actual` expands the actual sticky-wage utility around the EFFICIENT
steady state `(Y*, H*)`. Here the expansion point is the DISTORTED steady state. The labour
requirement of a good producing `Y*e^{z}` (at `a = 0`) is `H*G(z)`; normalised at
`Ȳ = Y*e^{c}` it is `H̄G_c(z)` with `H̄ = H*G(c)` and `G_c(z) = G(z + c)/G(c)`, and
`φ_h(Ȳ) = G′(c)/G(c)` is the elasticity `Ȳ/(H̄f′(H̄))`. The distorted steady state is
`H̄v_h(H̄)φ_h(Ȳ) = (1 − Φ)Ȳu_c(Ȳ)`.

* `periodU12_shift`: the actual utility is the same function of actual outputs and labour,
  whichever steady state the deviations are measured from.
* **`distorted_ss612`**: along a branch `Ȳ_b → Y*` with `Φ_b = O(ε)`,
  `log(Ȳ_b/Y*) = −x*_b + O(ε²)`.
* **`prop612_distorted`**, **`prop612_distorted_layerB`**: Proposition 6.12 around the distorted
  steady state, with target `Ŷ − Ŷⁿ − x*`.
-/

namespace Woodford.StabilizationWelfare.TidyR5Distorted612

open Filter Topology Asymptotics
open BridgeExtensions TidyR5DistortedTools TidyR5Distorted610
open ExpLogCES (crossVar)

variable {B : Type*} {L : Filter B} {s : B → ℝ}
variable {Ξ : Type*}
variable {ι : Type*} [Fintype ι] {J : Type*} [Fintype J]

/-! ## Changing the reference output and labour -/

/-- Woodford (2003), (E.36), p. 708: renormalising the labour requirement at `Ȳ = Y*e^{c}`
(`G_c(z) = G(z + c)/G(c)`) changes the log labour index by the constant `−log G(c)`. -/
theorem logHidx_shift {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {G : ℝ → ℝ}
    (hGpos : ∀ z, 0 < G z) (a c : ℝ) (yd : ι → ℝ) :
    logHidx w (fun z => G (z + c) / G c) a yd =
      logHidx w G a (fun i => yd i + c) - Real.log (G c) := by
  have hS : 0 < ∑ i, w i * G (yd i + c - a) := by
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hw1]; exact one_ne_zero)
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hw0 j) (hGpos _).le)
      ⟨i, Finset.mem_univ i, mul_pos (lt_of_le_of_ne (hw0 i) (Ne.symm hi)) (hGpos _)⟩
  unfold logHidx
  have e : ∑ i, w i * (G (yd i - a + c) / G c) = (∑ i, w i * G (yd i + c - a)) / G c := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show yd i - a + c = yd i + c - a by ring]
    ring
  rw [e, Real.log_div hS.ne' (hGpos c).ne']

/-- Woodford (2003), §4.4, (4.27), p. 444 (**the actual utility does not depend on the
reference point**): the sticky-wage period utility with outputs `Ȳe^{ŷ(i)}` and labour
requirement `H̄G_c` (`Ȳ = Y*e^{c}`, `H̄ = H*G(c)`) equals the one with reference `(Y*, H*, G)`
and log deviations `ŷ(i) + c`. -/
theorem periodU12_shift {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (ωt : J → ℝ)
    {θp : ℝ} (hθp1 : θp ≠ 1) (θw : ℝ) (u v : ℝ × Ξ → ℝ) {Ys Yb : ℝ} (hYs : 0 < Ys)
    (hYb : 0 < Yb) (Hs : ℝ) {G : ℝ → ℝ} (hGpos : ∀ z, 0 < G z) (a : ℝ) (yd : ι → ℝ)
    (lw : J → ℝ) (xu xv : Ξ) :
    periodU12 u v w ωt θp θw Ys Hs G a (fun i => yd i + Real.log (Yb / Ys)) lw xu xv =
      periodU12 u v w ωt θp θw Yb (Hs * G (Real.log (Yb / Ys)))
        (fun z => G (z + Real.log (Yb / Ys)) / G (Real.log (Yb / Ys))) a yd lw xu xv := by
  set c := Real.log (Yb / Ys) with hc
  have hy : Ys * Real.exp (logYidx w θp yd + c) = Yb * Real.exp (logYidx w θp yd) := by
    rw [Real.exp_add, hc, Real.exp_log (div_pos hYb hYs)]
    field_simp
  unfold periodU12
  rw [logYidx_shift hw0 hw1 hθp1, hy, logHidx_shift hw0 hw1 hGpos]
  have e : ∀ x y : ℝ, Hs * G c * Real.exp (x - Real.log (G c) - y) = Hs * Real.exp (x - y) := by
    intro x y
    rw [show x - Real.log (G c) - y = (x - y) - Real.log (G c) by ring, Real.exp_sub,
      Real.exp_log (hGpos c)]
    field_simp [(hGpos c).ne']
  simp only [e]

/-! ## The distorted steady state -/

variable [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]

/-- Woodford (2003), (E.33), p. 707 and (2.17), p. 399 (**the distorted steady state of the
sticky-wage model**): with `σ⁻¹ = −Y*u_cc/u_c`, `ν = H*v_hh/v_h`, `G(0) = 1`, `G′(0) = φ_h`,
`G″(0) = φ_h(1 + ω_p)`, `ω = ω_p + νφ_h` and the efficient steady state `H*v_hφ_h = Y*u_c`, a
branch `Ȳ_b → Y*` of distorted steady states `H̄v_h(H̄)φ_h(Ȳ) = (1 − Φ_b)Ȳu_c(Ȳ)` (`H̄ = H*G(c)`,
`φ_h(Ȳ) = G′(c)/G(c)`, `c = log(Ȳ/Y*)`) with `Φ_b = O(ε)` has `c_b = O(ε)` and
`c_b + x*_b = O(ε²)`, `x*_b = Φ_b/(σ⁻¹ + ω)`. -/
theorem distorted_ss612 {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 3 G) (hG0 : G 0 = 1)
    (hGpos : ∀ z, 0 < G z) {σi ω ν ωp φh Ys Hs : ℝ}
    (hG1 : fderiv ℝ G 0 1 = φh) (hG2 : fderiv ℝ (fderiv ℝ G) 0 1 1 = φh * (1 + ωp))
    (hω : ω = ωp + ν * φh) (hσω : σi + ω ≠ 0) (hYs : 0 < Ys) (huc : dY u (Ys, 0) ≠ 0)
    (hucc : dYY u (Ys, 0) = -(σi * dY u (Ys, 0) / Ys))
    (hvhh : dYY v (Hs, 0) = ν * dY v (Hs, 0) / Hs)
    (hss : Hs * dY v (Hs, 0) * φh = Ys * dY u (Ys, 0))
    {Yb Phi : B → ℝ} (hYb0 : ∀ b, 0 < Yb b) (hYb : Tendsto Yb L (𝓝 Ys))
    (hFOC : ∀ b, Hs * G (Real.log (Yb b / Ys)) * dY v (Hs * G (Real.log (Yb b / Ys)), 0) *
      (deriv G (Real.log (Yb b / Ys)) / G (Real.log (Yb b / Ys))) =
        (1 - Phi b) * Yb b * dY u (Yb b, 0))
    (hPhi : Phi =O[L] fun b => s b ^ 1) :
    (fun b => Real.log (Yb b / Ys)) =O[L] (fun b => s b ^ 1) ∧
      (fun b => Real.log (Yb b / Ys) + Prop61.xStarLin σi ω (Phi b)) =O[L]
        fun b => s b ^ 2 := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by norm_num)
  set K := Ys * dY u (Ys, 0) with hK
  have hK0 : K ≠ 0 := mul_ne_zero hYs.ne' huc
  set κ := K * (σi + ω) with hκd
  have hκ : κ ≠ 0 := mul_ne_zero hK0 hσω
  -- the pieces of `h(c) = H*v_h(H*G(c))G′(c) − Y*e^{c}u_c(Y*e^{c})`
  have hP : HasDerivAt (fun c => Hs * G c) (Hs * φh) 0 := by
    have := ((hG.differentiable (by norm_num) 0).hasDerivAt).const_mul Hs
    rw [← hG1]
    exact this
  have hV : HasDerivAt (fun c => dY v (Hs * G c, 0)) (dYY v (Hs, 0) * (Hs * φh)) 0 := by
    have h := (hasDerivAt_dY hv2 (Hs * G 0)).comp 0 hP
    rw [hG0, mul_one] at h
    exact h
  have hGd : ContDiff ℝ 2 (fun c => fderiv ℝ G c 1) :=
    (hG.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
  have hD : HasDerivAt (fun c => deriv G c) (φh * (1 + ωp)) 0 := by
    have h1 : ContDiff ℝ 1 (fderiv ℝ G) := hG.fderiv_right (m := 1) (by norm_num)
    have hF : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) 0) 0 :=
      (h1.differentiable (by norm_num) 0).hasFDerivAt
    have h := (((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).hasFDerivAt).comp 0 hF).hasDerivAt
    rw [← hG2]
    exact h
  have hE : HasDerivAt (fun c => Ys * Real.exp c) Ys 0 := by
    have := (Real.hasDerivAt_exp 0).const_mul Ys
    rwa [Real.exp_zero, mul_one] at this
  have hUc : HasDerivAt (fun c => dY u (Ys * Real.exp c, 0)) (dYY u (Ys, 0) * Ys) 0 := by
    have h := (hasDerivAt_dY hu2 (Ys * Real.exp 0)).comp 0 hE
    rw [Real.exp_zero, mul_one] at h
    exact h
  have hH : HasDerivAt (fun c => Hs * dY v (Hs * G c, 0) * deriv G c -
      Ys * Real.exp c * dY u (Ys * Real.exp c, 0)) κ 0 := by
    have h := ((hV.const_mul Hs).mul hD).sub (hE.mul hUc)
    convert h using 1
    have e1 : deriv G 0 = φh := hG1
    have hHs : Hs ≠ 0 := by
      rintro rfl
      apply hK0
      rw [← hss]
      ring
    have ev : Hs * (dYY v (Hs, 0) * (Hs * φh)) * φh = ν * φh * (Hs * dY v (Hs, 0) * φh) := by
      rw [hvhh]
      field_simp
    have eu : Ys * (dYY u (Ys, 0) * Ys) = -(σi * (Ys * dY u (Ys, 0))) := by
      rw [hucc]
      field_simp
    simp only [hG0, mul_one, Real.exp_zero, e1]
    rw [ev, eu, hκd, hK, hω]
    linear_combination (-(ν * φh + 1 + ωp)) * hss
  have hh : ContDiffAt ℝ 2 (fun c => Hs * dY v (Hs * G c, 0) * deriv G c -
      Ys * Real.exp c * dY u (Ys * Real.exp c, 0)) 0 := by
    have hc1 : ContDiff ℝ 2 (fun c => dY v (Hs * G c, 0)) :=
      (contDiff_dY hv).comp (contDiff_const.mul (hG.of_le (by norm_num)))
    have hc2 : ContDiff ℝ 2 (fun c => Ys * Real.exp c) := contDiff_const.mul Real.contDiff_exp
    have hc3 : ContDiff ℝ 2 (fun c => dY u (Ys * Real.exp c, 0)) := (contDiff_dY hu).comp hc2
    exact (((contDiff_const.mul hc1).mul hGd).sub (hc2.mul hc3)).contDiffAt
  have hk : DifferentiableAt ℝ (fun c => Ys * Real.exp c * dY u (Ys * Real.exp c, 0)) 0 :=
    (hE.mul hUc).differentiableAt
  have hc0 : Tendsto (fun b => Real.log (Yb b / Ys)) L (𝓝 0) := by
    have h := ((Real.continuousAt_log (by positivity : Ys / Ys ≠ 0)).tendsto).comp
      (hYb.div_const Ys)
    rwa [div_self hYs.ne', Real.log_one] at h
  have hYe : ∀ b, Ys * Real.exp (Real.log (Yb b / Ys)) = Yb b := fun b => by
    rw [Real.exp_log (div_pos (hYb0 b) hYs)]
    field_simp
  obtain ⟨h1, h2⟩ := ss_first_order hh hH.deriv hκ
    (by simp only [hG0, mul_one, Real.exp_zero]; have e1 : deriv G 0 = φh := hG1
        rw [e1, hss]; ring) hk hc0
    (fun b => by
      have hGc := (hGpos (Real.log (Yb b / Ys))).ne'
      have hf := hFOC b
      have e : Hs * G (Real.log (Yb b / Ys)) * dY v (Hs * G (Real.log (Yb b / Ys)), 0) *
          (deriv G (Real.log (Yb b / Ys)) / G (Real.log (Yb b / Ys))) =
          Hs * dY v (Hs * G (Real.log (Yb b / Ys)), 0) * deriv G (Real.log (Yb b / Ys)) := by
        field_simp
      rw [e] at hf
      simp only [hYe b]
      linear_combination hf) hPhi
  refine ⟨h1.congr_left fun b => by rw [sub_zero],
    (h2.const_mul_left κ⁻¹).congr_left fun b => ?_⟩
  simp only [Real.exp_zero, mul_one, sub_zero, Prop61.xStarLin, hκd, hK]
  field_simp

/-! ## Proposition 6.12 around the distorted steady state -/

/-- Woodford (2003), (4.28)/(E.33) with `Φ > 0`: the quadratic form of Proposition 6.12 around
the distorted steady state, `(σ⁻¹ + ω)(Ŷ − Ŷⁿ − x*)² + θ_p(1 + ω_pθ_p)V_p +
θ_wφ_h⁻¹(1 + νθ_w)V_w`, `x* = Φ/(σ⁻¹ + ω)` (the form of
`StickyWageWelfare.prop_6_12_layerA`). -/
noncomputable def loss612Phi (σi ω ν θp ωp θw φh Phi g a hb Y Vp Vw : ℝ) : ℝ :=
  loss612 σi ω ν θp ωp θw φh g a hb (Y - Prop61.xStarLin σi ω Phi) Vp Vw

/-- **Woodford (2003), Proposition 6.12, (4.28)/(E.33), pp. 444, 707–708, expanded around the
DISTORTED steady state.** Under the hypotheses of `prop612_actual` at the efficient point
`(Y*, H*, G)`, with `G > 0` and a branch of distorted steady states `Ȳ_b → Y*`
(`distorted_ss612`, `Φ_b = O(ε)`), measure outputs relative to `Ȳ_b` (`y(i) = Ȳ_b e^{ŷ(i)}`)
and labour relative to `H̄_b = H*G(c_b)` with the renormalised requirement
`G_b(z) = G(z + c_b)/G(c_b)`, `c_b = log(Ȳ_b/Y*)`. Then the actual period utility is
`t.i.p. − ½Y*u_c·loss612Φ + O(ε³)`, with target `Ŷ − Ŷⁿ − x*` (`Ŷ` the index of the
distorted-steady-state deviations), `x* = Φ/(σ⁻¹ + ω)`, and the coefficients and disturbances of
the efficient point. -/
theorem prop612_distorted (hs : Tendsto s L (𝓝 0)) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {ωt : J → ℝ} (hωt0 : ∀ j, 0 ≤ ωt j) (hωt1 : ∑ j, ωt j = 1)
    {θp θw : ℝ} (hθp : θp ≠ 0) (hθp1 : θp ≠ 1) (hθw1 : θw ≠ 1)
    {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 3 G) (hG0 : G 0 = 1) (hGpos : ∀ z, 0 < G z)
    {σi ω ν ωp φh Ys Hs : ℝ}
    (hG1 : fderiv ℝ G 0 1 = φh) (hG2 : fderiv ℝ (fderiv ℝ G) 0 1 1 = φh * (1 + ωp))
    (hω : ω = ωp + ν * φh) (hφ : φh ≠ 0) (hσω : σi + ω ≠ 0) (hYs : 0 < Ys)
    (huc : dY u (Ys, 0) ≠ 0) (hucc : dYY u (Ys, 0) = -(σi * dY u (Ys, 0) / Ys))
    (hvhh : dYY v (Hs, 0) = ν * dY v (Hs, 0) / Hs)
    (hss : Hs * dY v (Hs, 0) * φh = Ys * dY u (Ys, 0))
    {Yb Phi : B → ℝ} (hYb0 : ∀ b, 0 < Yb b) (hYb : Tendsto Yb L (𝓝 Ys))
    (hFOC : ∀ b, Hs * G (Real.log (Yb b / Ys)) * dY v (Hs * G (Real.log (Yb b / Ys)), 0) *
      (deriv G (Real.log (Yb b / Ys)) / G (Real.log (Yb b / Ys))) =
        (1 - Phi b) * Yb b * dY u (Yb b, 0))
    (hPhi : Phi =O[L] fun b => s b ^ 1)
    {yd : B → ι → ℝ} {lw : B → J → ℝ} {a g hb : B → ℝ} {xu xv : B → Ξ}
    (hg : ∀ b, dYXi u (Ys, 0) (xu b) = σi * dY u (Ys, 0) * g b)
    (hhb : ∀ b, dYXi v (Hs, 0) (xv b) = -(ν * dY v (Hs, 0) * hb b))
    (hyd : yd =O[L] fun b => s b ^ 1) (hlw : lw =O[L] fun b => s b ^ 1)
    (ha : a =O[L] fun b => s b ^ 1) (hgO : g =O[L] fun b => s b ^ 1)
    (hhbO : hb =O[L] fun b => s b ^ 1) (hxu : xu =O[L] fun b => s b ^ 1)
    (hxv : xv =O[L] fun b => s b ^ 1) :
    (fun b => periodU12 u v w ωt θp θw (Yb b) (Hs * G (Real.log (Yb b / Ys)))
        (fun z => G (z + Real.log (Yb b / Ys)) / G (Real.log (Yb b / Ys))) (a b) (yd b) (lw b)
        (xu b) (xv b) -
      (tip12 u v Ys Hs (xu b) (xv b) + Ys * dY u (Ys, 0) *
        (StickyWageWelfare.tip612 σi ω ν 0 (g b) (a b) (hb b) -
          loss612Phi σi ω ν θp ωp θw φh (Phi b) (g b) (a b) (hb b) (logYidx w θp (yd b))
            (crossVar w (yd b) / θp ^ 2) (crossVar ωt (lw b)) / 2))) =O[L] fun b => s b ^ 3 := by
  obtain ⟨hc, hcx⟩ := distorted_ss612 hu hv hG hG0 hGpos hG1 hG2 hω hσω hYs huc hucc hvhh
    hss hYb0 hYb hFOC hPhi
  set c := fun b => Real.log (Yb b / Ys) with hcd
  have he : (fun b => fun i => yd b i + c b) =O[L] fun b => s b ^ 1 :=
    isBigO_pi.2 fun i => (coord_o hyd i).add hc
  have hW := prop612_actual hs hw0 hw1 hωt0 hωt1 hθp hθp1 hθw1 hu hv hG hG0 hG1 hG2 hω hφ hσω
    hucc hvhh hss hg hhb he hlw ha hgO hhbO hxu hxv
  have hYO : (fun b => logYidx w θp (yd b)) =O[L] fun b => s b ^ 1 :=
    logYidx_o hs hw0 hw1 hθp1 hyd
  have hnat : (fun b => StickyWageWelfare.natY612 σi ω ν (g b) (a b) (hb b))
      =O[L] fun b => s b ^ 1 :=
    ((((hgO.const_mul_left σi).add (ha.const_mul_left (1 + ω))).add
      (hhbO.const_mul_left ν)).const_mul_left (σi + ω)⁻¹).congr_left
        fun b => by unfold StickyWageWelfare.natY612; ring
  have hx : (fun b => Prop61.xStarLin σi ω (Phi b)) =O[L] fun b => s b ^ 1 :=
    (hPhi.const_mul_left (σi + ω)⁻¹).congr_left fun b => by
      simp only [Prop61.xStarLin]; ring
  have hgap : (fun b => 2 * (logYidx w θp (yd b) -
      StickyWageWelfare.natY612 σi ω ν (g b) (a b) (hb b)) + c b -
        Prop61.xStarLin σi ω (Phi b)) =O[L] fun b => s b ^ 1 :=
    ((((hYO.sub hnat).const_mul_left 2).add hc).sub hx)
  have hdiff := (o_mul hcx hgap (by norm_num : 2 + 1 = 3)).const_mul_left
    (Ys * dY u (Ys, 0) * (σi + ω) / 2)
  refine (hW.sub hdiff).congr_left fun b => ?_
  have s1 := logYidx_shift hw0 hw1 hθp1 (c b) (yd b)
  have v1 : crossVar w (fun i => yd b i + c b) = crossVar w (yd b) := by
    rw [← ExpLogCES.crossVar_const_add hw1 (c b) (yd b)]
    congr 1
    funext i
    ring
  have pU := periodU12_shift hw0 hw1 ωt hθp1 θw u v hYs (hYb0 b) Hs hGpos (a b) (yd b) (lw b)
    (xu b) (xv b)
  simp only [hcd] at s1 v1 ⊢
  rw [pU, s1, v1]
  simp only [loss612Phi, loss612]
  ring

/-- **Woodford (2003), Proposition 6.12, (4.28)/(E.33), LAYER B around the distorted steady
state**: under the hypotheses of `prop612_distorted`, if the family has a first-order solution
(`Φ = εΦ¹ + O(ε²)`, `ŷ = εŷ¹ + O(ε²)`, `lw = εlw¹ + O(ε²)`, `Ŷ, g, a, h̄ = ε × first order +
O(ε²)`, all first-order objects bounded), then
`W(ε) = t.i.p.(ε) − (ε²/2)·Y*u_c·loss612Φ(first-order solution) + O(ε³)`. -/
theorem prop612_distorted_layerB (hs : Tendsto s L (𝓝 0)) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {ωt : J → ℝ} (hωt0 : ∀ j, 0 ≤ ωt j) (hωt1 : ∑ j, ωt j = 1)
    {θp θw : ℝ} (hθp : θp ≠ 0) (hθp1 : θp ≠ 1) (hθw1 : θw ≠ 1)
    {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 3 G) (hG0 : G 0 = 1) (hGpos : ∀ z, 0 < G z)
    {σi ω ν ωp φh Ys Hs : ℝ}
    (hG1 : fderiv ℝ G 0 1 = φh) (hG2 : fderiv ℝ (fderiv ℝ G) 0 1 1 = φh * (1 + ωp))
    (hω : ω = ωp + ν * φh) (hφ : φh ≠ 0) (hσω : σi + ω ≠ 0) (hYs : 0 < Ys)
    (huc : dY u (Ys, 0) ≠ 0) (hucc : dYY u (Ys, 0) = -(σi * dY u (Ys, 0) / Ys))
    (hvhh : dYY v (Hs, 0) = ν * dY v (Hs, 0) / Hs)
    (hss : Hs * dY v (Hs, 0) * φh = Ys * dY u (Ys, 0))
    {Yb Phi : B → ℝ} (hYb0 : ∀ b, 0 < Yb b) (hYb : Tendsto Yb L (𝓝 Ys))
    (hFOC : ∀ b, Hs * G (Real.log (Yb b / Ys)) * dY v (Hs * G (Real.log (Yb b / Ys)), 0) *
      (deriv G (Real.log (Yb b / Ys)) / G (Real.log (Yb b / Ys))) =
        (1 - Phi b) * Yb b * dY u (Yb b, 0))
    {yd y1 : B → ι → ℝ} {lw lw1 : B → J → ℝ} {a g hb Phif af gf hbf Yf : B → ℝ}
    {xu xv : B → Ξ}
    (hg : ∀ b, dYXi u (Ys, 0) (xu b) = σi * dY u (Ys, 0) * g b)
    (hhb : ∀ b, dYXi v (Hs, 0) (xv b) = -(ν * dY v (Hs, 0) * hb b))
    (hyd : yd =O[L] fun b => s b ^ 1) (hlw : lw =O[L] fun b => s b ^ 1)
    (hxu : xu =O[L] fun b => s b ^ 1) (hxv : xv =O[L] fun b => s b ^ 1)
    (by1 : y1 =O[L] fun _ => (1 : ℝ)) (blw1 : lw1 =O[L] fun _ => (1 : ℝ))
    (bPhi : Phif =O[L] fun _ => (1 : ℝ))
    (ba : af =O[L] fun _ => (1 : ℝ)) (bg : gf =O[L] fun _ => (1 : ℝ))
    (bhb : hbf =O[L] fun _ => (1 : ℝ)) (bY : Yf =O[L] fun _ => (1 : ℝ))
    (hydd : (fun b => yd b - s b • y1 b) =O[L] fun b => s b ^ 2)
    (hlwd : (fun b => lw b - s b • lw1 b) =O[L] fun b => s b ^ 2)
    (hPhid : (fun b => Phi b - s b * Phif b) =O[L] fun b => s b ^ 2)
    (had : (fun b => a b - s b * af b) =O[L] fun b => s b ^ 2)
    (hgd : (fun b => g b - s b * gf b) =O[L] fun b => s b ^ 2)
    (hhbd : (fun b => hb b - s b * hbf b) =O[L] fun b => s b ^ 2)
    (hYd : (fun b => logYidx w θp (yd b) - s b * Yf b) =O[L] fun b => s b ^ 2) :
    (fun b => periodU12 u v w ωt θp θw (Yb b) (Hs * G (Real.log (Yb b / Ys)))
        (fun z => G (z + Real.log (Yb b / Ys)) / G (Real.log (Yb b / Ys))) (a b) (yd b) (lw b)
        (xu b) (xv b) -
      ((tip12 u v Ys Hs (xu b) (xv b) + Ys * dY u (Ys, 0) *
        StickyWageWelfare.tip612 σi ω ν 0 (g b) (a b) (hb b)) -
        s b ^ 2 / 2 * (Ys * dY u (Ys, 0) * loss612Phi σi ω ν θp ωp θw φh (Phif b) (gf b) (af b)
          (hbf b) (Yf b) (crossVar w (y1 b) / θp ^ 2) (crossVar ωt (lw1 b)))))
      =O[L] fun b => s b ^ 3 := by
  have fo : ∀ (x x1 : B → ℝ), (fun b => x b - s b * x1 b) =O[L] (fun b => s b ^ 2) →
      x1 =O[L] (fun _ => (1 : ℝ)) → x =O[L] fun b => s b ^ 1 := fun x x1 hd h1 =>
    ((o_weaken hs (by norm_num : 1 ≤ 2) hd).add
      (((isBigO_refl s L).mul h1).congr_right fun b => by ring)).congr_left fun b => by ring
  have hW := prop612_distorted hs hw0 hw1 hωt0 hωt1 hθp hθp1 hθw1 hu hv hG hG0 hGpos hG1 hG2 hω
    hφ hσω hYs huc hucc hvhh hss hYb0 hYb hFOC (fo Phi Phif hPhid bPhi) hg hhb hyd hlw
    (fo a af had ba) (fo g gf hgd bg) (fo hb hbf hhbd bhb) hxu hxv
  have hVp : (fun b => crossVar w (yd b) / θp ^ 2 - s b ^ 2 * (crossVar w (y1 b) / θp ^ 2))
      =O[L] fun b => s b ^ 3 :=
    ((crossVar_first_order hs hw0 hw1 hydd by1).const_mul_left (θp ^ 2)⁻¹).congr_left
      fun b => by ring
  have hYx : (fun b => (logYidx w θp (yd b) - Prop61.xStarLin σi ω (Phi b)) -
      s b * (Yf b - Prop61.xStarLin σi ω (Phif b))) =O[L] fun b => s b ^ 2 :=
    (hYd.sub (hPhid.const_mul_left (σi + ω)⁻¹)).congr_left fun b => by
      simp only [Prop61.xStarLin]; ring
  have bYx : (fun b => Yf b - Prop61.xStarLin σi ω (Phif b)) =O[L] fun _ => (1 : ℝ) :=
    (bY.sub (bPhi.const_mul_left (σi + ω)⁻¹)).congr_left fun b => by
      simp only [Prop61.xStarLin]; ring
  have hL := loss612_first_order hs σi ω ν θp ωp θw φh hgd had hhbd hYx
    (Vp := fun b => crossVar w (yd b) / θp ^ 2) (Vpf := fun b => crossVar w (y1 b) / θp ^ 2)
    hVp (crossVar_first_order hs hωt0 hωt1 hlwd blw1) bg ba bhb bYx
  exact bridge_first_order (hW.congr_left fun b => by simp only [loss612Phi]; ring) hL

end Woodford.StabilizationWelfare.TidyR5Distorted612
