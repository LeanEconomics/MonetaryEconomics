/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR5Distorted612

/-!
# The branch of distorted steady states (Propositions 6.10 and 6.12)

Woodford (2003), *Interest and Prices*, Chapter 6, §2.1, (2.9), p. 394 (the distorted steady
state `v_y(Ȳ) = (1 − Φ)u_c(Ȳ)`) and Appendix E.8, (E.33), p. 707 (its sticky-wage version
`H̄v_hφ_h = (1 − Φ)Ȳu_c`).

`TidyR5Distorted610.prop610_distorted` and `TidyR5Distorted612.prop612_distorted` take a branch
of distorted steady states `Ȳ_b → Y*` as a hypothesis. Here the branch is CONSTRUCTED by the
inverse function theorem (Mathlib's `HasStrictDerivAt.localInverse`) and shown to be locally
unique, and the propositions are restated on it, with no steady-state hypothesis left.

* `branch_gen`: if `h(Y*) = 0`, `h′(Y*) ≠ 0`, `k(Y*) ≠ 0` (`h, k` `C¹`), there is a function
  `g` with `g(0) = Y*`, `g(Φ) → Y*`, `h(g(Φ)) = −Φk(g(Φ))` for small `Φ`, and every solution of
  `h(Y) = −Φk(Y)` near `Y*` is `g(Φ)`.
* `modify_family`: a property holding near `Φ = 0` and at `0` can be made to hold at every index
  of a family, without changing the family eventually.
* **`branch610`**, **`prop610_on_branch`**; **`branch612`**, **`prop612_on_branch`**.
-/

namespace Woodford.StabilizationWelfare.TidyR5DistortedBranch

open Filter Topology Asymptotics
open BridgeExtensions TidyR5DistortedTools TidyR5Distorted610 TidyR5Distorted612
open ExpLogCES (crossVar)

variable {B : Type*} {L : Filter B} {s : B → ℝ}

/-- Woodford (2003), (2.9), p. 394 (**the branch of distorted steady states, by the inverse
function theorem**): if `h` and `k` are `C¹` near `Y*`, `h(Y*) = 0`, `h′(Y*) = κ ≠ 0` and
`k(Y*) ≠ 0`, there is `g` with `g(0) = Y*`, `g(Φ) → Y*` as `Φ → 0`, `h(g(Φ)) = −Φk(g(Φ))` for
all small `Φ`, and near `Y*` every solution of `h(Y) = −Φk(Y)` (any `Φ`) is `Y = g(Φ)`. -/
theorem branch_gen {h k : ℝ → ℝ} {Ys κ : ℝ} (hh : ContDiffAt ℝ 1 h Ys)
    (hk : ContDiffAt ℝ 1 k Ys) (hd : HasDerivAt h κ Ys) (hκ : κ ≠ 0) (h0 : h Ys = 0)
    (hk0 : k Ys ≠ 0) :
    ∃ g : ℝ → ℝ, g 0 = Ys ∧ Tendsto g (𝓝 0) (𝓝 Ys) ∧
      (∀ᶠ Φ in 𝓝 0, h (g Φ) = -(Φ * k (g Φ))) ∧
      ∀ᶠ Y in 𝓝 Ys, ∀ Φ, h Y = -(Φ * k Y) → g Φ = Y := by
  set ψ : ℝ → ℝ := fun Y => -(h Y / k Y) with hψ
  have hψc : ContDiffAt ℝ 1 ψ Ys := (hh.div hk hk0).neg
  have hψd : HasDerivAt ψ (-((κ * k Ys - h Ys * deriv k Ys) / k Ys ^ 2)) Ys :=
    (hd.div (hk.differentiableAt (by norm_num)).hasDerivAt hk0).neg
  have hψ0 : ψ Ys = 0 := by simp only [hψ, h0, zero_div, neg_zero]
  set ψ' := -((κ * k Ys - h Ys * deriv k Ys) / k Ys ^ 2) with hψ'
  have hψ'0 : ψ' ≠ 0 := by
    rw [hψ', h0, zero_mul, sub_zero]
    exact neg_ne_zero.2 (div_ne_zero (mul_ne_zero hκ hk0) (pow_ne_zero 2 hk0))
  have hs : HasStrictDerivAt ψ ψ' Ys := by
    have := hψc.hasStrictDerivAt (by norm_num)
    rwa [hψd.deriv] at this
  set g := hs.localInverse ψ ψ' Ys hψ'0 with hg
  have hT : Tendsto g (𝓝 (ψ Ys)) (𝓝 Ys) := (hs.hasStrictFDerivAt_equiv hψ'0).localInverse_tendsto
  rw [hψ0] at hT
  have hg0 : g 0 = Ys := by
    have := (hs.hasStrictFDerivAt_equiv hψ'0).localInverse_apply_image
    rw [hψ0] at this
    exact this
  have hR : ∀ᶠ Φ in 𝓝 (ψ Ys), ψ (g Φ) = Φ := hs.eventually_right_inverse hψ'0
  rw [hψ0] at hR
  have hkne : ∀ᶠ Y in 𝓝 Ys, k Y ≠ 0 := (hk.continuousAt).eventually_ne hk0
  refine ⟨g, hg0, hT, ?_, ?_⟩
  · filter_upwards [hR, hT.eventually hkne] with Φ h1 h2
    simp only [hψ] at h1
    field_simp at h1
    linarith
  · filter_upwards [hs.eventually_left_inverse hψ'0, hkne] with Y h1 h2 Φ hΦ
    have : ψ Y = Φ := by
      simp only [hψ, hΦ]
      field_simp
    rw [← this]
    exact h1

/-- Woodford (2003), §2.1 (bookkeeping for families): if `P` holds at `0` and near `0`, and
`Φ_b → 0`, there is a family `Φ′` with `P(Φ′_b)` for EVERY `b` and `Φ′ = Φ` eventually. -/
theorem modify_family {P : ℝ → Prop} (h0 : P 0) (hev : ∀ᶠ Φ in 𝓝 0, P Φ) {Phi : B → ℝ}
    (hT : Tendsto Phi L (𝓝 0)) : ∃ Phi' : B → ℝ, (∀ b, P (Phi' b)) ∧ Phi' =ᶠ[L] Phi := by
  classical
  refine ⟨fun b => if P (Phi b) then Phi b else 0, fun b => ?_, ?_⟩
  · by_cases hb : P (Phi b)
    · simp only [hb, ite_true]
    · simp only [hb, ite_false]; exact h0
  · filter_upwards [hT.eventually hev] with b hb
    simp only [hb, ite_true]

variable {Ξ : Type*} [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]

/-! ## Proposition 6.10 -/

/-- **Woodford (2003), (2.9), p. 394 (the distorted steady states of the two-sector model exist
and are locally unique).** Under the efficient-point conditions of `prop610_distorted`
(`v_y = u_c`, `σ⁻¹ + ω ≠ 0`, `u_c ≠ 0`), there is a branch `g` with `g(0) = Y*`, `g(Φ) → Y*`,
`g(Φ) > 0` and `v_y(g(Φ)) = (1 − Φ)u_c(g(Φ))` for small `Φ`; near `Y*` every steady state with
distortion `Φ` is `g(Φ)`. -/
theorem branch610 {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v) {Ys σi ω : ℝ}
    (hY : 0 < Ys) (hσω : σi + ω ≠ 0) (huc : dY u (Ys, 0) ≠ 0)
    (hucc : dYY u (Ys, 0) = -(σi * dY u (Ys, 0) / Ys))
    (hvy : dY v (Ys, 0) = dY u (Ys, 0)) (hvyy : dYY v (Ys, 0) = ω * dY v (Ys, 0) / Ys) :
    ∃ g : ℝ → ℝ, g 0 = Ys ∧ Tendsto g (𝓝 0) (𝓝 Ys) ∧
      (∀ᶠ Φ in 𝓝 0, 0 < g Φ ∧ dY v (g Φ, 0) = (1 - Φ) * dY u (g Φ, 0)) ∧
      ∀ᶠ Y in 𝓝 Ys, ∀ Φ, dY v (Y, 0) = (1 - Φ) * dY u (Y, 0) → g Φ = Y := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by norm_num)
  have hD : HasDerivAt (fun y => dY v (y, 0) - dY u (y, 0)) (dYY v (Ys, 0) - dYY u (Ys, 0))
      Ys := (hasDerivAt_dY hv2 Ys).sub (hasDerivAt_dY hu2 Ys)
  have hκ : dYY v (Ys, 0) - dYY u (Ys, 0) ≠ 0 := by
    rw [hvyy, hucc, hvy]
    have : ω * dY u (Ys, 0) / Ys - -(σi * dY u (Ys, 0) / Ys) =
        (σi + ω) * dY u (Ys, 0) / Ys := by ring
    rw [this]
    exact div_ne_zero (mul_ne_zero hσω huc) hY.ne'
  obtain ⟨g, hg0, hT, hsol, huniq⟩ := branch_gen (k := fun y => dY u (y, 0))
    (((contDiff_dY hv).sub (contDiff_dY hu)).contDiffAt.of_le (by norm_num))
    ((contDiff_dY hu).contDiffAt.of_le (by norm_num)) hD hκ
    (by simp only [hvy, sub_self]) huc
  refine ⟨g, hg0, hT, ?_, ?_⟩
  · filter_upwards [hsol, hT.eventually (lt_mem_nhds hY)] with Φ h1 h2
    exact ⟨h2, by linarith⟩
  · filter_upwards [huniq] with Y hY' Φ hΦ
    exact hY' Φ (by rw [hΦ]; ring)

variable {ι : Type*} [Fintype ι]

/-- **Woodford (2003), Proposition 6.10, (4.24), p. 436, around the CONSTRUCTED distorted
steady state.** Let `g` be a branch of distorted steady states (as given by `branch610`:
`g(0) = Y*`, `g(Φ) → Y*`, `g(Φ) > 0` and `v_y(g(Φ)) = (1 − Φ)u_c(g(Φ))` near `Φ = 0`). Along
any family with `Φ_b = O(ε)`, with outputs measured from `Ȳ_b = g(Φ_b)`, the conclusion of
`prop610_distorted` holds; no steady-state hypothesis on the family remains. -/
theorem prop610_on_branch (hs : Tendsto s L (𝓝 0)) {n1 η θ : ℝ} (hn0 : 0 < n1) (hn1 : n1 < 1)
    (hη : 0 < η) (hη1 : η ≠ 1) (hθ : θ ≠ 1) {w1 w2 : ι → ℝ} (hw10 : ∀ i, 0 ≤ w1 i)
    (hw11 : ∑ i, w1 i = 1) (hw20 : ∀ i, 0 ≤ w2 i) (hw21 : ∑ i, w2 i = 1)
    {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v) {Ys σi ω : ℝ}
    (hY : 0 < Ys) (hσω : σi + ω ≠ 0) (hηω : η⁻¹ + ω ≠ 0) (huc : dY u (Ys, 0) ≠ 0)
    (hucc : dYY u (Ys, 0) = -(σi * dY u (Ys, 0) / Ys))
    (hvy : dY v (Ys, 0) = dY u (Ys, 0))
    (hvyy : dYY v (Ys, 0) = ω * dY v (Ys, 0) / Ys)
    {g : ℝ → ℝ} (hg0 : g 0 = Ys) (hgT : Tendsto g (𝓝 0) (𝓝 Ys))
    (hgS : ∀ᶠ Φ in 𝓝 0, 0 < g Φ ∧ dY v (g Φ, 0) = (1 - Φ) * dY u (g Φ, 0))
    {Phi : B → ℝ} (hPhi : Phi =O[L] fun b => s b ^ 1)
    {yd1 yd2 : B → ι → ℝ} {f1 f2 gq q1 q2 : B → ℝ} {xu xv1 xv2 : B → Ξ}
    (hnorm : ∀ b, n1 * Real.exp (f1 b) + (1 - n1) * Real.exp (f2 b) = 1)
    (hg : ∀ b, dYXi u (Ys, 0) (xu b) = σi * dY u (Ys, 0) * gq b)
    (hq1 : ∀ b, dYXi v (Ys, 0) (xv1 b) = -(ω * dY v (Ys, 0) * q1 b))
    (hq2 : ∀ b, dYXi v (Ys, 0) (xv2 b) = -(ω * dY v (Ys, 0) * q2 b))
    (hyd1 : yd1 =O[L] fun b => s b ^ 1) (hyd2 : yd2 =O[L] fun b => s b ^ 1)
    (hf1 : f1 =O[L] fun b => s b ^ 1) (hf2 : f2 =O[L] fun b => s b ^ 1)
    (hgO : gq =O[L] fun b => s b ^ 1) (hq1O : q1 =O[L] fun b => s b ^ 1)
    (hq2O : q2 =O[L] fun b => s b ^ 1) (hxu : xu =O[L] fun b => s b ^ 1)
    (hxv1 : xv1 =O[L] fun b => s b ^ 1) (hxv2 : xv2 =O[L] fun b => s b ^ 1) :
    (fun b => periodU2 u v n1 η θ (g (Phi b)) w1 w2 (f1 b) (f2 b) (yd1 b) (yd2 b) (xu b)
        (xv1 b) (xv2 b) -
      (tip2 u v n1 Ys (xu b) (xv1 b) (xv2 b) + Ys * dY u (Ys, 0) *
        (TwoSectorWelfare.tip610 σi ω η⁻¹ n1 0 (gq b) (q1 b) (q2 b) (f2 b - f1 b)
            (tauAgg η⁻¹ n1 (f1 b) (f2 b)) -
          loss610Phi σi ω θ⁻¹ η⁻¹ n1 (Phi b) (gq b) (q1 b) (q2 b) (f2 b - f1 b)
            (logY2 n1 η (g (Phi b)) (f1 b) (f2 b) (logYidx w1 θ (yd1 b))
              (logYidx w2 θ (yd2 b)))
            (logYidx w1 θ (yd1 b)) (logYidx w2 θ (yd2 b)) (crossVar w1 (yd1 b))
            (crossVar w2 (yd2 b)) / 2))) =O[L] fun b => s b ^ 3 := by
  have hP0 : 0 < g 0 ∧ dY v (g 0, 0) = (1 - 0) * dY u (g 0, 0) := by
    rw [hg0, hvy]; exact ⟨hY, by ring⟩
  obtain ⟨Phi', hP', hEq⟩ := modify_family hP0 hgS (tendsto_of_o_one hs hPhi)
  have hPhi' : Phi' =O[L] fun b => s b ^ 1 := hPhi.congr' hEq.symm EventuallyEq.rfl
  have hT' : Tendsto (fun b => g (Phi' b)) L (𝓝 Ys) :=
    hgT.comp (tendsto_of_o_one hs hPhi')
  have h := prop610_distorted hs hn0 hn1 hη hη1 hθ hw10 hw11 hw20 hw21 hu hv hY hσω hηω huc
    hucc hvy hvyy (Yb := fun b => g (Phi' b)) (fun b => (hP' b).1) hT' (fun b => (hP' b).2)
    hPhi' hnorm hg hq1 hq2 hyd1 hyd2 hf1 hf2 hgO hq1O hq2O hxu hxv1 hxv2
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [hEq] with b hb
  simp only [hb]

/-! ## Proposition 6.12 -/

/-- **Woodford (2003), (E.33), p. 707 (the distorted steady states of the sticky-wage model
exist and are locally unique).** Under the efficient-point conditions of `prop612_distorted`,
there is a branch `c(Φ)` of log output gaps (`Ȳ = Y*e^{c}`, `H̄ = H*G(c)`) with `c(0) = 0`,
`c(Φ) → 0` and `H*v_h(H*G(c))G′(c) = (1 − Φ)Y*e^{c}u_c(Y*e^{c})` for small `Φ`; near `0` every
solution is `c(Φ)`. -/
theorem branch612 {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 3 G) (hG0 : G 0 = 1) {σi ω ν ωp φh Ys Hs : ℝ}
    (hG1 : fderiv ℝ G 0 1 = φh) (hG2 : fderiv ℝ (fderiv ℝ G) 0 1 1 = φh * (1 + ωp))
    (hω : ω = ωp + ν * φh) (hσω : σi + ω ≠ 0) (hYs : 0 < Ys) (huc : dY u (Ys, 0) ≠ 0)
    (hucc : dYY u (Ys, 0) = -(σi * dY u (Ys, 0) / Ys))
    (hvhh : dYY v (Hs, 0) = ν * dY v (Hs, 0) / Hs)
    (hss : Hs * dY v (Hs, 0) * φh = Ys * dY u (Ys, 0)) :
    ∃ gc : ℝ → ℝ, gc 0 = 0 ∧ Tendsto gc (𝓝 0) (𝓝 0) ∧
      (∀ᶠ Φ in 𝓝 0, Hs * dY v (Hs * G (gc Φ), 0) * deriv G (gc Φ) =
        (1 - Φ) * (Ys * Real.exp (gc Φ) * dY u (Ys * Real.exp (gc Φ), 0))) ∧
      ∀ᶠ c in 𝓝 0, ∀ Φ, Hs * dY v (Hs * G c, 0) * deriv G c =
        (1 - Φ) * (Ys * Real.exp c * dY u (Ys * Real.exp c, 0)) → gc Φ = c := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by norm_num)
  set K := Ys * dY u (Ys, 0) with hK
  have hK0 : K ≠ 0 := mul_ne_zero hYs.ne' huc
  set κ := K * (σi + ω) with hκd
  have hκ : κ ≠ 0 := mul_ne_zero hK0 hσω
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
    have ev : Hs * (dYY v (Hs, 0) * (Hs * φh)) * φh = ν * φh * (Hs * dY v (Hs, 0) * φh) := by
      have hHs : Hs ≠ 0 := by
        rintro rfl
        apply hK0
        rw [← hss]
        ring
      rw [hvhh]
      field_simp
    have eu : Ys * (dYY u (Ys, 0) * Ys) = -(σi * (Ys * dY u (Ys, 0))) := by
      rw [hucc]
      field_simp
    simp only [hG0, mul_one, Real.exp_zero, e1]
    rw [ev, eu, hκd, hK, hω]
    linear_combination (-(ν * φh + 1 + ωp)) * hss
  have hc1 : ContDiff ℝ 2 (fun c => dY v (Hs * G c, 0)) :=
    (contDiff_dY hv).comp (contDiff_const.mul (hG.of_le (by norm_num)))
  have hc2 : ContDiff ℝ 2 (fun c => Ys * Real.exp c) := contDiff_const.mul Real.contDiff_exp
  have hc3 : ContDiff ℝ 2 (fun c => dY u (Ys * Real.exp c, 0)) := (contDiff_dY hu).comp hc2
  have e1 : deriv G 0 = φh := hG1
  obtain ⟨gc, hg0, hT, hsol, huniq⟩ := branch_gen
    (h := fun c => Hs * dY v (Hs * G c, 0) * deriv G c -
      Ys * Real.exp c * dY u (Ys * Real.exp c, 0))
    (k := fun c => Ys * Real.exp c * dY u (Ys * Real.exp c, 0))
    ((((contDiff_const.mul hc1).mul hGd).sub (hc2.mul hc3)).contDiffAt.of_le (by norm_num))
    ((hc2.mul hc3).contDiffAt.of_le (by norm_num)) hH hκ
    (by simp only [hG0, mul_one, Real.exp_zero, e1]; rw [hss]; ring)
    (by simp only [Real.exp_zero, mul_one]; exact hK0)
  refine ⟨gc, hg0, hT, ?_, ?_⟩
  · filter_upwards [hsol] with Φ h1
    linear_combination h1
  · filter_upwards [huniq] with c hc Φ hΦ
    exact hc Φ (by linear_combination hΦ)

/-- **Woodford (2003), Proposition 6.12, (4.28), p. 444, around the CONSTRUCTED distorted
steady state.** Let `gc(Φ)` be a branch of log output gaps of distorted steady states (as given by
`branch612`). Along any family with `Φ_b = O(ε)`, with `Ȳ_b = Y*e^{gc(Φ_b)}`,
`H̄_b = H*G(gc(Φ_b))` and the renormalised labour requirement, the conclusion of
`prop612_distorted` holds; no steady-state hypothesis on the family remains. -/
theorem prop612_on_branch (hs : Tendsto s L (𝓝 0)) {J : Type*} [Fintype J] {w : ι → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {ωt : J → ℝ} (hωt0 : ∀ j, 0 ≤ ωt j)
    (hωt1 : ∑ j, ωt j = 1) {θp θw : ℝ} (hθp : θp ≠ 0) (hθp1 : θp ≠ 1) (hθw1 : θw ≠ 1)
    {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 3 G) (hG0 : G 0 = 1) (hGpos : ∀ z, 0 < G z)
    {σi ω ν ωp φh Ys Hs : ℝ}
    (hG1 : fderiv ℝ G 0 1 = φh) (hG2 : fderiv ℝ (fderiv ℝ G) 0 1 1 = φh * (1 + ωp))
    (hω : ω = ωp + ν * φh) (hφ : φh ≠ 0) (hσω : σi + ω ≠ 0) (hYs : 0 < Ys)
    (huc : dY u (Ys, 0) ≠ 0) (hucc : dYY u (Ys, 0) = -(σi * dY u (Ys, 0) / Ys))
    (hvhh : dYY v (Hs, 0) = ν * dY v (Hs, 0) / Hs)
    (hss : Hs * dY v (Hs, 0) * φh = Ys * dY u (Ys, 0))
    {gc : ℝ → ℝ} (hg0 : gc 0 = 0) (hgT : Tendsto gc (𝓝 0) (𝓝 0))
    (hgS : ∀ᶠ Φ in 𝓝 0, Hs * dY v (Hs * G (gc Φ), 0) * deriv G (gc Φ) =
      (1 - Φ) * (Ys * Real.exp (gc Φ) * dY u (Ys * Real.exp (gc Φ), 0)))
    {Phi : B → ℝ} (hPhi : Phi =O[L] fun b => s b ^ 1)
    {yd : B → ι → ℝ} {lw : B → J → ℝ} {a g hb : B → ℝ} {xu xv : B → Ξ}
    (hg : ∀ b, dYXi u (Ys, 0) (xu b) = σi * dY u (Ys, 0) * g b)
    (hhb : ∀ b, dYXi v (Hs, 0) (xv b) = -(ν * dY v (Hs, 0) * hb b))
    (hyd : yd =O[L] fun b => s b ^ 1) (hlw : lw =O[L] fun b => s b ^ 1)
    (ha : a =O[L] fun b => s b ^ 1) (hgO : g =O[L] fun b => s b ^ 1)
    (hhbO : hb =O[L] fun b => s b ^ 1) (hxu : xu =O[L] fun b => s b ^ 1)
    (hxv : xv =O[L] fun b => s b ^ 1) :
    (fun b => periodU12 u v w ωt θp θw (Ys * Real.exp (gc (Phi b))) (Hs * G (gc (Phi b)))
        (fun z => G (z + gc (Phi b)) / G (gc (Phi b))) (a b) (yd b) (lw b) (xu b) (xv b) -
      (tip12 u v Ys Hs (xu b) (xv b) + Ys * dY u (Ys, 0) *
        (StickyWageWelfare.tip612 σi ω ν 0 (g b) (a b) (hb b) -
          loss612Phi σi ω ν θp ωp θw φh (Phi b) (g b) (a b) (hb b) (logYidx w θp (yd b))
            (crossVar w (yd b) / θp ^ 2) (crossVar ωt (lw b)) / 2))) =O[L] fun b => s b ^ 3 := by
  have hlog : ∀ c, Real.log (Ys * Real.exp c / Ys) = c := fun c => by
    rw [mul_div_cancel_left₀ _ hYs.ne', Real.log_exp]
  have hP0 : Hs * dY v (Hs * G (gc 0), 0) * deriv G (gc 0) =
      (1 - 0) * (Ys * Real.exp (gc 0) * dY u (Ys * Real.exp (gc 0), 0)) := by
    have e1 : deriv G 0 = φh := hG1
    rw [hg0, hG0, e1, Real.exp_zero, mul_one, mul_one, ← hss]
    ring
  obtain ⟨Phi', hP', hEq⟩ := modify_family hP0 hgS (tendsto_of_o_one hs hPhi)
  have hPhi' : Phi' =O[L] fun b => s b ^ 1 := hPhi.congr' hEq.symm EventuallyEq.rfl
  have hT' : Tendsto (fun b => Ys * Real.exp (gc (Phi' b))) L (𝓝 Ys) := by
    have h := ((Real.continuous_exp.tendsto 0).comp (hgT.comp
      (tendsto_of_o_one hs hPhi'))).const_mul Ys
    simpa using h
  have hFOC : ∀ b, Hs * G (Real.log (Ys * Real.exp (gc (Phi' b)) / Ys)) *
      dY v (Hs * G (Real.log (Ys * Real.exp (gc (Phi' b)) / Ys)), 0) *
      (deriv G (Real.log (Ys * Real.exp (gc (Phi' b)) / Ys)) /
        G (Real.log (Ys * Real.exp (gc (Phi' b)) / Ys))) =
      (1 - Phi' b) * (Ys * Real.exp (gc (Phi' b))) *
        dY u (Ys * Real.exp (gc (Phi' b)), 0) := fun b => by
    rw [hlog]
    have hGc := (hGpos (gc (Phi' b))).ne'
    have e := hP' b
    field_simp
    linear_combination e
  have h := prop612_distorted hs hw0 hw1 hωt0 hωt1 hθp hθp1 hθw1 hu hv hG hG0 hGpos hG1 hG2 hω
    hφ hσω hYs huc hucc hvhh hss (Yb := fun b => Ys * Real.exp (gc (Phi' b)))
    (fun b => by positivity) hT' hFOC hPhi' hg hhb hyd hlw ha hgO hhbO hxu hxv
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [hEq] with b hb
  simp only [hb, hlog]

end Woodford.StabilizationWelfare.TidyR5DistortedBranch
